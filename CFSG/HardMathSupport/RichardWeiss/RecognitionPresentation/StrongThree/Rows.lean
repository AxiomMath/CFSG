module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Input
public import CFSG.Quasithin.Background.DicksonPerfectBasic
public import CFSG.Quasithin.EmptyFaithful.SzPS8S6Class

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open Subgroup

theorem isSolvable_of_normal_sup {X : Type*} [Group X] {Γ Q S : Subgroup X} (hΓ : Γ = Q ⊔ S)
    (hN : Γ ≤ Subgroup.normalizer (Q : Set X)) [Group.IsSolvable ↥Q] [Group.IsSolvable ↥S] :
    Group.IsSolvable ↥Γ := by
  have hQΓ : Q ≤ Γ := hΓ ▸ le_sup_left
  have hSΓ : S ≤ Γ := hΓ ▸ le_sup_right
  have hQn : (Q.subgroupOf Γ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).mpr hN
  have hQ' : Group.IsSolvable ↥(Q.subgroupOf Γ) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQΓ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQΓ).injective
  let f : ↥S →* (↥Γ ⧸ Q.subgroupOf Γ) :=
    (QuotientGroup.mk' (Q.subgroupOf Γ)).comp (Subgroup.inclusion hSΓ)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hsup : Q.subgroupOf Γ ⊔ S.subgroupOf Γ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hQΓ hSΓ, ← hΓ, Subgroup.subgroupOf_self]
    have hg : g ∈ (S.subgroupOf Γ ⊔ Q.subgroupOf Γ : Subgroup ↥Γ) := by
      rw [sup_comm, hsup]; exact Subgroup.mem_top g
    have hg' : g ∈ ((S.subgroupOf Γ ⊔ Q.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨s', hs', q', hq', rfl⟩ := hg'
    refine ⟨⟨(s' : X), hs'⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hSΓ ⟨(s' : X), hs'⟩) = QuotientGroup.mk (s' * q')
    rw [QuotientGroup.eq]
    have h1 : Subgroup.inclusion hSΓ ⟨(s' : X), hs'⟩ = s' := rfl
    rw [h1, inv_mul_cancel_left]
    exact hq'
  have hquot : Group.IsSolvable (↥Γ ⧸ Q.subgroupOf Γ) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_ker_le_range (Q.subgroupOf Γ).subtype
    (QuotientGroup.mk' (Q.subgroupOf Γ))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

section A6

open Equiv Equiv.Perm


theorem fixes_of_stable (σ : Perm (Fin 6)) (hσ : σ ^ 5 = 1) (s : Finset (Fin 6)) (hs : s.card = 3)
    (hst : ∀ x, x ∈ s ↔ σ x ∈ s) : ∀ x ∈ s, σ x = x := by
  let τ : Perm {x // x ∈ s} := σ.subtypePerm (fun x => (hst x).symm)
  have hτ5 : τ ^ 5 = 1 := by
    ext x
    simp [τ, subtypePerm_pow, hσ]
  have hd1 : orderOf τ ∣ 5 := orderOf_dvd_of_pow_eq_one hτ5
  have hd2 : orderOf τ ∣ 6 := by
    have := orderOf_dvd_card (x := τ)
    simpa [Fintype.card_perm, Fintype.card_coe, hs, Nat.factorial] using this
  have hτ1 : orderOf τ = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) hd1 hd2
  have hτ : τ = 1 := orderOf_eq_one_iff.mp hτ1
  intro x hx
  have := congrArg (fun π : Perm {x // x ∈ s} => (π ⟨x, hx⟩ : Fin 6)) hτ
  simpa [τ] using this

theorem no_order_five_partition (σ : Perm (Fin 6)) (hσ : orderOf σ = 5) (A : Finset (Fin 6))
    (hA : A.card = 3) (h : A.image σ = A ∨ A.image σ = Aᶜ) : False := by
  have hσ5 : σ ^ 5 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hinj : ∀ x y, σ x = σ y → x = y := fun x y hxy => σ.injective hxy
  rcases h with h | h
  · have hst : ∀ x, x ∈ A ↔ σ x ∈ A := by
      intro x
      constructor
      · intro hx
        have : σ x ∈ A.image σ := Finset.mem_image_of_mem σ hx
        rwa [h] at this
      · intro hx
        rw [← h] at hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
        exact (hinj y x hyx) ▸ hy
    have hstc : ∀ x, x ∈ Aᶜ ↔ σ x ∈ Aᶜ := fun x => by
      simp only [Finset.mem_compl]; exact not_congr (hst x)
    have hAc : (Aᶜ).card = 3 := by
      rw [Finset.card_compl, hA]; simp
    have h1 := fixes_of_stable σ hσ5 A hA hst
    have h2 := fixes_of_stable σ hσ5 Aᶜ hAc hstc
    have hone : σ = 1 := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x ∈ A
      · simpa using h1 x hx
      · simpa using h2 x (Finset.mem_compl.mpr hx)
    rw [hone, orderOf_one] at hσ
    omega
  · have hswap : ∀ x, x ∈ A ↔ σ x ∉ A := by
      intro x
      constructor
      · intro hx
        have : σ x ∈ A.image σ := Finset.mem_image_of_mem σ hx
        rw [h] at this
        exact Finset.mem_compl.mp this
      · intro hx
        have : σ x ∈ A.image σ := by rw [h]; exact Finset.mem_compl.mpr hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
        exact (hinj y x hyx) ▸ hy
    have hst2 : ∀ x, x ∈ A ↔ (σ ^ 2) x ∈ A := by
      intro x
      have := hswap x
      have h2 := hswap (σ x)
      simp only [pow_two, Perm.mul_apply]
      tauto
    have hstp : ∀ n : ℕ, ∀ x, x ∈ A ↔ ((σ ^ 2) ^ n) x ∈ A := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [pow_succ, Perm.mul_apply]
        exact (hst2 x).trans (ih _)
    have hσ6 : (σ ^ 2) ^ 3 = σ := by
      have : (σ ^ 2) ^ 3 = σ ^ 5 * σ := by rw [← pow_mul, ← pow_succ]
      rw [this, hσ5, one_mul]
    obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    have h3 := (hstp 3 x).mp hx
    rw [hσ6] at h3
    exact (hswap x).mp hx h3

theorem isSolvable_of_partition {X : Type*} [Group X] {Γ K : Subgroup X} (hΓK : Γ ≤ K)
    (φ : ↥K ≃* alternatingGroup (Fin 6)) (A : Finset (Fin 6)) (hA : A.card = 3)
    (h : ∀ k : ↥K, (k : X) ∈ Γ ↔
      (A.image (φ k : Equiv.Perm (Fin 6)) = A ∨ A.image (φ k : Equiv.Perm (Fin 6)) = Aᶜ)) :
    Group.IsSolvable ↥Γ := by
  let ψ : ↥Γ →* Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp (φ.toMonoidHom.comp (Subgroup.inclusion hΓK))
  have hψ : Function.Injective ψ :=
    Subtype.val_injective.comp (φ.injective.comp (Subgroup.inclusion_injective hΓK))
  have hS : Group.IsSolvable ↥ψ.range := by
    refine CFSG.Quasithin.SzPS8.S6Class.isSolvable_of_five_not_dvd_card fun h5 => ?_
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨σ', hσ'⟩ := exists_prime_orderOf_dvd_card' (G := ψ.range) 5 h5
    obtain ⟨γ, hγ⟩ := σ'.2
    have hσ5 : orderOf (σ' : Perm (Fin 6)) = 5 := by rw [← hσ']; exact orderOf_submonoid σ'
    refine no_order_five_partition (σ' : Perm (Fin 6)) hσ5 A hA ?_
    rw [← hγ]
    exact (h (Subgroup.inclusion hΓK γ)).mp γ.2
  exact Group.isSolvable_of_isSolvable_injective (f := ψ.rangeRestrict)
    (MonoidHom.rangeRestrict_injective_iff.mpr hψ)

end A6

theorem gammaCore_le {p k : ℕ} {X : Type*} [Group X] [Finite X] (A P : Subgroup X) :
    gammaCore p k A P ≤ A :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem isSolvable_of_isPGroup' {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsPGroup p ↥H) : Group.IsSolvable ↥H := by
  have := hH.isNilpotent
  infer_instance

theorem gamma_isSolvable {X : Type} [Group X] [Finite X] {K Q : Subgroup X}
    (hQ : IsPGroup 3 ↥Q) (h : Gls3Conclusion X K Q) :
    Group.IsSolvable ↥(gammaCore 3 1 K Q) := by
  obtain ⟨-, -, h⟩ := h
  have hQs : Group.IsSolvable ↥Q := isSolvable_of_isPGroup' hQ
  rcases h with ⟨-, hN, J, hJ, hΓ⟩ | ⟨-, -, -, -, ⟨e⟩⟩ | ⟨φ, A, hA, hmem⟩ |
      ⟨-, -, -, hN, S, -, -, hΓS, ⟨e⟩⟩ | ⟨-, hN, S, -, hΓS, hS16, -, -⟩
  · have : CommGroup ↥J := IsCyclic.commGroup
    have : Group.IsSolvable ↥J := inferInstance
    exact isSolvable_of_normal_sup hΓ (hN.le.trans inf_le_right)
  · have := CFSG.Quasithin.Dickson.isSolvable_dihedral 9
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · exact isSolvable_of_partition (gammaCore_le K Q) φ A hA hmem
  · have hQ8 : IsPGroup 2 (QuaternionGroup 2) := by
      refine IsPGroup.of_card (n := 3) ?_
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
    have : Group.IsSolvable (QuaternionGroup 2) := by
      have := hQ8.isNilpotent
      infer_instance
    have : Group.IsSolvable ↥S :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact isSolvable_of_normal_sup hΓS.symm (hN.le.trans inf_le_right)
  · have hS : Group.IsSolvable ↥S := isSolvable_of_isPGroup' (IsPGroup.of_card (p := 2) (n := 4) (by rw [hS16]; norm_num))
    exact isSolvable_of_normal_sup hΓS.symm (hN.le.trans inf_le_right)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
