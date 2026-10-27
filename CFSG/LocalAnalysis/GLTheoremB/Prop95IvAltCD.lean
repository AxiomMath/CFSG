module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT2
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Helpers

private lemma isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hcomm, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [hcomm] at hle
  haveI := hsimple
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

private lemma perm_eq_one_of_comm_alt {n : ℕ} (hn : 4 ≤ n) (g : Equiv.Perm (Fin n))
    (hg : ∀ y ∈ alternatingGroup (Fin n), g * y = y * g) : g = 1 := by
  refine Equiv.ext fun a => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hne
  obtain ⟨b, hb⟩ : (({a, g a} : Finset (Fin n))ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_two (a := a) (b := g a)
    omega
  obtain ⟨c, hc⟩ : (({a, g a, b} : Finset (Fin n))ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_three (a := a) (b := g a) (c := b)
    omega
  have hb' : b ≠ a ∧ b ≠ g a := by simpa using hb
  have hc' : c ≠ a ∧ c ≠ g a ∧ c ≠ b := by simpa using hc
  have hab : a ≠ b := fun h => hb'.1 h.symm
  have hac : a ≠ c := fun h => hc'.1 h.symm
  have hxA : Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap (fun h => hc'.2.2 h.symm)]
    decide
  have hxa : (Equiv.swap a b * Equiv.swap b c) a = b := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
  have hxga : (Equiv.swap a b * Equiv.swap b c) (g a) = g a := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hb'.2.symm hc'.2.1.symm,
      Equiv.swap_apply_of_ne_of_ne hne hb'.2.symm]
  have h1 : g ((Equiv.swap a b * Equiv.swap b c) a) = (Equiv.swap a b * Equiv.swap b c) (g a) := by
    have := congrArg (fun π : Equiv.Perm (Fin n) => π a) (hg _ hxA)
    simpa only [Equiv.Perm.mul_apply] using this
  rw [hxa, hxga] at h1
  exact hb'.1 (g.injective h1)

private lemma two_mul_card_alt (n : ℕ) (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [two_mul_nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

private lemma alt_deg_eq {n m : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m)
    (e : alternatingGroup (Fin n) ≃* alternatingGroup (Fin m)) : n = m := by
  have hc : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin m)) :=
    Nat.card_congr e.toEquiv
  have h1 := two_mul_card_alt n (by omega)
  have h2 := two_mul_card_alt m (by omega)
  have hf : n.factorial = m.factorial := by omega
  exact (Nat.factorial_inj (by omega)).1 hf

private lemma card_alt_le (n : ℕ) : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial := by
  have h : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
    Subgroup.card_le_card_group _
  rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm, Fintype.card_fin]
    at h

private lemma card_alt_ge {m : ℕ} (hm : 5 ≤ m) : 60 ≤ Nat.card (alternatingGroup (Fin m)) := by
  have h := two_mul_card_alt m (by omega)
  have hf : (5 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
  have h5 : (5 : ℕ).factorial = 120 := by decide
  omega

private lemma false_of_alt_four_simple {G : Type*} [Group G] {n : ℕ} (hn : n = 4)
    (e : G ≃* alternatingGroup (Fin n)) (hs : IsSimpleGroup G) : False := by
  subst hn
  haveI : IsSimpleGroup (alternatingGroup (Fin 4)) := e.symm.isSimpleGroup
  have hsolv : Group.IsSolvable (alternatingGroup (Fin 4)) :=
    alternatingGroup.isSolvable (by simp)
  have hcomm : ∀ a b : alternatingGroup (Fin 4), a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.2 hsolv
  letI : CommGroup (alternatingGroup (Fin 4)) :=
    { (inferInstance : Group (alternatingGroup (Fin 4))) with mul_comm := hcomm }
  have hp := CommGroup.is_simple_iff_prime_card.1 (inferInstance : IsSimpleGroup (alternatingGroup (Fin 4)))
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hp
  norm_num [Nat.factorial] at hp

private lemma alt_six_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩, ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  revert h'
  decide

private lemma quasisimple_of_alt_six_quotient {K : Type*} [Group K] (hperf : commutator K = ⊤)
    (e : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 6)) : CFSG.IsQuasisimple K := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨Group.isPerfect_def.mpr hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := alt_six_nonabelian
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

private lemma isChevTwo_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : IsChevTwo Y) : IsChevTwo Z := by
  rcases h with ⟨d, hd, ⟨eY⟩⟩ | ⟨n, hn, ⟨eY⟩⟩ | ⟨d, hd, ⟨eY⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans eY⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans eY⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans eY⟩⟩)

end Helpers

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

theorem alt_hyp28Three (hAC : AltNotChevTwo) (h : IvSetting m p M D L) (k : ℕ)
    (e : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* ↥(alternatingGroup (Fin (k * p + 4))))
    (hR : ActsLikeSubRootFourCQ (barX p M (gammaD D)) (barX p M L) (k * p + 4) e) :
    Hyp28Three (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M) := by
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hcomp : IsComponentOf (tl M L) ⊤ := isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ
  have hΓM : gammaD D ≤ M := gammaD_le h.hyp
  have hΓN : gammaD D ≤ Subgroup.normalizer (L : Set G) := gammaD_le_normalizer hp h.hyp h.hL h.hn
  let eT : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin (k * p + 4)) :=
    (psiHat h).trans e
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · exfalso
      subst hk0
      exact false_of_alt_four_simple (n := 0 * p + 4) (by omega) e h.hL.2.2.1.2.2.2
    · exact hk
  have hn5 : 5 ≤ k * p + 4 := by
    have : 0 < k * p := Nat.mul_pos (by omega) hp.pos
    omega
  have hnot : k * p + 4 ≠ 5 ∧ k * p + 4 ≠ 6 ∧ k * p + 4 ≠ 8 := by
    have hdiv : p ∣ k * p := Dvd.intro_left k rfl
    have hp2' : 2 ≤ p := hp.two_le
    refine ⟨fun h5 => ?_, fun h6 => ?_, fun h8 => ?_⟩
    · have hk1 : k * p = 1 := by omega
      rw [hk1] at hdiv
      exact hp.one_lt.ne' (Nat.dvd_one.1 hdiv)
    · have hk2 : k * p = 2 := by omega
      rw [hk2] at hdiv
      exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hdiv) hp2')
    · have hk4 : k * p = 4 := by omega
      rw [hk4] at hdiv
      have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
      interval_cases p <;> first | omega | (norm_num at hp)
  obtain ⟨V₄, V, hV₄, hVV₄, hact⟩ := hR
  have hact' : ActsLikeCQ (tl M (gammaD D)) (tl M L) eT (V.map (MulAut.conj :
      ↥(alternatingGroup (Fin (k * p + 4))) →* _)) :=
    (actsLikeCQ_tl_iff_bar h e _ hΓM hΓN).2 hact
  have hq : CFSG.IsQuasisimple ↥(tl M L) := isQuasisimple_of_open hcomp.2.2
  refine ⟨⟨hq, k * p + 4, hn5, ⟨eT⟩⟩, ?_, k * p + 4, eT, V₄, V, hV₄, hVV₄, hact'⟩
  rintro ⟨-, hchev⟩
  exact hAC (k * p + 4) hn5 hnot.1 hnot.2.1 hnot.2.2 (isChevTwo_of_mulEquiv eT hchev)

theorem not_concl28b_of_hyp28Three {X : Type} [Group X] (W K S : Subgroup X) [W.Normal] :
    Hyp28Three W K S → Concl28b W K S → False := by
  rintro ⟨⟨-, m, hm, ⟨eQm⟩⟩, -, n, e, V₄, V, -, -, hV⟩ ⟨-, n', e', hn', ⟨-, τ, hτ, hτA⟩, -, -⟩
  have hn : 5 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h1 := card_alt_le n
    have h2 := card_alt_ge hm
    have h3 : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin m)) :=
      Nat.card_congr (e.symm.trans eQm).toEquiv
    have h4 : n.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (by omega)
    have h5 : (4 : ℕ).factorial = 24 := by decide
    omega
  obtain rfl : n = n' := alt_deg_eq hn hn' (e.symm.trans e')
  obtain ⟨φ, hφ, hφτ⟩ :=
    hτA.2 (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) (Subgroup.mem_zpowers _)
  obtain ⟨σ, hσ, hφσ⟩ := hV.1 φ hφ
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hσ
  set ψ : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) := e.symm.trans e' with hψdef
  have hψe : ∀ z, e' z = ψ (e z) := fun z => by simp [hψdef]
  have hE : ∀ a, e (QuotientGroup.mk (φ a)) = v * e (QuotientGroup.mk a) * (v : _)⁻¹ :=
    fun a => by rw [hφσ a, MulAut.conj_apply]
  have hE' : ∀ a, ((e' (QuotientGroup.mk (φ a)) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
      (τ : Equiv.Perm (Fin n)) * ((e' (QuotientGroup.mk a) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) * (τ : Equiv.Perm (Fin n))⁻¹ :=
    fun a => by rw [hφτ a, MulAut.conjNormal_apply]
  have hkey : ∀ a : ↥(bar W K),
      ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
          ((ψ (e (QuotientGroup.mk a)) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
          ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))⁻¹ =
        (τ : Equiv.Perm (Fin n)) *
          ((ψ (e (QuotientGroup.mk a)) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
          (τ : Equiv.Perm (Fin n))⁻¹ := by
    intro a
    have h1 := hE' a
    simp only [hψe] at h1
    rw [hE a, map_mul, map_mul, map_inv] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hcon : ∀ z : alternatingGroup (Fin n),
      ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * (z : Equiv.Perm (Fin n)) *
          ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))⁻¹ =
        (τ : Equiv.Perm (Fin n)) * (z : Equiv.Perm (Fin n)) * (τ : Equiv.Perm (Fin n))⁻¹ := by
    intro z
    obtain ⟨q, hq⟩ := e.surjective (ψ.symm z)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have h := hkey a
    rw [hq, MulEquiv.apply_symm_apply] at h
    exact h
  have hg : ∀ y ∈ alternatingGroup (Fin n),
      (τ : Equiv.Perm (Fin n))⁻¹ * ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * y =
        y * ((τ : Equiv.Perm (Fin n))⁻¹ * ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) := by
    intro y hy
    have h := hcon ⟨y, hy⟩
    calc (τ : Equiv.Perm (Fin n))⁻¹ * ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * y
        = (τ : Equiv.Perm (Fin n))⁻¹ * (((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * y *
            ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))⁻¹) *
            ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by group
      _ = (τ : Equiv.Perm (Fin n))⁻¹ * ((τ : Equiv.Perm (Fin n)) * y *
            (τ : Equiv.Perm (Fin n))⁻¹) * ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
          rw [h]
      _ = y * ((τ : Equiv.Perm (Fin n))⁻¹ * ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) := by
          group
  have h1 := perm_eq_one_of_comm_alt (by omega) _ hg
  have hwτ : ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = (τ : Equiv.Perm (Fin n)) :=
    (inv_mul_eq_one.1 h1).symm
  have hsw : Equiv.Perm.sign ((ψ v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.1 (ψ v).2
  have hst : Equiv.Perm.sign (τ : Equiv.Perm (Fin n)) = -1 := hτ.sign_eq
  rw [← hwτ, hsw] at hst
  exact absurd hst (by decide)

theorem not_concl28c_of_hyp28Two {X : Type} [Group X] (W K S : Subgroup X) [W.Normal] :
    Hyp28Two W K S → Concl28c W K S → False := by
  rintro ⟨-, -, -, -, n₂, e₂, hT⟩ ⟨e, ⟨V, hV, hact⟩, -⟩
  have hcard : Nat.card (inducedAutGroup (bar W S) (bar W K)) = 2 := hT.1
  haveI : Finite (inducedAutGroup (bar W S) (bar W K)) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hsurj : ∀ y : ↥(alternatingGroup (Fin 7)), ∃ a : ↥(bar W K),
      e (QuotientGroup.mk a) = y := by
    intro y
    obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, hq⟩
  have hex : ∀ v : ↥V, ∃ φ ∈ inducedAutGroup (bar W S) (bar W K),
      InducesOn e φ (MulAut.conj (v : ↥(alternatingGroup (Fin 7)))) := fun v =>
    hact.2 _ (Subgroup.mem_map.2 ⟨v, v.2, rfl⟩)
  choose f hfmem hfact using hex
  let F : ↥V → ↥(inducedAutGroup (bar W S) (bar W K)) := fun v => ⟨f v, hfmem v⟩
  have hinj : Function.Injective F := by
    intro v w hvw
    have hfeq : f v = f w := congrArg Subtype.val hvw
    have hconj : ∀ y : ↥(alternatingGroup (Fin 7)),
        (v : ↥(alternatingGroup (Fin 7))) * y * (v : ↥(alternatingGroup (Fin 7)))⁻¹ =
          (w : ↥(alternatingGroup (Fin 7))) * y * (w : ↥(alternatingGroup (Fin 7)))⁻¹ := by
      intro y
      obtain ⟨a, ha⟩ := hsurj y
      have h1 := hfact v a
      have h2 := hfact w a
      rw [hfeq] at h1
      have key := h1.symm.trans h2
      rw [ha, MulAut.conj_apply, MulAut.conj_apply] at key
      exact key
    have hcommP : ∀ y ∈ alternatingGroup (Fin 7),
        ((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹ *
            ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) * y =
          y * (((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹ *
            ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))) := by
      intro y hy
      have h := congrArg Subtype.val (hconj ⟨y, hy⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc ((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹ *
            ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) * y
          = ((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹ *
              (((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) * y *
                ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹) *
              ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) := by group
        _ = ((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹ *
              (((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) * y *
                ((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹) *
              ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) := by rw [h]
        _ = y * (((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))⁻¹ *
              ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))) := by group
    have h1 := perm_eq_one_of_comm_alt (by norm_num) _ hcommP
    have hvw' : ((v : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) =
        ((w : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) := (inv_mul_eq_one.1 h1).symm
    exact Subtype.ext (Subtype.ext hvw')
  have hle := Nat.card_le_card_of_injective F hinj
  have hV4 : Nat.card ↥V = 4 := hV.1
  omega

theorem alt_hyp28Four (hM : AltSixSevenCentre) (h : IvSetting m p M D L)
    (hd : Nonempty ((↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* alternatingGroup (Fin 6)) ∧
      p = 5 ∧ Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
      Nonempty (↥(inducedAutGroup (barX p M L ⊔ barX p M (gammaD D)) (barX p M L)) ≃*
        ↥CFSG.QuasithinUnique.A6Models.pgl29)) :
    Hyp28Four (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M) := by
  obtain ⟨⟨e6⟩, -, hcard, ⟨eP⟩⟩ := hd
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hcomp : IsComponentOf (tl M L) ⊤ := isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ
  have hperfT : commutator ↥(tl M L) = ⊤ := hcomp.2.2.1
  have hΓM : gammaD D ≤ M := gammaD_le h.hyp
  have hΓN : gammaD D ≤ Subgroup.normalizer (L : Set G) := gammaD_le_normalizer hp h.hyp h.hL h.hn
  let eT : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin 6) := (psiHat h).trans e6
  have hO2 : CFSG.pCore 2 ↥(tl M L) = ⊥ := pCore_tl_eq_bot h
  have hdvd : Nat.card (Subgroup.center ↥(tl M L)) ∣ 6 :=
    hM 6 (Or.inl rfl) ↥(tl M L) hperfT ⟨eT⟩
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.center ↥(tl M L)) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hzc : (z : ↥(tl M L)) ∈ Subgroup.center ↥(tl M L) := z.2
    have hHn : (Subgroup.zpowers (z : ↥(tl M L))).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hc : Commute g (z : ↥(tl M L)) := Subgroup.mem_center_iff.1 hzc g
      have : g * (z : ↥(tl M L)) ^ k * g⁻¹ = (z : ↥(tl M L)) ^ k := by
        rw [(hc.zpow_right k).eq]
        group
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ _
    have hPgrp : IsPGroup 2 (Subgroup.zpowers (z : ↥(tl M L))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]; norm_num)
    have hle : Subgroup.zpowers (z : ↥(tl M L)) ≤ CFSG.pCore 2 ↥(tl M L) := le_sSup ⟨hHn, hPgrp⟩
    rw [hO2, le_bot_iff] at hle
    have hz1 : (z : ↥(tl M L)) = 1 := by
      have hmem := Subgroup.mem_zpowers (z : ↥(tl M L))
      rw [hle] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [← Subgroup.orderOf_coe, hz1, orderOf_one] at hz
    norm_num at hz
  have hcases : Nat.card (Subgroup.center ↥(tl M L)) = 1 ∨
      Nat.card (Subgroup.center ↥(tl M L)) = 3 := by
    generalize Nat.card (Subgroup.center ↥(tl M L)) = c at hdvd hodd ⊢
    have hc6 : c ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases c <;> first | omega | (norm_num at hdvd hodd)
  have hS2 : Nat.card (inducedAutGroup (bar (CFSG.pCore 2 ↥M) ((gammaD D).subgroupOf M))
      (bar (CFSG.pCore 2 ↥M) (L.subgroupOf M))) = 2 :=
    (card_inducedAutGroup_tl_eq_bar h hΓM hΓN).trans hcard
  obtain ⟨eS⟩ := inducedAutGroupSup_nonempty h hΓM hΓN
  refine ⟨?_, hS2, ⟨eS.trans eP⟩⟩
  rcases hcases with hc1 | hc3
  ·
    have hbot : Subgroup.center ↥(tl M L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
    exact Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans eT⟩
  · exact Or.inr ⟨hperfT, hc3, ⟨eT⟩⟩

theorem not_concl28abc_of_hyp28Four {X : Type} [Group X] (W K S : Subgroup X) [W.Normal] :
    Hyp28Four W K S → ¬ (Concl28a W K S ∨ Concl28b W K S ∨ Concl28c W K S) := by
  rintro ⟨hK, -, -⟩ (⟨hone, -⟩ | ⟨htwo, -⟩ | ⟨e7, -⟩)
  ·
    apply hone.2.1
    rcases hK with h6 | h6
    · obtain ⟨φ6⟩ := h6
      haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
        Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
      have hperf : commutator (↥(bar W K)) = ⊤ :=
        Group.isPerfect_def.1
          (Group.IsPerfect.ofSurjective (f := φ6.symm.toMonoidHom) φ6.symm.surjective)
      haveI : IsSimpleGroup (↥(bar W K)) := φ6.isSimpleGroup
      have hZ : Subgroup.center ↥(bar W K) = ⊥ := by
        rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥(bar W K)) with hb | ht
        · exact hb
        · exfalso
          obtain ⟨a, b, hab⟩ := alt_six_nonabelian
          apply hab
          have hc : ∀ g : ↥(bar W K), g * φ6.symm a = φ6.symm a * g := fun g =>
            Subgroup.mem_center_iff.1 (by rw [ht]; exact Subgroup.mem_top _) g
          have h := congrArg φ6 (hc (φ6.symm b))
          simpa using h.symm
      have eQ : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* alternatingGroup (Fin 6) :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans φ6)
      exact ⟨quasisimple_of_alt_six_quotient hperf eQ, 6, by norm_num, ⟨eQ⟩⟩
    · obtain ⟨hcommK, -, ⟨e6⟩⟩ := h6
      exact ⟨quasisimple_of_alt_six_quotient hcommK e6, 6, by norm_num, ⟨e6⟩⟩
  ·
    rcases hK with h6 | h6
    · exact htwo.2.1 h6
    · exact htwo.2.2.1 h6
  ·
    rcases hK with h6 | h6
    · obtain ⟨φ6⟩ := h6
      have hK360 : Nat.card ↥(bar W K) = 360 := by
        have h1 := two_mul_card_alt 6 (by norm_num)
        have h2 : Nat.card ↥(bar W K) = Nat.card (alternatingGroup (Fin 6)) :=
          Nat.card_congr φ6.toEquiv
        have h3 : (6 : ℕ).factorial = 720 := by decide
        omega
      haveI : Finite ↥(bar W K) := Nat.finite_of_card_ne_zero (by omega)
      have hQ : Nat.card (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) = 2520 := by
        have h1 := two_mul_card_alt 7 (by norm_num)
        have h2 : Nat.card (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) =
            Nat.card (alternatingGroup (Fin 7)) := Nat.card_congr e7.toEquiv
        have h3 : (7 : ℕ).factorial = 5040 := by decide
        omega
      have hle : Nat.card (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≤ Nat.card ↥(bar W K) := by
        have h1 := Subgroup.card_mul_index (Subgroup.center ↥(bar W K))
        have h2 : Nat.card (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) =
            (Subgroup.center ↥(bar W K)).index := (Subgroup.index_eq_card _).symm
        have h3 : 0 < Nat.card (Subgroup.center ↥(bar W K)) := Nat.card_pos
        rw [h2, ← h1]
        exact Nat.le_mul_of_pos_left _ h3
      omega
    · obtain ⟨-, hZ3, ⟨e6⟩⟩ := h6
      exact absurd (alt_deg_eq (by norm_num) (by norm_num) (e6.symm.trans e7)) (by norm_num)

theorem prime_eq_three_of_concl28c (h : IvSetting m p M D L) (k : ℕ)
    (e : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* ↥(alternatingGroup (Fin (k * p + 4))))
    (hc : Concl28c (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M)) : p = 3 := by
  obtain ⟨e7, -⟩ := hc
  have hp : p.Prime := prime_of_standing h.standing
  have hcard : Nat.card (alternatingGroup (Fin (k * p + 4))) = Nat.card (alternatingGroup (Fin 7)) :=
    Nat.card_congr (((psiHat h).trans e).symm.trans e7).toEquiv
  have h1 := two_mul_card_alt (k * p + 4) (by omega)
  have h2 := two_mul_card_alt 7 (by norm_num)
  have hfac : (k * p + 4).factorial = (7 : ℕ).factorial := by omega
  have hkp : k * p + 4 = 7 := (Nat.factorial_inj (by omega)).1 hfac
  have hdvd : p ∣ 3 := Dvd.intro_left k (by omega)
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
