module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4A
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_stab {K : Subgroup G} {X : Set G} {x₀ : G} (hx₀ : x₀ ∈ X)
    (hfix : ∀ k ∈ K, k * x₀ * k⁻¹ = x₀)
    (h₀ : ∀ σ₀ : Equiv.Perm ↥(X \ {x₀}), ∃ k ∈ K, ∀ x : ↥(X \ {x₀}),
      ((σ₀ x : ↥(X \ {x₀})) : G) = k * x * k⁻¹)
    (σ : Equiv.Perm ↥X) (hσ : (σ ⟨x₀, hx₀⟩ : ↥X) = ⟨x₀, hx₀⟩) :
    ∃ k ∈ K, ∀ x : ↥X, ((σ x : ↥X) : G) = k * x * k⁻¹ := by
  have hmem : ∀ τ : Equiv.Perm ↥X, (τ ⟨x₀, hx₀⟩ : ↥X) = ⟨x₀, hx₀⟩ →
      ∀ y : ↥(X \ {x₀}), ((τ ⟨y, y.2.1⟩ : ↥X) : G) ∈ X \ {x₀} := by
    intro τ hτ y
    refine (Set.mem_diff _).mpr ⟨(τ ⟨y, y.2.1⟩).2, fun h => y.2.2 ?_⟩
    have h1 : τ ⟨y, y.2.1⟩ = τ ⟨x₀, hx₀⟩ := by
      rw [hτ]
      exact Subtype.ext (Set.mem_singleton_iff.mp h)
    have h2 := τ.injective h1
    exact Set.mem_singleton_iff.mpr (congrArg Subtype.val h2)
  have hσ' : (σ.symm ⟨x₀, hx₀⟩ : ↥X) = ⟨x₀, hx₀⟩ := by
    rw [Equiv.symm_apply_eq]
    exact hσ.symm
  let σ₀ : Equiv.Perm ↥(X \ {x₀}) :=
    { toFun := fun y => ⟨(σ ⟨y, y.2.1⟩ : ↥X), hmem σ hσ y⟩
      invFun := fun y => ⟨(σ.symm ⟨y, y.2.1⟩ : ↥X), hmem σ.symm hσ' y⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  obtain ⟨k, hk, hkx⟩ := h₀ σ₀
  refine ⟨k, hk, fun x => ?_⟩
  by_cases hx : (x : G) = x₀
  · have hx' : x = ⟨x₀, hx₀⟩ := Subtype.ext hx
    rw [hx', hσ]
    exact (hfix k hk).symm
  · exact hkx ⟨x, x.2, fun h => hx (Set.mem_singleton_iff.mp h)⟩

theorem exists_conj_of_trans_stab {N K : Subgroup G} {X : Set G} {x₀ : G} (hx₀ : x₀ ∈ X)
    (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hKN : K ≤ N)
    (htrans : ∀ x ∈ X, ∃ n ∈ N, n * x₀ * n⁻¹ = x)
    (hstab : ∀ σ : Equiv.Perm ↥X, (σ ⟨x₀, hx₀⟩ : ↥X) = ⟨x₀, hx₀⟩ →
      ∃ k ∈ K, ∀ x : ↥X, ((σ x : ↥X) : G) = k * x * k⁻¹) (σ : Equiv.Perm ↥X) :
    ∃ n ∈ N, ∀ x : ↥X, ((σ x : ↥X) : G) = n * x * n⁻¹ := by
  obtain ⟨n, hn, hnx⟩ := htrans (σ ⟨x₀, hx₀⟩ : G) (σ ⟨x₀, hx₀⟩).2
  have han : (conjAct N X hX ⟨n, hn⟩) ⟨x₀, hx₀⟩ = σ ⟨x₀, hx₀⟩ := Subtype.ext hnx
  obtain ⟨k, hk, hkx⟩ := hstab ((conjAct N X hX ⟨n, hn⟩)⁻¹ * σ) (by
    rw [Equiv.Perm.mul_apply, ← han, Equiv.Perm.inv_def]
    exact Equiv.symm_apply_apply _ _)
  refine ⟨n * k, Subgroup.mul_mem _ hn (hKN hk), fun x => ?_⟩
  have h2 : σ x = (conjAct N X hX ⟨n, hn⟩) (((conjAct N X hX ⟨n, hn⟩)⁻¹ * σ) x) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have h3 := hkx x
  rw [h2, conjAct_apply, h3]
  group

theorem exists_perm_four_section {N W : Subgroup G} {X : Set G}
    (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hcard : Nat.card X = 4)
    (hsurj : Function.Surjective (conjAct N X hX))
    (hker : (conjAct N X hX).ker = W.subgroupOf N) :
    ∃ φ : ↥N →* Equiv.Perm (Fin 4), Function.Surjective φ ∧ φ.ker = W.subgroupOf N := by
  have : Fintype ↥X := Fintype.ofFinite _
  have hX' : Fintype.card ↥X = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let E : Equiv.Perm ↥X ≃* Equiv.Perm (Fin 4) :=
    Equiv.permCongrHom (Fintype.equivFinOfCardEq hX')
  refine ⟨E.toMonoidHom.comp (conjAct N X hX), E.surjective.comp hsurj, ?_⟩
  rw [← hker]
  ext n
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact map_eq_one_iff E E.injective

theorem card_eq_mul_of_section {V W : Subgroup G} (hWV : W ≤ V) {K : Type} [Group K]
    (ψ : ↥V →* K) (hs : Function.Surjective ψ) (hker : ψ.ker = W.subgroupOf V) :
    Nat.card V = Nat.card K * Nat.card W := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective hs
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv] at h1
  rw [← h1, mul_comm]

theorem nonempty_closure_dihedral {D : Type} [Group D] [Finite D] {ρ σ : D} (hσ : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ zpowers ρ) :
    Nonempty (closure ({ρ, σ} : Set D) ≃* DihedralGroup (orderOf ρ)) := by
  set H := closure ({ρ, σ} : Set D)
  have hρH : ρ ∈ H := subset_closure (by simp)
  have hσH : σ ∈ H := subset_closure (by simp)
  have hgen : (⊤ : Subgroup H) = zpowers ⟨ρ, hρH⟩ ⊔ zpowers ⟨σ, hσH⟩ := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union,
      ← closure_closure_coe_preimage (k := ({ρ, σ} : Set D))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (D := H) ⟨ρ, hρH⟩ ⟨σ, hσH⟩
    hgen (Subtype.ext (by simpa using hσ)) (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ
      (by
        obtain ⟨k, hk⟩ := (mem_zpowers_iff).mp hmem
        exact (mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h

theorem exists_dihedral_section {V W : Subgroup G} (hV2 : IsPGroup 2 V)
    {Φ : Type} [Group Φ] [Finite Φ] (hΦ : Nat.card Φ ∣ 24) (φ : ↥V →* Φ)
    (hker : φ.ker = W.subgroupOf V) {r s : ↥V} (hr : orderOf (φ r) = 4)
    (hs : φ s * φ s = 1) (hrel : φ s * φ r * (φ s)⁻¹ = (φ r)⁻¹) :
    ∃ ψ : ↥V →* DihedralGroup 4, Function.Surjective ψ ∧ ψ.ker = W.subgroupOf V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ2 : φ s ^ 2 = 1 := by
    rw [pow_two]
    exact hs
  have hnot : φ s ∉ zpowers (φ r) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hc : φ s * φ r * (φ s)⁻¹ = φ r := by
      rw [← hk]
      group
    have h2 : φ r * φ r = 1 := by
      have : φ r = (φ r)⁻¹ := hc.symm.trans hrel
      calc φ r * φ r = φ r * (φ r)⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel (φ r)
    have h4 : orderOf (φ r) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hr] at h4
    omega
  obtain ⟨e⟩ := nonempty_closure_dihedral hσ2 hrel hnot
  rw [hr] at e
  have hE8 : Nat.card ↥(closure ({φ r, φ s} : Set Φ)) = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hD2 : IsPGroup 2 ↥φ.range :=
    hV2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hDcard : Nat.card φ.range ∣ 8 := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hD2
    have h1 : Nat.card φ.range ∣ 24 := (Subgroup.card_subgroup_dvd_card _).trans hΦ
    rw [hm] at h1 ⊢
    have h2 : 2 ^ m ∣ 8 * 3 := h1
    exact Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)) h2
  have hle : closure ({φ r, φ s} : Set Φ) ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
    · rw [hg]
      exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have heq : closure ({φ r, φ s} : Set Φ) = φ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by
      have := Nat.le_of_dvd (by norm_num) hDcard
      omega)
  let ψ₀ : ↥V →* ↥(closure ({φ r, φ s} : Set Φ)) :=
    φ.codRestrict _ (fun v => by
      rw [heq]
      exact MonoidHom.mem_range.mpr ⟨v, rfl⟩)
  have hψ₀surj : Function.Surjective ψ₀ := by
    intro x
    have hx : (x : Φ) ∈ φ.range := by
      rw [← heq]
      exact x.2
    obtain ⟨v, hv⟩ := hx
    exact ⟨v, Subtype.ext hv⟩
  refine ⟨e.toMonoidHom.comp ψ₀, e.surjective.comp hψ₀surj, ?_⟩
  rw [← hker]
  ext v
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [map_eq_one_iff e e.injective]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
