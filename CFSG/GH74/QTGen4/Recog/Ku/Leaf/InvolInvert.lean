module

public import CFSG.GH74.QTGen4.Recog.Ku.NInvolutionsC
public import CFSG.GH74.QTGen4.Recog.Ku.NInvolutions
public import Certificates.Data.A5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

private theorem perm5_invert : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 → Equiv.Perm.sign σ = 1 →
    ∃ τ : Equiv.Perm (Fin 5), τ * τ = 1 ∧ Equiv.Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

private theorem lamS_invert : ∀ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 → σ ∈ lamS →
    ∃ τ : Equiv.Perm (Fin 6), τ * τ = 1 ∧ τ ∈ lamS ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

private abbrev stabAlt : Subgroup (Equiv.Perm (Fin 6)) := stabS ⊓ alternatingGroup (Fin 6)

private instance : DecidablePred (· ∈ stabAlt) := fun σ =>
  decidable_of_iff (σ ∈ stabS ∧ Equiv.Perm.sign σ = 1)
    (by simp [stabAlt, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, and_comm])

private theorem card_stabAlt : Nat.card stabAlt = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem stabAlt_invert : ∀ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 → σ ∈ stabAlt →
    ∃ τ : Equiv.Perm (Fin 6), τ * τ = 1 ∧ τ ∈ stabAlt ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

private theorem lamS_fpf : ∀ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 → σ ∈ lamS →
    σ = 1 ∨ ∀ v : SpV, actS6 σ v = v → v = 0 := by
  decide +kernel

private theorem cent_exp3 : ∀ a : Equiv.Perm (Fin 6), a ^ 3 = 1 → a ∈ lamS → a ∈ stabS → a = 1 ∨
    ∀ c : Equiv.Perm (Fin 6), c ^ 3 = 1 ∨ Equiv.Perm.sign c ≠ 1 ∨ a * c ≠ c * a := by
  decide +kernel

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_invol_inverting_of_mod {X K : Subgroup G}
    (hKX : X ≤ Subgroup.normalizer (K : Set G)) (hK2 : IsPGroup 2 K)
    {y : G} (hyX : y ∈ X) (hy3 : orderOf y = 3)
    (hfpf : ∀ k ∈ K, y * k = k * y → k = 1)
    {x₀ : G} (hx₀X : x₀ ∈ X) (hx₀y : y * (x₀ * y * x₀⁻¹) ∈ K) (hx₀sq : x₀ * x₀ ∈ K) :
    ∃ x ∈ X, x * x = 1 ∧ x * y * x⁻¹ = y⁻¹ := by
  have hconj : ∀ g ∈ X, ∀ k : G, g * k * g⁻¹ ∈ K ↔ k ∈ K := fun g hg k =>
    (Subgroup.mem_normalizer_iff.mp (hKX hg) k).symm
  have hF : ∀ k : ↥(K ⊓ X), y * (k : G)⁻¹ * y⁻¹ * k ∈ K ⊓ X := by
    intro k
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp k.2
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem ?_ hk1, ?_⟩
    · exact (hconj y hyX _).mpr (K.inv_mem hk1)
    · exact X.mul_mem (X.mul_mem (X.mul_mem hyX (X.inv_mem hk2)) (X.inv_mem hyX)) hk2
  let F : ↥(K ⊓ X) → ↥(K ⊓ X) := fun k => ⟨y * (k : G)⁻¹ * y⁻¹ * k, hF k⟩
  have hinj : Function.Injective F := by
    intro k m hkm
    have h1 : y * (k : G)⁻¹ * y⁻¹ * k = y * (m : G)⁻¹ * y⁻¹ * m := congrArg Subtype.val hkm
    have hu : (m : G) * (k : G)⁻¹ ∈ K :=
      K.mul_mem (Subgroup.mem_inf.mp m.2).1 (K.inv_mem (Subgroup.mem_inf.mp k.2).1)
    have hc : y * ((m : G) * (k : G)⁻¹) * y⁻¹ = (m : G) * (k : G)⁻¹ := by
      calc y * ((m : G) * (k : G)⁻¹) * y⁻¹
          = (y * m * y⁻¹) * (y * (k : G)⁻¹ * y⁻¹ * k) * (k : G)⁻¹ := by group
        _ = (y * m * y⁻¹) * (y * (m : G)⁻¹ * y⁻¹ * m) * (k : G)⁻¹ := by rw [h1]
        _ = (m : G) * (k : G)⁻¹ := by group
    have h2 : (m : G) * (k : G)⁻¹ = 1 := hfpf _ hu (mul_inv_eq_iff_eq_mul.mp hc)
    exact Subtype.ext (mul_inv_eq_one.mp h2).symm
  have hk₀ : y * (x₀ * y * x₀⁻¹) ∈ K ⊓ X :=
    Subgroup.mem_inf.mpr ⟨hx₀y, X.mul_mem hyX (X.mul_mem (X.mul_mem hx₀X hyX) (X.inv_mem hx₀X))⟩
  obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.mp hinj ⟨_, hk₀⟩
  have hk' : y * (k : G)⁻¹ * y⁻¹ * k = y * (x₀ * y * x₀⁻¹) := congrArg Subtype.val hk
  have key : (k : G) * (x₀ * y * x₀⁻¹) * (k : G)⁻¹ = y⁻¹ := by
    have h3 : y * ((k : G)⁻¹ * y⁻¹ * k) = y * (x₀ * y * x₀⁻¹) := by rw [← hk']; group
    have h2 : (k : G)⁻¹ * y⁻¹ * k = x₀ * y * x₀⁻¹ := mul_left_cancel h3
    rw [← h2]; group
  obtain ⟨hkK, hkX⟩ := Subgroup.mem_inf.mp k.2
  have hxX : (k : G) * x₀ ∈ X := X.mul_mem hkX hx₀X
  have hxy : (k : G) * x₀ * y * ((k : G) * x₀)⁻¹ = y⁻¹ := by
    rw [← key]; group
  have hxsq : (k : G) * x₀ * ((k : G) * x₀) ∈ K := by
    have e : (k : G) * x₀ * ((k : G) * x₀) = (k : G) * (x₀ * (k : G) * x₀⁻¹) * (x₀ * x₀) := by
      group
    rw [e]
    exact K.mul_mem (K.mul_mem hkK ((hconj x₀ hx₀X _).mpr hkK)) hx₀sq
  refine ⟨(k : G) * x₀, hxX, ?_, hxy⟩
  set x : G := (k : G) * x₀ with hx
  apply hfpf _ hxsq
  have h4 : x * y = y⁻¹ * x := mul_inv_eq_iff_eq_mul.mp hxy
  have h5 : x * y⁻¹ = y * x := by
    have := congrArg (·⁻¹) hxy
    simp only [mul_inv_rev, inv_inv, mul_assoc] at this
    calc x * y⁻¹ = (x * (y⁻¹ * x⁻¹)) * x := by group
      _ = y * x := by rw [this]
  calc y * (x * x) = (y * x) * x := by group
    _ = (x * y⁻¹) * x := by rw [h5]
    _ = x * (y⁻¹ * x) := by group
    _ = x * (x * y) := by rw [h4]
    _ = (x * x) * y := by group

omit [Finite G] in
private theorem mul_self_of_mem_E {E W V2 N : Subgroup G} {z : G}
    (Ψ : KuA6Model E W V2 N z) {a : G} (ha : a ∈ E) : a * a = 1 := by
  obtain ⟨u, rfl⟩ := Ψ.surj a ha
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  have hu : u + u = 0 := funext fun i => hz (u i)
  rw [← Ψ.add, hu, Ψ.Φ_zero]

omit [Finite G] in
private theorem pi_pow_three {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z) {y : G}
    (hyN : y ∈ N) (hy3 : orderOf y = 3) : Ψ.π ⟨y, hyN⟩ ^ 3 = 1 := by
  have h3 : (⟨y, hyN⟩ : ↥N) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy3]
    exact pow_orderOf_eq_one y
  rw [← map_pow, h3, map_one]

omit [Finite G] in
private theorem pi_ne_one {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z) {y : G}
    (hyN : y ∈ N) (hy3 : orderOf y = 3) : Ψ.π ⟨y, hyN⟩ ≠ 1 := by
  intro h1
  have hyE : y ∈ E := (Ψ.ker ⟨y, hyN⟩).mp h1
  have h2 : orderOf y ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact mul_self_of_mem_E Ψ hyE)
  rw [hy3] at h2
  norm_num at h2

omit [Finite G] in
private theorem fpf_of_mem_L2 {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z) {y : G}
    (hyL2 : y ∈ Ψ.L2) (hy3 : orderOf y = 3) : ∀ k ∈ E, y * k = k * y → k = 1 := by
  obtain ⟨hyN, hyπ⟩ := (Ψ.mem_pre_iff lamS).mp hyL2
  have hne := pi_ne_one Ψ hyN hy3
  have hcube := pi_pow_three Ψ hyN hy3
  intro k hk hyk
  obtain ⟨v, rfl⟩ := Ψ.surj k hk
  have h1 : y * Ψ.Φ v * y⁻¹ = Ψ.Φ v := by rw [hyk, mul_inv_cancel_right]
  have h2 : Ψ.Φ (actS6 (Ψ.π ⟨y, hyN⟩) v) = Ψ.Φ v := by rw [← Ψ.act ⟨y, hyN⟩ v]; exact h1
  have hv : v = 0 := by
    rcases lamS_fpf _ hcube hyπ with h | h
    · exact absurd h hne
    · exact h v (Ψ.inj h2)
  rw [hv, Ψ.Φ_zero]

private theorem invol_of_lift
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {X : Subgroup G}
    (hXN : X ≤ kuN P H) {y : G} (hyX : y ∈ X) (hy3 : orderOf y = 3)
    (hfpf : ∀ k ∈ kuA P H, y * k = k * y → k = 1)
    {τ : Equiv.Perm (Fin 6)} {x₀ : G} (hx₀X : x₀ ∈ X) (hx₀τ : Ψ.π ⟨x₀, hXN hx₀X⟩ = τ)
    (hτ2 : τ * τ = 1)
    (hτy : τ * Ψ.π ⟨y, hXN hyX⟩ * τ⁻¹ = (Ψ.π ⟨y, hXN hyX⟩)⁻¹) :
    ∃ x ∈ X, x * x = 1 ∧ x * y * x⁻¹ = y⁻¹ := by
  have hK2 : IsPGroup 2 (kuA P H) := IsPGroup.of_card (n := 4) (by rw [Ψ.card_E]; norm_num)
  refine exists_invol_inverting_of_mod hXN hK2 hyX hy3 hfpf hx₀X ?_ ?_
  · have h1 : Ψ.π (⟨y, hXN hyX⟩ * (⟨x₀, hXN hx₀X⟩ * ⟨y, hXN hyX⟩ * ⟨x₀, hXN hx₀X⟩⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hx₀τ, hτy]
      exact mul_inv_cancel _
    exact (Ψ.ker _).mp h1
  · have h1 : Ψ.π (⟨x₀, hXN hx₀X⟩ * ⟨x₀, hXN hx₀X⟩) = 1 := by
      rw [map_mul, hx₀τ, hτ2]
    exact (Ψ.ker _).mp h1

private theorem pre_stabAlt_eq [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    Ψ.pre stabAlt = M ⊓ Subgroup.normalizer (kuV2 T M : Set G) := by
  have hle : M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ≤ Ψ.pre stabAlt := by
    intro x hx
    have hxN : x ∈ kuN P H := h.M_inf_normalizer_V2_le_kuN hx
    exact (Ψ.mem_pre_iff _).mpr ⟨hxN, Subgroup.mem_inf.mpr
      ⟨pi_mem_stabS_of_normalizer Ψ hxN hx.2, Ψ.π_alt _⟩⟩
  have hcard : Nat.card ↥(Ψ.pre stabAlt) =
      Nat.card ↥(M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) := by
    rw [h.card_pre Ψ inf_le_right, card_stabAlt, h.card_M_inf_normalizer_kuV2]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

private theorem mem_X_of_mem_L2 [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {y : G}
    (hy : y ∈ oTwoUpper M ⊓ Ψ.L2) :
    y ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) := by
  have h1 : y ∈ oTwoUpper M ⊓ kuN P H :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, Ψ.pre_le_N lamS (Subgroup.mem_inf.mp hy).2⟩
  rwa [h.oTwoUpper_inf_kuN_eq] at h1

theorem exists_t_inverting
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {y : G}
    (hy : y ∈ oTwoUpper M ⊓ Ψ.L2) (hy3 : orderOf y = 3) :
    ∃ t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G), t * t = 1 ∧ t * y * t⁻¹ = y⁻¹ := by
  have hyL2 : y ∈ Ψ.L2 := (Subgroup.mem_inf.mp hy).2
  obtain ⟨hyN, -⟩ := (Ψ.mem_pre_iff lamS).mp hyL2
  have hyX : y ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) := by
    have h1 := mem_X_of_mem_L2 h Ψ hy
    exact ⟨oTwoUpper_le M h1.1, h1.2⟩
  have hXN : M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ≤ kuN P H :=
    h.M_inf_normalizer_V2_le_kuN
  have hσ : Ψ.π ⟨y, hyN⟩ ∈ stabAlt :=
    Subgroup.mem_inf.mpr ⟨pi_mem_stabS_of_normalizer Ψ hyN hyX.2, Ψ.π_alt _⟩
  obtain ⟨τ, hτ2, hτ, hτy⟩ := stabAlt_invert _ (pi_pow_three Ψ hyN hy3) hσ
  obtain ⟨n, hn⟩ := Ψ.π_surj τ (Subgroup.mem_inf.mp hτ).2
  have hnX : (n : G) ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) := by
    rw [← pre_stabAlt_eq h Ψ]
    exact (Ψ.mem_pre_iff _).mpr ⟨n.2, by
      show Ψ.π n ∈ _
      rw [hn]; exact hτ⟩
  exact invol_of_lift Ψ hXN hyX hy3 (fpf_of_mem_L2 Ψ hyL2 hy3) hnX hn hτ2 hτy

theorem exists_j_inverting
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {y : G}
    (hy : y ∈ oTwoUpper M ⊓ Ψ.L2) (hy3 : orderOf y = 3) :
    ∃ j ∈ Ψ.L2, j * j = 1 ∧ j * y * j⁻¹ = y⁻¹ := by
  have hyL2 : y ∈ Ψ.L2 := (Subgroup.mem_inf.mp hy).2
  obtain ⟨hyN, hyπ⟩ := (Ψ.mem_pre_iff lamS).mp hyL2
  obtain ⟨τ, hτ2, hτ, hτy⟩ := lamS_invert _ (pi_pow_three Ψ hyN hy3) hyπ
  obtain ⟨x₀, hx₀L, _, hx₀τ⟩ := Ψ.exists_lift_lamS hτ
  exact invol_of_lift Ψ (Ψ.pre_le_N lamS) hyL2 hy3 (fpf_of_mem_L2 Ψ hyL2 hy3) hx₀L hx₀τ hτ2 hτy

theorem exists_t₁_inverting (h : KuHyp G T M H P z) {y : G} (hy : y ∈ oTwoUpper M)
    (hy3 : orderOf y = 3) :
    ∃ t₁ ∈ oTwoUpper M, t₁ * t₁ = 1 ∧ t₁ * y * t₁⁻¹ = y⁻¹ := by
  obtain ⟨φ, hφs, hker⟩ := h.mQuot
  have hyM : y ∈ M := oTwoUpper_le M hy
  have hmem : ∀ x : ↥M, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 M := fun x => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hσalt : φ ⟨y, hyM⟩ ∈ alternatingGroup (Fin 5) := by
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (oTwoUpper_le_map_comap φ hy)
    have hwe : w = ⟨y, hyM⟩ := Subtype.ext hwx
    rw [← hwe]
    exact hw
  have hy3M : (⟨y, hyM⟩ : ↥M) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy3]
    exact pow_orderOf_eq_one y
  have hσ3 : φ ⟨y, hyM⟩ ^ 3 = 1 := by rw [← map_pow, hy3M, map_one]
  obtain ⟨τ, hτ2, hτa, hτσ⟩ := perm5_invert _ hσ3 (Equiv.Perm.mem_alternatingGroup.mp hσalt)
  obtain ⟨m, hm, hmτ⟩ := Subgroup.mem_map.mp
    (alt_le_map_subgroupOf h hφs (Equiv.Perm.mem_alternatingGroup.mpr hτa))
  have hmL : (m : G) ∈ oTwoUpper M := Subgroup.mem_subgroupOf.mp hm
  have hK2 : IsPGroup 2 (pCoreOf 2 M) := IsPGroup.of_card (n := 4) (by rw [h.vCard]; norm_num)
  refine exists_invol_inverting_of_mod (h.oTwoUpper_le_normalizer_V) hK2 hy hy3
    (fun k hk hyk => h.fpf_of_order_three hy hy3 hk (by rw [hyk, mul_inv_cancel_right]))
    hmL ?_ ?_
  · have h1 : φ (⟨y, hyM⟩ * (m * ⟨y, hyM⟩ * m⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hmτ, hτσ]
      exact mul_inv_cancel _
    exact (hmem _).mp h1
  · have h1 : φ (m * m) = 1 := by rw [map_mul, hmτ, hτ2]
    exact (hmem _).mp h1

theorem cube_of_inverting
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {y t j : G}
    (hy3 : orderOf y = 3) (hyL : y ∈ oTwoUpper M ⊓ Ψ.L2)
    (ht : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (hty : t * y * t⁻¹ = y⁻¹)
    (hj : j ∈ Ψ.L2) (hjy : j * y * j⁻¹ = y⁻¹) : (t * j) ^ 3 = 1 := by
  have hyL2 : y ∈ Ψ.L2 := (Subgroup.mem_inf.mp hyL).2
  obtain ⟨hyN, hyπ⟩ := (Ψ.mem_pre_iff lamS).mp hyL2
  have hyX := mem_X_of_mem_L2 h Ψ hyL
  have hstab := pi_mem_stabS_of_normalizer Ψ hyN hyX.2
  have htN : t ∈ kuN P H := h.M_inf_normalizer_V2_le_kuN ht
  have hjN : j ∈ kuN P H := Ψ.pre_le_N lamS hj
  have hcN : t * j ∈ kuN P H := Subgroup.mul_mem _ htN hjN
  have hcy : (t * j) * y * (t * j)⁻¹ = y := by
    calc (t * j) * y * (t * j)⁻¹ = t * (j * y * j⁻¹) * t⁻¹ := by group
      _ = t * y⁻¹ * t⁻¹ := by rw [hjy]
      _ = (t * y * t⁻¹)⁻¹ := by group
      _ = y := by rw [hty, inv_inv]
  have hcomm : y * (t * j) = (t * j) * y := (mul_inv_eq_iff_eq_mul.mp hcy).symm
  have hπc : Ψ.π ⟨y, hyN⟩ * Ψ.π ⟨t * j, hcN⟩ = Ψ.π ⟨t * j, hcN⟩ * Ψ.π ⟨y, hyN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ.π (Subtype.ext hcomm)
  have hc3 : Ψ.π ⟨t * j, hcN⟩ ^ 3 = 1 := by
    rcases cent_exp3 _ (pi_pow_three Ψ hyN hy3) hyπ hstab with h1 | h1
    · exact absurd h1 (pi_ne_one Ψ hyN hy3)
    · rcases h1 (Ψ.π ⟨t * j, hcN⟩) with h2 | h2 | h2
      · exact h2
      · exact absurd (Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt _)) h2
      · exact absurd hπc h2
  have hc3E : (t * j) ^ 3 ∈ kuA P H := by
    refine (Ψ.ker ⟨(t * j) ^ 3, Subgroup.pow_mem _ hcN 3⟩).mp ?_
    have : (⟨(t * j) ^ 3, Subgroup.pow_mem _ hcN 3⟩ : ↥(kuN P H)) = ⟨t * j, hcN⟩ ^ 3 := rfl
    rw [this, map_pow, hc3]
  exact fpf_of_mem_L2 Ψ hyL2 hy3 _ hc3E (Commute.pow_right (show Commute y (t * j) from hcomm) 3).eq

end KuHyp

end CFSG.GH74.QTGen4.Ku
