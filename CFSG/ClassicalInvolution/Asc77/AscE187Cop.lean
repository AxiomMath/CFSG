module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {Γ : Type*} [Group Γ]

theorem relIndex_sup_dvd_card_of_normal [Finite Γ] (A N : Subgroup Γ) [N.Normal] :
    A.relIndex (A ⊔ N) ∣ Nat.card N := by
  have h1 : (A ⊓ N).relIndex A * A.relIndex (A ⊔ N) = (A ⊓ N).relIndex (A ⊔ N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (A ⊓ N).relIndex N * N.relIndex (A ⊔ N) = (A ⊓ N).relIndex (A ⊔ N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : N.relIndex (A ⊔ N) = N.relIndex A := Subgroup.relIndex_sup_right A N
  have h4 : (A ⊓ N).relIndex A = N.relIndex A := Subgroup.inf_relIndex_left A N
  have h5 : N.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h6 : A.relIndex (A ⊔ N) = (A ⊓ N).relIndex N := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5) ?_
    rw [← h4] at h5 ⊢
    calc (A ⊓ N).relIndex A * A.relIndex (A ⊔ N) = (A ⊓ N).relIndex (A ⊔ N) := h1
      _ = (A ⊓ N).relIndex N * N.relIndex (A ⊔ N) := h2.symm
      _ = (A ⊓ N).relIndex A * (A ⊓ N).relIndex N := by rw [h3, ← h4, mul_comm]
  rw [h6]
  exact Subgroup.relIndex_dvd_card _ _

theorem exists_conj_mem_of_mem_sup_of_odd [Finite Γ] {A N : Subgroup Γ} [N.Normal]
    (hN : Odd (Nat.card N)) {u : Γ} (hu : IsPGroup 2 (Subgroup.zpowers u)) (huAN : u ∈ A ⊔ N) :
    ∃ n ∈ N, n * u * n⁻¹ ∈ A := by
  classical
  set B : Subgroup Γ := A ⊔ N with hB
  set u' : ↥B := ⟨u, huAN⟩ with hu'
  have hodd : Odd (A.subgroupOf B).index := by
    have : (A.subgroupOf B).index = A.relIndex B := rfl
    rw [this]
    exact hN.of_dvd_nat (relIndex_sup_dvd_card_of_normal A N)
  obtain ⟨k, hk⟩ := hu.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hu'k : u' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simp only [hu', Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk]
    exact pow_orderOf_eq_one u
  have : Fintype (↥B ⧸ A.subgroupOf B) := Fintype.ofFinite _
  have hσ : (MulAction.toPermHom ↥B (↥B ⧸ A.subgroupOf B) u') ^ 2 ^ k = 1 := by
    rw [← map_pow, hu'k, map_one]
  have hcard : ¬ 2 ∣ Fintype.card (↥B ⧸ A.subgroupOf B) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) hcard hσ
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix : (↑(u' * b) : ↥B ⧸ A.subgroupOf B) = ↑b := hx
  rw [QuotientGroup.eq] at hfix
  have hbA : (b : Γ)⁻¹ * u * (b : Γ) ∈ A := by
    have h1 : (b : Γ)⁻¹ * u * (b : Γ) = (((u' * b)⁻¹ * b)⁻¹ : ↥B) := by
      simp only [hu', Subgroup.coe_inv, Subgroup.coe_mul]
      group
    have h2 := (A.subgroupOf B).inv_mem hfix
    rw [Subgroup.mem_subgroupOf] at h2
    rw [h1]
    exact h2
  have hbinv : (b : Γ)⁻¹ ∈ A ⊔ N := B.inv_mem b.2
  obtain ⟨a₀, ha₀, n₀, hn₀, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hbinv
  refine ⟨n₀, hn₀, ?_⟩
  have hb : (b : Γ) = n₀⁻¹ * a₀⁻¹ := by
    have : (b : Γ) = ((b : Γ)⁻¹)⁻¹ := (inv_inv _).symm
    rw [this, ← hab]
    group
  have h3 : a₀⁻¹ * ((b : Γ)⁻¹ * u * (b : Γ)) * a₀ = n₀ * u * n₀⁻¹ := by
    rw [hb]
    group
  rw [← h3]
  exact A.mul_mem (A.mul_mem (A.inv_mem ha₀) hbA) ha₀

theorem exists_mul_mem_centralizer_of_odd [Finite Γ] {N : Subgroup Γ} [N.Normal]
    (hN : Odd (Nat.card N)) {δ x : Γ} (hδ : δ * δ = 1) (hx : x⁻¹ * (δ * x * δ⁻¹) ∈ N) :
    ∃ n ∈ N, δ * (x * n) = (x * n) * δ := by
  classical
  have hmap : ∀ y : Γ, x⁻¹ * y ∈ N → x⁻¹ * (δ * y * δ⁻¹) ∈ N := by
    intro y hy
    have e : x⁻¹ * (δ * y * δ⁻¹) = (x⁻¹ * (δ * x * δ⁻¹)) * (δ * (x⁻¹ * y) * δ⁻¹) := by group
    rw [e]
    exact N.mul_mem hx (Subgroup.Normal.conj_mem inferInstance _ hy δ)
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ
  let σ : Equiv.Perm {y : Γ // x⁻¹ * y ∈ N} :=
    { toFun := fun y => ⟨δ * y.1 * δ⁻¹, hmap _ y.2⟩
      invFun := fun y => ⟨δ * y.1 * δ⁻¹, hmap _ y.2⟩
      left_inv := fun y => by
        apply Subtype.ext
        show δ * (δ * y.1 * δ⁻¹) * δ⁻¹ = y.1
        rw [hδi]
        calc δ * (δ * y.1 * δ) * δ = (δ * δ) * y.1 * (δ * δ) := by group
          _ = y.1 := by rw [hδ]; group
      right_inv := fun y => by
        apply Subtype.ext
        show δ * (δ * y.1 * δ⁻¹) * δ⁻¹ = y.1
        rw [hδi]
        calc δ * (δ * y.1 * δ) * δ = (δ * δ) * y.1 * (δ * δ) := by group
          _ = y.1 := by rw [hδ]; group }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext y
    show δ * (δ * y.1 * δ⁻¹) * δ⁻¹ = y.1
    rw [hδi]
    calc δ * (δ * y.1 * δ) * δ = (δ * δ) * y.1 * (δ * δ) := by group
      _ = y.1 := by rw [hδ]; group
  have : Fintype {y : Γ // x⁻¹ * y ∈ N} := Fintype.ofFinite _
  have hcardeq : Nat.card {y : Γ // x⁻¹ * y ∈ N} = Nat.card N :=
    Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨x * n.1, by simp⟩
        left_inv := fun y => by apply Subtype.ext; simp
        right_inv := fun n => by apply Subtype.ext; simp }
  have hcard : ¬ 2 ∣ Fintype.card {y : Γ // x⁻¹ * y ∈ N} := by
    rw [← Nat.card_eq_fintype_card, hcardeq]
    exact fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) hcard hσ2
  have hy' : δ * y.1 * δ⁻¹ = y.1 := congrArg Subtype.val hy
  refine ⟨x⁻¹ * y.1, y.2, ?_⟩
  have e : x * (x⁻¹ * y.1) = y.1 := by group
  rw [e]
  exact (mul_inv_eq_iff_eq_mul.mp hy')

end CFSG.ClassicalInvolution.Asc77
