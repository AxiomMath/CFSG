module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLift
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

variable {L G' : Type*} [Group L] [Group G']

theorem commutatorElement_mul_of_central_left {r d : L} (hd : d ∈ Subgroup.center L) (b : L) :
    ⁅r * d, b⁆ = ⁅r, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hd b
  rw [commutatorElement_def, commutatorElement_def]
  calc r * d * b * (r * d)⁻¹ * b⁻¹ = r * (d * b * d⁻¹) * r⁻¹ * b⁻¹ := by group
    _ = r * b * r⁻¹ * b⁻¹ := by rw [← h, mul_inv_cancel_right]

theorem commutatorElement_mul_of_central_right (a : L) {r d : L}
    (hd : d ∈ Subgroup.center L) : ⁅a, r * d⁆ = ⁅a, r⁆ := by
  have h := Subgroup.mem_center_iff.mp hd a⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (r * d) * a⁻¹ * (r * d)⁻¹ = a * r * (d * a⁻¹ * d⁻¹) * r⁻¹ := by group
    _ = a * r * a⁻¹ * r⁻¹ := by rw [← h, mul_inv_cancel_right]

theorem card_ker_le_two_of_index_three [Finite L] {x y : L} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hgen : Subgroup.closure {x, y} = ⊤) (ψ : L →* G') (hDZ : ψ.ker ≤ Subgroup.center L)
    (hD2 : IsPGroup 2 ψ.ker) {W : Subgroup G'} (huW : ψ (x * y) ∈ W) (hvW : ψ (y * x) ∈ W)
    (hW : ∀ w ∈ W, w = 1 ∨ w = ψ (x * y) ∨ w = ψ (y * x) ∨ w = ψ (x * y) * ψ (y * x))
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hS3 : (W.comap ψ).index = 3) :
    Nat.card ψ.ker ≤ 2 := by
  classical
  set S := W.comap ψ with hSdef
  set u := x * y
  set v := y * x
  have hDS : ψ.ker ≤ S := fun d hd => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hd]
    exact W.one_mem
  have hsq : ∀ s ∈ S, s ^ 2 ∈ ψ.ker := fun s hs => by
    rw [MonoidHom.mem_ker, map_pow]
    exact hW2 _ hs
  have hS2 : IsPGroup 2 S := fun s => by
    obtain ⟨k, hk⟩ := hD2 ⟨(s : L) ^ 2, hsq s s.2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at hk' ⊢
    rw [pow_succ', pow_mul, hk']
  have : S.FiniteIndex := ⟨by rw [hS3]; norm_num⟩
  set V := (Abelianization.of (G := S)).transfer
  have hA2 : IsPGroup 2 (Abelianization S) :=
    hS2.of_surjective Abelianization.of (QuotientGroup.mk'_surjective _)
  have hVx : ∀ g : L, g ^ 3 = 1 → V g = 1 := fun g hg =>
    eq_one_of_pow_three_eq_one_of_isPGroup hA2 (by rw [← map_pow, hg, map_one])
  have hV : ∀ g : L, V g = 1 := by
    have hle : Subgroup.closure {x, y} ≤ V.ker := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact hVx _ hx
      · exact hVx _ hy
    rw [hgen] at hle
    exact fun g => hle (Subgroup.mem_top g)
  have hDcomm : ∀ d (hd : d ∈ ψ.ker), (⟨d, hDS hd⟩ : S) ∈ commutator S := by
    intro d hd
    have hdc := Subgroup.mem_center_iff.mp (hDZ hd)
    have hpow := MonoidHom.transfer_eq_pow (Abelianization.of (G := S)) d fun k g₀ _ => by
      have hc : d ^ k ∈ Subgroup.center L := Subgroup.pow_mem _ (hDZ hd) k
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hc g₀, inv_mul_cancel_left]
    rw [hV d] at hpow
    have h3 : (Abelianization.of (⟨d, hDS hd⟩ : S)) ^ 3 = 1 := by
      rw [← map_pow]
      convert hpow.symm using 2
      refine Subtype.ext ?_
      change d ^ 3 = d ^ S.index
      rw [hS3]
    have h1 := eq_one_of_pow_three_eq_one_of_isPGroup hA2 h3
    rw [← Abelianization.ker_of]
    exact h1
  have hrep : ∀ s ∈ S, ∃ r : L, (r = 1 ∨ r = u ∨ r = v ∨ r = u * v) ∧ r⁻¹ * s ∈ ψ.ker := by
    intro s hs
    have hker : ∀ r : L, ψ s = ψ r → r⁻¹ * s ∈ ψ.ker := fun r h => by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h]
      exact inv_mul_cancel _
    rcases hW _ hs with h | h | h | h
    · exact ⟨1, Or.inl rfl, hker 1 (by rw [h, map_one])⟩
    · exact ⟨u, Or.inr (Or.inl rfl), hker u h⟩
    · exact ⟨v, Or.inr (Or.inr (Or.inl rfl)), hker v h⟩
    · exact ⟨u * v, Or.inr (Or.inr (Or.inr rfl)), hker (u * v) (by
        rw [h]
        exact (map_mul ψ u v).symm)⟩
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => by
    have hinv : ∀ w ∈ W, w⁻¹ = w := fun w hw =>
      inv_eq_of_mul_eq_one_right (by rw [← sq, hW2 w hw])
    rw [← hinv _ (W.mul_mem ha hb), mul_inv_rev, hinv a ha, hinv b hb]
  have hcommD : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ ψ.ker := fun s hs t ht => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hWcomm _ hs _ ht
  set c := ⁅u, v⁆
  have hcD : c ∈ ψ.ker := hcommD u huW v hvW
  have hc2 : c ^ 2 = 1 := by
    have hu2 : u * u ∈ Subgroup.center L := hDZ (by rw [← sq]; exact hsq u huW)
    have h := Subgroup.mem_center_iff.mp (hDZ hcD) u
    have e : ⁅u * u, v⁆ = u * c * u⁻¹ * c := by
      simp only [c, commutatorElement_def]
      group
    rw [h, mul_inv_cancel_right] at e
    rw [sq, ← e]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hu2 v).symm
  have hcc := Subgroup.mem_center_iff.mp (hDZ hcD)
  have hvu : ⁅v, u⁆ = c⁻¹ := (commutatorElement_inv u v).symm
  have hu_uv : ⁅u, u * v⁆ = c := by
    have e : ⁅u, u * v⁆ = u * c * u⁻¹ := by
      simp only [c, commutatorElement_def]
      group
    rw [e, hcc u, mul_inv_cancel_right]
  have hv_uv : ⁅v, u * v⁆ = c⁻¹ := by
    have e : ⁅v, u * v⁆ = ⁅v, u⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hvu]
  have huv_u : ⁅u * v, u⁆ = c⁻¹ := by rw [← commutatorElement_inv, hu_uv]
  have huv_v : ⁅u * v, v⁆ = c := by rw [← commutatorElement_inv, hv_uv, inv_inv]
  have hcomm_le : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ Subgroup.zpowers c := by
    intro s hs t ht
    obtain ⟨r, hr, hrd⟩ := hrep s hs
    obtain ⟨r', hr', hrd'⟩ := hrep t ht
    rw [← mul_inv_cancel_left r s, ← mul_inv_cancel_left r' t,
      commutatorElement_mul_of_central_left (hDZ hrd),
      commutatorElement_mul_of_central_right _ (hDZ hrd')]
    have m1 : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
    have m2 : c⁻¹ ∈ Subgroup.zpowers c := Subgroup.inv_mem _ m1
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;>
      (try simp only [commutatorElement_one_left, commutatorElement_one_right,
        commutatorElement_self, hvu, hu_uv, hv_uv, huv_u, huv_v]) <;>
      first | exact Subgroup.one_mem _ | exact m1 | exact m2
  have hS'le : (commutator S).map S.subtype ≤ Subgroup.zpowers c := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact Subgroup.commutator_le.mpr hcomm_le
  have hDle : ψ.ker ≤ Subgroup.zpowers c := fun d hd =>
    hS'le ⟨⟨d, hDS hd⟩, hDcomm d hd, rfl⟩
  calc Nat.card ψ.ker ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hDle
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hc2

end CFSG.LocalAnalysis.ComponentInitial
