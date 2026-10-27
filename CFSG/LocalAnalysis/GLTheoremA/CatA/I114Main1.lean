module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114W

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem cj_map_subtype {K : Subgroup Y} (a : ↥K) (U : Subgroup ↥K) :
    cj (a : Y) (U.map K.subtype) = (cj a U).map K.subtype := by
  ext z
  rw [mem_cj, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hue⟩
    refine ⟨a * u * a⁻¹, ?_, ?_⟩
    · rw [mem_cj]
      have e : a⁻¹ * (a * u * a⁻¹) * a = u := by group
      rw [e]
      exact hu
    · show ((a * u * a⁻¹ : ↥K) : Y) = z
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hz : (u : Y) = (a : Y)⁻¹ * z * (a : Y) := by
        rw [← hue]
        rfl
      rw [hz]
      group
  · rintro ⟨w, hw, hwz⟩
    rw [mem_cj] at hw
    refine ⟨a⁻¹ * w * a, hw, ?_⟩
    rw [← hwz]
    rfl

theorem isPGroup_cj {p : ℕ} {V : Subgroup Y} (hV : IsPGroup p V) (g : Y) :
    IsPGroup p ↥(cj g V) := by
  intro w
  obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.1 w.2
  obtain ⟨n, hn⟩ := hV ⟨v, hv⟩
  have hv1 : v ^ p ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hvw, ← map_pow, hv1, map_one]

theorem elemCommute_of_le {A C A' C' : Subgroup Y} (hA : A ≤ A') (hC : C ≤ C')
    (h : ElemCommute A' C') : ElemCommute A C :=
  fun a ha c hc => h a (hA ha) c (hC hc)

theorem gen_B0 {B K U : Subgroup Y} {x β : Y} (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hβB : β ∈ B) (hβK : Cent K β) (hUK : U ≤ K) :
    β ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  have hβx : β * x = x * β := isElemAbelian_commute hB hβB hxB
  have h2 : Cent (cj x K) β := cent_cj hβx hβK
  have h3 : Cent (cj (x * x) K) β := by
    rw [show cj (x * x) K = cj x (cj x K) from (cj_mul x x K)]
    exact cent_cj hβx h2
  exact mem_normalizer_WU_of_cent hUK hβK h2 h3

theorem gen_m0 {B U : Subgroup Y} {x m : Y} (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hmB : m ∈ B)
    (hmU : cj m U = U) : m ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  have hmx : m * x = x * m := isElemAbelian_commute hB hmB hxB
  have hmxx : m * (x * x) = (x * x) * m := by
    rw [← mul_assoc, hmx, mul_assoc, hmx, ← mul_assoc]
  apply mem_normalizer_WU hmU
  · rw [cj_comm_cj hmx, hmU]
  · rw [cj_comm_cj hmxx, hmU]

theorem gen_y {K U : Subgroup Y} {x y : Y} (hKK₂ : ElemCommute K (cj x K))
    (hKK₃ : ElemCommute K (cj (x * x) K)) (hyK : y ∈ K) (hyU : cj y U = U) (hUK : U ≤ K) :
    y ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  have hg2 : Cent (cj x K) y := cent_of_elemCommute (commutes_symm hKK₂) hyK
  have hg3 : Cent (cj (x * x) K) y := cent_of_elemCommute (commutes_symm hKK₃) hyK
  apply mem_normalizer_WU hyU
  · exact cj_eq_of_cent (cent_of_le (cj_mono x hUK) hg2)
  · exact cj_eq_of_cent (cent_of_le (cj_mono (x * x) hUK) hg3)

theorem gen_y1 {K U : Subgroup Y} {x y : Y} (hKK₂ : ElemCommute K (cj x K))
    (hKK₃ : ElemCommute K (cj (x * x) K)) (hyK : y ∈ K) (hyU : cj y U = U) (hUK : U ≤ K) :
    x * y * x⁻¹ ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  have hy₁K : x * y * x⁻¹ ∈ cj x K := conj_mem_cj x hyK
  have f23 : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
  have hCK : Cent K (x * y * x⁻¹) := cent_of_elemCommute hKK₂ hy₁K
  have hC3 : Cent (cj (x * x) K) (x * y * x⁻¹) := cent_of_elemCommute (commutes_symm f23) hy₁K
  apply mem_normalizer_WU
  · exact cj_eq_of_cent (cent_of_le hUK hCK)
  · calc cj (x * y * x⁻¹) (cj x U) = cj (x * y * x⁻¹ * x) U := (cj_mul _ _ _).symm
      _ = cj (x * y) U := by rw [show x * y * x⁻¹ * x = x * y by group]
      _ = cj x (cj y U) := cj_mul _ _ _
      _ = cj x U := by rw [hyU]
  · exact cj_eq_of_cent (cent_of_le (cj_mono (x * x) hUK) hC3)

theorem gen_y2 {K U : Subgroup Y} {x y : Y} (hKK₂ : ElemCommute K (cj x K))
    (hKK₃ : ElemCommute K (cj (x * x) K)) (hyK : y ∈ K) (hyU : cj y U = U) (hUK : U ≤ K) :
    (x * x) * y * (x * x)⁻¹ ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  have hy₂K : (x * x) * y * (x * x)⁻¹ ∈ cj (x * x) K := conj_mem_cj (x * x) hyK
  have f23 : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
  have hCK : Cent K ((x * x) * y * (x * x)⁻¹) := cent_of_elemCommute hKK₃ hy₂K
  have hC2 : Cent (cj x K) ((x * x) * y * (x * x)⁻¹) := cent_of_elemCommute f23 hy₂K
  apply mem_normalizer_WU
  · exact cj_eq_of_cent (cent_of_le hUK hCK)
  · exact cj_eq_of_cent (cent_of_le (cj_mono x hUK) hC2)
  · calc cj ((x * x) * y * (x * x)⁻¹) (cj (x * x) U)
        = cj ((x * x) * y * (x * x)⁻¹ * (x * x)) U := (cj_mul _ _ _).symm
      _ = cj ((x * x) * y) U := by rw [show (x * x) * y * (x * x)⁻¹ * (x * x) = (x * x) * y by group]
      _ = cj (x * x) (cj y U) := cj_mul _ _ _
      _ = cj (x * x) U := by rw [hyU]

end CFSG.LocalAnalysis.GLTheoremA.I114
