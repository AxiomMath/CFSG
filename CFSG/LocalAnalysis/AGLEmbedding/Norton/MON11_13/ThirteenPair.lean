module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
public import Certificates.Certificate125500
public import Certificates.Certificate125501

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.RankThree.PartOne.StrongP
open scoped commutatorElement

section Algebra

variable {G : Type*} [Group G]

theorem inversion_conj {x a h : G} (hh : h * h = 1) (hha : Commute h a) (hhx : h * x * h = x⁻¹) :
    h * (a * x * a⁻¹) * h = (a * x * a⁻¹)⁻¹ := by
  have h1 : h * a = a * h := hha.eq
  have h2 : a⁻¹ * h = h * a⁻¹ := (hha.inv_right.eq).symm
  calc h * (a * x * a⁻¹) * h = (h * a) * x * (a⁻¹ * h) := by simp only [mul_assoc]
    _ = (a * h) * x * (h * a⁻¹) := by rw [h1, h2]
    _ = a * (h * x * h) * a⁻¹ := by simp only [mul_assoc]
    _ = a * x⁻¹ * a⁻¹ := by rw [hhx]
    _ = (a * x * a⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem heisenberg_inversion_of_subgroup {H : Subgroup G} {x a z t : G} (hxH : x ∈ H) (haH : a ∈ H)
    (hzH : z ∈ H) (htH : t ∈ H) (hx : x ^ 13 = 1) (hz : z ≠ 1) (hzx : Commute z x)
    (hza : Commute z a) (hcomm : ⁅x, a * x * a⁻¹⁆ = z) (ht : t * t = 1) (hta : Commute t a)
    (htx : t * x * t = x⁻¹) :
    ∃ x y h : H, x ^ 13 = 1 ∧ y ^ 13 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      h * h = 1 ∧ h * x * h = x⁻¹ ∧ h * y * h = y⁻¹ := by
  have hy : (a * x * a⁻¹) ^ 13 = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hzy : Commute z (a * x * a⁻¹) := (hza.mul_right hzx).mul_right hza.inv_right
  have hyH : a * x * a⁻¹ ∈ H := mul_mem (mul_mem haH hxH) (inv_mem haH)
  have hc : (⁅(⟨x, hxH⟩ : H), (⟨a * x * a⁻¹, hyH⟩ : H)⁆ : H).1 = z := by
    rw [← hcomm]
    simp [commutatorElement_def]
  refine ⟨⟨x, hxH⟩, ⟨a * x * a⁻¹, hyH⟩, ⟨t, htH⟩, Subtype.ext (by simpa using hx),
    Subtype.ext (by simpa using hy), ?_, ?_, ?_, Subtype.ext (by simpa using ht),
    Subtype.ext (by simpa using htx), Subtype.ext (by simpa using inversion_conj ht hta htx)⟩
  · intro h
    exact hz (by rw [← hc, h]; rfl)
  · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]; exact hzx.eq)
  · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]; exact hzy.eq)

end Algebra

theorem thirteen_order_check : thirteenOrderCheck () = true :=
  Certificates.certificate125500

theorem thirteen_rel_check : thirteenRelCheck () = true :=
  Certificates.certificate125501

private theorem eq_of_eqWords3C
    {w₁ w₂ : List Native.Gen} (h : eqWords3C (Native.mkCtx ()) w₁ w₂ = true) :
    wordLin w₁ = wordLin w₂ :=
  eq_of_eqWords3 (by rwa [eqWords3C_mkCtx] at h)

theorem thirteen_relations :
    wordLin (thirteenX ++ thirteenXi) = wordLin [] ∧
    wordLin (thirteenK ++ thirteenKi) = wordLin [] ∧
    wordLin (thirteenYi ++ thirteenXi ++ thirteenY ++ thirteenX) = wordLin thirteenZ ∧
    wordLin (thirteenX ++ thirteenZ) = wordLin (thirteenZ ++ thirteenX) ∧
    wordLin (thirteenK ++ thirteenZ) = wordLin (thirteenZ ++ thirteenK) ∧
    wordLin (thirteenT0 ++ thirteenX ++ thirteenT0) = wordLin thirteenXi ∧
    wordLin (thirteenT0 ++ thirteenK) = wordLin (thirteenK ++ thirteenT0) ∧
    wordLin (thirteenT0 ++ thirteenT0) = wordLin [] ∧
    wordLin thirteenZ ≠ 1 := by
  have h := thirteen_rel_check
  simp only [thirteenRelCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h7'⟩, h8⟩ := h
  refine ⟨eq_of_eqWords3C h1, eq_of_eqWords3C h2, eq_of_eqWords3C h3, eq_of_eqWords3C h4,
    eq_of_eqWords3C h5, eq_of_eqWords3C h6, eq_of_eqWords3C h7, eq_of_eqWords3C h7', ?_⟩
  intro hz
  have hne := ne_of_neX (v := bV ()) (p := thirteenP) (by norm_num [thirteenP])
    (by rwa [neXC_mkCtx] at h8 : neX thirteenZ [] (bV ()) thirteenP = true)
  exact hne (by rw [hz, wordLin_nil])

theorem thirteen_x_pow :
    wordLin thirteenX ^ 13 = 1 := by
  have h := thirteen_order_check
  simp only [thirteenOrderCheck] at h
  have := eq_of_eqWords3C h
  rwa [wordLin_powL, wordLin_nil] at this

theorem thirteen_heisenberg_inversion :
    ∃ x y h : Gmat, x ^ 13 = 1 ∧ y ^ 13 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      h * h = 1 ∧ h * x * h = x⁻¹ ∧ h * y * h = y⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h7', h8⟩ := thirteen_relations
  have hx := thirteen_x_pow
  have hxi : wordLin thirteenXi = (wordLin thirteenX)⁻¹ := by
    rw [wordLin_append, wordLin_nil] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hki : wordLin thirteenKi = (wordLin thirteenK)⁻¹ := by
    rw [wordLin_append, wordLin_nil] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hy : wordLin thirteenY = wordLin thirteenK * wordLin thirteenX * (wordLin thirteenK)⁻¹ := by
    simp only [thirteenY, wordLin_append, hki, mul_assoc]
  have hyi : wordLin thirteenYi =
      wordLin thirteenK * (wordLin thirteenX)⁻¹ * (wordLin thirteenK)⁻¹ := by
    simp only [thirteenYi, wordLin_append, hki, hxi, mul_assoc]
  have hcomm : ⁅wordLin thirteenX, wordLin thirteenK * wordLin thirteenX * (wordLin thirteenK)⁻¹⁆ =
      wordLin thirteenZ := by
    rw [← h3]
    simp only [wordLin_append, hy, hyi, hxi, commutatorElement_def]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hzx : Commute (wordLin thirteenZ) (wordLin thirteenX) := by
    simp only [wordLin_append] at h4
    exact h4
  have hza : Commute (wordLin thirteenZ) (wordLin thirteenK) := by
    simp only [wordLin_append] at h5
    exact h5
  have hzy : Commute (wordLin thirteenZ)
      (wordLin thirteenK * wordLin thirteenX * (wordLin thirteenK)⁻¹) :=
    (hza.mul_right hzx).mul_right hza.inv_right
  have ht : wordLin thirteenT0 * wordLin thirteenT0 = 1 := by
    rw [wordLin_append] at h7'
    exact h7'
  have hta : Commute (wordLin thirteenT0) (wordLin thirteenK) := by
    simp only [wordLin_append] at h7
    exact h7.symm
  have htx : wordLin thirteenT0 * wordLin thirteenX * wordLin thirteenT0 =
      (wordLin thirteenX)⁻¹ := by
    simp only [wordLin_append, hxi, mul_assoc] at h6
    simpa [mul_assoc] using h6
  exact heisenberg_inversion_of_subgroup (wordLin_mem_Gmat _) (wordLin_mem_Gmat _)
    (wordLin_mem_Gmat _) (wordLin_mem_Gmat _) hx h8 hzx hza hcomm ht hta htx

theorem hasNoncommPair_thirteen_Gmat :
    HasNoncommPair 13 Gmat := by
  obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -, -⟩ := thirteen_heisenberg_inversion
  exact hasNoncommPair_of_central_commutator (by norm_num : Nat.Prime 13) hx hy hz hzx hzy

theorem hasNoncommPair_thirteen_of_mulEquiv_Gmat
    {T : Type*} [Group T] (e : T ≃* Gmat) : HasNoncommPair 13 T :=
  HasNoncommPair.map e.symm.toMonoidHom e.symm.injective hasNoncommPair_thirteen_Gmat

end CFSG.AGLEmbedding.Norton.MON11_13
