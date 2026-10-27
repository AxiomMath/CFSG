module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN2c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndCtx

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable {n : ℕ} (P : PsiData T L V n) (h : Hyp6Sec2 G T M L V)

include h in

theorem eq_of_mem_V_F4 (h6211 : Stmt6_2_11_F4) (a b : ↥(HH T)) (haV : (a : G) ∈ V) (hbV : (b : G) ∈ V)
    (ha : (a : G) ∉ CHU T L V) (hb : (b : G) ∉ CHU T L V) : P.ψ a = P.ψ b := by
  have hidx := relIndex_V_CHU_F4 h h6211
  have hinv : (a : G)⁻¹ ∈ CHU T L V → (a : G) ∈ CHU T L V := fun hh => by
    simpa using (CHU T L V).inv_mem hh
  have hA : (a : G)⁻¹ * b ∈ V ⊓ CHU T L V :=
    mul_mem_of_relIndex_two hidx (V.inv_mem haV) hbV
      (fun hh => ha (hinv (Subgroup.mem_inf.mp hh).2)) (fun hh => hb (Subgroup.mem_inf.mp hh).2)
  have h1 : P.ψ (a⁻¹ * b) = 1 := (P.ker _).mpr (by simpa using (Subgroup.mem_inf.mp hA).2)
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

include h in

theorem mem_V_F4 (h6211 : Stmt6_2_11_F4) (a v : ↥(HH T)) (haV : (a : G) ∈ V)
    (haC : (a : G) ∉ CHU T L V) (hvV : (v : G) ∈ V) : P.ψ v = 1 ∨ P.ψ v = P.ψ a := by
  by_cases hv : (v : G) ∈ CHU T L V
  · exact Or.inl ((P.ker v).mpr hv)
  · exact Or.inr (P.eq_of_mem_V_F4 h h6211 v a hvV haV hv haC)

include h in

theorem conj_le_Mz_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9_F4)
    (h6211 : Stmt6_2_11_F4) (a x : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (hc : Commute ((P.ψ x)⁻¹ * P.ψ a * P.ψ x) (P.ψ a)) :
    conjSubgroup V (x : G) ≤ HH T ⊓ M := by
  intro u hu
  have hxu : (x : G) * u * (x : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hu
  have hxH : (x : G) * u * (x : G)⁻¹ ∈ HH T := V_le_HH h hZ hxu
  have huH : u ∈ HH T := by
    have h1 := (HH T).mul_mem ((HH T).mul_mem ((HH T).inv_mem x.2) hxH) x.2
    have e : (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * (x : G) = u := by group
    rwa [e] at h1
  set u' : ↥(HH T) := ⟨u, huH⟩ with hu'
  have hv : (x : G) * u * (x : G)⁻¹ = ((x * u' * x⁻¹ : ↥(HH T)) : G) := rfl
  have hψ : P.ψ u' = 1 ∨ P.ψ u' = (P.ψ x)⁻¹ * P.ψ a * P.ψ x := by
    have e : P.ψ u' = (P.ψ x)⁻¹ * P.ψ (x * u' * x⁻¹) * P.ψ x := by
      rw [map_mul, map_mul, map_inv]
      group
    rcases P.mem_V_F4 h h6211 a (x * u' * x⁻¹) haV haC (by rw [← hv]; exact hxu) with h1 | h1
    · left
      rw [e, h1]
      group
    · right
      rw [e, h1]
  have hcomm : P.ψ u' * P.ψ a = P.ψ a * P.ψ u' := by
    rcases hψ with h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact hc.eq
  have hN := ((P.swap_norm a haV haC).2 u').mpr hcomm
  have := (h629 G T M L V h).1
  have hM : u ∈ HH T ⊓ M := by
    rw [this]
    exact Subgroup.mem_inf.mpr ⟨huH, hN⟩
  exact hM

end PsiData

end CFSG.Quasithin.H13.GM22
