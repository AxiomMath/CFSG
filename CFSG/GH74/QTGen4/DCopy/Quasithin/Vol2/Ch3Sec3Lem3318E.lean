module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318E

public section
namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem false_of_pCoreOf_ne_bot_F4 (hD : Data G T M L D n k α Φ) (h15 : Step3_3_15R_F4)
    (hO : pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T ⊔ D) ≠ ⊥) : False := by
  have hn := hD.n4
  have hn5 := hD.n5
  obtain ⟨ψ₁, hψ₁s, hψ₁k, -⟩ := hD.exists_levi_one
  obtain ⟨ψ₂, hψ₂s, hψ₂k, -⟩ := hD.exists_levi_three
  have ht₁ : L3312.Type3312R (↥(liftCore α (flagStabilizer n (ZMod 2) {1})) ⧸
      CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {1}))) := by
    have h := isPSL_of_hom (by omega) hψ₁s hψ₁k
    rcases (by omega : n - 1 = 3 ∨ n - 1 = 4) with h3 | h4
    · rw [h3] at h
      exact Or.inr (Or.inl h)
    · rw [h4] at h
      exact Or.inr (Or.inr h)
  have ht₂ : L3312.Type3312R (↥(liftCore α (flagStabilizer n (ZMod 2) {3})) ⧸
      CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))) :=
    Or.inr (Or.inl (isPSL_of_hom le_rfl hψ₂s hψ₂k))
  obtain ⟨Y, hY, -, hpsl, -⟩ := h15 G T M L D _ _ hD.hyp hD.mem_lFamilyOf_one
    hD.mem_lFamilyOf_three hD.sup_eq hD.pCoreOf_ne_bot_one hO ht₁ ht₂
  rcases hY with rfl | rfl
  · exact not_isPSL_two_two (by omega) (by omega) hψ₁s hψ₁k hpsl
  · exact not_isPSL_two_two le_rfl (by norm_num) hψ₂s hψ₂k hpsl

end Data

end CFSG.Quasithin.H13.L3318
