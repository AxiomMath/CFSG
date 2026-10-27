module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Core
public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3SQTK
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
import CFSG.Quasithin.MS93.FFTypes

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem isPSL_quot_of_sl3_cover {B K : Type} [Group B] [Group K] {f : ℕ} (hf1 : 1 ≤ f)
    (e : B ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f))
    (h : B →* K) (hs : Function.Surjective h) (hker : h.ker ≤ Subgroup.center B)
    (hperf : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤) :
    IsPSL 3 2 f (K ⧸ Subgroup.center K) := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let e' : ↥(StatedSL 3 (GaloisField 2 f)) ≃* B :=
    (specialLinearGroupEquivStatedSL 3 (GaloisField 2 f)).symm.trans e.symm
  have hPSLB : IsPSL 3 2 f (B ⧸ Subgroup.center B) :=
    (MS93.isPSL_quot_of_equiv_statedSL_three hF e').2.1
  obtain ⟨q⟩ := StarAux.nonempty_quotientCenterEquiv_of_central_ker h hs hker hperf
  exact IsPSL.of_mulEquiv q hPSLB

theorem ker_inf_center_eq_bot
    (h51 : AsB51) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {J K : Subgroup (MulAut V)} (hB : B51Hyp J K) {B : Type} [Group B] [Finite B] {f : ℕ}
    (hf : Even f) (hf1 : 1 ≤ f) (e : B ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f))
    (h : B →* ↥K) (hs : Function.Surjective h) (hker : h.ker ≤ Subgroup.center B)
    (hperf : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤) :
    h.ker ⊓ Subgroup.center B = ⊥ := by
  by_contra hne
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let e' : ↥(StatedSL 3 (GaloisField 2 f)) ≃* B :=
    (specialLinearGroupEquivStatedSL 3 (GaloisField 2 f)).symm.trans e.symm
  have hPSLB : IsPSL 3 2 f (B ⧸ Subgroup.center B) :=
    (MS93.isPSL_quot_of_equiv_statedSL_three hF e').2.1
  obtain ⟨q⟩ := StarAux.nonempty_quotientCenterEquiv_of_central_ker h hs hker hperf
  have hPSLK : IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K) := IsPSL.of_mulEquiv q hPSLB
  have hN : h.ker.map e.toMonoidHom ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f)) := by
    rw [← SmithC27.map_center_of_mulEquiv e]
    exact Subgroup.map_mono hker
  have hker_eq : h.ker = Subgroup.center B := by
    rcases eq_bot_or_eq_center_of_le_center _ hN with h0 | h0
    · exfalso
      apply hne
      have : h.ker = ⊥ := (Subgroup.map_eq_bot_iff_of_injective h.ker e.injective).mp h0
      rw [this, bot_inf_eq]
    · rw [← SmithC27.map_center_of_mulEquiv e] at h0
      exact Subgroup.map_injective e.injective h0
  apply core_center_ne_bot h51 hV hB hf hPSLK
  rw [← StarAux.map_center_eq_center h hs hker hperf, ← hker_eq]
  exact (Subgroup.map_eq_bot_iff _).mpr le_rfl

end CFSG.HardMathSupport.Curtis.Coordinator
