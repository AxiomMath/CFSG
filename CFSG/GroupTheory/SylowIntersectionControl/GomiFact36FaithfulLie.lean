module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4
import CFSG.Quasithin.Background.SmithA36
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Lin2

variable {W : Type} [CommGroup W]

private theorem inf_centSec_eq_bot_of_ker_eq_bot_fas {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (h : (B5.Ln.secHomL L hLI hLZ).ker = ⊥) : L ⊓ centSec I Z = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
  have hmem : (⟨g, hgL⟩ : ↥L) ∈ (B5.Ln.secHomL L hLI hLZ).ker :=
    (mem_ker_secHomL hLI hLZ ⟨g, hgL⟩).mpr hgC
  rw [h] at hmem
  have h1 : (⟨g, hgL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hmem
  simpa using congrArg Subtype.val h1

private theorem inf_centSec_eq_bot_of_sl3_equiv_fas {L : Subgroup (MulAut W)}
    (hL : CFSG.IsQuasisimple ↥L) {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z)
    (hodd : Odd (Nat.card ↥(L ⊓ centSec I Z))) {a : ℕ} {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 2 ^ a) (e : ↥(StatedSL 3 K) ≃* ↥(autSec L I Z)) :
    L ⊓ centSec I Z = ⊥ := by
  have hK2 : ringChar K = 2 := SmithA36.ringChar_eq_two_of_card hcard
  have hLI := hIZ.le_stabSub_left
  have hLZ := hIZ.le_stabSub_right
  let f := B5.Ln.secHomL L hLI hLZ
  have hf : Function.Surjective f := by
    simpa [f] using B5.Ln.secHomL_surjective hLI hLZ
  have hker : Nat.card f.ker = Nat.card ↥(L ⊓ centSec I Z) := by
    simpa [f] using card_ker_secHomL hLI hLZ
  have hodd' : ∀ z ∈ f.ker, Odd (orderOf z) := by
    intro z hz
    have hdvd : orderOf z ∣ Nat.card ↥f.ker := Subgroup.orderOf_dvd_natCard f.ker hz
    exact hodd.of_dvd_nat (hker ▸ hdvd)
  have hinj : Function.Injective f :=
    SmithA36.injective_of_isQuasisimple_statedSL hL (m := 2) le_rfl hK2 e.symm hf hodd'
  exact inf_centSec_eq_bot_of_ker_eq_bot_fas hLI hLZ (MonoidHom.ker_eq_bot f hinj)

private theorem inf_centSec_eq_bot_of_sp4_equiv_fas [Finite W] {L : Subgroup (MulAut W)}
    (hL : CFSG.IsQuasisimple ↥L) {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z)
    (hodd : Odd (Nat.card ↥(L ⊓ centSec I Z))) {a : ℕ} (ha : 2 ≤ a) {K : Type} [Field K]
    [Finite K] (hcard : Nat.card K = 2 ^ a) (e : ↥(StatedSp 2 K) ≃* ↥(autSec L I Z))
    (hSp : Sp4OddMultiplierTrivial) : L ⊓ centSec I Z = ⊥ := by
  have hchar : CharP K 2 := ringChar.eq_iff.mp (SmithA36.ringChar_eq_two_of_card hcard)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hLI := hIZ.le_stabSub_left
  have hLZ := hIZ.le_stabSub_right
  let f := B5.Ln.secHomL L hLI hLZ
  have hf : Function.Surjective f := by
    simpa [f] using B5.Ln.secHomL_surjective hLI hLZ
  let η : ↥L →* StatedSp 2 K := e.symm.toMonoidHom.comp f
  have hηsurj : Function.Surjective η := by
    simpa [η] using e.symm.surjective.comp hf
  have hηker : η.ker = f.ker := by
    simp [η]
  have hker : Nat.card f.ker = Nat.card ↥(L ⊓ centSec I Z) := by
    simpa [f] using card_ker_secHomL hLI hLZ
  have hkerle : η.ker ≤ Subgroup.center ↥L := by
    rw [hηker]
    exact ker_secHomL_le_center hL hIZ hLI hLZ
  have hoddη : Odd (Nat.card η.ker) := by
    rw [hηker, hker]
    exact hodd
  have hfinAut : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => DFunLike.ext f g (fun x => congrFun h x))
  have hfinL : Finite ↥L :=
    @Finite.of_injective ↥L (MulAut W) hfinAut Subtype.val Subtype.val_injective
  have hbot : η.ker = ⊥ :=
    @hSp K inferInstance inferInstance hchar hK4 ↥L inferInstance hfinL hL.1 η hηsurj hkerle hoddη
  exact inf_centSec_eq_bot_of_ker_eq_bot_fas hLI hLZ (hηker ▸ hbot)

theorem inf_centSec_eq_bot_of_binaryNaturalSL [Finite W] {L : Subgroup (MulAut W)}
    (hL : CFSG.IsQuasisimple ↥L) {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z)
    (hodd : Odd (Nat.card ↥(L ⊓ centSec I Z))) {a : ℕ}
    (hnat : BinaryNaturalSL (autSec L I Z) ⊤ ⊥ 3 a) : L ⊓ centSec I Z = ⊥ := by
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
  exact @inf_centSec_eq_bot_of_sl3_equiv_fas W _ L hL I Z hIZ hodd a K hK hKfin hcard e

theorem inf_centSec_eq_bot_of_binaryNaturalSp4 (hSp : Sp4OddMultiplierTrivial) [Finite W]
    {L : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L) {I Z : Subgroup W}
    (hIZ : IsGomiNoncentralFactor L I Z) (hodd : Odd (Nat.card ↥(L ⊓ centSec I Z))) {a : ℕ}
    (ha : 2 ≤ a) (hnat : BinaryNaturalSp4 (autSec L I Z) ⊤ ⊥ a) : L ⊓ centSec I Z = ⊥ := by
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hnat
  exact @inf_centSec_eq_bot_of_sp4_equiv_fas W _ _ L hL I Z hIZ hodd a ha K hK hKfin hcard e hSp

end CFSG.GroupTheory
