module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance

theorem fixSub_eq_fixSubgroup_up34 {Y : Type*} [Group Y] (α : MulAut Y) :
    Lemma510Ns.fixSub α = fixSubgroup α :=
  Subgroup.ext fun _ => Iff.rfl

theorem Up34Pumpup.card_dvd {S : Type} [Group S] [Finite S] {α : MulAut S}
    (h : Up34Pumpup S α) : 20160 ∣ Nat.card S := by
  obtain ⟨-, -, I, -, hI34⟩ := h
  rw [← card_eq_of_isLThreeFour hI34]
  exact (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥I)).trans
    (Subgroup.card_subgroup_dvd_card I)

theorem Up34Pumpup.of_congr {S T : Type} [Group S] [Finite S] [Group T] [Finite T] (e : S ≃* T)
    {α : MulAut S} (h : Up34Pumpup S α) : Up34Pumpup T (MulAut.congr e α) := by
  obtain ⟨hα3, hα1, I, hI, hI34⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow, hα3, map_one]
  · intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  · have hker : (e : S →* T).ker ≤ Subgroup.center S := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
      exact bot_le
    obtain ⟨A, hA, hAT⟩ := isLThreeFour_barOf_of_central (e : S →* T) e.surjective hker α
      (MulAut.congr e α) (fun y => by simp [MulAut.congr_apply]) hI hI34
    exact ⟨A, hA, hAT⟩

end CFSG.HardMathSupport.Dickson.Sec6
