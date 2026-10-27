module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PerfectCover

theorem card_center_dvd_card_griessHopfMultiplier {Q S : Type} [Group Q] [Finite Q] [Group S]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : Group.IsPerfect Q := hQ
  have : Finite S := Finite.of_surjective q hq
  have : Group.IsPerfect S := Group.IsPerfect.ofSurjective hq
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier q hq hker.le
  rw [← hker, ← Nat.card_congr e'.toEquiv, Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

end CFSG.AGLEmbedding
