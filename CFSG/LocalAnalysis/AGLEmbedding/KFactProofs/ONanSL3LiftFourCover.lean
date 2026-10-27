module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCentre
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Cover
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.PushingUpLit.CGT6X.End4

theorem exists_mulEquiv_specialLinear_four
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {L : Type} [Group L] [Finite L] (hL : commutator L = ⊤)
    (hmod : CFSG.Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 2)
    (e : L ⧸ Subgroup.center L ≃* LinearFlag.projectiveSL 3 k)
    (hodd : Odd (Nat.card (Subgroup.center L))) (hz : Subgroup.center L ≠ ⊥) :
    Nonempty (SpecialLinearGroup (Fin 3) k ≃* L) := by
  have : Group.IsPerfect L := ⟨hL⟩
  obtain ⟨ρ, hρ⟩ := exists_cover_l34 hmod hk e hodd
  have hker : ∀ s, e (QuotientGroup.mk (ρ s)) = 1 ↔
      s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    intro s
    rw [hρ s, ← MonoidHom.mem_ker, LinearFlag.ker_proj, LinearFlag.scalars_eq_center]
  have hsurj : Function.Surjective ρ := by
    have hdec : ∀ g : L, ∃ z ∈ Subgroup.center L, ∃ l ∈ ρ.range, g = z * l := by
      intro g
      obtain ⟨s, hs⟩ := LinearFlag.proj_surjective 3 k (e (QuotientGroup.mk g))
      have h1 : (QuotientGroup.mk g : L ⧸ Subgroup.center L) = QuotientGroup.mk (ρ s) :=
        e.injective (by rw [hρ s, hs])
      refine ⟨g * (ρ s)⁻¹, ?_, ρ s, ⟨s, rfl⟩, by group⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
        mul_inv_cancel]
    exact MonoidHom.range_eq_top.1 (eq_top_of_perfect_of_dec hL hdec)
  have hcard : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) k)) ∣ 3 :=
    (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by norm_num) k).trans
      (Nat.gcd_dvd_left _ _)
  obtain ⟨⟨z, hzc⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have hz1 : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨s, hs⟩ := hsurj z
  have hsc : s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    rw [← hker, hs, (QuotientGroup.eq_one_iff z).2 hzc, map_one]
  have hkerle : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    intro t ht
    rw [← hker, MonoidHom.mem_ker.1 ht, QuotientGroup.mk_one, map_one]
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact SL3Lift.ker_eq_bot_of_card_dvd_prime Nat.prime_three ρ hkerle hcard
      ⟨s, hsc, by rw [hs]; exact hz1⟩
  exact ⟨MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour
