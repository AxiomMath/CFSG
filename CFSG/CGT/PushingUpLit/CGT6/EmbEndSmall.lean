module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.CGT.PushingUpLit.CGT6M.FiveKernel
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspCover
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.Blueprint CFSG.CGT.PushingUpLit.CGT6M
open CFSG.Open (StatedClassicalModel)
open scoped commutatorElement

section Bound

variable {V : Type} [CommGroup V] [Finite V]

theorem card_models_sixteen :
    Nat.card (Multiplicative (Fin 2 → Fq 2)) = 16 ∧ Nat.card ↥(G6.coreMod 5) = 16 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → Fq 2) ≃ _), Nat.card_fun,
      GaloisField.card 2 2 (by norm_num)]
    simp
  · rw [Quasithin.X1512.card_coreMod (Or.inr rfl)]
    norm_num

theorem card_commV_le_sixteen_of_ysl2 (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y)
    (hcls : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥)
    (hY : YSL Y 2) : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y) := by
  rcases hcls with hX | ⟨n, hn, hΩ⟩
  · obtain ⟨h16, h5⟩ := card_models_sixteen
    rcases natSection_of_classX hV hperf hX le_rfl hY with hsl | ⟨-, halt⟩
    · exact CGT6M.card_commV_le_sixteen_of_isNatSectionBy (slAct 2) Y h16 hsl
    · exact CGT6M.card_commV_le_sixteen_of_isNatSectionBy (altAct 5) Y h5 halt
  · have := not_natOmegaMinus_of_ysl (f := 2) (by norm_num) (by omega) hY hΩ
    omega

end Bound

@[expose] def FiveSix (Q : Type) [Group Q] : Prop :=
  StatedClassicalModel Q .PSL 2 5 2 ∨ StatedClassicalModel Q .PSL 3 5 1 ∨
    StatedClassicalModel Q .PSU 3 5 1 ∨ NativeSporadic.IsSporadic Q .M12 ∨
    NativeSporadic.IsSporadic Q .J1 ∨ NativeSporadic.IsSporadic Q .J2

@[expose] def SporadicThreeCenterSmallPrimes : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    (NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J1 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2) →
      ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card (Subgroup.center K)

theorem exists_order_five {V : Type} [CommGroup V] [Finite V] {Y : Subgroup (MulAut V)}
    (hY : YSL Y 2) : ∃ y ∈ Y, y ^ 5 = 1 ∧ y ≠ 1 := by
  have hcard : Nat.card ↥Y = 60 := by
    rw [hY.card_eq (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 (by rw [hcard]; norm_num)
  refine ⟨(g : MulAut V), g.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  · intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    omega

theorem end4Small_six
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small (fun Q _ => FiveSix Q) := by
  intro V _ _ hV G T Y h hY2 hQ
  have hperf : ⁅Y, Y⁆ = Y := h.toEmb4Cfg.adm.hperf
  have hU := card_commV_le_sixteen_of_ysl2 hV hperf h.hcls2 hY2
  obtain ⟨y, hyY, hy5, hy1⟩ := exists_order_five hY2
  have hYL : Y ≤ conjClosure Y G := le_conjClosure
  have hq := h.quasi
  have : Group.IsPerfect ↥(conjClosure Y G) := ⟨hq.1⟩
  let π : ↥(conjClosure Y G) →* LayerQ G Y := QuotientGroup.mk' (Subgroup.center _)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = Subgroup.center ↥(conjClosure Y G) := QuotientGroup.ker_mk' _
  refine CGT6M.false_of_five_element_rank_four_perfect (Subgroup.subtype (conjClosure Y G))
    (Subgroup.subtype_injective _) hV π hπs hπk.le (y := ⟨y, hYL hyY⟩)
    (fun h1 => hy1 (congrArg Subtype.val h1)) (Subtype.ext hy5)
    (CGT6M.card_le_sixteen_fixSub_of_comm hV Y hyY hy5 hU) ?_ hQ
  intro hsp
  have hqs := isQuasisimple_of_open hq
  have h5 := hS ↥(conjClosure Y G) hqs hsp 5 Nat.prime_five (by norm_num)
  have h11 := hS ↥(conjClosure Y G) hqs hsp 11 (by norm_num) (by norm_num)
  rw [hπk]
  have c5 : Nat.Coprime (Nat.card ↥(Subgroup.center ↥(conjClosure Y G))) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5).symm
  have c11 : Nat.Coprime (Nat.card ↥(Subgroup.center ↥(conjClosure Y G))) 11 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h11).symm
  exact (show (55 : ℕ) = 5 * 11 by norm_num) ▸ c5.mul_right c11

theorem end4Small_l225
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small fun Q _ => StatedClassicalModel Q .PSL 2 5 2 :=
  fun V _ _ hV G T Y h hY hQ => end4Small_six hS V hV G T Y h hY (Or.inl hQ)

theorem end4Small_l35
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small fun Q _ => StatedClassicalModel Q .PSL 3 5 1 :=
  fun V _ _ hV G T Y h hY hQ => end4Small_six hS V hV G T Y h hY (Or.inr (Or.inl hQ))

theorem end4Small_u35
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small fun Q _ => StatedClassicalModel Q .PSU 3 5 1 :=
  fun V _ _ hV G T Y h hY hQ => end4Small_six hS V hV G T Y h hY (Or.inr (Or.inr (Or.inl hQ)))

theorem end4Small_m12
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small fun Q _ => NativeSporadic.IsSporadic Q .M12 :=
  fun V _ _ hV G T Y h hY hQ =>
    end4Small_six hS V hV G T Y h hY (Or.inr (Or.inr (Or.inr (Or.inl hQ))))

theorem end4Small_j1
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small fun Q _ => NativeSporadic.IsSporadic Q .J1 :=
  fun V _ _ hV G T Y h hY hQ =>
    end4Small_six hS V hV G T Y h hY (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))

theorem end4Small_j2
    (hS : SporadicThreeCenterSmallPrimes) :
    End4Small fun Q _ => NativeSporadic.IsSporadic Q .J2 :=
  fun V _ _ hV G T Y h hY hQ =>
    end4Small_six hS V hV G T Y h hY (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ)))))

end CFSG.CGT.PushingUpLit.CGT6
