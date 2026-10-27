module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClCases
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeRank
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Six
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThree.PartTwo.Sec19 SL3E27

namespace LieClAltSix

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]

theorem map_center_eq_inf_centralizer :
    (center ↥L).map L.subtype = L ⊓ centralizer (L : Set Y) := by
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.2 fun a ha => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.1 hy ⟨a, ha⟩)
  · rintro ⟨hyL, hyC⟩
    refine ⟨⟨y, hyL⟩, mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.1 hyC g g.2

theorem not_two_dvd_card_inf (hO : CFSG.pCore 2 Y = ⊥) :
    ¬ 2 ∣ Nat.card ↥(L ⊓ centralizer (L : Set Y)) := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := L ⊓ centralizer (L : Set Y)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hcomm : ∀ a b : ↥Z, a * b = b * a := fun a b =>
    Subtype.ext (mem_centralizer_iff.1 b.2.2 a a.2.1)
  have hTn : (zpowers t).Normal := ⟨fun n hn g => by
    rw [hcomm g n, mul_inv_cancel_right]
    exact hn⟩
  have hTp : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht, pow_one]
  have hT : zpowers t ≤ CFSG.pCore 2 ↥Z := le_sSup ⟨hTn, hTp⟩
  have hZ : pCoreOf 2 Z = ⊥ := le_bot_iff.1
    ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (le_top : Z ≤ ⊤)
      fun g _ => normalizer_eq_top (H := Z) ▸ mem_top g).trans
      (by rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore, hO]))
  have htZ : (t : Y) ∈ pCoreOf 2 Z := ⟨t, hT (mem_zpowers t), rfl⟩
  rw [hZ, mem_bot] at htZ
  rw [show t = 1 from Subtype.ext htZ, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem exists_mul_eq (hT : IsTripleA6 ↥L) [Group.IsPerfect ↥L] {x : Y} (hx : x ^ 3 = 1) :
    ∃ l c : Y, l ∈ L ∧ c ∈ centralizer (L : Set Y) ∧ l ^ 3 = 1 ∧ c ^ 3 = 1 ∧ l * c = x := by
  set σ : MulAut ↥L := MulAut.conjNormal x with hσdef
  have hσ : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hx, map_one]
  obtain ⟨y, hy⟩ := Item19Res4Proof.exists_eq_conj_of_isTripleA6 hT σ hσ
  have hxy : ∀ a ∈ L, x * a * x⁻¹ = (y : Y) * a * (y : Y)⁻¹ := fun a ha => by
    have := congrArg (fun τ : MulAut ↥L => ((τ ⟨a, ha⟩ : ↥L) : Y)) hy
    simpa [hσdef, MulAut.conjNormal_apply, MulAut.conj_apply] using this
  have hy3 : (y : Y) ^ 3 = 1 := by
    have h1 : y ^ 3 ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      have h2 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, ← hy, hσ]
      have h3 := congrArg (fun τ : MulAut ↥L => τ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h3]
        _ = y ^ 3 * g := by group
    have h2 := Item19Res4Proof.pow_three_eq_one_of_isTripleA6 hT (x := y)
      (by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact h1)
    simpa using congrArg Subtype.val h2
  have hxl : x * (y : Y) = (y : Y) * x := by
    have h := hxy y y.2
    calc x * (y : Y) = x * (y : Y) * x⁻¹ * x := by group
      _ = (y : Y) * (y : Y) * (y : Y)⁻¹ * x := by rw [h]
      _ = (y : Y) * x := by group
  refine ⟨y, (y : Y)⁻¹ * x, y.2, mem_centralizer_iff.2 fun a ha => ?_, hy3, ?_, by group⟩
  · calc a * ((y : Y)⁻¹ * x) = (y : Y)⁻¹ * ((y : Y) * a * (y : Y)⁻¹) * x := by group
      _ = (y : Y)⁻¹ * (x * a * x⁻¹) * x := by rw [hxy a ha]
      _ = (y : Y)⁻¹ * x * a := by group
  · have hc : Commute ((y : Y)⁻¹) x := (Commute.inv_left hxl.symm)
    rw [hc.mul_pow, hx, mul_one, inv_pow, hy3, inv_one]

end LieClAltSix

open LieClAltSix in
theorem kFactTripleAltSixHTwo_holds : KFactTripleAltSixHTwo := by
  intro Y _ _ L hLn hq hO he h3 hrk E hE hEc
  haveI := hLn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  obtain ⟨e⟩ := he
  set C := centralizer (L : Set Y) with hCdef
  set Z := L ⊓ C with hZdef
  have hZc : Nat.card Z = Nat.card (center ↥L) := by
    rw [hZdef, ← map_center_eq_inf_centralizer,
      Subgroup.card_map_of_injective L.subtype_injective]
  have h6 := CFSG.LocalAnalysis.GLTheoremB.Prop95I1921.card_center_dvd_six_of_alt6 hq.1 e
  have h2 := not_two_dvd_card_inf (L := L) hO
  have hZ3 : Nat.card (center ↥L) = 3 := by
    rw [← hZc] at h3 h6 ⊢
    obtain ⟨k, hk⟩ := h3
    have hk6 : k ∣ 2 := by
      have := h6
      rw [hk, show (6 : ℕ) = 3 * 2 from rfl] at this
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_two).1 hk6 with rfl | rfl
    · simpa using hk
    · exact absurd (hk ▸ dvd_mul_left 2 3) h2
  have hT : IsTripleA6 ↥L := ⟨hZ3, ⟨e⟩⟩
  have hdec := fun {x : Y} (hx : x ^ 3 = 1) => exists_mul_eq hT hx
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [hZc, hZ3])
  set z : Y := (z₀ : Y) with hzdef
  have hz : orderOf z = 3 := by rw [hzdef, Subgroup.orderOf_coe, hz₀]
  have hz3 : z ^ 3 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hzZ : zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 z₀.2) ?_
    rw [Nat.card_zpowers, hz, hZc, hZ3]
  have hmemZ : ∀ y : Y, y ∈ L → y ∈ C → y ∈ zpowers z := fun y h1 h2 => hzZ ▸ ⟨h1, h2⟩
  have hzL : zpowers z ≤ L := hzZ ▸ inf_le_left
  have hzC : zpowers z ≤ C := hzZ ▸ inf_le_right
  have hEc' : Nat.card E = 3 ^ 2 := by rw [hEc]; norm_num
  have hzc : ∀ y : Y, y ^ 3 = 1 → y * z = z * y := fun y hy => by
    obtain ⟨l, c, hl, hc, -, -, rfl⟩ := hdec hy
    have h1 : l * z = z * l := (mem_centralizer_iff.1 (hzC (mem_zpowers z)) l hl)
    have h2 : z * c = c * z := (mem_centralizer_iff.1 hc z (hzL (mem_zpowers z)))
    calc l * c * z = l * (z * c) := by rw [mul_assoc, h2]
      _ = z * (l * c) := by rw [← mul_assoc, h1, mul_assoc]
  obtain ⟨w, hwC, hw3, hwL⟩ : ∃ w ∈ C, w ^ 3 = 1 ∧ w ∉ L := by
    by_contra hno
    push Not at hno
    obtain ⟨A, -, hA, hAc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup Y)
    rw [hrk] at hAc
    have hAL : A ≤ L := fun a ha => by
      obtain ⟨l, c, hl, hc, -, hc3, rfl⟩ := hdec (hA.2 a ha)
      exact mul_mem hl (hno c hc hc3)
    set A' : Subgroup ↥L := A.subgroupOf L
    have hA' : IsElemAbelian 3 A' := by
      haveI := hA.1
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · change ((a : ↥L) : Y) * ((b : ↥L) : Y) = ((b : ↥L) : Y) * ((a : ↥L) : Y)
        exact congrArg Subtype.val
          (mul_comm' (⟨_, mem_subgroupOf.mp a.2⟩ : A) ⟨_, mem_subgroupOf.mp b.2⟩)
      · simpa using hA.2 _ (mem_subgroupOf.mp hx)
    have hA'c : Nat.card A' = 27 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv, hAc]
      norm_num
    exact Item19Res4Proof.card_ne_twentySeven_of_isTripleA6 hT A' hA' hA'c
  by_cases hzE : z ∈ E
  swap
  · exact three_le_pRank_centralizer_of_commute_not_mem hE hEc' hzE hz3
      fun d hd => hzc d (hE.2 d hd)
  have hlt : zpowers z < E := by
    refine lt_of_le_of_ne (zpowers_le.2 hzE) fun h => ?_
    have := congrArg (fun H : Subgroup Y => Nat.card H) h
    simp only [Nat.card_zpowers, hz, hEc] at this
    norm_num at this
  obtain ⟨x, hxE, hxz⟩ := SetLike.exists_of_lt hlt
  have hDxz := eq_sup_zpowers_of_card hEc' hz hzE hxE hxz
  obtain ⟨l, c, hlL, hcC, hl3, hc3, hlc⟩ := hdec (hE.2 x hxE)
  have hcl : c * l = l * c := (mem_centralizer_iff.1 hcC l hlL).symm
  obtain ⟨u, huE, hu3, hud⟩ : ∃ u : Y, u ∉ E ∧ u ^ 3 = 1 ∧ ∀ d ∈ E, d * u = u * d := by
    by_cases hl : l ∈ zpowers z
    ·
      have hxC : x ∈ C := hlc ▸ mul_mem (hzC hl) hcC
      have hEC : E ≤ C := hDxz ▸ sup_le (zpowers_le.2 hxC) hzC
      obtain ⟨v, hv3, hvZ⟩ := Item19Res4Proof.exists_noncentral_of_isTripleA6 hT
      refine ⟨v, fun hvE => hvZ ?_, by simpa using congrArg Subtype.val hv3,
        fun d hd => (mem_centralizer_iff.1 (hEC hd) v v.2).symm⟩
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 (hEC hvE) g g.2)
    by_cases hc : c ∈ zpowers z
    ·
      have hxL : x ∈ L := hlc ▸ mul_mem hlL (hzL hc)
      have hEL : E ≤ L := hDxz ▸ sup_le (zpowers_le.2 hxL) hzL
      exact ⟨w, fun h => hwL (hEL h), hw3, fun d hd => mem_centralizer_iff.1 hwC d (hEL hd)⟩
    ·
      refine ⟨c, fun hcE => hc ?_, hc3, fun d hd => ?_⟩
      · have hlE : l ∈ E := by
          have : l = x * c⁻¹ := by rw [← hlc, mul_inv_cancel_right]
          rw [this]
          exact mul_mem hxE (inv_mem hcE)
        have hEL : E ≤ L := (eq_sup_zpowers_of_card hEc' hz hzE hlE hl) ▸
          sup_le (zpowers_le.2 hlL) hzL
        exact hmemZ c (hEL hcE) hcC
      · have hxc : x * c = c * x := by rw [← hlc, ← mul_assoc c l c, hcl]
        have hzc' : z * c = c * z := mem_centralizer_iff.1 hcC z (hzL (mem_zpowers z))
        have hcen : E ≤ centralizer ({c} : Set Y) := hDxz ▸ sup_le
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 hxc))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzc'))
        exact mem_centralizer_singleton_iff.1 (hcen hd)
  exact three_le_pRank_centralizer_of_commute_not_mem hE hEc' huE hu3 hud

end CFSG.LocalAnalysis.RankThreeTheoremC
