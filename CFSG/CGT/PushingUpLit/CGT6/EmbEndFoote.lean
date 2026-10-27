module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.CGT.PushingUpLit.CGT6M.FiveKernel
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvert
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspSp4

public section

attribute [-instance] CFSG.RankThree.Native.fact_prime_five
namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.Blueprint CFSG.CGT.PushingUpLit.CGT6M
open CFSG.Open (StatedClassicalModel standardIsStandardSubgroup)
open scoped commutatorElement

@[expose] def FooteList (Q : Type) [Group Q] : Prop :=
  StatedClassicalModel Q .PSL 3 5 1 ∨ StatedClassicalModel Q .PSU 3 5 1 ∨
    ChevalleyExceptionalModel Q .G2 5 1 ∨
    (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel Q .trialityD4 5 f) ∨
    StatedClassicalModel Q .PSp 2 5 1 ∨ StatedClassicalModel Q .PSL 4 5 1 ∨
    StatedClassicalModel Q .PSU 4 5 1

@[expose] def EndFoote : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → YSL5 Y → FooteList (LayerQ G Y)

@[expose] def FooteInspU4 : Prop :=
  ∀ (Q : Type) [Group Q], StatedClassicalModel Q .PSU 4 5 1 → CoverInv Q

@[expose] def FooteInspExc : Prop :=
  (∀ (Q : Type) [Group Q], ChevalleyExceptionalModel Q .G2 5 1 → CoverInv Q) ∧
  (∀ (Q : Type) [Group Q] (f : ℕ), 1 ≤ f → ChevalleyExceptionalModel Q .trialityD4 5 f →
    CoverInv Q)

section Core

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_ysl5 {Y : Subgroup (MulAut V)} (h : YSL5 Y) : Nat.card ↥Y = 120 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.card_zmod]
  norm_num

omit [Finite V] in
theorem center_ne_bot_ysl5 {Y : Subgroup (MulAut V)} (h : YSL5 Y) : Subgroup.center ↥Y ≠ ⊥ := by
  obtain ⟨e⟩ := h
  intro hc
  let m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) := ⟨-1, by simp [Matrix.det_neg]⟩
  have hm : m ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    show (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) (ZMod 5))
    simp
  have h1 : (Subgroup.center ↥Y).map e.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := Subgroup.map_center_eq e
  rw [hc, Subgroup.map_bot] at h1
  rw [← h1] at hm
  have hm1 : m = 1 := hm
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) hm1
  simp [m] at this
  revert this
  decide

theorem exists_order_five_of_dvd {Y : Subgroup (MulAut V)} (h : 5 ∣ Nat.card ↥Y) :
    ∃ y ∈ Y, y ^ 5 = 1 ∧ y ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 h
  refine ⟨(g : MulAut V), g.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  · intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    omega

omit [Finite V] in
theorem not_natOmegaMinus_of_ysl5 {Y : Subgroup (MulAut V)} {n : ℕ} (hn : 2 ≤ n) (h : YSL5 Y)
    (hΩ : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) : False := by
  obtain ⟨-, θ, -⟩ := hΩ
  have h1 := Nat.card_congr θ.toEquiv
  rw [card_ysl5 h, card_sl2_fq (by omega)] at h1
  have h2 : 16 ≤ 2 ^ (2 * n) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 256 ≤ 2 ^ (2 * (2 * n)) := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (2 * (2 * n)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 16 * 255 ≤ 2 ^ (2 * n) * (2 ^ (2 * (2 * n)) - 1) := Nat.mul_le_mul h2 (by omega)
  omega

end Core

theorem end415_of_inputs (hM2 : H1NaturalSL2) (hM4 : SchurMultL2Two)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hFoote : EndFoote) (hU : FooteInspU4)
    (hExc : FooteInspExc) : End415 := by
  intro V _ _ hV G T Y h hY5
  have hperf : ⁅Y, Y⁆ = Y := h.toEmb4Cfg.adm.hperf
  have hX : InClassX ↥(yuHol Y) := by
    rcases h.hcls2 with hX | ⟨n, hn, hΩ⟩
    · exact hX
    · exact (not_natOmegaMinus_of_ysl5 hn hY5 hΩ).elim
  rcases emb_four_five hM2 hM4 V hV Y hperf hX with hc | ⟨-, hcard, hsl, hle, hC4⟩
  · exact (center_ne_bot_ysl5 hY5 hc).elim
  obtain ⟨z, hz1⟩ : ∃ z : ↥(Subgroup.center ↥Y), z ≠ 1 := by
    have h1 : 1 < Nat.card ↥(Subgroup.center ↥Y) := by rw [hcard]; norm_num
    have := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne (1 : ↥(Subgroup.center ↥Y))
  have hz2 : z ^ 2 = 1 := by
    have : orderOf z ∣ 2 := hcard ▸ orderOf_dvd_natCard z
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · rw [← h2]
      exact pow_orderOf_eq_one z
  let z0 : MulAut V := ((z : ↥Y) : MulAut V)
  have hzz : z0 * z0 = 1 := by
    have := congrArg (fun g : ↥(Subgroup.center ↥Y) => ((g : ↥Y) : MulAut V)) hz2
    simpa [sq] using this
  have hz0mem : z0 ∈ (Subgroup.center ↥Y).map Y.subtype := ⟨(z : ↥Y), z.2, rfl⟩
  have hW : Nat.card ↥(commSub z0) ≤ 4 :=
    (Subgroup.card_le_of_le (CGT6M.commSub_le_commV _ hz0mem)).trans (hle.trans hC4)
  have hYL : Y ≤ conjClosure Y G := le_conjClosure
  have hq := h.quasi
  have : Group.IsPerfect ↥(conjClosure Y G) := ⟨hq.1⟩
  let π : ↥(conjClosure Y G) →* LayerQ G Y := QuotientGroup.mk' (Subgroup.center _)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = Subgroup.center ↥(conjClosure Y G) := QuotientGroup.ker_mk' _
  have inspect : CoverInv (LayerQ G Y) → False := by
    intro hcov
    have hzL : z0 ∈ conjClosure Y G := hYL (z : ↥Y).2
    have hz1L : (⟨z0, hzL⟩ : ↥(conjClosure Y G)) ≠ 1 := fun h1 => by
      have h0 : z0 = 1 := congrArg Subtype.val h1
      exact hz1 (Subtype.ext (Subtype.ext h0))
    have hz2L : (⟨z0, hzL⟩ : ↥(conjClosure Y G)) * ⟨z0, hzL⟩ = 1 := Subtype.ext hzz
    let ρ : ↥(conjClosure Y G) →* MulAut V := Subgroup.subtype (conjClosure Y G)
    have hρ : Function.Injective ρ := Subgroup.subtype_injective _
    rcases hcov ↥(conjClosure Y G) hq h.oddZ ⟨MulEquiv.refl _⟩ ⟨z0, hzL⟩ hz1L hz2L with
      ⟨Φ, hΦi, hΦinv⟩ | ⟨X, Y', hX5, hY5', hZX, hZY, hZ1, hinv⟩
    · refine CGT6M.false_of_inverted_C55 hV hzz hW (ρ.comp Φ) (hρ.comp hΦi) fun u => ?_
      have := congrArg ρ (hΦinv u)
      simpa [ρ] using this
    · have hx5 : (ρ X) ^ 5 = 1 := by rw [← map_pow, hX5, map_one]
      have hy5 : (ρ Y') ^ 5 = 1 := by rw [← map_pow, hY5', map_one]
      have hzx : Commute ⁅ρ Y', ρ X⁆ (ρ X) := by
        rw [← map_commutatorElement]
        exact hZX.map ρ
      have hzy : Commute ⁅ρ Y', ρ X⁆ (ρ Y') := by
        rw [← map_commutatorElement]
        exact hZY.map ρ
      have hz1' : ⁅ρ Y', ρ X⁆ ≠ 1 := by
        rw [← map_commutatorElement]
        intro h1
        exact hZ1 (hρ (h1.trans (map_one ρ).symm))
      have hinv' : z0 * ρ X * z0⁻¹ = (ρ X)⁻¹ := by
        have := congrArg ρ hinv
        simpa [ρ] using this
      have hxle : Nat.card (commSub (ρ X)) ≤ 16 := by
        have h1 := CGT6M.card_commSub_le_of_inverted hzz hinv' hx5
        have h2 : Nat.card (commSub z0) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hW 2
        omega
      have hx1 : ρ X ≠ 1 := fun h1 => hz1' (by rw [h1, commutatorElement_one_right])
      exact CGT6M.false_of_heisenberg (i := 1) (j := 0) (k := 0) hx5 hy5 hzx hzy hz1' hV
        (by simpa using hx5) (by simpa using hx1) (by simpa using hxle)
  obtain ⟨y, hyY, hy5, hy1⟩ : ∃ y ∈ Y, y ^ 5 = 1 ∧ y ≠ 1 :=
    exists_order_five_of_dvd (by rw [card_ysl5 hY5]; norm_num)
  have hU' : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y) := by
    have := card_commV_of_natSL hV hperf hX.1 hsl (by norm_num)
    rw [this, mul_comm]
  have h16 := CGT6M.card_le_sixteen_fixSub_of_comm hV Y hyY hy5 hU'
  rcases hFoote V hV G T Y h hY5 with hQ | hQ | hQ | hQ | hQ | hQ | hQ
  · exact CGT6M.false_of_rank_four_psl3_5 (Subgroup.subtype (conjClosure Y G))
      (Subgroup.subtype_injective _) hV π hπs hπk.le (y := ⟨y, hYL hyY⟩)
      (fun h1 => hy1 (congrArg Subtype.val h1)) (Subtype.ext hy5) h16
      (CGT6M.not_five_dvd_card_ker_psl3_5 π hπs hπk.le hQ) hQ
  · exact CGT6M.false_of_rank_four_psu3_5 (Subgroup.subtype (conjClosure Y G))
      (Subgroup.subtype_injective _) hV π hπs hπk.le (y := ⟨y, hYL hyY⟩)
      (fun h1 => hy1 (congrArg Subtype.val h1)) (Subtype.ext hy5) h16
      (CGT6M.not_five_dvd_card_ker_psu3_5 π hπs hπk.le hQ) hQ
  · exact inspect (hExc.1 _ hQ)
  · obtain ⟨f, hf, hQ'⟩ := hQ
    exact inspect (hExc.2 _ f hf hQ')
  · exact inspect (CGT6M.coverInv_psp4 hGA _ hQ)
  · exact inspect (CGT6M.coverInv_psl4 hGA _ hQ)
  · exact inspect (hU _ hQ)

end CFSG.CGT.PushingUpLit.CGT6
