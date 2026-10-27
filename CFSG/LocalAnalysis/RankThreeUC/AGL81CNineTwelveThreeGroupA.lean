module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveIrred
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.Walter.Cited.HuppertBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped MatrixGroups
open scoped commutatorElement


private theorem card_GL_three_zero : Nat.card (GL (Fin 0) (ZMod 3)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide +kernel

private theorem card_GL_three_one : Nat.card (GL (Fin 1) (ZMod 3)) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide +kernel

private theorem card_GL_three_two : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide +kernel

private theorem card_GL_three_three : Nat.card (GL (Fin 3) (ZMod 3)) = 11232 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide +kernel

private theorem card_GL_three_four : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide +kernel

theorem prime_dvd_card_GL_three {k q : ℕ} (hk : k ≤ 4) (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hdvd : q ∣ Nat.card (GL (Fin k) (ZMod 3))) :
    (k = 3 ∧ q = 13) ∨ (k = 4 ∧ (q = 5 ∨ q = 13)) := by
  interval_cases k
  · rw [card_GL_three_zero] at hdvd
    exact absurd hdvd (hq.not_dvd_one)
  · rw [card_GL_three_one] at hdvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd) hq2
  · rw [card_GL_three_two] at hdvd
    rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (hq.dvd_of_dvd_pow h)) hq2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h) hq3
  · rw [card_GL_three_three] at hdvd
    rw [show (11232 : ℕ) = 2 ^ 5 * 3 ^ 3 * 13 by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | h
    · rcases hq.dvd_mul.mp h with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
          (hq.dvd_of_dvd_pow h')) hq2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
          (hq.dvd_of_dvd_pow h')) hq3
    · exact Or.inl ⟨rfl, (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13)).mp h⟩
  · rw [card_GL_three_four] at hdvd
    rw [show (24261120 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 13 by norm_num] at hdvd
    refine Or.inr ⟨rfl, ?_⟩
    rcases hq.dvd_mul.mp hdvd with h | h
    · rcases hq.dvd_mul.mp h with h' | h'
      · rcases hq.dvd_mul.mp h' with h'' | h''
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
            (hq.dvd_of_dvd_pow h'')) hq2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
            (hq.dvd_of_dvd_pow h'')) hq3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp h')
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13)).mp h)

theorem orderOf_ne_thirteen_of_card_center {V : Type} [Group V] [Finite V]
    (hV : Nat.card V = 3 ^ 4) (hZ : Nat.card (center V) = 3 ^ 2) (β : MulAut V) :
    orderOf β ≠ 13 := by
  intro hβ
  let C : Subgroup V :=
    { carrier := {x : V | β x = x}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change β a = a at ha
        change β b = b at hb
        change β (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change β a = a at ha
        change β a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hCmem : ∀ x : V, x ∈ C ↔ β x = x := fun x => Iff.rfl
  have hsetT : ({x : V | x ∈ (⊤ : Subgroup V) ∧ β x = x} : Set V) = (C : Set V) := by
    ext x
    simp only [Set.mem_setOf_eq, Subgroup.mem_top, true_and, SetLike.mem_coe]
    exact (hCmem x).symm
  have hmod1 : Nat.card C ≡ 3 [MOD 13] := by
    have h := card_modEq_card_fixed_mulAut (q := 13) (β := β) (by norm_num) hβ
      (B := ⊤) (by intro b hb; simp)
    rw [Subgroup.card_top, hsetT, hV] at h
    exact h.symm.trans (by norm_num : (3 : ℕ) ^ 4 ≡ 3 [MOD 13])
  have hCcard : Nat.card C = 3 := by
    obtain ⟨j, hjle, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (hV ▸ C.card_subgroup_dvd_card)
    have hjmod : (3 : ℕ) ^ j ≡ 3 [MOD 13] := by rw [← hj]; exact hmod1
    interval_cases j
    · norm_num at hjmod
    · rw [hj]; norm_num
    · norm_num at hjmod
    · norm_num at hjmod
    · exfalso
      have hCtop : C = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hj, hV]
      have hβ1 : β = 1 := by
        ext x
        have hx : x ∈ C := by rw [hCtop]; exact Subgroup.mem_top x
        exact (hCmem x).mp hx
      rw [hβ1, orderOf_one] at hβ
      norm_num at hβ
  have hsetZ : ({x : V | x ∈ Subgroup.center V ∧ β x = x} : Set V) =
      (C ⊓ Subgroup.center V : Set V) := by
    ext x
    simp only [Set.mem_setOf_eq, Subgroup.mem_inf, SetLike.mem_coe]
    constructor
    · rintro ⟨hxZ, hxfix⟩; exact ⟨(hCmem x).mpr hxfix, hxZ⟩
    · rintro ⟨hxC, hxZ⟩; exact ⟨hxZ, (hCmem x).mp hxC⟩
  have hZinv : ∀ z ∈ Subgroup.center V, β z ∈ Subgroup.center V := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have hcalc : β z * g = g * β z := by
      calc
        β z * g = β (z * β.symm g) := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = β (β.symm g * z) := by rw [(hz (β.symm g)).symm]
        _ = g * β z := by rw [map_mul, MulEquiv.apply_symm_apply]
    exact hcalc.symm
  have hZmod : Nat.card ↥(C ⊓ Subgroup.center V) ≡ 9 [MOD 13] := by
    have h := card_modEq_card_fixed_mulAut (q := 13) (β := β) (by norm_num) hβ
      (B := Subgroup.center V) hZinv
    rw [hsetZ, hZ] at h
    exact h.symm.trans (by norm_num : (3 : ℕ) ^ 2 ≡ 9 [MOD 13])
  have hZfix_card : Nat.card ↥(C ⊓ Subgroup.center V) = 9 := by
    have hle : Nat.card ↥(C ⊓ Subgroup.center V) ≤ 9 := by
      have := Subgroup.card_le_of_le (inf_le_right : C ⊓ Subgroup.center V ≤
        Subgroup.center V)
      rwa [hZ] at this
    have hlt : Nat.card ↥(C ⊓ Subgroup.center V) < 13 := by omega
    rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 9 < 13)] at hZmod
    exact hZmod
  have hCle : Nat.card ↥(C ⊓ Subgroup.center V) ≤ Nat.card C :=
    Subgroup.card_le_of_le inf_le_left
  omega

theorem exists_omega_of_mulAut {R : Type} [Group R] [Finite R] (hR : IsPGroup 3 R)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup R) ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {α : MulAut R} (hα : orderOf α = p) :
    ∃ D : Subgroup R, D.Characteristic ∧ (∀ x ∈ D, x ^ 3 = 1) ∧
      ⁅D, (⊤ : Subgroup R)⁆ ≤ D ⊓ centralizer (D : Set R) ∧ (∃ d ∈ D, α d ≠ d) ∧
      ((p = 13 ∧ IsMulCommutative ↥D ∧ Nat.card D = 27 ∧ D ≤ center R) ∨
        (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥D ∧ Nat.card D = 3 ^ 5)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, hCcrit, hCne, hCfaith, hDset, hDchar, hDne, hDcomm, hDexp, hDfixP, hDdet⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (P := R) (p := 3)
      (by norm_num) hR
  let D : Subgroup R := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn 3 C
  haveI : D.Characteristic := hDchar
  have hDp : IsPGroup 3 ↥D := hR.to_subgroup D
  have hDexp' : ∀ x : ↥D, x ^ 3 = 1 := fun x => by
    apply Subtype.ext
    simpa using hDexp (x : R) x.2
  have hDrank : CFSG.pRank 3 ↥D ≤ 3 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top).trans hrk
  have hclass : commutator ↥D ≤ Subgroup.center ↥D := by
    change ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ ≤ Subgroup.center ↥D
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hmem : ⁅(x : R), (y : R)⁆ ∈ ⁅D, (⊤ : Subgroup R)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top (y : R))
    have hcen : (z : R) * ⁅(x : R), (y : R)⁆ = ⁅(x : R), (y : R)⁆ * (z : R) :=
      Subgroup.mem_centralizer_iff.mp (hDcomm hmem).2 (z : R) z.2
    have hcoe : ((⁅x, y⁆ : ↥D) : R) = ⁅(x : R), (y : R)⁆ :=
      map_commutatorElement (f := D.subtype) x y
    simpa only [Subgroup.coe_mul, hcoe] using hcen
  have hfratt : frattini ↥D = commutator ↥D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hDexp'
  have hWp : IsPGroup 3 (↥D ⧸ frattini ↥D) := hDp.to_quotient (frattini ↥D)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWp
  have hWc_card : Nat.card (↥D ⧸ commutator ↥D) = 3 ^ k := by
    rw [← hfratt]
    exact hk
  have hqr :=
    CFSG.RankThree.PartTwo.quotient_commutator_rank (p := 3) Nat.prime_three hDexp' hWc_card
  have hk_le : k ≤ 4 := by
    rw [← hqr.2]
    exact (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds (p := 3) hDp hDexp'
      hclass).2.2 hDrank
  let β : MulAut ↥D := MulAut.characteristic D α
  have hcopα : Nat.Coprime (orderOf α) 3 := by
    rw [hα]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  have hDmove : ∃ d ∈ D, α d ≠ d := by
    by_contra h
    push Not at h
    have hα1 : α = 1 := hDdet α hcopα h
    have : orderOf α = 1 := by rw [hα1, orderOf_one]
    rw [hα] at this
    exact hp.one_lt.ne' this
  have hD_ne_bot : D ≠ ⊥ := by
    obtain ⟨d, hd, hdm⟩ := hDmove
    intro hbot
    rw [hbot] at hd
    have hd1 : d = 1 := Subgroup.mem_bot.mp hd
    rw [hd1] at hdm
    exact hdm (map_one α)
  have hβ_ne : β ≠ 1 := by
    obtain ⟨d, hd, hdm⟩ := hDmove
    intro hβ1
    apply hdm
    have h1 : MulAut.characteristic D α ⟨d, hd⟩ = ⟨d, hd⟩ := by
      rw [show MulAut.characteristic D α = (1 : MulAut ↥D) from hβ1, MulAut.one_apply]
    have h2 := congrArg (fun y : ↥D => (y : R)) h1
    rw [MulAut.characteristic_apply_apply_coe] at h2
    simpa using h2
  have hβdvd : orderOf β ∣ p := by
    have h1 : orderOf β ∣ orderOf α := orderOf_map_dvd (MulAut.characteristic D) α
    rwa [hα] at h1
  have hβ_eq : orderOf β = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf β) hβdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hβ_ne
    · exact h
  have hcopβ : Nat.Coprime 3 (orderOf β) := by
    rw [hβ_eq]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd).symm)
  let γ : MulAut (↥D ⧸ frattini ↥D) := CFSG.Walter.Huppert.frattiniAut ↥D β
  have hγ_ne : γ ≠ 1 := by
    intro hγ1
    exact hβ_ne (CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one (p := 3) hDp hcopβ hγ1)
  have hγdvd : orderOf γ ∣ p := by
    have h1 : orderOf γ ∣ orderOf β := orderOf_map_dvd (CFSG.Walter.Huppert.frattiniAut ↥D) β
    rwa [hβ_eq] at h1
  have hγ_eq : orderOf γ = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf γ) hγdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hγ_ne
    · exact h
  haveI : IsMulCommutative (↥D ⧸ frattini ↥D) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini ↥D)).mpr (by
      rw [hfratt])
  have hWcomm : ∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a := fun a b => mul_comm' a b
  have hWpow : ∀ a : ↥D ⧸ frattini ↥D, a ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.quotient_pow_eq_one (p := 3) hDexp' (frattini ↥D)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hWcomm hWpow hk
  have hp_dvd_GL : p ∣ Nat.card (GL (Fin k) (ZMod 3)) := by
    rw [← CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
    rw [← hγ_eq]
    exact orderOf_dvd_natCard γ
  have hkpq := prime_dvd_card_GL_three hk_le hp hp2 hp3 hp_dvd_GL
  have hpRank : CFSG.pRank 3 ↥D = 3 := by
    have hnotle : ¬ CFSG.pRank 3 ↥D ≤ 2 := by
      intro hle2
      have hk2 : k ≤ 2 := by
        rw [← hqr.2]
        exact (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds (p := 3) hDp hDexp'
          hclass).1 hle2
      rcases hkpq with ⟨hk3, -⟩ | ⟨hk4, -⟩ <;> omega
    omega
  obtain ⟨i, hi, -⟩ :=
    (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds (p := 3) hDp hDexp'
      hclass).2.1 hpRank
  refine ⟨D, hDchar, hDexp, hDcomm, hDmove, ?_⟩
  fin_cases i
  ·
    simp at hi
    obtain ⟨hE, hcard, hrank⟩ := hi
    have hk3 : k = 3 := hqr.2.symm.trans hrank
    have hp13 : p = 13 := by
      rcases hkpq with ⟨-, h13⟩ | ⟨hk4, -⟩
      · exact h13
      · omega
    have hDcard27 : Nat.card ↥D = 27 := hcard.trans (by norm_num)
    refine Or.inl ⟨hp13, hE.toIsMulCommutative, hDcard27, ?_⟩
    have hβ13 : orderOf β = 13 := by rw [hβ_eq, hp13]
    let B : Subgroup ↥D := (Subgroup.center R).subgroupOf D
    have hBinv : ∀ b ∈ B, β b ∈ B := by
      intro b hb
      change (b : R) ∈ Subgroup.center R at hb
      show ((β b : ↥D) : R) ∈ Subgroup.center R
      rw [MulAut.characteristic_apply_apply_coe]
      rw [Subgroup.mem_center_iff] at hb ⊢
      intro g
      have hcalc : α (b : R) * g = g * α (b : R) := by
        calc
          α (b : R) * g = α ((b : R) * α.symm g) := by
            rw [map_mul, MulEquiv.apply_symm_apply]
          _ = α (α.symm g * (b : R)) := by rw [(hb (α.symm g)).symm]
          _ = g * α (b : R) := by rw [map_mul, MulEquiv.apply_symm_apply]
      exact hcalc.symm
    have hB_ne : B ≠ ⊥ := by
      have hDcen_ne : D ⊓ Subgroup.center R ≠ ⊥ := by
        haveI : Group.IsNilpotent R := hR.isNilpotent
        exact Group.IsNilpotent.inf_center_ne_bot_of_normal (G := R) (H := D) hD_ne_bot
      intro hbot
      apply hDcen_ne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxD, hxZ⟩ := hx
      have hmem : (⟨x, hxD⟩ : ↥D) ∈ B := hxZ
      rw [hbot] at hmem
      have hx1 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
      rw [hx1]
      exact Subgroup.one_mem ⊥
    rcases eq_bot_or_eq_top_of_orderOf_eq_thirteen hDcard27 hβ13 hBinv with h | h
    · exact absurd h hB_ne
    · exact Subgroup.subgroupOf_eq_top.mp h
  ·
    simp at hi
    obtain ⟨hcard, hZ, hcomm, hrank⟩ := hi
    have hk4 : k = 4 := hqr.2.symm.trans hrank
    have hext : CFSG.IsExtraspecialPGroup 3 ↥D := ⟨hDp, hcomm, hfratt.trans hcomm, hZ⟩
    have hp5 : p = 5 := by
      rcases hkpq with ⟨hk3, -⟩ | ⟨-, h5 | h13⟩
      · omega
      · exact h5
      · exact absurd (by rw [hβ_eq, h13] : orderOf β = 13)
          (orderOf_ne_thirteen_of_extraspecial hext hcard β)
    exact Or.inr ⟨hp5, hext, hcard⟩
  ·
    simp at hi
    obtain ⟨hcard, hZ, hc, hrank⟩ := hi
    have hk3 : k = 3 := hqr.2.symm.trans hrank
    have hp13 : p = 13 := by
      rcases hkpq with ⟨-, h13⟩ | ⟨hk4, -⟩
      · exact h13
      · omega
    exact absurd (by rw [hβ_eq, hp13] : orderOf β = 13)
      (orderOf_ne_thirteen_of_card_center hcard hZ β)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
