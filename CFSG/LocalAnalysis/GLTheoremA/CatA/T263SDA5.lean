module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FRStruct
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem sd_card_three_group_le {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hnc : ∃ a b : G, a * b ≠ b * a) (hG : Nat.card G = 60)
    (A : Subgroup (MulAut G)) (hA : IsPGroup 3 ↥A) : Nat.card ↥A ≤ 3 := by
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := G) hG
  have hAut : Nat.card (MulAut G) ≤ 120 := by
    rw [CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr e]
    exact CFSG.LargeExtraspecial.S12Tri.card_mulAut_alternatingGroup_five_le
  have hcen : Subgroup.center G = ⊥ := sd_center_eq_bot_of_simple hs hnc
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcen
  have hdvd60 : 60 ∣ Nat.card (MulAut G) := by
    have h1 : Nat.card (MulAut.conj : G →* MulAut G).range = 60 := by
      rw [← hG]
      exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    rw [← h1]
    exact Subgroup.card_subgroup_dvd_card _
  haveI : Finite (MulAut G) := Finite.of_injective (fun σ : MulAut G => (σ : G → G)) DFunLike.coe_injective
  have hpos : 0 < Nat.card (MulAut G) := Nat.card_pos
  obtain ⟨j, hj⟩ := hA.exists_card_eq
  have hjdvd : 3 ^ j ∣ Nat.card (MulAut G) := by
    rw [← hj]
    exact Subgroup.card_subgroup_dvd_card A
  obtain ⟨m, hm⟩ := hdvd60
  have hm12 : m ≤ 2 := by omega
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    have h9 : 9 ∣ 3 ^ j := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact pow_dvd_pow 3 hj2
    have h9' : 9 ∣ Nat.card (MulAut G) := h9.trans hjdvd
    rw [hm] at h9'
    interval_cases m <;> omega
  rw [hj]
  calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
    _ = 3 := by norm_num

theorem sd_concl_of_a5 (hLB : LBalanceAt Ω 3) (hK : CFSG.Open.IsKGroup Ω)
    {S B B₀ T' : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore 3 ↥S = ⊥) (hBel : IsElemAbelian 3 B) (h4 : 3 ^ 4 ≤ Nat.card ↥B)
    (hB₀B : B₀ ≤ B) (hxB₀ : x ∈ B₀) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hT'2 : IsPGroup 2 ↥T') (hBT' : B ≤ Subgroup.normalizer (T' : Set Ω)) {J : Subgroup Ω}
    (hJ : SDCore 3 S B₀ T' x J) (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) :
    T263GConcl 3 S B := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => isElemAbelian_commute hBel ha hb
  have hxB : x ∈ B := hB₀B hxB₀
  have hJo : CFSG.Open.IsQuasisimple ↥J := hJ.comp.2.2
  have hJn : CFSG.IsQuasisimple ↥J := native_of_open_dx hJo
  have hJX : J ≤ S ⊓ Subgroup.centralizer ({x} : Set Ω) := hJ.comp.1
  obtain ⟨hBX, hBP, hPT'⟩ := norm_data_dx hSn hBab hB₀B hxB₀ hBT'
  have hPX : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω) := hJ.inn.trans (sup_le hJX inf_le_left)
  obtain ⟨W, hWJ, hW2, hWB, hWC⟩ := exists_two_of_act_open hJX hJo (hT'2.to_le hPT') hPX
    hJ.inn hJ.act (inf_le_left.trans hBX) inf_le_right (inf_le_left.trans hBP)
  have hJcomp : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J :=
    glaPComponent_of_isComponentOf_of_dvd hp hJ.comp hJ.pdvd
  have hJq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    open_of_native_dx (isQuasisimple_pQuot_of_dvd hp hJn hJ.pdvd)
  have hWnc : ¬ W ≤ GLAPPrimeCoreOf 3 J := fun h =>
    hWC ((h.trans (glaPPrimeCoreOf_le_centralizer_of_dvd hp hJn hJ.pdvd)).trans inf_le_right)
  obtain ⟨D, I, hDB, hI, hBI, hIq, ⟨e⟩, -, -⟩ := t263DiagStep_holds 3 hp (by norm_num) Ω S B x J W
    hSn hSq hSp hBel hxB hxC hJcomp hJq hWJ hW2 hWB hWnc
  obtain ⟨ε⟩ := nonempty_pSimple_equiv_of_dvd hp hJn hJ.pdvd
  have hcard : Nat.card (PSimple 3 I) = 60 := by
    rw [Nat.card_congr (e.trans ε).toEquiv]
    exact h60
  have hsimple : IsSimpleGroup (PSimple 3 I) := hIq.2
  have hnc : ∃ a b : PSimple 3 I, a * b ≠ b * a := (native_of_open_dx hIq).2.2
  set ψ := actionHom I B hBI 3 with hψ
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hBel
  have hrange : Nat.card ↥ψ.range ≤ 3 :=
    sd_card_three_group_le hsimple hnc hcard ψ.range
      (hBp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
  have hker : 3 ^ 3 ≤ Nat.card ↥ψ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ Nat.card ↥ψ.ker * 3 :=
      Nat.mul_le_mul_left _ hrange
    omega
  set E₀ : Subgroup Ω := ψ.ker.map B.subtype with hE₀
  have hE₀B : E₀ ≤ B := Subgroup.map_subtype_le _
  have hE₀card : Nat.card ↥E₀ = Nat.card ↥ψ.ker :=
    Subgroup.card_map_of_injective B.subtype_injective
  obtain ⟨E, hEE₀, hEcard⟩ := exists_sub_card_pow_three hp (isElemAbelian_mono hBel hE₀B)
    (hE₀card ▸ hker)
  have hEB : E ≤ B := hEE₀.trans hE₀B
  have hEdQ : E ≤ dQ I := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 (hEE₀ hg)
    have hb1 : ψ b = 1 := hb
    rw [hψ, actionHom_apply] at hb1
    have hcm := (chevAut_eq_one_iff hp hI (hBI b.2)).1 hb1
    have hcm' := (mem_centModSubgroup (p := 3) (L := I)).1 ((centMod_iff).1 hcm)
    exact (mem_dQ_of_mem_normalizer (hBI b.2)).2 fun y hy => hcm'.2 y hy
  obtain ⟨J', hJ'⟩ := coverStmt Ω (S ⊓ Subgroup.centralizer (D : Set Ω)) I E hI
    (hBp.to_le hEB) hEdQ |>.imp fun J' h => h.1
  have hlay : GLAPLayer 3 (I ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ :=
    (CFSG.LocalAnalysis.GLTheoremA.S3.glaPLayer_ne_bot_iff hp).2 ⟨J', hJ'⟩
  have hlayer := layer_ne_bot_of_desc hp hSn hBel hDB hI hEB hlay
  have hcardE : 3 ^ 3 ≤ Nat.card ↥(E ⊔ D) := by
    have := Subgroup.card_le_of_le (le_sup_left : E ≤ E ⊔ D)
    rw [hEcard] at this
    exact this
  exact Or.inl (kConcl_of_ge hp hLB hK hSn hBel (sup_le hEB hDB) hcardE hlayer)

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
