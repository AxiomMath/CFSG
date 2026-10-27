module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR18
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR9
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR15

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G]

theorem p79_of_data {t : G} {J B : Subgroup G}
    (hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J) (hnqs : ¬ CFSG.IsQuasisimple ↥J)
    (hsimple : IsSimpleGroup (kBar J))
    (hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J))
    (hBN : B ≤ normalizer (J : Set G)) (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hrk : 4 ≤ pRank 2 ↥B)
    (hglue : ∃ (V : Subgroup G) (hVB : V ≤ B) (b : G) (hbB : b ∈ B), Nat.card B = 2 * Nat.card V ∧
      ∃ c : kBar J, Nat.Prime (orderOf c) ∧ Odd (orderOf c) ∧
        (∀ v (hv : v ∈ V), barAct J ⟨v, hBN (hVB hv)⟩ c = c) ∧ barAct J ⟨b, hBN hbB⟩ c = c⁻¹) :
    ∃ (W V : Subgroup G) (b : G) (X₀ X₁ : Subgroup G),
      W ≤ V ∧ V ≤ B ∧ Nat.card B = 2 * Nat.card V ∧ Nat.card B = 4 * Nat.card W ∧ b ∈ B ∧
      Odd (Nat.card X₀) ∧ Odd (Nat.card X₁) ∧
      X₀ ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ∧ X₁ ≤ centralizer ({t} : Set G) ∧
      (∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w) ∧ (∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v) ∧
      (∀ g ∈ B, ∀ z ∈ X₀, g * z * g⁻¹ ∈ X₀) ∧ (∀ z ∈ X₁, ∀ z' ∈ X₀, z * z' * z⁻¹ ∈ X₀) ∧
      (∀ z ∈ X₁, b * z * b⁻¹ = z⁻¹) ∧ ⁅⁅X₀, X₁⁆, X₁⁆ ≠ ⊥ ∧
      ((∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
        (∀ v ∈ V, v ∉ W → ∃ z ∈ ⁅⁅X₀, X₁⁆, X₁⁆, v * z ≠ z * v)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVB, b, hbB, hVcard, c, hcp, hcodd, hVc, hbc⟩ := hglue
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr (C3.Layer1.Bk.perfect_of_isPCompIn hJc)
  have hVel : CFSG.IsElementaryAbelian 2 ↥V := isElementaryAbelian_le hBel hVB
  have hrkV : 3 ≤ pRank 2 ↥V := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hBel
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hVel
    have h3 : 2 ^ 4 ≤ 2 ^ pRank 2 ↥B := Nat.pow_le_pow_right (by norm_num) hrk
    by_contra hlt
    have h4 : pRank 2 ↥V ≤ 2 := by omega
    have h5 : 2 ^ pRank 2 ↥V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h4
    omega
  obtain ⟨W, X₀, X₁, hWV, hWcard, hrest⟩ := p79_of_cbar hperf hsimple hnqs hdih hJc.1
    (pPrimeCoreOf_le_of_isPCompIn hJc) hBN hBel hVB hrkV hbB hcp hcodd hVc hbc
  exact ⟨W, V, b, X₀, X₁, hWV, hVB, hVcard, by omega, hbB, hrest⟩

omit [Finite G] in
theorem normalizer_and_inner_of_le_R {x : G} {K T B : Subgroup G}
    (hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K)) :
    ∃ hBK : B ≤ normalizer (K : Set G),
      ∀ g (hg : g ∈ B), barAct K ⟨g, hBK hg⟩ ∈ IVK.innAut (kBar K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : T ⊓ K ≤ normalizer (K : Set G) := fun p hp => Subgroup.le_normalizer hp.2
  have hQc : ∀ q ∈ T ⊓ CxK x K, q ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    fun q hq => hq.2.2
  have hQN : T ⊓ CxK x K ≤ normalizer (K : Set G) := fun q hq => (hQc q hq).1
  have hBK : B ≤ normalizer (K : Set G) := hBR.trans (sup_le hPN hQN)
  refine ⟨hBK, ?_⟩
  let 𝒢 : Subgroup ↥(normalizer (K : Set G)) := (IVK.innAut (kBar K)).comap (barAct K)
  let 𝒢' : Subgroup G := 𝒢.map (normalizer (K : Set G)).subtype
  have hP𝒢 : T ⊓ K ≤ 𝒢' := by
    intro p hp
    refine ⟨⟨p, hPN hp⟩, ?_, rfl⟩
    show barAct K ⟨p, hPN hp⟩ ∈ IVK.innAut (kBar K)
    rw [barAct_of_mem hp.2]
    exact ⟨_, rfl⟩
  have hQ𝒢 : T ⊓ CxK x K ≤ 𝒢' := by
    intro q hq
    refine ⟨⟨q, hQN hq⟩, ?_, rfl⟩
    show barAct K ⟨q, hQN hq⟩ ∈ IVK.innAut (kBar K)
    rw [(barAct_eq_one_iff _).2 (hQc q hq)]
    exact (IVK.innAut (kBar K)).one_mem
  intro g hg
  obtain ⟨h, hh, hhg⟩ := (sup_le hP𝒢 hQ𝒢) (hBR hg)
  have : h = ⟨g, hBK hg⟩ := Subtype.ext hhg
  rw [← this]
  exact hh

theorem p79_of_pick (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) : B_p72c_P79 := by
  intro G _ _ hG x y K T S hstd hnt ρ hρ hρh B t J hpick
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hP⟩ := hstd.centerless_and_shape hG hL34 h102
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hpick.pump.2.1.2.2
  have hxJ : x ∈ normalizer (J : Set G) := hpick.normalizes hpick.x_mem
  have htB : t ∈ B := hpick.t_mem.1
  obtain ⟨e⟩ := hpick.bar
  rcases hρ with rfl | rfl | rfl
  ·
    obtain ⟨hK, -⟩ := hρh
    have hmem := hpick.mem
    obtain ⟨⟨hBR, -⟩, -⟩ := hmem
    obtain ⟨F, _, _, hF, -, ⟨eF⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq.1) hK
    have hsimpleK : IsSimpleGroup (kBar K) := IVK.Proofs2.isSimpleGroup_of_l2 hF eF
    have hsimple : IsSimpleGroup (kBar J) := (e.isSimpleGroup_congr).2 hsimpleK
    have hdihK := hasDihedralSylowTwo_of_hasL2Model (fun q hq => hq.1) hK
    have hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e hdihK
    refine p79_of_data hJc hpick.nonqs hsimple hdih hpick.normalizes hpick.elem hpick.rank ?_
    obtain ⟨hBK, hinner⟩ := normalizer_and_inner_of_le_R hBR
    have hEel : CFSG.IsElementaryAbelian 2 ↥(B ⊓ (T ⊓ K)) :=
      isElementaryAbelian_le hpick.elem inf_le_left
    have hE4 : 4 ≤ Nat.card ↥(B ⊓ (T ⊓ K)) := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel, hpick.rank_P, pRank_eq_two_of_rankTwoShape hP]
      norm_num
    exact exists_cbar_L2 hpick.pump hxJ e hK hpick.normalizes hBK hpick.elem htB hinner
      inf_le_left (inf_le_right.trans inf_le_right) hEel hE4
  ·
    obtain ⟨D, ⟨hDP, hPK, hDel, hD4, eA, hD6⟩, hBeq⟩ := hpick.mem
    have hDB : D ≤ B := by
      rw [hBeq]
      intro d hd
      exact Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem S.one_mem
        ⟨d, hd, by simp⟩)
    have hsimpleK : IsSimpleGroup (kBar K) :=
      (eA.isSimpleGroup_congr).2 (alternatingGroup.isSimpleGroup (by simp))
    have hsimple : IsSimpleGroup (kBar J) := (e.isSimpleGroup_congr).2 hsimpleK
    have hdihK : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar K) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eA
        CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
    have hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e hdihK
    refine p79_of_data hJc hpick.nonqs hsimple hdih hpick.normalizes hpick.elem hpick.rank ?_
    exact exists_cbar_A7 hpick.pump hxJ e eA hpick.normalizes hpick.elem htB hDB (hDP.trans hPK)
      hDel hD4 hD6
  ·
    obtain ⟨-, D, ⟨hDP, hPK, hDel, hD4, eA, hD6⟩, hDB⟩ := hpick.mem
    have hsimpleK : IsSimpleGroup (kBar K) :=
      (eA.isSimpleGroup_congr).2 (alternatingGroup.isSimpleGroup (by simp))
    have hsimple : IsSimpleGroup (kBar J) := (e.isSimpleGroup_congr).2 hsimpleK
    have hdihK : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar K) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eA
        CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
    have hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e hdihK
    refine p79_of_data hJc hpick.nonqs hsimple hdih hpick.normalizes hpick.elem hpick.rank ?_
    exact exists_cbar_A7 hpick.pump hxJ e eA hpick.normalizes hpick.elem htB hDB (hDP.trans hPK)
      hDel hD4 hD6

theorem u2_of_oddcent (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hKG : B_ivk_oddcent) :
    B_thm2_p72c_U2 :=
  u2_of_p79 hL34 h102 hKG (p79_of_pick hL34 h102)

end Final

end CFSG.GH74.GLS
