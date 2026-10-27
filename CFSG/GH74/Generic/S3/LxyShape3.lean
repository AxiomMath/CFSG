module

public import CFSG.GH74.Generic.S3.LxyShape2
public import CFSG.GH74.Generic.S3.LxySplit
public import CFSG.GH74.Generic.S3.OnlyInvT1
public import CFSG.GH74.Generic.S3.LyVert
public import CFSG.GH74.Generic.S1.CompIdent

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS (InG2 InC2 InT2 InB2 InCalK2 HasSL2Model)
open CFSG.GH74.Filter.ClassicalOdd (Q8)
open scoped MatrixGroups commutatorElement

section J1

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_hasSL2Model (hnd : NbrData G t p f x y Iw Iv) :
    HasSL2Model ↥(S45.barSub (y * x) Iv) (fun q => q = p ^ f) := by
  obtain ⟨F, hFf, hFfin, hFc, ⟨eS⟩⟩ := hnd.Iv_iso
  obtain ⟨φΛ, -⟩ := hnd.lxy_barSub_equiv hnd.lxy_Iv_le
  exact ⟨F, hFf, hFfin, hFc, ⟨(φΛ.symm.trans eS.symm).trans
    (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F).symm⟩⟩

theorem NbrData.lxy_false_of_J1 (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y * x} : Set G)))} (hle : S45.barSub (y * x) Iv ≤ L)
    (hJ : CFSG.Blueprint.NativeSporadic.IsSporadic ↥L .J1) : False := by
  obtain ⟨e⟩ := hJ
  let e' : ↥L ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hodd : Odd (p ^ f) := (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
  obtain ⟨ψ, hψinj, hψΛ⟩ := CFSG.GH74.Generic.S1.exists_q8_of_hasSL2Model hodd hnd.lxy_hasSL2Model
  let ψ' : Q8 →* ↥L := ψ.codRestrict L (fun g => hle (hψΛ g))
  let θ : Q8 →* CFSG.Open.walterJ1 := e'.toMonoidHom.comp ψ'
  have hψ' : Function.Injective ψ' := by
    intro a b h
    apply hψinj
    exact congrArg Subtype.val h
  have hθ : Function.Injective θ := e'.injective.comp hψ'
  have hP : IsPGroup 2 θ.range := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv.symm, Nat.card_eq_fintype_card]
    decide
  obtain ⟨P, hPle⟩ := hP.exists_le_sylow
  have hcomm := CFSG.Walter.J1Props.hasAbelianSylowTwo P
  have hab : ∃ a b : Q8, a * b ≠ b * a := by decide
  obtain ⟨a, b, hab⟩ := hab
  apply hab
  have ha : θ a ∈ P := hPle ⟨a, rfl⟩
  have hb : θ b ∈ P := hPle ⟨b, rfl⟩
  have := hcomm.is_comm.comm ⟨θ a, ha⟩ ⟨θ b, hb⟩
  apply hθ
  rw [map_mul, map_mul]
  exact congrArg Subtype.val this

end J1


section Ree

open CFSG.Open (ordA ordTwistedA ordRee)

theorem d2_le_six_of_shapeS4
    {G : Type} [Group G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hc : IsComponent K) (hG2 : InG2 ↥K) (hsh : ShapeS4 x K) : d2 ↥K ≤ 6 := by
  obtain ⟨⟨f₀, hmod⟩, -⟩ := hsh
  have hs : IsSimpleGroup ↥K := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hmod
  have hcen : center ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hc.1
      apply hab
      have : a ∈ center ↥K := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
  have hlie : OfLieType ↥K :=
    ⟨.twistedG2, 0, 3, f₀, CFSG.GH74.lieModel_of_mulEquiv (mulEquivOfCenterBot hcen) hmod⟩
  have hnL3 : ¬ IsL3Odd ↥K := by
    rintro ⟨p'', f'', hp'', hp2'', hm | hm⟩
    · obtain ⟨k, -, hk⟩ := card_of_lieModel_twistedG2 hmod
      have h1 : Nat.card ↥K = ordA 2 (p'' ^ f'') := card_of_lieModel_PSL (by norm_num) hm
      have hodd : (p'' ^ f'') % 2 = 1 := Nat.odd_iff.1 ((hp''.odd_of_ne_two hp2'').pow)
      have h16 := sixteen_dvd_ordA_two hodd
      rw [← h1, hk] at h16
      exact not_sixteen_dvd_ordRee k h16
    · obtain ⟨k, -, hk⟩ := card_of_lieModel_twistedG2 hmod
      have h1 : Nat.card ↥K = ordTwistedA 2 (p'' ^ f'') := card_of_lieModel_PSU (by norm_num) hp2'' hm
      have hodd : (p'' ^ f'') % 2 = 1 := Nat.odd_iff.1 ((hp''.odd_of_ne_two hp2'').pow)
      have h16 := sixteen_dvd_ordTwistedA_two hodd
      rw [← h1, hk] at h16
      exact not_sixteen_dvd_ordRee k h16
  exact Nat.sInf_le ⟨hG2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hlie, hnL3⟩)))))⟩

end Ree


section Main

theorem b_S3_LxyShapeJNT_of_parts
    (hF : GenericKnownFacts) (hKG : TwoThinKGroupVerticalQ Gen4Cen) (hB2 : B2NoncentralTable) :
    B_S3_LxyShapeJNT := by
  intro G _ _ x K hset hmax _hthin _honly _hLy t p f y Iw Iv hnd _himg L hL hle hne
  have hgen4 : Gen4 (barQ ↥(centralizer ({y * x} : Set G))) :=
    (gen4Cen_barQ hset.gen4 hnd.lxy_inv).gen4
  have hKP : GLS.IsKProperSimple G := ⟨hset.simple, hset.nonab, CFSG.GH74.kProper_of_kgh hset.kgh⟩
  have hcal : InCalK2 ↥L := GLS.inCalK2_of_isComponent hKP hnd.lxy_inv hL
  by_cases hC : InC2 ↥L ∨ InT2 ↥L
  · exfalso
    exact hnd.lxy_false_of_inB2 hB2 hL hle hne (hnd.lxy_vertical_inB2 hKG hset.gen4 hC hL hle)
  · push Not at hC
    have hG2 : InG2 ↥L := ⟨hcal, hC.1, hC.2⟩
    have h7 : d2 ↥K = 7 := d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
    have hle7 : d2 ↥K ≤ d2 ↥L := (hmax.2 (y * x) L ⟨hnd.lxy_inv, hL, hG2⟩).1
    rcases generic_shapes_of_inG2 hF hset.simple hset.nonab hset.gen4 hset.kgh hnd.lxy_inv hG2 with
      h1 | h2 | h3 | h4 | h5
    · have := d2_le_six_of_shapeS1 hL hG2 h1
      omega
    · have := d2_le_six_of_shapeS2 hL hG2 (fun hbot => xbar_not_mem_of_center_eq_bot hnd.lxy_inv hbot h2.2) h2
      omega
    · obtain ⟨⟨p', f', hp', hp2', hq', hmod⟩, hxL⟩ := h3
      have hlev := hnd.lxy_level hgen4 hxL hle hp' hp2' hmod
      have hf' : f' ≠ 0 := by
        rintro rfl
        simp at hq'
      have hpp : p' = p := by
        have h1 : p' ∣ p ^ f := hlev ▸ dvd_pow_self p' hf'
        exact (Nat.prime_dvd_prime_iff_eq hp' hnd.prime.1).1 (hp'.dvd_of_dvd_pow h1)
      subst hpp
      have hff : f' = f := Nat.pow_right_injective hp'.two_le hlev
      subst hff
      rcases hmod with hm | hm
      · exact ⟨.PSL, Or.inl rfl, hm⟩
      · exact ⟨.PSU, Or.inr rfl, hm⟩
    · have := d2_le_six_of_shapeS4 hL hG2 h4
      omega
    · exact (hnd.lxy_false_of_J1 hle h5.1).elim

end Main

end CFSG.GH74.Generic.S3
