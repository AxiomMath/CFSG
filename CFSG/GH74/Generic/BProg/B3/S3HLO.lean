module

public import CFSG.GH74.Generic.BProg.B3.S3PumpFinal
public import CFSG.GH74.Generic.BProg.B3.S3HLOMain

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop306a_bar'
    (hC2 : C2CoverInput) {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    barSub y (pumpUp 2 (Ly K y) y) = barSub y (Ly K y) := by
  obtain ⟨T, hT, -⟩ := Setup30.exists_T h
  obtain ⟨hH, hxH⟩ := thm9_l3_rank1 h
  exact S3HLOMain.barSub_pumpup_of_F' hC2 h hT (prop301T h hT) hH hxH (S3Pump305.le_pumpUp h)

theorem hLO_proved
    (hC2 : C2CoverInput) {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    pPrimeCoreOf 2 (Ly K y) ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy : orderOf y = 2 := h.y_ord
  obtain ⟨hH, -⟩ := thm9_l3_rank1 h
  have hHb : CFSG.IsComponent (barSub y (pumpUp 2 (Ly K y) y)) := FalseCtxS45Comp.isComponent_bar hH
  have hKP : GLS.IsKProperSimple G :=
    ⟨h.hyp.simple, h.hyp.nonab, CFSG.GH74.kProper_of_kgh h.hyp.kgh⟩
  have hCal : InCalK2 ↥(barSub y (pumpUp 2 (Ly K y) y)) := GLS.inCalK2_of_isComponent hKP hy hHb
  have hZ2 : IsPGroup 2 ↥(center ↥(barSub y (pumpUp 2 (Ly K y) y))) := by
    have := pCore_isPGroup (p := 2) (G := ↥(barSub y (pumpUp 2 (Ly K y) y)))
    rw [← hCal.2.1] at this
    exact this
  rw [prop306a_bar' hC2 h] at hHb hZ2
  obtain ⟨q, hqodd, -, -, hqdvd⟩ := S3HLOCard.sl2Quot_card_data (S3HLOMain.hasSL2Quot_bar h)
  have heven : 2 ∣ Nat.card ↥(barSub y (Ly K y)) :=
    (Dvd.dvd.mul_left (even_iff_two_dvd.1 (Nat.Odd.sub_odd hqodd.pow odd_one)) q).trans hqdvd
  have hOb : pPrimeCore 2 ↥(barSub y (Ly K y)) = ⊥ := S3SL2AltTr.pPrimeCore_eq_bot hHb.1 hZ2 heven
  have hL : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) := (Setup30.layer h).1
  have hLC : Ly K y ≤ centralizer ({y} : Set G) := hL.1.trans inf_le_right
  let φ : ↥(Ly K y) →* CentralizerBar y := (proj y).comp (Subgroup.inclusion hLC)
  have hφr : φ.range = barSub y (Ly K y) := by
    ext b
    constructor
    · rintro ⟨l, rfl⟩
      exact proj_mem_barSub (hLC l.2) l.2
    · intro hb
      obtain ⟨g, hg, hgL, rfl⟩ := mem_barSub.1 hb
      exact ⟨⟨g, hgL⟩, rfl⟩
  let f : ↥(Ly K y) →* ↥(barSub y (Ly K y)) :=
    (MulEquiv.subgroupCongr hφr).toMonoidHom.comp φ.rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hφr).surjective.comp φ.rangeRestrict_surjective
  rintro _ ⟨o, ho, rfl⟩
  have hfo : f o ∈ pPrimeCore 2 ↥(barSub y (Ly K y)) := CFSG.map_pPrimeCore_le f hf ⟨o, ho, rfl⟩
  rw [hOb, Subgroup.mem_bot] at hfo
  have h0 : φ o = 1 := congrArg Subtype.val hfo
  exact ⟨Subgroup.inclusion hLC o, (QuotientGroup.eq_one_iff _).1 h0, rfl⟩

end CFSG.GH74.Generic.BProg.B3
