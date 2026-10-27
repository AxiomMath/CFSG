module

public import CFSG.CGT.PushingUpLit.CGT6.EmbQuotIso
public import CFSG.CGT.PushingUpLit.CGT6.EmbQuotShort
public import CFSG.CGT.PushingUpLit.CGT6.EmbQuotNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Basic

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {A : Subgroup V}

theorem QData.smaller (D : QData G A) (hA : A ≠ ⊥) : Smaller (barQ D.inv G) G := by
  refine Or.inr ⟨card_homImg_self D.resQ_injective, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
  have h2 : 1 < Nat.card ↥A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hA
  have h3 : 0 < Nat.card (V ⧸ A) := Nat.card_pos
  nlinarith

omit [Finite V] in
theorem isKGroup_barQ (D : QData G A) (hK : CFSG.IsKGroup ↥G) :
    CFSG.IsKGroup ↥(barQ D.inv G) := by
  show CFSG.IsKGroup ↥(homImg (resQ G A D.inv) G)
  rw [homImg_self]
  exact isKGroup_of_surjective hK (resQ G A D.inv).rangeRestrict
    (resQ G A D.inv).rangeRestrict_surjective

omit [Finite V] in
theorem QData.inf_commV_eq_bot_of_nat (D : QData G A) {n : ℕ} (hn : 2 ≤ n)
    {Y : Subgroup (MulAut V)} (hYG : Y ≤ G) (hY : NatOmegaN n Y) : A ⊓ commV Y = ⊥ := by
  have hUS : USelf Y := USelf_of_perfect (hY.commutator_eq_self hn)
  have hinv : ∀ x ∈ Y, ∀ a ∈ A ⊓ commV Y, x a ∈ A ⊓ commV Y := fun x hx a ha =>
    ⟨D.inv x (hYG hx) a ha.1, commV_invariant hx ha.2⟩
  rcases NatOmegaN.irreducible hn hY (A ⊓ commV Y) hinv inf_le_right with h | h
  · exact h
  · exfalso
    have hle : commV Y ≤ A := fun u hu => by
      have : u ∈ A ⊓ commV Y := by
        rw [h]
        exact hu
      exact this.1
    have hbot : commV Y ≤ ⊥ := hUS ⊥ (fun g hg u hu => by
      rw [D.fix g (hYG hg) u (hle hu), mul_inv_cancel]
      exact Subgroup.one_mem _)
    exact commV_ne_bot_of_not_isPGroup (hY.not_isPGroup hn) (le_bot_iff.mp hbot)

theorem QData.classX4_barQ (hV : ∀ v : V, v ^ 2 = 1) (D : QData G A)
    {Y : Subgroup (MulAut V)} (hYG : Y ≤ G) (hY : ClassX4 Y) : ClassX4 (barQ D.inv Y) := by
  rcases classX4_iff.mp hY with hc | ⟨n, hn, hΩ⟩
  · exact classX4_iff.mpr (Or.inl
      ((thetaQ_centralTwoQuot hV D hYG).inClassX_quot hc.1.residual_eq hc))
  · have hbot := D.inf_commV_eq_bot_of_nat hn hYG hΩ
    refine classX4_iff.mpr (Or.inr ⟨n, hn, ?_⟩)
    rcases hΩ with h1 | h1
    · exact Or.inl ((isNatSectionBy_barQ_iff D.inv _ hYG hbot D.resQ_injective).mp h1)
    · exact Or.inr ((isNatSectionBy_barQ_iff D.inv _ hYG hbot D.resQ_injective).mp h1)

theorem QData.adm4_barQ (hV : ∀ v : V, v ^ 2 = 1) (D : QData G A)
    {T Y : Subgroup (MulAut V)} (h : Adm4 G T Y) :
    Adm4 (barQ D.inv G) (barQ D.inv T) (barQ D.inv Y) where
  hTG := homImg_mono h.hTG
  hT1 := by
    intro h0
    apply h.hT1
    rw [eq_bot_iff]
    intro t ht
    have h1 : resQ G A D.inv ⟨t, h.hTG ht⟩ ∈ barQ D.inv T := hom_mem_homImg ht
    rw [h0, Subgroup.mem_bot] at h1
    have h2 : (⟨t, h.hTG ht⟩ : ↥G) = 1 := D.resQ_injective (h1.trans (map_one _).symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  hT2 := isPGroup_homImg h.hTG h.hT2
  hYC := homImg_le_centralizer (fun y hy => (h.hYC hy).1) fun y hy => (h.hYC hy).2
  hsub := by
    have hYG : Y ≤ G := fun y hy => (h.hYC hy).1
    rw [← homImg_inf_centralizer D.resQ_injective h.hTG]
    exact isSubnormal_homImg (fun y hy => h.hYC hy) inf_le_left h.hsub
  hperf := by
    have hYG : Y ≤ G := fun y hy => (h.hYC hy).1
    rw [homImg_commutator hYG hYG, h.hperf]
  hcls := D.classX4_barQ hV (fun y hy => (h.hYC hy).1) h.hcls

end Basic

section Pull

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {A : Subgroup V}

omit [Finite V] in
theorem thetaQ_compat {G X Y : Subgroup (MulAut V)} (h : GInv G A)
    (hYG : Y ≤ G) (hXG : X ≤ G) (hYX : Y ≤ X) (y : ↥(yuHol Y)) :
    ((thetaQ h hYG y : ↥(yuHol (barQ h Y))) : Hol (V ⧸ A)) =
      ((thetaQ h hXG ⟨y, yuHol_mono hYX y.2⟩ : ↥(yuHol (barQ h X))) : Hol (V ⧸ A)) := by
  rw [coe_thetaQ, coe_thetaQ]
  apply SemidirectProduct.ext
  · rw [thetaQHol_left, thetaQHol_left]
  · rw [thetaQHol_right, thetaQHol_right]

theorem isSubnormal_homPre {M Γ : Type*} [Group M] [Group Γ] {H : Subgroup M} {ρ : ↥H →* Γ}
    {X : Subgroup Γ} (hX : (X.subgroupOf (homImg ρ H)).IsSubnormal) :
    ((homPre ρ X).subgroupOf H).IsSubnormal := by
  let ρ' : ↥H →* ↥(homImg ρ H) :=
    ρ.codRestrict (homImg ρ H) (fun g => hom_mem_homImg (ρ := ρ) (g := g) g.2)
  have h1 := hX.comap ρ'
  convert h1 using 1
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · intro hg
    obtain ⟨g', hg', hg''⟩ := mem_homPre.mp hg
    have : g' = g := Subtype.ext hg'
    subst this
    exact hg''
  · intro hg
    exact mem_homPre.mpr ⟨g, rfl, hg⟩

theorem QData.lift_of_bar (hV : ∀ v : V, v ^ 2 = 1) {T Y : Subgroup (MulAut V)}
    (cfg : Emb4Cfg G T Y) (D : QData G A) {Xb : Subgroup (MulAut (V ⧸ A))}
    (h : Lift4 (barQ D.inv G) (barQ D.inv Y) Xb) : ∃ X, Lift4 G Y X := by
  obtain ⟨hYX, hXG, hXsub, h4⟩ := h
  have hρ := D.resQ_injective
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  obtain ⟨X, hXdef⟩ : ∃ X, X = preQ D.inv Xb := ⟨_, rfl⟩
  have hXG' : X ≤ G := hXdef ▸ homPre_le Xb
  have hXr : Xb ≤ (resQ G A D.inv).range := by
    rw [← homImg_self]
    exact hXG
  have hbarX : barQ D.inv X = Xb := hXdef ▸ homImg_homPre hXr
  have hYX' : Y ≤ X := hXdef ▸ (le_homPre_homImg hYG).trans (homPre_mono hYX)
  have hsub : (X.subgroupOf G).IsSubnormal := hXdef ▸ isSubnormal_homPre hXsub
  have hXX : homPre (resQ G A D.inv) (barQ D.inv X) = X := homPre_homImg hρ hXG'
  have hYY : homPre (resQ G A D.inv) (barQ D.inv Y) = Y := homPre_homImg hρ hYG
  refine ⟨X, hYX', hXG', hsub, ?_⟩
  rcases h4 with ⟨hXcl, harr⟩ | ⟨n, hn, hnat, hcase⟩
  ·
    left
    have hXcl' : InClassX ↥(yuHol (barQ D.inv X)) := by
      rw [hbarX]
      exact hXcl
    have hOb : oResidualTwo ↥(barQ D.inv X) = ⊤ := by
      rw [hbarX]
      exact oResidualTwo_eq_top_of_surjective (yuProj Xb) (yuProj_surjective Xb)
        hXcl.1.residual_eq
    have hOX : oResidualTwo ↥X = ⊤ :=
      oResidualTwo_eq_top_of_mulEquiv (homImgEquiv hρ hXG').symm hOb
    have hO2G : oTwoIn G = ⊥ := by
      show (pCore 2 ↥G).map G.subtype = ⊥
      rw [cfg.o2, Subgroup.map_bot]
    have hO2X : oTwoIn X = ⊥ :=
      le_bot_iff.mp (hO2G ▸ oTwoIn_le_of_isSubnormal hXG' hsub)
    have hres : oResidualTwo ↥(yuHol X) = ⊤ := oResidualTwo_yuHol_of_oResidualTwo hV hOX
    have hUc := shortU_comm_pCore_yuHol_of_oTwoIn_eq_bot hV hO2X
    have hΘX := thetaQ_centralTwoQuot hV D hXG'
    have hΘY := thetaQ_centralTwoQuot hV D hYG
    refine ⟨hΘX.inClassX_of_quot hres hUc hXcl', ?_⟩
    have harr' : ArrowNat (yuHol (barQ D.inv Y)) (yuHol (barQ D.inv X)) := by
      rw [hbarX]
      exact harr
    have hUY : USelf Y := USelf_of_perfect cfg.adm.hperf
    have hOY : ⁅oTwoIn Y, Y⁆ = ⊥ := commutator_oTwoIn_eq_bot hV cfg.adm.hperf cfg.adm.hcls
    have hUX : USelf X := USelf_of_oResidualTwo hV hOX
    have hOXc : ⁅oTwoIn X, X⁆ = ⊥ := by
      rw [hO2X]
      exact Subgroup.commutator_bot_left _
    have hsU : (shortU ↥(yuHol Y)).map (yuHol Y).subtype ≤
        (shortU ↥(yuHol X)).map (yuHol X).subtype := by
      rw [shortU_yuHol_eq_range hV hUY hOY, shortU_yuHol_eq_range hV hUX hOXc]
      rintro _ ⟨s, ⟨u, rfl⟩, rfl⟩
      exact ⟨yuInc X ⟨(u : V), commV_mono hYX' u.2⟩, ⟨_, rfl⟩, rfl⟩
    have heq : yuHol (barQ D.inv Y) = yuHol (barQ D.inv X) → yuHol Y = yuHol X := by
      intro he
      have h1 : barQ D.inv Y = barQ D.inv X := yuHol_inj he
      have h2 : Y = X := by
        rw [← hYY, ← hXX]
        exact congrArg (homPre (resQ G A D.inv)) h1
      rw [h2]
    exact arrowNat_of_central' hΘX hres hΘY (yuHol_mono hYX')
      (thetaQ_compat D.inv hYG hXG' hYX') hsU heq harr'
  ·
    right
    obtain ⟨hbotX0, hnatX0⟩ := D.natOmegaN_pre hV hn hXG hnat
    have hbotX : A ⊓ commV X = ⊥ := by
      rw [hXdef]
      exact hbotX0
    have hnatX : NatOmegaN n X := by
      rw [hXdef]
      exact hnatX0
    refine ⟨n, hn, hnatX, ?_⟩
    rcases hcase with hb | ⟨hY1, ⟨e⟩, hcard⟩
    · left
      calc Y = homPre (resQ G A D.inv) (barQ D.inv Y) := hYY.symm
        _ = homPre (resQ G A D.inv) Xb := by rw [hb]
        _ = X := by rw [hXdef]
    · right
      have hbotY : A ⊓ commV Y = ⊥ := by
        rw [eq_bot_iff, ← hbotX]
        exact inf_le_inf_left _ (commV_mono hYX')
      have eY : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n) := (homImgEquiv hρ hYG).trans e
      have hO2Y : oTwoIn Y = ⊥ := by
        have : pCore 2 ↥Y = ⊥ := pCore_eq_bot_of_equiv eY (pCore_sl2_eq_bot hn)
        show (pCore 2 ↥Y).map Y.subtype = ⊥
        rw [this, Subgroup.map_bot]
      have hOb : oResidualTwo ↥(barQ D.inv Y) = ⊤ :=
        oResidualTwo_eq_top_of_surjective (yuProj (barQ D.inv Y)) (yuProj_surjective _)
          hY1.1.residual_eq
      have hOY : oResidualTwo ↥Y = ⊤ :=
        oResidualTwo_eq_top_of_mulEquiv (homImgEquiv hρ hYG).symm hOb
      have hres : oResidualTwo ↥(yuHol Y) = ⊤ := oResidualTwo_yuHol_of_oResidualTwo hV hOY
      have hUc := shortU_comm_pCore_yuHol_of_oTwoIn_eq_bot hV hO2Y
      refine ⟨(thetaQ_centralTwoQuot hV D hYG).inClassX_of_quot hres hUc hY1, ⟨eY⟩, ?_⟩
      rw [Nat.card_congr (commBarQEquiv D.inv hYG hbotY).toEquiv]
      exact hcard

end Pull

end CFSG.CGT.PushingUpLit.CGT6
