module

public import CFSG.CGT.PushingUpLit.CGT6.EmbConjMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbEightFive

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUp
open scoped commutatorElement

section Trans

variable {V : Type} [CommGroup V]

structure Trans (G Y : Subgroup (MulAut V)) (W : Subgroup V) : Prop where
  inv : GInv G W
  yg : Y ≤ G
  yw : commV Y ≤ W
  cy : G ⊓ fixW W ≤ Subgroup.centralizer (Y : Set (MulAut V))
  qy : ⁅oTwoIn G, Y⁆ = ⊥
  oy : ⁅oTwoIn Y, Y⁆ = ⊥
  no : SubTwo.NoTwoQuotient Y
  uy : USelf Y

variable {G Y : Subgroup (MulAut V)} {W : Subgroup V}

section Conj

variable (T : Trans G Y W) {Xt : Subgroup (MulAut V)} (hXt : Xt ≤ G)

include T hXt in
theorem Trans.conj_le_trivQ : conjClosure Y Xt ≤ trivQ W := by
  apply conjClosure_le_trivQ
  intro g hg y hy v
  rw [conj_mul_apply]
  exact T.inv g (hXt hg) _ (T.yw (Subgroup.subset_closure ⟨y, hy, _, rfl⟩))

include T hXt in
theorem Trans.commV_conj_le : commV (conjClosure Y Xt) ≤ W :=
  commV_le_iff_le_trivQ.mpr (T.conj_le_trivQ hXt)

include T in
theorem Trans.uself_conj : USelf (conjClosure Y Xt) := USelf_conjClosure Xt T.uy

include T hXt in
theorem Trans.hU_conj : commV (conjClosure Y Xt) ≤ commVW W (conjClosure Y Xt) :=
  (T.uself_conj (Xt := Xt)).le_commVW.trans (commVW_mono_W (T.commV_conj_le hXt))

theorem conj_le_G_of_le {Y Xt G : Subgroup (MulAut V)} (hXt : Xt ≤ G) (hYXt : Y ≤ Xt) :
    conjClosure Y Xt ≤ G :=
  (conjClosure_le hYXt).trans hXt

include T hXt in
theorem Trans.ker_central (hYXt : Y ≤ Xt) :
    ∀ k ∈ conjClosure Y Xt ⊓ fixW W, ∀ k' ∈ conjClosure Y Xt, k * k' = k' * k := by
  intro k hk k' hk'
  have hKG := conj_le_G_of_le hXt hYXt
  have hcent : conjClosure Y Xt ≤ Subgroup.centralizer ({k} : Set (MulAut V)) := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hgG : g ∈ G := hXt hg
    have hc : g⁻¹ * z * g ∈ G ⊓ fixW W := by
      refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hgG) (hKG hk.1)) hgG, fun w hw => ?_⟩
      have h1 : g w ∈ W := T.inv g hgG w hw
      have h2 : z (g w) = g w := hk.2 _ h1
      show (g⁻¹ * z * g) w = w
      simp only [MulAut.mul_apply]
      rw [h2]
      simp
    have hcy := Subgroup.mem_centralizer_iff.mp (T.cy hc) y hy
    calc z * (g * y * g⁻¹) = g * (g⁻¹ * z * g) * y * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [mul_assoc g, ← hcy, mul_assoc g, mul_assoc]
      _ = (g * y * g⁻¹) * z := by group
  exact (Subgroup.mem_centralizer_iff.mp (hcent hk') k (Set.mem_singleton k))

include T hXt in
theorem Trans.ker_two (hV : ∀ v : V, v ^ 2 = 1) :
    ∀ k ∈ conjClosure Y Xt ⊓ fixW W, ∃ m : ℕ, k ^ 2 ^ m = 1 := by
  intro k hk
  exact ⟨1, by
    rw [pow_one]
    exact sq_eq_one_of_mem_trivQ_fixW hV (T.conj_le_trivQ hXt hk.1) hk.2⟩

include T hXt in
theorem Trans.oTwo_conj (hYXt : Y ≤ Xt)
    (hsub : ((conjClosure Y Xt).subgroupOf G).IsSubnormal) :
    ⁅oTwoIn (conjClosure Y Xt), conjClosure Y Xt⁆ = ⊥ := by
  have hKG := conj_le_G_of_le hXt hYXt
  have hQK : ⁅oTwoIn G, conjClosure Y Xt⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (commutator_conjClosure_le (W := ⊥) ?_ ?_)
    · rw [Subgroup.normalizer_eq_top]
      exact le_top
    · intro g hg y hy m hm
      have hgG : g ∈ G := hXt hg
      have hQn : G ≤ Subgroup.normalizer (oTwoIn G : Set (MulAut V)) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn G)
      have hm' : g⁻¹ * m * g ∈ oTwoIn G := by
        have := (Subgroup.mem_normalizer_iff.mp (hQn (G.inv_mem hgG)) m).mp hm
        simpa using this
      have h1 : ⁅g⁻¹ * m * g, y⁆ = 1 := by
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp T.qy hm'
        have h2 := Subgroup.mem_centralizer_iff.mp this y hy
        rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact h2.symm
      rw [Subgroup.mem_bot]
      calc ⁅m, g * y * g⁻¹⁆ = g * ⁅g⁻¹ * m * g, y⁆ * g⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = 1 := by rw [h1]; group
  exact le_bot_iff.mp ((Subgroup.commutator_mono (oTwoIn_le_of_isSubnormal hKG hsub) le_rfl).trans
    hQK.le)

end Conj

section Main

theorem Trans.centralShort_conj (hV : ∀ v : V, v ^ 2 = 1) (T : Trans G Y W)
    {Xt : Subgroup (MulAut V)} (hXt : Xt ≤ G) (hYXt : Y ≤ Xt)
    (hsub : ((conjClosure Y Xt).subgroupOf G).IsSubnormal) :
    CentralShort (thetaK T.inv (conj_le_G_of_le hXt hYXt) (T.commV_conj_le hXt)
      (T.hU_conj hXt)) :=
  thetaK_centralShort T.inv hV _ _ _ (T.ker_central hXt hYXt) (T.ker_two hXt hV)
    (T.oTwo_conj hXt hYXt hsub)

theorem Trans.hU_self (T : Trans G Y W) : commV Y ≤ commVW W Y :=
  T.uy.le_commVW.trans (commVW_mono_W T.yw)

theorem Trans.centralShort_self (hV : ∀ v : V, v ^ 2 = 1) (T : Trans G Y W) :
    CentralShort (thetaK T.inv T.yg T.yw T.hU_self) :=
  thetaK_centralShort T.inv hV _ _ _
    (fun k hk k' hk' => (Subgroup.mem_centralizer_iff.mp (T.cy ⟨T.yg hk.1, hk.2⟩) k' hk').symm)
    (fun k hk => ⟨1, by
      rw [pow_one]
      exact sq_eq_one_of_mem_trivQ_fixW hV (commV_le_iff_le_trivQ.mp T.yw hk.1) hk.2⟩) T.oy

theorem Trans.descent [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (T : Trans G Y W)
    (hY : InClassX ↥(yuHol Y)) : InClassX ↥(yuHol (barW T.inv Y)) :=
  ((T.centralShort_self hV).inClassX_iff hY.1.residual_eq).mp hY

structure BlockHyp (T : Trans G Y W) (X : Subgroup (MulAut ↥W)) : Prop where
  xg : X ≤ barW T.inv G
  yx : barW T.inv Y ≤ X
  sub : (X.subgroupOf (barW T.inv G)).IsSubnormal
  gen : conjClosure (barW T.inv Y) X = X

section Block

variable {T : Trans G Y W} {X : Subgroup (MulAut ↥W)} (B : BlockHyp T X)

include B

theorem BlockHyp.xr : X ≤ (resG G W T.inv).range := barW_self T.inv ▸ B.xg

theorem BlockHyp.yxt : Y ≤ preW T.inv X :=
  (le_preW_barW T.inv T.yg).trans (preW_mono T.inv B.yx)

theorem BlockHyp.xt_sub : ((preW T.inv X).subgroupOf G).IsSubnormal := by
  let ρ' : ↥G →* ↥(barW T.inv G) :=
    (resG G W T.inv).codRestrict (barW T.inv G) (fun g => resG_mem_barW T.inv g.2)
  have h1 := B.sub.comap ρ'
  convert h1 using 1
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · intro hg
    obtain ⟨g', hg', hg''⟩ := (mem_preW T.inv).mp hg
    have : g' = g := Subtype.ext hg'
    subst this
    exact hg''
  · intro hg
    exact (mem_preW T.inv).mpr ⟨g, rfl, hg⟩

theorem BlockHyp.kG : conjClosure Y (preW T.inv X) ≤ G :=
  conj_le_G_of_le (preW_le T.inv X) B.yxt

theorem BlockHyp.k_sub : ((conjClosure Y (preW T.inv X)).subgroupOf G).IsSubnormal := by
  have hKXt : conjClosure Y (preW T.inv X) ≤ preW T.inv X := conjClosure_le B.yxt
  have hn : ((conjClosure Y (preW T.inv X)).subgroupOf (preW T.inv X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKXt).2 le_normalizer_conjClosure
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hKXt (preW_le T.inv X) hn.isSubnormal B.xt_sub

theorem BlockHyp.barK : barW T.inv (conjClosure Y (preW T.inv X)) = X := by
  apply le_antisymm
  · calc barW T.inv (conjClosure Y (preW T.inv X)) ≤ barW T.inv (preW T.inv X) :=
          barW_mono T.inv (conjClosure_le B.yxt)
      _ = X := barW_preW T.inv B.xr
  · calc X = conjClosure (barW T.inv Y) X := B.gen.symm
      _ ≤ barW T.inv (conjClosure Y (preW T.inv X)) := by
        rw [conjClosure, Subgroup.closure_le]
        rintro _ ⟨x, hx, yb, hyb, rfl⟩
        obtain ⟨g, rfl⟩ := B.xr hx
        obtain ⟨g', hg', rfl⟩ := (mem_barW T.inv).mp hyb
        have hgXt : (g : MulAut V) ∈ preW T.inv X := (mem_preW T.inv).mpr ⟨g, rfl, hx⟩
        refine (mem_barW T.inv).mpr ⟨g * g' * g⁻¹, ?_, by simp⟩
        exact mem_conjClosure_of_mem hgXt hg'

end Block

theorem Trans.conj_le_of_eq (T : Trans G Y W) {X : Subgroup (MulAut ↥W)} (hb : barW T.inv Y = X) :
    conjClosure Y (preW T.inv X) ≤ Y := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  have hgG : g ∈ G := preW_le T.inv X hg
  have hρ : resG G W T.inv ⟨g, hgG⟩ ∈ barW T.inv Y := by
    rw [hb]
    exact resG_mem_of_mem_preW T.inv hg hgG
  obtain ⟨g₀, hg₀, hρ₀⟩ := (mem_barW T.inv).mp hρ
  have hker : g₀⁻¹ * ⟨g, hgG⟩ ∈ (resG G W T.inv).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρ₀, inv_mul_cancel]
  have hfix := (mem_ker_resG T.inv).mp hker
  have hcy := Subgroup.mem_centralizer_iff.mp (T.cy ⟨(g₀⁻¹ * ⟨g, hgG⟩ : ↥G).2, hfix⟩) y hy
  have hg0 : (g₀ : MulAut V) ∈ Y := hg₀
  have h1 : ((g₀⁻¹ * ⟨g, hgG⟩ : ↥G) : MulAut V) = (g₀ : MulAut V)⁻¹ * g := rfl
  rw [h1] at hcy
  obtain ⟨a, ha⟩ : ∃ a : MulAut V, a = (g₀ : MulAut V) := ⟨_, rfl⟩
  rw [← ha] at hcy hg0
  have h2 : g * y * g⁻¹ = a * y * a⁻¹ := by
    calc g * y * g⁻¹ = a * ((a⁻¹ * g) * y * (a⁻¹ * g)⁻¹) * a⁻¹ := by group
      _ = a * y * a⁻¹ := by
        rw [← hcy]
        group
  show g * y * g⁻¹ ∈ Y
  rw [h2]
  exact Y.mul_mem (Y.mul_mem hg0 hy) (Y.inv_mem hg0)

theorem Trans.ascent [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (T : Trans G Y W)
    {X : Subgroup (MulAut ↥W)} (B : BlockHyp T X) (hX : InClassX ↥(yuHol X))
    (harr : ArrowNat (yuHol (barW T.inv Y)) (yuHol X)) :
    ∃ K : Subgroup (MulAut V), Y ≤ K ∧ K ≤ G ∧ (K.subgroupOf G).IsSubnormal ∧
      barW T.inv K = X ∧ InClassX ↥(yuHol K) ∧ ArrowNat (yuHol Y) (yuHol K) := by
  have hXtG := preW_le T.inv X
  have hYXt := B.yxt
  set K := conjClosure Y (preW T.inv X) with hK
  have hKG : K ≤ G := B.kG
  have hKsub : (K.subgroupOf G).IsSubnormal := B.k_sub
  have hbarK : barW T.inv K = X := B.barK
  have hKW := T.commV_conj_le hXtG
  have hUK := T.hU_conj hXtG
  have hCS := T.centralShort_conj hV hXtG hYXt hKsub
  have hres : oResidualTwo ↥(yuHol K) = ⊤ := oResidualTwo_yuHol_conjClosure T.no T.uy
  have hX' : InClassX ↥(yuHol (barW T.inv K)) := by rw [hbarK]; exact hX
  have hclass : InClassX ↥(yuHol K) := (hCS.inClassX_iff hres).mpr hX'
  refine ⟨K, le_conjClosure, hKG, hKsub, hbarK, hclass, ?_⟩
  have hharr : ArrowNat (yuHol (barW T.inv Y)) (yuHol (barW T.inv K)) := by
    rw [hbarK]; exact harr
  have hU' : ∀ u ∈ shortU ↥(yuHol (barW T.inv K)), ∀ o ∈ pCore 2 ↥(yuHol (barW T.inv K)),
      u * o = o * u := fun u hu o ho =>
    ((shortU_le_center_iff.mp hX'.1.U_le_center) u hu).2 o ho
  have hYX' : yuHol Y ≤ yuHol K := yuHol_mono le_conjClosure
  have hUKself : USelf K := T.uself_conj
  have hOK := T.oTwo_conj hXtG hYXt hKsub
  have hsU : (shortU ↥(yuHol Y)).map (yuHol Y).subtype ≤
      (shortU ↥(yuHol K)).map (yuHol K).subtype := by
    rw [shortU_yuHol_eq_range hV T.uy T.oy, shortU_yuHol_eq_range hV hUKself hOK]
    rintro _ ⟨s, ⟨u, rfl⟩, rfl⟩
    exact ⟨yuInc K ⟨(u : V), commV_mono le_conjClosure u.2⟩, ⟨_, rfl⟩, rfl⟩
  have heq : yuHol (barW T.inv Y) = yuHol (barW T.inv K) → yuHol Y = yuHol K := by
    intro heq
    have hb : barW T.inv Y = X := by rw [yuHol_inj heq, hbarK]
    rw [le_antisymm le_conjClosure (T.conj_le_of_eq hb)]
  exact arrowNat_of_central hCS (ΘY := thetaK T.inv T.yg T.yw T.hU_self) hU'
    (T.centralShort_self hV).toCentralTwoQuot hYX' (fun y => rfl) hsU heq hharr

end Main

end Trans

end CFSG.CGT.PushingUpLit.CGT6
