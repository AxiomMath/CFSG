module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusRes
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusFix

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.BHS6

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commVW_wb {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n)
    {b : MulAut V} (hb : b ∈ B) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    commVW (fixV (Subgroup.zpowers b)) D = commV (Subgroup.zpowers b) := by
  obtain ⟨hfix, -, -⟩ := hP.fixb b hb hb2 hb1
  have hnat := hP.natE b hb hb2 hb1
  have hDE : GInv D (commV (Subgroup.zpowers b)) := hnat.1
  have hEW : commV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers b) := hfix ▸ le_sup_left
  refine le_antisymm (commVW_le fun d hd w hw => ?_) (commVW_eq_of_natSL hnat hEW)
  rw [hfix] at hw
  obtain ⟨e, he, f, hf, rfl⟩ := Subgroup.mem_sup.mp hw
  have hdf : d f = f := (mem_fixV.mp (hP.fD ▸ hf)) d hd
  have : d (e * f) * (e * f)⁻¹ = d e * e⁻¹ := by
    rw [map_mul, hdf]
    group
  rw [this]
  exact (commV (Subgroup.zpowers b)).mul_mem (hDE d hd e he)
    ((commV (Subgroup.zpowers b)).inv_mem he)

omit [Finite V] in
theorem dle_cent {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n)
    {b : MulAut V} (hb : b ∈ B) : D ≤ G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) :=
  le_inf (hP.dy.trans hP.yg) fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hP.comm d hd b hb)

omit [Finite V] in
theorem commV_bar {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n)
    {b : MulAut V} (hb : b ∈ B) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    commV (barW (ginv_cent G b) D) =
      (commV (Subgroup.zpowers b)).subgroupOf (fixV (Subgroup.zpowers b)) := by
  have h1 := commV_barW (ginv_cent G b) (dle_cent hP hb)
  rw [commVW_wb hP hb hb2 hb1] at h1
  have hEW : commV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers b) :=
    (hP.fixb b hb hb2 hb1).1 ▸ le_sup_left
  apply Subgroup.map_injective (fixV (Subgroup.zpowers b)).subtype_injective
  rw [h1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEW]

omit [Finite V] in
theorem dinj_cent {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n)
    {b : MulAut V} (hb : b ∈ B) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    D ⊓ fixW (fixV (Subgroup.zpowers b)) = ⊥ := by
  rw [eq_bot_iff]
  rintro d ⟨hd, hdf⟩
  have hEW : commV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers b) :=
    (hP.fixb b hb hb2 hb1).1 ▸ le_sup_left
  rw [Subgroup.mem_bot]
  exact natSL_faithful (hP.natE b hb hb2 hb1) hd fun p hp => mem_fixW.mp hdf p (hEW hp)

omit [Finite V] in
theorem natSL_bar {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n)
    {b : MulAut V} (hb : b ∈ B) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    IsNatSectionBy (slAct n) (barW (ginv_cent G b) D) (commV (barW (ginv_cent G b) D)) ⊥ := by
  have hEW : commV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers b) :=
    (hP.fixb b hb hb2 hb1).1 ▸ le_sup_left
  rw [commV_bar hP hb hb2 hb1]
  exact isNatSectionBy_barW (ginv_cent G b) (dle_cent hP hb) (dinj_cent hP hb hb2 hb1) hEW
    (hP.natE b hb hb2 hb1)

theorem adm4_bar (hV : ∀ v : V, v ^ 2 = 1) {G T Y D B : Subgroup (MulAut V)} {n : ℕ}
    (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n) {b t : MulAut V} (hb : b ∈ B)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (htT : t ∈ T) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Adm4 (resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V))) (fixV (Subgroup.zpowers b))
        (ginv_cent G b)).range
      (barW (ginv_cent G b) (Subgroup.zpowers t)) (barW (ginv_cent G b) D) := by
  set X := G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) with hX
  have h := ginv_cent G b
  have hbY : b ∈ Y := hP.by_ hb
  have htG : t ∈ G := cfg.adm.hTG htT
  have htC : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) := cfg.adm.le_centralizer htT
  have htY : ∀ y ∈ Y, y * t = t * y := fun y hy => Subgroup.mem_centralizer_iff.mp htC y hy
  have hDX : D ≤ X := dle_cent hP hb
  have htX : t ∈ X := ⟨htG, Subgroup.mem_centralizer_singleton_iff.mpr (htY b hbY).symm⟩
  have hDt : ∀ d ∈ D, d * t = t * d := fun d hd => htY d (hP.dy hd)
  have hzD : ∀ s ∈ Subgroup.zpowers t, ∀ d ∈ D, s * d = d * s := by
    intro s hs d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact ((Commute.zpow_left (show Commute t d from (hDt d hd).symm) k).eq)
  have hfix : fixV Y ≤ fixV (Subgroup.zpowers b) := fun v hv =>
    Quasithin.mem_fixV_zpowers_iff.mpr (hv b hbY)
  refine
    { hTG := (barW_mono h (Subgroup.zpowers_le.mpr htX)).trans (barW_self h).le
      hT1 := ?_
      hT2 := ?_
      hYC := ?_
      hsub := ?_
      hperf := barW_perfect h hDX (hP.dfacts.1)
      hcls := Or.inl (inClassX_yuHol_of_natSL (fun v => Subtype.ext (by simpa using hV v))
        hP.hn (natSL_bar hP hb hb2 hb1)) }
  · intro hbot
    have hmem : resG X (fixV (Subgroup.zpowers b)) h ⟨t, htX⟩ ∈
        barW h (Subgroup.zpowers t) := resG_mem_barW h (Subgroup.mem_zpowers t)
    rw [hbot, Subgroup.mem_bot] at hmem
    apply ht1
    ext v
    have hv : v ∈ fixV Y ⊔ commV Y := by rw [hP.vsup]; exact Subgroup.mem_top v
    obtain ⟨w, hw, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
    have htw : t w = w := by
      have := congrArg (fun φ : MulAut ↥(fixV (Subgroup.zpowers b)) =>
        ((φ ⟨w, hfix hw⟩ : ↥(fixV (Subgroup.zpowers b))) : V)) hmem
      simpa [resG_apply] using this
    have htu : t u = u := hP.ctriv t ⟨htG, htC⟩ ⟨1, by simpa using ht2⟩ u hu
    show t (w * u) = w * u
    rw [map_mul, htw, htu]
  · intro z
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := z
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hy
    have hg2 : g ^ 2 = 1 := by
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      show (g : MulAut V) ^ 2 = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
    apply Subtype.ext
    show (resG X (fixV (Subgroup.zpowers b)) h g) ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, hg2, map_one]
  · refine le_inf (barW_le_range h D) fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hy
    obtain ⟨s, hs, rfl⟩ := (mem_barW h).mp hz
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzD _ hs _ hg)
  · have hDY := hP.dy
    have hYK : Y ≤ G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := fun y hy =>
      ⟨hP.yg hy, Subgroup.mem_centralizer_singleton_iff.mpr (htY y hy)⟩
    have hDsub : (D.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_trans hDY hYK hP.dnormal.isSubnormal
        (cfg.cent t ⟨htG, htC⟩ ht1 ht2)
    set C₀ := X ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) with hC₀
    have hC₀le : C₀ ≤ G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hC₀X : C₀ ≤ X := inf_le_left
    have hDC₀ : D ≤ C₀ := le_inf hDX fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hDt d hd)
    have h1 : (D.subgroupOf C₀).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hC₀le hDsub
    have h2 : ((D.subgroupOf X).subgroupOf (C₀.subgroupOf X)).IsSubnormal :=
      (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff hC₀X).mpr h1
    have h3 := isSubnormal_subgroupOf_map (resG X (fixV (Subgroup.zpowers b)) h)
      (show D.subgroupOf X ≤ C₀.subgroupOf X from fun x hx => hDC₀ hx) h2
    rw [← barW_cent_eq htX fun x hx hk => commutator_kStab_eq_one hV cfg hP hb hb2 hb1 htT hx hk]
    exact h3

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
