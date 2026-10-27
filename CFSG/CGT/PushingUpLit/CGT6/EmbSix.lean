module

public import CFSG.CGT.PushingUpLit.CGT6.EmbSpine
public import CFSG.CGT.PushingUpLit.CGT6.EmbTransNat
public import CFSG.CGT.PushingUpLit.CGT6.EmbFrattini
public import CFSG.CGT.PushingUpLit.CGT6.EmbThree

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUp
open scoped commutatorElement

section Basic

variable {V : Type} [CommGroup V]

theorem normalizer_trivQ {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) :
    G ≤ Subgroup.normalizer (trivQ W : Set (MulAut V)) := by
  have key : ∀ g ∈ G, ∀ x ∈ trivQ W, g * x * g⁻¹ ∈ trivQ W := by
    intro g hg x hx v
    rw [conj_mul_apply]
    exact h g hg _ (hx _)
  intro g hg
  exact mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
    simpa using key g⁻¹ (G.inv_mem hg) x hx)

theorem normalizer_fixW {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) :
    G ≤ Subgroup.normalizer (fixW W : Set (MulAut V)) := by
  have key : ∀ g ∈ G, ∀ x ∈ fixW W, g * x * g⁻¹ ∈ fixW W := by
    intro g hg x hx w hw
    have h1 : g⁻¹ w ∈ W := h g⁻¹ (G.inv_mem hg) w hw
    show g (x (g⁻¹ w)) = w
    rw [hx _ h1]
    simp
  intro g hg
  exact mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
    simpa using key g⁻¹ (G.inv_mem hg) x hx)

theorem inf_fixW_trivQ_le_oTwoIn (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    {W : Subgroup V} (h : GInv G W) [Finite V] : G ⊓ fixW W ⊓ trivQ W ≤ oTwoIn G := by
  have hnorm : G ≤ Subgroup.normalizer
      ((G ⊓ fixW W ⊓ trivQ W : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have h1 : G ≤ Subgroup.normalizer ((G ⊓ fixW W : Subgroup (MulAut V)) : Set (MulAut V)) :=
      le_trans (le_inf Subgroup.le_normalizer (normalizer_fixW h))
        Subgroup.inf_normalizer_le_normalizer_inf
    exact le_trans (le_inf h1 (normalizer_trivQ h)) Subgroup.inf_normalizer_le_normalizer_inf
  exact le_oTwoIn_of_normal (inf_le_left.trans inf_le_left) hnorm
    (fun x => ⟨1, Subtype.ext (by
      simpa using sq_eq_one_of_mem_trivQ_fixW hV x.2.2 x.2.1.2)⟩)

theorem commutator_mem_inf {G Y : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W)
    (hYG : Y ≤ G) (hYW : commV Y ≤ W) {y c : MulAut V} (hy : y ∈ Y) (hc : c ∈ G ⊓ fixW W) :
    ⁅y, c⁆ ∈ G ⊓ fixW W ⊓ trivQ W := by
  have hyG : y ∈ G := hYG hy
  have hy' : y ∈ trivQ W := commV_le_iff_le_trivQ.mp hYW hy
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact G.mul_mem (G.mul_mem (G.mul_mem hyG hc.1) (G.inv_mem hyG)) (G.inv_mem hc.1)
  · intro w hw
    have hw1 : c⁻¹ w = w := (fixW W).inv_mem hc.2 w hw
    have hw2 : y⁻¹ w ∈ W := h y⁻¹ (G.inv_mem hyG) w hw
    have hw3 : c (y⁻¹ w) = y⁻¹ w := hc.2 _ hw2
    show (y * c * y⁻¹ * c⁻¹ : MulAut V) w = w
    simp only [MulAut.mul_apply]
    rw [hw1, hw3]
    simp
  · have h1 : c * y⁻¹ * c⁻¹ ∈ trivQ W :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_trivQ h hc.1) y⁻¹).mp ((trivQ W).inv_mem hy')
    have h2 : ⁅y, c⁆ = y * (c * y⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact (trivQ W).mul_mem hy' h1

theorem fixW_le_centralizer_perfect [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G Y : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) (hYG : Y ≤ G)
    (hYW : commV Y ≤ W) (hperf : ⁅Y, Y⁆ = Y) (hQY : ⁅oTwoIn G, Y⁆ = ⊥) :
    G ⊓ fixW W ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  have hS := inf_fixW_trivQ_le_oTwoIn hV h
  have hYC : ⁅Y, G ⊓ fixW W⁆ ≤ oTwoIn G := by
    rw [Subgroup.commutator_le]
    intro y hy c hc
    exact hS (commutator_mem_inf h hYG hYW hy hc)
  have hZ1 : ⁅⁅Y, G ⊓ fixW W⁆, Y⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hYC le_rfl).trans hQY.le)
  have hZ2 : ⁅⁅G ⊓ fixW W, Y⁆, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (G ⊓ fixW W) Y]
    exact hZ1
  have hZ3 : ⁅⁅Y, Y⁆, G ⊓ fixW W⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hZ1 hZ2
  rw [hperf] at hZ3
  have hZ4 : ⁅G ⊓ fixW W, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hZ3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZ4

theorem fixW_le_centralizer_three [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G Y : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) (hYG : Y ≤ G)
    (hYW : commV Y ≤ W) (h3 : Nat.card ↥Y = 3) (hQY : ⁅oTwoIn G, Y⁆ = ⊥) :
    G ⊓ fixW W ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hzS : ⁅c, y⁆ ∈ G ⊓ fixW W ⊓ trivQ W := by
    have := (G ⊓ fixW W ⊓ trivQ W).inv_mem (commutator_mem_inf h hYG hYW hy hc)
    rwa [commutatorElement_inv] at this
  have hzQ : ⁅c, y⁆ ∈ oTwoIn G := inf_fixW_trivQ_le_oTwoIn hV h hzS
  have hzy : y * ⁅c, y⁆ = ⁅c, y⁆ * y :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQY hzQ) y hy
  have hz2 : ⁅c, y⁆ ^ 2 = 1 := sq_eq_one_of_mem_trivQ_fixW hV hzS.2 hzS.1.2
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have hcy3 : (c * y * c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3]
    simp
  have hrel : c * y * c⁻¹ = ⁅c, y⁆ * y := by
    simp only [commutatorElement_def]
    group
  have hcomm : Commute ⁅c, y⁆ y := hzy.symm
  have h1 : (⁅c, y⁆ * y) ^ 3 = ⁅c, y⁆ ^ 3 * y ^ 3 := hcomm.mul_pow 3
  rw [← hrel, hcy3, hy3, mul_one] at h1
  have h2 : ⁅c, y⁆ ^ 3 = ⁅c, y⁆ := by
    rw [pow_succ, hz2, one_mul]
  have h4 : ⁅c, y⁆ = 1 := by rw [← h2]; exact h1.symm
  rw [h4, one_mul] at hrel
  have := hrel
  calc y * c = (c * y * c⁻¹) * c := by rw [hrel]
    _ = c * y := by group

end Basic

section Bar

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W)

theorem commutator_subgroupOf {A B G : Subgroup (MulAut V)} (hA : A ≤ G) (hB : B ≤ G) :
    ⁅A.subgroupOf G, B.subgroupOf G⁆ = (⁅A, B⁆).subgroupOf G := by
  have hAB : ⁅A, B⁆ ≤ G := (Subgroup.commutator_mono hA hB).trans (Subgroup.commutator_le_self _)
  apply Subgroup.map_injective G.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]

theorem barW_commutator {A B : Subgroup (MulAut V)} (hA : A ≤ G) (hB : B ≤ G) :
    ⁅barW h A, barW h B⁆ = barW h ⁅A, B⁆ := by
  unfold barW
  rw [← Subgroup.map_commutator, commutator_subgroupOf hA hB]

theorem isKGroup_barW (hK : CFSG.IsKGroup ↥G) : CFSG.IsKGroup ↥(barW h G) := by
  rw [barW_self h]
  exact isKGroup_of_surjective hK (resG G W h).rangeRestrict
    (resG G W h).rangeRestrict_surjective

theorem card_barW_lt [Finite V] {q : MulAut V} (hqG : q ∈ G) (hq1 : q ≠ 1) (hqW : q ∈ fixW W) :
    Nat.card ↥(barW h G) < Nat.card ↥G := by
  rw [barW_self h]
  have h1 := (resG G W h).ker.card_mul_index
  rw [Subgroup.index_ker] at h1
  have hker : (resG G W h).ker ≠ ⊥ := by
    intro hbot
    have : (⟨q, hqG⟩ : ↥G) ∈ (resG G W h).ker := (mem_ker_resG h).mpr hqW
    rw [hbot, Subgroup.mem_bot] at this
    exact hq1 (congrArg Subtype.val this)
  have h2 : 1 < Nat.card ↥(resG G W h).ker := (Subgroup.one_lt_card_iff_ne_bot _).mpr hker
  have h3 : 0 < Nat.card ↥(resG G W h).range := Nat.card_pos
  nlinarith

theorem barW_eq_bot_of_le_fixW {T : Subgroup (MulAut V)} (hT : T ≤ fixW W) :
    barW h T = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  exact (mem_ker_resG h).mpr (hT hg) |> fun h1 => MonoidHom.mem_ker.mp h1

theorem barW_ne_bot_of_not_le_fixW {T : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hT : ¬ T ≤ fixW W) : barW h T ≠ ⊥ := by
  intro hbot
  apply hT
  intro t ht
  have h1 : resG G W h ⟨t, hTG ht⟩ ∈ barW h T := resG_mem_barW h ht
  rw [hbot, Subgroup.mem_bot] at h1
  exact (mem_ker_resG h).mp (MonoidHom.mem_ker.mpr h1)

theorem isPGroup_barW {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT2 : IsPGroup 2 ↥T) :
    IsPGroup 2 ↥(barW h T) :=
  (IsPGroup.of_surjective hT2 (Subgroup.subgroupOfEquivOfLe hTG).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTG).symm.surjective).map _

theorem barW_le_centralizer {T Y : Subgroup (MulAut V)} (hYG : Y ≤ G)
    (hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V))) :
    barW h Y ≤ barW h G ⊓ Subgroup.centralizer (barW h T : Set (MulAut ↥W)) := by
  refine le_inf (barW_mono h hYG) ?_
  intro yb hyb
  rw [Subgroup.mem_centralizer_iff]
  intro tb htb
  obtain ⟨y, hy, rfl⟩ := (mem_barW h).mp hyb
  obtain ⟨t, ht, rfl⟩ := (mem_barW h).mp htb
  have : (t : MulAut V) * (y : MulAut V) = (y : MulAut V) * (t : MulAut V) :=
    Subgroup.mem_centralizer_iff.mp (hYT hy) _ ht
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext this

end Bar

section O2

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem oResidualTwo_eq_top_of_perfect' {L : Type} [Group L] [Finite L] (h : Group.IsPerfect L) :
    oResidualTwo L = ⊤ := by
  rw [oResidualTwo_eq_top_iff]
  intro N hN hpow
  have hp : IsPGroup 2 (L ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hpow g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have hnil : Group.IsNilpotent (L ⧸ N) := hp.isNilpotent
  have := hnil
  have hperf : Group.IsPerfect (L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  by_contra hne
  obtain ⟨g, -, hg⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have hnt : Nontrivial (L ⧸ N) :=
    ⟨⟨(g : L ⧸ N), 1, fun h1 => hg ((QuotientGroup.eq_one_iff g).mp h1)⟩⟩
  exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance

omit [CommGroup V] in
theorem noTwoQuotient_of_perfect {Γ : Type} [Group Γ] [Finite Γ] {Y : Subgroup Γ}
    (hperf : ⁅Y, Y⁆ = Y) : SubTwo.NoTwoQuotient Y :=
  SubTwo.noTwoQuotient_of_oResidualTwo
    (oResidualTwo_eq_top_of_perfect' (Subgroup.isPerfect_iff.mpr hperf))

theorem fixV_inv (G : Subgroup (MulAut V)) : GInv G (fixV (oTwoIn G)) := by
  intro g hg w hw q hq
  have hQn : G ≤ Subgroup.normalizer (oTwoIn G : Set (MulAut V)) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn G)
  have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ oTwoIn G :=
    (Subgroup.mem_normalizer_iff.mp (hQn (G.inv_mem hg)) q).mp hq
  have h1 := hw _ hq'
  have h2 : (q : MulAut V) (g w) = g ((g⁻¹ * q * g⁻¹⁻¹) w) := by
    simp [MulAut.mul_apply]
  show q (g w) = g w
  rw [h2, h1]

omit [CommGroup V] in
theorem lift4_of_subnormal {Γ : Type} [CommGroup Γ] [Finite Γ] {G Y : Subgroup (MulAut Γ)}
    (hYG : Y ≤ G) (hsub : (Y.subgroupOf G).IsSubnormal) (hY : ClassX4 Y) : Lift4 G Y Y := by
  refine ⟨le_rfl, hYG, hsub, ?_⟩
  rcases classX4_iff.mp hY with hc | ⟨n, hn, hΩ⟩
  · exact Or.inl ⟨hc, Or.inl rfl⟩
  · exact Or.inr ⟨n, hn, hΩ, Or.inl rfl⟩

theorem emb4_caseB [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (hpre : Emb4Pre G T Y) {W : Subgroup V} (T' : Trans G Y W) (hTW : ¬ T ≤ fixW W)
    (hsm : Smaller (barW T'.inv G) G) : False := by
  have hperf := hpre.adm.hperf
  have hcls := hpre.adm.hcls
  have hYG : Y ≤ G := T'.yg
  have hTG := hpre.adm.hTG
  have hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V)) := fun y hy => (hpre.adm.hYC hy).2
  have hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)) := hpre.adm.le_centralizer
  have hsubN := isSubnormal_barW_normalizer T'.inv hYG hTG hpre.adm.hT2 T'.cy hTY hpre.sylow hYT
    hpre.adm.hsub
  have hbarT1 : barW T'.inv T ≠ ⊥ := barW_ne_bot_of_not_le_fixW T'.inv hTG hTW
  have hsubC := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
    (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)) hsubN
  have hperfbar : ⁅barW T'.inv Y, barW T'.inv Y⁆ = barW T'.inv Y := by
    rw [barW_commutator T'.inv hYG hYG, hperf]
  have hadm : Adm4 (barW T'.inv G) (barW T'.inv T) (barW T'.inv Y) :=
    ⟨barW_mono T'.inv hTG, hbarT1, isPGroup_barW T'.inv hTG hpre.adm.hT2,
      barW_le_centralizer T'.inv hYG hYT, hsubC, hperfbar, T'.classX4_bar hV hcls⟩
  have hVW : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  obtain ⟨X, hX⟩ := hpre.ih ↥W hVW (barW T'.inv G) hsm (isKGroup_barW T'.inv hpre.kgroup)
    (barW T'.inv T) (barW T'.inv Y) hadm
  have hY2 : ¬ IsPGroup 2 ↥(barW T'.inv Y) := (T'.classX4_bar hV hcls).not_isPGroup hVW
  have hgen := Lift4.conjClosure_eq hVW hY2 hX
  obtain ⟨hYX, hXG, hXsub, h4⟩ := hX
  have B : BlockHyp T' X := ⟨hXG, hYX, hXsub, hgen⟩
  rcases h4 with ⟨hc, harr⟩ | ⟨n, hn, hΩ, hcase⟩
  · obtain ⟨K, hYK, hKG, hKsub, -, hKc, harrK⟩ := T'.ascent hV B hc harr
    exact hpre.nolift ⟨K, hYK, hKG, hKsub, Or.inl ⟨hKc, harrK⟩⟩
  · obtain ⟨K, hYK, hKG, hKsub, hnat, hcaseK⟩ := T'.ascent_nat hV hn B hΩ hcase
    exact hpre.nolift ⟨K, hYK, hKG, hKsub, Or.inr ⟨n, hn, hnat, hcaseK⟩⟩

theorem o2Step4_holds : O2Step4 := by
  intro V _ _ hV G T Y hpre _
  by_contra hne
  have hQne : oTwoIn G ≠ ⊥ := by
    intro hQ
    apply hne
    have h0 : (pCore 2 ↥G).map G.subtype = ⊥ := hQ
    exact (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp h0
  obtain ⟨⟨q, hqQ⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have hperf := hpre.adm.hperf
  have hcls := hpre.adm.hcls
  have hYG : Y ≤ G := fun y hy => (hpre.adm.hYC hy).1
  have hTG := hpre.adm.hTG
  have hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V)) := fun y hy => (hpre.adm.hYC hy).2
  have hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)) := hpre.adm.le_centralizer
  have hQ2 : IsPGroup 2 ↥(oTwoIn G) := SixThree.isPGroup_oTwoIn G
  have hGN : G ≤ Subgroup.normalizer (oTwoIn G : Set (MulAut V)) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn G)
  have hno := noTwoQuotient_of_perfect hperf
  have hoy : ⁅oTwoIn Y, Y⁆ = ⊥ := commutator_oTwoIn_eq_bot hV hperf hcls
  have hQY : ⁅oTwoIn G, Y⁆ = ⊥ :=
    commutator_eq_bot_of_centralizer hno (Or.inl hperf) hoy hpre.adm.hT2 hQ2 (oTwoIn_le G)
      (hTG.trans hGN) (hYG.trans hGN) hpre.adm.hYC hpre.adm.hsub
  have hGW : GInv G (fixV (oTwoIn G)) := fixV_inv G
  have hQYc : ∀ q ∈ oTwoIn G, ∀ y ∈ Y, q * y = y * q := fun q hq y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQY hq)
      y hy).symm
  have hYW : commV Y ≤ fixV (oTwoIn G) := commV_le_fixV_of_commute hV hperf hcls hQ2 hQYc
  have hcy := fixW_le_centralizer_perfect hV hGW hYG hYW hperf hQY
  let T' : Trans G Y (fixV (oTwoIn G)) :=
    ⟨hGW, hYG, hYW, hcy, hQY, hoy, hno, USelf_of_perfect hperf⟩
  by_cases hTW : T ≤ fixW (fixV (oTwoIn G))
  ·
    have hsubN := isSubnormal_barW_normalizer T'.inv hYG hTG hpre.adm.hT2 T'.cy hTY hpre.sylow
      hYT hpre.adm.hsub
    have hbarT : barW T'.inv T = ⊥ := barW_eq_bot_of_le_fixW T'.inv hTW
    rw [hbarT, Subgroup.normalizer_eq_top, inf_top_eq] at hsubN
    have B : BlockHyp T' (barW T'.inv Y) := ⟨barW_mono T'.inv hYG, le_rfl, hsubN, conjClosure_self⟩
    have hKY : conjClosure Y (preW T'.inv (barW T'.inv Y)) = Y :=
      le_antisymm (T'.conj_le_of_eq rfl) le_conjClosure
    have hsubY : (Y.subgroupOf G).IsSubnormal := hKY ▸ B.k_sub
    exact hpre.nolift ⟨Y, lift4_of_subnormal hYG hsubY hcls⟩
  · have hqne : q ≠ 1 := fun h1 => hq1 (Subtype.ext h1)
    exact emb4_caseB hV hpre T' hTW
      (Or.inl (card_barW_lt T'.inv (oTwoIn_le G hqQ) hqne (fun w hw => hw q hqQ)))

omit [CommGroup V] in
theorem eq_one_of_sq_of_card_three {Γ : Type} [Group Γ] {Y : Subgroup Γ} (h3 : Nat.card ↥Y = 3)
    {r : Γ} (hr : r ∈ Y) (h2 : r ^ 2 = 1) : r = 1 := by
  have h3' : r ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨r, hr⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have : r = r ^ 3 * (r ^ 2)⁻¹ := by group
  rw [this, h3', h2]
  simp

theorem emb5_caseB [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (hpre : Emb5Pre G T Y) {W : Subgroup V} (T' : Trans G Y W) (hTW : ¬ T ≤ fixW W)
    (hsm : Smaller (barW T'.inv G) G) : False := by
  have h3 := hpre.adm.h3
  have h4 := hpre.adm.h4
  have hYG : Y ≤ G := T'.yg
  have hTG := hpre.adm.hTG
  have hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V)) := fun y hy => (hpre.adm.hYC hy).2
  have hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)) := hpre.adm.le_centralizer
  have hsubN := isSubnormal_barW_normalizer T'.inv hYG hTG hpre.adm.hT2 T'.cy hTY hpre.sylow hYT
    hpre.adm.hsub
  have hbarT1 : barW T'.inv T ≠ ⊥ := barW_ne_bot_of_not_le_fixW T'.inv hTG hTW
  have hsubC := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
    (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)) hsubN
  have hinjY : Y ⊓ fixW W = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    exact eq_one_of_sq_of_card_three h3 hr.1
      (sq_eq_one_of_mem_trivQ_fixW hV (commV_le_iff_le_trivQ.mp T'.yw hr.1) hr.2)
  have h3' : Nat.card ↥(barW T'.inv Y) = 3 := by
    rw [← Nat.card_congr (barWEquiv T'.inv hYG hinjY).toEquiv]
    exact h3
  have h4' : Nat.card ↥(commV (barW T'.inv Y)) = 4 := by
    have h2 := map_commV_barW_eq T'.inv hYG T'.hU_self
    rw [← Subgroup.card_map_of_injective (f := W.subtype) W.subtype_injective, h2]
    exact h4
  have hadm : Adm5 (barW T'.inv G) (barW T'.inv T) (barW T'.inv Y) :=
    ⟨barW_mono T'.inv hTG, hbarT1, isPGroup_barW T'.inv hTG hpre.adm.hT2,
      barW_le_centralizer T'.inv hYG hYT, hsubC, h3', h4'⟩
  have hVW : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  obtain ⟨X, hX⟩ := hpre.ih ↥W hVW (barW T'.inv G) hsm (isKGroup_barW T'.inv hpre.kgroup)
    (barW T'.inv T) (barW T'.inv Y) hadm
  have hY2 : ¬ IsPGroup 2 ↥(barW T'.inv Y) := not_isPGroup_two_of_card_three h3'
  have hgen := Lift5.conjClosure_eq hY2 hX
  obtain ⟨hYX, hXG, hXsub, hc, harr⟩ := hX
  have B : BlockHyp T' X := ⟨hXG, hYX, hXsub, hgen⟩
  obtain ⟨K, hYK, hKG, hKsub, -, hKc, harrK⟩ := T'.ascent hV B hc harr
  exact hpre.nolift ⟨K, hYK, hKG, hKsub, hKc, harrK⟩

theorem o2Step5_holds : O2Step5 := by
  intro V _ _ hV G T Y hpre _
  by_contra hne
  have hQne : oTwoIn G ≠ ⊥ := by
    intro hQ
    apply hne
    have h0 : (pCore 2 ↥G).map G.subtype = ⊥ := hQ
    exact (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp h0
  obtain ⟨⟨q, hqQ⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have h3 := hpre.adm.h3
  have h4 := hpre.adm.h4
  have hYG : Y ≤ G := fun y hy => (hpre.adm.hYC hy).1
  have hTG := hpre.adm.hTG
  have hYT : Y ≤ Subgroup.centralizer (T : Set (MulAut V)) := fun y hy => (hpre.adm.hYC hy).2
  have hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)) := hpre.adm.le_centralizer
  have hQ2 : IsPGroup 2 ↥(oTwoIn G) := SixThree.isPGroup_oTwoIn G
  have hGN : G ≤ Subgroup.normalizer (oTwoIn G : Set (MulAut V)) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn G)
  have hno := noTwoQuotient_of_card_three h3
  have hoy : ⁅oTwoIn Y, Y⁆ = ⊥ := by
    rw [oTwoIn_eq_bot_of_card_three h3]
    exact Subgroup.commutator_bot_left Y
  have hQY : ⁅oTwoIn G, Y⁆ = ⊥ :=
    commutator_eq_bot_of_centralizer hno (Or.inr h3) hoy hpre.adm.hT2 hQ2 (oTwoIn_le G)
      (hTG.trans hGN) (hYG.trans hGN) hpre.adm.hYC hpre.adm.hsub
  have hGW : GInv G (fixV (oTwoIn G)) := fixV_inv G
  have hQYc : ∀ q ∈ oTwoIn G, ∀ y ∈ Y, q * y = y * q := fun q hq y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQY hq)
      y hy).symm
  have hYW : commV Y ≤ fixV (oTwoIn G) := commV_le_fixV_of_commute_three hV h3 h4 hQ2 hQYc
  have hcy := fixW_le_centralizer_three hV hGW hYG hYW h3 hQY
  have hodd : Odd (Nat.card ↥Y) := by rw [h3]; decide
  let T' : Trans G Y (fixV (oTwoIn G)) :=
    ⟨hGW, hYG, hYW, hcy, hQY, hoy, hno, USelf_of_odd hV hodd⟩
  by_cases hTW : T ≤ fixW (fixV (oTwoIn G))
  · have hsubN := isSubnormal_barW_normalizer T'.inv hYG hTG hpre.adm.hT2 T'.cy hTY hpre.sylow
      hYT hpre.adm.hsub
    have hbarT : barW T'.inv T = ⊥ := barW_eq_bot_of_le_fixW T'.inv hTW
    rw [hbarT, Subgroup.normalizer_eq_top, inf_top_eq] at hsubN
    have B : BlockHyp T' (barW T'.inv Y) := ⟨barW_mono T'.inv hYG, le_rfl, hsubN, conjClosure_self⟩
    have hKY : conjClosure Y (preW T'.inv (barW T'.inv Y)) = Y :=
      le_antisymm (T'.conj_le_of_eq rfl) le_conjClosure
    have hsubY : (Y.subgroupOf G).IsSubnormal := hKY ▸ B.k_sub
    exact hpre.nolift ⟨Y, Lift5.of_subnormal hV h3 h4 hYG hsubY⟩
  · have hqne : q ≠ 1 := fun h1 => hq1 (Subtype.ext h1)
    exact emb5_caseB hV hpre T' hTW
      (Or.inl (card_barW_lt T'.inv (oTwoIn_le G hqQ) hqne (fun w hw => hw q hqQ)))

theorem ginv_commV (G : Subgroup (MulAut V)) : GInv G (commV G) :=
  fun _ hg _ hw => commV_invariant hg hw

theorem oTwoIn_eq_bot_of_pCore {G : Subgroup (MulAut V)} (h : pCore 2 ↥G = ⊥) : oTwoIn G = ⊥ := by
  show (pCore 2 ↥G).map G.subtype = ⊥
  rw [h, Subgroup.map_bot]

theorem inf_fixW_commV_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (ho2 : pCore 2 ↥G = ⊥) : G ⊓ fixW (commV G) = ⊥ := by
  have hGW : GInv G (commV G) := fun g hg w hw => commV_invariant hg hw
  rw [eq_bot_iff]
  intro c hc
  have h1 : c ∈ G ⊓ fixW (commV G) ⊓ trivQ (commV G) :=
    ⟨hc, fun v => Subgroup.subset_closure ⟨c, hc.1, v, rfl⟩⟩
  have h2 := inf_fixW_trivQ_le_oTwoIn hV hGW h1
  rwa [oTwoIn_eq_bot_of_pCore ho2] at h2

theorem smaller_barW_commV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (ho2 : pCore 2 ↥G = ⊥) (hne : commV G ≠ ⊤) :
    Smaller (barW (ginv_commV G) G) G := by
  right
  refine ⟨?_, ?_⟩
  · rw [barW_self]
    have hinj : Function.Injective (resG G (commV G) (ginv_commV G)) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have : (g : MulAut V) ∈ G ⊓ fixW (commV G) :=
        ⟨g.2, (mem_ker_resG _).mp (MonoidHom.mem_ker.mpr hg)⟩
      rw [inf_fixW_commV_eq_bot hV ho2, Subgroup.mem_bot] at this
      exact Subtype.ext this
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · have hdvd := Subgroup.card_subgroup_dvd_card (commV G)
    refine Nat.lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun h1 => hne ?_
    exact Subgroup.eq_top_of_card_eq _ h1

theorem commStep4_holds : CommStep4 := by
  intro V _ _ hV G T Y hpre _ ho2
  by_contra hne
  have hperf := hpre.adm.hperf
  have hcls := hpre.adm.hcls
  have hYG : Y ≤ G := fun y hy => (hpre.adm.hYC hy).1
  have hTG := hpre.adm.hTG
  have hQ : oTwoIn G = ⊥ := oTwoIn_eq_bot_of_pCore ho2
  have hGW : GInv G (commV G) := fun g hg w hw => commV_invariant hg hw
  have hC := inf_fixW_commV_eq_bot hV ho2
  let T' : Trans G Y (commV G) :=
    ⟨hGW, hYG, commV_mono hYG,
      fun c hc => by
        rw [hC, Subgroup.mem_bot] at hc
        rw [hc]
        exact Subgroup.one_mem _,
      by rw [hQ]; exact Subgroup.commutator_bot_left Y,
      commutator_oTwoIn_eq_bot hV hperf hcls, noTwoQuotient_of_perfect hperf,
      USelf_of_perfect hperf⟩
  have hTW : ¬ T ≤ fixW (commV G) := by
    intro h1
    apply hpre.adm.hT1
    rw [eq_bot_iff]
    intro t ht
    have : t ∈ G ⊓ fixW (commV G) := ⟨hTG ht, h1 ht⟩
    rw [hC] at this
    exact this
  exact emb4_caseB hV hpre T' hTW (smaller_barW_commV hV ho2 hne)

theorem commStep5_holds : CommStep5 := by
  intro V _ _ hV G T Y hpre _ ho2
  by_contra hne
  have h3 := hpre.adm.h3
  have hYG : Y ≤ G := fun y hy => (hpre.adm.hYC hy).1
  have hTG := hpre.adm.hTG
  have hQ : oTwoIn G = ⊥ := oTwoIn_eq_bot_of_pCore ho2
  have hGW : GInv G (commV G) := fun g hg w hw => commV_invariant hg hw
  have hC := inf_fixW_commV_eq_bot hV ho2
  have hodd : Odd (Nat.card ↥Y) := by rw [h3]; decide
  have hoy : ⁅oTwoIn Y, Y⁆ = ⊥ := by
    rw [oTwoIn_eq_bot_of_card_three h3]
    exact Subgroup.commutator_bot_left Y
  let T' : Trans G Y (commV G) :=
    ⟨hGW, hYG, commV_mono hYG,
      fun c hc => by
        rw [hC, Subgroup.mem_bot] at hc
        rw [hc]
        exact Subgroup.one_mem _,
      by rw [hQ]; exact Subgroup.commutator_bot_left Y, hoy, noTwoQuotient_of_card_three h3,
      USelf_of_odd hV hodd⟩
  have hTW : ¬ T ≤ fixW (commV G) := by
    intro h1
    apply hpre.adm.hT1
    rw [eq_bot_iff]
    intro t ht
    have : t ∈ G ⊓ fixW (commV G) := ⟨hTG ht, h1 ht⟩
    rw [hC] at this
    exact this
  exact emb5_caseB hV hpre T' hTW (smaller_barW_commV hV ho2 hne)

end O2

end CFSG.CGT.PushingUpLit.CGT6
