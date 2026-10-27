module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutWClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Comm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Diagonal

public section

namespace CFSG.OddStandard.SmallF3.Omega.NCPWide

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.Omega CFSG.LocalAnalysis.ComponentInitial
  CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G]

@[expose] def Unp (K : Subgroup G) : Prop :=
  InCStar K ∧ InFStar K ∧ ¬ InF K ∧ ¬ IsL3Eps3 K

@[expose] def GoodI (B : Subgroup G) (x : G) : Prop :=
  orderOf x = 2 ∧ IsComponentIn B (centralizer ({x} : Set G))

@[expose] def BadI (B : Subgroup G) (y : G) : Prop :=
  orderOf y = 2 ∧ y ∈ centralizer (B : Set G) ∧ ¬ IsComponentIn B (centralizer ({y} : Set G))

structure SwapCfg (B : Subgroup G) (x y : G) (M : Subgroup G) : Prop where
  x_ord : orderOf x = 2
  y_ord : orderOf y = 2
  comm : x * y = y * x
  comp : IsComponentIn M (centralizer ({y} : Set G))
  ne : CFSG.conjugate M x ≠ M
  mem_iff : ∀ b : G, b ∈ B ↔ ∃ m ∈ M, b = m * (x * m * x)

theorem le_cent_iff {B : Subgroup G} {y : G} :
    B ≤ centralizer ({y} : Set G) ↔ y ∈ centralizer (B : Set G) :=
  ⟨fun h => Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.1 (h ha),
    fun h a ha => Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 h a ha)⟩

theorem badI_iff {B : Subgroup G} {y : G} : BadI B y ↔ ThmU.BadInv B y := by
  unfold BadI ThmU.BadInv
  rw [le_cent_iff]
  exact Iff.rfl

theorem BadI.conj {B : Subgroup G} {y c : G} (h : BadI B y) (hc : ∀ b ∈ B, c * b = b * c) :
    BadI B (c * y * c⁻¹) :=
  badI_iff.2 (ThmU.BadInv.conj (badI_iff.1 h) hc)

theorem goodI_of_not_badI {B : Subgroup G} {y : G} (hy : orderOf y = 2)
    (hB : y ∈ centralizer (B : Set G)) (h : ¬ BadI B y) : GoodI B y :=
  ThmU.goodInv_of_not_badInv hy (le_cent_iff.2 hB) (fun hh => h (badI_iff.2 hh))

theorem BadI.not_goodI {B : Subgroup G} {y : G} (h : BadI B y) : ¬ GoodI B y :=
  fun hg => h.2.2 hg.2

theorem not_mem_of_unp [Finite G] {K : Subgroup G} (hK : Unp K) {c : G} (hc : orderOf c = 2)
    (hcK : c ∈ centralizer (K : Set G)) : c ∉ K := by
  intro hcmem
  obtain ⟨-, hXF, hF, hL⟩ := hK
  unfold InFStar IsFStarGroup at hXF
  rcases hXF with hF' | ⟨hq, hstar⟩
  · exact hF hF'
  have hs : IsSimpleGroup (K ⧸ CFSG.oddCore K) := by
    unfold SmallF3StarQuotient at hstar
    rcases hstar with h | h | h | h
    · exact (CFSG.LieType.Simplicity.fam_classical_converse (K ⧸ CFSG.oddCore K)
        ⟨.PSL, 2, 3, 2, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
    · exact (CFSG.LieType.Simplicity.fam_classical_converse (K ⧸ CFSG.oddCore K)
        ⟨.PSL, 2, 3, 4, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
    · exact absurd (Or.inl h) hL
    · exact absurd (Or.inr h) hL
  have hcen := ff_center_eq_oddCore_of_simple hq hs
  have hmem : (⟨c, hcmem⟩ : K) ∈ center K := by
    refine Subgroup.mem_center_iff.mpr fun k => ?_
    apply Subtype.ext
    show k.1 * c = c * k.1
    exact Subgroup.mem_centralizer_iff.mp hcK k.1 k.2
  rw [hcen] at hmem
  have hodd := ff_odd_card_oddCore K
  have hdvd : orderOf (⟨⟨c, hcmem⟩, hmem⟩ : CFSG.oddCore K) ∣ Nat.card (CFSG.oddCore K) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨⟨c, hcmem⟩, hmem⟩ : CFSG.oddCore K) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hc
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem exists_swapCfg [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {B : Subgroup G} (hB : Unp B) {x y : G} (hx : GoodI B x) (hy : BadI B y) (hxy : x * y = y * x) :
    ∃ M : Subgroup G, SwapCfg B x y M ∧ Unp M := by
  obtain ⟨hBC, hBF, hBnF, hBL⟩ := hB
  have hBy : B ≤ centralizer ({y} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy.2.1 a ha)
  have hpair : centralizer ({x, y} : Set G) ≤ centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Set.mem_insert x {y}))
  have hBxy : B ≤ centralizer ({x, y} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | hw
    · exact Subgroup.mem_centralizer_iff.mp (hx.2.le hz) _ (Set.mem_singleton _)
    · rw [Set.mem_singleton_iff.mp hw]
      exact Subgroup.mem_centralizer_iff.mp (hBy hz) _ (Set.mem_singleton _)
  have hBpair : IsComponentIn B (centralizer ({x, y} : Set G)) := hx.2.mono hBxy hpair
  obtain ⟨M, hM, hBle⟩ := hS.lBalance x y hx.1 hy.1 hxy B hBpair
  have hMF : InFStar M := hS.a2 x y hx.1 hy.1 hxy B M hBpair hM hBle hBF
  have hx2 : x * x = 1 := by
    rw [← pow_two]
    exact hx.1 ▸ pow_orderOf_eq_one x
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  by_cases hMx : CFSG.conjugate M x = M
  · exfalso
    have hBM : B ≤ M := by
      rw [hMx, sup_idem] at hBle
      exact hBle
    rcases commutator_zpowers_eq_self_or_le_centralizer hM.isQuasisimple hMx with hcM | hMc
    · exact aor_not_walterArrow_of_inCStar hBC M ⟨x, y, hx.1, hy.1, hxy, hx.2, hM, hBM, hcM⟩
    · have hBM' : IsComponentIn B M := hx.2.mono hBM hMc
      have hMM : IsComponentIn M M := isComponentIn_of_normal le_rfl hM.isQuasisimple (by
        rw [Subgroup.subgroupOf_self]
        infer_instance)
      exact hy.2.2 (by rw [hBM'.eq_of_le hMM hBM]; exact hM)
  · have hxy' : x ∈ centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxy
    have hM' : IsComponentIn (CFSG.conjugate M x) (centralizer ({y} : Set G)) :=
      hM.conjugate hxy'
    have hne : M ⊔ CFSG.conjugate M x ≠ M := by
      intro heq
      exact hMx (hM'.eq_of_le hM (le_sup_right.trans heq.le))
    have hdiag : WalterArrowDiag B M := ⟨x, y, hx.1, hy.1, hxy, hx.2, hM, hBle, hne⟩
    obtain ⟨e⟩ := hBC.2 M (Relation.ReflTransGen.single (Or.inr hdiag))
    have hctr : ctrQ B = ctrQ M := Nat.card_congr e.toEquiv
    have hMp : ¬ (InF M ∨ IsL3Eps3 M) := fun hMp =>
      ctrQ_ne_of_pocketed hMF hMp hBF hBnF hBL hctr.symm
    rw [not_or] at hMp
    have hMC : InCStar M := aor_inCStar_of_walterArrowDiag hBC hdiag
    refine ⟨M, ⟨hx.1, hy.1, hxy, hM, hMx, ?_⟩, hMC, hMF, hMp.1, hMp.2⟩
    have hcj : CFSG.EvenSporadicStandard.Induction.ThmU.cj x M = CFSG.conjugate M x := by
      unfold CFSG.EvenSporadicStandard.Induction.ThmU.cj CFSG.conjugate
      rw [hxinv]
    have hc : CFSG.EvenSporadicStandard.Induction.ThmU.DiagComm x M := by
      intro a ha b hb
      rw [hcj] at hb
      exact hM.commute_of_ne hM' (Ne.symm hMx) a ha b hb
    let f : ↥M →* G :=
      { toFun := fun m => CFSG.EvenSporadicStandard.Induction.ThmU.diag x m.1
        map_one' := CFSG.EvenSporadicStandard.Induction.ThmU.diag_one
        map_mul' := fun a b => CFSG.EvenSporadicStandard.Induction.ThmU.diag_mul hc a.2 b.2 }
    have hfmem : ∀ g : G, g ∈ f.range ↔ ∃ m ∈ M, g = m * (x * m * x) := by
      intro g
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨m.1, m.2, ?_⟩
        rw [← hm]
        show CFSG.EvenSporadicStandard.Induction.ThmU.diag x m.1 = _
        unfold CFSG.EvenSporadicStandard.Induction.ThmU.diag
        rw [hxinv]
      · rintro ⟨m, hm, rfl⟩
        refine ⟨⟨m, hm⟩, ?_⟩
        show CFSG.EvenSporadicStandard.Induction.ThmU.diag x m = _
        unfold CFSG.EvenSporadicStandard.Induction.ThmU.diag
        rw [hxinv]
    have hBperf : ⁅B, B⁆ = B := CFSG.EvenSporadicStandard.Induction.ThmU.IsCompIn.perfect hx.2
    have hBfix : ∀ k ∈ B, x * k * x⁻¹ = k := by
      intro k hk
      have h1 : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.mp (hx.2.le hk)
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    have hBle' : B ≤ M ⊔ CFSG.EvenSporadicStandard.Induction.ThmU.cj x M := by
      rw [hcj]; exact hBle
    have hBD : B ≤ f.range := by
      intro k hk
      obtain ⟨m, hm, hkm⟩ :=
        CFSG.EvenSporadicStandard.Induction.ThmU.le_diag_of_perfect hx2 hc hBperf hBle' hBfix k hk
      exact ⟨⟨m, hm⟩, hkm.symm⟩
    have hker : f.ker ≤ center ↥M := by
      intro m hm
      rw [MonoidHom.mem_ker] at hm
      change m.1 * (x * m.1 * x⁻¹) = 1 at hm
      have hinv : x * m.1 * x⁻¹ = m.1⁻¹ := eq_inv_of_mul_eq_one_right hm
      have hmcj : m.1 ∈ CFSG.EvenSporadicStandard.Induction.ThmU.cj x M := by
        have h1 : x * m.1⁻¹ * x⁻¹ ∈ CFSG.EvenSporadicStandard.Induction.ThmU.cj x M :=
          CFSG.EvenSporadicStandard.Induction.ThmU.conj_mem_cj (M.inv_mem m.2)
        have h2 : x * m.1⁻¹ * x⁻¹ = m.1 := by
          have : x * m.1⁻¹ * x⁻¹ = (x * m.1 * x⁻¹)⁻¹ := by group
          rw [this, hinv, inv_inv]
        rwa [h2] at h1
      have hcen := CFSG.EvenSporadicStandard.Induction.ThmU.inf_cj_central hc ⟨m.2, hmcj⟩
      refine Subgroup.mem_center_iff.mpr fun n => Subtype.ext ?_
      exact hcen n.1 ((le_sup_left : M ≤ M ⊔ _) n.2)
    have hDq := CFSG.GH74.Generic.S1.isQuasisimple_range_of_ker hM.isQuasisimple f hker
    have hDle : f.range ≤ centralizer ({x, y} : Set G) := by
      rintro _ ⟨m, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hfx := CFSG.EvenSporadicStandard.Induction.ThmU.diag_fixed hx2 hc m.2
      rcases hw with rfl | hw
      · change w * CFSG.EvenSporadicStandard.Induction.ThmU.diag w m.1 =
          CFSG.EvenSporadicStandard.Induction.ThmU.diag w m.1 * w
        calc w * CFSG.EvenSporadicStandard.Induction.ThmU.diag w m.1
            = (w * CFSG.EvenSporadicStandard.Induction.ThmU.diag w m.1 * w⁻¹) * w := by group
          _ = _ := by rw [hfx]
      · rw [Set.mem_singleton_iff.mp hw]
        change y * (m.1 * (x * m.1 * x⁻¹)) = (m.1 * (x * m.1 * x⁻¹)) * y
        have hmy : m.1 * y = y * m.1 :=
          Subgroup.mem_centralizer_singleton_iff.mp (hM.le m.2)
        have hxm : x * m.1 * x⁻¹ ∈ CFSG.conjugate M x := by
          rw [← hcj]; exact CFSG.EvenSporadicStandard.Induction.ThmU.conj_mem_cj m.2
        have hxmy : (x * m.1 * x⁻¹) * y = y * (x * m.1 * x⁻¹) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hM'.le hxm)
        calc y * (m.1 * (x * m.1 * x⁻¹)) = (y * m.1) * (x * m.1 * x⁻¹) := by group
          _ = (m.1 * y) * (x * m.1 * x⁻¹) := by rw [hmy]
          _ = m.1 * (y * (x * m.1 * x⁻¹)) := by group
          _ = m.1 * ((x * m.1 * x⁻¹) * y) := by rw [hxmy]
          _ = (m.1 * (x * m.1 * x⁻¹)) * y := by group
    have hBD' : IsComponentIn B f.range := hBpair.mono hBD hDle
    have hDD : IsComponentIn f.range f.range := isComponentIn_of_normal le_rfl hDq (by
      rw [Subgroup.subgroupOf_self]
      infer_instance)
    have hBeq : B = f.range := hBD'.eq_of_le hDD hBD
    intro b
    rw [hBeq]
    exact hfmem b

end CFSG.OddStandard.SmallF3.Omega.NCPWide
