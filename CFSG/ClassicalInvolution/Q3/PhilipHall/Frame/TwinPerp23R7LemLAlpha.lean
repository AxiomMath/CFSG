module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZNormT
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionThmD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem t_quiet_at_e_of_ecase1 (hc : P23Cfg n Y R S t K' W u e g) (hE : ECase1 R W e)
    (htC : t ∈ Subgroup.centralizer ({e} : Set Y)) :
    ∀ L : Subgroup (OddQuot e), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk e ⟨t, htC⟩ * y = y * oddQuotMk e ⟨t, htC⟩ := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  obtain ⟨htC', htY, -⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 (ZTwo.twins_tq hc).1 hz
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2
  have hHs : IsSubnormal (coreHull (Om R) e) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (TwinExitPf6.normal_coreHull hΩ hc2).isSubnormal
  set C := Subgroup.centralizer ({e} : Set Y) with hCdef
  set H := coreHull (Om R) e with hH
  set O := classicalInvolutionOddCore ↥H with hO
  let ι : ↥H →* Y := C.subtype.comp H.subtype
  have hιinj : Function.Injective ι :=
    (Subgroup.subtype_injective C).comp (Subgroup.subtype_injective H)
  have hιr : ι.range = rLayer (Om R) e := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  set N : Subgroup (↥H ⧸ O) := (W.comap ι).map (QuotientGroup.mk' O) with hN
  have hW2 : IsPGroup 2 W := by
    obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := hc.std.hW
    exact S₀.isPGroup'.to_le (hWη ▸ iSup₂_le fun U hU => (hη.1 hU).2)
  have hN2 : IsPGroup 2 N := (hW2.comap_of_injective ι hιinj).map _
  have hconj : ∀ x : ↥H, ι x ∈ Subgroup.normalizer (W : Set Y) → ∀ m ∈ N,
      QuotientGroup.mk' O x * m * (QuotientGroup.mk' O x)⁻¹ ∈ N := by
    rintro x hx _ ⟨w, hw, rfl⟩
    refine ⟨x * w * x⁻¹, ?_, by simp⟩
    show ι (x * w * x⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp hw
  have hNn : N.Normal := by
    have hsub : ∀ x : ↥H, ι x ∈ oddCoreOf (rLayer (Om R) e) ⊔
        (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)) := fun x =>
      hE (hιr ▸ ⟨x, rfl⟩)
    have htop : (⊤ : Subgroup ↥H) ≤ (oddCoreOf (rLayer (Om R) e)).comap ι ⊔
        (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)).comap ι := by
      rw [Subgroup.comap_sup_eq_of_le_range]
      · exact fun x _ => hsub x
      · rw [hιr]; exact Subgroup.map_subtype_le _
      · rw [hιr]; exact inf_le_left
    have hnorm : (⊤ : Subgroup (↥H ⧸ O)) ≤ Subgroup.normalizer (N : Set (↥H ⧸ O)) := by
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O q
      have hx := htop (Subgroup.mem_top x)
      have hle : ((oddCoreOf (rLayer (Om R) e)).comap ι ⊔
          (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)).comap ι).map (QuotientGroup.mk' O) ≤
            Subgroup.normalizer (N : Set (↥H ⧸ O)) := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          have hyO : y ∈ O := by
            apply R56.mem_oddCore_coreHull_of_mem_oddCoreOf_coreLayer
            show ι y ∈ oddCoreOf (coreLayer (Om R) e)
            unfold coreLayer
            rw [hmap]
            exact hy
          rw [show QuotientGroup.mk' O y = 1 from (QuotientGroup.eq_one_iff y).mpr hyO]
          exact Subgroup.one_mem _
        · rintro _ ⟨y, hy, rfl⟩
          rw [Subgroup.mem_normalizer_iff]
          intro m
          refine ⟨hconj y hy.2 m, fun hm => ?_⟩
          have hy' : ι y⁻¹ ∈ Subgroup.normalizer (W : Set Y) := by
            rw [map_inv]; exact Subgroup.inv_mem _ hy.2
          have := hconj y⁻¹ hy' _ hm
          simpa [mul_assoc] using this
      exact hle ⟨x, hx, rfl⟩
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hnorm)
  have htN : QuotientGroup.mk' O (⟨⟨t, htC'⟩, htY⟩ : ↥H) ∈ N :=
    ⟨⟨⟨t, htC'⟩, htY⟩, (hd.hzW : ι ⟨⟨t, htC'⟩, htY⟩ ∈ W), rfl⟩
  intro L hL
  exact TL4.quiet_of_inO2_sub hHs htY ⟨N, hNn, hN2, htN⟩ L hL

theorem e_quiet_at_t_of_zdata {Z : Subgroup Y} (hZd : P23ZData t u e Z)
    (heC : e ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∀ L : Subgroup (OddQuot t), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk t ⟨e, heC⟩ * y = y * oddQuotMk t ⟨e, heC⟩ := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hZ2 : IsPGroup 2 ↥(modOdd t Z) :=
    (hZd.isPGroup.comap_of_injective C.subtype C.subtype_injective).map _
  have hZn : (modOdd t Z).Normal := by
    refine ⟨fun q hq x => ?_⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨o, ho, m, hm, hcm⟩ := hZd.frattini c c.2
    obtain ⟨o', ho', rfl⟩ := ho
    have hmC : m ∈ C := (Subgroup.mem_inf.mp hm).1
    have hmN : m ∈ Subgroup.normalizer (Z : Set Y) := (Subgroup.mem_inf.mp hm).2
    have h1 : c = o' * ⟨m, hmC⟩ := Subtype.ext hcm
    obtain ⟨z, hz, rfl⟩ := hq
    have hmz : m * (z : Y) * m⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hmN _).mp (Subgroup.mem_subgroupOf.mp hz)
    have ho1 : oddQuotMk t o' = 1 := oddQuotMk_eq_one_iff.mpr ho'
    refine ⟨⟨m, hmC⟩ * z * ⟨m, hmC⟩⁻¹, Subgroup.mem_subgroupOf.mpr hmz, ?_⟩
    show oddQuotMk t (⟨m, hmC⟩ * z * ⟨m, hmC⟩⁻¹) =
      QuotientGroup.mk' _ c * oddQuotMk t z * (QuotientGroup.mk' _ c)⁻¹
    have h2 : QuotientGroup.mk' (componentClassificationOddCore ↥C) c = oddQuotMk t ⟨m, hmC⟩ := by
      show oddQuotMk t c = _
      rw [h1, map_mul, ho1, one_mul]
    rw [h2, map_mul, map_mul, map_inv]
  intro L hL
  exact TL4.commute_of_mem_normal_isPGroup hL hZn hZ2 (oddQuotMk_mem_modOdd hZd.he heC)

theorem mem_normalizer_alpha_te_of_quiet (hc : P23Cfg n Y R S t K' W u e g)
    (hqt : ∀ heC : e ∈ Subgroup.centralizer ({t} : Set Y), ∀ L : Subgroup (OddQuot t),
      CFSG.IsComponent L → ∀ y ∈ L, oddQuotMk t ⟨e, heC⟩ * y = y * oddQuotMk t ⟨e, heC⟩)
    (hqe : ∀ htC : t ∈ Subgroup.centralizer ({e} : Set Y), ∀ L : Subgroup (OddQuot e),
      CFSG.IsComponent L → ∀ y ∈ L, oddQuotMk e ⟨t, htC⟩ * y = y * oddQuotMk e ⟨t, htC⟩)
    {c d h : Y} (hhc : h * c * h⁻¹ = t * e) (hhd : h * d * h⁻¹ = t) (hc1 : c ≠ 1) (hd1 : d ≠ 1)
    (hdc : d ≠ c) (hdC : d ∈ Subgroup.centralizer ({c} : Set Y))
    (hqc : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨d, hdC⟩ * y = y * oddQuotMk c ⟨d, hdC⟩)
    {Z : Subgroup Y} (hZd : P23ZData t u e Z) {m : Y}
    (hmC : m ∈ Subgroup.centralizer ({t} : Set Y)) (hmN : m ∈ Subgroup.normalizer (Z : Set Y)) :
    m ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, e} : Set Y)) : Set Y) := by
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have ht2 : t * t = 1 := hzt.sq
  have ht1 : t ≠ 1 := hzt.ne_one
  have he2 : e * e = 1 := hd.he2
  have he1 : e ≠ 1 := hd.he1
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  have hte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have hmt : m * t * m⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hmC, mul_inv_cancel_right]
  obtain ⟨y, hy⟩ : ∃ y : Y, m * e * m⁻¹ = y := ⟨_, rfl⟩
  have hyZ : y ∈ Z := by
    rw [← hy]
    exact (Subgroup.mem_normalizer_iff.mp hmN e).mp hZd.he
  have hy2 : y * y = 1 := by
    rw [← hy]
    calc m * e * m⁻¹ * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = 1 := by rw [he2, mul_one, mul_inv_cancel]
  have hey' : e = m⁻¹ * y * m := by rw [← hy]; group
  have hy1 : y ≠ 1 := fun h => he1 (by rw [hey', h]; group)
  have hyt : y ≠ t := fun h => het (by
    rw [hey', h]
    calc m⁻¹ * t * m = m⁻¹ * (m * t * m⁻¹) * m := by rw [hmt]
      _ = t := by group)
  have hty : t * y = y * t := hZd.comm t hZd.ht y hyZ
  have hey : e * y = y * e := hZd.comm e hZd.he y hyZ
  have hconj : Generic.conjSub m (Subgroup.closure ({t, e} : Set Y)) =
      Subgroup.closure ({t, y} : Set Y) := by
    rw [T7A.conjSub_closure_pair, hmt, hy]
  have hA4 := T7A.isElemAbelian2_closure_pair ht2 he2 ht1 he1 het.symm hte
  have hD4 := T7A.isElemAbelian2_closure_pair ht2 hy2 ht1 hy1 hyt.symm hty
  have key : alphaOf (Subgroup.closure ({t, y} : Set Y)) =
      alphaOf (Subgroup.closure ({t, e} : Set Y)) := by
    by_cases hyA : y ∈ Subgroup.closure ({t, e} : Set Y)
    ·
      have hle : Subgroup.closure ({t, y} : Set Y) ≤ Subgroup.closure ({t, e} : Set Y) := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h | h
        · rw [h]
          exact Subgroup.subset_closure (by simp)
        · rw [Set.mem_singleton_iff.mp h]
          exact hyA
      rw [Subgroup.eq_of_le_of_card_ge hle (hA4.1.trans hD4.1.symm).le]
    ·
      obtain ⟨B₃, hB₃⟩ : ∃ B₃ : Subgroup Y, B₃ = Subgroup.closure ({t * y, t, e} : Set Y) :=
        ⟨_, rfl⟩
      have hB : IsElemAbelian 2 B₃ := by
        rw [hB₃]
        exact S24.B_isElemAbelian_of ht2 he2 hy2 hte hty hey
      have hB8 : Nat.card B₃ = 8 := by
        rw [hB₃]
        exact S24.B_natCard_of ht2 he2 hy2 ht1 he1 het.symm hte hty hey hyA
      have hmemB : ∀ x ∈ ({t * y, t, e} : Set Y), x ∈ B₃ := fun x hx => by
        rw [hB₃]
        exact Subgroup.subset_closure hx
      have htB : t ∈ B₃ := hmemB _ (by simp)
      have heB : e ∈ B₃ := hmemB _ (by simp)
      have htyB : t * y ∈ B₃ := hmemB _ (by simp)
      have hyB : y ∈ B₃ := by
        have h := B₃.mul_mem (B₃.inv_mem htB) htyB
        rwa [inv_mul_cancel_left] at h
      have hteB : t * e ∈ B₃ := B₃.mul_mem htB heB
      have hAB : Subgroup.closure ({t, e} : Set Y) ≤ B₃ := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h | h
        · rw [h]; exact htB
        · rw [Set.mem_singleton_iff.mp h]; exact heB
      have hDB : Subgroup.closure ({t, y} : Set Y) ≤ B₃ := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h | h
        · rw [h]; exact htB
        · rw [Set.mem_singleton_iff.mp h]; exact hyB
      have hC : ∀ {a b : Y}, a ∈ B₃ → b ∈ B₃ → b ∈ Subgroup.centralizer ({a} : Set Y) :=
        fun ha hb => Lemma52Proof.le_centralizer_of_mem hB ha hb
      have hte1 : t * e ≠ 1 := fun h => het (by
        calc e = t⁻¹ * (t * e) := by group
          _ = t := by rw [h, mul_one]; exact inv_eq_of_mul_eq_one_right ht2)
      have htte : t ≠ t * e := fun h => he1 (by
        calc e = t⁻¹ * (t * e) := by group
          _ = 1 := by rw [← h, inv_mul_cancel])
      have hmte : m * (t * e) * m⁻¹ = t * y := by
        rw [← hy]
        calc m * (t * e) * m⁻¹ = (m * t * m⁻¹) * (m * e * m⁻¹) := by group
          _ = t * (m * e * m⁻¹) := by rw [hmt]
      have htCe : t ∈ Subgroup.centralizer ({e} : Set Y) := hC heB htB
      have htCte : t ∈ Subgroup.centralizer ({t * e} : Set Y) := hC hteB htB
      have v_t : Hyp51At B₃ t :=
        hyp51At_of_quiet_witness hB htB heB ht1 he1 het (hC htB heB) (hqt _)
      have v_e : Hyp51At B₃ e :=
        hyp51At_of_quiet_witness hB heB htB he1 ht1 het.symm htCe (hqe htCe)
      have v_te : Hyp51At B₃ (t * e) := by
        have h := hyp51At_conj_of_quiet_witness hB (g := h) (c := c) (d := d)
          (by rw [hhc]; exact hteB) (by rw [hhd]; exact htB) hc1 hd1 hdc hdC hqc
        rwa [hhc] at h
      have v_y : Hyp51At B₃ y := by
        have h := hyp51At_conj_of_quiet_witness hB (g := m) (c := e) (d := t)
          (by rw [hy]; exact hyB) (by rw [hmt]; exact htB) he1 ht1 het.symm htCe (hqe htCe)
        rwa [hy] at h
      have hmhc : m * h * c * (m * h)⁻¹ = t * y := by
        rw [← hmte, ← hhc]
        group
      have hmhd : m * h * d * (m * h)⁻¹ = t := by
        rw [← hmt, ← hhd]
        group
      have v_ty : Hyp51At B₃ (t * y) := by
        have h := hyp51At_conj_of_quiet_witness hB (g := m * h) (c := c) (d := d)
          (by rw [hmhc]; exact htyB) (by rw [hmhd]; exact htB) hc1 hd1 hdc hdC hqc
        rwa [hmhc] at h
      have hHA : ∀ a ∈ Subgroup.closure ({t, e} : Set Y), a ≠ 1 → Hyp51At B₃ a := by
        intro a ha ha1
        rcases T8.mem_closure_pair_involutions ht2 he2 hte ha with h | h | h | h
        · exact absurd h ha1
        · rw [h]; exact v_t
        · rw [h]; exact v_e
        · rw [h]; exact v_te
      have hHD : ∀ d ∈ Subgroup.closure ({t, y} : Set Y), d ≠ 1 → Hyp51At B₃ d := by
        intro d hd hd1
        rcases T8.mem_closure_pair_involutions ht2 hy2 hty hd with h | h | h | h
        · exact absurd h hd1
        · rw [h]; exact v_t
        · rw [h]; exact v_y
        · rw [h]; exact v_ty
      exact (Lemma54Local.alphaOf_eq_alphaOf_of_hyp51At hB hB8 hAB hDB hA4.1 hD4.1 hHA
        hHD).symm
  rw [mem_normalizer_iff_conjSub_eq, ← alphaOf_conjSub, hconj, key]

theorem ct_le_normalizer_alpha_of_quiet (hα : P23Alpha n) (hc : P23Cfg n Y R S t K' W u e g)
    (hYT : YType R u e)
    (hqt : ∀ heC : e ∈ Subgroup.centralizer ({t} : Set Y), ∀ L : Subgroup (OddQuot t),
      CFSG.IsComponent L → ∀ y ∈ L, oddQuotMk t ⟨e, heC⟩ * y = y * oddQuotMk t ⟨e, heC⟩)
    (hqe : ∀ htC : t ∈ Subgroup.centralizer ({e} : Set Y), ∀ L : Subgroup (OddQuot e),
      CFSG.IsComponent L → ∀ y ∈ L, oddQuotMk e ⟨t, htC⟩ * y = y * oddQuotMk e ⟨t, htC⟩)
    {c d h : Y} (hhc : h * c * h⁻¹ = t * e) (hhd : h * d * h⁻¹ = t) (hc1 : c ≠ 1) (hd1 : d ≠ 1)
    (hdc : d ≠ c) (hdC : d ∈ Subgroup.centralizer ({c} : Set Y))
    (hqc : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨d, hdC⟩ * y = y * oddQuotMk c ⟨d, hdC⟩)
    {Z : Subgroup Y} (hZd : P23ZData t u e Z) :
    Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  obtain ⟨-, hbal⟩ := hα Y R S t K' W u e g hc hYT
  have hmemB : ∀ x ∈ ({u * e, u, t} : Set Y), x ∈ Subgroup.closure ({u * e, u, t} : Set Y) :=
    fun x hx => Subgroup.subset_closure hx
  have heB : e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmemB u (by simp)))
      (hmemB (u * e) (by simp))
    rwa [inv_mul_cancel_left] at h
  have hAB : Subgroup.closure ({t, e} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact hmemB t (by simp)
    · rw [Set.mem_singleton_iff.mp h]; exact heB
  have hA := hbal _ hAB
    (T7A.isElemAbelian2_closure_pair hzt.sq hd.he2 hzt.ne_one hd.he1 het.symm hte)
  rw [← hA]
  intro c hcC
  obtain ⟨o, ho, m, hm, rfl⟩ := hZd.frattini c hcC
  obtain ⟨hmC, hmN⟩ := Subgroup.mem_inf.mp hm
  exact Subgroup.mul_mem _
    (oddCoreOf_centralizer_le_normalizer_alphaOf (c := t) (z := e) hd.he2 hzt.ne_one hte ho)
    (mem_normalizer_alpha_te_of_quiet hc hqt hqe hhc hhd hc1 hd1 hdc hdC hqc hZd hmC hmN)

namespace LemL

theorem zstar_layer_of_cu (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y))) :
    u * e ∈ zStarOf (rLayer (Om R) u) := by
  have hd := hc.data
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨J₁, -, hJ₁, -, hτ₁, -, -⟩ := R56.u_trans_or_pair hT hc
  obtain ⟨htC, htY, -⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ₁ hτ₁
  have hlay : u * e ∈ rLayer (Om R) u :=
    TwinDisc.coreHull_map_le_rLayer hΩ hc2 (Subgroup.mem_map.mpr ⟨⟨u * e, htC⟩, htY, rfl⟩)
  exact T7T.mem_zStarOf_of_le (rLayer_le_centralizer _ u) hZ hlay

theorem lemL_alpha_eq_bot (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {Z V : Subgroup Y} {f₁ f₂ : Y}
    (hX : LemLCtx n Y R S t K' W u e g Z V f₁ f₂) :
    alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ := by
  have hc := hX.cfg
  have hZ := zstar_layer_of_cu hT hc hX.zstar
  have hYT : YType R u e := Or.inl hZ
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  have hte1 : t * e ≠ 1 := fun h => het (by
    calc e = t⁻¹ * (t * e) := by group
      _ = t := by rw [h, mul_one]; exact inv_eq_of_mul_eq_one_right hzt.sq)
  have htte : t ≠ t * e := fun h => hd.he1 (by
    calc e = t⁻¹ * (t * e) := by group
      _ = 1 := by rw [← h, inv_mul_cancel])
  have htCte : t ∈ Subgroup.centralizer ({t * e} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : Commute t (t * e) := (Commute.refl t).mul_right (T7K.comm_e_of_mem_W hd hd.hzW)
    first | exact h.eq | exact h.eq.symm
  have hNt := ct_le_normalizer_alpha_of_quiet hα hc hYT
    (fun heC => e_quiet_at_t_of_zdata hX.zdata heC)
    (fun htC => t_quiet_at_e_of_ecase1 hc hX.ecase htC)
    (h := 1) (by group) (by group) hte1 hzt.ne_one htte htCte
    (p23E8Z_t_quiet_at_te hT hc hZ htCte) hX.zdata
  exact p23_alpha_eq_bot hc (p23Two_of_thmEQ8 hE hcit hP Y R S t K' W u e g hc)
    (hα Y R S t K' W u e g hc hYT).1 ⟨p23E8Z_cu_le_normalizer_alpha hT hα hc hZ, hNt⟩

theorem lemL_members_isPGroup (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {Z V : Subgroup Y} {f₁ f₂ : Y}
    (hX : LemLCtx n Y R S t K' W u e g Z V f₁ f₂) :
    ∀ J ∈ Om R, IsPGroup 2 ↥J :=
  p23E8Z_members_isPGroup_of_alpha hE hT hcit hP hX.cfg (zstar_layer_of_cu hT hX.cfg hX.zstar)
    (lemL_alpha_eq_bot hE hT hα hcit hP hX)

theorem secCoresTwoGroup_of_isPGroup {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {A : Subgroup G} (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) : SecCoresTwoGroup Ω A := by
  intro J hJ _
  exact SectionThmD.isPGroup_secImage
    ((h2 J hJ).to_le ((tightCore_le _).trans inf_le_left))

theorem lemLCoreTwo_proved (hE : TwinThmEW.ThmEQ8) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hT4 : TwinThmE.T4Supply) : LemLCoreTwo n := by
  intro hcit hP Y _ _ R S t K' W u e g Z V f₁ f₂ hX
  exact secCoresTwoGroup_of_isPGroup
    (lemL_members_isPGroup hE (hT4 n hcit hP) (p23Alpha_proved hD4 hM12 hT4 hcit hP) hcit hP hX)

end LemL

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
