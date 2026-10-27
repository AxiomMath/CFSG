module

public import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelCard
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoSL

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem five_le_of_odd_prime_dvd_add_one {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1) : 5 ≤ p := by
  refine hp.five_le_of_ne_two_of_ne_three hp2 ?_
  rintro rfl
  norm_num at hdp
  have hdvd : d ∣ 2 ^ 2 := by simpa using hdp
  have h2 : d ∣ 2 := hd.dvd_of_dvd_pow hdvd
  exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)

private theorem isSylowOf_map_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] {P : Subgroup A} (e : A ≃* B)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map e.toMonoidHom) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨-, hpg, hdvd⟩ := hP
  refine ⟨le_top, hpg.map e.toMonoidHom, ?_⟩
  rw [Subgroup.relIndex_top_right] at hdvd ⊢
  have hindex : (P.map e.toMonoidHom).index = P.index := by
    simpa using Subgroup.index_map_equiv P e
  rwa [hindex]

private theorem exists_sylow_eq_of_isSylowOf_top {A : Type*} [Group A] [Finite A] {p : ℕ}
    [Fact p.Prime] {P : Subgroup A} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) :
    ∃ T : Sylow p A, (T : Subgroup A) = P := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP
  obtain ⟨-, hpg, hdvd⟩ := hP
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hpg.toSylow hdvd, IsPGroup.toSylow_coe hpg hdvd⟩

private theorem isMaxParabolicP_projStabilizer_flagSpace {p d : ℕ} [Fact p.Prime]
    (hd : 1 ≤ d) (hdn : d < 3) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)))
      (LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) := by
  have hF : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hQ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)))
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) := by
    have h := CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_sl3_zmod_singleton
      (p := p) (d := d) hd hdn
    rwa [LinearFlag.flagStabilizer_singleton] at h
  have hgrp : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.IsMaxParabolicGrp p
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_top_iff_isMaxParabolicGrp _).mp hQ
  have hker : (LinearFlag.proj 3 (ZMod p)).ker ≤
      LinearFlag.stabilizer (LinearFlag.flagSpace 3 (ZMod p) d) := by
    rw [LinearFlag.ker_proj]
    exact LinearFlag.scalars_le_stabilizer _
  have hgrp2 : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.IsMaxParabolicGrp p
      ((LinearFlag.stabilizer (LinearFlag.flagSpace 3 (ZMod p) d)).map
        (LinearFlag.proj 3 (ZMod p))) :=
    (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.isMaxParabolicGrp_map_iff
      (LinearFlag.proj 3 (ZMod p)) (LinearFlag.proj_surjective 3 (ZMod p))
      (CFSG.LocalAnalysis.AGL81I.Section3.proj_ker_le_center 3)
      (CFSG.LocalAnalysis.AGL81I.Section3.coprime_card_proj_ker 3 (by norm_num) hF)
      hker).mpr hgrp
  exact (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_top_iff_isMaxParabolicGrp _).mpr
    hgrp2

private theorem not_dvd_card_upperTriangular {p d : ℕ} [Fact p.Prime] (hp : p.Prime) (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) :
    ¬ d ∣ Nat.card (LinearFlag.upperTriangular 3 (ZMod p)) := by
  intro hdB
  have hdiv : d ∣ Nat.card (ZMod p) ^ 3 * (Nat.card (ZMod p) - 1) ^ 2 :=
    hdB.trans (CFSG.Quasithin.H13.NQCore.L3Odd.card_upperTriangular_dvd (K := ZMod p))
  have hF : Nat.card (ZMod p) = p := Nat.card_zmod p
  rw [hF] at hdiv
  rcases hd.dvd_mul.mp hdiv with h | h
  · have hdp' : d ∣ p := hd.dvd_of_dvd_pow h
    have hdpeq : d = p := (Nat.prime_dvd_prime_iff_eq hd hp).mp hdp'
    have hp1 : p ∣ 1 := by
      have hpp : p ∣ p + 1 := by rwa [hdpeq] at hdp
      have hsub := Nat.dvd_sub hpp (dvd_refl p)
      rwa [Nat.add_sub_cancel_left] at hsub
    exact hp.not_dvd_one hp1
  · have hdpm1 : d ∣ p - 1 := hd.dvd_of_dvd_pow h
    have h2 : d ∣ 2 := by
      have hsub := Nat.dvd_sub hdp hdpm1
      rwa [show p + 1 - (p - 1) = 2 by
        have hp2 : 2 ≤ p := hp.two_le
        omega] at hsub
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)

private theorem isMaxParabolicP_top_of_borel_le {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1)
    {Y : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))}
    (hB : LinearFlag.projUpperTriangular 3 (ZMod p) ≤ Y) (hYne : Y ≠ ⊤)
    (hdY : d ∣ Nat.card Y) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y := by
  classical
  have hp : p.Prime := Fact.out
  set P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    Y.comap (LinearFlag.proj 3 (ZMod p)) with hP
  have hmapP : P.map (LinearFlag.proj 3 (ZMod p)) = Y := by
    rw [hP]
    exact Subgroup.map_comap_eq_self_of_surjective (LinearFlag.proj_surjective 3 (ZMod p)) Y
  have hBup : LinearFlag.upperTriangular 3 (ZMod p) ≤ P := by
    intro x hx
    exact Subgroup.mem_comap.mpr (hB (Subgroup.mem_map_of_mem _ hx))
  have hPne : P ≠ ⊤ := by
    intro h
    apply hYne
    rw [← hmapP, h, Subgroup.map_top_of_surjective _ (LinearFlag.proj_surjective 3 (ZMod p))]
  have hdP : d ∣ Nat.card P := by
    have hdvd : Nat.card Y ∣ Nat.card P := by
      rw [← hmapP]
      exact Subgroup.card_map_dvd P (LinearFlag.proj 3 (ZMod p))
    exact hdY.trans hdvd
  have hPneB : P ≠ LinearFlag.upperTriangular 3 (ZMod p) := by
    intro h
    exact not_dvd_card_upperTriangular hp hd hd2 hdp (h ▸ hdP)
  rcases CFSG.LocalAnalysis.AGL81I.Section3.borel_overgroups_sl3 P hBup with
    htop | h1 | h2 | hB
  · exact absurd htop hPne
  · have hY1 : Y = LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) 1) := by
      rw [← hmapP, h1, LinearFlag.flagStabilizer_singleton]
      rfl
    rw [hY1]
    exact isMaxParabolicP_projStabilizer_flagSpace (p := p) (by norm_num) (by norm_num)
  · have hY1 : Y = LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) 2) := by
      rw [← hmapP, h2, LinearFlag.flagStabilizer_singleton]
      rfl
    rw [hY1]
    exact isMaxParabolicP_projStabilizer_flagSpace (p := p) (by norm_num) (by norm_num)
  · exact absurd hB hPneB

private theorem isMaxParabolicP_top_of_borel_conj_le {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1)
    {Y : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))}
    {x : LinearFlag.projectiveSL 3 (ZMod p)}
    (hBx0 : (LinearFlag.projUpperTriangular 3 (ZMod p)).map
      (MulAut.conj x).toMonoidHom ≤ Y) (hYne : Y ≠ ⊤) (hdY : d ∣ Nat.card Y) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y := by
  classical
  let c : LinearFlag.projectiveSL 3 (ZMod p) ≃* LinearFlag.projectiveSL 3 (ZMod p) :=
    MulAut.conj x
  let c' : LinearFlag.projectiveSL 3 (ZMod p) ≃* LinearFlag.projectiveSL 3 (ZMod p) :=
    MulAut.conj x⁻¹
  have hBx : (LinearFlag.projUpperTriangular 3 (ZMod p)).map c.toMonoidHom ≤ Y := hBx0
  have hcc' : c.toMonoidHom.comp c'.toMonoidHom = MonoidHom.id _ := by
    ext y
    simp [c, c', MulAut.conj_apply]
  have hc'c : c'.toMonoidHom.comp c.toMonoidHom = MonoidHom.id _ := by
    ext y
    simp [c, c', MulAut.conj_apply]
  set Y₃ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)) := Y.map c'.toMonoidHom with hY₃
  have hY₃ne : Y₃ ≠ ⊤ := by
    intro h
    apply hYne
    have h1 : Y₃.map c.toMonoidHom = Y := by
      rw [hY₃, Subgroup.map_map, hcc', Subgroup.map_id]
    rw [h, Subgroup.map_top_of_surjective _ c.surjective] at h1
    exact h1.symm
  have hB : LinearFlag.projUpperTriangular 3 (ZMod p) ≤ Y₃ := by
    have h := Subgroup.map_mono (f := c'.toMonoidHom) hBx
    have heq : ((LinearFlag.projUpperTriangular 3 (ZMod p)).map c.toMonoidHom).map
        c'.toMonoidHom = LinearFlag.projUpperTriangular 3 (ZMod p) := by
      rw [Subgroup.map_map, hc'c, Subgroup.map_id]
    rwa [heq] at h
  have hdY₃ : d ∣ Nat.card Y₃ := by
    rw [hY₃, Subgroup.card_map_of_injective c'.injective]
    exact hdY
  have hmax₃ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y₃ :=
    isMaxParabolicP_top_of_borel_le (p := p) (d := d) hd hd2 hdp hB hY₃ne hdY₃
  have hmax : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y := by
    have h := (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_of_mulEquiv
      (p := p) c Y₃).mp hmax₃
    have heq : Y₃.map c.toMonoidHom = Y := by
      rw [hY₃, Subgroup.map_map, hcc', Subgroup.map_id]
    rwa [heq] at h
  exact hmax

private theorem isMaxParabolicP_top_of_sylowNormalizer_le {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1)
    {Y U : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))}
    (hU : CFSG.ABGLocalTools.IsSylowOf p U ⊤)
    (hN : Subgroup.normalizer (U : Set (LinearFlag.projectiveSL 3 (ZMod p))) ≤ Y)
    (hYne : Y ≠ ⊤) (hdY : d ∣ Nat.card Y) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y := by
  classical
  obtain ⟨T, hT⟩ := exists_sylow_eq_of_isSylowOf_top hU
  have hnorm : Subgroup.normalizer (T : Set (LinearFlag.projectiveSL 3 (ZMod p))) ≤ Y := by
    change Subgroup.normalizer ((T : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) :
      Set (LinearFlag.projectiveSL 3 (ZMod p))) ≤ Y
    rw [hT]
    exact hN
  have hmem : Subgroup.normalizer (T : Set (LinearFlag.projectiveSL 3 (ZMod p))) ∈
      LinearFlag.sylowNormalizers (LinearFlag.projectiveSL 3 (ZMod p)) p :=
    LinearFlag.mem_sylowNormalizers.mpr ⟨T, rfl⟩
  rw [LinearFlag.sylowNormalizers_eq (K := ZMod p) p (by norm_num)] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hBx : (LinearFlag.projUpperTriangular 3 (ZMod p)).map
      (MulAut.conj x).toMonoidHom ≤ Y := by
    simpa [hx] using hnorm
  exact isMaxParabolicP_top_of_borel_conj_le (p := p) (d := d) hd hd2 hdp hBx hYne hdY

theorem isMaxParabolicP_of_isPSLType_three {A : Type} [Group A] [Finite A] {p d : ℕ}
    [Fact p.Prime] (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1) {K Y : Subgroup A}
    (e : ↥K ≃* PSL(3, ZMod p)) (hYK : Y ≤ K) (hne : Y ≠ K) {U : Subgroup A}
    (hU : CFSG.ABGLocalTools.IsSylowOf p U K)
    (hN : K ⊓ Subgroup.normalizer (U : Set A) ≤ Y) (hdY : d ∣ Nat.card Y) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p K Y := by
  classical
  let e2 : ↥K ≃* LinearFlag.projectiveSL 3 (ZMod p) :=
    e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p))
  set Y₂ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)) :=
    (Y.subgroupOf K).map e2.toMonoidHom with hY₂
  set U₂ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)) :=
    (U.subgroupOf K).map e2.toMonoidHom with hU₂
  have hYne₂ : Y₂ ≠ ⊤ := by
    intro h
    apply hne
    have h' : Y.subgroupOf K = ⊤ := by
      have := congrArg (Subgroup.comap e2.toMonoidHom) h
      rwa [hY₂, Subgroup.comap_map_eq_self_of_injective e2.injective,
        Subgroup.comap_top] at this
    exact le_antisymm hYK (Subgroup.subgroupOf_eq_top.mp h')
  have hU₁ : CFSG.ABGLocalTools.IsSylowOf p (U.subgroupOf K) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hU.le, Subgroup.map_top, Subgroup.range_subtype]
    exact hU
  have hU₂s : CFSG.ABGLocalTools.IsSylowOf p U₂ ⊤ :=
    isSylowOf_map_mulEquiv e2 hU₁
  have hN₁ : Subgroup.normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) ≤
      Y.subgroupOf K := by
    rw [← Subgroup.subgroupOf_normalizer_eq hU.le, ← Subgroup.inf_subgroupOf_left]
    exact Subgroup.subgroupOf_mono K hN
  have hN₂ : Subgroup.normalizer (U₂ : Set (LinearFlag.projectiveSL 3 (ZMod p))) ≤ Y₂ := by
    rw [← Subgroup.map_equiv_normalizer_eq (U.subgroupOf K) e2]
    exact Subgroup.map_mono hN₁
  have hdY₂ : d ∣ Nat.card Y₂ := by
    rw [hY₂, Subgroup.card_map_of_injective e2.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
    exact hdY
  have hmax₂ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y₂ :=
    isMaxParabolicP_top_of_sylowNormalizer_le (p := p) (d := d) hd hd2 hdp hU₂s hN₂ hYne₂ hdY₂
  rw [CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff hYK]
  rw [CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_of_mulEquiv e2 (Y.subgroupOf K)]
  exact hmax₂


private theorem centralizer_pCore_le_of_mulEquiv {B C : Type*} [Group B] [Group C]
    [Finite B] [Finite C] {p : ℕ} {P : Subgroup B} {Q : Subgroup C} (e : ↥P ≃* ↥Q)
    (h : Subgroup.centralizer (CFSG.pCore p ↥Q : Set ↥Q) ≤ CFSG.pCore p ↥Q) :
    Subgroup.centralizer (CFSG.pCore p ↥P : Set ↥P) ≤ CFSG.pCore p ↥P := by
  have hmap : (CFSG.pCore p ↥P).map e.toMonoidHom = CFSG.pCore p ↥Q :=
    CFSG.pCore_map_iso p e
  intro x hx
  have hx' : e x ∈ Subgroup.centralizer (CFSG.pCore p ↥Q : Set ↥Q) := by
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [← hmap] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    change e z * e x = e x * e z
    rw [← map_mul, ← map_mul, hx z hz]
  have hx'' := h hx'
  rw [← hmap] at hx''
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx''
  rwa [← e.injective hzx]

private theorem radical_sub_one_sq {p d : ℕ} [Fact p.Prime]
    {g : SpecialLinearGroup (Fin 3) (ZMod p)}
    (hg : g ∈ CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d) :
    ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) *
      ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) = 0 := by
  obtain ⟨hg1, hg2⟩ := hg
  refine CFSG.QuasithinUnique.B113Lie.Lin.matrix_eq_of_mulVec ?_
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  have hmem : ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) *ᵥ v ∈
      LinearFlag.flagSpace 3 (ZMod p) d := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hg1 v
  have h2 := hg2 _ hmem
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2, sub_self]

private theorem radical_pow_eq_one {p d : ℕ} [Fact p.Prime]
    {g : SpecialLinearGroup (Fin 3) (ZMod p)}
    (hg : g ∈ CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d) : g ^ p = 1 := by
  have hNp : ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) ^ p = 0 :=
    pow_eq_zero_of_le (Fact.out : p.Prime).two_le (by
      rw [pow_two]
      exact radical_sub_one_sq hg)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow,
    show (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      1 + ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) by abel,
    add_pow_char_of_commute p (Commute.one_left _), one_pow, hNp, add_zero,
    Matrix.SpecialLinearGroup.coe_one]

private theorem isPGroup_radical {p d : ℕ} [Fact p.Prime] :
    IsPGroup p (CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using radical_pow_eq_one g.2

private theorem radical_map_le_Op {p d : ℕ} [Fact p.Prime] (hdn : d < 3) :
    (CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d).map
        (LinearFlag.proj 3 (ZMod p)) ≤
      CFSG.GH74.GLS.Bg.Op p
        (LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) := by
  refine CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.le_Op ?_ ?_ ?_
  · exact Subgroup.map_mono (CFSG.QuasithinUnique.B113Lie.Lin.radical_le_stabilizer d)
  · exact (isPGroup_radical (p := p) (d := d)).map _
  · change (LinearFlag.stabilizer (LinearFlag.flagSpace 3 (ZMod p) d)).map
      (LinearFlag.proj 3 (ZMod p)) ≤
      Subgroup.normalizer
        (((CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d).map
          (LinearFlag.proj 3 (ZMod p))) : Set (LinearFlag.projectiveSL 3 (ZMod p)))
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨q * r * q⁻¹, CFSG.QuasithinUnique.B113Lie.Lin.radical_conj_mem hq hr,
        by simp [map_mul, map_inv]⟩
    · rintro ⟨r, hr, hry⟩
      obtain ⟨y', rfl⟩ := LinearFlag.proj_surjective 3 (ZMod p) y
      refine ⟨q⁻¹ * r * q, ?_, ?_⟩
      · have := CFSG.QuasithinUnique.B113Lie.Lin.radical_conj_mem (inv_mem hq) hr
        simpa using this
      · have h1 : LinearFlag.proj 3 (ZMod p) r =
            LinearFlag.proj 3 (ZMod p) q * LinearFlag.proj 3 (ZMod p) y' *
              (LinearFlag.proj 3 (ZMod p) q)⁻¹ := hry
        calc LinearFlag.proj 3 (ZMod p) (q⁻¹ * r * q) =
            (LinearFlag.proj 3 (ZMod p) q)⁻¹ * LinearFlag.proj 3 (ZMod p) r *
              LinearFlag.proj 3 (ZMod p) q := by simp [map_mul, map_inv]
          _ = LinearFlag.proj 3 (ZMod p) y' := by rw [h1]; group

private theorem inf_centralizer_radical_map_le {p d : ℕ} [Fact p.Prime]
    (hd0 : 0 < d) (hdn : d < 3) :
    LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d) ⊓
        Subgroup.centralizer
          (((CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d).map
            (LinearFlag.proj 3 (ZMod p))) :
            Set (LinearFlag.projectiveSL 3 (ZMod p))) ≤
      (CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d).map
        (LinearFlag.proj 3 (ZMod p)) := by
  rintro x ⟨hxP, hxC⟩
  change x ∈ (LinearFlag.stabilizer (LinearFlag.flagSpace 3 (ZMod p) d)).map
    (LinearFlag.proj 3 (ZMod p)) at hxP
  obtain ⟨g, hgQ, rfl⟩ := hxP
  have hxC' := Subgroup.mem_centralizer_iff.1 hxC
  have hcomm : ∀ r ∈ CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d, g * r = r * g := by
    intro r hr
    have h1 : LinearFlag.proj 3 (ZMod p) r * LinearFlag.proj 3 (ZMod p) g =
        LinearFlag.proj 3 (ZMod p) g * LinearFlag.proj 3 (ZMod p) r :=
      hxC' _ ⟨r, hr, rfl⟩
    have hcommR : g * r * g⁻¹ * r⁻¹ ∈
        CFSG.QuasithinUnique.B113Lie.Lin.radical 3 (ZMod p) d :=
      mul_mem (CFSG.QuasithinUnique.B113Lie.Lin.radical_conj_mem hgQ hr) (inv_mem hr)
    have hsc : g * r * g⁻¹ * r⁻¹ ∈ LinearFlag.scalars 3 (ZMod p) := by
      rw [← LinearFlag.proj_eq_one_iff]
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    have h2 := CFSG.QuasithinUnique.B113Lie.Lin.scalar_mem_radical hdn hsc hcommR
    calc g * r = g * r * g⁻¹ * r⁻¹ * (r * g) := by group
      _ = r * g := by rw [h2, one_mul]
  obtain ⟨c, hcn, r, hr, hgr⟩ :=
    CFSG.QuasithinUnique.B113Lie.Lin.centralizer_radical hd0 hdn hcomm
  refine ⟨r, hr, ?_⟩
  rw [hgr, map_mul, LinearFlag.proj_eq_one_iff.2
    (LinearFlag.scalarElement_mem_scalars c hcn), one_mul]

private theorem inf_centralizer_Op_le {p d : ℕ} [Fact p.Prime] (hd0 : 0 < d) (hdn : d < 3) :
    LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d) ⊓
        Subgroup.centralizer
          (CFSG.GH74.GLS.Bg.Op p
            (LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) :
            Set (LinearFlag.projectiveSL 3 (ZMod p))) ≤
      CFSG.GH74.GLS.Bg.Op p
        (LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) := by
  have hV := radical_map_le_Op (p := p) (d := d) hdn
  exact (inf_le_inf_left _ (Subgroup.centralizer_le hV)).trans
    ((inf_centralizer_radical_map_le (p := p) (d := d) hd0 hdn).trans hV)

private theorem centralizer_pCore_le_projStabilizer_flagSpace {p d : ℕ} [Fact p.Prime]
    (hd : 1 ≤ d) (hdn : d < 3) :
    Subgroup.centralizer
        (CFSG.pCore p ↥(LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) :
          Set ↥(LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d))) ≤
      CFSG.pCore p ↥(LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d)) := by
  set P : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)) :=
    LinearFlag.projStabilizer (LinearFlag.flagSpace 3 (ZMod p) d) with hPdef
  intro x hx
  have hx' : (x : LinearFlag.projectiveSL 3 (ZMod p)) ∈
      P ⊓ Subgroup.centralizer
        (CFSG.GH74.GLS.Bg.Op p P : Set (LinearFlag.projectiveSL 3 (ZMod p))) := by
    refine ⟨x.2, ?_⟩
    have hcent : Subgroup.centralizer (CFSG.pCore p ↥P : Set ↥P) =
        (Subgroup.centralizer (CFSG.GH74.GLS.Bg.Op p P :
          Set (LinearFlag.projectiveSL 3 (ZMod p)))).subgroupOf P := by
      rw [← CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.Op_subgroupOf]
      exact CFSG.centralizer_subgroupOf_eq _ _
        (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.Op_le P)
    rw [hcent] at hx
    exact Subgroup.mem_subgroupOf.mp hx
  have hmem := inf_centralizer_Op_le (p := p) (d := d) (by omega) hdn hx'
  rw [← CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.Op_subgroupOf]
  exact Subgroup.mem_subgroupOf.mpr hmem

private theorem centralizer_pCore_le_projStabilizer {p : ℕ} [Fact p.Prime]
    {W : Submodule (ZMod p) (Fin 3 → ZMod p)} (h0 : ⊥ < W) (htop : W < ⊤) :
    Subgroup.centralizer
        (CFSG.pCore p ↥(LinearFlag.projStabilizer W) :
          Set ↥(LinearFlag.projStabilizer W)) ≤
      CFSG.pCore p ↥(LinearFlag.projStabilizer W) := by
  obtain ⟨g, hg⟩ := LinearFlag.exists_map_flagSpace_eq W
  obtain ⟨hd, hdn⟩ := LinearFlag.one_le_finrank_and_lt h0 htop
  have hconj : (LinearFlag.projStabilizer
      (LinearFlag.flagSpace 3 (ZMod p) (Module.finrank (ZMod p) W))).map
      (MulAut.conj (LinearFlag.proj 3 (ZMod p) g) :
        LinearFlag.projectiveSL 3 (ZMod p) →* LinearFlag.projectiveSL 3 (ZMod p)) =
      LinearFlag.projStabilizer W := by
    rw [LinearFlag.projStabilizer_map_conj, hg]
  let e : ↥(LinearFlag.projStabilizer W) ≃*
      ↥(LinearFlag.projStabilizer
        (LinearFlag.flagSpace 3 (ZMod p) (Module.finrank (ZMod p) W))) :=
    (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.subEquiv
      (MulAut.conj (LinearFlag.proj 3 (ZMod p) g)) hconj).symm
  exact centralizer_pCore_le_of_mulEquiv e
    (centralizer_pCore_le_projStabilizer_flagSpace (p := p) hd hdn)

theorem centralizer_pCore_le_of_isMaxParabolicP_psl_three {A : Type} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] {K Y : Subgroup A} (e : ↥K ≃* PSL(3, ZMod p))
    (hY : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p K Y) :
    Subgroup.centralizer (CFSG.pCore p ↥Y : Set ↥Y) ≤ CFSG.pCore p ↥Y := by
  classical
  have hYK : Y ≤ K := hY.1.1
  let e2 : ↥K ≃* LinearFlag.projectiveSL 3 (ZMod p) :=
    e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p))
  set Y₂ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)) :=
    (Y.subgroupOf K).map e2.toMonoidHom with hY₂
  have hmax₂ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (LinearFlag.projectiveSL 3 (ZMod p))) Y₂ := by
    have h1 : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
        (⊤ : Subgroup ↥K) (Y.subgroupOf K) :=
      (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff hYK).mp hY
    exact (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_of_mulEquiv (p := p) e2
      (Y.subgroupOf K)).mp h1
  have hgrp : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.IsMaxParabolicGrp p Y₂ :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_top_iff_isMaxParabolicGrp Y₂).mp hmax₂
  have hmem : Y₂ ∈ LinearFlag.maximalParabolics
      (LinearFlag.projectiveSL 3 (ZMod p)) p :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicGrp_iff_mem_maximalParabolics Y₂).mp hgrp
  rw [(LinearFlag.maximal_parabolics (K := ZMod p) (n := 3) p (by norm_num)).1] at hmem
  obtain ⟨W, ⟨hW0, hWtop⟩, hW⟩ := hmem
  have hY₂stat : Subgroup.centralizer (CFSG.pCore p ↥Y₂ : Set ↥Y₂) ≤ CFSG.pCore p ↥Y₂ := by
    rw [← hW]
    exact centralizer_pCore_le_projStabilizer (p := p) hW0 hWtop
  let φ : ↥Y ≃* ↥Y₂ :=
    (Subgroup.subgroupOfEquivOfLe hYK).symm.trans
      (Subgroup.equivMapOfInjective (Y.subgroupOf K) e2.toMonoidHom e2.injective)
  exact centralizer_pCore_le_of_mulEquiv φ hY₂stat

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
