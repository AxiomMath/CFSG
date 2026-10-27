module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

variable {X : Type} [Group X] (L : Subgroup X)

@[expose] def barMap {K : Subgroup X} (hKL : K ≤ L) : ↥K →* Bar L :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion hKL)

variable {L}

theorem barMap_apply {K : Subgroup X} (hKL : K ≤ L) (k : K) :
    barMap L hKL k = (QuotientGroup.mk (Subgroup.inclusion hKL k) : Bar L) :=
  rfl

theorem mem_ker_barMap {K : Subgroup X} (hKL : K ≤ L) (k : K) :
    k ∈ (barMap L hKL).ker ↔ (k : X) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
  rw [MonoidHom.mem_ker, barMap_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨l, hl, hlk⟩
    have : Subgroup.inclusion hKL k = l := Subtype.ext hlk.symm
    rw [this]
    exact hl

theorem not_two_dvd_card_oddCore [Finite X] :
    ¬ 2 ∣ Nat.card ((pPrimeCore 2 ↥L).map L.subtype) := by
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card

theorem range_barMap_centralizer [Finite X] {g : X} (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) :
    (barMap L (inf_le_left : L ⊓ centralizer {g} ≤ L)).range =
      fixedPoints (barAction L ⟨g, hg⟩) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [mem_fixedPoints, barMap_apply, barAction_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply]
    have hc : (c : X) * g = g * c := mem_centralizer_singleton_iff.mp c.2.2
    show g * (c : X) * g⁻¹ = c
    rw [← hc, mul_inv_cancel_right]
  · intro y hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hgN : g ∈ normalizer (((pPrimeCore 2 ↥L).map L.subtype : Subgroup X) : Set X) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L) hg
    have hPN : zpowers g ≤ normalizer (((pPrimeCore 2 ↥L).map L.subtype : Subgroup X) : Set X) :=
      zpowers_le.mpr hgN
    let Fix : Subgroup X :=
      ((MulAction.stabilizer (MulAut (Bar L)) (QuotientGroup.mk l : Bar L)).comap
        (barAction L)).map (normalizer (L : Set X)).subtype
    have hgF : zpowers g ≤ Fix := by
      rw [zpowers_le]
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hy
    have hy' : ∀ u ∈ zpowers g, (l : X)⁻¹ * (u * l * u⁻¹) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hgF hu
      rw [SetLike.mem_coe, mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def,
        barAction_mk] at hv
      have h1 := QuotientGroup.eq.mp hv.symm
      refine ⟨_, h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply]
    obtain ⟨n, ⟨n', hn', rfl⟩, hcn⟩ :=
      FooteLit.exists_mul_mem_centralizer hg2 not_two_dvd_card_oddCore hPN hy'
    have hcg : (l : X) * n' * g = g * ((l : X) * n') :=
      (mem_centralizer_iff.mp hcn g (mem_zpowers g)).symm
    refine ⟨⟨(l : X) * n', L.mul_mem l.2 n'.2, mem_centralizer_singleton_iff.mpr hcg⟩, ?_⟩
    rw [barMap_apply]
    have : Subgroup.inclusion (inf_le_left : L ⊓ centralizer {g} ≤ L)
        ⟨(l : X) * n', L.mul_mem l.2 n'.2, mem_centralizer_singleton_iff.mpr hcg⟩ = l * n' :=
      Subtype.ext rfl
    rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n').mpr hn', mul_one]

theorem perfectResidual_map_subtype_eq {Y : Type*} [Group Y] {A B : Subgroup Y} (h : A = B) :
    (perfectResidual ↥A).map A.subtype = (perfectResidual ↥B).map B.subtype := by
  subst h
  rfl

theorem perfectResidual_le {C : Subgroup X} (hCL : C ≤ L) :
    (perfectResidual ↥C).map C.subtype ≤ L :=
  (map_subtype_le _).trans hCL

theorem range_barMap_perfectResidual [Finite X] {g : X} (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) :
    (barMap L (perfectResidual_le (inf_le_left : L ⊓ centralizer {g} ≤ L))).range =
      (perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))).map
        (fixedPoints (barAction L ⟨g, hg⟩)).subtype := by
  set ι := barMap L (inf_le_left : L ⊓ centralizer {g} ≤ L)
  have h1 : (barMap L (perfectResidual_le (inf_le_left : L ⊓ centralizer {g} ≤ L))).range =
      (perfectResidual ↥(L ⊓ centralizer {g})).map ι := by
    ext y
    constructor
    · rintro ⟨⟨_, c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, c, hc, rfl⟩, rfl⟩
  rw [h1, (perfect_residual_transport ι).1]
  exact perfectResidual_map_subtype_eq (range_barMap_centralizer hg hg2)

theorem exists_psl2_of_lieModel {Y : Type} [Group Y] {p f : ℕ}
    (h : Blueprint.LieModel Y .PSL 2 p f) :
    p.Prime ∧ 1 ≤ f ∧ 4 ≤ p ^ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  rcases h with ⟨-, ⟨hp, hf, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · refine ⟨hp, hf, ?_, F, inferInstance, inferInstance, hF,
      ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    by_contra hlt
    interval_cases hpf : p ^ f
    · exact h22 rfl
    · exact h23 rfl
  all_goals exact absurd h0 (by norm_num)

theorem isSimpleGroup_of_lieModel_psl2 {Y : Type} [Group Y] {p f : ℕ}
    (h : Blueprint.LieModel Y .PSL 2 p f) : IsSimpleGroup Y :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h

theorem nonabelian_of_lieModel_psl2 {Y : Type} [Group Y] {p f : ℕ}
    (h : Blueprint.LieModel Y .PSL 2 p f) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨-, -, h4, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  obtain ⟨x, y, hxy⟩ :=
    CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F (by omega) (by omega)
  exact ⟨e.symm x, e.symm y, fun hc => hxy (by simpa using congrArg e hc)⟩

theorem even_card_of_lieModel_psl2 {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Y .PSL 2 p f) : Even (Nat.card Y) := by
  obtain ⟨hp, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp hp2 hF]
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
  have hsq : ((p ^ f) ^ 2 - 1) / 2 = 2 * (k ^ 2 + k) := by
    rw [hk]
    have : (2 * k + 1) ^ 2 = 2 * (2 * (k ^ 2 + k)) + 1 := by ring
    rw [this, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
  rw [hsq]
  exact (even_two_mul _).mul_left _

theorem hasDihedralSylowTwo_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y]
    (e : Y ≃* Y') (h : GorensteinWalter.HasDihedralSylowTwo Y') :
    GorensteinWalter.HasDihedralSylowTwo Y := by
  intro S
  have hs : Function.Surjective (e : Y →* Y') := fun y => ⟨e.symm y, by simp⟩
  have hi : Function.Injective (e : Y →* Y') := fun a b hab => e.injective (by simpa using hab)
  obtain ⟨m, hm, ⟨d⟩⟩ := h (S.mapSurjective hs)
  refine ⟨m, hm, ⟨?_⟩⟩
  refine (Subgroup.equivMapOfInjective (S : Subgroup Y) (e : Y →* Y') hi).trans ?_
  refine (MulEquiv.subgroupCongr ?_).trans d
  rw [Sylow.coe_mapSurjective]

theorem hasDihedralSylowTwo_of_lieModel_psl2 {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp2 : p ≠ 2) (h : Blueprint.LieModel Y .PSL 2 p f) :
    GorensteinWalter.HasDihedralSylowTwo Y := by
  obtain ⟨hp, hf, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  exact hasDihedralSylowTwo_of_mulEquiv e
    (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
      ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩)

theorem lieModel_psl2_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {p f : ℕ}
    (h : Blueprint.LieModel Y' .PSL 2 p f) : Blueprint.LieModel Y .PSL 2 p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e.symm h

theorem eq_bot_of_odd_of_simple {Y : Type*} [Group Y] [Finite Y] {A B N : Subgroup Y}
    (hBA : B ≤ A) (hrel : B.relIndex A ≤ 2) (hB : IsSimpleGroup ↥B) (hBeven : Even (Nat.card B))
    (hNA : N ≤ A) (hN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hnorm : ((N ⊓ B).subgroupOf B).Normal := by
    refine ⟨fun x hx b => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    exact ⟨hN b (hBA b.2) x hx.1, B.mul_mem (B.mul_mem b.2 hx.2) (B.inv_mem b.2)⟩
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  ·
    have hinj : Function.Injective (fun n : ↥(N.subgroupOf A) =>
        (QuotientGroup.mk (n : ↥A) : ↥A ⧸ B.subgroupOf A)) := by
      intro n₁ n₂ h12
      rw [QuotientGroup.eq] at h12
      have hmem : ((n₁ : ↥A)⁻¹ * n₂ : ↥A) ∈ (N ⊓ B).subgroupOf A :=
        ⟨N.mul_mem (N.inv_mem n₁.2) n₂.2, h12⟩
      have h1 : ((n₁ : ↥A) : Y)⁻¹ * ((n₂ : ↥A) : Y) = 1 := by
        have hB' : (⟨((n₁ : ↥A) : Y)⁻¹ * ((n₂ : ↥A) : Y), h12⟩ : ↥B) ∈ (N ⊓ B).subgroupOf B :=
          ⟨hmem.1, h12⟩
        rw [hbot, mem_bot] at hB'
        exact congrArg Subtype.val hB'
      apply Subtype.ext
      apply Subtype.ext
      exact (inv_mul_eq_one.mp h1)
    have hle : Nat.card ↥(N.subgroupOf A) ≤ 2 :=
      (Nat.card_le_card_of_injective _ hinj).trans hrel
    have hcard : Nat.card ↥(N.subgroupOf A) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
    rw [hcard] at hle
    have h1 : Nat.card N = 1 := by
      obtain ⟨k, hk⟩ := hNodd
      omega
    exact Subgroup.eq_bot_of_card_eq N h1
  · exfalso
    have hBN : B ≤ N := fun b hb => by
      have : (⟨b, hb⟩ : ↥B) ∈ (N ⊓ B).subgroupOf B := by rw [htop]; exact mem_top _
      exact this.1
    have hdvd := Subgroup.card_dvd_of_le hBN
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hNodd hdvd)) hBeven

end CFSG.ComponentClassification.HarrisLit
