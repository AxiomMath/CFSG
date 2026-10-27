module

public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.L2Rank
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

private theorem i112d_ordA_one_ne_6048 {f : ℕ} (hf : 1 ≤ f) : CFSG.Open.ordA 1 (2 ^ f) ≠ 6048 := by
  intro h
  rw [CFSG.RankThree.PartOne.S12K.ordA_one_eq hf] at h
  have hf5 : f ≤ 5 := by
    by_contra hlt
    have h64 : 2 ^ 6 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 6 * ((2 ^ 6) ^ 2 - 1) ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      Nat.mul_le_mul h64 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h64 2) 1)
    omega
  interval_cases f <;> norm_num at h

theorem i112d_conj_of_mem_conjImage {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m)
    {φ : MulAut (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F))}
    (hφ : φ ∈ CFSG.Assembly.LargeEvenMatConjImage
      (CFSG.Assembly.LargeEvenProjMk (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F)) Set.univ) :
    φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F)) := by
  obtain ⟨A, -, hA⟩ := hφ
  have hodd : Odd (Nat.card Fˣ) := by
    haveI := Fintype.ofFinite F
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h3 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    rw [Nat.odd_iff]
    omega
  obtain ⟨k, hk⟩ := hodd
  set d : Fˣ := Matrix.GeneralLinearGroup.det A with hd
  have hcc : d ^ (k + 1) * d ^ (k + 1) = d := by
    have h := pow_card_eq_one' (G := Fˣ) (x := d)
    rw [hk] at h
    calc d ^ (k + 1) * d ^ (k + 1) = d ^ (2 * k + 1) * d := by
          rw [← pow_add, ← pow_succ]; congr 1; omega
      _ = d := by rw [h, one_mul]
  set z : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) (d ^ (k + 1)) with hz
  set s : GL (Fin 2) F := z⁻¹ * A with hs
  have hdz : Matrix.GeneralLinearGroup.det z = d := by
    rw [hz, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two, hcc]
  have hs1 : s ∈ CFSG.Assembly.LargeEvenSLGroup (Fin 2) F := by
    show Matrix.GeneralLinearGroup.det s = 1
    rw [hs, map_mul, map_inv, hdz]
    exact inv_mul_cancel d
  have hAz : A = z * s := by rw [hs, mul_inv_cancel_left]
  have hconj : ∀ X : GL (Fin 2) F, A * X * A⁻¹ = s * X * s⁻¹ := by
    intro X
    have hc : ∀ Y : GL (Fin 2) F, z * Y * z⁻¹ = Y := fun Y => by
      rw [Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
    calc A * X * A⁻¹ = z * (s * X * s⁻¹) * z⁻¹ := by rw [hAz]; group
      _ = s * X * s⁻¹ := hc _
  refine ⟨CFSG.Assembly.LargeEvenProjMk _ ⟨s, hs1⟩, ?_⟩
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have hrel : ((⟨s * (h : GL (Fin 2) F) * s⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hs1 h.2)
      (Subgroup.inv_mem _ hs1)⟩ : CFSG.Assembly.LargeEvenSLGroup (Fin 2) F) : GL (Fin 2) F) =
      A * (h : GL (Fin 2) F) * A⁻¹ := (hconj _).symm
  have := hA h _ hrel
  rw [MulAut.conj_apply]
  show CFSG.Assembly.LargeEvenProjMk _ ⟨s, hs1⟩ * QuotientGroup.mk h *
    (CFSG.Assembly.LargeEvenProjMk _ ⟨s, hs1⟩)⁻¹ = φ (QuotientGroup.mk h)
  rw [show (QuotientGroup.mk h : CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup
    (Fin 2) F)) = CFSG.Assembly.LargeEvenProjMk _ h from rfl, this, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem i112d_rawDatum_A_iff (r m : ℕ) (Q : CFSG.Assembly.LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum ⟨.A, r, m⟩ Q ↔
      CFSG.Assembly.LargeEvenRecipeLinear (r + 1) (2 ^ m) Q :=
  Iff.rfl

theorem i112d_card_le_three {G : Type} [Group G] [Finite G] {X K B : Subgroup G}
    (hK : GLAPComponent 3 X K) (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)), a ∈ B →
      chevAut 3 K ⟨a, ha⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K))
    (hZ : Subgroup.center (PSimple 3 K) = ⊥) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (PSimple 3 K)) ≤ 1) :
    Nat.card B ≤ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let H : Subgroup N := B.subgroupOf N
  let ψ : H →* MulAut (PSimple 3 K) := (chevAut 3 K).comp H.subtype
  have hcardH : Nat.card H = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hmap : ψ.ker.map (N.subtype.comp H.subtype) = B ⊓ centModSubgroup 3 K := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : chevAut 3 K x.1 = 1 := hx
      have hcent : CentMod 3 K (x.1 : G) := (chevAut_eq_one_iff Nat.prime_three hK x.1.2).1 hx'
      exact ⟨Subgroup.mem_subgroupOf.1 x.2, centMod_iff.1 hcent⟩
    · rintro ⟨hgB, hgC⟩
      have hgN : g ∈ N := (mem_centModSubgroup.1 hgC).1
      refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, ?_, rfl⟩
      show chevAut 3 K ⟨g, hgN⟩ = 1
      exact (chevAut_eq_one_iff Nat.prime_three hK hgN).2 (centMod_iff.2 hgC)
  have hf : Function.Injective (N.subtype.comp H.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hkerCard : Nat.card ψ.ker = Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  set S := PSimple 3 K with hS
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have := congrArg (fun α : MulAut S => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hle : ψ.range ≤ (MulAut.conj : S →* MulAut S).range := by
    rintro _ ⟨x, rfl⟩
    exact hinner (x.1 : G) x.1.2 (Subgroup.mem_subgroupOf.1 x.2)
  let E : Subgroup S := ψ.range.comap (MulAut.conj : S →* MulAut S)
  have hEmap : E.map (MulAut.conj : S →* MulAut S) = ψ.range := Subgroup.map_comap_eq_self hle
  have hEcard : Nat.card E = Nat.card ψ.range := by
    rw [← hEmap, Subgroup.card_map_of_injective hinj]
  have hHcomm : ∀ x y : H, x * y = y * x := fun x y => by
    have hxy := congrArg Subtype.val (hB.1.is_comm.comm
      ⟨(x.1 : G), Subgroup.mem_subgroupOf.1 x.2⟩ ⟨(y.1 : G), Subgroup.mem_subgroupOf.1 y.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hxy
  have hH3 : ∀ x : H, x ^ 3 = 1 := fun x => by
    refine Subtype.ext (Subtype.ext ?_)
    exact hB.2 (x.1 : G) (Subgroup.mem_subgroupOf.1 x.2)
  have hE : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      simp only [Subgroup.coe_mul, map_mul]
      rw [← hu, ← hv, ← map_mul, ← map_mul, hHcomm]
    · apply hinj
      obtain ⟨u, hu⟩ := hx
      rw [map_pow, ← hu, ← map_pow, hH3, map_one, map_one]
  have h3 : Nat.card E ≤ 3 ^ 1 :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le Nat.prime_three hrank E hE
  have hsplitB : Nat.card B = Nat.card ψ.range * Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
    rw [← hcardH, hsplit, hkerCard]
  rw [hsplitB]
  exact Nat.mul_le_mul_right _ (by simpa [hEcard] using h3)

private theorem i112d_hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
  CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

theorem i112d_l2_label {lab : CFSG.Assembly.LargeEvenLabel}
    (hlab : CFSG.Assembly.LargeEvenInLambda2 lab) {R : Type} [Group R]
    (hm : CFSG.StandardType.MarkedModel lab R) {n : ℕ} (hn : Odd n)
    (hR : CFSG.Blueprint.LieModel R .PSL 2 2 n) : lab.tag = .A ∧ lab.rank = 1 := by
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨k, hk⟩ := hn
  obtain ⟨tag, rank, nl⟩ := lab
  have key : CFSG.StandardType.markChar ⟨tag, rank, nl⟩ = 2 →
      CFSG.StandardType.markTag ⟨tag, rank, nl⟩ = .PSL ∧
        CFSG.StandardType.markRank ⟨tag, rank, nl⟩ = 2 ∧
        CFSG.StandardType.markDeg ⟨tag, rank, nl⟩ = n := by
    intro h2
    have hm' : CFSG.Blueprint.LieModel R (CFSG.StandardType.markTag ⟨tag, rank, nl⟩)
        (CFSG.StandardType.markRank ⟨tag, rank, nl⟩) 2 (CFSG.StandardType.markDeg ⟨tag, rank, nl⟩) :=
      h2 ▸ hm
    exact CFSG.SeitzReduction.RankOne.sl2EvenTypeDet R n _ _ _ hR
      (CFSG.Blueprint.LieModel.admissible hm') hm'
  cases tag
  case A =>
    have h := key (by simp [CFSG.StandardType.markChar])
    simp only [CFSG.StandardType.markRank, CFSG.StandardType.markDeg] at h
    refine ⟨rfl, ?_⟩
    show rank = 1
    omega
  case D =>
    exfalso
    have h := key (by simp [CFSG.StandardType.markChar])
    by_cases h3 : rank = 3
    · simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank, h3] at h
    · simp [CFSG.StandardType.markTag, h3] at h
  case twD =>
    exfalso
    have h := key (by simp [CFSG.StandardType.markChar])
    by_cases h2 : rank = 2
    · simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markDeg,
        h2] at h
      omega
    · by_cases h3 : rank = 3
      · simp [CFSG.StandardType.markTag, h2, h3] at h
      · simp [CFSG.StandardType.markTag, h2, h3] at h
  case B2der =>
    exfalso
    have hm' : CFSG.Blueprint.LieModel R .PSL 2 3 2 := hm
    have h1 := (i112d_hO R .PSL 2 3 2 (CFSG.Blueprint.LieModel.admissible hm') hm').2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (3 ^ 2) = 720 from by
        decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (3 ^ 2) = 2 from by
        decide] at h1
    have hcard := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hR
    exact CFSG.SeitzReduction.RankOne.ordA_one_ne_360 hn1 (by omega)
  case G2der =>
    exfalso
    have hm' : CFSG.Blueprint.LieModel R .PSU 3 3 1 := hm
    have h1 := (i112d_hO R .PSU 3 3 1 (CFSG.Blueprint.LieModel.admissible hm') hm').2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 from by
        decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) = 1 from rfl] at h1
    have hcard := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hR
    exact i112d_ordA_one_ne_6048 hn1 (by omega)
  all_goals
    exfalso
    have h := key (by simp [CFSG.StandardType.markChar])
    simp [CFSG.StandardType.markTag] at h

theorem i112d_chevAut_inner {G : Type} [Group G] [Finite G] {K B : Subgroup G}
    (hinn : InnDiagOn 3 B K) (hL2 : IsL2TwoPowOdd (PSimple 3 K)) :
    ∀ (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)), a ∈ B →
      chevAut 3 K ⟨a, ha⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) := by
  obtain ⟨hBN, hmark⟩ := hinn
  obtain ⟨n, hn, hn1, ⟨eL⟩⟩ := hL2
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : 5 ≤ 2 ^ n :=
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hLM : CFSG.Blueprint.LieModel (PSimple 3 K) .PSL 2 2 n :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .PSL) (by decide)
      (CFSG.Models.lieModel_of_statedClassicalModel
        (CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv (PSimple 3 K) 2 n h5 eL))
  obtain ⟨-, ⟨t, r, m⟩, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hmark
  obtain ⟨R0, _, I0, F0, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, -, hMM0⟩ := hQ0
  have hMM : CFSG.StandardType.MarkedModel ⟨t, r, m⟩ (PSimple 3 K) :=
    hMM0.of_mulEquiv θ0.symm
  obtain ⟨ht, hr⟩ : t = .A ∧ r = 1 := i112d_l2_label hlab hMM hn hLM
  subst ht
  subst hr
  obtain ⟨F, hFf, hFfin, hFcard, hQ⟩ := (i112d_rawDatum_A_iff 1 m _).1 hraw
  obtain ⟨hs, hna, θ, hP, -⟩ := hQ
  intro a ha haB
  obtain ⟨φ, hφI, hφind⟩ := hP a haB
  obtain ⟨u, hu⟩ := i112d_conj_of_mem_conjImage hlab.1 hFcard hφI
  have hγ : a⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ ha
  have key : chevAut 3 K ⟨a⁻¹, hγ⟩ = MulAut.conj (θ.symm u) := by
    ext x
    obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 K x
    apply θ.injective
    have h1 := hφind (pQuotHom 3 K k) (pQuotHom 3 K (K.normalizerMonoidHom ⟨a⁻¹, hγ⟩ k))
      ⟨k, K.normalizerMonoidHom ⟨a⁻¹, hγ⟩ k, rfl, rfl, by
        show (a⁻¹ : G) * (k : G) * (a⁻¹)⁻¹ = a⁻¹ * (k : G) * a
        rw [inv_inv]⟩
    have h2 : chevAut 3 K ⟨a⁻¹, hγ⟩ (chevQuotHom 3 K k) =
        chevQuotHom 3 K (K.normalizerMonoidHom ⟨a⁻¹, hγ⟩ k) := chevAut_chevQuotHom 3 K _ k
    rw [h2]
    show θ (QuotientGroup.mk (pQuotHom 3 K (K.normalizerMonoidHom ⟨a⁻¹, hγ⟩ k))) = _
    rw [← h1, ← hu]
    simp [MulAut.conj_apply]
    rfl
  have hinv : chevAut 3 K ⟨a, ha⟩ = (chevAut 3 K ⟨a⁻¹, hγ⟩)⁻¹ := by
    rw [← map_inv]
    congr 1
    exact Subtype.ext (inv_inv a).symm
  rw [hinv, key, ← map_inv]
  exact ⟨(θ.symm u)⁻¹, rfl⟩

theorem i112d_l2_false {G : Type} [Group G] [Finite G] {X K B : Subgroup G}
    (hK : GLAPComponent 3 X K) (hB : IsElemAbelian 3 B) (hinn : InnDiagOn 3 B K)
    (hcard : 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ Nat.card B)
    (hZ : Subgroup.center (PSimple 3 K) = ⊥) (hL2 : IsL2TwoPowOdd (PSimple 3 K)) : False := by
  have hrank := CFSG.HardMathSupport.Timmesfeld.Tables.Census.pRank_three_le_one_of_isL2TwoPowOdd hL2
  have hle := i112d_card_le_three hK hB hinn.1 (i112d_chevAut_inner hinn hL2) hZ hrank
  have hpos : 0 < Nat.card ↥(B ⊓ centModSubgroup 3 K) := Nat.card_pos
  omega

end CFSG.LocalAnalysis.GLTheoremA
