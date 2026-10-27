module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPoint
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Loc
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.RankThree.PartOne.K159F.SzAbs
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (U3LineWC)

variable {G : Type} [Group G] [Finite G]

@[expose] def Sz32DataFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → ∀ T : Sylow 5 K,
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.Sz32Data K (T : Subgroup K) ∧
      ∀ f : MulAut K, (∀ x ∈ (T : Subgroup K), f x = x) →
        ∃ t ∈ (T : Subgroup K), f = MulAut.conj t

theorem sz32DataFacts_holds :
    Sz32DataFacts := by
  intro K _ _ hK T
  have hd := sz32_data K hK T
  refine ⟨hd, fun f hf => ?_⟩
  have hiso := hK.2
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hOut : (CFSG.ComponentClassification.OuterAutomorphisms.inner K).index ∣ 5 :=
    CFSG.RankThree.PartOne.K159F.card_outer_dvd_five hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  exact hd.aut hSz hsimple hOut hf

@[expose] def Sz32SecondPointFalse (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop :=
  ∀ {u : G}, IsGenericPoint p P M u → u ∉ Subgroup.zpowers x → ∀ {J : Subgroup G},
    J ≤ Subgroup.centralizer ({u} : Set G) →
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) →
    Group.IsPerfect J → rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → IsoLie Q (.suzuki 2) → False

theorem sps_mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {s : G} (hs : s ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => h a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem sps_commutator_mem {P T Z : Subgroup G} (hTZ : T ⊔ Z = P)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hZcyc : IsCyclic Z) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : a * b * a⁻¹ * b⁻¹ ∈ T := by
  have hTZc : ∀ t ∈ T, ∀ z ∈ Z, t * z = z * t := fun t ht z hz => (hZT z hz t ht).symm
  obtain ⟨t₁, ht₁, z₁, hz₁, rfl⟩ := sps_mem_sup_of_commute hTZc (hTZ ▸ ha)
  obtain ⟨t₂, ht₂, z₂, hz₂, rfl⟩ := sps_mem_sup_of_commute hTZc (hTZ ▸ hb)
  have hzz : z₁ * z₂ = z₂ * z₁ := by
    have : (⟨z₁, hz₁⟩ : Z) * ⟨z₂, hz₂⟩ = ⟨z₂, hz₂⟩ * ⟨z₁, hz₁⟩ := mul_comm' _ _
    exact congrArg Subtype.val this
  let φ : ↥T × ↥Z →* G :=
    MonoidHom.noncommCoprod T.subtype Z.subtype (fun t z => hTZc t t.2 z z.2)
  have hφ : ∀ (t : T) (z : Z), φ (t, z) = (t : G) * (z : G) := fun t z => rfl
  have key : (⟨t₁, ht₁⟩, ⟨z₁, hz₁⟩) * (⟨t₂, ht₂⟩, ⟨z₂, hz₂⟩) * (⟨t₁, ht₁⟩, ⟨z₁, hz₁⟩)⁻¹ *
      (⟨t₂, ht₂⟩, ⟨z₂, hz₂⟩)⁻¹ = ((⟨t₁, ht₁⟩ * ⟨t₂, ht₂⟩ * ⟨t₁, ht₁⟩⁻¹ * ⟨t₂, ht₂⟩⁻¹ : T), (1 : Z)) := by
    refine Prod.ext rfl ?_
    show (⟨z₁, hz₁⟩ : Z) * ⟨z₂, hz₂⟩ * ⟨z₁, hz₁⟩⁻¹ * ⟨z₂, hz₂⟩⁻¹ = 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hzz]
    group
  have h := congrArg φ key
  simp only [map_mul, map_inv] at h
  have hmem : (φ (⟨t₁, ht₁⟩ * ⟨t₂, ht₂⟩ * ⟨t₁, ht₁⟩⁻¹ * ⟨t₂, ht₂⟩⁻¹, (1 : Z))) ∈ T := by
    show ((⟨t₁, ht₁⟩ * ⟨t₂, ht₂⟩ * ⟨t₁, ht₁⟩⁻¹ * ⟨t₂, ht₂⟩⁻¹ : T) : G) * ((1 : Z) : G) ∈ T
    rw [OneMemClass.coe_one, mul_one]
    exact Subtype.prop _
  rw [← h] at hmem
  exact hmem

theorem sps_pow_mem_Z {P T Z : Subgroup G} (hTZ : T ⊔ Z = P)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTexp : ∀ t ∈ T, t ^ 5 = 1) {g : G} (hg : g ∈ P) :
    g ^ 5 ∈ Z := by
  have hTZc : ∀ t ∈ T, ∀ z ∈ Z, t * z = z * t := fun t ht z hz => (hZT z hz t ht).symm
  obtain ⟨t, ht, z, hz, rfl⟩ := sps_mem_sup_of_commute hTZc (hTZ ▸ hg)
  have hc : Commute t z := hTZc t ht z hz
  rw [hc.mul_pow, hTexp t ht, one_mul]
  exact Z.pow_mem hz 5

theorem sps_eq_one_of_mem_T {P T Z : Subgroup G} (hTZ : T ⊔ Z = P)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ0 : T ⊓ Z = ⊥) (hTexp : ∀ t ∈ T, t ^ 5 = 1)
    {g : G} (hg : g ∈ P) (hgo : orderOf g = 25) {y : G} (hy : y ∈ Subgroup.zpowers g)
    (hyT : y ∈ T) : y = 1 := by
  have hy' : y ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr hy
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy'
  have h1 : (g ^ k) ^ 5 = 1 := hTexp _ hyT
  rw [← pow_mul] at h1
  have h2 : 25 ∣ k * 5 := hgo ▸ orderOf_dvd_of_pow_eq_one h1
  obtain ⟨m, rfl⟩ : 5 ∣ k := by omega
  have h5 : g ^ 5 ∈ Z := sps_pow_mem_Z hTZ hZT hTexp hg
  have hmem : g ^ (5 * m) ∈ Z := by
    rw [pow_mul]
    exact Z.pow_mem h5 m
  have : g ^ (5 * m) ∈ T ⊓ Z := ⟨hyT, hmem⟩
  rw [hTZ0, Subgroup.mem_bot] at this
  exact this

theorem sps_commute_of_normalized {P T Z S : Subgroup G} (hTZ : T ⊔ Z = P)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ0 : T ⊓ Z = ⊥) (hTexp : ∀ t ∈ T, t ^ 5 = 1)
    (hZcyc : IsCyclic Z) (hSP : S ≤ P) {g : G} (hgS : g ∈ S) (hgo : orderOf g = 25)
    (hnorm : ∀ e ∈ S, e * g * e⁻¹ ∈ Subgroup.zpowers g) {e : G} (he : e ∈ S) :
    e * g = g * e := by
  have h1 : e * g * e⁻¹ * g⁻¹ ∈ Subgroup.zpowers g :=
    Subgroup.mul_mem _ (hnorm e he) (Subgroup.inv_mem _ (Subgroup.mem_zpowers g))
  have h2 : e * g * e⁻¹ * g⁻¹ ∈ T := sps_commutator_mem hTZ hZT hZcyc (hSP he) (hSP hgS)
  have h3 := sps_eq_one_of_mem_T hTZ hZT hTZ0 hTexp (hSP hgS) hgo h1 h2
  have h4 : e * g * e⁻¹ = g := mul_inv_eq_one.mp h3
  calc e * g = e * g * e⁻¹ * e := by group
    _ = g * e := by rw [h4]

theorem sps_conj_hom (J H : Subgroup G) (hH : H ≤ Subgroup.normalizer (J : Set G)) :
    ∃ ι : H →* MulAut J, ∀ (c : H) (j : J), ((ι c j : J) : G) = (c : G) * j * (c : G)⁻¹ := by
  let f : ∀ c : G, c ∈ Subgroup.normalizer (J : Set G) → MulAut J := fun c hc =>
    { toFun := fun j => ⟨c * j * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc j).mp j.2⟩
      invFun := fun j => ⟨c⁻¹ * j * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hc) j).mp j.2⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  refine ⟨{ toFun := fun c => f c (hH c.2), map_one' := ?_, map_mul' := ?_ }, fun c j => rfl⟩
  · ext j; simp [f]
  · intro a b; ext j; simp [f, mul_assoc]

theorem sps_descent {J Q H : Type} [Group J] [Group Q] [Group H] (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (ι : H →* MulAut J)
    (h : ∀ c j, ψ j = 1 → ψ (ι c j) = 1) :
    ∃ θ : H →* MulAut Q, ∀ c j, θ c (ψ j) = ψ (ι c j) := by
  have key : ∀ c : H, ∃ f : Q →* Q, ∀ j, f (ψ j) = ψ (ι c j) := by
    intro c
    refine ⟨ψ.liftOfSurjective hψ ⟨ψ.comp (ι c).toMonoidHom, fun j hj => h c j hj⟩, fun j => ?_⟩
    simp
  choose F hF using key
  have hmul : ∀ c d : H, ∀ q, F (c * d) q = F c (F d q) := by
    intro c d q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF, hF, hF]
    simp
  have hone : ∀ q, F 1 q = q := by
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF]
    simp
  let θ' : ∀ c : H, MulAut Q := fun c =>
    { toFun := F c
      invFun := F c⁻¹
      left_inv := fun q => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := (F c).map_mul }
  refine ⟨{ toFun := θ', map_one' := ?_, map_mul' := ?_ }, fun c j => hF c j⟩
  · ext q; exact hone q
  · intro a b; ext q; exact hmul a b q

theorem sps_exists_action {p : ℕ} {C J : Subgroup G} (hCN : C ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    ∃ ρ : ↥C →* MulAut Q, ∀ (c : ↥C) (j : ↥J) (hj : (c : G) * (j : G) * (c : G)⁻¹ ∈ J),
      ρ c (ψ j) = ψ ⟨(c : G) * (j : G) * (c : G)⁻¹, hj⟩ := by
  obtain ⟨ι, hι⟩ := sps_conj_hom J C hCN
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hιker : ∀ (c : ↥C) (j : J), ψ j = 1 → ψ (ι c j) = 1 := by
    intro c j hj
    rw [hOker] at hj ⊢
    rw [hι]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_core_conj (hCN c.2) hj
  obtain ⟨θ, hθ⟩ := sps_descent ψ hψ ι hιker
  refine ⟨θ, fun c j hj => ?_⟩
  rw [hθ]
  congr 1
  exact Subtype.ext (hι c j)

theorem sps_frattini {p : ℕ} [Fact p.Prime] {J O R M : Subgroup G} (hOJ : O ≤ J)
    (hJN : J ≤ Subgroup.normalizer (O : Set G)) (hRN : R ≤ Subgroup.normalizer (O : Set G))
    (hcop : p.Coprime (Nat.card O)) (hRp : IsPGroup p R)
    (hcomm : ∀ r ∈ R, ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ O) (hOM : O ≤ M)
    (hNR : Subgroup.normalizer (R : Set G) ≤ M) : J ≤ M := by
  set Γ : Subgroup G := J ⊔ R with hΓ
  have hJΓ : J ≤ Γ := le_sup_left
  have hRΓ : R ≤ Γ := le_sup_right
  have hOΓ : O ≤ Γ := hOJ.trans hJΓ
  have hΓN : Γ ≤ Subgroup.normalizer (O : Set G) := sup_le hJN hRN
  have hnorm : (O.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOΓ).mpr hΓN
  let π : ↥Γ →* ↥Γ ⧸ O.subgroupOf Γ := QuotientGroup.mk' (O.subgroupOf Γ)
  have hker : π.ker = O.subgroupOf Γ := QuotientGroup.ker_mk' _
  have hcop' : p.Coprime (Nat.card π.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOΓ).toEquiv]
    exact hcop
  have hR'p : IsPGroup p (R.subgroupOf Γ) := hRp.comap_subtype
  intro j hj
  have hjΓ : j ∈ Γ := hJΓ hj
  have hcent : ∀ r' ∈ R.subgroupOf Γ, π ⟨j, hjΓ⟩ * π r' = π r' * π ⟨j, hjΓ⟩ := by
    intro r' hr'
    have hr : (r' : G) ∈ R := hr'
    have h1 : (r' : G) * j * (r' : G)⁻¹ * j⁻¹ ∈ O := hcomm _ hr j hj
    have h2 : (⟨j, hjΓ⟩ * r' * ⟨j, hjΓ⟩⁻¹ * r'⁻¹ : ↥Γ) ∈ π.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      have h3 := O.inv_mem h1
      have e : ((⟨j, hjΓ⟩ * r' * ⟨j, hjΓ⟩⁻¹ * r'⁻¹ : ↥Γ) : G) =
          ((r' : G) * j * (r' : G)⁻¹ * j⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact h3
    have h4 := MonoidHom.mem_ker.mp h2
    simp only [map_mul, map_inv] at h4
    have h5 : π ⟨j, hjΓ⟩ * π r' * (π ⟨j, hjΓ⟩)⁻¹ = π r' := mul_inv_eq_one.mp h4
    calc π ⟨j, hjΓ⟩ * π r' = π ⟨j, hjΓ⟩ * π r' * (π ⟨j, hjΓ⟩)⁻¹ * π ⟨j, hjΓ⟩ := by group
      _ = π r' * π ⟨j, hjΓ⟩ := by rw [h5]
  have hnormπ : π ⟨j, hjΓ⟩ ∈ Subgroup.normalizer
      ((((R.subgroupOf Γ).map π : Subgroup (↥Γ ⧸ O.subgroupOf Γ))) : Set _) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r', hr', rfl⟩
    exact (hcent r' hr').symm
  obtain ⟨n, hn, hπn⟩ := typeII_frattini_ker π hcop' hR'p hnormπ
  have hnG : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
    have h := u3main_mem_normalizer_map hn
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRΓ] at h
  have hmem : ((n⁻¹ * ⟨j, hjΓ⟩ : ↥Γ) : G) ∈ O := by
    have : n⁻¹ * ⟨j, hjΓ⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπn, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  have hj' : j = (n : G) * ((n⁻¹ * ⟨j, hjΓ⟩ : ↥Γ) : G) := by
    simp
  rw [hj']
  exact M.mul_mem (hNR hnG) (hOM hmem)

theorem sps_le_pRank {p : ℕ} (hp : 1 < p) {E H : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEH, hE, hk⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem sps_exists_elemAbelian {p : ℕ} {Q : Subgroup G} {k : ℕ} (hp : 1 < p) (hk : 0 < k)
    (h : k ≤ CFSG.Open.pRank p Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ ∃ j : ℕ, k ≤ j ∧ Nat.card E = p ^ j := by
  set S : Set ℕ := {j | ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ j} with hS
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro n ⟨F, -, -, hF⟩
    have h1 : n < p ^ n := Nat.lt_pow_self hp
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : CFSG.Open.pRank p Q = 0 := by
      unfold CFSG.Open.pRank
      rw [← hS, hne]
      simp
    omega
  obtain ⟨E, hEQ, hEel, hEc⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEQ, hEel, _, h, hEc⟩

theorem sps_isElemAbelian_of_le {p : ℕ} {E R : Subgroup G} (hE : IsElemAbelian p E) (hRE : R ≤ E) :
    IsElemAbelian p R := by
  haveI := hE.1
  refine ⟨⟨⟨?_⟩⟩, fun x hx => hE.2 x (hRE hx)⟩
  intro a b
  apply Subtype.ext
  have h := congrArg Subtype.val (mul_comm' (⟨a, hRE a.2⟩ : E) ⟨b, hRE b.2⟩)
  exact h

theorem sps_card_le_of_not_two_le {p : ℕ} [Fact p.Prime] {E R : Subgroup G} {j : ℕ}
    (hE : IsElemAbelian p E) (hEj : Nat.card E = p ^ j) (hRE : R ≤ E)
    (h1 : ¬ 2 ≤ CFSG.Open.pRank p R) : Nat.card R ≤ p := by
  have hp : p.Prime := Fact.out
  have hdvd : Nat.card R ∣ p ^ j := hEj ▸ Subgroup.card_dvd_of_le hRE
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hi' : i ≤ CFSG.Open.pRank p R :=
    sps_le_pRank hp.one_lt le_rfl (sps_isElemAbelian_of_le hE hRE) hi
  have : i ≤ 1 := by omega
  rw [hi]
  calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
    _ = p := pow_one p

theorem sps_card_range_le {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsElemAbelian p E)
    {A : Type} [Group A] (φ : ↥E →* A) (f : A) (hφ : ∀ e, φ e ∈ Subgroup.zpowers f) :
    Nat.card φ.range ≤ p := by
  have hKle : φ.range ≤ Subgroup.zpowers f := by
    rintro _ ⟨e, rfl⟩
    exact hφ e
  have hexp : ∀ x : ↥(φ.range.subgroupOf (Subgroup.zpowers f)), x ^ p = 1 := by
    intro x
    obtain ⟨e, he⟩ := Subgroup.mem_subgroupOf.mp x.2
    have hep : e ^ p = 1 := Subtype.ext (hE.2 e e.2)
    apply Subtype.ext
    apply Subtype.ext
    show (((x : ↥(Subgroup.zpowers f)) : A)) ^ p = 1
    rw [← he, ← map_pow, hep, map_one]
  have hdvd : Nat.card (φ.range.subgroupOf (Subgroup.zpowers f)) ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd

theorem sps_card_le_of_cyclic_image {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) {A : Type} [Group A] (φ : ↥E →* A) (f : A)
    (hφ : ∀ e, φ e ∈ Subgroup.zpowers f) : Nat.card E ≤ Nat.card φ.ker * p := by
  rw [← Subgroup.card_ker_mul_card_range φ]
  exact Nat.mul_le_mul_left _ (sps_card_range_le hE φ f hφ)

theorem sps_normalizer_core {p : ℕ} (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer ((rankThreePrimeCore p J : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro o
  constructor
  · exact fun ho => CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_core_conj hc ho
  · intro ho
    have := CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_core_conj (inv_mem hc) ho
    simpa [mul_assoc] using this

theorem sps_rank_le_one (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G) {P : Sylow 5 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 5 P M) (hp : 5 ∈ rankThreeSigmaA G) {u : G}
    (hgen : IsGenericPoint 5 P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)) (hJM : ¬ J ≤ M)
    {R : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRC : R ≤ Subgroup.centralizer ({u} : Set G))
    (hcomm : ∀ r ∈ R, ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ rankThreePrimeCore 5 J) :
    ¬ 2 ≤ CFSG.Open.pRank 5 R := by
  intro h2
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hRp : IsPGroup 5 R := P.isPGroup'.to_le hRP
  have hNR : Subgroup.normalizer (R : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hRp (hRP.trans hPM) h2
  have hOM : rankThreePrimeCore 5 J ≤ M := (u3main_core_facts hS hD1 hp hM hgen hJC hCJ).1
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hcop : (5 : ℕ).Coprime (Nat.card (rankThreePrimeCore 5 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hJN : J ≤ Subgroup.normalizer ((rankThreePrimeCore 5 J : Subgroup G) : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 J).2.1
  have hRN : R ≤ Subgroup.normalizer ((rankThreePrimeCore 5 J : Subgroup G) : Set G) :=
    hRC.trans (hCJ.trans (sps_normalizer_core J))
  exact hJM (sps_frattini hOJ hJN hRN hcop hRp hcomm hOM hNR)

theorem sps_isCyclic_of_inj {A Q : Type} [Group A] [Group Q] (ψ : A →* Q) (T : Subgroup A)
    (hinj : ∀ t ∈ T, ψ t = 1 → t = 1) (hcyc : IsCyclic (T.map ψ)) : IsCyclic T := by
  have hinj' : Function.Injective (ψ.comp T.subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext (hinj a a.2 ha)
  have e1 : (ψ.comp T.subtype).range = T.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hc : IsCyclic ((ψ.comp T.subtype).range) := by
    rw [e1]
    exact hcyc
  exact (MonoidHom.ofInjective hinj').isCyclic.mpr hc

theorem sps_card_map_of_inj {A Q : Type} [Group A] [Group Q] (ψ : A →* Q) (T : Subgroup A)
    (hinj : ∀ t ∈ T, ψ t = 1 → t = 1) : Nat.card (T.map ψ) = Nat.card T := by
  have hinj' : Function.Injective (ψ.comp T.subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext (hinj a a.2 ha)
  have e1 : (ψ.comp T.subtype).range = T.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv]

theorem sps_sylow_data {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    ∃ Tsyl : Sylow p ↥J, (Tsyl : Subgroup ↥J) =
        ((P : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) ⊓ J).subgroupOf J ∧
      ∀ t ∈ (Tsyl : Subgroup ↥J), ψ t = 1 → t = 1 := by
  have hp : p.Prime := Fact.out
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hkcop : ¬ p ∣ Nat.card ψ.ker := by
    rw [hker]
    have : Nat.card ((rankThreePrimeCore p J).subgroupOf J) = Nat.card (rankThreePrimeCore p J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [this]
    exact (hp.coprime_iff_not_dvd).mp hOcop
  have hSylJ : IsSylowOf p ((P : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) ⊓ J) J :=
    hgen.2.2.1.inf_of_le_normalizer hJC hCJ
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  exact ⟨Tsyl, hTsyl, u3main_eq_one_of_ker ψ hkcop Tsyl.isPGroup'⟩

theorem sz32_second_point_false (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts) {P : Sylow 5 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 5 P M) (hp : 5 ∈ rankThreeSigmaA G) {x : G} (hxp : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    {T Z : Subgroup G} (hTZ : T ⊔ Z = (P : Subgroup G))
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ0 : T ⊓ Z = ⊥) (hTexp : ∀ t ∈ T, t ^ 5 = 1)
    (hZcyc : IsCyclic Z) (hxZ : x ∈ Z) : Sz32SecondPointFalse 5 P M x := by
  intro u hgen _hux J hJC hCJ _hperf _hlt _hmin hJM Q _ _ ψ hψ hker hiso
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  set S : Subgroup G := (P : Subgroup G) ⊓ C with hSdef
  have hSP : S ≤ (P : Subgroup G) := inf_le_left
  have hSC : S ≤ C := inf_le_right
  have hrank : CFSG.Open.pRank 5 S = 3 := hgen.2.2.2
  obtain ⟨Tsyl, hTsyl, hTinj⟩ := sps_sylow_data hgen hJC hCJ ψ hker
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Sylow 5 Q, (Tb : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    ⟨Tsyl.mapSurjective hψ, Sylow.coe_mapSurjective hψ Tsyl⟩
  obtain ⟨hD, haut⟩ := hdata Q ⟨rfl, hiso⟩ Tb
  have hTbcyc : IsCyclic ↥(Tb : Subgroup Q) := hD.isCyclic
  have hTb25 : Nat.card ↥(Tb : Subgroup Q) = 25 := hD.card_eq
  have hTsylcyc : IsCyclic ↥(Tsyl : Subgroup ↥J) := by
    refine sps_isCyclic_of_inj ψ _ hTinj ?_
    rw [← hTb]
    exact hTbcyc
  have hTsylcard : Nat.card ↥(Tsyl : Subgroup ↥J) = 25 := by
    rw [← sps_card_map_of_inj ψ _ hTinj, ← hTb]
    exact hTb25
  have hTuCyc : IsCyclic ↥(S ⊓ J) := by
    have h : IsCyclic ↥((S ⊓ J).subgroupOf J) := by
      rw [← hTsyl]
      exact hTsylcyc
    exact (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ J ≤ J)).isCyclic.mp h
  have hTuCard : Nat.card ↥(S ⊓ J) = 25 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ J ≤ J)).toEquiv,
      ← hTsyl]
    exact hTsylcard
  obtain ⟨g, hg⟩ := hTuCyc.exists_generator
  have hgo : orderOf (g : G) = 25 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hTuCard
  have hgS : (g : G) ∈ S := g.2.1
  have hTuz : ∀ y ∈ S ⊓ J, y ∈ Subgroup.zpowers (g : G) := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hnorm : ∀ e ∈ S, e * (g : G) * e⁻¹ ∈ Subgroup.zpowers (g : G) := by
    intro e he
    apply hTuz
    refine ⟨S.mul_mem (S.mul_mem he hgS) (S.inv_mem he), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hCJ (hSC he)) (g : G)).mp g.2.2
  have hcentral : ∀ e ∈ S, ∀ y ∈ S ⊓ J, e * y = y * e := by
    intro e he y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hTuz y hy)
    have hc : Commute e (g : G) :=
      sps_commute_of_normalized hTZ hZT hTZ0 hTexp hZcyc hSP hgS hgo hnorm he
    exact (hc.zpow_right k).eq
  obtain ⟨θ, hθ⟩ := sps_exists_action (p := 5) hCJ ψ hψ hker
  have hfix : ∀ e : ↥C, (e : G) ∈ S → ∀ q ∈ (Tb : Subgroup Q), θ e q = q := by
    intro e he q hq
    rw [hTb] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have htS : (t : G) ∈ S ⊓ J := by
      have h : t ∈ (S ⊓ J).subgroupOf J := hTsyl ▸ ht
      exact h
    have hj : (e : G) * (t : G) * (e : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hCJ e.2) (t : G)).mp t.2
    rw [hθ e t hj]
    congr 1
    apply Subtype.ext
    show (e : G) * (t : G) * (e : G)⁻¹ = t
    rw [hcentral e he t htS]
    group
  obtain ⟨E, hES, hEel, j, hj3, hEcard⟩ :=
    sps_exists_elemAbelian (p := 5) (Q := S) (by norm_num) (by norm_num) hrank.ge
  have hEC : E ≤ C := hES.trans hSC
  let φ : ↥E →* MulAut Q := θ.comp (Subgroup.inclusion hEC)
  have hφ1 : ∀ e : ↥E, φ e = θ ⟨(e : G), hEC e.2⟩ := fun e => rfl
  obtain ⟨b, hb⟩ := hTbcyc.exists_generator
  have hφ : ∀ e : ↥E, φ e ∈ Subgroup.zpowers (MulAut.conj (b : Q)) := by
    intro e
    obtain ⟨t, ht, hte⟩ := haut (θ ⟨(e : G), hEC e.2⟩) (hfix ⟨(e : G), hEC e.2⟩ (hES e.2))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hb ⟨t, ht⟩)
    have htk : t = (b : Q) ^ k := (congrArg Subtype.val hk).symm
    rw [hφ1, hte, htk, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hcard1 : Nat.card E ≤ Nat.card φ.ker * 5 := sps_card_le_of_cyclic_image hEel φ _ hφ
  set R : Subgroup G := φ.ker.map E.subtype with hRdef
  have hRE : R ≤ E := Subgroup.map_subtype_le _
  have hRP : R ≤ (P : Subgroup G) := hRE.trans (hES.trans hSP)
  have hRC : R ≤ C := hRE.trans hEC
  have hcomm : ∀ r ∈ R, ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ rankThreePrimeCore 5 J := by
    intro r hr j hj
    obtain ⟨r', hr', rfl⟩ := hr
    have h1 : θ ⟨(r' : G), hEC r'.2⟩ = 1 := hr'
    have hj' : (r' : G) * j * (r' : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hCJ (hEC r'.2)) j).mp hj
    have h2 := hθ ⟨(r' : G), hEC r'.2⟩ ⟨j, hj⟩ hj'
    rw [h1, MulAut.one_apply] at h2
    have h3 : ψ (⟨(r' : G) * j * (r' : G)⁻¹, hj'⟩ * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h2, mul_inv_cancel]
    have h4 : (⟨(r' : G) * j * (r' : G)⁻¹, hj'⟩ * ⟨j, hj⟩⁻¹ : ↥J) ∈ ψ.ker := h3
    rw [hker, Subgroup.mem_subgroupOf] at h4
    exact h4
  have hR1 : ¬ 2 ≤ CFSG.Open.pRank 5 R :=
    sps_rank_le_one hS hU0 hD1 hM hp hgen hJC hCJ hJM hRP hRC hcomm
  have hRcard : Nat.card R ≤ 5 := sps_card_le_of_not_two_le hEel hEcard hRE hR1
  have hkercard : Nat.card φ.ker = Nat.card R :=
    (Subgroup.card_map_of_injective E.subtype_injective).symm
  have h125 : 5 ^ 3 ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
  rw [hEcard, hkercard] at hcard1
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
