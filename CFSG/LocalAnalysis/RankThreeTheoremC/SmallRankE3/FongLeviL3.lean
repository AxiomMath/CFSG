module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviL3Model
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearFlag
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27G
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open scoped MatrixGroups
open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Order

open CFSG.QuasithinUnique.Setup.X7a Matrix

variable {K : Type*} [Field K]

theorem orderOf_ne_prime_of_mem_upperTriangular [Finite K] {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (hpK : ¬ p ∣ Nat.card K - 1)
    {b : SpecialLinearGroup (Fin n) K} (hb : b ∈ upperTriangular n K) : orderOf b ≠ p := by
  intro h
  obtain ⟨k, hk⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 (unitriangular n K) :=
    IsPGroup.of_card (n := k * (n * (n - 1) / 2)) (by rw [card_unitriangular, hk, pow_mul])
  let β : ↥(upperTriangular n K) := ⟨b, hb⟩
  have hβ : orderOf β = p := by rw [← h]; exact Subgroup.orderOf_mk b hb
  have hd : diagHomLin n K β = 1 := by
    funext i
    have h1 : (diagHomLin n K β i) ^ p = 1 := by
      have h' : (diagHomLin n K β) ^ p = 1 := by
        rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
      simpa using congrFun h' i
    have h2 : orderOf (diagHomLin n K β i) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3' : orderOf (diagHomLin n K β i) ∣ Nat.card K - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime p (Nat.card K - 1) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 hpK
    exact orderOf_eq_one_iff.1 ((Nat.Coprime.coprime_dvd_left h2 hcop).eq_one_of_dvd h3')
  have hmem : β ∈ (diagHomLin n K).ker := hd
  rw [ker_diagHomLin, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨j, hj⟩ := hU ⟨b, hmem⟩
  have hpow : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hpd : p ∣ 2 ^ j := by
    rw [← h]
    exact orderOf_dvd_of_pow_eq_one hpow
  have h2d : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hpd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2d)

end Order

theorem isParabolicTwo_bridge {A : Type} [Group A] [Finite A] {K K₀ : Subgroup A}
    (h : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) :
    CFSG.AGLEmbedding.IsParabolicTwo K K₀ := by
  obtain ⟨hKK, U, hU, hN⟩ := h
  refine ⟨hKK, U, ?_, ?_⟩
  · exact (CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists).2 hU
  · rw [inf_comm]
    exact hN

theorem two_le_pRank_of_dvd_pred {A : Type} [Group A] [Finite A] {K : Subgroup A} {F : Type}
    [Field F] [Finite F] (e0 : ↥K ≃* projectiveSL 3 F) {r : ℕ} [Fact r.Prime]
    (hdvd : r ∣ Nat.card F - 1) : 2 ≤ CFSG.Open.pRank r K := by
  have h2 := CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_psl3 (F := F) hdvd
  let eS : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* ↥K :=
    (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 F).trans e0.symm
  have h3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : r.Prime).one_lt eS
  have h4 : CFSG.Open.pRank r K = CFSG.Open.pRank r (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K
  omega

theorem l3_levi_of_equiv {A : Type} [Group A] [Finite A] {K K₀ : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    {z : A} (hz : orderOf z = p) (hzK₀ : z ∈ K₀) {F : Type} [Field F] [Finite F] [CharP F 2]
    (e0 : ↥K ≃* projectiveSL 3 F) :
    4 ≤ Nat.card F ∧ p ∣ Nat.card F + 1 ∧ ¬ p ∣ Nat.card F - 1 ∧ LeviSec p K₀ z ∧
      LeviHom K₀ (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hK₀K : K₀ ≤ K := hpar.1
  have hzK : z ∈ K := hK₀K hzK₀
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card F = 2 ^ k := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hpq : ¬ p ∣ Nat.card F - 1 := fun hdvd => by
    have := two_le_pRank_of_dvd_pred (K := K) e0 (r := p) hdvd
    omega
  have hcenter : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e0 x ∈ Subgroup.center (projectiveSL 3 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := Subgroup.mem_center_iff.mp hx (e0.symm y)
      have h3 := congrArg e0 h2
      simpa using h3
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)] at h1
    rw [Subgroup.mem_bot]
    exact e0.injective (by simpa using h1)
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by rw [hcenter]; simp
  let e : ↥K ⧸ Subgroup.center ↥K ≃* projectiveSL 3 F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans e0)
  let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* ↥K :=
    e0.symm.toMonoidHom.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
  have hρs : Function.Surjective ρ :=
    e0.symm.surjective.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F)
  have hρ : ∀ g, e (QuotientGroup.mk (ρ g)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F g := by
    intro g
    show e0 (QuotientGroup.quotientBot (QuotientGroup.mk (ρ g))) = _
    have h : QuotientGroup.quotientBot (QuotientGroup.mk (ρ g) : ↥K ⧸ (⊥ : Subgroup ↥K)) = ρ g :=
      rfl
    rw [h]
    simp [ρ]
  obtain ⟨σ, e', I, hσs, hσe, hI, hcomap, hIne, -⟩ :=
    CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer hodd (n := 3) (by norm_num) e hρs hρ
      (isParabolicTwo_bridge hpar)
  have hIne' : I.Nonempty := hIne (fun h => hne h)
  haveI : Finite (projectiveSL 3 F) := Finite.of_equiv _ e0.toEquiv
  have hd : ∃ d : ℕ, 1 ≤ d ∧ d < 3 ∧ I = {d} := by
    by_cases hall : ∀ i, 1 ≤ i → i < 3 → i ∈ I
    · exfalso
      have hQB := CFSG.AGLEmbedding.ToralCensus.flagStabilizer_eq_upperTriangular (K := F) hI hall
      obtain ⟨g, hg⟩ := hσs ⟨z, hzK⟩
      have hgK₀ : g ∈ (K₀.subgroupOf K).comap σ := by
        rw [Subgroup.mem_comap, hg]
        exact Subgroup.mem_subgroupOf.mpr hzK₀
      rw [hcomap, hQB] at hgK₀
      have hpg : p ∣ orderOf g := by
        have h1 := orderOf_map_dvd σ g
        rw [hg, Subgroup.orderOf_mk, hz] at h1
        exact h1
      have hord : orderOf (g ^ (orderOf g / p)) = p :=
        orderOf_pow_orderOf_div (orderOf_pos g).ne' hpg
      exact orderOf_ne_prime_of_mem_upperTriangular hp hp2 ⟨k, hk⟩ hpq
        (Subgroup.pow_mem _ hgK₀ _) hord
    · push_neg at hall
      obtain ⟨i, hi1, hi3, hiI⟩ := hall
      obtain ⟨j, hjI⟩ := hIne'
      have hj := hI j hjI
      refine ⟨j, hj.1, hj.2, ?_⟩
      ext x
      constructor
      · intro hx
        have hx' := hI x hx
        have hxi : x ≠ i := fun h => hiI (h ▸ hx)
        have hji : j ≠ i := fun h => hiI (h ▸ hjI)
        rw [Set.mem_singleton_iff]
        omega
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hjI
  obtain ⟨d, hd1, hd3, rfl⟩ := hd
  rw [flagStabilizer_singleton] at hcomap
  let θ : ↥K →* projectiveSL 3 F := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθσ : ∀ g, θ (σ g) = proj 3 F g := fun g => hσe g
  have hθinj : Function.Injective θ := by
    refine (injective_iff_map_eq_one θ).2 fun x hx => ?_
    have h1 : (QuotientGroup.mk x : ↥K ⧸ Subgroup.center ↥K) = 1 :=
      e'.injective (by simpa [θ] using hx)
    rw [QuotientGroup.eq_one_iff, hcenter, Subgroup.mem_bot] at h1
    exact h1
  have hθsurj : Function.Surjective θ :=
    e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hKP : (K₀.subgroupOf K).map θ = (stabilizer (flagSpace 3 F d)).map (proj 3 F) := by
    rw [← hcomap]
    conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective hσs (K₀.subgroupOf K)]
    rw [Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun g => hθσ g
  set P := (stabilizer (flagSpace 3 F d)).map (proj 3 F) with hP
  let z₀ : ↥K := ⟨z, hzK⟩
  have hz₀ : z₀ ∈ K₀.subgroupOf K := Subgroup.mem_subgroupOf.mpr hzK₀
  have hzP : θ z₀ ∈ P := by
    rw [← hKP]
    exact Subgroup.mem_map_of_mem θ hz₀
  have hzord : orderOf (θ z₀) = p := by
    rw [orderOf_injective θ hθinj, Subgroup.orderOf_mk, hz]
  obtain ⟨hpq1, hq4⟩ := projSL3_dvd_card_succ hp hp5 hpq hd1 hd3 hzord hzP
  refine ⟨hq4, hpq1, hpq, ?_⟩
  have hpkg := projSL3_levi hp hp5 hpq hd1 hd3 hzord hzP
  let θe : ↥K ≃* projectiveSL 3 F := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have h1s := hpkg.1.map θe.symm.toMonoidHom θe.symm.injective
  have h1h := hpkg.2.map θe.symm.toMonoidHom θe.symm.injective
  have hmap : P.map θe.symm.toMonoidHom = K₀.subgroupOf K := by
    rw [← hKP, Subgroup.map_map]
    have hid : θe.symm.toMonoidHom.comp θ = MonoidHom.id ↥K :=
      MonoidHom.ext fun x => θe.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  have hz' : θe.symm.toMonoidHom (θ z₀) = z₀ := θe.symm_apply_apply z₀
  rw [hmap, hz'] at h1s
  rw [hmap] at h1h
  have h2s := h1s.map K.subtype K.subtype_injective
  have h2h := h1h.map K.subtype K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hK₀K] at h2s h2h
  exact ⟨h2s, h2h⟩

theorem l3_levi_pkg {A : Type} [Group A] [Finite A] {K K₀ : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    {z : A} (hz : orderOf z = p) (hzK₀ : z ∈ K₀) {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (e : ↥K ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩)
    (hv' : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    LeviPkg p ⟨.A 1 q, hv'⟩ K₀ z := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
    (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
  haveI : CharP (GaloisField q.p q.exponent) 2 := ringChar.of_eq hchar
  let e0 : ↥K ≃* projectiveSL 3 (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _))
  obtain ⟨-, -, -, hsec, hhom⟩ := l3_levi_of_equiv hp hp5 hKr hpar hne hz hzK₀ e0
  refine ⟨hsec, hhom.of_mulEquiv ?_⟩
  exact ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv').trans
    ((QuotientGroup.quotientMulEquivOfEq
      (Parrott.P614.P614K136.center_SL2_eq_bot (F := GaloisField q.p q.exponent))).trans
      QuotientGroup.quotientBot)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
