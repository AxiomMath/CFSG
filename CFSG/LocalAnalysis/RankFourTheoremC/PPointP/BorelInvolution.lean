module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExclude
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC Subgroup
open CFSG.UnitaryThreeRecognition.Model (rootGroup)

@[expose] def BorelInvolutionDataP (p : ℕ) (K : Type) [Group K] (T : Sylow p K) (n : ℕ) : Prop :=
  IsCoatom (normalizer ((T : Subgroup K) : Set K)) ∧
  ∃ J ∈ normalizer ((T : Subgroup K) : Set K), orderOf J = 2 ∧
    (∀ t ∈ normalizer ((T : Subgroup K) : Set K), orderOf t = 2 →
      ∃ u ∈ (T : Subgroup K), t = u * J * u⁻¹) ∧
    IsElemAbelian p ((T : Subgroup K) ⊓ centralizer ({J} : Set K)) ∧
    Nat.card ((T : Subgroup K) ⊓ centralizer ({J} : Set K) : Subgroup K) = p ^ n ∧
    ¬ centralizer ({J} : Set K) ≤ normalizer ((T : Subgroup K) : Set K)

theorem kFactUnitaryInvolution_p {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (h : Nonempty (L ≃* CatGroup d)) (U : Sylow p L) :
    ∃ J ∈ normalizer ((U : Subgroup L) : Set L), orderOf J = 2 ∧
      (∀ t ∈ normalizer ((U : Subgroup L) : Set L), orderOf t = 2 →
        ∃ u ∈ (U : Subgroup L), t = u * J * u⁻¹) ∧
      IsElemAbelian p ((U : Subgroup L) ⊓ centralizer ({J} : Set L)) ∧
      Nat.card ((U : Subgroup L) ⊓ centralizer ({J} : Set L) : Subgroup L) =
        p ^ d.1.fieldExponent ∧
      ¬ centralizer ({J} : Set L) ≤ normalizer ((U : Subgroup L) : Set L) := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : CharP K p := UnitaryModel.charP_of_card Fact.out hK
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ :=
    he'.trans hS
  have hN : (normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  obtain ⟨Jv, hJvN, hJv2, hconj, hel, hcard, hnc⟩ :=
    UnitaryModel.exists_involution_model J hJ hK hfix Fact.out hp2 hq
  have hmemN : ∀ x : L, x ∈ normalizer ((U : Subgroup L) : Set L) ↔
      e' x ∈ normalizer (rootGroup J hJ : Set _) := fun x => by
    rw [← hN]
    exact (UnitaryModel.mem_map_iff e' _ x).symm
  have hinf : ((U : Subgroup L) ⊓ centralizer ({e'.symm Jv} : Set L)).map e'.toMonoidHom =
      rootGroup J hJ ⊓ centralizer ({Jv} : Set _) := by
    rw [Subgroup.map_inf _ _ e'.toMonoidHom e'.injective, hU,
      UnitaryModel.map_centralizer_singleton, MulEquiv.apply_symm_apply]
  refine ⟨e'.symm Jv, (hmemN _).2 (by simpa using hJvN), ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hJv2
  · intro t ht ht2
    obtain ⟨u, hu, htu⟩ := hconj (e' t) ((hmemN t).1 ht) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    refine ⟨e'.symm u, ?_, ?_⟩
    · rw [← hU] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      show e'.symm (e' y) ∈ (U : Subgroup L)
      rw [MulEquiv.symm_apply_apply]
      exact hy
    · apply e'.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact htu
  · rw [← UnitaryModel.isElemAbelian_map_iff e', hinf]
    exact hel
  · rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hinf]
    exact hcard
  · intro hle
    apply hnc
    have := Subgroup.map_mono (f := e'.toMonoidHom) hle
    rw [UnitaryModel.map_centralizer_singleton, MulEquiv.apply_symm_apply, hN] at this
    exact this

theorem borelData_of_unitary_p {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex} (hU : IsUnitaryIndex p d)
    (he : Nonempty (K ≃* CatGroup d)) (T : Sylow p K) :
    BorelInvolutionDataP p K T d.1.fieldExponent :=
  ⟨kFactUnitaryBorelMaximal K p d hU he T, kFactUnitaryInvolution_p hp2 hU he T⟩

variable {X : Type} [Group X] [Finite X]

theorem exists_involution_of_borelData_p {p : ℕ} [Fact p.Prime] {Tb : Sylow p X}
    {X₀ : Subgroup X} (hred : ReducedNongeneration p X Tb X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} (hKn : K.Normal)
    (hzK : z ∉ K) {n : ℕ} (hn : 2 ≤ n) (hB : ∀ T : Sylow p K, BorelInvolutionDataP p K T n)
    {A : Subgroup X} (hATb : A ≤ Tb) (hzA : z ∈ A) (hAK : A ⊓ K = ⊥) :
    ∃ J ∈ X₀, J ^ 2 = 1 ∧ J ≠ 1 ∧ ∃ Y : Subgroup X, IsPGroup p Y ∧ Y ≤ X₀ ∧
      Y ≤ centralizer ({J} : Set X) ∧ Nat.card A * p ^ n ≤ Nat.card Y ∧
      n + 1 ≤ CFSG.Open.pRank p Y ∧ ¬ centralizer ({J} : Set X) ≤ X₀ := by
  have hp : p.Prime := Fact.out
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Tb hKn.isSubnormal
  obtain ⟨hcoat, J, hJN, hJ2, hconj, hVel, hVcard, hCB⟩ := hB T
  set U : Subgroup X := (Tb : Subgroup X) ⊓ K with hU
  set J' : X := (J : X) with hJ'
  set V : Subgroup X := ((T : Subgroup K) ⊓ centralizer ({J} : Set K)).map K.subtype
  have hVel' : IsElemAbelian p V := elementary_abelian_map p hVel K.subtype
  have hVcard' : Nat.card V = p ^ n := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hVcard]
  have hVU : V ≤ U := by
    rw [← hT]
    exact Subgroup.map_mono inf_le_left
  have hVJ : V ≤ centralizer ({J'} : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hv.2))
  have hzTb : z ∈ (Tb : Subgroup X) := hATb hzA
  have hztV : z ∉ V := fun hzV => hzK (Subgroup.mem_inf.mp (hVU hzV)).2
  have hzt3 : z ^ p = 1 := by rw [← hzp, pow_orderOf_eq_one]
  have hU2 : 2 ≤ CFSG.Open.pRank p U :=
    hn.trans (le_csSup (pRank_bddAbove p hp _) ⟨V, hVU, hVel', hVcard'⟩)
  have hU3 : 3 ≤ CFSG.Open.pRank p (U ⊔ ((Tb : Subgroup X) ⊓ centralizer (U : Set X))) := by
    have hzC : z ∈ (Tb : Subgroup X) ⊓ centralizer (U : Set X) :=
      ⟨hzTb, mem_centralizer_iff.mpr fun u _ => mem_center_iff.mp hz u⟩
    have h := succ_le_pRank_of_isElemAbelian hp hVel' hVcard'
      (mem_centralizer_iff.mpr fun v _ => mem_center_iff.mp hz v) hzt3 hztV
      (hVU.trans le_sup_left) (Subgroup.mem_sup_right hzC)
    omega
  have hNU : normalizer (U : Set X) ≤ X₀ :=
    (normalizer_le_weakCore p inf_le_left hU2 hU3).trans hred.weakCore_le
  have hTbX : (Tb : Subgroup X) ≤ X₀ :=
    Subgroup.le_normalizer.trans ((normalizer_le_weakCore_of_rank p hp _
      hred.three_le_pRank).trans hred.weakCore_le)
  have hKX : ¬ K ≤ X₀ := by
    intro hK
    apply hred.ne_top
    rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top T, hT]
    exact sup_le hNU hK
  have hBX : (normalizer ((T : Subgroup K) : Set K)).map K.subtype ≤ X₀ := by
    refine (Subgroup.le_normalizer_map K.subtype).trans ?_
    rw [hT]
    exact hNU
  have hCX : ¬ (centralizer ({J} : Set K)).map K.subtype ≤ X₀ := by
    intro hYX
    have hK : K = (normalizer ((T : Subgroup K) : Set K) ⊔
        centralizer ({J} : Set K)).map K.subtype := by
      rw [(hcoat.not_le_iff_codisjoint.mp hCB).eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    apply hKX
    rw [hK, Subgroup.map_sup]
    exact sup_le hBX hYX
  have hJ'N : J' ∈ normalizer (U : Set X) := by
    rw [← hT]
    exact Subgroup.le_normalizer_map K.subtype ⟨J, hJN, rfl⟩
  have hJ'2 : J' ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hJ2, pow_orderOf_eq_one, Subgroup.coe_one]
  have hJ'1 : J' ≠ 1 := fun h => by
    rw [show J = 1 from Subtype.ext h, orderOf_one] at hJ2
    omega
  have hUN : ∀ y ∈ (Tb : Subgroup X), y ∈ normalizer (U : Set X) := fun y hy =>
    mem_normalizer_inf_of_mem_normalizer (Subgroup.le_normalizer hy)
      ((Subgroup.normalizer_eq_top K).symm ▸ Subgroup.mem_top y)
  have hAU : A ⊓ U = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans hAK.le)
  have hYP : A ⊔ U ≤ Tb := sup_le hATb inf_le_left
  have hconj' : ∀ y ∈ A ⊔ U, ∃ u ∈ U, y * J' * y⁻¹ = u * J' * u⁻¹ := by
    intro y hy
    have hyN := hUN y (hYP hy)
    set c : K := ⟨y * J' * y⁻¹, hKn.conj_mem _ J.2 y⟩
    have hmemT : ∀ k : K, k ∈ (T : Subgroup K) ↔ (k : X) ∈ U := fun k => by
      rw [← hT]
      exact ⟨fun hk => ⟨k, hk, rfl⟩, fun ⟨k', hk', hkk'⟩ => (Subtype.ext hkk' : k' = k) ▸ hk'⟩
    have hcN : c ∈ normalizer ((T : Subgroup K) : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [hmemT, hmemT]
      exact Subgroup.mem_normalizer_iff.mp ((mul_mem (mul_mem hyN hJ'N) (inv_mem hyN))) k
    have hc2 : orderOf c = 2 := by
      rw [← Subgroup.orderOf_coe c, ← hJ2, ← Subgroup.orderOf_coe J]
      exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective J'
    obtain ⟨u, hu, hcu⟩ := hconj c hcN hc2
    exact ⟨u, (hmemT u).mp hu, by simpa [c] using congrArg Subtype.val hcu⟩
  have hcount := card_mul_card_inf_centralizer_eq (fun y hy => hUN y (hATb hy)) hconj'
  rw [hAU, Subgroup.card_bot, mul_one] at hcount
  have hUJ : p ^ n ≤ Nat.card (U ⊓ centralizer ({J'} : Set X) : Subgroup X) :=
    hVcard' ▸ Subgroup.card_le_of_le (le_inf hVU hVJ)
  refine ⟨J', hNU hJ'N, hJ'2, hJ'1, (A ⊔ U) ⊓ centralizer ({J'} : Set X),
    Tb.isPGroup'.to_le (inf_le_left.trans hYP), inf_le_left.trans (hYP.trans hTbX), inf_le_right,
    hcount ▸ Nat.mul_le_mul_left _ hUJ, ?_, ?_⟩
  · exact succ_le_pRank_of_isElemAbelian hp hVel' hVcard'
      (mem_centralizer_iff.mpr fun v _ => mem_center_iff.mp hz v) hzt3 hztV
      (le_inf (hVU.trans le_sup_right) hVJ)
      ⟨Subgroup.mem_sup_left hzA, mem_centralizer_singleton_iff.mpr
        (mem_center_iff.mp hz J').symm⟩
  · intro hCJ
    apply hCX
    rintro _ ⟨k, hk, rfl⟩
    exact hCJ (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk)))

section PPoint

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem false_of_borelData_p [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (hS : D1Global G) (hD1 : D1For G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} (hRK : PPointReduced p M x R K)
    {n : ℕ} (hn : 2 ≤ n) (hB : ∀ T : Sylow p K, BorelInvolutionDataP p K T n) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  set z : RedCent p x := QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
    ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ with hz
  have hZ := hRK.center_eq_bot hp2 h243 (h.catalogSimpleSections hS hp)
  have hzK : z ∉ K := by
    intro hzK
    have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (mem_center_iff.mp hzc k)
    rw [hZ, mem_bot] at hzZ
    have : z = 1 := congrArg Subtype.val hzZ
    rw [this, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hATb : zpowers z ≤ (R : Subgroup (RedCent p x)) :=
    zpowers_le.mpr (mem_sylow_of_mem_center hzc hzp R)
  obtain ⟨J, hJX, hJ2, hJ1, Ys, hYp, hYX, hYJ, -, hYrk, hCJ⟩ :=
    exists_involution_of_borelData_p hRK.red hzc hzp hRK.normal hzK hn hB hATb (mem_zpowers z)
      (CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem hp hzp hzK)
  exact hCJ (h.centralizer_le_redCentM_of_involution hS hD1 hloc hJX hJ2 hJ1 hYp hYX hYJ
    (by omega))

theorem false_of_unitary_p [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (hS : D1Global G) (hD1 : D1For G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} (hRK : PPointReduced p M x R K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : 2 ≤ d.1.fieldExponent)
    (e : Nonempty (K ≃* CatGroup d)) : False :=
  false_of_borelData_p hp2 h243 hS hD1 hloc h hRK hn fun T => borelData_of_unitary_p hp2 hd e T

end PPoint

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
