module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def BorelInvolutionData (K : Type) [Group K] (T : Sylow 3 K) (n : ℕ) : Prop :=
  IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K)) ∧
  ∃ J ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), orderOf J = 2 ∧
    (∀ t ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), orderOf t = 2 →
      ∃ u ∈ (T : Subgroup K), t = u * J * u⁻¹) ∧
    IsElemAbelian 3 ((T : Subgroup K) ⊓ Subgroup.centralizer ({J} : Set K)) ∧
    Nat.card ((T : Subgroup K) ⊓ Subgroup.centralizer ({J} : Set K) : Subgroup K) = 3 ^ n ∧
    ¬ Subgroup.centralizer ({J} : Set K) ≤ Subgroup.normalizer ((T : Subgroup K) : Set K)

@[expose] def KFactUnitaryInvolution : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsUnitaryIndex 3 d →
    Nonempty (L ≃* CatGroup d) → ∀ U : Sylow 3 L,
    ∃ J ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), orderOf J = 2 ∧
      (∀ t ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), orderOf t = 2 →
        ∃ u ∈ (U : Subgroup L), t = u * J * u⁻¹) ∧
      IsElemAbelian 3 ((U : Subgroup L) ⊓ Subgroup.centralizer ({J} : Set L)) ∧
      Nat.card ((U : Subgroup L) ⊓ Subgroup.centralizer ({J} : Set L) : Subgroup L) =
        3 ^ d.1.fieldExponent ∧
      ¬ Subgroup.centralizer ({J} : Set L) ≤ Subgroup.normalizer ((U : Subgroup L) : Set L)

theorem borelData_of_ree (hKR4 : KFactReeBorelMaximal) (hKJ : KFactReeInvolution) {K : Type}
    [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hRee : IsReeGTwoIndex 3 d)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (T : Sylow 3 K) :
    BorelInvolutionData K T d.1.fieldExponent :=
  ⟨hKR4 K d hRee he T, hKJ K d hRee he T⟩

theorem borelData_of_unitary (hKU6 : KFactUnitaryBorelMaximal)
    (hKUJ : KFactUnitaryInvolution) {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (hU : IsUnitaryIndex 3 d) (he : Nonempty (K ≃* CatGroup d))
    (T : Sylow 3 K) : BorelInvolutionData K T d.1.fieldExponent := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨hKU6 K 3 d hU he T, hKUJ K d hU he T⟩

variable {X : Type} [Group X] [Finite X]

theorem exists_involution_of_borelData {Tb : Sylow 3 X} {X₀ : Subgroup X}
    (hred : ReducedNongeneration 3 X Tb X₀) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = 3) {K : Subgroup X} (hKn : K.Normal) (hzK : z ∉ K) {n : ℕ}
    (hn : 2 ≤ n) (hB : ∀ T : Sylow 3 K, BorelInvolutionData K T n) {A : Subgroup X}
    (hATb : A ≤ Tb) (hzA : z ∈ A) (hAK : A ⊓ K = ⊥) :
    ∃ J ∈ X₀, J ^ 2 = 1 ∧ J ≠ 1 ∧ ∃ Y : Subgroup X, IsPGroup 3 Y ∧ Y ≤ X₀ ∧
      Y ≤ Subgroup.centralizer ({J} : Set X) ∧ Nat.card A * 3 ^ n ≤ Nat.card Y ∧
      n + 1 ≤ CFSG.Open.pRank 3 Y ∧ ¬ Subgroup.centralizer ({J} : Set X) ≤ X₀ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Tb hKn.isSubnormal
  obtain ⟨hcoat, J, hJN, hJ2, hconj, hVel, hVcard, hCB⟩ := hB T
  set U : Subgroup X := (Tb : Subgroup X) ⊓ K with hU
  set J' : X := (J : X) with hJ'
  set V : Subgroup X := ((T : Subgroup K) ⊓ Subgroup.centralizer ({J} : Set K)).map K.subtype
  have hVel' : IsElemAbelian 3 V := elementary_abelian_map 3 hVel K.subtype
  have hVcard' : Nat.card V = 3 ^ n := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hVcard]
  have hVU : V ≤ U := by
    rw [← hT]
    exact Subgroup.map_mono inf_le_left
  have hVJ : V ≤ Subgroup.centralizer ({J'} : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hv.2))
  have hzTb : z ∈ (Tb : Subgroup X) := hATb hzA
  have hztV : z ∉ V := fun hzV => hzK (Subgroup.mem_inf.mp (hVU hzV)).2
  have hzt3 : z ^ 3 = 1 := by rw [← hzp, pow_orderOf_eq_one]
  have hU2 : 2 ≤ CFSG.Open.pRank 3 U :=
    hn.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨V, hVU, hVel', hVcard'⟩)
  have hU3 : 3 ≤ CFSG.Open.pRank 3 (U ⊔ ((Tb : Subgroup X) ⊓
      Subgroup.centralizer (U : Set X))) := by
    have hzC : z ∈ (Tb : Subgroup X) ⊓ Subgroup.centralizer (U : Set X) :=
      ⟨hzTb, Subgroup.mem_centralizer_iff.mpr fun u _ => Subgroup.mem_center_iff.mp hz u⟩
    have h := succ_le_pRank_of_isElemAbelian hp hVel' hVcard'
      (Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hz v) hzt3 hztV
      (hVU.trans le_sup_left) (Subgroup.mem_sup_right hzC)
    omega
  have hNU : Subgroup.normalizer (U : Set X) ≤ X₀ :=
    (normalizer_le_weakCore 3 inf_le_left hU2 hU3).trans hred.weakCore_le
  have hTbX : (Tb : Subgroup X) ≤ X₀ :=
    Subgroup.le_normalizer.trans ((normalizer_le_weakCore_of_rank 3 hp _
      hred.three_le_pRank).trans hred.weakCore_le)
  have hKX : ¬ K ≤ X₀ := by
    intro hK
    apply hred.ne_top
    rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top T, hT]
    exact sup_le hNU hK
  have hBX : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map K.subtype ≤ X₀ := by
    refine (Subgroup.le_normalizer_map K.subtype).trans ?_
    rw [hT]
    exact hNU
  have hCX : ¬ (Subgroup.centralizer ({J} : Set K)).map K.subtype ≤ X₀ := by
    intro hYX
    have hK : K = (Subgroup.normalizer ((T : Subgroup K) : Set K) ⊔
        Subgroup.centralizer ({J} : Set K)).map K.subtype := by
      rw [(hcoat.not_le_iff_codisjoint.mp hCB).eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    apply hKX
    rw [hK, Subgroup.map_sup]
    exact sup_le hBX hYX
  have hJ'N : J' ∈ Subgroup.normalizer (U : Set X) := by
    rw [← hT]
    exact Subgroup.le_normalizer_map K.subtype ⟨J, hJN, rfl⟩
  have hJ'2 : J' ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hJ2, pow_orderOf_eq_one, Subgroup.coe_one]
  have hJ'1 : J' ≠ 1 := fun h => by
    rw [show J = 1 from Subtype.ext h, orderOf_one] at hJ2
    omega
  have hUN : ∀ y ∈ (Tb : Subgroup X), y ∈ Subgroup.normalizer (U : Set X) := fun y hy =>
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
    have hcN : c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
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
  have hUJ : 3 ^ n ≤ Nat.card (U ⊓ Subgroup.centralizer ({J'} : Set X) : Subgroup X) :=
    hVcard' ▸ Subgroup.card_le_of_le (le_inf hVU hVJ)
  refine ⟨J', hNU hJ'N, hJ'2, hJ'1, (A ⊔ U) ⊓ Subgroup.centralizer ({J'} : Set X),
    Tb.isPGroup'.to_le (inf_le_left.trans hYP), inf_le_left.trans (hYP.trans hTbX), inf_le_right,
    hcount ▸ Nat.mul_le_mul_left _ hUJ, ?_, ?_⟩
  · exact succ_le_pRank_of_isElemAbelian hp hVel' hVcard'
      (Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hz v) hzt3 hztV
      (le_inf (hVU.trans le_sup_right) hVJ)
      ⟨Subgroup.mem_sup_left hzA, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hz J').symm⟩
  · intro hCJ
    apply hCX
    rintro _ ⟨k, hk, rfl⟩
    exact hCJ (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)))

end CFSG.AGLEmbedding
