module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmThreeZ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU CFSG.AGLEmbedding
  Subgroup

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem mem_zpowers_of_central_of_cyclic (hp : p.Prime) {Q : Subgroup Z}
    (hZc : IsCyclic (center Q)) {z w : Z} (hzQ : z ∈ Q) (hzo : orderOf z = p)
    (hzc : ∀ q ∈ Q, q * z = z * q) (hwQ : w ∈ Q) (hwo : orderOf w = p)
    (hwc : ∀ q ∈ Q, q * w = w * q) : w ∈ zpowers z := by
  have hwZ : (⟨w, hwQ⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g => Subtype.ext (hwc g g.2)
  have hzZ : (⟨z, hzQ⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2)
  set w₀ : center Q := ⟨⟨w, hwQ⟩, hwZ⟩
  set z₀ : center Q := ⟨⟨z, hzQ⟩, hzZ⟩
  have hord : ∀ {y : Z} (hy : y ∈ Q) (hyZ : (⟨y, hy⟩ : Q) ∈ center Q),
      orderOf (⟨⟨y, hy⟩, hyZ⟩ : center Q) = orderOf y := by
    intro y hy hyZ
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  have heq : zpowers w₀ = zpowers z₀ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hord, hord, hwo, hzo]
  have hmem : w₀ ∈ zpowers z₀ := heq ▸ mem_zpowers w₀
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hk' : z ^ k = w := by
    have := congrArg (fun y : center Q => ((y : Q) : Z)) hk
    simpa [w₀, z₀] using this
  rw [← hk']
  exact mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem w_mem_of_normal (hp : p.Prime) (hp2 : p ≠ 2) (hZ : primeComplementCore (G := Z) p = ⊥)
    (Q : Sylow p Z) (hZc : IsCyclic (center (Q : Subgroup Z))) {w : Z}
    (hwQ : w ∈ (Q : Subgroup Z)) (hwo : orderOf w = p)
    (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q) {N : Subgroup Z} [hN : N.Normal]
    (hne : N ≠ ⊥) : w ∈ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card N := by
    by_contra hnd
    apply hne
    have hle : N ≤ primeComplementCore (G := Z) p :=
      normal_coprime_le_primeComplementCore p N hN ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  have hsub : N.IsSubnormal := hN.isSubnormal
  have hinf : (Q : Subgroup Z) ⊓ N ≠ ⊥ := CFSG.Walter.sylow_inf_ne_bot_of_isSubnormal Q hsub hdvd
  have hQN : (Q : Subgroup Z) ≤ normalizer (N : Set Z) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨z, hzU, hzo, hzc⟩ := exists_central_of_inf hp Q hQN hinf
  have hw : w ∈ zpowers z :=
    mem_zpowers_of_central_of_cyclic hp hZc hzU.1 hzo hzc hwQ hwo hwc
  exact (zpowers_le.mpr hzU.2) hw

theorem exists_noncomm_of_ne (hp : p.Prime) {Q B U : Subgroup Z} (hQ : Open.pRank p Q ≤ 2)
    (hBQ : B ≤ Q) (hUQ : U ≤ Q) (hBel : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hUel : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) (hne : B ≠ U) :
    ∃ b ∈ B, ∃ u ∈ U, b * u ≠ u * b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hel, hcard⟩ := SU1.sup_isElemAbelian_card hp hBel hBc hUel hUc hne hcon
  obtain ⟨m, hm⟩ := SU1.IsElemAbelian.exists_card hp hel
  rw [hm] at hcard
  have h3 : 3 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by simpa using hcard)
  have := SU1.le_pRank hp.one_lt (sup_le hBQ hUQ : B ⊔ U ≤ Q) hel hm
  omega

theorem isSimpleGroup_of_center_eq_bot {K : Subgroup Z} (hK : IsComponentOf K ⊤)
    (hcen : Subgroup.center ↥K = ⊥) : IsSimpleGroup ↥K ∧ ∃ a b : ↥K, a * b ≠ b * a := by
  have hsimp := hK.2.2.2
  haveI : IsSimpleGroup ↥K := by
    have e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact e.symm.isSimpleGroup
  refine ⟨inferInstance, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥K)
  have hcomm : IsMulCommutative ↥K := ⟨⟨fun a b => hcon a b⟩⟩
  have h1 : commutator ↥K = ⊥ := (commutator_eq_bot_iff _).mpr hcomm
  have h2 : commutator ↥K = ⊤ := hK.2.2.1
  have hx : x ∈ commutator ↥K := by
    rw [h2]
    exact mem_top x
  rw [h1, Subgroup.mem_bot] at hx
  exact hx1 hx

theorem centralizer_eq_bot_of_unique_component [Fact p.Prime] {L : Subgroup Z}
    (hL : IsComponentOf L ⊤) (huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L)
    (hcenL : Subgroup.center ↥L = ⊥) (hZ : primeComplementCore (G := Z) p = ⊥)
    (hOp : CFSG.pCore p Z = ⊥) : centralizer (L : Set Z) = ⊥ := by
  have hlayer : CFSG.layer Z = L := layer_eq_of_unique_component hL huniq
  have hcore : CFSG.pPrimeCore p Z = ⊥ := hZ
  have hF : CFSG.generalizedFitting Z = L := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Z p hcore, hOp, hlayer, bot_sup_eq]
  have hle := CFSG.centralizer_generalizedFitting_le Z
  rw [hF] at hle
  rw [eq_bot_iff]
  intro g hg
  have hgL : g ∈ L := hle hg
  have : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hg) l l.2)
  rw [hcenL, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem catalog_trichotomy {K : Type} [Group K] (hK : IsCatalogGroup K)
    (hna : ∃ a b : K, a * b ≠ b * a) :
    P64IsAlt K ∨ (∃ r : ℕ, P64IsLie r K) ∨ ∃ s : TauCeti.SporadicName, P64IsSpor s K := by
  obtain ⟨i, ⟨e⟩⟩ := hK
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  | alternating n h => exact Or.inl ⟨n, h, ⟨e⟩⟩
  | lie idx => exact Or.inr (Or.inl ⟨idx.1.characteristic, idx, ⟨e⟩, rfl⟩)
  | sporadic s => exact Or.inr (Or.inr ⟨s, ⟨e⟩⟩)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
