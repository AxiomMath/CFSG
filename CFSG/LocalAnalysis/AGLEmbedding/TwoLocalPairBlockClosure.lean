module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
public import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPair
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem TwoLocalPair.le_blockClosure_of_dichotomy {G : Type} [Group G] [Finite G]
    {M H : Subgroup G} (h : TwoLocalPair M H) {p : ℕ} (hp3 : p = 3) {X : Subgroup G}
    (hD : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H ∨ X ≤ Y)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hB : BlockHasThree M (pCoreOf 2 H) L) : X ≤ blockClosure M (H ⊓ M) L := by
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  set Y : Subgroup G := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hY
  have hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases hD Y inf_le_left hYn with hYN | hXY
  · exfalso
    obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := hB
    have hyK : y ∈ H ⊓ M := hKeq ▸ ⟨hL.le hyL, hyS⟩
    have hyE : y ∈ blockClosure M (H ⊓ M) L :=
      Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
        (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨y, hyL, by simp⟩))
    have hyN := hYN ⟨hyK, hyE⟩
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hlQ
      simp
    obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
    have hya : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hcop : Nat.Coprime (3 ^ a) (Nat.card (GLBPrimeCore p H)) :=
      Nat.Coprime.pow_left a (hp3 ▸ glbPrimeCore_coprime p H)
    have h1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hya) (Subgroup.orderOf_dvd_natCard _ hyN)
    exact hy1 (orderOf_eq_one_iff.mp h1)
  · exact hXY.trans inf_le_right

end CFSG.AGLEmbedding
