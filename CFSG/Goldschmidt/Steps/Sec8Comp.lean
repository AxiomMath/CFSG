module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec8LemmaA
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem exists_component_of_not_mem_fitting {M : Subgroup G} {a : G}
    (haF : a ∈ GorensteinWalter.generalizedFittingSubgroupOf M)
    (haFM : a ∉ CFSG.fittingSubgroupOf M) :
    ∃ L : Subgroup G, GorensteinWalter.IsComponentOf L M ∧
      a ∉ Subgroup.centralizer (L : Set G) := by
  have haE : a ∉ Subgroup.centralizer (GorensteinWalter.componentLayerOf M : Set G) :=
    fun h => haFM (Walter.generalizedFittingSubgroupOf_inf_centralizer_le M ⟨haF, h⟩)
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  refine haE (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
  have hle : GorensteinWalter.componentLayerOf M ≤ Subgroup.centralizer ({a} : Set G) :=
    sSup_le fun K hK k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hno K hK) k hk)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem isComponentOf_normalClosureIn {M L : Subgroup G} {a : G}
    (hL : GorensteinWalter.IsComponentOf L M) (haQ : a ∈ normalClosureIn M A)
    (haL : a ∉ Subgroup.centralizer (L : Set G)) :
    GorensteinWalter.IsComponentOf L (normalClosureIn M A) := by
  have hQM := normalClosureIn_le_self M A
  rcases Walter.isComponentOf_le_or_commutator_eq_bot hL hQM
    (le_normalizer_normalClosureIn M A) with h | h
  · exact ⟨h, Walter.isSubnormal_subgroupOf_of_le h hQM hL.2.1, hL.2.2⟩
  · exact absurd (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) haQ) haL

theorem le_of_isComponentOf (h31 : S_G31) {M L : Subgroup G} (hS : IsSStarIn M A)
    (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4)
    (hL : GorensteinWalter.IsComponentOf L (normalClosureIn M A)) : A ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbar, hpre⟩ := G73.isComponentOf_barOf hL
  obtain ⟨hSK, hK, -⟩ := (h31 G M A hS).1 _ hbar
  rw [hpre] at hSK hK
  set K := L ⊔ oddCoreOf M with hKdef
  have hLM := G73.isComponentOf_of_normalClosureIn hL
  have hLO : L ≤ Subgroup.centralizer (oddCoreOf M : Set G) := G73.le_centralizer_oddCoreOf hLM
  have hLK : L ≤ K := le_sup_left
  have hAKL : A ⊓ K ≤ L := fun x hx =>
    G73.mem_of_mem_sup_of_sq_eq_one hLO (odd_card_oddCoreOf M) hx.2 (hA.2 x hx.1)
  have hLnot : ¬ L ≤ oddCoreOf K := by
    intro h
    have : Group.IsPerfect L := Walter.isPerfect_of_isComponentOf hL
    exact Walter.ne_bot_of_isComponentOf hL (Walter.eq_bot_of_isPerfect_of_le_isSolvable h
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreOf K)))
  have hdvd : Nat.card (A ⊓ K : Subgroup G) ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases i
  · exfalso
    have hbot : A ⊓ K = ⊥ := Subgroup.card_eq_one.mp (by simpa using hcard)
    have hN : normalClosureIn K (A ⊓ K) ≤ oddCoreOf K :=
      normalClosureIn_le (oddCoreOf_le K) (le_normalizer_oddCoreOf K)
        (inf_le_left.trans (hbot ▸ bot_le))
    exact hLnot (hLK.trans (hK.le.trans (sup_le hN le_rfl)))
  · exfalso
    rw [pow_one] at hcard
    obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A ⊓ K)).mp (fun h => by
      rw [h, Subgroup.card_bot] at hcard
      exact absurd hcard (by norm_num))
    have hb1' : b ≠ 1 := fun h => hb1 (by ext; exact h)
    obtain ⟨-, -, T, hT, hBT, hcl, -⟩ := hSK
    have hiso : ∀ k ∈ K, k⁻¹ * b * k ∈ T → k⁻¹ * b * k = b := fun k hk hkT => by
      rcases mem_two hcard hbB hb1' (hcl b hbB k hk hkT) with h | h
      · exact absurd h (by simpa using conj_ne_one (n := k⁻¹) hb1')
      · exact h
    have hTb : T ≤ Subgroup.centralizer ({b} : Set G) := fun t ht => by
      have h1 := hiso t (hT.1 ht) (T.mul_mem (T.mul_mem (T.inv_mem ht) (hBT hbB)) ht)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * b = t * (t⁻¹ * b * t) := by rw [h1]
        _ = b * t := by group
    have hz : ∀ c ∈ A ⊓ K, ∀ k ∈ K, k * c * k⁻¹ * c⁻¹ ∈ oddCoreOf K := by
      intro c hc k hk
      rcases mem_two hcard hbB hb1' hc with rfl | rfl
      · simp
      · exact commutator_mem_oddCoreOf hT (hBT hbB) hTb (mul_self_eq_one hA hbB.1) hb1' hiso hk
    have hNle : normalClosureIn K (A ⊓ K) ≤ (A ⊓ K) ⊔ oddCoreOf K :=
      normalClosureIn_le (sup_le inf_le_right (oddCoreOf_le K))
        (le_normalizer_sup_oddCoreOf hz) (inf_le_left.trans le_sup_left)
    have hBb : A ⊓ K ≤ Subgroup.zpowers b := fun c hc => by
      rcases mem_two hcard hbB hb1' hc with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hLle : L ≤ Subgroup.zpowers b ⊔ oddCoreOf K :=
      hLK.trans (hK.le.trans (sup_le (hNle.trans (sup_le_sup_right hBb _)) le_sup_right))
    exact hLnot (le_of_isPerfect_of_le_zpowers_sup (le_normalizer_oddCoreOf K hbB.2) hLle
      (G73.commutator_self_of_isComponentOf hL))
  · have hAK : A ⊓ K = A :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ K ≤ A) (by rw [hcard, h4]; norm_num)
    exact hAK ▸ hAKL

theorem normalClosureIn_eq_of_isComponentOf (h31 : S_G31) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {M L : Subgroup G} (hS : IsSStarIn M A)
    (hL : GorensteinWalter.IsComponentOf L (normalClosureIn M A)) :
    normalClosureIn M A = L ∧ M ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAL := le_of_isComponentOf h31 hS hset.elem h4 hL
  have hLM := G73.isComponentOf_of_normalClosureIn hL
  have hnot := G73.not_inf_le_centralizer h31 hS hset.elem hL
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hset.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := by
    intro m hm
    rw [← Walter.map_conj_eq_iff_mem_normalizer]
    by_contra hne
    have hLm := Walter.isComponentOf_map_conj hLM (Subgroup.le_normalizer hm)
    rcases Walter.isComponentOf_eq_or_commutator_eq_bot hLM hLm with h | h
    · exact hne h.symm
    · have hLC : L.map (MulAut.conj m).toMonoidHom ≤ Subgroup.centralizer (L : Set G) :=
        Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
      have hAmL : A.map (MulAut.conj m).toMonoidHom ≤ L.map (MulAut.conj m).toMonoidHom :=
        Subgroup.map_mono hAL
      have hAmC : A ≤ Subgroup.normalizer
          ((A.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) :=
        (Subgroup.le_centralizer_iff.mp ((hAmL.trans hLC).trans
          (Subgroup.centralizer_le hAL))).trans (Subgroup.centralizer_le_normalizer _)
      have hR : IsPGroup 2 (A ⊔ A.map (MulAut.conj m).toMonoidHom : Subgroup G) :=
        IsPGroup.to_sup_of_normal_right' hA2 (hA2.map _) hAmC
      obtain ⟨Q, hRQ, hQ⟩ := stronglyClosed_of_le_pGroup S hset.closed hR le_sup_left
      have hAm : conjSub m⁻¹ A = A := by
        refine conj_eq_of_conj_le hQ ?_
        show A.map (MulAut.conj m⁻¹⁻¹).toMonoidHom ≤ Q
        rw [inv_inv]
        exact le_sup_right.trans hRQ
      apply hnot
      rintro x ⟨hxA, -⟩
      have hxm : x ∈ A.map (MulAut.conj m).toMonoidHom := by
        have : x ∈ conjSub m⁻¹ A := hAm.symm ▸ hxA
        simpa [conjSub, inv_inv] using this
      exact hLC (hAmL hxm)
  exact ⟨le_antisymm (normalClosureIn_le hLM.1 hMN (inf_le_left.trans hAL)) hL.1, hMN⟩

end CFSG.Goldschmidt.Sec8
