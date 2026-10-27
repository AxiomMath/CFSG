module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G]

theorem injective_conj_pow_of_not_mem_normalizer {r : ℕ} [Fact r.Prime] {t : G}
    (ht : IsPGroup r (Subgroup.zpowers t)) {L : Subgroup G}
    (hL : t ∉ Subgroup.normalizer (L : Set G)) :
    Function.Injective fun j : Fin r => L.map (MulAut.conj (t ^ (j : ℕ))).toMonoidHom := by
  have hr : r.Prime := Fact.out
  have key : ∀ k : ℕ, 0 < k → k < r → t ^ k ∉ Subgroup.normalizer (L : Set G) := by
    intro k hk0 hkr hk
    obtain ⟨a, ha⟩ := ht ⟨t, Subgroup.mem_zpowers t⟩
    have ht1 : t ^ r ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one ht1)
    have hcop : k.Coprime (orderOf t) := by
      rw [hb]
      exact Nat.Coprime.pow_right b (Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd hr).mpr (Nat.not_dvd_of_pos_of_lt hk0 hkr)))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    exact hL (hm ▸ Subgroup.pow_mem _ hk m)
  have hstep : ∀ i j : ℕ, i < j → L.map (MulAut.conj (t ^ i)).toMonoidHom =
      L.map (MulAut.conj (t ^ j)).toMonoidHom → t ^ (j - i) ∈ Subgroup.normalizer (L : Set G) := by
    intro i j hij h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hj : t ^ j = t ^ i * t ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj, map_conj_mul_eq] at h
    exact (Subgroup.map_injective (MulAut.conj (t ^ i)).injective h).symm
  intro i j hij
  simp only at hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact key (j - i) (by omega) (by omega) (hstep i j hlt hij)
  · exact key (i - j) (by omega) (by omega) (hstep j i hlt hij.symm)

theorem IsWeakSBlock.map_conj {M S L : Subgroup G} (hL : IsWeakSBlock M S L) {g : G}
    (hgM : g ∈ M) (hgS : g ∈ Subgroup.normalizer (S : Set G)) :
    IsWeakSBlock M S (L.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hL.toIsTwoPrimeComponent.map_conj hgM, fun hle => hL.not_le_normalizer ?_⟩
  intro x hx
  have hxj : (MulAut.conj g).toMonoidHom x ∈ Subgroup.normalizer (S : Set G) := hle ⟨x, hx, rfl⟩
  have hx' : x = g⁻¹ * ((MulAut.conj g).toMonoidHom x) * g := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgS) hxj) hgS

theorem coe_mem_pCoreOf_two_of_mk_eq_one {M : Subgroup G} (m : M)
    (hm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = 1) : (m : G) ∈ pCoreOf 2 M := by
  have h1 : m ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp hm
  have h2 : (m : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨_, h1, rfl⟩
  exact h2

theorem isPGroup_zpowers_of_pow_eq_one {q k : ℕ} {x : G} (hx : x ^ q ^ k = 1) :
    IsPGroup q (Subgroup.zpowers x) := by
  rintro ⟨z, hz⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem le_normalizer_blockClosure {M K L : Subgroup G} (hKM : K ≤ M) :
    K ≤ Subgroup.normalizer (blockClosure M K L : Set G) := by
  refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
  rw [blockClosure, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · exact le_sup_of_le_left (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (localGroup_le_normalizer_pCoreOf 2 M (hKM hg))).le
  · rw [Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hk => ?_
    rw [← map_conj_mul_eq]
    exact le_sup_of_le_right (le_iSup₂_of_le (g * k) (K.mul_mem hg hk) le_rfl)

theorem blockClosure_le_preimage {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : ∀ k ∈ K, barM M (L.map (MulAut.conj k).toMonoidHom) ≤ T) :
    blockClosure M K L ≤ (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype := by
  refine sup_le (fun q hq => ?_) (iSup₂_le fun k hk z hz => ?_)
  · have hqM : q ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hq
    obtain ⟨q', hq', hqq'⟩ := hq
    have : q' = ⟨q, hqM⟩ := Subtype.ext hqq'
    subst this
    refine ⟨⟨q, hqM⟩, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨q, hqM⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hq'
    show QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨q, hqM⟩ ∈ T
    rw [h1]
    exact T.one_mem
  · have hzM : z ∈ M := (hL.map_conj (hKM hk)).le hz
    exact ⟨⟨z, hzM⟩, hT k hk (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)), rfl⟩

theorem barM_le_of_le_preimage {M X : Subgroup G} {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hX : X ≤ (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) : barM M X ≤ T := by
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  obtain ⟨m, hm, hmx⟩ := hX (Subgroup.mem_subgroupOf.mp hx)
  have : m = ⟨x, hxM⟩ := Subtype.ext hmx
  subst this
  exact hm

theorem barM_blockClosure_le_normalizer [Finite G] {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) {k : G} (hk : k ∈ K) :
    barM M (blockClosure M K L) ≤
      Subgroup.normalizer (barM M (L.map (MulAut.conj k).toMonoidHom) : Set _) := by
  refine barM_le_of_le_preimage (blockClosure_le_preimage hKM hL fun k' hk' z hz => ?_)
  by_cases he : barM M (L.map (MulAut.conj k').toMonoidHom) =
      barM M (L.map (MulAut.conj k).toMonoidHom)
  · rw [he] at hz
    exact Subgroup.le_normalizer hz
  · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (hL.map_conj (hKM hk')).component (hL.map_conj (hKM hk)).component he
    exact Subgroup.centralizer_le_normalizer _
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hz)

end CFSG.AGLEmbedding
