module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9L2b
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open Subgroup
open scoped MatrixGroups

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GorensteinWalter CFSG.ABGLocalTools

theorem factorization_card_of_mulEquiv_psl_N {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ n) {L : Subgroup G}
    (e : L ≃* PSL2 K) :
    (Nat.card L).factorization p = n := by
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hK
  have h1 : Nat.card (Q : Subgroup (PSL2 K)) = p ^ (Nat.card (PSL2 K)).factorization p :=
    Sylow.card_eq_multiplicity Q
  rw [hQ, psl2UpperUnipotentSubgroup_card, hK] at h1
  have h2 : (Nat.card (PSL2 K)).factorization p = n :=
    (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm
  rwa [← Nat.card_congr e.toEquiv] at h2

theorem exists_mulEquiv_of_isSylowOf_psl_N {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ n)
    {L U : Subgroup G} (e : L ≃* PSL2 K) (hU : IsSylowOf p U L) :
    ∃ e' : L ≃* PSL2 K, ∀ g : L, (g : G) ∈ U ↔ e' g ∈ psl2UpperUnipotentSubgroup K := by
  set U'' : Subgroup L := (psl2UpperUnipotentSubgroup K).map e.symm.toMonoidHom with hU''
  have hU''mem : ∀ g : L, g ∈ U'' ↔ e g ∈ psl2UpperUnipotentSubgroup K := by
    intro g
    rw [hU'', Subgroup.mem_map_equiv]
    simp
  have hU''card : Nat.card U'' = p ^ n := by
    rw [hU'', Subgroup.card_map_of_injective e.symm.injective, psl2UpperUnipotentSubgroup_card,
      hK]
  have hU''syl : IsSylowOf p (U''.map L.subtype) L := by
    refine isSylowOf_of_card (map_subtype_le _) ?_
    rw [Subgroup.card_map_of_injective L.subtype_injective, hU''card,
      factorization_card_of_mulEquiv_psl_N hK e]
  obtain ⟨k, hk, hconj⟩ := hU''syl.exists_mem_conj hU
  refine ⟨(MulAut.conj (⟨k, hk⟩ : L)⁻¹).trans e, fun g => ?_⟩
  have h1 := hconj (g : G)
  have h2 : (k⁻¹ * (g : G) * k) = L.subtype ((⟨k, hk⟩ : L)⁻¹ * g * ⟨k, hk⟩) := by simp
  rw [h1, h2, Subgroup.mem_map_iff_mem L.subtype_injective, hU''mem]
  simp

theorem kFactL2UnipotentCoprimeN :
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n : ℕ), 1 ≤ n → ∀ {G : Type} [Group G] [Finite G]
      (L : Subgroup G), Nonempty (L ≃* PSL(2, GaloisField p n)) → ∀ u ∈ L, orderOf u = p →
        ∀ V : Subgroup G, V ≤ L → ¬ p ∣ Nat.card V → u ∈ normalizer (V : Set G) → V = ⊥ := by
  intro p _ hp5 n hn G _ _ L hL u huL hup V hVL hVp hN
  obtain ⟨e⟩ := hL
  have hK : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hpg : IsPGroup p (Subgroup.zpowers (⟨u, huL⟩ : L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hup, pow_one]
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  have hU : IsSylowOf p ((Q : Subgroup L).map L.subtype) L := ⟨Q, rfl⟩
  have huU : u ∈ (Q : Subgroup L).map L.subtype :=
    ⟨⟨u, huL⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl_N hK e hU
  obtain ⟨a, ha⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 ((he' ⟨u, huL⟩).1 huU)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : e' ⟨u, huL⟩ = 1 := by rw [ha]; simp
    have h2 : u = 1 := congrArg Subtype.val (e'.injective (h1.trans (map_one e').symm))
    rw [h2, orderOf_one] at hup
    exact (Fact.out : p.Prime).one_lt.ne hup
  set V' : Subgroup (PSL2 (GaloisField p n)) := (V.subgroupOf L).map e'.toMonoidHom with hV'
  have hV'mem : ∀ w : L, e' w ∈ V' ↔ (w : G) ∈ V := fun w => by
    rw [hV', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  have hcop' : ¬ p ∣ Nat.card V' := by
    have h1 : Nat.card V' = Nat.card (V.subgroupOf L) :=
      Subgroup.card_map_of_injective e'.injective
    have h2 : Nat.card (V.subgroupOf L) = Nat.card V :=
      Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv
    rw [h1, h2]
    exact hVp
  have hN' : CFSG.LocalAnalysis.RankThreeTheoremC.psl2Root a ∈ normalizer (V' : Set (PSL2 (GaloisField p n))) := by
    have hu' := Subgroup.mem_normalizer_iff.mp hN
    have hroot : CFSG.LocalAnalysis.RankThreeTheoremC.psl2Root a = e' ⟨u, huL⟩ := ha.symm
    rw [hroot, Subgroup.mem_normalizer_iff]
    intro w
    obtain ⟨w₀, rfl⟩ := e'.surjective w
    rw [← map_inv, ← map_mul, ← map_mul, hV'mem, hV'mem]
    simpa using hu' (w₀ : G)
  have hbot := CFSG.LocalAnalysis.RankThreeTheoremC.gen49l2_root_coprime hp5 ha0 hcop' hN'
  rw [eq_bot_iff]
  intro w hw
  have hwL : w ∈ L := hVL hw
  have hw' : e' ⟨w, hwL⟩ ∈ V' := (hV'mem _).2 hw
  rw [hbot, Subgroup.mem_bot] at hw'
  have h1 := e'.injective (hw'.trans (map_one e').symm)
  exact congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankFourTheoremC.P5
