module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3TypeA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Transfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] [Finite G] {T Q P₁ S : Subgroup G} {e u y x : G}

namespace CaseC3Top

theorem mul_self_mem_of_sylow (hs : CaseC3Top T Q P₁ S e u y x) (hperf : Group.IsPerfect G)
    (Z : Subgroup G) [Z.Normal] (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (S' : Sylow 2 G)
    (hS' : (S' : Subgroup G) = S) : x * x ∈ Q ⊔ P₁ := by
  by_contra hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := hs.partC
  obtain ⟨φ⟩ := hs.quaternion_right
  obtain ⟨v, hvQ, hvv, hyv, hvfix⟩ := hs.toCaseC3.exists_inv_conj_left
  obtain ⟨m, hm, hm1, hm2⟩ := hs.moved
  have hZW := hc.le_sup_of_mem_iff Z hZ
  have hZT : Z ≤ T := hZW.trans hc.sup_le
  have hmemT : ∀ g : G, (g : G ⧸ Z) ∈ T.map (QuotientGroup.mk' Z) ↔ g ∈ T :=
    PartC.mk_mem_map_iff_of_le Z hZT
  have hmemW : ∀ g : G, (g : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ↔ g ∈ Q ⊔ P₁ :=
    PartC.mk_mem_map_iff_of_le Z hZW
  set S'' := S'.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hS'' : (S'' : Subgroup (G ⧸ Z)) = S.map (QuotientGroup.mk' Z) := by
    rw [Sylow.coe_mapSurjective, hS']
  have hindex : Nat.Coprime 2 (S.map (QuotientGroup.mk' Z)).index := by
    rw [← hS'']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S''.not_dvd_index
  have hperf' : commutator (G ⧸ Z) = ⊤ := Group.isPerfect_def.mp inferInstance
  have huv1 := hs.toCaseC3.mk_mul_ne_one Z hZ hvQ hvv
  obtain ⟨g₀, hg₀S, hg₀T, hg4⟩ : ∃ g₀ ∈ S, g₀ ∉ T ∧ (g₀ : G ⧸ Z) ^ 4 ≠ 1 := by
    by_cases hx4 : (x : G ⧸ Z) ^ 4 = 1
    · refine ⟨m * x, S.mul_mem (hs.le_top (hc.right_le hm)) hs.mem_top, fun h' => ?_, ?_⟩
      · exact hs.not_mem_bot (by simpa using T.mul_mem (T.inv_mem (hc.right_le hm)) h')
      · rw [QuotientGroup.mk_mul, hs.mk_mul_pow_four Z hZ hA hvQ hvfix hm hm1 hm2, hx4,
          mul_one]
        exact huv1
    · exact ⟨x, hs.mem_top, hs.not_mem_bot, hx4⟩
  have hgen : CaseC3.Genuine Z ((g₀ : G ⧸ Z) ^ 4) := by
    rcases hs.mk_pow_four Z hZ hA hvQ hvv hyv hvfix hg₀S hg₀T with h1 | h1
    · exact absurd h1 hg4
    · rw [h1]
      exact hs.toCaseC3.genuine_mul Z hvQ hvv
  refine caseC3_false_of_transfer hperf' hindex (Subgroup.map_mono hs.le_top) ?_ ?_ ?_ ?_
    (CaseC3.Genuine Z) (fun a b ha => CaseC3.genuine_conj Z ha b)
    (fun t ht hg ht1 => hs.toCaseC3.mem_of_genuine Z hZ ht hg ht1)
    (Subgroup.mem_map_of_mem _ hg₀S) (fun h' => hg₀T ((hmemT g₀).mp h')) hg4 hgen
  ·
    rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs', rfl⟩
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [hmemT]
    exact (Subgroup.mem_normalizer_iff.mp (hs.top_le_normalizer hs') t).mp ht
  ·
    rintro _ ⟨a, ha, rfl⟩ haT _ ⟨b, hb, rfl⟩ hbT
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul] at haT hbT ⊢
    rw [hmemT] at haT hbT ⊢
    exact hs.mul_mem_of_not_mem ha haT hb hbT
  ·
    rintro _ ⟨t, ht, rfl⟩
    simp only [QuotientGroup.mk'_apply]
    have h2 := hc.pow_two_eq_one_of_mem_map_sup Z φ hZ
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) (hc.mul_self_mem_sup ht))
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two (t : G ⧸ Z), ← QuotientGroup.mk_mul]
    exact h2
  ·
    rintro _ ⟨s, hsS, rfl⟩ hsT
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul] at hsT ⊢
    rw [hmemT] at hsT
    rw [hmemW]
    exact hs.mul_self_not_mem_of_typeA hA hsS hsT

end CaseC3Top

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
