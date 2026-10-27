module

public import CFSG.LocalAnalysis.SectionRank.Alternating
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven
public import CFSG.LocalAnalysis.SectionRank.Monster
public import CFSG.LocalAnalysis.SectionRank.Induction
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def sqtkSporadicNames : Finset TauCeti.SporadicName :=
  {.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J4, .HS, .He, .Ru}

@[expose] def SporadicThreeRankWitnesses : Prop :=
  ∀ s : TauCeti.SporadicName, s ∉ sqtkSporadicNames → s ≠ .M →
    ∃ E : Subgroup (NativeSporadic.Carrier s), IsElemAbelian 3 E ∧
      ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k

theorem not_isStronglyQuasithin_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S]
    (e : S ≃* T) {E : Subgroup T} (hE : IsElemAbelian 3 E) {k : ℕ} (hk : 3 ≤ k)
    (hcard : Nat.card E = 3 ^ k) : ¬ IsStronglyQuasithin S := by
  intro hS
  have : Finite T := Finite.of_equiv _ e.toEquiv
  have h1 := le_pRank (p := 3) (by norm_num) le_top hE hcard
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
  have := isStronglyQuasithin_iff.1 hS 3 Nat.prime_three (by norm_num)
  omega

theorem sqtk_simple_list_of_sporadic
    (hw : SporadicThreeRankWitnesses) (S : Type) [Group S]
    [Finite S] (hnonab : ∃ a b : S, a * b ≠ b * a) (hSQT : IsStronglyQuasithin S)
    (hcat : Catalog S) :
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel S .PSL 2 p f) ∨
        StatedClassicalModel S .PSL 3 p 1 ∨ StatedClassicalModel S .PSU 3 p 1)) ∨
    ((∃ f : ℕ,
      (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)) ∨
      ReeTitsModel S .Tits 2 1) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel S .PSL n 2 1) ∨
    (∃ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
        s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
      Nonempty (S ≃* NativeSporadic.Carrier s)) := by
  have hSQT' := isStronglyQuasithin_iff.1 hSQT
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hex | ⟨s, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  ·
    refine Or.inl ⟨n, hn, ?_, ⟨e⟩⟩
    by_contra h9
    push Not at h9
    have h3 := three_le_pRank_alternating h9
    rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h3
    have := hSQT' 3 Nat.prime_three (by norm_num)
    omega
  ·
    have hp : p.Prime := hm.1.1
    by_cases hp2 : p = 2
    · subst hp2
      rcases ClassicalEven.sqt_even_classical_restriction hSQT' hm with
          ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, hn, rfl⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inl ⟨hf, hm⟩⟩)))
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hm⟩)))
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩)))
      · exact Or.inr (Or.inr (Or.inl (Or.inl
          ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))⟩)))
    · refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
      rcases sqt_odd_classical_restriction hSQT' hp2 hm with
          ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨f, hf, hm⟩
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hm)
  ·
    rcases sqt_exceptional_restriction hSQT' hex with
        ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hodd, hf, hm⟩ | hm | ⟨f, hodd, hf, hm⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hodd, hf, hm⟩))))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr hm)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩))))))⟩)))
  ·
    by_cases hs : s ∈ sqtkSporadicNames
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ?_, ⟨e⟩⟩)))
      simp only [sqtkSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
      exact hs
    · exfalso
      by_cases hM : s = .M
      · subst hM
        have : Nontrivial S := by
          obtain ⟨a, b, hab⟩ := hnonab
          exact ⟨⟨a * b, b * a, hab⟩⟩
        let e' : S ≃* NativeSporadic.M := e
        have : Nontrivial NativeSporadic.M := e'.injective.nontrivial
        obtain ⟨E, hE, hcard⟩ := M_nontrivial_elementary_three_rank_four
        exact not_isStronglyQuasithin_of_mulEquiv e' hE (by norm_num) hcard hSQT
      · obtain ⟨E, hE, k, hk, hcard⟩ := hw s hs hM
        exact not_isStronglyQuasithin_of_mulEquiv e hE hk hcard hSQT

theorem layer_eq_top_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) : layer S = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isSimpleGroup hnonab

theorem sqt_catalog_of_simple_section (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    {X : Type} [Group X] [Finite X] (hX : IsSQTKCat X) (H : Subgroup X) (N : Subgroup H)
    [N.Normal] [IsSimpleGroup (H ⧸ N)] (hnonab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    IsStronglyQuasithin (H ⧸ N) ∧ Catalog (H ⧸ N) :=
  ⟨sqtk_semisimple_section_rank_of_catalog hcent hcat hX H N
    (layer_eq_top_of_isSimpleGroup hnonab), hX.2 H N inferInstance⟩

end CFSG.SectionRank
