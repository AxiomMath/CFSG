module

public import CFSG.GH74.KGH
public import CFSG.GH74.Constrained
public import CFSG.GH74.SmallRanks
public import CFSG.GH74.Statements

public section

namespace CFSG.GH74

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def S_walterNative : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ LieModel G .PSL 2 2 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ LieModel G .PSL 2 p f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ LieModel G .twistedG2 0 3 f) ∨
      NativeSporadic.IsSporadic G .J1

@[expose] def S_noComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
    (∀ x : G, orderOf x = 2 → layerBar x = ⊥) → GH74Conclusion G

open scoped commutatorElement in
theorem commutator_eq_top_of_nonabelian_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    have hmem : ⁅a, b⁆ ∈ commutator G := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact absurd hmem hab
  · exact h

theorem pPrimeCore_two_eq_bot_of_nonabelian_simple {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) : pPrimeCore 2 X = ⊥ := by
  rcases (inferInstance : (pPrimeCore 2 X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hcop
    have heven := even_card_of_nonabelian_simple hnonab
    obtain ⟨k, hk⟩ := heven
    rw [hk, ← two_mul] at hcop
    exact absurd (Nat.Coprime.coprime_mul_right_right hcop) (by norm_num)

theorem nonempty_quotient_commutator_mulEquiv {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Nonempty ((↥(commutator G) ⧸ pPrimeCore 2 ↥(commutator G)) ≃* G) := by
  have hC := commutator_eq_top_of_nonabelian_simple hnonab
  let e₁ : ↥(commutator G) ≃* G := (MulEquiv.subgroupCongr hC).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥(commutator G) := e₁.isSimpleGroup
  have hnonab' : ∃ a b : ↥(commutator G), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e₁.symm a, e₁.symm b, fun h => hab ?_⟩
    simpa using congrArg e₁ h
  have hcore := pPrimeCore_two_eq_bot_of_nonabelian_simple hnonab'
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans
    (QuotientGroup.quotientBot)).trans e₁⟩

theorem sylow_not_comm_of_not_comm {G : Type*} [Group G] [Finite G]
    (h : ¬ ∃ S : Sylow 2 G, IsMulCommutative (S : Subgroup G)) (S : Sylow 2 G) :
    ¬ IsMulCommutative (S : Subgroup G) :=
  fun hS => h ⟨S, hS⟩

section Cases

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem gh74Conclusion_of_abelian (hW : S_walterNative) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : 3 ≤ Open.twoRank G) (hgen : Gen4 G) (S : Sylow 2 G)
    (hS : IsMulCommutative (S : Subgroup G)) : GH74Conclusion G := by
  rcases hW G hnonab S hS with ⟨f, hf, h⟩ | ⟨p, f, hp, hp2, hf, -, -, h⟩ | ⟨f, -, -, h⟩ | h
  · have hrankf : Open.twoRank G = f := twoRank_eq_of_lieModel_PSL_two_two h
    have h4 : Open.twoRank G ≤ 4 := hgen.twoRank_le
    have hf3 : f = 3 ∨ f = 4 := by omega
    rcases hf3 with rfl | rfl
    · exact GH74Conclusion.of_eight (Or.inl h)
    · exact GH74Conclusion.of_eight (Or.inr (Or.inl h))
  · have := twoRank_le_two_of_lieModel_PSL_two_odd hp hp2 h
    omega
  · exact Or.inr (Or.inr (Or.inl ⟨f, h⟩))
  · exact GH74Conclusion.of_J1 h

theorem gh74Conclusion_of_solvable_locals
    (hI : S_partI) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : 3 ≤ Open.twoRank G) (hgen : Gen4 G)
    (hloc : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → Group.IsSolvable (normalizer (P : Set G))) :
    GH74Conclusion G := by
  have hns : ¬ Group.IsSolvable G := fun hs => by
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hs a b)
  obtain ⟨e⟩ := nonempty_quotient_commutator_mulEquiv hnonab
  have hlist := hI G hns hgen hloc
  have L := fun {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel (↥(commutator G) ⧸ pPrimeCore 2 ↥(commutator G)) t n p f) =>
    lieModel_of_mulEquiv e h
  rcases hlist with ⟨p, f, hp, hp2, hf, h⟩ | h | h | h | h | h | h | h | h
  · have := twoRank_le_two_of_lieModel_PSL_two_odd hp hp2 (L h)
    omega
  · have := twoRank_le_two_of_lieModel_PSL_three_three (L h)
    omega
  · have := twoRank_le_two_of_lieModel_PSU_three_three (L h)
    omega
  · exact GH74Conclusion.of_eight (Or.inl (L h))
  · exact GH74Conclusion.of_eight (Or.inr (Or.inl (L h)))
  · exact GH74Conclusion.of_eight (Or.inr (Or.inr (Or.inr (L h))))
  · have := twoRank_le_two_of_lieModel_PSU_three_four (L h)
    omega
  · obtain ⟨e'⟩ := h
    have := twoRank_le_two_of_alternating_seven (e.symm.trans e')
    omega
  · have := twoRank_le_two_of_M11 (isSporadic_of_mulEquiv e h)
    omega

theorem gh74Conclusion_of_constrained_centralizer (hIID : S_partII_D)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G)
    (hx : ∃ x : G, orderOf x = 2 ∧ ¬ Group.IsSolvable (centralizer ({x} : Set G)) ∧
      IsTwoConstrained (centralizer ({x} : Set G))) : GH74Conclusion G := by
  rcases hIID G inferInstance hnonab hgen hx with h | h | h
  · exact GH74Conclusion.of_J2 h
  · exact GH74Conclusion.of_J3 h
  · exact GH74Conclusion.of_M23 h

theorem gh74Conclusion_of_nonsimple_layer (hIIIB : S_partIII_B)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G)
    (hx : ∃ x : G, orderOf x = 2 ∧ sectionalTwoRank (layerBar x) = 4 ∧
      AllComponentsNonsimple x) : GH74Conclusion G := by
  rcases hIIIB G inferInstance hnonab hgen hK hx with
    ⟨p, f, hp, hp2, hf, ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, hq, h⟩ | ⟨-, hq, h⟩ | ⟨hq, h⟩ | ⟨hq, h⟩⟩ |
      h | h
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inl h⟩
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr h⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hq, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hq, h⟩))))))
  · exact GH74Conclusion.of_McL h
  · exact GH74Conclusion.of_Ly h

omit [Finite G] [IsSimpleGroup G] in
theorem gh74Conclusion_of_partII_C_outcome
    (h : LieModel G .PSL 4 3 1 ∨ LieModel G .PSU 4 3 1 ∨ LieModel G .PSp 2 3 1 ∨
      LieModel G .G2 0 3 1 ∨ LieModel G .PSL 3 2 2 ∨
      (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      NativeSporadic.IsSporadic G .M22) : GH74Conclusion G := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 1, Nat.prime_three, by norm_num, le_rfl,
      by norm_num, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 1, Nat.prime_three, by norm_num, le_rfl,
      by norm_num, h⟩))))
  · exact Or.inr (Or.inl ⟨3, 1, Nat.prime_three, by norm_num, le_rfl, h⟩)
  · exact Or.inl ⟨3, 1, Nat.prime_three, by norm_num, le_rfl, Or.inl h⟩
  · exact GH74Conclusion.of_eight (Or.inr (Or.inr (Or.inl h)))
  · exact GH74Conclusion.of_nine h
  · exact GH74Conclusion.of_M22 h

end Cases

theorem noComponent_of_parts
    (hI : S_partI) (hIIC : S_partII_C) (hIID : S_partII_D) :
    S_noComponent := by
  intro G _ _ hs hnonab hrank hgen _ hL
  by_cases hloc : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P →
      Group.IsSolvable (normalizer (P : Set G))
  · exact gh74Conclusion_of_solvable_locals hI hnonab hrank hgen hloc
  have hnsloc : ∃ H : Subgroup G, IsPLocal 2 H ∧ ¬ Group.IsSolvable H := by
    push Not at hloc
    obtain ⟨P, hP, hP2, hPs⟩ := hloc
    exact ⟨normalizer (P : Set G), ⟨P, hP, hP2, rfl⟩, hPs⟩
  have hcon : ∀ x : G, orderOf x = 2 → IsTwoConstrained (centralizer ({x} : Set G)) :=
    fun x hx => isTwoConstrained_of_layerBar_eq_bot x (hL x hx)
  by_cases hD : ∃ x : G, orderOf x = 2 ∧ ¬ Group.IsSolvable (centralizer ({x} : Set G))
  · obtain ⟨x, hx, hxs⟩ := hD
    exact gh74Conclusion_of_constrained_centralizer hIID hnonab hgen ⟨x, hx, hxs, hcon x hx⟩
  have hsolvC : ∀ x : G, orderOf x = 2 → Group.IsSolvable (centralizer ({x} : Set G)) := by
    intro x hx
    by_contra h
    exact hD ⟨x, hx, h⟩
  obtain ⟨H, hH, hHs⟩ := hnsloc
  exact gh74Conclusion_of_partII_C_outcome (hIIC G inferInstance hnonab hgen
    (fun z hz => hsolvC z hz.1) ⟨H, hH, hHs, isTwoConstrained_of_isPLocal hsolvC H hH⟩)

theorem gh74_of_branches
    (hW : S_walterNative) (hNC : S_noComponent) (hIIC : S_partII_C)
    (hIID : S_partII_D) (hIIIB : S_partIII_B) (hIV : S_partIV) (hV : S_partV)
    (hVI : S_partVI) : GH74Statement := by
  suffices key : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n → IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → 3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G by
    intro G _ _ hs hnonab hrank hgen
    exact key _ G rfl hs hnonab hrank hgen
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hs hnonab hrank hgen
  have hK : KGH G := kgh_of_smaller hgen fun X _ _ hlt hsX hnX hrX hgX =>
    ih _ (hn ▸ hlt) X rfl hsX hnX hrX hgX
  by_cases habel : ∃ S : Sylow 2 G, IsMulCommutative (S : Subgroup G)
  · obtain ⟨S, hS⟩ := habel
    exact gh74Conclusion_of_abelian hW hnonab hrank hgen S hS
  have hnab := sylow_not_comm_of_not_comm habel
  by_cases hL : ∀ x : G, orderOf x = 2 → layerBar x = ⊥
  · exact hNC G hs hnonab hrank hgen hK hL
  have hLx : ∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥ := by
    push Not at hL
    exact hL
  by_cases hD : ∃ x : G, orderOf x = 2 ∧ ¬ Group.IsSolvable (centralizer ({x} : Set G)) ∧
      IsTwoConstrained (centralizer ({x} : Set G))
  · exact gh74Conclusion_of_constrained_centralizer hIID hnonab hgen hD
  have hnD : ∀ x : G, orderOf x = 2 → Group.IsSolvable (centralizer ({x} : Set G)) ∨
      ¬ IsTwoConstrained (centralizer ({x} : Set G)) := by
    intro x hx
    by_contra hcon
    push Not at hcon
    exact hD ⟨x, hx, hcon.1, hcon.2⟩
  by_cases hB : ∃ x : G, orderOf x = 2 ∧ sectionalTwoRank (layerBar x) = 4 ∧
      AllComponentsNonsimple x
  · exact gh74Conclusion_of_nonsimple_layer hIIIB hnonab hgen hK hB
  have hR1 : R1 G := ⟨hs, hnonab, hrank, hnab, hgen, hK, hLx, hnD, hB⟩
  by_cases hIVc : (∃ z : G, IsCentralInvolution z ∧ layerBar z ≠ ⊥) ∧
      ∀ z : G, IsCentralInvolution z → AllComponentsNonsimple z
  · exact Or.inl ⟨3, 1, Nat.prime_three, by norm_num, le_rfl,
      Or.inr (hIV G hR1 hIVc.1 hIVc.2)⟩
  have hVhyp : (∀ z : G, IsCentralInvolution z → layerBar z = ⊥) ∨
      ∃ z : G, IsCentralInvolution z ∧ HasSimpleComponent z := by
    by_cases hA : ∃ z : G, IsCentralInvolution z ∧ layerBar z ≠ ⊥
    · right
      have hnB : ¬ ∀ z : G, IsCentralInvolution z → AllComponentsNonsimple z :=
        fun hB' => hIVc ⟨hA, hB'⟩
      push Not at hnB
      obtain ⟨z, hz, hzB⟩ := hnB
      unfold AllComponentsNonsimple at hzB
      push Not at hzB
      obtain ⟨K, hK, hKs⟩ := hzB
      exact ⟨z, hz, K, hK, hKs⟩
    · left
      push Not at hA
      exact hA
  have hcentral := hV G hR1 hVhyp
  by_cases hII : ∃ H : Subgroup G, IsPLocal 2 H ∧ ¬ Group.IsSolvable H ∧ IsTwoConstrained H
  · exact gh74Conclusion_of_partII_C_outcome (hIIC G inferInstance hnonab hgen hcentral hII)
  · have hloc' : ∀ H : Subgroup G, IsPLocal 2 H → Group.IsSolvable H ∨ ¬ IsTwoConstrained H := by
      intro H hH
      by_contra hcon
      push Not at hcon
      exact hII ⟨H, hH, hcon.1, hcon.2⟩
    exact GH74Conclusion.of_M12 (hVI G hR1 hcentral hloc')

theorem gh74_of_parts
    (hW : S_walterNative) (hI : S_partI) (hIIC : S_partII_C)
    (hIID : S_partII_D) (hIIIB : S_partIII_B) (hIV : S_partIV) (hV : S_partV)
    (hVI : S_partVI) : GH74Statement :=
  gh74_of_branches hW (noComponent_of_parts hI hIIC hIID) hIIC hIID hIIIB hIV hV hVI

end CFSG.GH74
