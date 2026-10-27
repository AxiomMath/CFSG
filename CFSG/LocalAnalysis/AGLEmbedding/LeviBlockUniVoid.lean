module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedASetup
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFivesAt
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise


@[expose] def IdxTwistedAExcept (c : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q => q.p = 2 ∧ q.card ≠ c
  | _ => False

theorem idxTwistedA_of_except {c : ℕ} {d : TauCeti.LieTypeIndex} (hd : IdxTwistedAExcept c d) :
    IdxTwistedA d := by
  cases d with
  | twistedA r₀ q => exact hd.1
  | _ => exact hd.elim

theorem two_pow_ne_of_except {c f : ℕ} {d : TauCeti.LieTypeIndex} (hd : IdxTwistedAExcept c d)
    (hq : ∀ r₀ q, d = .twistedA r₀ q → q.card = 2 ^ f) : 2 ^ f ≠ c := by
  cases d with
  | twistedA r₀ q => exact (hq r₀ q rfl) ▸ hd.2
  | _ => exact hd.elim

@[expose] def IdxTwistedAAt (c : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q => q.p = 2 ∧ q.card = c
  | _ => False

theorem isLieOf_twistedA_cases (c : ℕ) {X : Type} [Group X] (hX : IsLieOf IdxTwistedA X) :
    IsLieOf (IdxTwistedAExcept c) X ∨ IsLieOf (IdxTwistedAAt c) X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := hX
  cases d with
  | twistedA r₀ q =>
    by_cases hq : q.card = c
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, hq⟩, he⟩
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, hq⟩, he⟩
  | _ => exact hd.elim

theorem exists_uniFlag_of_compParab {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (f t s ε : ℕ) (h : UnitaryFieldData 2 f K)
      (ρ : hypSU h (t + s) ε →* ↥L) (I : Finset ℕ) (g : hypSU h (t + s) ε),
      ε ≤ 1 ∧ LeviBlock.IsTopCut I t ∧ (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f) ∧
      Function.Surjective ρ ∧ ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
        ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i := by
  obtain ⟨K, _, _, f, h, r, ε, ρ, hr, hε, hq, hρ, -⟩ :=
    ToralCensus.exists_hypCover hCP.comp hCP.odd d hd e
  obtain ⟨T, hT⟩ := ToralCensus.exists_sylow_normalizer_le_comap_of_surjective hρ hCP.parab
  obtain ⟨g, I₀, hI₀, hJ⟩ := ToralCensus.exists_eq_stab_hypFlag_of_normalizer_le h hr hε T _ hT
  have hne := ToralCensus.comap_ne_top_of_ne hρ hCP.parab.1 hCP.ne_top
  have hfin : I₀.Finite := (Set.finite_Icc 1 r).subset hI₀
  obtain ⟨I, rfl⟩ : ∃ I : Finset ℕ, (↑I : Set ℕ) = I₀ := ⟨hfin.toFinset, hfin.coe_toFinset⟩
  have hIne : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hne (eq_top_iff.mpr fun y _ => (hJ y).mpr fun i hi => absurd hi (by simp))
  obtain ⟨t, htI, htmax⟩ : ∃ t ∈ I, ∀ i ∈ I, i ≤ t :=
    ⟨I.max' hIne, I.max'_mem hIne, fun i hi => I.le_max' i hi⟩
  have htr : t ≤ r := (hI₀ (Finset.mem_coe.mpr htI)).2
  obtain ⟨s, rfl⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
  exact ⟨K, inferInstance, f, t, s, ε, h, ρ, I, g, hε,
    ⟨htI, fun i hi => ⟨(hI₀ (Finset.mem_coe.mpr hi)).1, htmax i hi⟩⟩, hq, hρ, hJ⟩

theorem kFactCompParabSU38On_unitary : KFactCompParabSU38On (IsLieOf (IdxTwistedAExcept 8)) := by
  intro Y _ _ L P hCP hC
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hJ⟩ :=
    exists_uniFlag_of_compParab hCP d (idxTwistedA_of_except hd) e
  have hf8 : 2 ^ f ≠ 8 := two_pow_ne_of_except hd hq
  have : Finite K := h.finite
  refine su38At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ, uniBlockOrders f s ε, hρ,
    hasLeviBlocks_hypStab h hε hI g hJ, ?_⟩
  rintro (⟨k, hk⟩ | hk)
  · exact ordA_ne_u38 (n := k) (f := 2 * f) (by rw [← pow_mul, mul_comm]) hk.symm
  · exact hf8 ((ordTwistedA_eq_u38_iff (f := f) rfl).mp hk.symm).2

theorem kFactCompParabLeviU42On_unitary :
    KFactCompParabLeviU42On (IsLieOf (IdxTwistedAExcept 2)) := by
  intro Y _ _ L P hCP hC
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hJ⟩ :=
    exists_uniFlag_of_compParab hCP d (idxTwistedA_of_except hd) e
  have hf2 : 2 ^ f ≠ 2 := two_pow_ne_of_except hd hq
  have : Finite K := h.finite
  refine leviU42At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ, uniBlockOrders f s ε,
    hρ, hasLeviBlocks_hypStab h hε hI g hJ, ?_⟩
  rintro (⟨k, hk⟩ | hk)
  · exact ordA_ne_u42 (n := k) (f := 2 * f) (by rw [← pow_mul, mul_comm]) hk.symm
  · exact hf2 ((ordTwistedA_eq_u42_iff (f := f) rfl).mp hk.symm).2

theorem kFactCompParabThreeFivesOn_unitary :
    KFactCompParabThreeFivesOn (IsLieOf (IdxTwistedAExcept 2)) := by
  intro Y _ _ L P hCP hC
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hJ⟩ :=
    exists_uniFlag_of_compParab hCP d (idxTwistedA_of_except hd) e
  have hf2 : 2 ^ f ≠ 2 := two_pow_ne_of_except hd hq
  have : Finite K := h.finite
  set β := LeviBlock.uniLeviHom (s := s) h hε hI
  set e' := LeviBlock.stabMulEquiv g hJ
  have hrange : (β.comp e'.toMonoidHom).range = β.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map (e'.toMonoidHom),
      Subgroup.map_top_of_surjective _ e'.surjective, ← MonoidHom.range_eq_map]
  refine fivesAt_of_levi hCP.parab.1 ρ hρ (β.comp e'.toMonoidHom)
    ((LeviBlock.isPGroup_ker_uniLeviHom h hε hI).comap_of_injective e'.toMonoidHom e'.injective)
    (hrange ▸ LeviBlock.pi_uniBlockSub_le_range h hε hI)
    (hrange ▸ LeviBlock.commutator_range_le_pi h hε hI)
    (fun j => (LeviBlock.uniBlockSub_facts h hε hI j).1)
    (fun j hq h60 => LeviBlock.card_uniBlockSub_of_sixty h hε hI j hq h60) ?_
  set S := LeviBlock.uniBlockSub (s := s) (ε := ε) h I with hS
  have hnone : ∀ j, CFSG.Open.IsQuasisimple (S j) →
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 → j = none := by
    rintro (_ | b) hq h60
    · rfl
    · exfalso
      rw [(LeviBlock.uniBlockSub_facts h hε hI (some b)).2 hq] at h60
      change ordA (b.1 - LeviBlock.predCut I b.1 - 1) ((2 ^ f) ^ 2) = 60 at h60
      obtain ⟨-, h4⟩ := (ordA_eq_sixty_iff (f := 2 * f) (by rw [← pow_mul, mul_comm])).mp h60
      exact hf2 (Nat.pow_left_injective two_ne_zero (h4.trans (by norm_num)))
  have : Subsingleton {j // CFSG.Open.IsQuasisimple (S j) ∧
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60} :=
    ⟨fun x y => Subtype.ext ((hnone x.1 x.2.1 x.2.2).trans (hnone y.1 y.2.1 y.2.2).symm)⟩
  exact (Finite.card_le_one_iff_subsingleton.mpr this).trans (by norm_num)

theorem kFactCompParabSU38On_twistedA_of
    (h8 : KFactCompParabSU38On (IsLieOf (IdxTwistedAAt 8))) :
    KFactCompParabSU38On (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC
  rcases isLieOf_twistedA_cases 8 hC with hC | hC
  · exact kFactCompParabSU38On_unitary Y L P hCP hC
  · exact h8 Y L P hCP hC

theorem kFactCompParabLeviU42On_twistedA_of
    (h2 : KFactCompParabLeviU42On (IsLieOf (IdxTwistedAAt 2))) :
    KFactCompParabLeviU42On (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC
  rcases isLieOf_twistedA_cases 2 hC with hC | hC
  · exact kFactCompParabLeviU42On_unitary Y L P hCP hC
  · exact h2 Y L P hCP hC

theorem kFactCompParabThreeFivesOn_twistedA_of
    (h2 : KFactCompParabThreeFivesOn (IsLieOf (IdxTwistedAAt 2))) :
    KFactCompParabThreeFivesOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC
  rcases isLieOf_twistedA_cases 2 hC with hC | hC
  · exact kFactCompParabThreeFivesOn_unitary Y L P hCP hC
  · exact h2 Y L P hCP hC

end CFSG.AGLEmbedding
