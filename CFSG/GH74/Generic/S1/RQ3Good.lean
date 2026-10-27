module

public import CFSG.GH74.Generic.S1.RQ3
public import CFSG.GH74.Generic.S1.RQ3Lin
public import CFSG.GH74.Generic.S1.RQ3Sys

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic

@[expose] def S1NormalizerYClause3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → S1FrameOddFree x u →
          ∀ y ∈ symJ3 (symX x u) 1, orderOf y = 2 → (∀ a ∈ symJ3 (symX x u) 1, a * y = y * a) →
            centralizer ({y} : Set G) ≤ normalizer ((⨆ i, symJ3 (symX x u) i : Subgroup G) : Set G)

variable {G : Type} [Group G]

omit [Group G] in
theorem injective_proj_of_pPrimeCore_eq_bot [Group G] [Finite G] {x : G}
    (h : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) : Function.Injective (proj x) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hmem : n ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) := (QuotientGroup.eq_one_iff n).1 hn
  rw [h] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem comap_le_liftL_of_injective {x : G} {K : Subgroup (CentralizerBar x)}
    (hinj : Function.Injective (proj x)) (hK : ⁅K, K⁆ = K) : K.comap (proj x) ≤ liftL x K := by
  set M : Subgroup ↥(centralizer ({x} : Set G)) := K.comap (proj x) with hM
  have hsurj : Function.Surjective (proj x) := fun b => QuotientGroup.mk_surjective b
  have hMK : M.map (proj x) = K := Subgroup.map_comap_eq_self_of_surjective hsurj _
  have hcomm : (⁅M, M⁆).map (proj x) = K := by
    rw [Subgroup.map_commutator, hMK]
    exact hK
  have hperf : ⁅M, M⁆ = M := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun g hg h hh => ?_
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hg hh) (M.inv_mem hg)) (M.inv_mem hh)
    · intro m hm
      have hmK : proj x m ∈ K := hm
      rw [← hcomm] at hmK
      obtain ⟨m', hm', hmm'⟩ := hmK
      have : m' = m := hinj hmm'
      rw [← this]
      exact hm'
  exact perfect_le_liftL le_rfl hperf

variable [Finite G]

theorem sym_layerData3 (x : G) (u : Fin 4 → G) {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    (hodd : S1FrameOddFree x u)
    (hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G))
    (hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j)) :
    ∀ e : Fin 5, ∃ D : LayerData3 (symX x u e) (StatedSL 4 F),
      D.K = layer (CentralizerBar (symX x u e)) ∧
        ∀ j, ActsAsReflOn D.iso (barOf (hw e j)) (reflDiag F j) := by
  intro e
  obtain ⟨K', hw', hset', hfront', iso, hiso⟩ := hloc e
  have hn : K'.Normal := normal_of_layer_eq hfront'.layer_eq
  have hinj : Function.Injective (proj (symX x u e)) := injective_proj_of_pPrimeCore_eq_bot (hodd e)
  have hexact : LiftExact (symX x u e) K' := fun l _ hl1 => hinj (hl1.trans (map_one _).symm)
  refine ⟨⟨⟨K', Subgroup.isPerfect_iff.mp hset'.comp.1.1, hn,
    fun P hP => hfront'.good_le P (Or.inl hP), hexact, iso⟩, hinj,
    fun P hP => hfront'.good_le P (Or.inr ⟨hP, ⟨F, inferInstance, inferInstance, hF3, Or.inl ⟨iso⟩⟩⟩)⟩,
    hfront'.layer_eq.symm, hiso⟩

theorem s1Nbhd_q3_of_yclause3 (hY3 : S1NormalizerYClause3)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3) (hlin : S1SymFrameLin x u F)
    (hodd : S1FrameOddFree x u) : ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData3 x u hF3 hodd hw hloc
  obtain ⟨hcomm, hpair, ⟨U, W, hchain', hlinked⟩, ⟨z, hz, hz2, hzc⟩⟩ :=
    symSystem3 (linBlockOps3 hF3) (symX x u) D hw hDact (linKind F)
      (fun a b c hab hac hbc => blkLin_standardPair a b c hab hac hbc) blkLin_chain
      (lin_blk_center3 hF3)
  have hK : (D 4).K = K := (hDK 4).trans hfront.layer_eq
  obtain ⟨p, f, hpp, -, hcard⟩ := exists_prime_pow_card F
  have hq3 : 3 ≤ p ^ f := by rw [← hcard, hF3]
  have hlink : S1LinkedLin x (D 4).K F (symJ3 (symX x u)) := ⟨U, W, hchain', hlinked⟩
  have hlinkK : S1LinkedLin x K F (symJ3 (symX x u)) := hlink.congr hK
  refine ⟨symJ3 (symX x u), Or.inl ⟨p, f, F, inferInstance, inferInstance, hpp, hcard, hq3,
    ⟨hcomm, hpair⟩, hlinkK⟩, ⟨z, hz, hz2, hzc, ?_⟩⟩
  intro Q hQ hQle
  have hKn : K.Normal := normal_of_layer_eq hfront.layer_eq
  have hfacts := s1A4Facts_lin (symJ3 (symX x u)) p f F hpp hcard hq3 ⟨hcomm, hpair⟩ hlinkK hz hz2 hzc
  obtain ⟨D0⟩ := frontDataStatement ↥K (Or.inl hset.shape.1)
  have hx0 : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥ := hodd 4
  have hinj : Function.Injective (proj x) := injective_proj_of_pPrimeCore_eq_bot hx0
  have hexact : LiftExact x K := fun l _ hl1 => hinj (hl1.trans (map_one _).symm)
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hset.comp.1.1
  have hsub := comap_le_liftL_of_injective hinj hKperf
  exact normalizer_clause_of_yclause_of_lift hset.inv hfront hset.shape.2 D0.toFrontData0 hexact hz
    hz2 (fun _ hπ => hsub hπ) hfacts
    (hY3 G x K hset hfront u hu hf F inferInstance inferInstance hF3 hlin hodd z hz hz2 hzc) Q hQ hQle

theorem s1NbhdQ3Good_of_yclause3 (hY3 : S1NormalizerYClause3) : S1NbhdQ3Good := by
  intro G _ _ x K hset hfront u hu hf F hFld hFin hF3 hlin hodd
  exact s1Nbhd_q3_of_yclause3 hY3 hset hfront hf hF3 hlin hodd

end CFSG.GH74.Generic.S1
