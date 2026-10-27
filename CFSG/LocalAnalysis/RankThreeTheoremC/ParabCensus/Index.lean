module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Cover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.RankThree.PartTwo.Census.Classical.EvenLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup

theorem card_eq_two_pow_of_charP_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ n : ℕ, n ≠ 0 ∧ Nat.card K = 2 ^ n := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.2.ne', by rw [Nat.card_eq_fintype_card, hn]⟩

theorem odd_card_sub_one_of_charP_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card K - 1) := by
  obtain ⟨n, hn, hcard⟩ := card_eq_two_pow_of_charP_two (K := K)
  have heven : Even (Nat.card K) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero hn
  exact Nat.Even.sub_odd (m := Nat.card K) (n := 1)
    (by have := Finite.one_lt_card (α := K); omega) heven odd_one

theorem four_le_card_of_charP_two_ne_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : Nat.card K ≠ 2) : 4 ≤ Nat.card K := by
  obtain ⟨n, hn, hcard⟩ := card_eq_two_pow_of_charP_two (K := K)
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1 : n = 1 := by omega
      exact absurd (by rw [hcard, hn1]; norm_num) h
    · exact hge
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

theorem not_two_dvd_index_range_toGL {K : Type} [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    ¬ 2 ∣ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range.index := by
  rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, Subgroup.index_ker]
  intro h2
  have hdvd : Nat.card (Matrix.GeneralLinearGroup.det (n := Fin m) (R := K)).range ∣
      Nat.card K - 1 := by
    have := Subgroup.card_subgroup_dvd_card
      (Matrix.GeneralLinearGroup.det (n := Fin m) (R := K)).range
    rwa [Nat.card_units] at this
  have hodd := odd_card_sub_one_of_charP_two (K := K)
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (h2.trans hdvd))

theorem range_toGL_cases {K : Type} [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range = ⊥ ∨
      (Nat.card K = 2 ∧ m = 2 ∧ IsSymThreeOrSUThreeTwo ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) ∨
      (CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range ∧
        Odd (Nat.card (center ↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set S : Subgroup (GL (Fin m) K) :=
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
  have e : Matrix.SpecialLinearGroup (Fin m) K ≃* ↥S :=
    CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := K) m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · refine Or.inl ?_
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin m) K) :=
      CFSG.AGLEmbedding.LeviBlock.subsingleton_specialLinear_of_lt_two (K := K) hm
    haveI : Subsingleton ↥S := Equiv.subsingleton e.symm.toEquiv
    exact Subgroup.eq_bot_of_subsingleton S
  · by_cases h2 : Nat.card K = 2 ∧ m = 2
    · obtain ⟨hK, rfl⟩ := h2
      obtain ⟨f⟩ := CFSG.StandardType.RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
      exact Or.inr (Or.inl ⟨hK, rfl, Or.inl ⟨e.symm.trans f⟩⟩)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · have hq : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset K, s.card = 4) := by
          refine ⟨hm, ?_⟩
          rcases Nat.lt_or_ge m 3 with h3 | h3
          · have hm3 : m = 2 := by omega
            subst hm3
            refine Or.inr ?_
            have hne : Nat.card K ≠ 2 := fun hK => h2 ⟨hK, rfl⟩
            obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
              (n := 4) (by
                rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
                exact four_le_card_of_charP_two_ne_two hne)
            exact ⟨s, hs⟩
          · exact Or.inl h3
        have hQ : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) K) :=
          ⟨(CFSG.LinearGroups.special_linear_isPerfect hq.1 hq.2).commutator_eq_top,
            (CFSG.LinearGroups.linear_projective_simple hq.1 hq.2).2.1⟩
        exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hQ
      ·
        have hc : Nat.Coprime
            (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))) 2 :=
          CFSG.RankThree.PartTwo.Census.coprime_card_center_SL (K := K) (by omega)
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hc
        have hodd : Odd (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))) :=
          Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp hc)
        rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv.symm]
        exact hodd

@[expose] def piReindex {ι κ : Type} {G : ι → Type} [∀ j, Group (G j)] (e : ι ≃ κ) :
    (∀ j, G j) ≃* (∀ i, G (e.symm i)) :=
  { Equiv.piCongrLeft' G e with map_mul' := fun _ _ => rfl }

theorem map_pi_piReindex {ι κ : Type} {G : ι → Type} [∀ j, Group (G j)] (e : ι ≃ κ)
    (S : ∀ j, Subgroup (G j)) :
    (Subgroup.pi Set.univ S).map (piReindex (G := G) e).toMonoidHom =
      Subgroup.pi Set.univ (fun i => S (e.symm i)) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_pi] at hx ⊢
    intro i _
    exact hx (e.symm i) trivial
  · intro y hy
    obtain ⟨x, rfl⟩ := (piReindex (G := G) e).surjective y
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_pi] at hy ⊢
    intro j _
    have h1 : x (e.symm (e j)) ∈ S (e.symm (e j)) := hy (e j) trivial
    exact (Equiv.symm_apply_apply e j) ▸ h1

theorem not_two_dvd_relIndex_pi_of_finite {ι : Type} [Finite ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S T : ∀ j, Subgroup (G j)} (hST : ∀ j, S j ≤ T j)
    {Λ : Subgroup (∀ j, G j)} (h1 : Subgroup.pi Set.univ S ≤ Λ)
    (h2 : Λ ≤ Subgroup.pi Set.univ T) (h : ∀ j, ¬ 2 ∣ (S j).relIndex (T j)) :
    ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex Λ := by
  classical
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let φe : (∀ j, G j) ≃* (∀ i : Fin (Nat.card ι), G (e.symm i)) := piReindex e
  have hmap := map_pi_piReindex (G := G) e
  have h1' : Subgroup.pi Set.univ (fun i => S (e.symm i)) ≤ Λ.map φe.toMonoidHom := by
    rw [← hmap S]
    exact Subgroup.map_mono h1
  have h2' : Λ.map φe.toMonoidHom ≤ Subgroup.pi Set.univ (fun i => T (e.symm i)) := by
    rw [← hmap T]
    exact Subgroup.map_mono h2
  have key := not_two_dvd_relIndex_pi (G := fun i => G (e.symm i))
    (S := fun i => S (e.symm i)) (T := fun i => T (e.symm i))
    (fun i => hST (e.symm i)) h1' h2' (fun i => h (e.symm i))
  rw [← hmap S, Subgroup.relIndex_map_map_of_injective _ _ φe.injective] at key
  exact key

theorem hasLeviCensus_of_cover_of_finite {X C : Type} [Group X] [Group C] [Finite C]
    {L J : Subgroup X} (hJL : J ≤ L) (ρ : C →* ↥L) (hρ : Function.Surjective ρ)
    (hc : ρ.ker ≤ center C) (ho : Odd (Nat.card ρ.ker)) {B : (X : Type) → [Group X] → Prop}
    {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]
    [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    (β : ↥((J.subgroupOf L).comap ρ) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range) (hS : ∀ j, S j = ⊥ ∨ B ↥(S j))
    (hZ : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z : ↥((J.subgroupOf L).comap ρ),
      ρ z = 1 → β z ∈ (S j).map (MonoidHom.mulSingle G j) → β z = 1) :
    HasLeviCensus ↥J B := by
  classical
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let φe : (∀ j, G j) ≃* (∀ i : Fin (Nat.card ι), G (e.symm i)) := piReindex e
  let β' : ↥((J.subgroupOf L).comap ρ) →* (∀ i : Fin (Nat.card ι), G (e.symm i)) :=
    φe.toMonoidHom.comp β
  have hφapply : ∀ (x : ∀ j, G j) (i : Fin (Nat.card ι)), φe x i = x (e.symm i) :=
    fun x i => Equiv.piCongrLeft'_apply G e x i
  have hmap := map_pi_piReindex (G := G) e
  have hβ'def : β' = φe.toMonoidHom.comp β := rfl
  have hβ' : IsPGroup 2 β'.ker := by
    have hker : β'.ker = β.ker := by
      ext z
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact φe.map_eq_one_iff
    rw [hker]
    exact hβ
  have hle' : Subgroup.pi Set.univ (fun i => S (e.symm i)) ≤ β'.range := by
    rw [hβ'def, MonoidHom.range_comp, ← hmap S]
    exact Subgroup.map_mono hle
  have hn' : β'.range ≤ normalizer (Subgroup.pi Set.univ (fun i => S (e.symm i)) :
      Set (∀ i : Fin (Nat.card ι), G (e.symm i))) := by
    rw [hβ'def, MonoidHom.range_comp, ← hmap S,
      ← Subgroup.map_normalizer_eq_of_bijective (Subgroup.pi Set.univ S) φe.bijective]
    exact Subgroup.map_mono hn
  have hi' : ¬ 2 ∣ (Subgroup.pi Set.univ (fun i => S (e.symm i))).relIndex β'.range := by
    rw [hβ'def, MonoidHom.range_comp, ← hmap S,
      Subgroup.relIndex_map_map_of_injective _ _ φe.injective]
    exact hi
  have hsingle : ∀ (i : Fin (Nat.card ι)) (x : G (e.symm i)),
      φe (MonoidHom.mulSingle G (e.symm i) x) =
        MonoidHom.mulSingle (fun i => G (e.symm i)) i x := by
    intro i x
    funext k
    rw [hφapply, MonoidHom.mulSingle_apply, MonoidHom.mulSingle_apply]
    by_cases hk : k = i
    · rw [hk, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have hk' : e.symm k ≠ e.symm i := fun h => hk (e.symm.injective h)
      rw [Pi.mulSingle_eq_of_ne hk', Pi.mulSingle_eq_of_ne hk]
  have hZ' : ∀ i, ¬ CFSG.Open.IsQuasisimple ↥(S (e.symm i)) →
      ∀ z : ↥((J.subgroupOf L).comap ρ), ρ z = 1 →
        β' z ∈ (S (e.symm i)).map (MonoidHom.mulSingle (fun i => G (e.symm i)) i) →
        β' z = 1 := by
    intro i hq z hz1 hz2
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hz2
    have hβz : β z = MonoidHom.mulSingle G (e.symm i) x := by
      apply φe.injective
      rw [hsingle i x, hxeq]
      rfl
    have hmem : β z ∈ (S (e.symm i)).map (MonoidHom.mulSingle G (e.symm i)) :=
      Subgroup.mem_map.mpr ⟨x, hx, hβz.symm⟩
    rw [show β' z = φe (β z) from rfl, hZ (e.symm i) hq z hz1 hmem]
    exact map_one φe
  exact hasLeviCensus_of_cover hJL ρ hρ hc ho (G := fun i => G (e.symm i))
    (S := fun i => S (e.symm i)) β' hβ' hle' hn' hi' (fun i => hS (e.symm i)) hZ'

theorem hasLeviCensus_of_mulEquiv_of_finite {X C : Type} [Group X] [Group C] [Finite C]
    {L J : Subgroup X} (hJL : J ≤ L) (ρ : C ≃* ↥L) {B : (X : Type) → [Group X] → Prop}
    {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]
    [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    (β : ↥((J.subgroupOf L).comap ρ.toMonoidHom) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range) (hS : ∀ j, S j = ⊥ ∨ B ↥(S j)) :
    HasLeviCensus ↥J B := by
  refine hasLeviCensus_of_cover_of_finite hJL ρ.toMonoidHom ρ.surjective ?_ ?_ β hβ hle hn hi hS ?_
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr ρ.injective]
    exact bot_le
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr ρ.injective, Subgroup.card_bot]
    exact odd_one
  · intro j _ z hz _
    have hz1 : z = 1 := Subtype.ext (by
      have h : ρ (z : C) = 1 := hz
      have h2 : ρ (z : C) = ρ 1 := by rw [h, map_one]
      exact ρ.injective h2)
    rw [hz1]
    exact map_one β

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
