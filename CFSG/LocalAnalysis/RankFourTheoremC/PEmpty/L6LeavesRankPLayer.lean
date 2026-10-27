module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Comp
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG CFSG.LocalCores Subgroup CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem center_eq_bot_of_simple {V : Type*} [Group V] {C : Subgroup V} (hC : IsComponent C)
    (hs : IsSimpleGroup C) : center C = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) with h | h
  · exact h
  · exfalso
    haveI : IsSimpleGroup (C ⧸ center C) := hC.1.2.1
    have hsub : Subsingleton (C ⧸ center C) := QuotientGroup.subsingleton_iff.mpr h
    exact not_subsingleton _ hsub

theorem normal_le_layer_eq_bot_or_layer_le {V : Type} [Group V] [Finite V]
    (hC : ∀ C : ComponentIndex V, IsSimpleGroup C.1)
    (htrans : ∀ C D : ComponentIndex V, ∃ g : V, C.1.map (MulAut.conj g).toMonoidHom = D.1)
    (N : Subgroup V) [N.Normal] (hN : N ≤ layer V) : N = ⊥ ∨ layer V ≤ N := by
  have hZ : ∀ C : ComponentIndex V, center C.1 = ⊥ := fun C => center_eq_bot_of_simple C.2 (hC C)
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨⟨n, hnN⟩, hn1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hn1 : n ≠ 1 := fun h => hn1' (Subtype.ext h)
  have hnL : n ∈ layer V := hN hnN
  obtain ⟨C, hCn⟩ : ∃ C : ComponentIndex V, π hZ C n hnL ≠ 1 := by
    by_contra h
    push Not at h
    exact hn1 (eq_one_of_π_eq_one (hZ := hZ) hnL h)
  have hncent : n ∉ centralizer (C.1 : Set V) := fun h =>
    hCn ((π_eq_one_iff (hZ := hZ) C hnL).mpr h)
  rw [mem_centralizer_iff] at hncent
  push Not at hncent
  obtain ⟨c, hcC, hnc⟩ := hncent
  have hnorm : n ∈ normalizer (C.1 : Set V) := mem_normalizer_of_mem_layer hZ C hnL
  have hmC : n * c * n⁻¹ * c⁻¹ ∈ C.1 := by
    have h1 : n * c * n⁻¹ ∈ C.1 := (Subgroup.mem_normalizer_iff.mp hnorm c).mp hcC
    exact mul_mem h1 (inv_mem hcC)
  have hmN : n * c * n⁻¹ * c⁻¹ ∈ N := by
    have : n * (c * n⁻¹ * c⁻¹) ∈ N :=
      mul_mem hnN ((inferInstance : N.Normal).conj_mem _ (inv_mem hnN) c)
    simpa [mul_assoc] using this
  have hm1 : n * c * n⁻¹ * c⁻¹ ≠ 1 := by
    intro h
    apply hnc
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hCN : C.1 ≤ N := by
    let M : Subgroup C.1 := N.subgroupOf C.1
    haveI : M.Normal := Subgroup.normal_subgroupOf
    haveI := hC C
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exfalso
      have hmem : (⟨n * c * n⁻¹ * c⁻¹, hmC⟩ : C.1) ∈ M := hmN
      rw [h, Subgroup.mem_bot] at hmem
      exact hm1 (congrArg Subtype.val hmem)
    · intro x hx
      have : (⟨x, hx⟩ : C.1) ∈ M := by rw [h]; exact Subgroup.mem_top _
      exact this
  refine sSup_le fun K hK => ?_
  obtain ⟨g, hg⟩ := htrans C ⟨K, hK⟩
  have : K = C.1.map (MulAut.conj g).toMonoidHom := hg.symm
  rw [this]
  rintro _ ⟨c', hc', rfl⟩
  exact (inferInstance : N.Normal).conj_mem _ (hCN hc') g

theorem map_pLayer_eq_layer {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] :
    (pLayer X p).map (QuotientGroup.mk' (pPrimeCore p X)) = layer (X ⧸ pPrimeCore p X) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    obtain ⟨K, hK, -, hJK, -⟩ := hJ
    rw [← Subgroup.map_le_iff_le_comap, hJK]
    exact le_sSup hK
  · exact CFSG.ComponentClassification.CatalogueBPrimeJoin.layer_quotient_le_map_pLayer

theorem dichotomy {X : Type} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] (E : Subgroup X)
    (hfrat : ∀ g : X, ∃ n ∈ normalizer (E : Set X), ∃ o ∈ pPrimeCore p X, g = n * o)
    (hC : ∀ C : ComponentIndex (X ⧸ pPrimeCore p X), IsSimpleGroup C.1)
    (htrans : ∀ C D : ComponentIndex (X ⧸ pPrimeCore p X), ∃ g : X ⧸ pPrimeCore p X,
      C.1.map (MulAut.conj g).toMonoidHom = D.1) :
    ((pLayer X p ⊓ centralizer (E : Set X)).map (QuotientGroup.mk' (pPrimeCore p X)) = ⊥) ∨
      layer (X ⧸ pPrimeCore p X) ≤
        (pLayer X p ⊓ centralizer (E : Set X)).map (QuotientGroup.mk' (pPrimeCore p X)) := by
  haveI : (pLayer X p).Characteristic :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := p)
  set R := pPrimeCore p X with hR
  set π := QuotientGroup.mk' R with hπ
  set H := pLayer X p ⊓ centralizer (E : Set X) with hH
  have hHL : H.map π ≤ layer (X ⧸ R) := by
    rw [← map_pLayer_eq_layer p]
    exact Subgroup.map_mono inf_le_left
  have hnH : ∀ n ∈ normalizer (E : Set X), ∀ h ∈ H, n * h * n⁻¹ ∈ H := by
    intro n hn h hh
    refine Subgroup.mem_inf.mpr ⟨(inferInstance : (pLayer X p).Normal).conj_mem _ hh.1 n, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hen : n⁻¹ * e * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) e).mp he
      simpa using this
    have hc := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2) _ hen
    calc e * (n * h * n⁻¹) = n * ((n⁻¹ * e * n) * h) * n⁻¹ := by group
      _ = n * (h * (n⁻¹ * e * n)) * n⁻¹ := by rw [hc]
      _ = (n * h * n⁻¹) * e := by group
  haveI hNnorm : (H.map π).Normal := by
    refine ⟨fun x hx v => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨n, hn, o, ho, rfl⟩ := hfrat g
    refine ⟨n * h * n⁻¹, hnH n hn h hh, ?_⟩
    have ho1 : ((o : X) : X ⧸ R) = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    simp only [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ho1,
      mul_one]
  exact normal_le_layer_eq_bot_or_layer_le hC htrans (H.map π) hHL

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
