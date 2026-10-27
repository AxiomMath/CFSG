module

public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.LieType.Steinberg.Bruhat

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

section Rank

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}

theorem weylAction_single_eq_or_neg (hA : TauCeti.IsFiniteType A) (hsub : ∀ i j : I, i = j)
    (i₀ : I) (w : (coxeterMatrix hA).Group) :
    weylAction hA w (Pi.single i₀ 1) = Pi.single i₀ 1 ∨
      weylAction hA w (Pi.single i₀ 1) = -Pi.single i₀ 1 := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
    have hi : i = i₀ := hsub i i₀
    subst hi
    rw [weylAction_mul_apply, weylAction_simple]
    rcases ih with h | h
    · right
      rw [h, reflection_single_self (hA.apply_self i)]
    · left
      rw [h, map_neg, reflection_single_self (hA.apply_self i), neg_neg]

end Rank

section Group

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem rankOne_ne_top
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {i j : Fin D.rank} (hij : i ≠ j) :
    rankOne D.rootGroup i ≠ ⊤ := by
  intro htop
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inl ⟨1, i, by simp⟩
  have hnj : n j ∈ rankOne D.rootGroup i := htop ▸ Subgroup.mem_top _
  have hB : ∀ {x : K}, x ∈ D.rootGroup (Pi.single i 1) → x ∈ borel D H := fun hx =>
    rootGroup_le_borel hα (ht_single_pos i) hx
  have hT : ∀ {x : K}, x ∈ H i → x ∈ borel D H := fun hx => iSup_le_borel (le_iSup H i hx)
  have hcell : n j ∈ bruhatCell hct 1 ∨
      n j ∈ bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) := by
    rcases hext.rankOne_bruhat i (n j) hnj with ⟨h, hh, u, hu, e⟩ | ⟨u, hu, h, hh, v, hv, e⟩
    · left
      rw [bruhatCell_one, e]
      exact mul_mem (hT hh) (hB hu)
    · right
      refine ⟨u, hB hu, h * v, mul_mem (hT hh) (hB hv), ?_⟩
      rw [nrep_simple, e]
      group
  have hcj : n j ∈ bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j) := by
    rw [← nrep_simple hct j]
    exact nrep_mem_bruhatCell hct _
  rcases hcell with h | h
  · exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_ne_one j
      (eq_of_mem_bruhatCell hct hext hcj h)
  · exact hij ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_injective
      (eq_of_mem_bruhatCell hct hext hcj h)).symm

theorem exists_le_map_conj_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ (g : K) (i : Fin D.rank), D.rootGroup γ ⊔ D.rootGroup (-γ) ≤
      (rankOne D.rootGroup i).map (MulAut.conj g).toMonoidHom := by
  have key : ∀ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank), ∃ g : K,
      (rankOne D.rootGroup i).map (MulAut.conj g).toMonoidHom =
        D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ⊔
          D.rootGroup (-weylAction D.isFiniteType w (Pi.single i 1)) := by
    intro w i
    obtain ⟨g, hg⟩ := exists_map_conj_rankOne hct w
    exact ⟨g, hg _ (Or.inl ⟨1, i, by simp⟩)⟩
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · obtain ⟨g, hg⟩ := key w i
    exact ⟨g, i, hg.ge⟩
  · obtain ⟨g, hg⟩ := key w i
    refine ⟨g, i, ?_⟩
    rw [hg]
    have h1 : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots := Or.inl ⟨w, i, rfl⟩
    have h2 : 2 • weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots := Or.inr ⟨w, i, hi, rfl⟩
    refine sup_le_sup (hext.two_smul_le _ h1 h2) ?_
    have h3 := OfCartan.neg_mem_roots D.isFiniteType h1
    have h4 : 2 • (-weylAction D.isFiniteType w (Pi.single i 1)) ∈ D.roots := by
      rw [smul_neg]
      exact OfCartan.neg_mem_roots D.isFiniteType h2
    have := hext.two_smul_le _ h3 h4
    rwa [smul_neg] at this

theorem eq_top_of_map_conj_eq_top {L : Subgroup K} {h : K}
    (hL : L.map (MulAut.conj h).toMonoidHom = ⊤) : L = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : h * x * h⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom := hL ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by simpa [mul_assoc] using hyx
  exact this ▸ hy

theorem map_conj_ne_top
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hrank : 2 ≤ D.rank) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (g : K) :
    (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  obtain ⟨g', i, hle⟩ := exists_le_map_conj_rankOne hct hext hγ
  obtain ⟨j, hij⟩ : ∃ j : Fin D.rank, i ≠ j := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff, h0] at h⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by simp [Fin.ext_iff] at h; omega)⟩
  intro htop
  have h1 : (rankOne D.rootGroup i).map (MulAut.conj (g * g')).toMonoidHom = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← htop]
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
    refine this.trans (le_of_eq ?_)
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  exact rankOne_ne_top hct hext hij (eq_top_of_map_conj_eq_top h1)

theorem map_conj_eq_top_of_subsingleton
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hsub : ∀ i j : Fin D.rank, i = j) (hdiv : D.divisible = ∅) (i₀ : Fin D.rank)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (g : K) :
    (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom = ⊤ := by
  set e : Fin D.rank → ℤ := Pi.single i₀ 1 with he
  have hw : ∀ w : (coxeterMatrix D.isFiniteType).Group,
      weylAction D.isFiniteType w e = e ∨ weylAction D.isFiniteType w e = -e :=
    weylAction_single_eq_or_neg D.isFiniteType hsub i₀
  have hroots : ∀ γ ∈ D.roots, γ = e ∨ γ = -e := by
    rintro γ (⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩)
    · have hi : i = i₀ := hsub i i₀
      subst hi
      exact hw w
    · simp [hdiv] at hi
  have hL : rankOne D.rootGroup i₀ = ⊤ := by
    rw [eq_top_iff, ← hct.iSup_eq_top]
    refine iSup₂_le fun γ hγ => ?_
    rcases hroots γ hγ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hR : D.rootGroup γ ⊔ D.rootGroup (-γ) = ⊤ := by
    rcases hroots γ hγ with rfl | rfl
    · exact hL
    · rw [neg_neg, sup_comm]
      exact hL
  rw [hR]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

end Group

end CFSG.ClassicalInvolution.ModelFacts
