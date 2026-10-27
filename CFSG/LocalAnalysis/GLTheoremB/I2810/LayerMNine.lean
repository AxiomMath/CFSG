module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

variable {n : ℕ}

open Equiv in
theorem exists_altEmbedding (T : Finset (Fin n)) (e : Fin 9 ≃ {i // i ∈ T}) :
    ∃ ι : ↥(alternatingGroup (Fin 9)) →* ↥(alternatingGroup (Fin n)),
      Function.Injective ι ∧
      (∀ (σ : ↥(alternatingGroup (Fin 9))) (j : Fin 9),
        ((ι σ : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ((e j : {i // i ∈ T}) : Fin n) =
          ((e ((σ : Perm (Fin 9)) j) : {i // i ∈ T}) : Fin n)) ∧
      ∀ g : ↥(alternatingGroup (Fin n)), (∀ i, i ∉ T → (g : Perm (Fin n)) i = i) → g ∈ ι.range := by
  classical
  have hmem : ∀ σ : ↥(alternatingGroup (Fin 9)),
      Perm.extendDomainHom e (σ : Perm (Fin 9)) ∈ alternatingGroup (Fin n) := by
    intro σ
    rw [Perm.mem_alternatingGroup, Perm.extendDomainHom_apply, Perm.sign_extendDomain]
    exact Perm.mem_alternatingGroup.1 σ.2
  let ι : ↥(alternatingGroup (Fin 9)) →* ↥(alternatingGroup (Fin n)) :=
    ((Perm.extendDomainHom e).comp (alternatingGroup (Fin 9)).subtype).codRestrict
      (alternatingGroup (Fin n)) hmem
  have hι : ∀ σ : ↥(alternatingGroup (Fin 9)),
      ((ι σ : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) = (σ : Perm (Fin 9)).extendDomain e :=
    fun σ => rfl
  refine ⟨ι, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Perm (Fin n))) hab
    simp only [hι] at h1
    exact Subtype.ext (Perm.extendDomainHom_injective e h1)
  · intro σ j
    rw [hι]
    exact Perm.extendDomain_apply_image _ e j
  · rintro ⟨g, hg⟩ hfix
    have hfix' : ∀ i, i ∉ T → g i = i := hfix
    have hpres : ∀ x, g x ∈ T ↔ x ∈ T := by
      intro x
      constructor
      · intro hx
        by_contra hxT
        rw [hfix' x hxT] at hx
        exact hxT hx
      · intro hx
        by_contra hgx
        have h2 : g x = x := g.injective (hfix' (g x) hgx)
        rw [h2] at hgx
        exact hgx hx
    set σ₀ : Perm (Fin 9) :=
      (Equiv.permCongr e.symm) (g.subtypePerm (p := fun x => x ∈ T) hpres) with hσ₀
    have hext : σ₀.extendDomain e = g := by
      ext x
      by_cases hx : x ∈ T
      · rw [Perm.extendDomain_apply_subtype σ₀ e hx]
        simp [hσ₀]
      · rw [Perm.extendDomain_apply_not_subtype σ₀ e hx, hfix' x hx]
    have hsign : Perm.sign σ₀ = 1 := by
      rw [← Perm.sign_extendDomain σ₀ e, hext]
      exact Perm.mem_alternatingGroup.1 hg
    exact ⟨⟨σ₀, Perm.mem_alternatingGroup.2 hsign⟩, Subtype.ext hext⟩

theorem perm_gen_nine_of_base (hn : 9 ≤ n)
    (hbase : ∀ {V₄ Vv : Subgroup ↥(alternatingGroup (Fin 9))}, IsRootFour V₄ → Vv ≤ V₄ →
      (Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) →
      ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin 9))), Nat.card ↥Vv ^ s ≤ 2 ^ 6 ∧
        ⊤ ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom)
    {V₄ Vv : Subgroup ↥(alternatingGroup (Fin n))} (hV₄ : IsRootFour V₄) (hVv : Vv ≤ V₄)
    (hc : Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) :
    ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin n))), Nat.card ↥Vv ^ s ≤ 2 ^ 6 ∧
      ∃ F : Subgroup ↥(alternatingGroup (Fin n)),
        F ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom ∧
          Nonempty (↥F ≃* ↥(alternatingGroup (Fin 9))) := by
  classical
  obtain ⟨hcard4, hsq, hmov⟩ := hV₄
  have hM : (Finset.univ.filter
      fun i : Fin n => ¬ ∀ v ∈ V₄, (v : Equiv.Perm (Fin n)) i = i).card = 4 := by
    rw [← hmov, Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨T, hMT, hT⟩ := Finset.exists_superset_card_eq
    (s := Finset.univ.filter fun i : Fin n => ¬ ∀ v ∈ V₄, (v : Equiv.Perm (Fin n)) i = i) (n := 9)
    (by omega) (by simpa using hn)
  let e : Fin 9 ≃ {i // i ∈ T} := (Fintype.equivFinOfCardEq (by simpa using hT)).symm
  obtain ⟨ι, hinj, happ, hrange⟩ := exists_altEmbedding T e
  have hfix : ∀ v ∈ V₄, ∀ i, i ∉ T → (v : Equiv.Perm (Fin n)) i = i := by
    intro v hv i hi
    by_contra hne
    exact hi (hMT (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hall => hne (hall v hv)⟩))
  have hV₄le : V₄ ≤ ι.range := fun v hv => hrange v (hfix v hv)
  have hVvle : Vv ≤ ι.range := hVv.trans hV₄le
  have hmapV₄ : (V₄.comap ι).map ι = V₄ := Subgroup.map_comap_eq_self hV₄le
  have hmapVv : (Vv.comap ι).map ι = Vv := Subgroup.map_comap_eq_self hVvle
  have hcardV₄ : Nat.card (V₄.comap ι) = Nat.card V₄ := by
    have := Subgroup.card_map_of_injective (K := V₄.comap ι) hinj
    rw [hmapV₄] at this
    exact this.symm
  have hcardVv : Nat.card (Vv.comap ι) = Nat.card Vv := by
    have := Subgroup.card_map_of_injective (K := Vv.comap ι) hinj
    rw [hmapVv] at this
    exact this.symm
  have hroot : IsRootFour (V₄.comap ι) := by
    refine ⟨hcardV₄.trans hcard4, ?_, ?_⟩
    · intro w hw
      apply hinj
      rw [map_pow, map_one]
      exact hsq _ hw
    · have key : ∀ j : Fin 9, (¬ ∀ w ∈ V₄.comap ι, (w : Equiv.Perm (Fin 9)) j = j) ↔
          ¬ ∀ v ∈ V₄, (v : Equiv.Perm (Fin n)) ((e j : {i // i ∈ T}) : Fin n) =
            ((e j : {i // i ∈ T}) : Fin n) := by
        intro j
        constructor
        · intro hj hall
          apply hj
          intro w hw
          have h1 := hall (ι w) hw
          rw [happ] at h1
          exact e.injective (Subtype.ext h1)
        · intro hj hall
          apply hj
          intro v hv
          obtain ⟨w, rfl⟩ := hV₄le hv
          have h1 := hall w hv
          rw [happ, h1]
      rw [← hmov]
      refine Nat.card_eq_of_bijective
        (fun j => ⟨((e j.1 : {i // i ∈ T}) : Fin n), (key j.1).1 j.2⟩) ⟨?_, ?_⟩
      · intro a b hab
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (e.injective (Subtype.ext h1))
      · rintro ⟨i, hi⟩
        have hiT : i ∈ T := hMT (by simpa using hi)
        refine ⟨⟨e.symm ⟨i, hiT⟩, (key _).2 ?_⟩, ?_⟩
        · simpa using hi
        · apply Subtype.ext
          simp
  have hc' : Nat.card (Vv.comap ι) = 2 ∨ Nat.card (Vv.comap ι) = 4 := by
    rwa [hcardVv]
  obtain ⟨s, ys, hs, hgen⟩ := hbase hroot (Subgroup.comap_mono hVv) hc'
  refine ⟨s, fun i => ι (ys i), ?_, ι.range, ?_, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩
  · rw [← hcardVv]
    exact hs
  · have h1 := Subgroup.map_mono (f := ι) hgen
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map] at h1
    refine h1.trans (le_of_eq (iSup_congr fun i => ?_))
    conv_rhs => rw [← hmapVv]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext v
    simp [MulAut.conj_apply]

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
