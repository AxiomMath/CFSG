module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Split
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof
public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.Open
open CFSG.HardMathSupport.Lang.TwE6Step3 (exists_fixed_split exists_fixed_split₂
  canonicalRep_conj_mem_rootSpan canonicalRep_inv_conj_mem_rootSpan rootSpan_union')

set_option linter.unusedSectionVars false


section Two

variable {L : Type} [Field L]

theorem rootSpan_inf_le_torusGroup_E7 {J₀ J₁ : Set (Fin Tag.E7.rank)}
    (hcomm : ∀ a ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀),
      ∀ b ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁), a * b = b * a) :
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀) ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁) ≤
      torusGroup Tag.E7 L := by
  intro g hg
  obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
  have hgS : g ∈ subsystemGroup Tag.E7 L J₀ := by
    rw [subsystemGroup_eq_rootSpan]
    exact hg₁
  have hc : (⟨g, hgS⟩ : subsystemGroup Tag.E7 L J₀) ∈
      Subgroup.center (subsystemGroup Tag.E7 L J₀) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    have hh : (h : ModGL Tag.E7 L) ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀) :=
      (subsystemGroup_eq_rootSpan (K := L) J₀).le h.2
    exact hcomm _ hh _ hg₂
  have h3 := mem_supportedTorus_of_mem_center hc
  rw [← subsystemGroup_inf_torusGroup_eq_supportedTorus] at h3
  exact (Subgroup.mem_inf.1 h3).2

theorem torusGroup_inf_sup_le_E7 (J₀ J₁ : Set (Fin Tag.E7.rank)) :
    torusGroup Tag.E7 L ⊓ (rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀) ⊔
        rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁)) ≤
      (torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀)) ⊔
        (torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁)) := by
  intro g hg
  obtain ⟨hgH, hgQ⟩ := Subgroup.mem_inf.1 hg
  have hsub : rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀) ⊔
      rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁) ≤
        rootSpan Tag.E7 L (parabolicRoots Tag.E7 (J₀ ∪ J₁)) := by
    rw [← rootSpan_union']
    refine biSup_mono (Set.union_subset ?_ ?_)
    · exact fun α hα => ⟨hα.1, fun i hi => hα.2 i fun h => hi (Or.inl h)⟩
    · exact fun α hα => ⟨hα.1, fun i hi => hα.2 i fun h => hi (Or.inr h)⟩
  have hgT : g ∈ supportedTorus Tag.E7 L (J₀ ∪ J₁) := by
    rw [← torusGroup_inf_rootSpan_parabolicRoots_E7]
    exact Subgroup.mem_inf.2 ⟨hgH, hsub hgQ⟩
  rw [supportedTorus_eq_subsystemTorus] at hgT
  have hJ : ∀ {J : Set (Fin Tag.E7.rank)} {i : Fin Tag.E7.rank}, i ∈ J → ∀ t : Lˣ,
      torusElt Tag.E7 L i t ∈
        torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J) := by
    intro J i hi t
    rw [torusGroup_inf_rootSpan_parabolicRoots_E7, supportedTorus_eq_subsystemTorus]
    exact torusElt_mem_subsystemTorus hi t
  refine (Subgroup.closure_le _).2 ?_ hgT
  rintro _ ⟨i, hi, t, rfl⟩
  rcases hi with hi | hi
  · exact Subgroup.mem_sup_left (hJ hi t)
  · exact Subgroup.mem_sup_right (hJ hi t)

theorem e7_fixedSplit_two [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr) {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {n : ModGL Tag.E7 L}
    (hn : n ∈ monomialSubgroup Tag.E7 L) (v : WeylGroup Tag.E7)
    {J₀ J₁ : Set (Fin Tag.E7.rank)}
    (hJ₀ : ∀ β ∈ parabolicRoots Tag.E7 J₀,
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • β ∈ parabolicRoots Tag.E7 J₀)
    (hJ₁ : ∀ β ∈ parabolicRoots Tag.E7 J₁,
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • β ∈ parabolicRoots Tag.E7 J₁)
    (hcomm : ∀ a ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀),
      ∀ b ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁), a * b = b * a)
    {m : ModGL Tag.E7 L}
    (hm : m ∈ torusGroup Tag.E7 L ⊔
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 J₀ ∪
        (fun γ => v • γ) '' parabolicRoots Tag.E7 J₁))
    (hθm : n * Units.map (entrywiseHom Fr) m * n⁻¹ = m) :
    ∃ t ∈ torusGroup Tag.E7 L, n * Units.map (entrywiseHom Fr) t * n⁻¹ = t ∧
      ∃ a₀ ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 J₀),
        n * Units.map (entrywiseHom Fr) a₀ * n⁻¹ = a₀ ∧
        ∃ a₁ ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 J₁),
          n * Units.map (entrywiseHom Fr) a₁ * n⁻¹ = a₁ ∧ m = t * a₀ * a₁ := by
  classical
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  have hJ₀' : ∀ β ∈ parabolicRoots Tag.E7 J₀,
      weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • β ∈ parabolicRoots Tag.E7 J₀ := by
    intro β hβ
    rw [hπn']
    exact hJ₀ β hβ
  have hJ₁' : ∀ β ∈ parabolicRoots Tag.E7 J₁,
      weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • β ∈ parabolicRoots Tag.E7 J₁ := by
    intro β hβ
    rw [hπn']
    exact hJ₁ β hβ
  let θ' : ModGL Tag.E7 L →* ModGL Tag.E7 L :=
    (MulAut.conj n').toMonoidHom.comp (Units.map (entrywiseHom Fr))
  have hθ'app : ∀ x, θ' x = n' * Units.map (entrywiseHom Fr) x * n'⁻¹ := fun x => by
    simp [θ', MulAut.conj_apply]
  have hconj : ∀ x, n * Units.map (entrywiseHom Fr) (V * x * V⁻¹) * n⁻¹ = V * θ' x * V⁻¹ := by
    intro x
    rw [conj_theta_canonicalRep hFrb n v x, hθ'app]
    simp only [hn', hV]
    group
  have hInvH : ∀ {t : ModGL Tag.E7 L}, t ∈ torusGroup Tag.E7 L →
      V⁻¹ * t * V ∈ torusGroup Tag.E7 L := by
    intro t ht
    have h := (Subgroup.mem_normalizer_iff.1
      (inv_mem (canonicalRep_mem_normalizer (R := L) v)) t).1 ht
    rwa [inv_inv] at h
  have hVH : ∀ {t : ModGL Tag.E7 L}, t ∈ torusGroup Tag.E7 L →
      V * t * V⁻¹ ∈ torusGroup Tag.E7 L :=
    fun {t} ht => (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) v) t).1 ht
  have hm' : V⁻¹ * m * V ∈ torusGroup Tag.E7 L ⊔
      (rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀) ⊔
        rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₁)) := by
    rw [← rootSpan_union']
    have hle : (torusGroup Tag.E7 L ⊔
        rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 J₀ ∪
          (fun γ => v • γ) '' parabolicRoots Tag.E7 J₁)).map
        (MulAut.conj V⁻¹).toMonoidHom ≤
        torusGroup Tag.E7 L ⊔
          rootSpan Tag.E7 L (parabolicRoots Tag.E7 J₀ ∪ parabolicRoots Tag.E7 J₁) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        simpa [MulAut.conj_apply] using hInvH ht
      · rintro _ ⟨g, hg, rfl⟩
        have := canonicalRep_inv_conj_mem_rootSpan (K := L) (τ := Tag.E7) v
          (S := (fun γ => v • γ) '' parabolicRoots Tag.E7 J₀ ∪
            (fun γ => v • γ) '' parabolicRoots Tag.E7 J₁)
          (S' := parabolicRoots Tag.E7 J₀ ∪ parabolicRoots Tag.E7 J₁)
          (by
            rintro _ (⟨α, hα, rfl⟩ | ⟨α, hα, rfl⟩)
            · exact ⟨CFSG.LieType.Chevalley.IsRoot.smul hα.1 v, Or.inl (by simpa using hα)⟩
            · exact ⟨CFSG.LieType.Chevalley.IsRoot.smul hα.1 v, Or.inr (by simpa using hα)⟩)
          hg
        simpa [MulAut.conj_apply] using this
    simpa [MulAut.conj_apply] using hle ⟨m, hm, rfl⟩
  have hθm' : θ' (V⁻¹ * m * V) = V⁻¹ * m * V := by
    have h := hconj (V⁻¹ * m * V)
    have e : V * (V⁻¹ * m * V) * V⁻¹ = m := by group
    rw [e, hθm] at h
    calc θ' (V⁻¹ * m * V) = V⁻¹ * (V * θ' (V⁻¹ * m * V) * V⁻¹) * V := by group
      _ = V⁻¹ * m * V := by rw [← h]
  have hlang : ∀ {J : Set (Fin Tag.E7.rank)},
      (∀ β ∈ parabolicRoots Tag.E7 J,
        weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • β ∈ parabolicRoots Tag.E7 J) →
      ∀ s ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J),
        ∃ t ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J),
          t⁻¹ * θ' t = s := by
    intro J hJ' s hs
    rw [torusGroup_inf_rootSpan_parabolicRoots_E7] at hs ⊢
    obtain ⟨t, ht, hts⟩ :=
      CFSG.HardMathSupport.Foote.Coordinator.exists_lang_supportedTorus_of_monomial
        hq hFr n' hn'm hJ' s hs
    exact ⟨t, ht, by rw [hθ'app]; exact hts⟩
  obtain ⟨t', ht'H, ht'θ, g₀, hg₀, hg₀θ, g₁, hg₁, hg₁θ, hm'eq⟩ := exists_fixed_split₂ θ'
    (fun a ha b hb => torusGroup_comm ha hb)
    (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => hα.1)
    (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => hα.1)
    hcomm
    (fun h hh => by rw [hθ'app]; exact theta_mem_torusGroup hFrb hn'm hh)
    (fun g hg => by rw [hθ'app]; exact theta_mem_rootSpan hFrb hn'm hJ₀' hg)
    (fun g hg => by rw [hθ'app]; exact theta_mem_rootSpan hFrb hn'm hJ₁' hg)
    (rootSpan_inf_le_torusGroup_E7 hcomm) (torusGroup_inf_sup_le_E7 J₀ J₁)
    (hlang hJ₀') (hlang hJ₁') hm' hθm'
  have hVg₀ : V * g₀ * V⁻¹ ∈
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 J₀) :=
    canonicalRep_conj_mem_rootSpan (K := L) (τ := Tag.E7) v
      (S := parabolicRoots Tag.E7 J₀) (S' := (fun γ => v • γ) '' parabolicRoots Tag.E7 J₀)
      (fun γ hγ => ⟨hγ.1, γ, hγ, rfl⟩) hg₀
  have hVg₁ : V * g₁ * V⁻¹ ∈
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 J₁) :=
    canonicalRep_conj_mem_rootSpan (K := L) (τ := Tag.E7) v
      (S := parabolicRoots Tag.E7 J₁) (S' := (fun γ => v • γ) '' parabolicRoots Tag.E7 J₁)
      (fun γ hγ => ⟨hγ.1, γ, hγ, rfl⟩) hg₁
  refine ⟨V * t' * V⁻¹, hVH ht'H, ?_, V * g₀ * V⁻¹, hVg₀, ?_, V * g₁ * V⁻¹, hVg₁, ?_, ?_⟩
  · rw [hconj, ht'θ]
  · rw [hconj, hg₀θ]
  · rw [hconj, hg₁θ]
  · calc m = V * (V⁻¹ * m * V) * V⁻¹ := by group
      _ = V * (t' * g₀ * g₁) * V⁻¹ := by rw [hm'eq]
      _ = V * t' * V⁻¹ * (V * g₀ * V⁻¹) * (V * g₁ * V⁻¹) := by group

theorem rootSpan_e7T3J_commute :
    ∀ a ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (e7T3J 0)),
      ∀ b ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (e7T3J 1)), a * b = b * a := by
  refine rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inl rfl))) (fun r hr => hr.1)
    (fun r hr => hr.1) ?_
  intro α hα β hβ
  rw [dotProduct_mulVec_eq_iform]
  rw [parabolicRoots_e7T3J (by norm_num : (0 : ℕ) < 4)] at hα
  rw [parabolicRoots_e7T3J (by norm_num : (1 : ℕ) < 4)] at hβ
  obtain ⟨l, hl, rfl⟩ := hα
  obtain ⟨l', hl', rfl⟩ := hβ
  exact e7T3_orth_A2_A1 l hl l' hl'

theorem e7_fixedSplit_A2_3A1 [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {n : ModGL Tag.E7 L}
    (hn : n ∈ monomialSubgroup Tag.E7 L) (v : WeylGroup Tag.E7)
    (hJ₀ : ∀ β ∈ parabolicRoots Tag.E7 (e7T3J 0),
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • β ∈ parabolicRoots Tag.E7 (e7T3J 0))
    (hJ₁ : ∀ β ∈ parabolicRoots Tag.E7 (e7T3J 1),
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • β ∈ parabolicRoots Tag.E7 (e7T3J 1))
    {m : ModGL Tag.E7 L}
    (hm : m ∈ torusGroup Tag.E7 L ⊔
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ∪
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1)))
    (hθm : n * Units.map (entrywiseHom Fr) m * n⁻¹ = m) :
    ∃ t ∈ torusGroup Tag.E7 L, n * Units.map (entrywiseHom Fr) t * n⁻¹ = t ∧
      ∃ a₀ ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0)),
        n * Units.map (entrywiseHom Fr) a₀ * n⁻¹ = a₀ ∧
        ∃ a₁ ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1)),
          n * Units.map (entrywiseHom Fr) a₁ * n⁻¹ = a₁ ∧ m = t * a₀ * a₁ :=
  e7_fixedSplit_two hFrb hq hFr hn v hJ₀ hJ₁ rootSpan_e7T3J_commute hm hθm

end Two

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
