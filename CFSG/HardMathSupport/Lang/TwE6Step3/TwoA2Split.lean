module

public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2
public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorus
public import CFSG.HardMathSupport.Lang.TwE6Step3.FixedSplit

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


section RootSpan

variable {τ : Tag} {K : Type} [Field K]

theorem map_mem_rootSpan (F : ModGL τ K →* ModGL τ K) (ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    {S S' : Set (Fin τ.rank → ℤ)}
    (hF : ∀ γ ∈ S, ∀ c : K, ∃ d : K, F (pinnedX τ K γ c) = pinnedX τ K (ρ γ) d)
    (hS : ∀ γ ∈ S, ρ γ ∈ S') {g : ModGL τ K} (hg : g ∈ rootSpan τ K S) :
    F g ∈ rootSpan τ K S' := by
  have hle : rootSpan τ K S ≤ (rootSpan τ K S').comap F := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hF γ hγ c
    change F (pinnedX τ K γ c) ∈ rootSpan τ K S'
    rw [hd]
    exact pinnedX_mem_rootSpan (hS γ hγ) d
  exact hle hg

theorem rootSpan_union' (A B : Set (Fin τ.rank → ℤ)) :
    rootSpan τ K (A ∪ B) = rootSpan τ K A ⊔ rootSpan τ K B := by
  simp only [rootSpan]
  exact iSup_union

theorem rootSpan_commute {A B : Set (Fin τ.rank → ℤ)}
    (h : ∀ α ∈ A, ∀ β ∈ B, ∀ x ∈ rootSubgroup τ K α, ∀ y ∈ rootSubgroup τ K β, Commute x y)
    {a b : ModGL τ K} (ha : a ∈ rootSpan τ K A) (hb : b ∈ rootSpan τ K B) : a * b = b * a := by
  have h1 : ∀ α ∈ A, ∀ x ∈ rootSubgroup τ K α,
      rootSpan τ K B ≤ Subgroup.centralizer ({x} : Set (ModGL τ K)) := by
    intro α hα x hx
    refine iSup₂_le fun β hβ => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h α hα β hβ x hx y hy).eq.symm
  have h2 : rootSpan τ K A ≤ Subgroup.centralizer (rootSpan τ K B : Set (ModGL τ K)) := by
    refine iSup₂_le fun α hα => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 α hα x hx hb)
  exact (Subgroup.mem_centralizer_iff.1 (h2 ha) b hb).symm

theorem canonicalRep_conj_mem_rootSpan (w : WeylGroup τ) {S S' : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ ∧ w • γ ∈ S') {g : ModGL τ K} (hg : g ∈ rootSpan τ K S) :
    canonicalRep (coxeterSystem τ) K w * g * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      rootSpan τ K S' := by
  have hF : ∀ γ ∈ S, ∀ c : K, ∃ d : K,
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom (pinnedX τ K γ c) =
        pinnedX τ K (w • γ) d := by
    intro γ hγ c
    obtain ⟨ε, -, hε⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (hS γ hγ).1
    exact ⟨ε * c, hε c⟩
  exact map_mem_rootSpan _ (w • ·) hF (fun γ hγ => (hS γ hγ).2) hg

theorem canonicalRep_inv_conj_mem_rootSpan (w : WeylGroup τ) {S S' : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ ∧ w⁻¹ • γ ∈ S') {g : ModGL τ K} (hg : g ∈ rootSpan τ K S) :
    (canonicalRep (coxeterSystem τ) K w)⁻¹ * g * canonicalRep (coxeterSystem τ) K w ∈
      rootSpan τ K S' := by
  have hF : ∀ γ ∈ S, ∀ c : K, ∃ d : K,
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)⁻¹).toMonoidHom (pinnedX τ K γ c) =
        pinnedX τ K (w⁻¹ • γ) d := by
    intro γ hγ c
    have hγ' : IsRoot τ (w⁻¹ • γ) := CFSG.LieType.Chevalley.IsRoot.smul (hS γ hγ).1 w⁻¹
    obtain ⟨ε, hε1, hε⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ'
    refine ⟨ε * c, ?_⟩
    have h1 := hε (ε * c)
    rw [smul_inv_smul, ← mul_assoc, hε1, one_mul] at h1
    change (canonicalRep (coxeterSystem τ) K w)⁻¹ * pinnedX τ K γ c *
      (canonicalRep (coxeterSystem τ) K w)⁻¹⁻¹ = pinnedX τ K (w⁻¹ • γ) (ε * c)
    rw [← h1]
    group
  have h := map_mem_rootSpan _ (w⁻¹ • ·) hF (fun γ hγ => (hS γ hγ).2) hg
  simpa using h

end RootSpan

theorem not_isRoot_nsmul_add_nsmul_support13_support56 {α β : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
    (hβ : β ∈ parabolicRoots Tag.E6 support56) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot Tag.E6 (a • α + b • β) := by
  intro hγ
  have h13 : ∀ i : Fin Tag.E6.rank, i ≠ 0 → i ≠ 2 → α i = 0 := fun i h0 h2 =>
    hα.2 i (by rintro (h | h); exacts [h0 h, h2 (Set.mem_singleton_iff.1 h)])
  have h56 : ∀ i : Fin Tag.E6.rank, i ≠ 4 → i ≠ 5 → β i = 0 := fun i h4 h5 =>
    hβ.2 i (by rintro (h | h); exacts [h4 h, h5 (Set.mem_singleton_iff.1 h)])
  have hval : ∀ i, (a • α + b • β) i = (a : ℤ) * α i + (b : ℤ) * β i := fun i => by
    simp [nsmul_eq_mul]
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  rcases supportA2A2_root_split _ (mem_rootFinset.2 hγ)
      ⟨by rw [hval, h13 1 (by decide) (by decide), h56 1 (by decide) (by decide)]; ring,
        by rw [hval, h13 3 (by decide) (by decide), h56 3 (by decide) (by decide)]; ring⟩ with
    ⟨h4, h5⟩ | ⟨h0, h2⟩
  · rw [hval, h13 4 (by decide) (by decide), mul_zero, zero_add] at h4
    rw [hval, h13 5 (by decide) (by decide), mul_zero, zero_add] at h5
    refine hβ.1.ne_zero (funext fun i => ?_)
    by_cases hi4 : i = 4
    · subst hi4
      exact (mul_eq_zero.1 h4).resolve_left hb'
    by_cases hi5 : i = 5
    · subst hi5
      exact (mul_eq_zero.1 h5).resolve_left hb'
    exact h56 i hi4 hi5
  · rw [hval, h56 0 (by decide) (by decide), mul_zero, add_zero] at h0
    rw [hval, h56 2 (by decide) (by decide), mul_zero, add_zero] at h2
    refine hα.1.ne_zero (funext fun i => ?_)
    by_cases hi0 : i = 0
    · subst hi0
      exact (mul_eq_zero.1 h0).resolve_left ha'
    by_cases hi2 : i = 2
    · subst hi2
      exact (mul_eq_zero.1 h2).resolve_left ha'
    exact h13 i hi0 hi2

theorem ne_of_support13_of_support56 {α β : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
    (hβ : β ∈ parabolicRoots Tag.E6 support56) : α ≠ β ∧ α ≠ -β := by
  have h0 : β 0 = 0 := hβ.2 0 (by
    rintro (h | h)
    · exact absurd h (by decide)
    · exact absurd (Set.mem_singleton_iff.1 h) (by decide))
  have h2 : β 2 = 0 := hβ.2 2 (by
    rintro (h | h)
    · exact absurd h (by decide)
    · exact absurd (Set.mem_singleton_iff.1 h) (by decide))
  have key : ∀ γ : Fin Tag.E6.rank → ℤ, γ 0 = 0 → γ 2 = 0 → α ≠ γ := by
    rintro γ hγ0 hγ2 rfl
    refine hα.1.ne_zero (funext fun i => ?_)
    by_cases hi0 : i = 0
    · subst hi0
      exact hγ0
    by_cases hi2 : i = 2
    · subst hi2
      exact hγ2
    exact hα.2 i (by rintro (h | h); exacts [hi0 h, hi2 (Set.mem_singleton_iff.1 h)])
  exact ⟨key β h0 h2, key (-β) (by simp [h0]) (by simp [h2])⟩

theorem rootSpan_support13_commute_support56 {L : Type} [Field L] {a b : ModGL Tag.E6 L}
    (ha : a ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13))
    (hb : b ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 support56)) : a * b = b * a := by
  refine rootSpan_commute ?_ ha hb
  intro α hα β hβ
  obtain ⟨hne, hne'⟩ := ne_of_support13_of_support56 hα hβ
  exact commute_of_forall_not_isRoot hα.1 hβ.1 hne hne'
    (not_isRoot_nsmul_add_nsmul_support13_support56 hα hβ) L

theorem torusGroup_inf_rootSpan_parabolicRoots (L : Type) [Field L] (J : Set (Fin Tag.E6.rank)) :
    torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J) =
      supportedTorus Tag.E6 L J := by
  rw [inf_comm, ← subsystemGroup_eq_rootSpan, subsystemGroup_inf_torusGroup_eq_supportedTorus]

section Transport

variable {L : Type} [Field L] {Fr : L →+* L}

theorem tw6Theta_inv_conj (w : WeylGroup Tag.E6) (g : ModGL Tag.E6 L) :
    tw6Theta L Fr ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * g *
      canonicalRep (coxeterSystem Tag.E6) L w) =
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * tw6ThetaConj L Fr w g *
        canonicalRep (coxeterSystem Tag.E6) L w := by
  rw [tw6ThetaConj_apply]
  group

theorem tw6ThetaConj_mem_torusGroup [IsAlgClosed L] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup Tag.E6) {h : ModGL Tag.E6 L} (hh : h ∈ torusGroup Tag.E6 L) :
    tw6ThetaConj L Fr w h ∈ torusGroup Tag.E6 L := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨b', hb', -⟩ := tw6ThetaConj_rootDiagUnit hFr w b
  rw [hb']
  exact rootDiagUnit_mem_torusGroup b'

theorem tw6ThetaConj_mem_rootSpan (w : WeylGroup Tag.E6) {J : Set (Fin Tag.E6.rank)}
    (hJ : ∀ β ∈ parabolicRoots Tag.E6 J, (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 J)
    {g : ModGL Tag.E6 L} (hg : g ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J)) :
    tw6ThetaConj L Fr w g ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J) := by
  refine map_mem_rootSpan (tw6ThetaConj L Fr w) (fun β => -((w * e6T3W * w⁻¹) • β))
    (fun γ hγ c => ?_) (fun γ hγ => neg_mem_parabolicRoots (hJ γ hγ)) hg
  obtain ⟨ε, -, hε⟩ := exists_conj_tw6Theta_pinnedX (Ω := L) (Fr := Fr) w hγ.1
  exact ⟨ε * Fr c, hε c⟩

theorem exists_lang_torusGroup_inf_rootSpan [IsAlgClosed L] {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup Tag.E6) {J : Set (Fin Tag.E6.rank)}
    (hJ : ∀ β ∈ parabolicRoots Tag.E6 J, (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 J) :
    ∀ s ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J),
      ∃ t ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J),
        t⁻¹ * tw6ThetaConj L Fr w t = s := by
  rw [torusGroup_inf_rootSpan_parabolicRoots]
  exact exists_lang_supportedTorus hq hFr w fun β hβ => neg_mem_parabolicRoots (hJ β hβ)

theorem canonicalRep_conj_mem_torusGroup_sup (w : WeylGroup Tag.E6)
    {S S' : Set (Fin Tag.E6.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot Tag.E6 γ ∧ w • γ ∈ S')
    {m : ModGL Tag.E6 L} (hm : m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S) :
    canonicalRep (coxeterSystem Tag.E6) L w * m * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ ∈
      torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S' := by
  have hle : (torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L w)).toMonoidHom ≤
        torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S' := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w) t).1 ht
    · rintro _ ⟨g, hg, rfl⟩
      exact canonicalRep_conj_mem_rootSpan w hS hg
  exact hle ⟨m, hm, rfl⟩

theorem canonicalRep_inv_conj_mem_torusGroup (w : WeylGroup Tag.E6) {t : ModGL Tag.E6 L}
    (ht : t ∈ torusGroup Tag.E6 L) :
    (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * t * canonicalRep (coxeterSystem Tag.E6) L w ∈
      torusGroup Tag.E6 L := by
  have h := (Subgroup.mem_normalizer_iff.1 (inv_mem (canonicalRep_mem_normalizer w)) t).1 ht
  rwa [inv_inv] at h

theorem smul_mem_of_mem_image_inv_smul (w : WeylGroup Tag.E6) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) :
    ∀ γ ∈ (fun α => w⁻¹ • α) '' S, IsRoot Tag.E6 γ ∧ w • γ ∈ S := by
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨CFSG.LieType.Chevalley.IsRoot.smul (hS α hα) w⁻¹, by simpa using hα⟩

end Transport

theorem fixedSplit_of_block {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hT : ∀ β ∈ parabolicRoots Tag.E6 J, (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 J)
    {m : ModGL Tag.E6 L} (hm : m ∈ torusGroup Tag.E6 L ⊔
      rootSpan Tag.E6 L ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 J))
    (hθm : tw6Theta L Fr m = m) :
    ∃ t ∈ torusGroup Tag.E6 L, tw6Theta L Fr t = t ∧
      ∃ a ∈ rootSpan Tag.E6 L ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 J),
        tw6Theta L Fr a = a ∧ m = t * a := by
  have hm' := canonicalRep_conj_mem_torusGroup_sup w
    (smul_mem_of_mem_image_inv_smul w fun α hα => hα.1) hm
  have hθm' : tw6ThetaConj L Fr w (canonicalRep (coxeterSystem Tag.E6) L w * m *
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) L w * m * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
    rw [tw6ThetaConj_conj, hθm]
  obtain ⟨t', ht'H, ht'θ, g, hg, hgθ, hm'eq⟩ := exists_fixed_split (tw6ThetaConj L Fr w)
    (fun a ha b hb => torusGroup_comm ha hb)
    (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => hα.1)
    (fun h hh => tw6ThetaConj_mem_torusGroup hFr w hh)
    (fun g hg => tw6ThetaConj_mem_rootSpan w hT hg)
    (exists_lang_torusGroup_inf_rootSpan hq hFr w hT) hm' hθm'
  refine ⟨_, canonicalRep_inv_conj_mem_torusGroup w ht'H, by rw [tw6Theta_inv_conj, ht'θ], _,
    canonicalRep_inv_conj_mem_rootSpan (S := parabolicRoots Tag.E6 J)
      (S' := (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 J) w
      (fun γ hγ => ⟨hγ.1, γ, hγ, rfl⟩) hg, by rw [tw6Theta_inv_conj, hgθ], ?_⟩
  set n := canonicalRep (coxeterSystem Tag.E6) L w
  calc m = n⁻¹ * (n * m * n⁻¹) * n := by group
    _ = n⁻¹ * (t' * g) * n := by rw [hm'eq]
    _ = n⁻¹ * t' * n * (n⁻¹ * g * n) := by group

theorem twoA2Split_of_blocks {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {w : WeylGroup Tag.E6}
    (hT13 : ∀ β ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
    (hT56 : ∀ β ∈ parabolicRoots Tag.E6 support56,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support56) :
    TwoA2Split L Fr ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
      ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56) := by
  intro m hm hθm
  have hm' := canonicalRep_conj_mem_torusGroup_sup
    (S' := parabolicRoots Tag.E6 CFSG.RankThree.E6.support13 ∪ parabolicRoots Tag.E6 support56) w
    (by
      rw [Set.forall_mem_union]
      exact ⟨fun γ hγ => (smul_mem_of_mem_image_inv_smul w (fun α hα => hα.1) γ hγ).imp_right
          Or.inl,
        fun γ hγ => (smul_mem_of_mem_image_inv_smul w (fun α hα => hα.1) γ hγ).imp_right
          Or.inr⟩) hm
  rw [rootSpan_union'] at hm'
  have hθm' : tw6ThetaConj L Fr w (canonicalRep (coxeterSystem Tag.E6) L w * m *
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) L w * m * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
    rw [tw6ThetaConj_conj, hθm]
  have h13A : CFSG.RankThree.E6.support13 ⊆ supportA2A2 := by
    rintro i (h | h) <;> rw [mem_supportA2A2]
    · exact Or.inl h
    · exact Or.inr (Or.inl (Set.mem_singleton_iff.1 h))
  have h56A : support56 ⊆ supportA2A2 := by
    rintro i (h | h) <;> rw [mem_supportA2A2]
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.1 h)))
  have hQ₁₂ : rootSpan Tag.E6 L (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13) ⊓
      rootSpan Tag.E6 L (parabolicRoots Tag.E6 support56) ≤ torusGroup Tag.E6 L := by
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
    have hgS : g ∈ subsystemGroup Tag.E6 L CFSG.RankThree.E6.support13 := by
      rw [subsystemGroup_eq_rootSpan]
      exact hg₁
    have hc : (⟨g, hgS⟩ : subsystemGroup Tag.E6 L CFSG.RankThree.E6.support13) ∈
        Subgroup.center (subsystemGroup Tag.E6 L CFSG.RankThree.E6.support13) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hh : (h : ModGL Tag.E6 L) ∈
          rootSpan Tag.E6 L (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13) :=
        (subsystemGroup_eq_rootSpan (K := L) CFSG.RankThree.E6.support13).le h.2
      exact rootSpan_support13_commute_support56 hh hg₂
    have h3 := mem_supportedTorus_of_mem_center hc
    rw [← subsystemGroup_inf_torusGroup_eq_supportedTorus] at h3
    exact (Subgroup.mem_inf.1 h3).2
  have hHQ12 : torusGroup Tag.E6 L ⊓
      (rootSpan Tag.E6 L (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13) ⊔
        rootSpan Tag.E6 L (parabolicRoots Tag.E6 support56)) ≤
      (torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)) ⊔
        (torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 support56)) := by
    intro g hg
    obtain ⟨hgH, hgQ⟩ := Subgroup.mem_inf.1 hg
    have hsub : rootSpan Tag.E6 L (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13) ⊔
        rootSpan Tag.E6 L (parabolicRoots Tag.E6 support56) ≤
          rootSpan Tag.E6 L (parabolicRoots Tag.E6 supportA2A2) := by
      rw [← rootSpan_union']
      refine biSup_mono (Set.union_subset ?_ ?_)
      · exact fun α hα => ⟨hα.1, fun i hi => hα.2 i fun h => hi (h13A h)⟩
      · exact fun α hα => ⟨hα.1, fun i hi => hα.2 i fun h => hi (h56A h)⟩
    have hgT : g ∈ supportedTorus Tag.E6 L supportA2A2 := by
      rw [← torusGroup_inf_rootSpan_parabolicRoots]
      exact Subgroup.mem_inf.2 ⟨hgH, hsub hgQ⟩
    rw [supportedTorus_eq_subsystemTorus] at hgT
    have hJ : ∀ {J : Set (Fin Tag.E6.rank)} {i : Fin Tag.E6.rank}, i ∈ J → ∀ t : Lˣ,
        torusElt Tag.E6 L i t ∈
          torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 J) := by
      intro J i hi t
      rw [torusGroup_inf_rootSpan_parabolicRoots, supportedTorus_eq_subsystemTorus]
      exact torusElt_mem_subsystemTorus hi t
    refine (Subgroup.closure_le _).2 ?_ hgT
    rintro _ ⟨i, hi, t, rfl⟩
    rw [mem_supportA2A2] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left
        (hJ (J := CFSG.RankThree.E6.support13) (Or.inl rfl) t)
    · exact Subgroup.mem_sup_left
        (hJ (J := CFSG.RankThree.E6.support13) (Or.inr rfl) t)
    · exact Subgroup.mem_sup_right (hJ (J := support56) (Or.inl rfl) t)
    · exact Subgroup.mem_sup_right (hJ (J := support56) (Or.inr rfl) t)
  obtain ⟨t', ht'H, ht'θ, g₁, hg₁, hg₁θ, g₂, hg₂, hg₂θ, hm'eq⟩ :=
    exists_fixed_split₂ (tw6ThetaConj L Fr w) (fun a ha b hb => torusGroup_comm ha hb)
      (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => hα.1)
      (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => hα.1)
      (fun a ha b hb => rootSpan_support13_commute_support56 ha hb)
      (fun h hh => tw6ThetaConj_mem_torusGroup hFr w hh)
      (fun g hg => tw6ThetaConj_mem_rootSpan w hT13 hg)
      (fun g hg => tw6ThetaConj_mem_rootSpan w hT56 hg) hQ₁₂ hHQ12
      (exists_lang_torusGroup_inf_rootSpan hq hFr w hT13)
      (exists_lang_torusGroup_inf_rootSpan hq hFr w hT56) hm' hθm'
  refine ⟨_, canonicalRep_inv_conj_mem_torusGroup w ht'H, by rw [tw6Theta_inv_conj, ht'θ], _,
    canonicalRep_inv_conj_mem_rootSpan (S := parabolicRoots Tag.E6 CFSG.RankThree.E6.support13)
      (S' := (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 CFSG.RankThree.E6.support13) w
      (fun γ hγ => ⟨hγ.1, γ, hγ, rfl⟩) hg₁, by rw [tw6Theta_inv_conj, hg₁θ], _,
    canonicalRep_inv_conj_mem_rootSpan (S := parabolicRoots Tag.E6 support56)
      (S' := (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56) w
      (fun γ hγ => ⟨hγ.1, γ, hγ, rfl⟩) hg₂, by rw [tw6Theta_inv_conj, hg₂θ], ?_⟩
  set n := canonicalRep (coxeterSystem Tag.E6) L w
  calc m = n⁻¹ * (n * m * n⁻¹) * n := by group
    _ = n⁻¹ * (t' * g₁ * g₂) * n := by rw [hm'eq]
    _ = n⁻¹ * t' * n * (n⁻¹ * g₁ * n) * (n⁻¹ * g₂ * n) := by group

theorem linesOfType_A2A2 : LinesOfType IsA2A2Kernel := by
  intro ℓ f _ K _ _ _ hf hK σ hσ p _ hp3 hpq L _ _ _ _ g0 hg0C hg0 hperf E hE hEc c hT y hy hy1
    hA2A2 k hk
  obtain ⟨w, hw⟩ := hA2A2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  have hFr : ∀ c, (iterateFrobenius L ℓ f) c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hvS := tw6_torusRootKernel_smul_stable hFr (hT y hy)
  have hT' : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨hT13, hT56⟩ := conj_e6T3W_preserves_blocks hT'
  have hq : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  exact le_hyperClosure_of_kernel_A2A2 K hf hK σ hσ hp3 hpq L hg0C hg0 hperf hE hEc c hT hy hy1
    hw (twoA2Split_of_blocks hq hFr hT13 hT56) hk

end CFSG.HardMathSupport.Lang.TwE6Step3
