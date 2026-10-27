module

public import CFSG.ClassicalInvolution.RouteD.GapsToralD

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv
  IsLongestRoot)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Equiv

variable {A B : Type} [Group A] [Group B]

theorem commutes_map_equiv (ι : A ≃* B) {R R' : Subgroup A} :
    Commutes (R.map ι.toMonoidHom) (R'.map ι.toMonoidHom) ↔ Commutes R R' := by
  constructor
  · intro h a ha b hb
    have := h (ι a) ⟨a, ha, rfl⟩ (ι b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact ι.injective this
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show ι a * ι b = ι b * ι a
    rw [← map_mul, ← map_mul, h a ha b hb]

theorem ModelAdj.map_equiv (ι : A ≃* B) {R R' : Subgroup A}
    (h : ModelAdj (Subgroup.center A) R R') :
    ModelAdj (Subgroup.center B) (R.map ι.toMonoidHom) (R'.map ι.toMonoidHom) := by
  obtain ⟨hne, hnc, r, r', hr, hr', hc, hn⟩ := h
  have hinv : ∀ {S : Subgroup A} {s : A}, InvOf S s → InvOf (S.map ι.toMonoidHom) (ι s) :=
    fun {S s} hs => ⟨⟨s, hs.1, rfl⟩, by rw [MulEquiv.orderOf_eq]; exact hs.2⟩
  refine ⟨fun e => hne (Subgroup.map_injective ι.injective e),
    fun hc' => hnc ((commutes_map_equiv ι).mp hc'), ι r, ι r', hinv hr, hinv hr', ?_, ?_⟩
  · rw [← map_commutatorElement]
    exact (MulEquivClass.apply_mem_center_iff ι).mpr hc
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨r' * x * r'⁻¹, hn x hx, ?_⟩
    simp [map_mul, map_inv]

theorem linearBlockStandardPair_map_equiv {F : Type} [Field F] (ι : A ≃* B) {W U V : Subgroup A}
    (h : LinearBlockStandardPair F W U V) :
    LinearBlockStandardPair F (W.map ι.toMonoidHom) (U.map ι.toMonoidHom)
      (V.map ι.toMonoidHom) := by
  obtain ⟨θ, c, hrange, hker, hUV⟩ := h
  refine ⟨ι.toMonoidHom.comp θ, c, by rw [MonoidHom.range_comp, hrange], ?_, ?_⟩
  · intro s hs
    have h1 : θ s = 1 := by
      have : ι (θ s) = 1 := hs
      exact ι.injective (by rw [this, map_one])
    exact hker (MonoidHom.mem_ker.mpr h1)
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← Subgroup.map_map, h1], by rw [← Subgroup.map_map, h2]⟩
    · exact Or.inr ⟨by rw [← Subgroup.map_map, h1], by rw [← Subgroup.map_map, h2]⟩

end Equiv

section Fund

variable {p f m : ℕ} [Fact p.Prime]

theorem isLongestRoot_model (hm3 : 3 ≤ m) {γ : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ℤ}
    (hγ : γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots) :
    IsLongestRoot (modelUniv .POmegaPlus m p f Fact.out).D γ := by
  revert γ
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
  intro γ hγ
  exact RouteD.isLongestRoot_of_mem_roots_plusDatum hm3 hγ

theorem map_mem_fund_iso (hm3 : 3 ≤ m)
    {e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m}
    {ι : spinGroup (quadPlus m (GaloisField p f)) ≃* (modelUniv .POmegaPlus m p f Fact.out).K}
    (hc : IsoCompatPlus hm3 e ι)
    {R : Subgroup (spinGroup (quadPlus m (GaloisField p f)))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) :
    R.map ι.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus m p f Fact.out).D := by
  obtain ⟨g, γ', hγ', rfl⟩ := hR
  have hγ'long : IsLongestRoot (plusDatum m (GaloisField p f) hm3) γ' := by
    rcases hγ' with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  let γ : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ℤ := fun i => γ' (e i)
  have hγe : γ ∘ e.symm = γ' := by
    funext i
    simp [γ]
  have hroot : γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots :=
    ((hc γ).1).mpr (by rw [hγe]; exact hγ'long.1)
  refine ⟨ι g, γ, Or.inl (isLongestRoot_model hm3 hroot), ?_⟩
  have hγe' : (-γ) ∘ e.symm = -γ' := by
    funext i
    show -(γ (e.symm i)) = -(γ' i)
    simp [γ]
  have h1 : (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ =
      ((plusDatum m (GaloisField p f) hm3).rootGroup γ').map ι.toMonoidHom := by
    rw [(hc γ).2]
    exact congrArg (fun δ => ((plusDatum m (GaloisField p f) hm3).rootGroup δ).map
      ι.toMonoidHom) hγe
  have h2 : (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ) =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (-γ')).map ι.toMonoidHom := by
    rw [(hc (-γ)).2]
    exact congrArg (fun δ => ((plusDatum m (GaloisField p f) hm3).rootGroup δ).map
      ι.toMonoidHom) hγe'
  rw [h1, h2, ← Subgroup.map_sup]
  exact CFSG.ClassicalInvolution.ModelFacts.map_conj_map ι.toMonoidHom g _

theorem map_symm_mem_fund_iso (hm3 : 3 ≤ m)
    {e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m}
    {ι : spinGroup (quadPlus m (GaloisField p f)) ≃* (modelUniv .POmegaPlus m p f Fact.out).K}
    (hc : IsoCompatPlus hm3 e ι)
    {R : Subgroup (modelUniv .POmegaPlus m p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) :
    R.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField p f) hm3) := by
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hγlong : γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots := by
    rcases hγ with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h.1
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  have hroot : γ ∘ e.symm ∈ (plusDatum m (GaloisField p f) hm3).roots := ((hc γ).1).mp hγlong
  refine ⟨ι.symm g, γ ∘ e.symm, Or.inl (RouteD.isLongestRoot_of_mem_roots_plusDatum hm3 hroot),
    ?_⟩
  have h1 : ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ).map ι.symm.toMonoidHom =
      (plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm) := by
    rw [(hc γ).2, Subgroup.map_map]
    have : ι.symm.toMonoidHom.comp ι.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have h2 : ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ)).map ι.symm.toMonoidHom =
      (plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm)) := by
    rw [(hc (-γ)).2, Subgroup.map_map]
    have : ι.symm.toMonoidHom.comp ι.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
    rfl
  show ((conjSub g _).map ι.symm.toMonoidHom) = conjSub (ι.symm g) _
  rw [conjSub, conjSub, CFSG.ClassicalInvolution.ModelFacts.map_conj_map, Subgroup.map_sup, h1, h2]
  rfl

end Fund

end CFSG.ClassicalInvolution.RouteD.Gaps
