module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternBasic
public import CFSG.ClassicalInvolution.Balance.LayerGenerationRoots
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdMain
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.CurtisTits (rankOne)

variable {p f : ℕ} [Fact p.Prime]

namespace TypeEPattern

theorem range_le_iSup_fund_simplyLaced {t : StatedLieTag} {n : ℕ}
    (hfund : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t)
    (hadm : StatedLieAdmissible t n p f)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) {X : Type} [Group X]
    (ψ : (modelUniv t n p f Fact.out).K →* X) :
    ψ.range ≤ ⨆ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D, R.map ψ := by
  rw [← Balance.iSup_rankOneImage_eq_range t n p f Fact.out hfund hadm ψ 1]
  refine iSup₂_le fun γ hγ => ?_
  exact le_iSup₂_of_le (Balance.rankOneRoot (modelUniv t n p f Fact.out).D 1 γ)
    ⟨1, γ, Or.inl (Balance.isLongestRoot_of_mem_roots_simplyLaced t n p f Fact.out hfund hadm ht
      hγ), rfl⟩ le_rfl

theorem map_eq_of_forall_mem {Y : Type} [Group Y] (σ : Y ≃* Y) (hσ2 : ∀ y, σ (σ y) = y)
    {S : Subgroup Y} (h : ∀ y ∈ S, σ y ∈ S) : S.map σ.toMonoidHom = S := by
  refine le_antisymm ?_ fun y hy => ⟨σ y, h y hy, hσ2 y⟩
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

theorem conjSub_map_equiv {A B : Type} [Group A] [Group B] (ι : A ≃* B) (k : A)
    (S : Subgroup A) :
    conjSub (ι k) (S.map ι.toMonoidHom) =
      (S.map (MulAut.conj k).toMonoidHom).map ι.toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem charOf_comp_equiv {r m : ℕ} (e : Fin r ≃ Fin m) (v : Fin m → ZMod 2) (γ : Fin r → ℤ) :
    charOf (v ∘ e) γ = ∑ i, ((γ ∘ e.symm) i : ZMod 2) * v i := by
  unfold charOf
  rw [← Equiv.sum_comp e (fun j : Fin m => ((γ ∘ e.symm) j : ZMod 2) * v j)]
  simp

end TypeEPattern

section Toral

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

@[expose] def ToralNormalE (c : ETCtx p f tY nY Ω K z) {t : G} (ht : t * z * t⁻¹ = z) : Prop :=
  ∃ (k₀ : (modelUniv tY nY p f Fact.out).K)
    (v : Fin (modelUniv tY nY p f Fact.out).D.rank → ZMod 2),
    ∀ γ ∈ (modelUniv tY nY p f Fact.out).D.roots,
      ((conjSub k₀ ((modelUniv tY nY p f Fact.out).D.rootGroup γ ⊔
          (modelUniv tY nY p f Fact.out).D.rootGroup (-γ))).map c.d.ψ).map
          (Gaps.locAut c.hΩ.conjInvariant ht).toMonoidHom =
        (conjSub k₀ ((modelUniv tY nY p f Fact.out).D.rootGroup γ ⊔
          (modelUniv tY nY p f Fact.out).D.rootGroup (-γ))).map c.d.ψ ∧
      ((∀ x ∈ (conjSub k₀ ((modelUniv tY nY p f Fact.out).D.rootGroup γ ⊔
          (modelUniv tY nY p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)

theorem ETCtx.fixed_of_commutes (c : ETCtx p f tY nY Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    {β M : Subgroup G} (htβ : IsClassicalMember p f β t) (hM : M ∈ centralizingMembers Ω {z})
    (hMβ : Commutes β M) :
    ∀ x ∈ locImg Ω z M, Gaps.locAut c.hΩ.conjInvariant ht x = x :=
  (Gaps.locAut_fixed_iff c.hΩ c.hP1 ht hM).mp fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t htβ.mem n hn).symm

@[expose] def TorusFixedE7 (c : ETCtx p f .E7 0 Ω K z) {t : G} (ht : t * z * t⁻¹ = z) : Prop :=
  ∃ k₀ : ↥(Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f)),
    (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup
        ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank) :
          Subgroup ↥(Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f))) =
      conjSub k₀ ((Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup
        CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7 ⊔
        (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup
          (-CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7)) ∧
    ∀ j : Fin 7, j ≠ 0 → ∀ h ∈ Steinberg.Minuscule.e7Data_valid.torus (GaloisField p f) j,
      Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ (k₀ * h * k₀⁻¹)) = c.d.ψ (k₀ * h * k₀⁻¹)

theorem ETCtx.toralNormal_E7 (c : ETCtx p f .E7 0 Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hfix0 : ∀ x ∈ (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup
        ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank)).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant htz x = x) (hT : TorusFixedE7 c htz) :
    ToralNormalE c htz := by
  obtain ⟨k₀, hframe, H2⟩ := hT
  have H1 : ∀ y ∈ (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup
        CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7 ⊔
        (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup
          (-CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7),
      Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ (k₀ * y * k₀⁻¹)) = c.d.ψ (k₀ * y * k₀⁻¹) := by
    intro y hy
    refine hfix0 _ ⟨k₀ * y * k₀⁻¹, ?_, rfl⟩
    have : k₀ * y * k₀⁻¹ ∈ conjSub k₀ ((Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup
        CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7 ⊔
        (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup
          (-CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7)) := conj_mem_conjSub hy
    rw [← hframe] at this
    exact this
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr c.hf, rfl⟩
  have hgen := TypeEPattern.range_le_iSup_fund_simplyLaced (p := p) (f := f) (t := .E7) (n := 0)
    trivial hadm (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) c.d.ψ
  have hσ2 := Gaps.locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr := fun k => c.locAut_mem_range htz h2t hKt hgen k
  have hq5 : 5 ≤ Nat.card (GaloisField p f) := by rw [c.card_eq]; exact c.hq
  obtain ⟨v, hv⟩ := ModelFacts.ChevAut.toral_std_E7 (F := GaloisField p f) c.hp2 hq5 c.d.ψ
    c.d.ker_le (Gaps.locAut c.hΩ.conjInvariant htz) hσ2 hσr k₀ H2 H1
  refine ⟨k₀, v, fun γ hγ => ?_⟩
  obtain ⟨hn, hi⟩ := hv γ hγ
  exact ⟨TypeEPattern.map_eq_of_forall_mem _ hσ2 hn, hi⟩

@[expose] def IsoCompatP {m : ℕ} (hm3 : 3 ≤ m)
    (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    (ι : spinGroup (quadPlus m (GaloisField p f)) ≃*
      (modelUniv .POmegaPlus m p f Fact.out).K) : Prop :=
  ∀ γ : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ℤ,
    (γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots ↔
      (γ ∘ e.symm) ∈ (plusDatum m (GaloisField p f) hm3).roots) ∧
    (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm)).map ι.toMonoidHom

theorem exists_isoCompatP {m : ℕ} (hm3 : 3 ≤ m) :
    ∃ (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
      (ι : spinGroup (quadPlus m (GaloisField p f)) ≃*
        (modelUniv .POmegaPlus m p f Fact.out).K), IsoCompatP hm3 e ι := by
  unfold IsoCompatP
  rw [modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
  exact ⟨Equiv.refl _, MulEquiv.refl _, fun γ => ⟨Iff.rfl, (Subgroup.map_id _).symm⟩⟩

@[expose] def TorusFixedP {m : ℕ} (hm3 : 3 ≤ m) (c : ETCtx p f .POmegaPlus m Ω K z)
    (a₀ : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank) {t : G}
    (htz : t * z * t⁻¹ = z) : Prop :=
  ∃ (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    (ι : spinGroup (quadPlus m (GaloisField p f)) ≃* (modelUniv .POmegaPlus m p f Fact.out).K),
    IsoCompatP hm3 e ι ∧
    ∃ (i₀ i₁ : Fin m) (_ : i₀ ≠ i₁) (γ₀ : Fin m → ℤ) (s₀ t₀ : Bool)
      (_ : toStdD m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
      (k : spinGroup (quadPlus m (GaloisField p f)))
      (T : Subgroup (spinGroup (quadPlus m (GaloisField p f)))),
      ((((plusDatum m (GaloisField p f) hm3).rootGroup γ₀ ⊔
          (plusDatum m (GaloisField p f) hm3).rootGroup (-γ₀)).map
            (MulAut.conj k).toMonoidHom).map ι.toMonoidHom =
        rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a₀) ∧
      (∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ u : (GaloisField p f)ˣ,
        (plusFrame m (GaloisField p f) hm3).longTorus hij true false u ∈ T) ∧
      (∀ x ∈ T, Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ (ι (k * x * k⁻¹))) =
        c.d.ψ (ι (k * x * k⁻¹)))

theorem ETCtx.toralNormal_plus {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m)
    (c : ETCtx p f .POmegaPlus m Ω K z) {t : G} (htz : t * z * t⁻¹ = z) (h2t : t * t = 1)
    (hKt : conjSub t K = K) (a₀ : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank)
    (hfix0 : ∀ x ∈ (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a₀).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant htz x = x) (hT : TorusFixedP hm3 c a₀ htz) :
    ToralNormalE c htz := by
  classical
  obtain ⟨e, ι, hc, i₀, i₁, h01, γ₀, s₀, t₀, hγ₀, k, T, hframe, hTT, H2⟩ := hT
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hF : Nat.card (GaloisField p f) = p ^ f := c.card_eq
  have hq : 5 ≤ Nat.card (GaloisField p f) := by rw [hF]; exact c.hq
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
  let θ : spinGroup (quadPlus m (GaloisField p f)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m (GaloisField p f))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have H1 : ∀ y ∈ (((plusDatum m (GaloisField p f) hm3).rootGroup γ₀ ⊔
      (plusDatum m (GaloisField p f) hm3).rootGroup (-γ₀)).map (MulAut.conj k).toMonoidHom),
      Gaps.locAut c.hΩ.conjInvariant htz (θ y) = θ y := by
    intro y hy
    refine hfix0 _ ⟨ι y, ?_, rfl⟩
    rw [← hframe]
    exact ⟨y, hy, rfl⟩
  have hσ2 : ∀ y, Gaps.locAut c.hΩ.conjInvariant htz (Gaps.locAut c.hΩ.conjInvariant htz y) = y :=
    Gaps.locAut_locAut c.hΩ.conjInvariant htz h2t
  have hgen := TypeEPattern.range_le_iSup_fund_simplyLaced (p := p) (f := f) (t := .POmegaPlus)
    (n := m) trivial hadm (Or.inr (Or.inl rfl)) c.d.ψ
  have hσr : ∀ k', Gaps.locAut c.hΩ.conjInvariant htz (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := c.locAut_mem_range htz h2t hKt hgen (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  obtain ⟨k₀, v', hk₀⟩ := ModelFacts.OrthAut.toralNormal_plus_of_subgroups c.hp2 hf1 hF hq hm hm3
    θ hker (Gaps.locAut c.hΩ.conjInvariant htz) hσ2 hσr h01 hγ₀ k H1 T hTT H2
  refine ⟨ι k₀, v' ∘ e, fun γ hγ => ?_⟩
  have hγ' : γ ∘ e.symm ∈ (plusDatum m (GaloisField p f) hm3).roots := (hc γ).1.mp hγ
  obtain ⟨hnorm, hfix⟩ := hk₀ (γ ∘ e.symm) hγ'
  have hG₁ : (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm)).map ι.toMonoidHom :=
    (hc γ).2
  have hG₂ : (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ) =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm))).map ι.toMonoidHom :=
    (hc (-γ)).2
  have hRG : conjSub (ι k₀) ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ)) =
      (((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map ι.toMonoidHom := by
    rw [hG₁, hG₂, ← Subgroup.map_sup]
    exact TypeEPattern.conjSub_map_equiv ι k₀ _
  have himg : (conjSub (ι k₀) ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ =
      (((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map θ := by
    rw [hRG, Subgroup.map_map]
  rw [himg]
  refine ⟨hnorm, hfix.trans ?_⟩
  rw [TypeEPattern.charOf_comp_equiv]

end Toral

end CFSG.ClassicalInvolution.RouteD
