module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInputs

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.Fischer

section Pure

theorem map_conj_eq_of_mem {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_pCoreOf_eq {G : Type*} [Group G] (P : Subgroup G) (p : ℕ) {g : G} (hg : g ∈ P) :
    ((CFSG.pCore p P).map P.subtype).map (MulAut.conj g).toMonoidHom =
      (CFSG.pCore p P).map P.subtype := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(⟨g, hg⟩ : P) * y * (⟨g, hg⟩ : P)⁻¹, (CFSG.pCore_normal).conj_mem y hy ⟨g, hg⟩, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, ⟨(⟨g, hg⟩ : P)⁻¹ * y * (⟨g, hg⟩ : P), by
      simpa using (CFSG.pCore_normal).conj_mem y hy (⟨g, hg⟩ : P)⁻¹, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem planeClosure_eq_closure_fixUnion {G : Type*} [Group G] (E : Subgroup (MulAut G)) :
    CFSG.LieType.SeitzGeneration.planeClosure E = Subgroup.closure (fixUnion E) := by
  unfold CFSG.LieType.SeitzGeneration.planeClosure
  congr 1
  ext k
  constructor
  · rintro ⟨e, he, he1, hek⟩
    exact ⟨Subgroup.zpowers e, Subgroup.zpowers_le.2 he, mt Subgroup.zpowers_eq_bot.1 he1,
      fun φ hφ => (Subgroup.zpowers_le.2 (mem_fixAut.2 hek)) hφ⟩
  · rintro ⟨F, hFE, hF1, hF⟩
    obtain ⟨⟨φ, hφF⟩, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    exact ⟨φ, hFE hφF, fun h => hφ1 (Subtype.ext h), hF φ hφF⟩

end Pure

section LongRoot


@[expose] def TwE6InnerLineLongRoot : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
      ∀ D : TwLangData K σ q (twPlanePre K σ E), D.IsRegular →
        ∃ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm ∧
          (∀ ε ∈ E, (twE6LongRootSL2 X Xm).map ε.toMonoidHom = twE6LongRootSL2 X Xm) ∧
          ∃ e ∈ E, e ≠ 1 ∧ (∀ u ∈ twE6LongRootSL2 X Xm, e u = u) ∧
            ∃ R : Subgroup (twistedE6RootGroup K σ), R ≤ twE6LongRootRadical X ∧
              (∀ u ∈ R, e u = u) ∧ ¬ R ≤ X

@[expose] def TwE6LeviPlaneGeneration : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm →
      ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), CFSG.IsElementaryAbelian 3 E →
        Nat.card E = 3 ^ 2 →
        (∀ ε ∈ E, (twE6LongRootSL2 X Xm).map ε.toMonoidHom = twE6LongRootSL2 X Xm) →
        twE6LongRootLevi X Xm ≤ CFSG.LieType.SeitzGeneration.planeClosure E

theorem twE6DiagRegularGen_of_longRoot (hQ1 : TwE6LongRootParabolicStructure)
    (hQ2 : TwE6LongRootIrreducible) (hQ4 : TwE6LongRootGenerates)
    (hSA : TwE6InnerLineLongRoot) (hJ : TwE6LeviPlaneGeneration) : TwE6DiagRegularGen := by
  intro K _ _ σ q hK3 hσ hK E hE hEab hcard hnin D hreg
  classical
  obtain ⟨X, Xm, hpair, hSinv, e, heE, he1, hSfix, R, hRQ, hRfix, hRX⟩ :=
    hSA K σ q hK3 hσ hK E hE hEab hcard hnin D hreg
  have hXQ := hQ1 K σ q hK3 hσ hK X Xm hpair
  have hJH := hJ K σ q hK3 hσ hK X Xm hpair E hEab hcard hSinv
  rw [planeClosure_eq_closure_fixUnion] at hJH
  obtain ⟨n, hnS, hn⟩ := hQ4 K σ q hK3 hσ hK X Xm hpair
  set H : Subgroup (twistedE6RootGroup K σ) := Subgroup.closure (fixUnion E) with hH
  have hfixH : ∀ u, e u = u → u ∈ H := fun u hu =>
    Subgroup.subset_closure (mem_fixUnion_of_fixed heE he1 hu)
  have hSH : twE6LongRootSL2 X Xm ≤ H := fun u hu => hfixH u (hSfix u hu)
  have hXS : X ≤ twE6LongRootSL2 X Xm := fun u hu => Subgroup.subset_closure (Or.inl hu)
  have hTS : twE6LongRootTorus X Xm ≤ twE6LongRootSL2 X Xm := inf_le_left.trans inf_le_left
  have hRH : R ≤ H := fun u hu => hfixH u (hRfix u hu)
  have hJP : twE6LongRootLevi X Xm ≤ twE6LongRootParabolic X := by
    have h1 : twE6LongRootLevi X Xm ≤
        Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    have h2 : Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) ≤
        Subgroup.centralizer (X : Set (twistedE6RootGroup K σ)) :=
      Subgroup.centralizer_le (fun u hu => hXS hu)
    exact h1.trans (h2.trans (Subgroup.centralizer_le_normalizer _))
  have hTP : twE6LongRootTorus X Xm ≤ twE6LongRootParabolic X := inf_le_left.trans inf_le_right
  have hJTP : twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm ≤ twE6LongRootParabolic X :=
    sup_le hJP hTP
  have hJTH : twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm ≤ H :=
    sup_le hJH (hTS.trans hSH)
  have hMnorm : ∀ g ∈ twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm,
      (H ⊓ twE6LongRootRadical X).map (MulAut.conj g).toMonoidHom = H ⊓ twE6LongRootRadical X := by
    intro g hg
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_eq_of_mem H (hJTH hg)]
    congr 1
    exact map_conj_pCoreOf_eq (twE6LongRootParabolic X) (ringChar K) (hJTP hg)
  have hXM : X ≤ H ⊓ twE6LongRootRadical X := le_inf (hXS.trans hSH) hXQ
  rcases hQ2 K σ q hK3 hσ hK X Xm hpair (H ⊓ twE6LongRootRadical X) hXM inf_le_right hMnorm with
    hMX | hMQ
  · exfalso
    apply hRX
    intro u hu
    have hu' : u ∈ H ⊓ twE6LongRootRadical X := ⟨hRH hu, hRQ hu⟩
    rw [hMX] at hu'
    exact hu'
  · have hQH : twE6LongRootRadical X ≤ H := by
      intro u hu
      have : u ∈ H ⊓ twE6LongRootRadical X := by
        rw [hMQ]
        exact hu
      exact this.1
    rw [← top_le_iff, ← hn, Subgroup.closure_le]
    rintro u (hu | ⟨v, hv, rfl⟩)
    · exact hQH hu
    · exact H.mul_mem (H.mul_mem (hSH hnS) (hQH hv)) (H.inv_mem (hSH hnS))

end LongRoot

end CFSG.LieType.SeitzGeneration.ExcWideThree
