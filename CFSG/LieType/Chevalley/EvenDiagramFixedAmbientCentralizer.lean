module

public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem diagram_fixed_ambient_centralizer_trivial_of_three_le
    (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hq : 3 ≤ p ^ f) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] (ι : K →+* L) :
    Function.Injective (baseChangeGL (τ := t.tag) ι) ∧
    (graphFixedRootGroup t K σ).map (baseChangeGL ι) ≤ adjointGroup t.tag L ∧
    (∀ z ∈ adjointGroup t.tag L, (∀ h ∈ (graphFixedRootGroup t K σ).map (baseChangeGL ι),
      z * h = h * z) → z = 1) ∧
    Function.Injective (conjNormalizerHom (adjointGroup t.tag L)
      ((graphFixedRootGroup t K σ).map (baseChangeGL ι))) := by
  classical
  set q := p ^ f
  set H := (graphFixedRootGroup t K σ).map (baseChangeGL ι)
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hHle : H ≤ adjointGroup t.tag L := by
    rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι
      (twistedFixedGroup_le_adjointGroup t K σ (graphFixedRootGroup_le t K σ hg))
  obtain ⟨σ', hσ', -, hcard, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  have hcardL : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card := fun a => by
    rw [← hσσ']
    exact hcard a
  have hgen : ∀ z : Module.End L (RootModule t.tag L),
      (∀ a (c : orbitField t K σ a),
        Commute z ((baseChangeGL ι (orbitX t K σ a c : ModGL t.tag K) : ModGL t.tag L) :
          Module.End L (RootModule t.tag L)) ∧
        Commute z ((baseChangeGL ι (orbitY t K σ a c : ModGL t.tag K) : ModGL t.tag L) :
          Module.End L (RootModule t.tag L))) →
      ∀ (i : Fin t.tag.rank) (s : L), Commute z (xOp t.tag L i s) ∧
        Commute z (yOp t.tag L i s) := by
    intro z hz i s
    set a := t.orbitIndex i
    have : Fintype (orbitField t K σ a) := Fintype.ofFinite _
    have hf' : Function.Injective fun c : orbitField t K σ a => ι c :=
      ι.injective.comp Subtype.val_injective
    have hcard' : q ^ (t.orbit a).card ≤ Fintype.card (orbitField t K σ a) := by
      rw [← Nat.card_eq_fintype_card, hcardL]
    have hpow : ∀ (c : orbitField t K σ a) (k : ℕ), ι ((σ ^ k) (c : K)) = ι c ^ q ^ k :=
      fun c k => by rw [pow_apply_eq_pow hσ, map_pow]
    refine ⟨?_, ?_⟩
    · have hX : ∀ n : Fin 3, Commute z (xCoeff t.tag L i n) :=
        commute_coeff_of_commute_orbit_prod hq a (fun i (n : Fin 3) => xCoeff t.tag L i n)
          (fun _ => xCoeff_zero _) hf' hcard' (fun c => by
            have h := (hz a c).1
            rw [coe_baseChangeGL_orbitX] at h
            simpa only [hpow, xOp_eq_sum_fin_three] using h)
          (t.mem_orbit_orbitIndex i)
      rw [xOp_eq_sum_fin_three]
      exact Commute.sum_right _ _ _ fun n _ => (hX n).smul_right _
    · have hY : ∀ n : Fin 3, Commute z (yCoeff t.tag L i n) :=
        commute_coeff_of_commute_orbit_prod hq a (fun i (n : Fin 3) => yCoeff t.tag L i n)
          (fun _ => yCoeff_zero _) hf' hcard' (fun c => by
            have h := (hz a c).2
            rw [coe_baseChangeGL_orbitY] at h
            simpa only [hpow, yOp_eq_sum_fin_three] using h)
          (t.mem_orbit_orbitIndex i)
      rw [yOp_eq_sum_fin_three]
      exact Commute.sum_right _ _ _ fun n _ => (hY n).smul_right _
  have hcentral : ∀ z ∈ adjointGroup t.tag L,
      (∀ (i : Fin t.tag.rank) (s : L), Commute (z : Module.End L (RootModule t.tag L))
        (xOp t.tag L i s) ∧ Commute (z : Module.End L (RootModule t.tag L)) (yOp t.tag L i s)) →
      z = 1 := by
    intro z hzC hzg
    have hcent : ⟨z, hzC⟩ ∈ Subgroup.center (adjointGroup t.tag L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hle : adjointGroup t.tag L ≤ Subgroup.centralizer {z} := by
        rw [adjointGroup, Subgroup.closure_le]
        rintro g ⟨i, c, hg | hg⟩ <;>
          refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) <;>
          rw [Units.val_mul, Units.val_mul, hg]
        · exact (hzg i c).1.eq.symm
        · exact (hzg i c).2.eq.symm
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hcentralizer : ∀ z ∈ adjointGroup t.tag L, (∀ h ∈ H, z * h = h * z) → z = 1 := by
    intro z hzC hz
    refine hcentral z hzC (hgen z fun a c => ⟨?_, ?_⟩)
    · have h1 := hz _ (Subgroup.mem_map_of_mem _ (graphFixedPosUnipotent_le_graphFixedRootGroup
        t K σ (orbitX_mem_graphFixedPosUnipotent t σ a c)))
      exact congrArg Units.val h1
    · have h1 := hz _ (Subgroup.mem_map_of_mem _ (graphFixedNegUnipotent_le_graphFixedRootGroup
        t K σ (orbitY_mem_graphFixedNegUnipotent t σ a c)))
      exact congrArg Units.val h1
  refine ⟨baseChangeGL_injective ι, hHle, hcentralizer, ?_⟩
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  apply Subtype.ext
  refine hcentralizer g (Subgroup.mem_inf.1 g.2).1 fun h hh => ?_
  have h1 := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : ModGL t.tag L)) hg
  simp only [conjNormalizerHom_apply, MulAut.one_apply] at h1
  calc (g : ModGL t.tag L) * h = (g * h * (g : ModGL t.tag L)⁻¹) * g := by group
    _ = h * g := by rw [h1]

theorem even_diagram_fixed_finite_root_ambient_faithfulness
    (t : TwistTag) {f : ℕ} (hf : 2 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (L : Type) [Field L] (ι : K →+* L) :
    Function.Injective (baseChangeGL (τ := t.tag) ι) ∧
    (graphFixedRootGroup t K σ).map (baseChangeGL ι) ≤ adjointGroup t.tag L ∧
    (∀ z ∈ adjointGroup t.tag L, (∀ h ∈ (graphFixedRootGroup t K σ).map (baseChangeGL ι),
      z * h = h * z) → z = 1) ∧
    Function.Injective (conjNormalizerHom (adjointGroup t.tag L)
      ((graphFixedRootGroup t K σ).map (baseChangeGL ι))) := by
  have hq : 3 ≤ 2 ^ f :=
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact diagram_fixed_ambient_centralizer_trivial_of_three_le t Nat.prime_two (by omega) hq K hK
    σ hσ L ι

end CFSG.LieType.Chevalley
