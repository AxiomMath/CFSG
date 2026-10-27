module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Core4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Sign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_norm_ne_zero_of_orth {ι : Type} [Fintype ι] [DecidableEq ι] (hQ : Q.Nondegenerate)
    (b : Module.Basis ι (ZMod 3) V)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0) (i : ι) : Q (b i) ≠ 0 := by
  intro hc
  have hB : Q.polarBilin.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mpr hQ
  have hzero : Q.polarBilin (b i) = 0 := by
    apply b.ext
    intro j
    rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply]
    by_cases hji : j = i
    · rw [hji, QuadraticMap.polar_self, hc, smul_zero]
    · exact horth i j (Ne.symm hji)
  exact b.ne_zero i (hB.1 (b i) fun y => by rw [hzero, LinearMap.zero_apply])

variable (B : Subgroup (OGroup Q)) [Fintype ↥B] [DecidableEq ↥B]

theorem fg_exists_wt_basis (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6)
    {χo : Option (Fin 5) → (↥B → ZMod 3)} (hinj : Function.Injective χo)
    (hne : ∀ o, fgWt (fgT B) (χo o) ≠ ⊥) :
    ∃ b : Module.Basis (Option (Fin 5)) (ZMod 3) V, ∀ o, b o ∈ fgWt (fgT B) (χo o) := by
  have h1 : ∀ o, ∃ w : V, w ∈ fgWt (fgT B) (χo o) ∧ w ≠ 0 := fun o =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hne o)
  choose w hw hw0 using h1
  have hind : iSupIndep (fun o => fgWt (fgT B) (χo o)) :=
    (fgWt_iSupIndep (fgT B) (fgT_comm B hB)).comp hinj
  have hli : LinearIndependent (ZMod 3) w := hind.linearIndependent _ hw hw0
  have hcard : Fintype.card (Option (Fin 5)) = Module.finrank (ZMod 3) V := by
    rw [hdim, Fintype.card_option, Fintype.card_fin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' w hli hcard, fun o => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact hw o

variable (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6) (f : OGroup Q)
  (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1)

include hB hdim hf hf5 hf1

open Classical in
theorem fg_norm_const :
    ∃ a : ZMod 3, ∀ χ ∈ fgS B, ∀ v ∈ fgWt (fgT B) χ, v ≠ 0 → Q v = a := by
  obtain ⟨hcard, hd1⟩ := fg_orbit_structure B hB hdim f hf hf5 hf1
  obtain ⟨χ0, hχ0⟩ : (fgS B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w0, hw0, hw00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((mem_fgS_iff B).1 hχ0).2
  have hline : ∀ v ∈ fgWt (fgT B) χ0, v ≠ 0 → Q v = Q w0 := by
    intro v hv hv0
    have hw0' : (⟨w0, hw0⟩ : ↥(fgWt (fgT B) χ0)) ≠ 0 := fun h => hw00 (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw0').1 (hd1 χ0 hχ0) ⟨v, hv⟩
    have hc' : c • w0 = v := congrArg Subtype.val hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [← hc', zero_smul])
    have hcc : c * c = 1 := by
      revert hc0
      generalize c = x
      revert x
      decide
    rw [← hc', QuadraticMap.map_smul, smul_eq_mul, hcc, one_mul]
  have hQf : ∀ u : V, Q (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) u) = Q u := fun u =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup f.2 u
  set σ : Equiv.Perm (↥B → ZMod 3) := fgPerm B (ZMod 3) (fgCj B f hf) with hσdef
  have hσ5 : σ ^ 5 = 1 := fgPerm_pow_five B (ZMod 3) f hf hf5
  have hPf : ∀ χ : ↥B → ZMod 3, (∀ v ∈ fgWt (fgT B) χ, v ≠ 0 → Q v = Q w0) ↔
      ∀ v ∈ fgWt (fgT B) (σ χ), v ≠ 0 → Q v = Q w0 := by
    intro χ
    constructor
    · intro h v hv hv0
      have hv' : v ∈ (fgWt (fgT B) χ).map
          (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) := by
        rw [fgWt_map_f B f hf χ]
        exact hv
      obtain ⟨u, hu, rfl⟩ := hv'
      have hu0 : u ≠ 0 := fun h' => hv0 (by rw [h', map_zero])
      have h2 := hQf u
      exact h2.trans (h u hu hu0)
    · intro h v hv hv0
      have hfv : ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v ∈ fgWt (fgT B) (σ χ) := by
        rw [← fgWt_map_f B f hf χ]
        exact ⟨v, hv, rfl⟩
      have hfv0 : ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v ≠ 0 := fun h' =>
        hv0 (((f : OGroup Q) : V ≃ₗ[ZMod 3] V).injective (h'.trans (map_zero _).symm))
      exact (hQf v).symm.trans (h _ hfv hfv0)
  set S0 := (fgS B).filter (fun χ => ∀ v ∈ fgWt (fgT B) χ, v ≠ 0 → Q v = Q w0) with hS0
  have hmem0 : ∀ χ, χ ∈ S0 ↔ χ ∈ fgS B ∧ ∀ v ∈ fgWt (fgT B) χ, v ≠ 0 → Q v = Q w0 :=
    fun χ => Finset.mem_filter
  have hinv : ∀ χ, χ ∈ S0 ↔ σ χ ∈ S0 := fun χ =>
    (hmem0 χ).trans ((and_congr (fgS_perm_iff B f hf χ).symm (hPf χ)).trans (hmem0 (σ χ)).symm)
  have hfree : ∀ χ ∈ S0, σ χ ≠ χ := fun χ hχ =>
    fgS_perm_ne_self B hB hdim f hf hf5 hf1 ((hmem0 χ).1 hχ).1
  have hdvd : 5 ∣ S0.card := fg_five_dvd_card_of_free σ hσ5 S0 hinv hfree
  have hsub : S0 ⊆ fgS B := Finset.filter_subset _ _
  have hS0ne : S0.Nonempty := ⟨χ0, (hmem0 χ0).2 ⟨hχ0, hline⟩⟩
  have hle := Finset.card_le_card hsub
  have hpos : 0 < S0.card := Finset.card_pos.2 hS0ne
  have hEq : S0 = fgS B := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨Q w0, fun χ hχ => ((hmem0 χ).1 ?_).2⟩
  rw [hEq]
  exact hχ

theorem fg_frame_E16 (hQ : Q.Nondegenerate) (hsgn : quadSign Q = 1) :
    ∃ (b : Module.Basis (Option (Fin 5)) (ZMod 3) V) (a : ZMod 3), a ≠ 0 ∧
      (∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0) ∧ Q (b none) = -a ∧
      (∀ i : Fin 5, Q (b (some i)) = a) ∧
      ∀ g ∈ B, ∀ o, ∃ s : ZMod 3, s * s = 1 ∧
        ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) (b o) = s • b o := by
  obtain ⟨χo, hinj, -, hsome, hne⟩ := fg_exists_family B hB hdim f hf hf5 hf1
  obtain ⟨b, hb⟩ := fg_exists_wt_basis B hB hdim hinj hne
  obtain ⟨a, ha⟩ := fg_norm_const B hB hdim f hf hf5 hf1
  have horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0 := fun i j hij =>
    fgWt_polar_eq_zero B hB (hne i) (hne j) (hinj.ne hij) (hb i) (hb j)
  have hnorm : ∀ i : Fin 5, Q (b (some i)) = a := fun i =>
    ha _ (hsome i) _ (hb _) (b.ne_zero _)
  have ha0 : a ≠ 0 := by
    rw [← hnorm 0]
    exact fg_norm_ne_zero_of_orth hQ b horth _
  have h0 : Q (b none) ≠ 0 := fg_norm_ne_zero_of_orth hQ b horth none
  refine ⟨b, a, ha0, horth, fg_norm_none_eq_neg hQ hsgn b horth ha0 h0 hnorm, hnorm, ?_⟩
  intro g hg o
  exact ⟨χo o ⟨g, hg⟩, fgWt_sq (fgT B) (fgT_sq B hB) (hne o) ⟨g, hg⟩,
    (mem_fgWt (fgT B)).1 (hb o) ⟨g, hg⟩⟩

end CFSG.OddStandard.SmallF3.Omega
