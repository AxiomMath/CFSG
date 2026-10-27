module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EMod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Props

public section

namespace CFSG.QuasithinUnique.Setup.X3E

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.X3

@[expose] def fixW {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (g : Bool → (M →ₗ[ZMod 2] M)) : Submodule (ZMod 2) M where
  carrier := {w | ∀ w' ∈ eR0W, (wmap g w') w = w}
  zero_mem' := fun w' _ => map_zero _
  add_mem' := fun {x y} hx hy w' hw' => by rw [map_add, hx w' hw', hy w' hw']
  smul_mem' := fun c x hx w' hw' => by rw [map_smul, hx w' hw']

theorem σ_evalG {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (σ : S6 →* (W ≃ₗ[ZMod 2] W)) :
    ∀ (w : List Bool) (x : W),
      σ (evalG w) x = (wmap (fun b => ((σ (gen b) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) w) x
  | [], x => by simp [evalG, wmap]
  | b :: w, x => by
    rw [evalG, map_mul, LinearEquiv.mul_apply, σ_evalG σ w x, wmap_cons]
    rfl

theorem fixSub_R0_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : S6 →* (W ≃ₗ[ZMod 2] W)) :
    fixSub σ R0 = fixW (fun b => ((σ (gen b) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) := by
  ext w
  simp only [mem_fixSub, fixW, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq]
  constructor
  · intro h w' hw'
    rw [← σ_evalG σ w' w]
    exact h _ (by rw [mem_R0]; exact List.mem_map_of_mem hw')
  · intro h r hr
    rw [mem_R0] at hr
    unfold R0list at hr
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hr
    rw [σ_evalG σ w' w]
    exact h w' hw'

theorem finrank_fixW_block {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {d : ℕ} (hd : d = 4)
    (cols : Bool → List ℕ) (hbound : ∀ b, ∀ j < d, (cols b).getD j 0 < 2 ^ d)
    (hfix : ((List.range 16).filter fun t => eR0W.all fun w => wapp 4 cols w t == t).length = 2)
    (Ψ : Vec d ≃ₗ[ZMod 2] W) (g : Bool → (W →ₗ[ZMod 2] W))
    (hΨ : ∀ b s, Ψ (lin d (cols b) s) = g b (Ψ s)) :
    Module.finrank (ZMod 2) (fixW g) = 1 := by
  subst hd
  let S : Set (Vec 4) := {s | ∀ w' ∈ eR0W, (wmap (fun b => lin 4 (cols b)) w') s = s}
  have hint : ∀ w' s, Ψ ((wmap (fun b => lin 4 (cols b)) w') s) = (wmap g w') (Ψ s) :=
    fun w' s => wmap_intertwine (fun b => lin 4 (cols b)) g Ψ.toLinearMap (fun b s => hΨ b s) w' s
  have hset : (fixW g : Set W) = Ψ '' S := by
    ext w
    constructor
    · intro hw
      obtain ⟨s, rfl⟩ := Ψ.surjective w
      refine ⟨s, fun w' hw' => Ψ.injective ?_, rfl⟩
      rw [hint]
      exact hw w' hw'
    · rintro ⟨s, hs, rfl⟩ w' hw'
      rw [← hint, hs w' hw']
  have hmem : ∀ t < 16, toVec 4 t ∈ S ↔ (eR0W.all fun w => wapp 4 cols w t == t) = true := by
    intro t ht
    simp only [S, Set.mem_ofPred_eq, List.all_eq_true, beq_iff_eq]
    refine forall_congr' fun w' => forall_congr' fun _ => ?_
    rw [← toVec_wapp]
    constructor
    · intro h
      exact toVec_injOn (wapp_lt hbound w' (by simpa using ht)) (by simpa using ht) h
    · intro h; rw [h]
  let F : Finset ℕ :=
    ((List.range 16).filter fun t => eR0W.all fun w => wapp 4 cols w t == t).toFinset
  have hF : F.card = 2 := by
    rw [List.toFinset_card_of_nodup ((List.nodup_range).filter _), hfix]
  have hSset : S = (fun t => toVec 4 t) '' (F : Set ℕ) := by
    ext v
    constructor
    · intro hv
      obtain ⟨t, ht, rfl⟩ := exists_toVec v
      refine ⟨t, ?_, rfl⟩
      simp only [F, Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range]
      exact ⟨ht, (hmem t (by simpa using ht)).mp hv⟩
    · rintro ⟨t, ht, rfl⟩
      simp only [F, Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at ht
      exact (hmem t (by simpa using ht.1)).mpr ht.2
  have hinjF : Set.InjOn (fun t => toVec 4 t) (F : Set ℕ) := by
    intro t ht t' ht' h
    simp only [F, Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at ht ht'
    exact toVec_injOn (by simpa using ht.1) (by simpa using ht'.1) h
  have hcard : Nat.card (fixW g) = 2 := by
    have h1 : Nat.card (fixW g) = (fixW g : Set W).ncard :=
      (Nat.card_coe_set_eq (fixW g : Set W))
    rw [h1, hset, Set.InjOn.ncard_image (Ψ.injective.injOn), hSset, hinjF.ncard_image,
      Set.ncard_coe_finset, hF]
  have h2 : Nat.card (fixW g) = 2 ^ Module.finrank (ZMod 2) (fixW g) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixW g)]
    simp
  rw [hcard] at h2
  exact Nat.pow_right_injective (le_refl 2) (by simpa using h2.symm :
    2 ^ Module.finrank (ZMod 2) (fixW g) = 2 ^ 1)

theorem linearEquiv_one_dim {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (h : Module.finrank (ZMod 2) W = 1) (f : W ≃ₗ[ZMod 2] W) (w : W) : f w = w := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h
  obtain ⟨c, hc⟩ := hv (f v)
  obtain ⟨c', rfl⟩ := hv w
  have hc1 : c = 1 := by
    by_contra hne
    have hc0 : c = 0 := by
      revert hne
      generalize c = c''
      revert c''
      decide
    rw [hc0, zero_smul] at hc
    exact hv0 (f.injective (hc.symm.trans (map_zero f).symm))
  rw [map_smul, ← hc, hc1, one_smul]

theorem factorization_two : (360 : ℕ).factorization 2 = 3 := by
  have h : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_R0 {R : Subgroup S6} (hR : Nat.card R = 8) :
    ∃ g : S6, ∀ r : S6, r ∈ R ↔ ∃ r₀ ∈ R0, g * r₀ * g⁻¹ = r := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (Nat.card S6).factorization 2 = 3 := by rw [card_S6]; exact factorization_two
  let P0 : Sylow 2 S6 := Sylow.ofCard R0 (by rw [card_R0, h2]; norm_num)
  let P1 : Sylow 2 S6 := Sylow.ofCard R (by rw [hR, h2]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S6 P0 P1
  refine ⟨g, fun r => ?_⟩
  have hsub : ((g • P0 : Sylow 2 S6) : Subgroup S6) = R := by rw [hg]; rfl
  rw [← hsub, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  rfl

theorem fixSub_conj {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : S6 →* (W ≃ₗ[ZMod 2] W)) (g : S6) (R R0' : Subgroup S6)
    (hg : ∀ r, r ∈ R ↔ ∃ r₀ ∈ R0', g * r₀ * g⁻¹ = r) :
    fixSub σ R = Submodule.map ((σ g : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (fixSub σ R0') := by
  ext w
  constructor
  · intro hw
    refine ⟨σ g⁻¹ w, fun r₀ hr₀ => ?_, ρ_apply_inv σ g w⟩
    have h1 := hw (g * r₀ * g⁻¹) ((hg _).mpr ⟨r₀, hr₀, rfl⟩)
    have h2 : σ g⁻¹ (σ (g * r₀ * g⁻¹) w) = σ g⁻¹ w := by rw [h1]
    rw [← ρ_mul_apply] at h2
    have h3 : g⁻¹ * (g * r₀ * g⁻¹) = r₀ * g⁻¹ := by group
    rw [h3, ρ_mul_apply] at h2
    exact h2
  · rintro ⟨u, hu, rfl⟩ r hr
    obtain ⟨r₀, hr₀, rfl⟩ := (hg r).mp hr
    change σ (g * r₀ * g⁻¹) (σ g u) = σ g u
    rw [← ρ_mul_apply, show g * r₀ * g⁻¹ * g = g * r₀ by group, ρ_mul_apply, hu r₀ hr₀]

theorem dims_facts : ∀ i < 12, eNs.getD (i + 1) 0 - eNs.getD i 0 = 1 ∨
    eNs.getD (i + 1) 0 - eNs.getD i 0 = 4 ∨ eNs.getD (i + 1) 0 - eNs.getD i 0 = 16 := by
  have h := dimsOK_true
  unfold dimsOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  intro i hi
  have := h i hi
  tauto

theorem fix_facts : ∀ i < 12, eNs.getD (i + 1) 0 - eNs.getD i 0 = 4 →
    ((List.range 16).filter fun t => eR0W.all fun w => wapp 4 (blkOf i) w t == t).length = 2 := by
  have h := fixOK_true
  unfold fixOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  intro i hi h4
  rcases h i hi with h1 | h1
  · exact absurd h4 h1
  · exact h1

theorem a6SimpleModules : A6SimpleModules := by
  intro W _ _ _ σ hS
  obtain ⟨i, hi, Ψ, hΨ⟩ := exists_block_iso σ hS
  have hd : Module.finrank (ZMod 2) W = eNs.getD (i + 1) 0 - eNs.getD i 0 := by
    rw [← Ψ.finrank_eq, Module.finrank_fin_fun]
  refine ⟨by rw [hd]; exact dims_facts i hi, ?_, ?_⟩
  · intro h1 g w
    exact linearEquiv_one_dim h1 (σ g) w
  · intro h4 R hR
    have hd4 : eNs.getD (i + 1) 0 - eNs.getD i 0 = 4 := by rw [← hd]; exact h4
    obtain ⟨g, hg⟩ := exists_conj_R0 hR
    have hmap := fixSub_conj σ g R R0 hg
    rw [hmap, LinearEquiv.finrank_map_eq (σ g), fixSub_R0_eq]
    exact finrank_fixW_block hd4 (blkOf i) (fun b j hj => blkCols_lt _ _ _ j hj)
      (fix_facts i hi hd4) Ψ _ (fun b s => by
        simpa using hΨ b s)

theorem composition_series :
    (∀ i ≤ 12, ∀ b, ∀ u ∈ Submodule.map (lin 45 eB) (Fl 45 (eNs.getD i 0)),
        lin 45 (piColsOf b) u ∈ Submodule.map (lin 45 eB) (Fl 45 (eNs.getD i 0))) ∧
    (∀ i < 12, IrredPair
      (fun b => lin (eNs.getD (i + 1) 0 - eNs.getD i 0) (blkOf i b))) ∧
    ((List.range 12).map fun i => eNs.getD (i + 1) 0 - eNs.getD i 0) =
      [4, 1, 4, 1, 1, 4, 4, 1, 4, 1, 4, 16] ∧
    (∀ i < 12, eNs.getD (i + 1) 0 - eNs.getD i 0 = 4 →
      ((List.range 16).filter fun t => eR0W.all fun w => wapp 4 (blkOf i) w t == t).length = 2) := by
  obtain ⟨hns0, hnsN, hmono, hfl⟩ := flagOK_facts
  refine ⟨?_, ?_, by decide +kernel, fix_facts⟩
  · intro i hi b u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨lin 45 (colsOf b) v, ?_, lin_eB_cols b v⟩
    apply lin_mem_Fl _ hv
    intro j hj
    have := hfl i hi j hj
    cases b
    · exact this.1
    · exact this.2
  · intro i hi
    have hwin : eNs.getD i 0 + (eNs.getD (i + 1) 0 - eNs.getD i 0) ≤ 45 := by
      have h1 := hmono i hi
      have h2 : eNs.getD (i + 1) 0 ≤ eNs.getD 12 0 :=
        ns_mono (ns := fun i => eNs.getD i 0) (nSteps := 12) hmono (i + 1) 12 (by omega) le_rfl
      omega
    exact nortonOK_sound (blocksOK_facts i hi)

end CFSG.QuasithinUnique.Setup.X3E
