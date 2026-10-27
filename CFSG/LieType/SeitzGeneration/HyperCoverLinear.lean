module

public import CFSG.LieType.SeitzGeneration.HyperCoverLift
public import CFSG.LieType.SeitzGeneration.NonabParabolic
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.LieType.Chevalley

section Radical

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

@[expose] def unipRadSL (W : Submodule F (Fin n → F)) :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W}
  mul_mem' := by
    intro g h hg hh
    change (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W at hg
    change (h : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W at hh
    change (g : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W
    have e : (g : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) - 1 =
        ((g : Matrix (Fin n) (Fin n) F) - 1) + ((h : Matrix (Fin n) (Fin n) F) - 1) +
          ((g : Matrix (Fin n) (Fin n) F) - 1) * ((h : Matrix (Fin n) (Fin n) F) - 1) := by
      noncomm_ring
    rw [e, thetaSpace_mul hg hh, add_zero]
    exact (thetaSpace W).add_mem hg hh
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W
    rw [sub_self]
    exact (thetaSpace W).zero_mem
  inv_mem' := by
    intro g hg
    change (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W at hg
    change ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W
    have hsq := thetaSpace_mul hg hg
    have hgi : ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (g : Matrix (Fin n) (Fin n) F) = 1 := congrArg Subtype.val (inv_mul_cancel g)
    have h2 : (g : Matrix (Fin n) (Fin n) F) * (1 - ((g : Matrix (Fin n) (Fin n) F) - 1)) = 1 := by
      calc (g : Matrix (Fin n) (Fin n) F) * (1 - ((g : Matrix (Fin n) (Fin n) F) - 1)) =
          1 - ((g : Matrix (Fin n) (Fin n) F) - 1) * ((g : Matrix (Fin n) (Fin n) F) - 1) := by
            noncomm_ring
        _ = 1 := by rw [hsq, sub_zero]
    have h1 : ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        1 - ((g : Matrix (Fin n) (Fin n) F) - 1) := by
      calc ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            ((g : Matrix (Fin n) (Fin n) F) * (1 - ((g : Matrix (Fin n) (Fin n) F) - 1))) := by
            rw [h2, Matrix.mul_one]
        _ = 1 - ((g : Matrix (Fin n) (Fin n) F) - 1) := by
            rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
    rw [h1, show (1 : Matrix (Fin n) (Fin n) F) - ((g : Matrix (Fin n) (Fin n) F) - 1) - 1 =
      -((g : Matrix (Fin n) (Fin n) F) - 1) by abel]
    exact (thetaSpace W).neg_mem hg

omit [Finite F] in
theorem mem_unipRadSL {W : Submodule F (Fin n → F)} {g : SpecialLinearGroup (Fin n) F} :
    g ∈ unipRadSL W ↔ (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W := Iff.rfl

omit [Finite F] in
theorem isPGroup_unipRadSL (W : Submodule F (Fin n → F)) :
    IsPGroup (ringChar F) (unipRadSL W) := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  have hg : ((g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈
      thetaSpace W := g.2
  set φ := ((g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 with hφ
  have hsq : φ * φ = 0 := thetaSpace_mul hg hg
  have hpow : ∀ k : ℕ, (1 + φ) ^ k = 1 + (k : F) • φ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      simp only [Nat.cast_succ, add_smul, one_smul, add_mul, mul_add, Matrix.mul_one,
        Matrix.one_mul, Matrix.smul_mul, hsq, smul_zero, add_zero]
      abel
  apply Subtype.ext
  apply Subtype.ext
  have hcoe : ((g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + φ := by
    rw [hφ]
    abel
  change ((g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ ringChar F = 1
  rw [hcoe, hpow, ringChar.Nat.cast_ringChar, zero_smul, add_zero]

omit [Finite F] in
theorem le_normalizer_unipRadSL {E : Subgroup (SpecialLinearGroup (Fin n) F)}
    {W : Submodule F (Fin n → F)}
    (hWE : ∀ x ∈ E, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    E ≤ Subgroup.normalizer ((unipRadSL W : Subgroup (SpecialLinearGroup (Fin n) F)) :
      Set (SpecialLinearGroup (Fin n) F)) := by
  have key : ∀ x ∈ E, ∀ h ∈ unipRadSL W, x * h * x⁻¹ ∈ unipRadSL W := by
    intro x hx h hh
    rw [mem_unipRadSL] at hh ⊢
    have hxx : (x : Matrix (Fin n) (Fin n) F) *
        ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
      congrArg Subtype.val (mul_inv_cancel x)
    have e : (x : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
        ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        conjAction x ((h : Matrix (Fin n) (Fin n) F) - 1) := by
      rw [conjAction_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hxx]
    change (x : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
      ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W
    rw [e]
    exact conjAction_mem_thetaSpace hWE hx hh
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key x hx h, fun hh => ?_⟩
  have := key x⁻¹ (E.inv_mem hx) _ hh
  simpa [mul_assoc] using this

theorem hyperGen_sl_of_stable {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {E : Subgroup (SpecialLinearGroup (Fin n) F)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : ∀ x ∈ E, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    HyperGen p (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have hEF : (Nat.card E : F) ≠ 0 := by
    rw [hcard, Nat.cast_pow]
    exact pow_ne_zero 3 hpF
  obtain ⟨W', hc, hW'E⟩ := exists_invariant_compl hEF hWE
  have hW'0 : W' ≠ ⊥ := fun h => hWt (by
    have := codisjoint_iff.1 hc.2
    rwa [h, sup_bot_eq] at this)
  have hr : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hr⟩
  have hrp : ringChar F ≠ p := fun h => hpF (by rw [← h]; exact ringChar.Nat.cast_ringChar)
  have : IsElementaryAbelian p ↥E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  have hle : ∀ V : Submodule F (Fin n → F),
      (∀ x ∈ E, ∀ w ∈ V, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ V) →
      unipRadSL V ≤ ⨆ (B : Subgroup (SpecialLinearGroup (Fin n) F)) (_ : B ≤ E)
        (_ : B.relIndex E = p), (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) ⊓
          Subgroup.centralizer (B : Set (SpecialLinearGroup (Fin n) F)) := fun V hV =>
    le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp (isPGroup_unipRadSL V))
      (le_normalizer_unipRadSL hV) le_top
  have htop := eq_top_of_unip_isCompl hc hW0 hW'0
    (fun g hg => hle W hWE ((mem_unipRadSL).2 hg)) (fun g hg => hle W' hW'E ((mem_unipRadSL).2 hg))
  intro g _
  have hg : g ∈ ⨆ (B : Subgroup (SpecialLinearGroup (Fin n) F)) (_ : B ≤ E)
      (_ : B.relIndex E = p), (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) ⊓
        Subgroup.centralizer (B : Set (SpecialLinearGroup (Fin n) F)) := by
    rw [htop]
    exact Subgroup.mem_top g
  refine (iSup₂_le fun B hB => iSup_le fun hBi => ?_ : _ ≤ Subgroup.closure _) hg
  intro x hx
  exact Subgroup.subset_closure ⟨Subgroup.mem_top x, B, hB, hBi,
    fun f hf => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 f hf⟩

end Radical

theorem relIndex_map_of_injOn {G H : Type*} [Group G] [Group H] (φ : G →* H) {E F : Subgroup G}
    (hFE : F ≤ E) (hinj : ∀ x ∈ E, φ x = 1 → x = 1) :
    (F.map φ).relIndex (E.map φ) = F.relIndex E := by
  set φE : E →* H := φ.comp E.subtype
  have hφE : Function.Injective φE := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have h1 : F.map φ = (F.subgroupOf E).map φE := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hFE]
  have h2 : E.map φ = (⊤ : Subgroup E).map φE := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1, h2, Subgroup.relIndex_map_map_of_injective _ _ hφE, Subgroup.relIndex_top_right]
  rfl

theorem hyperGen_map_of_surjective {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (hφ : Function.Surjective φ) {E : Subgroup G} (hinj : ∀ x ∈ E, φ x = 1 → x = 1)
    (h : HyperGen p (⊤ : Subgroup G) E) : HyperGen p (⊤ : Subgroup H) (E.map φ) := by
  intro y _
  obtain ⟨x, rfl⟩ := hφ y
  have hx := h (Subgroup.mem_top x)
  have hle : (Subgroup.closure {k : G | k ∈ (⊤ : Subgroup G) ∧ ∃ F : Subgroup G, F ≤ E ∧
      F.relIndex E = p ∧ ∀ f ∈ F, f * k = k * f}).map φ ≤
      Subgroup.closure {k : H | k ∈ (⊤ : Subgroup H) ∧ ∃ F : Subgroup H, F ≤ E.map φ ∧
        F.relIndex (E.map φ) = p ∧ ∀ f ∈ F, f * k = k * f} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨k, ⟨-, F, hFE, hFi, hF⟩, rfl⟩
    refine ⟨Subgroup.mem_top _, F.map φ, Subgroup.map_mono hFE, ?_, ?_⟩
    · rw [relIndex_map_of_injOn φ hFE hinj, hFi]
    · rintro _ ⟨f, hf, rfl⟩
      rw [← map_mul, ← map_mul, hF f hf]
  exact hle ⟨x, hx, rfl⟩

theorem exists_sl_cover_hom {m : ℕ} {F : Type} [Field F] [Finite F] (hm : 2 ≤ m)
    (hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m F) {K : Type*} [Group K]
    [Group.IsPerfect K] (ρ : K →* ProjectiveSpecialLinearGroup (Fin (m + 1)) F)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K) :
    ∃ φ : SpecialLinearGroup (Fin (m + 1)) F →* K, Function.Surjective φ ∧
      ∀ g, ρ (φ g) =
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) g := by
  set π := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
  let P : Subgroup (K × SpecialLinearGroup (Fin (m + 1)) F) :=
    MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _))
  let pr : P →* SpecialLinearGroup (Fin (m + 1)) F := (MonoidHom.snd _ _).comp P.subtype
  have hpr : Function.Surjective pr := fun g => by
    obtain ⟨k, hk⟩ := hρ (π g)
    exact ⟨⟨(k, g), hk⟩, rfl⟩
  have hprk : pr.ker ≤ Subgroup.center P := by
    intro x hx
    have hx2 : (x : K × SpecialLinearGroup (Fin (m + 1)) F).2 = 1 := hx
    have hxP : ρ (x : K × SpecialLinearGroup (Fin (m + 1)) F).1 =
        π (x : K × SpecialLinearGroup (Fin (m + 1)) F).2 := x.2
    have hx1 : (x : K × SpecialLinearGroup (Fin (m + 1)) F).1 ∈ Subgroup.center K := by
      refine hker ?_
      rw [MonoidHom.mem_ker, hxP, hx2, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.1 hx1 _
    · show (y : K × SpecialLinearGroup (Fin (m + 1)) F).2 * (x : K × _).2 =
        (x : K × SpecialLinearGroup (Fin (m + 1)) F).2 * (y : K × _).2
      rw [hx2, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating hm hsep hpr hprk
  let φ : SpecialLinearGroup (Fin (m + 1)) F →* K := (MonoidHom.fst _ _).comp (P.subtype.comp σ)
  have hφρ : ∀ g, ρ (φ g) = π g := by
    intro g
    have h1 : ρ ((σ g : K × SpecialLinearGroup (Fin (m + 1)) F).1) =
        π ((σ g : K × SpecialLinearGroup (Fin (m + 1)) F).2) := (σ g).2
    have h2 : (σ g : K × SpecialLinearGroup (Fin (m + 1)) F).2 = g := hσ g
    rw [h2] at h1
    exact h1
  refine ⟨φ, ?_, hφρ⟩
  have htop : φ.range = ⊤ := eq_top_of_map_eq_top_of_perfect ρ hker (by
    rw [← MonoidHom.range_comp, eq_top_iff]
    rintro x -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) x
    exact ⟨g, hφρ g⟩)
  exact MonoidHom.range_eq_top.1 htop

section Diag

variable (m : ℕ) (F : Type*) [Field F]

@[expose] def diagThreeVec : Fˣ × Fˣ × Fˣ →* (Fin (m + 1) → Fˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin (m + 1) => Fˣ) 0).comp (MonoidHom.fst _ _) *
    (MonoidHom.mulSingle (fun _ : Fin (m + 1) => Fˣ) 1).comp
      ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    (MonoidHom.mulSingle (fun _ : Fin (m + 1) => Fˣ) 2).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)) *
    (MonoidHom.mulSingle (fun _ : Fin (m + 1) => Fˣ) (Fin.last m)).comp (invMonoidHom.comp
      ((MonoidHom.fst _ _) * (MonoidHom.fst _ _).comp (MonoidHom.snd _ _) *
        (MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))

theorem diagThreeVec_apply (x : Fˣ × Fˣ × Fˣ) : diagThreeVec m F x =
    Pi.mulSingle 0 x.1 * Pi.mulSingle 1 x.2.1 * Pi.mulSingle 2 x.2.2 *
      Pi.mulSingle (Fin.last m) (x.1 * x.2.1 * x.2.2)⁻¹ := rfl

theorem prod_diagThreeVec (x : Fˣ × Fˣ × Fˣ) : ∏ j, diagThreeVec m F x j = 1 := by
  rw [diagThreeVec_apply]
  simp only [Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
  group

@[expose] noncomputable def diagThree : Fˣ × Fˣ × Fˣ →* SpecialLinearGroup (Fin (m + 1)) F where
  toFun x := ⟨diagonal fun j => (diagThreeVec m F x j : F), by
    rw [det_diagonal, ← Units.coe_prod, prod_diagThreeVec, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    change diagonal (fun j => (diagThreeVec m F 1 j : F)) = 1
    rw [map_one]
    simp only [Pi.one_apply, Units.val_one]
    exact diagonal_one
  map_mul' x y := by
    apply Subtype.ext
    change diagonal (fun j => (diagThreeVec m F (x * y) j : F)) =
      diagonal (fun j => (diagThreeVec m F x j : F)) *
        diagonal (fun j => (diagThreeVec m F y j : F))
    rw [diagonal_mul_diagonal, map_mul]
    simp only [Pi.mul_apply, Units.val_mul]

theorem coe_diagThree (x : Fˣ × Fˣ × Fˣ) :
    ((diagThree m F x : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal fun j => (diagThreeVec m F x j : F) := rfl

theorem diagThreeVec_apply_of (x : Fˣ × Fˣ × Fˣ) (j : Fin (m + 1)) :
    diagThreeVec m F x j = (if j = 0 then x.1 else 1) * (if j = 1 then x.2.1 else 1) *
      (if j = 2 then x.2.2 else 1) *
        (if j = Fin.last m then (x.1 * x.2.1 * x.2.2)⁻¹ else 1) := by
  rw [diagThreeVec_apply]
  simp only [Pi.mul_apply, Pi.mulSingle_apply]

end Diag

section Cube

variable {m : ℕ} {F : Type*} [Field F]

private theorem fin_ne {m : ℕ} {a b : Fin (m + 1)} (h : (a : ℕ) ≠ b) : a ≠ b :=
  fun e => h (congrArg Fin.val e)

theorem val_one_fin (hm : 1 ≤ m) : ((1 : Fin (m + 1)) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]

theorem val_two_fin (hm : 2 ≤ m) : ((2 : Fin (m + 1)) : ℕ) = 2 := by
  rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega)]

theorem fin_positions (hm : 4 ≤ m) :
    (0 : Fin (m + 1)) ≠ 1 ∧ (0 : Fin (m + 1)) ≠ 2 ∧ (0 : Fin (m + 1)) ≠ Fin.last m ∧
      (1 : Fin (m + 1)) ≠ 0 ∧ (1 : Fin (m + 1)) ≠ 2 ∧ (1 : Fin (m + 1)) ≠ Fin.last m ∧
      (2 : Fin (m + 1)) ≠ 0 ∧ (2 : Fin (m + 1)) ≠ 1 ∧ (2 : Fin (m + 1)) ≠ Fin.last m ∧
      (⟨3, by omega⟩ : Fin (m + 1)) ≠ 0 ∧ (⟨3, by omega⟩ : Fin (m + 1)) ≠ 1 ∧
      (⟨3, by omega⟩ : Fin (m + 1)) ≠ 2 ∧ (⟨3, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
  have v1 := val_one_fin (m := m) (by omega)
  have v2 := val_two_fin (m := m) (by omega)
  refine ⟨fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_,
    fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_, fin_ne ?_⟩ <;>
    simp only [v1, v2, Fin.val_zero, Fin.val_last] <;> omega

theorem diagThreeVec_at_zero (hm : 4 ≤ m) (x : Fˣ × Fˣ × Fˣ) : diagThreeVec m F x 0 = x.1 := by
  obtain ⟨h01, h02, h0l, -⟩ := fin_positions hm
  rw [diagThreeVec_apply_of]
  simp [h01, h02, h0l]

theorem diagThreeVec_at_one (hm : 4 ≤ m) (x : Fˣ × Fˣ × Fˣ) : diagThreeVec m F x 1 = x.2.1 := by
  obtain ⟨-, -, -, h10, h12, h1l, -⟩ := fin_positions hm
  rw [diagThreeVec_apply_of]
  simp [h10, h12, h1l]

theorem diagThreeVec_at_two (hm : 4 ≤ m) (x : Fˣ × Fˣ × Fˣ) : diagThreeVec m F x 2 = x.2.2 := by
  obtain ⟨-, -, -, -, -, -, h20, h21, h2l, -⟩ := fin_positions hm
  rw [diagThreeVec_apply_of]
  simp [h20, h21, h2l]

theorem diagThreeVec_at_three (hm : 4 ≤ m) (x : Fˣ × Fˣ × Fˣ) :
    diagThreeVec m F x ⟨3, by omega⟩ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h30, h31, h32, h3l⟩ := fin_positions hm
  rw [diagThreeVec_apply_of]
  simp [h30, h31, h32, h3l]

theorem diagThree_injective (hm : 4 ≤ m) : Function.Injective (diagThree m F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h := congrArg (fun g : SpecialLinearGroup (Fin (m + 1)) F =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (MonoidHom.mem_ker.1 hx)
  simp only [coe_diagThree] at h
  have hentry : ∀ j, (diagThreeVec m F x j : F) = 1 := fun j => by
    have := congrFun (congrFun h j) j
    simpa using this
  have h0 := hentry 0
  have h1 := hentry 1
  have h2 := hentry 2
  rw [diagThreeVec_at_zero hm] at h0
  rw [diagThreeVec_at_one hm] at h1
  rw [diagThreeVec_at_two hm] at h2
  rw [Subgroup.mem_bot]
  ext <;> simp [h0, h1, h2]

theorem eq_one_of_diagThree_mem_center (hm : 4 ≤ m) {x : Fˣ × Fˣ × Fˣ}
    (hx : diagThree m F x ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    diagThree m F x = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  have h3 := congrFun (congrFun hr ⟨3, by omega⟩) ⟨3, by omega⟩
  simp only [coe_diagThree, diagonal_apply_eq, diagThreeVec_at_three hm, Units.val_one,
    scalar_apply] at h3
  apply Subtype.ext
  change ((diagThree m F x : SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1
  rw [← hr, h3, map_one]

end Cube

theorem exists_hyperGen_cover_linear {m : ℕ} (hm : 4 ≤ m) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q.card - 1) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.A m q, hv⟩) :
    ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ HyperGen p ⊤ E := by
  classical
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  have hq4 : 4 ≤ q.card := by
    have h1 : p ≤ q.card - 1 := Nat.le_of_dvd (by omega) hpq
    omega
  let eL := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  let ρ : K →* ProjectiveSpecialLinearGroup (Fin (m + 1)) F :=
    (eL.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ :=
    (eL.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m F :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by omega) (by omega)
      (by omega) (by omega)
  obtain ⟨φ, hφs, hφρ⟩ := exists_sl_cover_hom (by omega) hsep ρ hρs hker
  have hpF : p ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; exact hpq
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hpF
  have htp : t ^ p = 1 := ht ▸ pow_orderOf_eq_one t
  have hpF0 : (p : F) ≠ 0 := by
    intro h0
    have hc : CharP F q.p := inferInstance
    have hdvd : q.p ∣ p := (CharP.cast_eq_zero_iff F q.p p).1 h0
    have hpq' : p = q.p := ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 hdvd).symm
    have : p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hpq']
      exact dvd_pow_self _ q.exponent_pos.ne'
    have h1 : p ∣ q.card - (q.card - 1) := Nat.dvd_sub this hpq
    rw [show q.card - (q.card - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  set g := diagThree m F with hg
  have hcomm : ∀ a b : Fˣ × Fˣ × Fˣ, Commute (g a) (g b) := fun a b =>
    (Commute.all a b).map g
  have hpow : ∀ a : Fˣ × Fˣ × Fˣ, a ^ p = 1 → g a ^ p = 1 := fun a ha => by
    rw [← map_pow, ha, map_one]
  have h0p : ((t, 1, 1) : Fˣ × Fˣ × Fˣ) ^ p = 1 := by simp [htp]
  have h1p : ((1, t, 1) : Fˣ × Fˣ × Fˣ) ^ p = 1 := by simp [htp]
  have h2p : ((1, 1, t) : Fˣ × Fˣ × Fˣ) ^ p = 1 := by simp [htp]
  obtain ⟨E₀, hE₀, hE₀c, hE₀gen, -, -, -⟩ := exists_cube_of_three hp (hcomm _ _) (hcomm _ _)
    (hcomm _ _) (hpow _ h0p) (hpow _ h1p) (hpow _ h2p) (by
      intro i j k hijk
      rw [← map_zpow, ← map_zpow, ← map_zpow, ← map_mul, ← map_mul,
        ← map_one g] at hijk
      have hijk' := diagThree_injective hm hijk
      have hti : t ^ i = 1 := by simpa using congrArg Prod.fst hijk'
      have htj : t ^ j = 1 := by simpa using congrArg (fun x => x.2.1) hijk'
      have htk : t ^ k = 1 := by simpa using congrArg (fun x => x.2.2) hijk'
      refine ⟨?_, ?_, ?_⟩ <;> rw [← ht]
      · exact orderOf_dvd_iff_zpow_eq_one.2 hti
      · exact orderOf_dvd_iff_zpow_eq_one.2 htj
      · exact orderOf_dvd_iff_zpow_eq_one.2 htk)
  have hE₀diag : ∀ x ∈ E₀, ∃ a : Fˣ × Fˣ × Fˣ, x = g a := by
    intro x hx
    obtain ⟨i, j, k, rfl⟩ := hE₀gen x hx
    exact ⟨(t, 1, 1) ^ i * (1, t, 1) ^ j * (1, 1, t) ^ k, by
      rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow]⟩
  have hinj : ∀ x ∈ E₀, φ x = 1 → x = 1 := by
    intro x hx h1
    obtain ⟨a, rfl⟩ := hE₀diag x hx
    have h2 : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) (g a) =
        1 := by rw [← hφρ, h1, map_one]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact eq_one_of_diagThree_mem_center hm h2
  set W : Submodule F (Fin (m + 1) → F) := Submodule.span F {Pi.single 0 1}
  have hWE : ∀ x ∈ E₀, ∀ w ∈ W, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F).mulVec w ∈ W := by
    intro x hx w hw
    obtain ⟨a, rfl⟩ := hE₀diag x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [coe_diagThree, Matrix.mulVec_smul, diagonal_mulVec_single, mul_one]
    refine W.smul_mem c (Submodule.mem_span_singleton.2 ⟨(diagThreeVec m F a 0 : F), ?_⟩)
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hW0 : W ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact Pi.single_ne_zero_iff.2 one_ne_zero
  have hWt : W ≠ ⊤ := by
    intro htop
    have h1 : (Pi.single 1 1 : Fin (m + 1) → F) ∈ W := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    have := congrFun hc 1
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [Pi.single_eq_of_ne (fin_ne (by simp; omega)), Pi.single_eq_same, mul_zero] at this
    exact zero_ne_one this
  have hgen := hyperGen_sl_of_stable hp hpF0 hE₀ hE₀c hW0 hWt hWE
  refine ⟨E₀.map φ, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ φ, ?_,
    hyperGen_map_of_surjective φ hφs hinj hgen⟩
  have hφE : Function.Injective (φ.comp E₀.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp E₀.subtype).range = E₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← hE₀c]
  exact (Nat.card_congr (MonoidHom.ofInjective hφE).toEquiv).symm

end CFSG.LieType.SeitzGeneration
