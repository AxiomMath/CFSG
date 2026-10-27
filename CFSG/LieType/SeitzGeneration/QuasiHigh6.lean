module

public import CFSG.LieType.SeitzGeneration.QuasiHigh4Unitary
public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighUnitaryGUTwo
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LieType.SeitzGeneration.QuasiHigh3

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh6

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LieType.SeitzGeneration.QuasiHigh5
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary

section Cover

variable {G K : Type*} [Group G] [Group K]

theorem apply_eq_of_model_lift {P : Type*} [Group P] (hG : commutator G = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* P) (π : G →* P) (φ : G →* K)
    (hφ : ∀ x, θ ((φ x : K) : K ⧸ Subgroup.center K) = π x) (e : MulAut K) (α : G →* G)
    (hα : ∀ x, modelAut θ e (π x) = π (α x)) {g : G} (hg : α g = g) : e (φ g) = φ g := by
  have heq := hom_eq_of_mk_eq hG ((e : K ≃* K).toMonoidHom.comp φ) (φ.comp α)
    (fun x => θ.injective (by
      change θ ((e (φ x) : K) : K ⧸ Subgroup.center K) = θ ((φ (α x) : K) : K ⧸ Subgroup.center K)
      rw [model_mk_apply, hφ, hφ, hα]))
  have h1 := DFunLike.congr_fun heq g
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at h1
  rw [h1, hg]

theorem exists_hyperplane_of_le_map {X Y : Type*} [Group X] [Group Y] (μ : X →* Y)
    (hμ : Function.Injective μ) {p : ℕ} {E : Subgroup X} {F' : Subgroup Y} (hF' : F' ≤ E.map μ)
    (hrel : F'.relIndex (E.map μ) = p) : ∃ F ≤ E, F.relIndex E = p ∧ ∀ e ∈ F, μ e ∈ F' := by
  refine ⟨F'.comap μ ⊓ E, inf_le_right, ?_, fun e he => he.1⟩
  have hmap : (F'.comap μ ⊓ E).map μ = F' := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hF' hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  rw [← Subgroup.relIndex_map_map_of_injective _ E hμ, hmap, hrel]

end Cover

section Inndiag

variable {ℓ f n : ℕ} {Kf : Type} [Field Kf]

theorem seitzHyperGamma_eq_top_of_le_primeFormD_cover
    {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n) (hq2 : ℓ ^ f ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n)) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hD : E.map (modelAut θ) ≤ primeFormD h (idGram Kf n)) : seitzHyperGamma p E = ⊤ := by
  classical
  haveI : Finite Kf := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP Kf ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (primeFormP h (idGram Kf n)) :=
    Finite.of_surjective (piG h n) (QuotientGroup.mk'_surjective _)
  haveI : Finite (MulAut (primeFormP h (idGram Kf n))) := MulEquiv.finite_left
  have hq4 : 4 ≤ ℓ ^ f :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux.four_le_of_dvd_succ hp
      hp2 (pow_ne_zero _ h.prime.ne_zero) hpq hq2
  have hne : (n, ℓ ^ f) ≠ (3, 2) := fun h' => hq2 (Prod.mk.inj h').2
  set κ := primeFormConjHom h (idGram Kf n) with hκ
  obtain ⟨φ, hφ, hφθ⟩ := exists_su_lift hperf h hn hne (fun _ => hq4) θ
  have hGU : commutator (GU1 h n) = ⊤ := commutator_GU1_eq_top h hn hne
  have hinj := modelAut_injective hperf θ
  set Ē := E.map (modelAut θ) with hĒdef
  have hĒa : IsElemAbelian p Ē := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hĒc : Nat.card Ē = p ^ 3 := by rw [Subgroup.card_map_of_injective hinj, hcard]
  have hSU : SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n = GU1 h n :=
    (suid_unitaryInvolution_eq h n).trans (unitarySU_eq_gramSU h n)
  set ε : SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n ≃* GU1 h n :=
    MulEquiv.subgroupCongr hSU with hε
  set H : Subgroup (SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n) :=
    (seitzHyperGamma p E).comap (φ.comp ε.toMonoidHom) with hHdef
  have hH : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.HyperLift h κ Ē H := by
    intro g a b haE hbE ha1 hb hga hgb
    have hrel := relIndex_closure_pair_of_not_mem hp hĒa hĒc haE hbE ha1 hb
    obtain ⟨F, hFE, hFrel, hFmap⟩ := exists_hyperplane_of_le_map (modelAut θ) hinj
      (closure_pair_le haE hbE) hrel
    set gG : GL (Fin n) Kf := (g : GL (Fin n) Kf) with hgG
    have hcl : Subgroup.closure ({a, b} : Set (primeFormUnitary h (idGram Kf n))) ≤
        (Subgroup.centralizer {gG}).comap (primeFormUnitary h (idGram Kf n)).subtype := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
        exact Units.ext (by simpa only [Subgroup.coe_subtype, Units.val_mul] using hga.symm)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
        exact Units.ext (by simpa only [Subgroup.coe_subtype, Units.val_mul] using hgb.symm)
    show φ (ε g) ∈ seitzHyperGamma p E
    refine (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hFrel⟩ le_rfl) ?_
    intro e he
    have hκe : modelAut θ e ∈ (Subgroup.closure ({a, b} : Set _)).map κ := by
      rw [MonoidHom.map_closure, Set.image_pair]
      exact hFmap e he
    obtain ⟨w, hw, hwe⟩ := hκe
    have hwg := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (hcl hw))
    refine apply_eq_of_model_lift hGU θ (piG h n) φ hφθ e
      (primeFormConjSU h (idGram Kf n) w).toMonoidHom (fun x => ?_) ?_
    · rw [← hwe]
      exact primeFormConjHom_piG h w x
    · refine primeFormConjSU_eq_self_of_comm h w ?_
      have h1 : ((w : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
          (gG : Matrix (Fin n) (Fin n) Kf) =
          (gG : Matrix (Fin n) (Fin n) Kf) * ((w : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) := by
        have := congrArg Units.val hwg
        simpa only [Subgroup.coe_subtype, Units.val_mul] using this
      exact h1.symm
  have hker : ∀ g ∈ κ.ker, ∃ c : Kf,
      ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) = c • 1 := by
    intro g hg
    obtain ⟨c, -, hc⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn g).1 hg
    refine ⟨(c : Kf), ?_⟩
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have htop := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.hyperLift_eq_top_gu h hp
    hp2 hpq hq2 hn κ (E := Ē) (fun e he => hD he) hker
    (fun g ⟨c, hc⟩ =>
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.primeFormConjHom_eq_one_of_scalar
        h hc) hĒa hĒc hH
  rw [eq_top_iff]
  intro k _
  obtain ⟨x, rfl⟩ := hφ k
  have hx : ε.symm x ∈ H := by rw [htop]; exact Subgroup.mem_top _
  have : φ (ε (ε.symm x)) ∈ seitzHyperGamma p E := hx
  rwa [MulEquiv.apply_symm_apply] at this

end Inndiag

section LiftFix

variable {G P : Type*} [Group G] [Group P]

@[expose] def modelLiftFix (π : G →* P) (g : G) : Subgroup (MulAut P) where
  carrier := {β | ∃ α : MulAut G, α g = g ∧ ∀ x, β (π x) = π (α x)}
  one_mem' := ⟨1, rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro β₁ β₂ ⟨α₁, h₁, h₁'⟩ ⟨α₂, h₂, h₂'⟩
    refine ⟨α₁ * α₂, ?_, fun x => ?_⟩
    · rw [MulAut.mul_apply, h₂, h₁]
    · rw [MulAut.mul_apply, MulAut.mul_apply, h₂', h₁']
  inv_mem' := by
    rintro β ⟨α, hα, hα'⟩
    refine ⟨α⁻¹, ?_, fun x => ?_⟩
    · calc α⁻¹ g = α⁻¹ (α g) := by rw [hα]
        _ = g := MulAut.inv_apply_self G α g
    · have h1 := hα' (α⁻¹ x)
      rw [MulAut.apply_inv_self] at h1
      rw [← h1, MulAut.inv_apply_self]

theorem apply_eq_of_mem_modelLiftFix {K : Type*} [Group K] (hG : commutator G = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* P) (π : G →* P) (φ : G →* K)
    (hφ : ∀ x, θ ((φ x : K) : K ⧸ Subgroup.center K) = π x) {e : MulAut K} {g : G}
    (he : modelAut θ e ∈ modelLiftFix π g) : e (φ g) = φ g := by
  obtain ⟨α, hαg, hα⟩ := he
  exact apply_eq_of_model_lift hG θ π φ hφ e α.toMonoidHom hα hαg

end LiftFix

section Field

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.LieType.Chevalley

variable {ℓ f n : ℕ} {Kf : Type} [Field Kf]

theorem map_pow_eq_prod_smul_of_map_eq (σ : Kf ≃+* Kf) {Z : Matrix (Fin n) (Fin n) Kf} {c : Kf}
    (hZ : Z.map σ = c • Z) (j : ℕ) :
    Z.map (σ ^ j) = (∏ i ∈ Finset.range j, (σ ^ i) c) • Z := by
  induction j with
  | zero =>
    ext a b
    simp only [Matrix.map_apply, Finset.range_zero, Finset.prod_empty, one_smul]
    rw [pow_zero]
    rfl
  | succ j ih =>
    ext a b
    have hab := congrFun (congrFun hZ a) b
    have ihab := congrFun (congrFun ih a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hab ihab ⊢
    have hσ : ∀ x : Kf, (σ ^ (j + 1)) x = σ ((σ ^ j) x) := fun x => by rw [pow_succ']; rfl
    have hσi : ∀ (i : ℕ) (x : Kf), (σ ^ (i + 1)) x = σ ((σ ^ i) x) := fun i x => by
      rw [pow_succ']; rfl
    have h0 : (σ ^ 0) c = c := by rw [pow_zero]; rfl
    rw [hσ, ihab, map_mul, hab, map_prod, Finset.prod_range_succ', h0]
    simp only [hσi]
    ring

theorem exists_norm_one_glAut_fixed (h : UnitaryFieldData ℓ f Kf) (hn : 1 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : Kf ≃+* Kf} (hσ : orderOf σ = p)
    {z : primeFormUnitary h (idGram Kf n)} {c : Kfˣ}
    (hz : glAut σ (z : GL (Fin n) Kf) = (z : GL (Fin n) Kf) * GeneralLinearGroup.scalar (Fin n) c) :
    ∃ s : Kfˣ, h.norm (s : Kf) = 1 ∧
      glAut σ ((z : GL (Fin n) Kf) * GeneralLinearGroup.scalar (Fin n) s) =
        (z : GL (Fin n) Kf) * GeneralLinearGroup.scalar (Fin n) s := by
  classical
  haveI : Finite Kf := h.finite
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hZ : ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf).map σ =
      (c : Kf) • ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) := by
    have h1 := congrArg (fun g : GL (Fin n) Kf => (g : Matrix (Fin n) (Fin n) Kf)) hz
    simp only [coe_glAut, Units.val_mul, coe_scalarGL, Matrix.mul_smul, Matrix.mul_one] at h1
    exact h1
  have hZ0 : ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ≠ 0 := by
    intro h0
    have := Matrix.GeneralLinearGroup.det_ne_zero (z : GL (Fin n) Kf)
    rw [h0, Matrix.det_zero] at this
    exact this rfl
  have hN : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (c : Kf) = 1 := by
    have h1 := map_pow_eq_prod_smul_of_map_eq σ hZ (orderOf σ)
    rw [pow_orderOf_eq_one] at h1
    have h2 : ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf).map (1 : Kf ≃+* Kf) =
        ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) := by
      ext a b
      rfl
    rw [h2] at h1
    have h3 : (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (c : Kf) - 1) •
        ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hZ0
  obtain ⟨a, u, hu⟩ := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.exists_norm_ratio σ
    ![c, 1] 1 (fun i => by
      fin_cases i
      · exact hN
      · simp)
  have hu0 := hu 0
  have hu1 := hu 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, mul_one] at hu0 hu1
  set μ : Kfˣ := u 0 / u 1 with hμdef
  have hσμ : (c : Kf) * σ (μ : Kf) = μ := by
    have hu0' : ((u 0 : Kfˣ) : Kf) ≠ 0 := (u 0).ne_zero
    have hu1' : ((u 1 : Kfˣ) : Kf) ≠ 0 := (u 1).ne_zero
    have hσ0 : σ ((u 0 : Kfˣ) : Kf) ≠ 0 := (map_ne_zero σ).2 hu0'
    have hσ1 : σ ((u 1 : Kfˣ) : Kf) ≠ 0 := (map_ne_zero σ).2 hu1'
    have ha0 : (a : Kf) ≠ 0 := a.ne_zero
    have hc : (c : Kf) = ((u 0 : Kf) / σ (u 0)) / a := by
      rw [← hu0]
      field_simp
    rw [hc, hu1, hμdef, Units.val_div_eq_div_val, map_div₀]
    field_simp
  have hcN : h.norm (c : Kf) = 1 := by
    have hσz : glAut σ (z : GL (Fin n) Kf) ∈ primeFormUnitary h (idGram Kf n) :=
      glAut_mem_primeFormUnitary h isPrimeFormGram_one σ z.2
    have hmem : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram Kf n) := by
      have : GeneralLinearGroup.scalar (Fin n) c =
          (z : GL (Fin n) Kf)⁻¹ * glAut σ (z : GL (Fin n) Kf) := by rw [hz]; group
      rw [this]
      exact mul_mem (inv_mem z.2) hσz
    exact norm_eq_one_of_scalar_mem_primeFormUnitary h hn 1 hmem
  set ν : Kf := h.norm (μ : Kf) with hνdef
  have hνσ : σ ν = ν := by
    have h1 : h.norm (μ : Kf) = h.norm (c : Kf) * h.norm (σ (μ : Kf)) := by
      conv_lhs => rw [← hσμ]
      simp only [UnitaryFieldData.norm, map_mul]
      ring
    rw [hcN, one_mul] at h1
    have h2 : σ (h.norm (μ : Kf)) = h.norm (σ (μ : Kf)) := by
      simp only [UnitaryFieldData.norm, map_mul, map_bar_comm]
    rw [hνdef, h2, ← h1]
  have hνbar : h.bar ν = ν := by
    rw [hνdef, UnitaryFieldData.norm, map_mul, h.bar_bar, mul_comm]
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set ν₀ : fixSubfield σ := ⟨ν, hνσ⟩ with hν₀
  have hν₀bar : h₀.bar ν₀ = ν₀ := Subtype.ext (by rw [hbar]; exact hνbar)
  obtain ⟨l, hl⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_norm_eq h₀ hν₀bar
  have hlν : h.norm (l : Kf) = ν := by
    rw [norm_subtype h h₀ hbar, hl]
  have hν0 : ν ≠ 0 := by
    rw [hνdef, UnitaryFieldData.norm]
    exact mul_ne_zero μ.ne_zero ((map_ne_zero h.bar).2 μ.ne_zero)
  have hl0 : (l : Kf) ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hlν
    exact hν0 hlν.symm
  have hσl : σ (l : Kf) = l := l.2
  refine ⟨μ * (Units.mk0 (l : Kf) hl0)⁻¹, ?_, ?_⟩
  · have : h.norm (((μ * (Units.mk0 (l : Kf) hl0)⁻¹ : Kfˣ)) : Kf) =
        h.norm (μ : Kf) / h.norm (l : Kf) := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, UnitaryFieldData.norm,
        map_mul, map_inv₀]
      field_simp
    rw [this, hlν, ← hνdef, div_self hν0]
  · apply Units.ext
    rw [coe_glAut, Units.val_mul, coe_scalarGL, Matrix.mul_smul, Matrix.mul_one]
    ext a b
    have hab := congrFun (congrFun hZ a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hab ⊢
    rw [map_mul, hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀,
      hσl]
    linear_combination ((l : Kf)⁻¹ * ((z : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) a b) * hσμ

theorem exists_subfieldGU_conj_eq (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : Kf ≃+* Kf} (hσ : orderOf σ = p)
    {z : primeFormUnitary h (idGram Kf n)} {c : Kfˣ}
    (hz : glAut σ (z : GL (Fin n) Kf) = (z : GL (Fin n) Kf) * GeneralLinearGroup.scalar (Fin n) c) :
    ∃ W : primeFormUnitary (fixSubfield_unitaryFieldData h hp hp2 hσ) (idGram (fixSubfield σ) n),
      primeFormConjHom h (idGram Kf n) (QuasiHigh4.subfieldGU h _
          (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n W) =
        primeFormConjHom h (idGram Kf n) z := by
  obtain ⟨s, hs, hfix⟩ := exists_norm_one_glAut_fixed h (by omega) hp hp2 hσ hz
  set w : primeFormUnitary h (idGram Kf n) :=
    z * ⟨GeneralLinearGroup.scalar (Fin n) s, scalar_mem_primeFormUnitary_one h hs⟩ with hw
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n (σ := σ) (g := (w : GL (Fin n) Kf)) hfix
  have hmem : g₀ ∈ primeFormUnitary (fixSubfield_unitaryFieldData h hp hp2 hσ)
      (idGram (fixSubfield σ) n) :=
    QuasiHigh4.mem_primeFormUnitary_of_subfieldGL h _ (fixSubfield_unitaryFieldData_bar h hp hp2 hσ)
      n (by rw [hg₀]; exact w.2)
  refine ⟨⟨g₀, hmem⟩, ?_⟩
  have hW : QuasiHigh4.subfieldGU h _ (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n ⟨g₀, hmem⟩ =
      w := Subtype.ext hg₀
  rw [hW, hw, map_mul, (OuterUnitaryWide.conjHom_eq_one_iff h hn
    ⟨GeneralLinearGroup.scalar (Fin n) s, scalar_mem_primeFormUnitary_one h hs⟩).2 ⟨s, hs, rfl⟩,
    mul_one]

theorem conjHom_subfieldGU_eq_one_iff (h : UnitaryFieldData ℓ f Kf) {e : ℕ} {k : Subfield Kf}
    (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : Kf) = h.bar c) (hn : 3 ≤ n)
    (W : primeFormUnitary h₀ (idGram k n)) :
    primeFormConjHom h₀ (idGram k n) W = 1 ↔
      primeFormConjHom h (idGram Kf n) (QuasiHigh4.subfieldGU h h₀ hbar n W) = 1 := by
  rw [OuterUnitaryWide.conjHom_eq_one_iff h₀ hn, OuterUnitaryWide.conjHom_eq_one_iff h hn]
  constructor
  · rintro ⟨c, hc, hW⟩
    refine ⟨Units.map k.subtype.toMonoidHom c, ?_, ?_⟩
    · change h.norm ((c : k) : Kf) = 1
      rw [norm_subtype h h₀ hbar, hc, Subfield.coe_one]
    · rw [QuasiHigh4.coe_subfieldGU, hW, subfieldGL_scalar]
  · rintro ⟨c, hcN, hgc⟩
    have hentry : ∀ i j, ((((W : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j : k) : Kf) =
        if i = j then (c : Kf) else 0 := by
      intro i j
      have h1 := congrArg (fun x : GL (Fin n) Kf => (x : Matrix (Fin n) (Fin n) Kf) i j) hgc
      simp only [QuasiHigh4.coe_subfieldGU, coe_subfieldGL, GeneralLinearGroup.coe_scalar,
        scalar_apply, diagonal_apply, Matrix.map_apply] at h1
      exact h1
    set i₀ : Fin n := ⟨0, by omega⟩
    set c₀ : k := ((W : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i₀ i₀ with hc₀
    have hc₀c : (c₀ : Kf) = c := by
      rw [hc₀, hentry]
      simp
    have hc₀0 : c₀ ≠ 0 := fun h0 => c.ne_zero (by rw [← hc₀c, h0, Subfield.coe_zero])
    refine ⟨Units.mk0 c₀ hc₀0, ?_, ?_⟩
    · apply Subtype.val_injective
      rw [Units.val_mk0, ← norm_subtype h h₀ hbar, hc₀c, hcN, Subfield.coe_one]
    · apply subfieldGL_injective k n
      rw [show subfieldGL k n (W : GL (Fin n) k) =
        ((QuasiHigh4.subfieldGU h h₀ hbar n W : primeFormUnitary h _) : GL (Fin n) Kf) from rfl,
        hgc, subfieldGL_scalar]
      congr 1
      exact Units.ext hc₀c.symm

theorem exists_subfield_plane (h : UnitaryFieldData ℓ f Kf) {e : ℕ} {k : Subfield Kf}
    (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : Kf) = h.bar c) (hn : 3 ≤ n)
    {p : ℕ} {B : Subgroup (MulAut (primeFormP h (idGram Kf n)))} (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2)
    (hlift : ∀ b ∈ B, ∃ W : primeFormUnitary h₀ (idGram k n),
      primeFormConjHom h (idGram Kf n) (QuasiHigh4.subfieldGU h h₀ hbar n W) = b) :
    ∃ B₀ : Subgroup (MulAut (primeFormP h₀ (idGram k n))), IsElemAbelian p B₀ ∧
      Nat.card B₀ = p ^ 2 ∧ B₀ ≤ primeFormD h₀ (idGram k n) ∧
      ∀ W : primeFormUnitary h₀ (idGram k n), primeFormConjHom h₀ (idGram k n) W ∈ B₀ →
        primeFormConjHom h₀ (idGram k n) W ≠ 1 →
          primeFormConjHom h (idGram Kf n) (QuasiHigh4.subfieldGU h h₀ hbar n W) ∈ B ∧
          primeFormConjHom h (idGram Kf n) (QuasiHigh4.subfieldGU h h₀ hbar n W) ≠ 1 := by
  classical
  set κ := primeFormConjHom h (idGram Kf n) with hκ
  set κ₀ := primeFormConjHom h₀ (idGram k n) with hκ₀
  set ι := QuasiHigh4.subfieldGU h h₀ hbar n with hι
  have hiff : ∀ W, κ₀ W = 1 ↔ κ (ι W) = 1 := conjHom_subfieldGU_eq_one_iff h h₀ hbar hn
  set Ŵ : Subgroup (primeFormUnitary h₀ (idGram k n)) := B.comap (κ.comp ι) with hŴ
  set B₀ := Ŵ.map κ₀ with hB₀
  have hiff2 : ∀ W W', κ₀ W = κ₀ W' ↔ κ (ι W) = κ (ι W') := by
    intro W W'
    have h1 := hiff (W * W'⁻¹)
    simp only [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  refine ⟨B₀, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_, Subgroup.map_le_range _ _, ?_⟩
  · obtain ⟨W₁, hW₁, hx⟩ := x.2
    obtain ⟨W₂, hW₂, hy⟩ := y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, hiff2, map_mul,
      map_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨_, hW₁⟩ ⟨_, hW₂⟩)
  · rintro _ ⟨W, hW, rfl⟩
    rw [← map_pow, hiff, map_pow, map_pow]
    exact hB.2 _ hW
  ·
    let ψ : Ŵ →* B := ((κ.comp ι).comp Ŵ.subtype).codRestrict B fun x => x.2
    let ψ₀ : Ŵ →* B₀ := (κ₀.comp Ŵ.subtype).codRestrict B₀ fun x => ⟨x, x.2, rfl⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨b, hb⟩
      obtain ⟨W, hW⟩ := hlift b hb
      exact ⟨⟨W, show κ (ι W) ∈ B by rw [hW]; exact hb⟩, Subtype.ext hW⟩
    have hψ₀ : Function.Surjective ψ₀ := by
      rintro ⟨_, ⟨W, hW, rfl⟩⟩
      exact ⟨⟨W, hW⟩, rfl⟩
    have hker : ψ₀.ker = ψ.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      constructor
      · intro hx
        exact Subtype.ext ((hiff x).1 (congrArg Subtype.val hx))
      · intro hx
        exact Subtype.ext ((hiff x).2 (congrArg Subtype.val hx))
    rw [← hBc]
    exact Nat.card_congr ((QuotientGroup.quotientKerEquivOfSurjective ψ₀ hψ₀).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))).toEquiv
  · rintro W ⟨W₁, hW₁, hW₁W⟩ hW1
    have h1 : κ (ι W) = κ (ι W₁) := ((hiff2 W W₁).1 hW₁W.symm)
    refine ⟨h1 ▸ hW₁, fun h2 => hW1 ((hiff W).2 h2)⟩

theorem suSub_le_comap_seitzHyperGamma
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (h : UnitaryFieldData ℓ f Kf)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {σ : Kf ≃+* Kf} (hσ : orderOf σ = p) (hq₀ : ℓ ^ (f / p) ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n)) (φ : GU1 h n →* K)
    (hφθ : ∀ g, θ ((φ g : K) : K ⧸ Subgroup.center K) = piG h n g)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ ∈ E.map (modelAut θ)) :
    suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ)
      (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n ≤ (seitzHyperGamma p E).comap φ := by
  classical
  haveI : Finite Kf := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP Kf ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) Kf) := isPrimeFormGram_one
  have hne' : (n, ℓ ^ f) ≠ (3, 2) := fun h' => hne ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
  have hGU := commutator_GU1_eq_top h hn hne'
  haveI : Finite (primeFormP h (idGram Kf n)) :=
    Finite.of_surjective (piG h n) (QuotientGroup.mk'_surjective _)
  haveI : Finite (MulAut (primeFormP h (idGram Kf n))) := MulEquiv.finite_left
  set κ := primeFormConjHom h (idGram Kf n) with hκ
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  haveI : Finite (fixSubfield σ) := h₀.finite
  haveI : CharP (fixSubfield σ) ℓ := h₀.charP
  set ι := QuasiHigh4.subfieldGU h h₀ hbar n with hι
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hinj := modelAut_injective hperf θ
  set Ē := E.map (modelAut θ) with hĒdef
  have hĒa : IsElemAbelian p Ē := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hĒc : Nat.card Ē = p ^ 3 := by rw [Subgroup.card_map_of_injective hinj, hcard]
  have hpq₀ : p ∣ ℓ ^ (f / p) + 1 := by
    obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
    have hqq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by
      rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hpf]
    have h1 : (((ℓ ^ (f / p)) ^ p + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).2 (by rw [← hqq]; exact hpq)
    push_cast at h1
    rw [ZMod.pow_card] at h1
    exact (ZMod.natCast_eq_zero_iff _ p).1 (by push_cast; exact h1)
  have hισ : primeFormFieldFactor h hC hn hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : fσ ∉ primeFormD h (idGram Kf n) := by
    rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  set B := Ē ⊓ primeFormD h (idGram Kf n) with hBdef
  have hBc : Nat.card B = p ^ 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.card_inf_eq_sq_of_decomp hp hĒa hĒc
      hσE hσD (fun x hx =>
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.exists_zpow_mul_mem_primeFormD h
          hn hne hp hσ hĒa hx)
  have hBa : IsElemAbelian p B := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hĒa.2 x hx.1⟩
    have h' := congrArg Subtype.val (hĒa.1.is_comm.comm (⟨a, a.2.1⟩ : Ē) ⟨b, b.2.1⟩)
    exact h'
  have hlift : ∀ b ∈ B, ∃ W : primeFormUnitary h₀ (idGram (fixSubfield σ) n), κ (ι W) = b := by
    intro b hb
    obtain ⟨z, rfl⟩ := hb.2
    have hcomm : fσ * κ z = κ z * fσ :=
      congrArg Subtype.val (hĒa.1.is_comm.comm (⟨_, hσE⟩ : Ē) ⟨_, hb.1⟩)
    obtain ⟨c, hc⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.exists_glAut_eq_mul_scalar h hn
        hcomm
    exact exists_subfieldGU_conj_eq h hn hp hp2 hσ hc
  obtain ⟨B₀, hB₀a, hB₀c, hB₀D, hB₀⟩ := exists_subfield_plane h h₀ hbar hn hBa hBc hlift
  have htop := closure_liftCent_eq_top h₀ hn hq₀ hp hp2 hpq₀ hB₀a hB₀c hB₀D
  have hgen : ∀ g₀ ∈ liftCent h₀ n B₀,
      subfieldSU h h₀ hbar n g₀ ∈ (seitzHyperGamma p E).comap φ := by
    rintro g₀ ⟨W, hWB, hW1, hgW⟩
    obtain ⟨hbB, hb1⟩ := hB₀ W hWB hW1
    have hgsu : subfieldSU h h₀ hbar n g₀ ∈ suSub h h₀ hbar n := ⟨g₀, rfl⟩
    have hfix₁ : fσ ∈ modelLiftFix (piG h n) (subfieldSU h h₀ hbar n g₀) :=
      ⟨primeFormFieldSU h hC σ, primeFormFieldSU_eq_self_of_mem_suSub h h₀ hbar hgsu,
        fun x => primeFormFieldAut_mk h hC σ x⟩
    have hfix₂ : κ (ι W) ∈ modelLiftFix (piG h n) (subfieldSU h h₀ hbar n g₀) := by
      refine ⟨primeFormConjSU h (idGram Kf n) (ι W), primeFormConjSU_eq_self_of_comm h (ι W) ?_,
        fun x => primeFormConjHom_piG h (ι W) x⟩
      rw [coe_subfieldSU, hι, QuasiHigh4.coe_subfieldGU, coe_subfieldGL, coe_subfieldGL,
        ← Matrix.map_mul, ← Matrix.map_mul, hgW]
    have hle : Subgroup.closure ({κ (ι W), fσ} : Set (MulAut (primeFormP h (idGram Kf n)))) ≤
        modelLiftFix (piG h n) (subfieldSU h h₀ hbar n g₀) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hfix₂
      · exact hfix₁
    have hσb : fσ ∉ Subgroup.zpowers (κ (ι W)) := fun h' =>
      hσD ((Subgroup.zpowers_le.2 hbB.2) h')
    have hrel :=
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.relIndex_closure_pair_of_indep hp
        hĒa hĒc hbB.1 hσE hb1 hσb).2
    obtain ⟨F, hFE, hFrel, hFmap⟩ := exists_hyperplane_of_le_map (modelAut θ) hinj
      (closure_pair_le hbB.1 hσE) hrel
    show φ (subfieldSU h h₀ hbar n g₀) ∈ seitzHyperGamma p E
    refine (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hFrel⟩ le_rfl) ?_
    intro e he
    exact apply_eq_of_mem_modelLiftFix hGU θ (piG h n) φ hφθ (hle (hFmap e he))
  have hcl : Subgroup.closure (liftCent h₀ n B₀) ≤
      ((seitzHyperGamma p E).comap φ).comap (subfieldSU h h₀ hbar n) :=
    (Subgroup.closure_le _).2 hgen
  rintro _ ⟨g₀, rfl⟩
  exact hcl (htop ▸ Subgroup.mem_top g₀)

theorem seitzHyperGamma_eq_top_of_not_le_primeFormD_cover
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (h : UnitaryFieldData ℓ f Kf)
    (hn : 3 ≤ n) (hq2 : ℓ ^ f ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (h8 : ¬ (p = 3 ∧ ℓ ^ f = 8)) (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hout : ¬ E.map (modelAut θ) ≤ primeFormD h (idGram Kf n)) : seitzHyperGamma p E = ⊤ := by
  classical
  haveI : Finite Kf := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP Kf ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (primeFormP h (idGram Kf n)) :=
    Finite.of_surjective (piG h n) (QuotientGroup.mk'_surjective _)
  haveI : Finite (MulAut (primeFormP h (idGram Kf n))) := MulEquiv.finite_left
  have hq4 : 4 ≤ ℓ ^ f :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux.four_le_of_dvd_succ hp
      hp2 (pow_ne_zero _ h.prime.ne_zero) hpq hq2
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => hq2 h'.2
  have hne' : (n, ℓ ^ f) ≠ (3, 2) := fun h' => hq2 (Prod.mk.inj h').2
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hC : IsPrimeFormGram (1 : GL (Fin n) Kf) := isPrimeFormGram_one
  set ι := primeFormFieldFactor h hC hn hne with hι
  set κ := primeFormConjHom h (idGram Kf n) with hκ
  have hĒ : IsElemAbelian p (E.map (modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E.map (modelAut θ), a ∉ primeFormD h (idGram Kf n) := by
    by_contra hcon
    push Not at hcon
    exact hout fun a ha => hcon a ha
  have haι : ι a ≠ 1 := fun h1 => haD (by
    rw [← ker_primeFormFieldFactor h hC hn hne]
    exact h1)
  have ha1 : a ≠ 1 := fun h1 => haι (by rw [h1, map_one])
  have haord : orderOf a = p := orderOf_eq_prime (hĒ.2 a haE) ha1
  have hσp : (ι a) ^ p = 1 := by rw [← map_pow, hĒ.2 a haE, map_one]
  have hσord : orderOf (ι a) = p := orderOf_eq_prime hσp haι
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ a
      haord _ rfl hσord
  set σ := ι a with hσdef
  have hσ1 : σ ≠ 1 := haι
  have hpf : p ∣ f := (dvd_and_card_fixSubfield_unitary h hp hp2 hσord).1
  have hq₀ : ℓ ^ (f / p) ≠ 2 := by
    intro h2
    obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h2
    have hfp : f = p := by
      have := Nat.div_mul_cancel hpf
      rw [hf1, one_mul] at this
      exact this.symm
    have hpq' := hpq
    have h8' := h8
    rw [hℓ2, hfp] at hpq' h8'
    have h3 : p ∣ 3 := by
      have h1 : ((2 ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hpq'
      push_cast at h1
      rw [ZMod.pow_card] at h1
      have h4 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h1
      exact (ZMod.natCast_eq_zero_iff _ p).1 h4
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    exact h8' ⟨hp3, by rw [hp3]; norm_num⟩
  have hq₀' : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := fun h' => hq₀ h'.2
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  set fσ := primeFormFieldHom h hC σ with hfσdef
  set θ' : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n) := θ.trans (κ M)⁻¹ with hθ'
  set E' := E.map (modelAut θ') with hE'def
  have hE'eq : E' = (E.map (modelAut θ)).map (MulAut.congr (κ M)⁻¹).toMonoidHom := by
    rw [hE'def, Subgroup.map_map]
    congr 1
  have hE'a : IsElemAbelian p E' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE'c : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective (modelAut_injective hperf θ'), hcard]
  have hfσE : fσ ∈ E' := by
    rw [hE'eq]
    refine ⟨a, haE, ?_⟩
    change (κ M)⁻¹ * a * ((κ M)⁻¹)⁻¹ = _
    rw [inv_inv]
    exact hM
  obtain ⟨φ', hφ', hφθ'⟩ := exists_su_lift hperf h hn hne' (fun _ => hq4) θ'
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord with hhbar
  have h1 := suSub_le_comap_seitzHyperGamma hperf h hn hne hp hp2 hpq hσord hq₀ θ' φ' hφθ' hE
    hcard hfσE
  have hισ : ι fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn hne 1 σ
    rwa [map_one, one_mul] at this
  have hσD : fσ ∉ primeFormD h (idGram Kf n) := by
    rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  have hBc := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.card_inf_eq_sq_of_decomp hp
    hE'a hE'c hfσE hσD (fun x hx =>
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.exists_zpow_mul_mem_primeFormD h
        hn hne hp hσord hE'a hx)
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ E' ⊓ primeFormD h (idGram Kf n), b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E' ⊓ primeFormD h (idGram Kf n) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hBc
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have hιb : ι b = 1 := by
    rw [← MonoidHom.mem_ker, hι, ker_primeFormFieldFactor]
    exact hbB.2
  have hbσE : b * fσ ∈ E' := E'.mul_mem hbB.1 hfσE
  have hbσι : ι (b * fσ) = σ := by rw [map_mul, hιb, one_mul, hισ]
  have hbσ1 : b * fσ ≠ 1 := fun h1 => hσ1 (by rw [← hbσι, h1, map_one])
  have hbσord : orderOf (b * fσ) = p := orderOf_eq_prime (hE'a.2 _ hbσE) hbσ1
  obtain ⟨-, -, -, -, -, M', hM'⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ
      (b * fσ) hbσord σ hbσι hσord
  set θ'' : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n) := θ'.trans (κ M')⁻¹ with hθ''
  set φ'' : GU1 h n →* K := φ'.comp (primeFormConjSU h (idGram Kf n) M').toMonoidHom with hφ''
  have hφθ'' : ∀ g, θ'' ((φ'' g : K) : K ⧸ Subgroup.center K) = piG h n g := by
    intro g
    change (κ M')⁻¹ (θ' ((φ' (primeFormConjSU h (idGram Kf n) M' g) : K) :
      K ⧸ Subgroup.center K)) = piG h n g
    rw [hφθ', ← primeFormConjHom_piG, MulAut.inv_apply_self]
  have hfσE'' : fσ ∈ E.map (modelAut θ'') := by
    obtain ⟨e₂, he₂, he₂b⟩ := hbσE
    refine ⟨e₂, he₂, ?_⟩
    rw [hθ'', modelAut_trans, he₂b]
    change (κ M')⁻¹ * (b * fσ) * ((κ M')⁻¹)⁻¹ = fσ
    rw [inv_inv]
    exact hM'
  have h2 := suSub_le_comap_seitzHyperGamma hperf h hn hne hp hp2 hpq hσord hq₀ θ'' φ'' hφθ'' hE
    hcard hfσE''
  have hconj' : (b * fσ) * κ M' = κ M' * fσ := by
    calc (b * fσ) * κ M' = κ M' * ((κ M')⁻¹ * (b * fσ) * κ M') := by group
      _ = κ M' * fσ := by rw [hM']
  have hFmk : (subfieldPSU h h₀ hbar n).range = (suSub h h₀ hbar n).map
      (QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) n)) :=
    range_subfieldPSU_eq_map h h₀ hbar n
  have hfixF : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, fσ x = x := fun x hx =>
    range_subfieldPSU_le h n h₀ hbar hx
  have hne'' : (suSub h h₀ hbar n).map (primeFormConjSU h _ M').toMonoidHom ≠
      suSub h h₀ hbar n := by
    intro heq
    have hFmap : ((subfieldPSU h h₀ hbar n).range).map (κ M').toMonoidHom =
        (subfieldPSU h h₀ hbar n).range := by
      rw [hFmk, map_primeFormConjHom_map_mk h h₀ hbar n M', heq]
    have hfix' : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, (b * fσ) x = x := by
      intro x hx
      have hx' : x ∈ ((subfieldPSU h h₀ hbar n).range).map (κ M').toMonoidHom := by
        rw [hFmap]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      change (b * fσ) (κ M' y) = κ M' y
      rw [show (b * fσ) (κ M' y) = (b * fσ * κ M') y from rfl, hconj', MulAut.mul_apply,
        hfixF y hy]
    have hβ : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, b x = x := by
      intro x hx
      have h3 : (b * fσ) x = b (fσ x) := rfl
      rw [hfixF x hx] at h3
      rw [← h3]
      exact hfix' x hx
    obtain ⟨τ, -, hτ⟩ := eq_primeFormFieldHom_of_fix h n h₀ hbar hn hne hq₀' b hβ
    have hτ1 : τ = 1 := by
      have e1 := primeFormFieldFactor_apply h hC hn hne 1 τ
      rw [map_one, one_mul] at e1
      rw [← e1, ← hτ]
      exact hιb
    apply hb1
    rw [hτ, hτ1, map_one]
  have hgen := subfieldPairSUOdd_of_ne_two ℓ f (f / p) Kf h (fixSubfield σ) h₀ hbar p hp hp2 hfeq
    hq₀ n hn M' hne''
  have hcomap : (seitzHyperGamma p E).comap φ' = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (hg | ⟨g₁, hg₁, rfl⟩)
    · exact h1 hg
    · exact h2 hg₁
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hφ' y
  have hx : x ∈ (seitzHyperGamma p E).comap φ' := by rw [hcomap]; exact Subgroup.mem_top x
  exact hx

end Field

end CFSG.LieType.SeitzGeneration.QuasiHigh6
