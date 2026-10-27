module

public import CFSG.ClassicalInvolution.Balance.StrongPowSu
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagUnitaryFrame

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (coordSet mem_coordSet exists_third
  mapGL coe_mapGL coe_mapGL_inv exists_pair_same exists_pair_of_card_four decide_eq_of_ne
  compIndicator compIndicator_mul_apply mul_compIndicator_apply compIndicator_apply)
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL exists_diagGL_of_offdiag_zero coe_diagGL
  coe_diagGL_inv)
open CFSG.ClassicalInvolution.Models (signOf suMat suMat_mul suMat_one suMat_inv_mul_suMat)

variable {K : Type} [Field K] {n : ℕ}

theorem SUid_le_GUid (σ : K ≃+* K) (n : ℕ) : SUid σ n ≤ GUid σ n := fun _ hg => hg.2

@[expose] noncomputable def suToGU (σ : K ≃+* K) (n : ℕ) : SUid σ n →* GUid σ n :=
  Subgroup.inclusion (SUid_le_GUid σ n)

theorem coe_suToGU (σ : K ≃+* K) (n : ℕ) (g : SUid σ n) :
    ((suToGU σ n g : GUid σ n) : GL (Fin n) K) = (g : GL (Fin n) K) := rfl

theorem conjSUid_conj (σ : K ≃+* K) (x : GUid σ n) (g y : SUid σ n) :
    conjSUid σ n x (g * y * g⁻¹) =
      g * conjSUid σ n ((suToGU σ n g)⁻¹ * x * suToGU σ n g) y * g⁻¹ := by
  apply Subtype.ext
  show ((x : GL (Fin n) K) * ((g : GL (Fin n) K) * (y : GL (Fin n) K) * (g : GL (Fin n) K)⁻¹) *
      (x : GL (Fin n) K)⁻¹) = (g : GL (Fin n) K) * (((g : GL (Fin n) K)⁻¹ * (x : GL (Fin n) K) *
        (g : GL (Fin n) K)) * (y : GL (Fin n) K) * ((g : GL (Fin n) K)⁻¹ * (x : GL (Fin n) K) *
          (g : GL (Fin n) K))⁻¹) * (g : GL (Fin n) K)⁻¹
  group

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

section Sign

theorem entry_eq_zero_of_comm_sign_gl (h2 : (2 : K) ≠ 0) {σ : Fin n → Bool}
    {D : Matrix (Fin n) (Fin n) K} {y : Su K p f n}
    (hD : D = diagonal fun i => signOf K (σ i))
    (hy : D * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D) {i j : Fin n} (hij : σ i ≠ σ j) :
    ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
  have h := congrFun (congrFun hy i) j
  simp only [hD, diagonal_mul, mul_diagonal] at h
  have h2' : (2 : K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
    cases hi : σ i <;> cases hj : σ j
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi, hj, signOf_true', signOf_false'] at h
      linear_combination (-1 : K) * h
    · rw [hi, hj, signOf_true', signOf_false'] at h
      linear_combination h
    · exact absurd (hi.trans hj.symm) hij
  exact (mul_eq_zero.mp h2').resolve_left h2

theorem compIndicator_comm_of_comm_sign_gl (h2 : (2 : K) ≠ 0) {σ : Fin n → Bool}
    {D : Matrix (Fin n) (Fin n) K} {y : Su K p f n}
    (hD : D = diagonal fun i => signOf K (σ i))
    (hy : D * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D) (b : Bool) :
    compIndicator K (coordSet σ b) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compIndicator K (coordSet σ b) := by
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hij : σ i = σ j
  · have : (i ∈ coordSet σ b) ↔ (j ∈ coordSet σ b) := by
      rw [mem_coordSet, mem_coordSet, hij]
    by_cases hi : i ∈ coordSet σ b
    · simp [hi, this.mp hi]
    · simp [hi, mt this.mpr hi]
  · rw [entry_eq_zero_of_comm_sign_gl h2 hD hy hij]
    simp

theorem comm_of_mem_coordBlockSU_gl {σ : Fin n → Bool} {D : Matrix (Fin n) (Fin n) K}
    {s : Su K p f n} (hD : D = diagonal fun i => signOf K (σ i)) (b : Bool)
    (hs : s ∈ coordBlockSU K p f (coordSet σ b)) :
    D * ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D := by
  rw [mem_coordBlockSU_iff] at hs
  rw [hD]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i ∈ coordSet σ b ∧ j ∈ coordSet σ b
  · rw [mem_coordSet, mem_coordSet] at hij
    rw [hij.1, ← hij.2]
    ring
  · have hor : i ∉ coordSet σ b ∨ j ∉ coordSet σ b := by tauto
    rw [hs i j hor]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]

theorem fixed_iff_comm {D : GL (Fin n) K} {δ : Su K p f n ≃* Su K p f n}
    (hδ : ∀ y, ((δ y : Su K p f n) : GL (Fin n) K) = D * (y : GL (Fin n) K) * D⁻¹)
    (y : Su K p f n) :
    δ y = y ↔ (D : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) := by
  rw [← Subtype.coe_inj, hδ, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    have := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) h
    simpa only [Units.val_mul] using this
  · intro h
    exact Units.ext (by simpa only [Units.val_mul] using h)

theorem isComponentOf_block_centralizer_gu (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (h2 : (2 : K) ≠ 0) {X : Type} [Group X] (Ψ : Su K p f n →* X)
    (hker : Ψ.ker ≤ Subgroup.center (Su K p f n)) (e : X) (σ : Fin n → Bool)
    (D : GL (Fin n) K) (δ : Su K p f n ≃* Su K p f n)
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (hδ : ∀ y, ((δ y : Su K p f n) : GL (Fin n) K) = D * (y : GL (Fin n) K) * D⁻¹)
    (hf : ∀ y, e * Ψ y * e⁻¹ = Ψ (δ y)) (b : Bool) (hcard : 2 ≤ (coordSet σ b).card) :
    CFSG.Open.IsComponentOf ((coordBlockSU K p f (coordSet σ b)).map Ψ)
      (Ψ.range ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have hQ : CFSG.Open.IsComponentOf (coordBlockSU K p f (coordSet σ b))
      (CFSG.ClassicalInvolution.Balance.fixedGroup δ) := by
    have hle : coordBlockSU K p f (coordSet σ b) ≤
        CFSG.ClassicalInvolution.Balance.fixedGroup δ := by
      intro s hs
      rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup, fixed_iff_comm hδ]
      exact comm_of_mem_coordBlockSU_gl hD b hs
    refine ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle ?_,
      isQuasisimple_coordBlockSU hK hq hcard⟩
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro s y hs hy
    have hyD := (fixed_iff_comm hδ y).mp (CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp hy)
    exact conj_mem_coordBlockSU (compIndicator_comm_of_comm_sign_gl h2 hD hyD b) hs
  have hmain := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 e δ
    (fun y => by simpa using hf y) hQ
  have e1 : (MulAut.conj (1 : Su K p f n)).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  rwa [e1, MonoidHom.comp_id] at hmain

end Sign

section Chart

variable {X : Type} [Group X]

theorem exists_chart_gu (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hn : 0 < n)
    (ψ : Su K p f n →* X) {f₁ f₂ : X} {x₁ x₂ : GUid (unitaryInvolution K p f) n}
    (hx₁ : ∀ y, f₁ * ψ y * f₁⁻¹ = ψ (conjSUid (unitaryInvolution K p f) n x₁ y))
    (hx₂ : ∀ y, f₂ * ψ y * f₂⁻¹ = ψ (conjSUid (unitaryInvolution K p f) n x₂ y))
    (hsq₁ : x₁ * x₁ = 1) (hsq₂ : x₂ * x₂ = 1) (hc : x₁ * x₂ = x₂ * x₁) :
    ∃ (P₀ : Su K p f n) (D₁ D₂ : GUid (unitaryInvolution K p f) n) (σ₁ σ₂ : Fin n → Bool),
      ((D₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal (fun i => signOf K (σ₁ i)) ∧
      ((D₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal (fun i => signOf K (σ₂ i)) ∧
      (∀ y, f₁ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₁⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom)
          (conjSUid (unitaryInvolution K p f) n D₁ y)) ∧
      (∀ y, f₂ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₂⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom)
          (conjSUid (unitaryInvolution K p f) n D₂ y)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.LieType.BorelTits.two_ne_zero_of_charP_ne_two p hp2
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hmat : ∀ x : GUid (unitaryInvolution K p f) n, x * x = 1 →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
    intro x h
    have := congrArg (fun z : GUid (unitaryInvolution K p f) n =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using this
  have hcm : ((x₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun z : GUid (unitaryInvolution K p f) n =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hc
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  obtain ⟨g₀, ε, h1, h2'⟩ := exists_gu_frame_signs hσ h2 hn (mem_GUid.mp x₁.2) (mem_GUid.mp x₂.2)
    (hmat x₁ hsq₁) (hmat x₂ hsq₂) hcm
  have hD : ∀ (x : GUid (unitaryInvolution K p f) n) (s : Fin n → Bool),
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * suMat g₀ =
        suMat g₀ * diagonal (fun j => signOf K (s j)) →
      ((((suToGU (unitaryInvolution K p f) n g₀)⁻¹ * x * suToGU (unitaryInvolution K p f) n g₀ :
        GUid (unitaryInvolution K p f) n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          diagonal (fun j => signOf K (s j)) := by
    intro x s hx
    show suMat (g₀⁻¹) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * suMat g₀ = _
    rw [Matrix.mul_assoc, hx, ← Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.one_mul]
  have hchart : ∀ (x : GUid (unitaryInvolution K p f) n) (e : X),
      (∀ y, e * ψ y * e⁻¹ = ψ (conjSUid (unitaryInvolution K p f) n x y)) →
      ∀ y, e * (ψ.comp (MulAut.conj g₀).toMonoidHom) y * e⁻¹ =
        (ψ.comp (MulAut.conj g₀).toMonoidHom) (conjSUid (unitaryInvolution K p f) n
          ((suToGU (unitaryInvolution K p f) n g₀)⁻¹ * x *
            suToGU (unitaryInvolution K p f) n g₀) y) := by
    intro x e hxe y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxe, conjSUid_conj]
  exact ⟨g₀, (suToGU (unitaryInvolution K p f) n g₀)⁻¹ * x₁ * suToGU (unitaryInvolution K p f) n g₀,
    (suToGU (unitaryInvolution K p f) n g₀)⁻¹ * x₂ * suToGU (unitaryInvolution K p f) n g₀,
    fun i => (ε i).1, fun i => (ε i).2, hD x₁ _ h1, hD x₂ _ h2', hchart x₁ f₁ hx₁,
    hchart x₂ f₂ hx₂⟩

end Chart

section Single

variable {X : Type} [Group X] [Finite X]

theorem act_diagonal_gu (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (Ψ : Su K p f n →* X) (hker : Ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : Ψ.range.Normal) (e : X) (σ : Fin n → Bool) (D : GL (Fin n) K)
    (δ : Su K p f n ≃* Su K p f n)
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (hδ : ∀ y, ((δ y : Su K p f n) : GL (Fin n) K) = D * (y : GL (Fin n) K) * D⁻¹)
    (hf : ∀ y, e * Ψ y * e⁻¹ = Ψ (δ y)) {d : X} (hd : d ∈ involutionOddCore e) :
    ∃ (u : Fin n → Kˣ) (α : Su K p f n →* Su K p f n), (∀ i j, σ i = σ j → u i = u j) ∧
      (∀ y, Ψ (α y) = d * Ψ y * d⁻¹) ∧
      ∀ y i j, ((α y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (u i : K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * ((u j)⁻¹ : Kˣ) := by
  have h2 : (2 : K) ≠ 0 := CFSG.LieType.BorelTits.two_ne_zero_of_charP_ne_two p hp2
  have hsub : CFSG.Open.IsSubnormal Ψ.range ⊤ :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have hdc : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSU K p f (coordSet σ b),
      d * Ψ s = Ψ s * d := by
    intro b hb s hs
    have hQ := isComponentOf_block_centralizer_gu hK hq h2 Ψ hker e σ D δ hD hδ hf b hb
    have hle := CFSG.ClassicalInvolution.Balance.le_centralizerLayer_of_isComponentOf hsub hQ
    exact CFSG.ClassicalInvolution.Balance.commute_of_mem_involutionOddCore_of_mem_centralizerLayer
      hd (hle ⟨s, hs, rfl⟩)
  have := hnorm
  have hkerR : Ψ.rangeRestrict.ker ≤ Subgroup.center (Su K p f n) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨α, g, φ, hαΨ, hαmat, -, -⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.unitaryAutClassification_isometry_of_card hK
      hp2 hq hn ↥Ψ.range Ψ.rangeRestrict Ψ.rangeRestrict_surjective hkerR (MulAut.conjNormal d)
  have hαd : ∀ x, Ψ (α x) = d * Ψ x * d⁻¹ := by
    intro x
    have h := congrArg Subtype.val (hαΨ x)
    simpa [MulAut.conjNormal_apply] using h
  have hfix : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSU K p f (coordSet σ b),
      α s = s := by
    intro b hb s hs
    have hperf : Group.IsPerfect ↥(coordBlockSU K p f (coordSet σ b)) :=
      ⟨(isQuasisimple_coordBlockSU hK hq hb).1⟩
    have hhom := hom_eq_of_central_ker_su Ψ hker (L := ↥(coordBlockSU K p f (coordSet σ b)))
      (α.comp (coordBlockSU K p f (coordSet σ b)).subtype)
      (coordBlockSU K p f (coordSet σ b)).subtype (fun l => by
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [hαd, hdc b hb l l.2, mul_inv_cancel_right])
    exact congrArg (fun h => (h ⟨s, hs⟩ : Su K p f n)) hhom
  have hpow : ∃ m : ℕ, Odd m ∧ ∀ x, α^[m] x = x := by
    refine ⟨orderOf d, odd_orderOf_of_mem_involutionOddCore hd, fun x => ?_⟩
    have hiter : ∀ k : ℕ, ∀ x, Ψ (α^[k] x) = d ^ k * Ψ x * (d ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', hαd, ih, pow_succ']
        group
    have hperfSu : Group.IsPerfect (Su K p f n) :=
      (isQuasisimple_su_of_two_le hK hq (by omega : 2 ≤ n)).1
    have hhom := hom_eq_of_central_ker_su Ψ hker (L := Su K p f n) (iterHom α (orderOf d))
      (MonoidHom.id _) (fun y => by
        rw [iterHom_apply, hiter, pow_orderOf_eq_one]
        simp)
    have := congrArg (fun h => (h x : Su K p f n)) hhom
    simpa [iterHom_apply] using this
  obtain ⟨hφ, u, hgu, hconst⟩ := diag_of_fixes_blocks_su hK hp2 hq hn σ α g φ hαmat hfix hpow
  refine ⟨u, α, hconst, hαd, fun y i j => ?_⟩
  rw [hαmat y, mapMatrix_eq_self hφ, hgu, coe_diagGL_inv]
  simp [coe_diagGL, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Single

section Delta

variable {X : Type} [Group X] [Finite X]

theorem deltaCore_trivial_gu (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (ψ : Su K p f n →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f' ∈ F, f' * f' = 1) (htoral : ToralDiagGU 2 ψ F) {d : X}
    (hd : d ∈ deltaCore F) {x : X} (hx : x ∈ ψ.range) : d * x = x * d := by
  obtain ⟨P, hP, hact⟩ := htoral
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := exists_pair_of_card_four hcard hF2
  have hdmem : ∀ f' ∈ F, f' ≠ 1 → d ∈ involutionOddCore f' := fun f' hf' hf'1 =>
    CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hd f' hf' hf'1
  obtain ⟨xa, hxaP, hxasq, hxa⟩ := hact a haF
  obtain ⟨xb, hxbP, hxbsq, hxb⟩ := hact b hbF
  obtain ⟨P₀, D₁, D₂, σ₁, σ₂, hD₁, hD₂, hch₁, hch₂⟩ := exists_chart_gu hK hp2 (by omega) ψ hxa hxb
    (by rwa [← pow_two]) (by rwa [← pow_two]) (hP xa hxaP xb hxbP)
  set Ψ' : Su K p f n →* X := ψ.comp (MulAut.conj P₀).toMonoidHom with hΨ'
  have hrange : Ψ'.range = ψ.range := CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : Ψ'.range.Normal := by
    rw [hrange]
    exact hnorm
  have hΨker := CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.ker_comp_conj_le_center ψ
    hker P₀
  have hD₃ : (((D₁ * D₂ : GUid (unitaryInvolution K p f) n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (decide (σ₁ i = σ₂ i)) := by
    simp only [Subgroup.coe_mul, Units.val_mul, hD₁, hD₂, diagonal_mul_diagonal]
    congr 1
    funext i
    exact signOf_mul_decide _ _
  have hch₃ : ∀ y, (a * b) * Ψ' y * (a * b)⁻¹ =
      Ψ' (conjSUid (unitaryInvolution K p f) n (D₁ * D₂) y) := by
    intro y
    have e : (a * b) * Ψ' y * (a * b)⁻¹ = a * (b * Ψ' y * b⁻¹) * a⁻¹ := by group
    rw [e, hch₂ y, hch₁, map_mul]
    rfl
  obtain ⟨u₁, α₁, hc₁, hα₁, hm₁⟩ := act_diagonal_gu hK hp2 hq hn Ψ' hΨker hΨnorm a σ₁
    (D₁ : GL (Fin n) K) (conjSUid (unitaryInvolution K p f) n D₁) hD₁
    (fun y => coe_conjSUid _ n D₁ y) hch₁ (hdmem a haF ha1)
  obtain ⟨u₂, α₂, hc₂, hα₂, hm₂⟩ := act_diagonal_gu hK hp2 hq hn Ψ' hΨker hΨnorm b σ₂
    (D₂ : GL (Fin n) K) (conjSUid (unitaryInvolution K p f) n D₂) hD₂
    (fun y => coe_conjSUid _ n D₂ y) hch₂ (hdmem b hbF hb1)
  obtain ⟨u₃, α₃, hc₃, hα₃, hm₃⟩ := act_diagonal_gu hK hp2 hq hn Ψ' hΨker hΨnorm (a * b) _
    ((D₁ * D₂ : GUid (unitaryInvolution K p f) n) : GL (Fin n) K)
    (conjSUid (unitaryInvolution K p f) n (D₁ * D₂)) hD₃ (fun y => coe_conjSUid _ n _ y) hch₃
    (hdmem _ (F.mul_mem haF hbF) hab1)
  have hperfSu : Group.IsPerfect (Su K p f n) :=
    (isQuasisimple_su_of_two_le hK hq (by omega : 2 ≤ n)).1
  have hagree : ∀ (β γ : Su K p f n →* Su K p f n), (∀ y, Ψ' (β y) = d * Ψ' y * d⁻¹) →
      (∀ y, Ψ' (γ y) = d * Ψ' y * d⁻¹) → ∀ y, β y = γ y := by
    intro β γ hβ hγ y
    have := hom_eq_of_central_ker_su Ψ' hΨker (L := Su K p f n) β γ (fun y => by rw [hβ, hγ])
    exact congrArg (fun h => (h y : Su K p f n)) this
  have hratio : ∀ (β γ : Su K p f n →* Su K p f n) (v w : Fin n → Kˣ), (∀ y, β y = γ y) →
      (∀ y i j, ((β y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (v i : K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * ((v j)⁻¹ : Kˣ)) →
      (∀ y i j, ((γ y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (w i : K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * ((w j)⁻¹ : Kˣ)) →
      ∀ i j, i ≠ j → v i * (v j)⁻¹ = w i * (w j)⁻¹ := by
    intro β γ v w hβγ hv hw i j hij
    obtain ⟨wm, hwm⟩ := exists_swapEl hK hq hij
    have h1 := congrArg (fun z : Su K p f n =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) (hβγ wm)
    simp only [hv, hw, hwm, unitSignedSwapMatrix_apply'', Equiv.swap_apply_left, ite_true] at h1
    apply Units.ext
    have h3 : (v i : K) * ((v j)⁻¹ : Kˣ) * (-1) = (w i : K) * ((w j)⁻¹ : Kˣ) * (-1) := by
      linear_combination h1
    have := neg_inj.mp (by linear_combination h3 : -((v i : K) * ((v j)⁻¹ : Kˣ)) =
      -((w i : K) * ((w j)⁻¹ : Kˣ)))
    simpa using this
  have e12 := hagree α₁ α₂ hα₁ hα₂
  have e13 := hagree α₁ α₃ hα₁ hα₃
  have hconst := const_of_three σ₁ σ₂ u₁ u₂ u₃ hc₁ hc₂ hc₃
    (hratio α₁ α₂ u₁ u₂ e12 hm₁ hm₂) (hratio α₁ α₃ u₁ u₃ e13 hm₁ hm₃)
  have hid : ∀ y, α₁ y = y := by
    intro y
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    rw [hm₁, hconst i j, mul_right_comm, Units.mul_inv, one_mul]
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  have := hα₁ y
  rw [hid y] at this
  exact mul_inv_eq_iff_eq_mul.mp this.symm

end Delta

theorem deltaCore_trivial_su_gf {e : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (hn : 3 ≤ n) {X : Type}
    [Group X] [Finite X] (ψ : Su (GaloisField p (2 * e)) p e n →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e n)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f' ∈ F, f' * f' = 1)
    (htoral : ToralDiagGU 2 ψ F) {d : X} (hd : d ∈ deltaCore F) {x : X} (hx : x ∈ ψ.range) :
    d * x = x * d :=
  deltaCore_trivial_gu
    (CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq h5) hp2 h5 hn ψ
    hker hnorm hcard hF2 htoral hd hx

end CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
