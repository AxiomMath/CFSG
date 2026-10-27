module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuDiag
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinear
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalUnitary

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (coordSet mem_coordSet exists_third
  mapGL coe_mapGL coe_mapGL_inv exists_pair_same exists_pair_of_card_four decide_eq_of_ne)
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL exists_diagGL_of_offdiag_zero coe_diagGL
  coe_diagGL_inv)
open CFSG.ClassicalInvolution.Models (signOf suMat suMat_mul suMat_one suMat_inv_mul_suMat)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem hom_eq_of_central_ker_su {X : Type*} [Group X] (Ψ : Su K p f n →* X)
    (hker : Ψ.ker ≤ Subgroup.center (Su K p f n)) {L : Type*} [Group L] [Group.IsPerfect L]
    (f₁ f₂ : L →* Su K p f n) (h : ∀ l, Ψ (f₁ l) = Ψ (f₂ l)) : f₁ = f₂ := by
  refine CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center f₂ f₁ fun l => ?_
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, h l, inv_mul_cancel]


omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem signOf_mul_self' (b : Bool) : signOf K b * signOf K b = (1 : K) := by
  cases b <;> simp [signOf]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem signOf_mul_decide (a b : Bool) :
    signOf K a * signOf K b = signOf K (decide (a = b)) := by
  cases a <;> cases b <;> simp [signOf]

theorem sign_inv_eq {σ : Fin n → Bool} {D : Su K p f n}
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i)) :
    D⁻¹ = D := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext ?_))
  simp only [Subgroup.coe_mul, Units.val_mul, hD, diagonal_mul_diagonal, Subgroup.coe_one,
    Units.val_one]
  rw [← diagonal_one]
  congr 1
  funext i
  exact signOf_mul_self' _

theorem entry_sign_conj {σ : Fin n → Bool} {D : Su K p f n}
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (y : Su K p f n) (i j : Fin n) :
    ((D * y * D⁻¹ : Su K p f n) : GL (Fin n) K).val i j =
      signOf K (σ i) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * signOf K (σ j) := by
  rw [sign_inv_eq hD]
  simp only [Subgroup.coe_mul, Units.val_mul, hD, diagonal_mul, mul_diagonal]

section Chart

variable {X : Type} [Group X]

theorem exists_chart_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hn : 0 < n)
    (ψ : Su K p f n →* X) {f₁ f₂ : X} {x₁ x₂ : Su K p f n}
    (hx₁ : ∀ y, f₁ * ψ y * f₁⁻¹ = ψ (x₁ * y * x₁⁻¹))
    (hx₂ : ∀ y, f₂ * ψ y * f₂⁻¹ = ψ (x₂ * y * x₂⁻¹)) (hsq₁ : x₁ * x₁ = 1) (hsq₂ : x₂ * x₂ = 1)
    (hc : x₁ * x₂ = x₂ * x₁) :
    ∃ (P₀ D₁ D₂ : Su K p f n) (σ₁ σ₂ : Fin n → Bool),
      ((D₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (fun i => signOf K (σ₁ i)) ∧
      ((D₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (fun i => signOf K (σ₂ i)) ∧
      (∀ y, f₁ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₁⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (D₁ * y * D₁⁻¹)) ∧
      (∀ y, f₂ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f₂⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (D₂ * y * D₂⁻¹)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.LieType.BorelTits.two_ne_zero_of_charP_ne_two p hp2
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨g₀, ε, h1, h2'⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_su_frame_signs hσ h2 hn
    (i₁ := x₁) (i₂ := x₂) (by rw [← suMat_mul, hsq₁, suMat_one])
    (by rw [← suMat_mul, hsq₂, suMat_one]) (by rw [← suMat_mul, ← suMat_mul, hc])
  have hD : ∀ (x : Su K p f n) (s : Fin n → Bool),
      suMat x * suMat g₀ = suMat g₀ * diagonal (fun j => signOf K (s j)) →
      ((g₀⁻¹ * x * g₀ : Su K p f n) : GL (Fin n) K).val = diagonal (fun j => signOf K (s j)) := by
    intro x s hx
    show suMat (g₀⁻¹ * x * g₀) = _
    rw [suMat_mul, suMat_mul, Matrix.mul_assoc, hx, ← Matrix.mul_assoc, suMat_inv_mul_suMat,
      Matrix.one_mul]
  have hchart : ∀ (x : Su K p f n) (e : X) (D : Su K p f n),
      (∀ y, e * ψ y * e⁻¹ = ψ (x * y * x⁻¹)) → D = g₀⁻¹ * x * g₀ →
      ∀ y, e * (ψ.comp (MulAut.conj g₀).toMonoidHom) y * e⁻¹ =
        (ψ.comp (MulAut.conj g₀).toMonoidHom) (D * y * D⁻¹) := by
    intro x e D hxe hDe y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxe, hDe]
    congr 1
    group
  exact ⟨g₀, g₀⁻¹ * x₁ * g₀, g₀⁻¹ * x₂ * g₀, fun i => (ε i).1, fun i => (ε i).2,
    hD x₁ _ h1, hD x₂ _ h2', hchart x₁ f₁ _ hx₁ rfl, hchart x₂ f₂ _ hx₂ rfl⟩

end Chart


section Single

variable {X : Type} [Group X] [Finite X]

@[expose] def iterHom {M : Type*} [Monoid M] (α : M →* M) : ℕ → (M →* M)
  | 0 => MonoidHom.id M
  | k + 1 => α.comp (iterHom α k)

theorem iterHom_apply {M : Type*} [Monoid M] (α : M →* M) (k : ℕ) (x : M) :
    iterHom α k x = α^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact congrArg α ih

theorem act_diagonal_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (Ψ : Su K p f n →* X) (hker : Ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : Ψ.range.Normal) (e : X) (σ : Fin n → Bool) (D : Su K p f n)
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (hf : ∀ y, e * Ψ y * e⁻¹ = Ψ (D * y * D⁻¹)) {d : X} (hd : d ∈ involutionOddCore e) :
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
    have hQ := isComponentOf_block_centralizer_su hK hq h2 Ψ hker e σ D hD hf b hb
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


section Commutator

variable {X : Type} [Group X] [Finite X]

theorem commutator_trivial_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (ψ : Su K p f n →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (P : Subgroup (Su K p f n))
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f' ∈ F, ∃ x ∈ P, x * x = 1 ∧ ∀ y, f' * ψ y * f'⁻¹ = ψ (x * y * x⁻¹))
    {f₀ : X} (hf₀ : f₀ ∈ F) {d : X} (hd : d ∈ involutionOddCore f₀) {g₀ : X} (hg₀ : g₀ ∈ F)
    {x : X} (hx : x ∈ ψ.range) : d * g₀ * x * (d * g₀)⁻¹ = g₀ * d * x * (g₀ * d)⁻¹ := by
  obtain ⟨x₁, hx₁P, hx₁sq, hx₁⟩ := hact f₀ hf₀
  obtain ⟨x₂, hx₂P, hx₂sq, hx₂⟩ := hact g₀ hg₀
  obtain ⟨P₀, D₁, D₂, σ₁, σ₂, hD₁, hD₂, hch₁, hch₂⟩ := exists_chart_su hK hp2 (by omega) ψ hx₁ hx₂
    hx₁sq hx₂sq (hP x₁ hx₁P x₂ hx₂P)
  have hrange : (ψ.comp (MulAut.conj P₀).toMonoidHom).range = ψ.range :=
    CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : (ψ.comp (MulAut.conj P₀).toMonoidHom).range.Normal := by
    rw [hrange]
    exact hnorm
  obtain ⟨u, α, -, hαΨ, hαmat⟩ := act_diagonal_su hK hp2 hq hn _
    (CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.ker_comp_conj_le_center ψ hker P₀)
    hΨnorm f₀ σ₁ D₁ hD₁ hch₁ hd
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  have e1 : d * g₀ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (d * g₀)⁻¹ =
      d * (g₀ * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * g₀⁻¹) * d⁻¹ := by group
  have e2 : g₀ * d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (g₀ * d)⁻¹ =
      g₀ * (d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * d⁻¹) * g₀⁻¹ := by group
  have hcomm : α (D₂ * y * D₂⁻¹) = D₂ * α y * D₂⁻¹ := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    rw [hαmat, entry_sign_conj hD₂, entry_sign_conj hD₂, hαmat]
    ring
  rw [e1, e2, hch₂ y, ← hαΨ (D₂ * y * D₂⁻¹), ← hαΨ y, hch₂ (α y), hcomm]

end Commutator

section Delta

variable {X : Type} [Group X] [Finite X]

omit [Finite K] in
theorem const_of_three (σ₁ σ₂ : Fin n → Bool) (u₁ u₂ u₃ : Fin n → Kˣ)
    (hc₁ : ∀ i j, σ₁ i = σ₁ j → u₁ i = u₁ j) (hc₂ : ∀ i j, σ₂ i = σ₂ j → u₂ i = u₂ j)
    (hc₃ : ∀ i j, decide (σ₁ i = σ₂ i) = decide (σ₁ j = σ₂ j) → u₃ i = u₃ j)
    (r12 : ∀ i j, i ≠ j → u₁ i * (u₁ j)⁻¹ = u₂ i * (u₂ j)⁻¹)
    (r13 : ∀ i j, i ≠ j → u₁ i * (u₁ j)⁻¹ = u₃ i * (u₃ j)⁻¹) : ∀ i j, u₁ i = u₁ j := by
  intro i j
  by_cases hij : σ₁ i = σ₁ j
  · exact hc₁ i j hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    by_cases hij₂ : σ₂ i = σ₂ j
    · have h1 := r12 i j hne
      rw [hc₂ i j hij₂, mul_inv_cancel] at h1
      exact mul_inv_eq_one.mp h1
    · have hx := decide_eq_of_ne hij hij₂
      have h1 := r13 i j hne
      rw [hc₃ i j hx, mul_inv_cancel] at h1
      exact mul_inv_eq_one.mp h1

theorem deltaCore_trivial_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (ψ : Su K p f n →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f' ∈ F, f' * f' = 1) (P : Subgroup (Su K p f n))
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f' ∈ F, ∃ x ∈ P, x * x = 1 ∧ ∀ y, f' * ψ y * f'⁻¹ = ψ (x * y * x⁻¹))
    {d : X} (hd : d ∈ deltaCore F) {x : X} (hx : x ∈ ψ.range) : d * x = x * d := by
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := exists_pair_of_card_four hcard hF2
  have hdmem : ∀ f' ∈ F, f' ≠ 1 → d ∈ involutionOddCore f' := fun f' hf' hf'1 =>
    CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hd f' hf' hf'1
  obtain ⟨xa, hxaP, hxasq, hxa⟩ := hact a haF
  obtain ⟨xb, hxbP, hxbsq, hxb⟩ := hact b hbF
  obtain ⟨P₀, D₁, D₂, σ₁, σ₂, hD₁, hD₂, hch₁, hch₂⟩ := exists_chart_su hK hp2 (by omega) ψ hxa hxb
    hxasq hxbsq (hP xa hxaP xb hxbP)
  set Ψ' : Su K p f n →* X := ψ.comp (MulAut.conj P₀).toMonoidHom with hΨ'
  have hrange : Ψ'.range = ψ.range := CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : Ψ'.range.Normal := by
    rw [hrange]
    exact hnorm
  have hΨker := CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.ker_comp_conj_le_center ψ
    hker P₀
  have hD₃ : ((D₁ * D₂ : Su K p f n) : GL (Fin n) K).val =
      diagonal fun i => signOf K (decide (σ₁ i = σ₂ i)) := by
    simp only [Subgroup.coe_mul, Units.val_mul, hD₁, hD₂, diagonal_mul_diagonal]
    congr 1
    funext i
    exact signOf_mul_decide _ _
  have hch₃ : ∀ y, (a * b) * Ψ' y * (a * b)⁻¹ = Ψ' ((D₁ * D₂) * y * (D₁ * D₂)⁻¹) := by
    intro y
    have e : (a * b) * Ψ' y * (a * b)⁻¹ = a * (b * Ψ' y * b⁻¹) * a⁻¹ := by group
    rw [e, hch₂ y, hch₁]
    congr 1
    group
  obtain ⟨u₁, α₁, hc₁, hα₁, hm₁⟩ := act_diagonal_su hK hp2 hq hn Ψ' hΨker hΨnorm a σ₁ D₁ hD₁ hch₁
    (hdmem a haF ha1)
  obtain ⟨u₂, α₂, hc₂, hα₂, hm₂⟩ := act_diagonal_su hK hp2 hq hn Ψ' hΨker hΨnorm b σ₂ D₂ hD₂ hch₂
    (hdmem b hbF hb1)
  obtain ⟨u₃, α₃, hc₃, hα₃, hm₃⟩ := act_diagonal_su hK hp2 hq hn Ψ' hΨker hΨnorm (a * b) _
    (D₁ * D₂) hD₃ hch₃ (hdmem _ (F.mul_mem haF hbF) hab1)
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

theorem strongConclusion_su {X : Type} [Group X] [Finite X] (hK : Nat.card K = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hn : 3 ≤ n) (ψ : Su K p f n →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f n)) (hnorm : ψ.range.Normal) {F : Subgroup X}
    (hcard : Nat.card F = 4) (hF2 : ∀ f' ∈ F, f' * f' = 1) (P : Subgroup (Su K p f n))
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f' ∈ F, ∃ x ∈ P, x * x = 1 ∧ ∀ y, f' * ψ y * f'⁻¹ = ψ (x * y * x⁻¹)) :
    StrongConclusion ψ.range F :=
  ⟨fun _ hd _ hx => deltaCore_trivial_su hK hp2 hq hn ψ hker hnorm hcard hF2 P hP hact hd hx,
    fun _ hf _ _ hd _ hg _ hx => commutator_trivial_su hK hp2 hq hn ψ hker hnorm P hP hact hf hd
      hg hx⟩

end CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
