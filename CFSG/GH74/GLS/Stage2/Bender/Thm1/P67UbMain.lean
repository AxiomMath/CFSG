module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbComm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnLift
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbZ
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbFour
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC

section Glue

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) [Finite K] [Fact p.Prime]
  [CharP K p]

theorem ub_SUid_eq :
    SUid (unitaryInvolution K p f) n = gramSU h (Cid n K) :=
  (SUid_eq_statedSU h.card_eq_sq n).trans (unitarySU_eq_gramSU h n)

@[expose] noncomputable def toT :
    SUid (unitaryInvolution K p f) n →* primeFormP h (Cid n K) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (Cid n K)) n)).comp
    (Subgroup.inclusion (le_of_eq (ub_SUid_eq h)))

theorem toT_surjective : Function.Surjective (toT h (n := n)) := by
  intro t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ t
  exact ⟨⟨y, by rw [ub_SUid_eq h]; exact y.2⟩, rfl⟩

theorem toT_conj (xU : ↥(primeFormUnitary h (Cid n K)))
    (g : SUid (unitaryInvolution K p f) n)
    (hcomm : (xU : GL (Fin n) K) * (g : GL (Fin n) K) * (xU : GL (Fin n) K)⁻¹ =
      (g : GL (Fin n) K)) :
    primeFormConjHom h (Cid n K) xU (toT h g) = toT h g := by
  have hg : (g : GL (Fin n) K) ∈ gramSU h (Cid n K) := by rw [← ub_SUid_eq h]; exact g.2
  show primeFormConjHom h (Cid n K) xU
    ((⟨(g : GL (Fin n) K), hg⟩ : gramSU h (Cid n K)) : primeFormP h (Cid n K)) = _
  rw [primeFormConjHom_mk]
  congr 1
  exact Subtype.ext hcomm

end Glue

section Main

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) [Finite K] [Fact p.Prime]
  [CharP K p]

theorem toT_mem_of_comm {V : Subgroup (MulAut (primeFormP h (Cid n K)))}
    (xU : ↥(primeFormUnitary h (Cid n K))) (hxV : primeFormConjHom h (Cid n K) xU ∈ V)
    (hx1 : primeFormConjHom h (Cid n K) xU ≠ 1)
    {x g : SUid (unitaryInvolution K p f) n} (hx : (xU : GL (Fin n) K) = (x : GL (Fin n) K))
    (hcomm : x * g = g * x) :
    toT h g ∈ ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v := by
  have hGL : (x : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * (x : GL (Fin n) K) := by
    have := congrArg (fun y : SUid (unitaryInvolution K p f) n => (y : GL (Fin n) K)) hcomm
    simpa using this
  have hc : (xU : GL (Fin n) K) * (g : GL (Fin n) K) * (xU : GL (Fin n) K)⁻¹ =
      (g : GL (Fin n) K) := by
    rw [hx, hGL]
    group
  have hfix : toT h g ∈ fixSub (primeFormConjHom h (Cid n K) xU) :=
    mem_fixSub.2 (toT_conj h xU g hc)
  have hle : fixSub (primeFormConjHom h (Cid n K) xU) ≤ ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v :=
    le_iSup₂_of_le (primeFormConjHom h (Cid n K) xU) hxV
      (le_iSup (fun _ : primeFormConjHom h (Cid n K) xU ≠ 1 =>
        fixSub (primeFormConjHom h (Cid n K) xU)) hx1)
  exact hle hfix

omit [Finite K] in
theorem ne_zero_of_herm_eq_one {σ : K ≃+* K} {u v : Fin n → K} (h : herm σ u v = 1) : u ≠ 0 := by
  rintro rfl
  rw [herm_zero_left] at h
  exact zero_ne_one h

omit [Finite K] in
theorem ne_zero_of_herm_eq_one' {σ : K ≃+* K} {u v : Fin n → K} (h : herm σ u v = 1) : v ≠ 0 := by
  rintro rfl
  rw [herm_zero_right] at h
  exact zero_ne_one h

theorem conj_ne_one_of_diagOn (hn3 : 3 ≤ n) {x : SUid (unitaryInvolution K p f) n}
    (xU : ↥(primeFormUnitary h (Cid n K))) (hx : (xU : GL (Fin n) K) = (x : GL (Fin n) K))
    {e₁ f₁ e₂ f₂ z : Fin n → K} (hF : FrameRel (unitaryInvolution K p f) e₁ f₁ e₂ f₂)
    {α β : K} (hD : DiagOn (unitaryInvolution K p f) x e₁ f₁ e₂ f₂ z α β)
    (hne : α ≠ α⁻¹ ∨ β ≠ β⁻¹) : primeFormConjHom h (Cid n K) xU ≠ 1 := by
  intro hc
  obtain ⟨c, hcs⟩ := (UnC.conj_eq_one_iff h hn3 xU).1 hc
  have hxv : ∀ v : Fin n → K, x • v = (c : K) • v := by
    intro v
    show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = _
    rw [← hx, hcs, GeneralLinearGroup.coe_scalar]
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  have he₁ : e₁ ≠ 0 := ne_zero_of_herm_eq_one hF.e1f1
  have hf₁ : f₁ ≠ 0 := ne_zero_of_herm_eq_one' hF.e1f1
  have he₂ : e₂ ≠ 0 := ne_zero_of_herm_eq_one hF.e2f2
  have hf₂ : f₂ ≠ 0 := ne_zero_of_herm_eq_one' hF.e2f2
  rcases hne with hne | hne
  · apply hne
    have h1 : α • e₁ = (c : K) • e₁ := by rw [← hD.e1, hxv]
    have h2 : α⁻¹ • f₁ = (c : K) • f₁ := by rw [← hD.f1, hxv]
    exact (smul_left_injective K he₁ h1).trans (smul_left_injective K hf₁ h2).symm
  · apply hne
    have h1 : β • e₂ = (c : K) • e₂ := by rw [← hD.e2, hxv]
    have h2 : β⁻¹ • f₂ = (c : K) • f₂ := by rw [← hD.f2, hxv]
    exact (smul_left_injective K he₂ h1).trans (smul_left_injective K hf₂ h2).symm

end Main

open CFSG.GH74.GLS.Stage2.OddAut CFSG.RankThree.Classical CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem false_of_u_block {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hn : n = 4 ∨ n = 5) {r : ℕ} (hrq : r ∣ p ^ f - 1)
    {V Z : Subgroup (MulAut (primeFormP h (Cid n K)))} (hVD : V ≤ primeFormD h (Cid n K))
    (h2 : N2Cfg (primeFormP h (Cid n K)) r V Z) (h3 : N3Full (primeFormP h (Cid n K)) V Z) :
    False := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hnq : ¬(n = 3 ∧ p ^ f = 2) := by omega
  obtain ⟨hr, hrodd, hVe, hVc, -, -, -, -, -⟩ := id h2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hrodd (by decide)
  have : Fact r.Prime := ⟨hr⟩
  have : IsElementaryAbelian r ↥V := hVe
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hrq' : ¬ r ∣ p ^ f + 1 := by
    intro hdiv
    have h1 : r ∣ (p ^ f + 1) - (p ^ f - 1) := Nat.dvd_sub hdiv hrq
    have h2' : (p ^ f + 1) - (p ^ f - 1) = 2 := by omega
    rw [h2'] at h1
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h1)
  obtain ⟨W, hWe, hWc, hWV, -, hWdet⟩ := UnC.exists_lift_group_u h hn3 hrq' hVD hVc
  have hWpow : ∀ x ∈ W, x ^ r = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := W) x hx
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => by
    have := hWe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥W) ⟨y, hy⟩
    exact congrArg Subtype.val this
  obtain ⟨a₀, ha₀, b₀, hb₀, hind₀, -⟩ := exists_basis_elemAbelian hr W hWc hWpow hWcomm
  set σ := unitaryInvolution K p f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hmem : ∀ x : ↥(primeFormUnitary h (Cid n K)),
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 → (x : GL (Fin n) K) ∈ SUid σ n :=
    fun x hx => by
      rw [hσdef, ub_SUid_eq h]
      exact ⟨x.2, hx⟩
  let a : SUid σ n := ⟨(a₀ : GL (Fin n) K), hmem a₀ (hWdet a₀ ha₀)⟩
  let b : SUid σ n := ⟨(b₀ : GL (Fin n) K), hmem b₀ (hWdet b₀ hb₀)⟩
  have hcoe : ∀ i j : ℕ, ((a ^ i * b ^ j : SUid σ n) : GL (Fin n) K) =
      ((a₀ ^ i * b₀ ^ j : ↥(primeFormUnitary h (Cid n K))) : GL (Fin n) K) := by
    intro i j
    simp [a, b]
  have hab : a * b = b * a := by
    have := hWcomm a₀ ha₀ b₀ hb₀
    apply Subtype.ext
    have h1 := congrArg (fun y : ↥(primeFormUnitary h (Cid n K)) => (y : GL (Fin n) K)) this
    simpa [a, b] using h1
  have ha : a ^ r = 1 := by
    apply Subtype.ext
    have h1 := congrArg (fun y : ↥(primeFormUnitary h (Cid n K)) => (y : GL (Fin n) K))
      (hWpow a₀ ha₀)
    simpa [a] using h1
  have hb : b ^ r = 1 := by
    apply Subtype.ext
    have h1 := congrArg (fun y : ↥(primeFormUnitary h (Cid n K)) => (y : GL (Fin n) K))
      (hWpow b₀ hb₀)
    simpa [b] using h1
  have hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → r ∣ i ∧ r ∣ j := by
    intro i j hij
    apply hind₀ i j
    apply Subtype.ext
    have h1 := congrArg (fun y : SUid σ n => (y : GL (Fin n) K)) hij
    rw [← hcoe i j]
    simpa using h1
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card_eq_sq]
    exact hrq.trans (by simpa using Nat.sub_dvd_pow_sub_pow (p ^ f) 1 2)
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hrK
  obtain ⟨ξ, hξ⟩ : ∃ ξ : K, IsPrimitiveRoot ξ r := by
    have h1 := IsPrimitiveRoot.orderOf ω₀
    rw [hω₀] at h1
    exact ⟨(ω₀ : K), IsPrimitiveRoot.coe_units_iff.mpr h1⟩
  have hσq : ∀ u : K, u ^ r = 1 → σ u = u := by
    intro u hu
    rw [hσdef, unitaryInvolution_apply]
    obtain ⟨t, ht⟩ := hrq
    have : p ^ f = r * t + 1 := by omega
    rw [this, pow_succ, pow_mul, hu, one_pow, one_mul]
  have hξr : ξ ^ r = 1 := hξ.pow_eq_one
  have hξ0 : ξ ≠ 0 := ne_zero_of_pow_eq_one hr.pos hξr
  have hξ1 : ξ ≠ 1 := hξ.ne_one hr.one_lt
  have hξinv : ξ ≠ ξ⁻¹ := by
    intro h'
    apply hξ1
    apply sq_eq_one_of_pow hr hr2 hξr
    calc ξ * ξ = ξ * ξ⁻¹ := by rw [← h']
      _ = 1 := mul_inv_cancel₀ hξ0
  have hσξ : σ ξ * ξ⁻¹ = 1 := by rw [hσq ξ hξr]; exact mul_inv_cancel₀ hξ0
  have hσξ' : σ ξ⁻¹ * ξ = 1 := by
    rw [map_inv₀, hσq ξ hξr]; exact inv_mul_cancel₀ hξ0
  obtain ⟨e₁, f₁, e₂, f₂, α₁, α₂, β₁, β₂, hF, hα₁, hα₂, hβ₁, hβ₂, ⟨ha1, ha2, ha3, ha4⟩,
    ⟨hb1, hb2, hb3, hb4⟩⟩ := exists_frame_weights hσ hr hr2 hξ hσq a b hab ha hb hind
  obtain ⟨z, hZ, hz0, hspan, hR⟩ := exists_z hσ hn hF
  have haz : a • z = z := fixes_z hσ hr hr2 hσq hZ hz0 hR ha hα₁ hα₂ ha1 ha2 ha3 ha4
  have hbz : b • z = z := fixes_z hσ hr hr2 hσq hZ hz0 hR hb hβ₁ hβ₂ hb1 hb2 hb3 hb4
  obtain ⟨xa, xb, x1, x1', ⟨ia, ja, hxa⟩, ⟨ib, jb, hxb⟩, ⟨i1, j1, hx1⟩, ⟨i1', j1', hx1'⟩,
    hDxa, hDxb, hDx1, hDx1'⟩ := exists_four_elements hr hr2 hξ
      (⟨ha1, ha2, ha3, ha4, haz⟩ : DiagOn σ a e₁ f₁ e₂ f₂ z α₁ α₂)
      (⟨hb1, hb2, hb3, hb4, hbz⟩ : DiagOn σ b e₁ f₁ e₂ f₂ z β₁ β₂) hα₁ hα₂ hβ₁ hβ₂ hind hspan
  have hxdata : ∀ (x : SUid σ n) (i j : ℕ), x = a ^ i * b ^ j →
      ∃ xU : ↥(primeFormUnitary h (Cid n K)), (xU : GL (Fin n) K) = (x : GL (Fin n) K) ∧
        primeFormConjHom h (Cid n K) xU ∈ V := by
    intro x i j hx
    refine ⟨a₀ ^ i * b₀ ^ j, ?_, ?_⟩
    · rw [hx, hcoe]
    · rw [map_mul, map_pow, map_pow]
      exact V.mul_mem (V.pow_mem (hWV a₀ ha₀) i) (V.pow_mem (hWV b₀ hb₀) j)
  obtain ⟨xaU, hxaU, hxaV⟩ := hxdata xa ia ja hxa
  obtain ⟨xbU, hxbU, hxbV⟩ := hxdata xb ib jb hxb
  obtain ⟨x1U, hx1U, hx1V⟩ := hxdata x1 i1 j1 hx1
  obtain ⟨x1'U, hx1'U, hx1'V⟩ := hxdata x1' i1' j1' hx1'
  have hxa1 := conj_ne_one_of_diagOn h hn3 xaU hxaU hF hDxa (Or.inl hξinv)
  have hxb1 := conj_ne_one_of_diagOn h hn3 xbU hxbU hF hDxb (Or.inr hξinv)
  have hx11 := conj_ne_one_of_diagOn h hn3 x1U hx1U hF hDx1 (Or.inl hξinv)
  have hx1'1 := conj_ne_one_of_diagOn h hn3 x1'U hx1'U hF hDx1' (Or.inl hξinv)
  set Hπ : Subgroup (primeFormP h (Cid n K)) := ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v with hHπ
  set Ĥ : Subgroup (SUid σ n) := Hπ.comap (toT h) with hĤ
  have hmemĤ : ∀ g : SUid σ n, toT h g ∈ Hπ → g ∈ Ĥ := fun g hg => hg
  have hS1 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x,
      g • x = x + (μ * herm σ e₁ x) • f₂ - (σ μ * herm σ f₂ x) • e₁ := by
    intro μ
    obtain ⟨g, -, hg⟩ := exists_mem_T_siegel hσ hF.e1e1 hF.f2f2 hF.e1f2 μ
    exact ⟨g, hmemĤ g (toT_mem_of_comm h x1U hx1V hx11 hx1U
      (comm_siegel hσ.invol hg hDx1.e1 hDx1.f2 hσξ)), hg⟩
  have hS2 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x,
      g • x = x + (μ * herm σ e₂ x) • f₁ - (σ μ * herm σ f₁ x) • e₂ := by
    intro μ
    obtain ⟨g, -, hg⟩ := exists_mem_T_siegel hσ hF.e2e2 hF.f1f1 hF.e2f1 μ
    exact ⟨g, hmemĤ g (toT_mem_of_comm h x1U hx1V hx11 hx1U
      (comm_siegel hσ.invol hg hDx1.e2 hDx1.f1 hσξ)), hg⟩
  have hS3 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x,
      g • x = x + (μ * herm σ e₁ x) • e₂ - (σ μ * herm σ e₂ x) • e₁ := by
    intro μ
    obtain ⟨g, -, hg⟩ := exists_mem_T_siegel hσ hF.e1e1 hF.e2e2 hF.e1e2 μ
    exact ⟨g, hmemĤ g (toT_mem_of_comm h x1'U hx1'V hx1'1 hx1'U
      (comm_siegel hσ.invol hg hDx1'.e1 hDx1'.e2 hσξ)), hg⟩
  have hS4 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x,
      g • x = x + (μ * herm σ f₁ x) • f₂ - (σ μ * herm σ f₂ x) • f₁ := by
    intro μ
    obtain ⟨g, -, hg⟩ := exists_mem_T_siegel hσ hF.f1f1 hF.f2f2 hF.f1f2 μ
    refine ⟨g, hmemĤ g (toT_mem_of_comm h x1'U hx1'V hx1'1 hx1'U
      (comm_siegel hσ.invol hg hDx1'.f1 hDx1'.f2 ?_)), hg⟩
    rw [inv_inv]
    exact hσξ'
  have hT : ∀ (a' : Fin n → K) (ha' : herm σ a' a' = 0) (c : K) (hc : c + σ c = 0),
      ((∃ c₁ c₂ : K, a' = vec4 e₁ f₁ e₂ f₂ c₁ c₂ 0 0) ∨
        (∃ c₃ c₄ : K, a' = vec4 e₁ f₁ e₂ f₂ 0 0 c₃ c₄)) → tv hσ.invol ha' hc ∈ Ĥ := by
    intro a' ha' c hc hcase
    rcases hcase with ⟨c₁, c₂, rfl⟩ | ⟨c₃, c₄, rfl⟩
    · have hfix : xb • vec4 e₁ f₁ e₂ f₂ c₁ c₂ 0 0 = vec4 e₁ f₁ e₂ f₂ c₁ c₂ 0 0 := by
        simp only [vec4, smul_add, smul_comm xb, hDxb.e1, hDxb.f1, one_smul, inv_one, smul_zero,
          zero_smul]
      exact hmemĤ _ (toT_mem_of_comm h xbU hxbV hxb1 hxbU
        (comm_tv (tv_smul hσ.invol ha' hc) hfix))
    · have hfix : xa • vec4 e₁ f₁ e₂ f₂ 0 0 c₃ c₄ = vec4 e₁ f₁ e₂ f₂ 0 0 c₃ c₄ := by
        simp only [vec4, smul_add, smul_comm xa, hDxa.e2, hDxa.f2, one_smul, inv_one, smul_zero,
          zero_smul]
      exact hmemĤ _ (toT_mem_of_comm h xaU hxaV hxa1 hxaU
        (comm_tv (tv_smul hσ.invol ha' hc) hfix))
  have hE : ∀ e : Fin n → K, (e = e₁ ∨ e = f₁ ∨ e = e₂ ∨ e = f₂) → ∀ (ν c : K)
      (hee : herm σ e e = 0) (hey : herm σ e (ν • z) = 0)
      (hc : c + σ c = -herm σ (ν • z) (ν • z)), eichler hσ.invol hee hey hc ∈ Ĥ := by
    intro e he ν c hee hey hc
    have hg := eichler_smul hσ.invol hee hey hc
    have hxz : ∀ x : SUid σ n, x • z = z → x • (ν • z) = ν • z := fun x hx => by
      rw [smul_comm, hx]
    rcases he with rfl | rfl | rfl | rfl
    · exact hmemĤ _ (toT_mem_of_comm h xbU hxbV hxb1 hxbU
        (comm_eichler hg (by rw [hDxb.e1, one_smul]) (hxz xb hDxb.z)))
    · exact hmemĤ _ (toT_mem_of_comm h xbU hxbV hxb1 hxbU
        (comm_eichler hg (by rw [hDxb.f1, inv_one, one_smul]) (hxz xb hDxb.z)))
    · exact hmemĤ _ (toT_mem_of_comm h xaU hxaV hxa1 hxaU
        (comm_eichler hg (by rw [hDxa.e2, one_smul]) (hxz xa hDxa.z)))
    · exact hmemĤ _ (toT_mem_of_comm h xaU hxaV hxa1 hxaU
        (comm_eichler hg (by rw [hDxa.f2, inv_one, one_smul]) (hxz xa hDxa.z)))
  have hTle := T_le_of_frame hσ hF Ĥ hZ hz0 hspan hS1 hS2 hS3 hS4 hT hE
  have hTtop : T σ n = ⊤ := T_eq_top hσ (by omega) (fun h3 => by omega)
  have hall : ∀ g : SUid σ n, toT h g ∈ Hπ := fun g => hTle (hTtop ▸ Subgroup.mem_top g)
  have hgen : Hπ = ⊤ := by
    rw [eq_top_iff]
    intro t _
    obtain ⟨g, rfl⟩ := toT_surjective h t
    exact hall g
  have hTn : ∃ x y : primeFormP h (Cid n K), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h hn3 hnq fun x y => hcon x y
  exact false_of_generation (isSimpleGroup_primeFormP_one h hn3 hnq) hTn h2 h3 hgen

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem false_of_u_nonplus {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hn : n = 4 ∨ n = 5) {r : ℕ} (hrp : r ≠ p) (hrq : ¬ r ∣ p ^ f + 1)
    {V Z : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hVD : V ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h2 : N2Cfg (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r V Z)
    (h3 : N3Full (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) V Z) : False := by
  have hr : r.Prime := h2.1
  by_cases hdiv : r ∣ p ^ f - 1
  · exact Ub.false_of_u_block h hn hdiv hVD h2 h3
  · refine UnC.false_of_u_cyclic h hn hrp ?_ hVD h2
    intro hdiv2
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hfac : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rcases (Nat.Prime.dvd_mul hr).1 (hfac ▸ hdiv2) with h' | h'
    · exact hdiv h'
    · exact hrq h'

end CFSG.GH74.GLS.Stage2.Bender.Thm1
