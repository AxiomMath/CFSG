module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ1

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three


section Field

variable {K : Type} [Field K] [Finite K]

theorem graph_mul_normal (ε : ℕ) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    d4Graph K ε * exactNormalAut Tag.D4 K a σ 0 =
      exactNormalAut Tag.D4 K (fun j => a ((d4Rho ^ ε).symm j)) σ 0 * d4Graph K ε := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [MulAut.mul_apply, MulAut.mul_apply, d4Graph_adjX]
    change d4Graph K ε (exactNormalAut Tag.D4 K a σ 0 (adjX Tag.D4 K i c)) = _
    rw [exactNormalAut_adjX, d4Graph_adjX]
    change _ = exactNormalAut Tag.D4 K _ σ 0 (adjX Tag.D4 K ((d4Rho ^ ε) i) c)
    rw [exactNormalAut_adjX]
    simp [exactPerm_D4]
  · rw [MulAut.mul_apply, MulAut.mul_apply, d4Graph_adjY]
    change d4Graph K ε (exactNormalAut Tag.D4 K a σ 0 (adjY Tag.D4 K i c)) = _
    rw [exactNormalAut_adjY, d4Graph_adjY]
    change _ = exactNormalAut Tag.D4 K _ σ 0 (adjY Tag.D4 K ((d4Rho ^ ε) i) c)
    rw [exactNormalAut_adjY]
    simp [exactPerm_D4]

theorem normal_inj {a a' : Fin Tag.D4.rank → Kˣ} {σ σ' : K ≃+* K}
    (h : exactNormalAut Tag.D4 K a σ 0 = exactNormalAut Tag.D4 K a' σ' 0) : a = a' ∧ σ = σ' := by
  have hx : ∀ i c, (a i : K) * σ c = (a' i : K) * σ' c := by
    intro i c
    have h1 := congrArg (fun m => m (adjX Tag.D4 K i c)) h
    simp only [exactNormalAut_adjX, exactPerm_D4, Equiv.Perm.one_apply] at h1
    exact adjX_injective i h1
  have ha : a = a' := by
    funext i
    have h1 := hx i 1
    simp only [map_one, mul_one] at h1
    exact Units.ext h1
  refine ⟨ha, RingEquiv.ext fun c => ?_⟩
  have h1 := hx 0 c
  rw [ha] at h1
  exact mul_left_cancel₀ (Units.ne_zero _) h1

def HasField (X : MulAut (adjointGroup Tag.D4 K)) (σ : K ≃+* K) : Prop :=
  ∃ a : Fin Tag.D4.rank → Kˣ, X = exactNormalAut Tag.D4 K a σ 0

theorem HasField.mul {X Y : MulAut (adjointGroup Tag.D4 K)} {σ τ : K ≃+* K} (hX : HasField X σ)
    (hY : HasField Y τ) : HasField (X * Y) (σ * τ) := by
  obtain ⟨a, rfl⟩ := hX
  obtain ⟨b, rfl⟩ := hY
  exact ⟨_, exactNormalAut_mul a b σ τ 0 0⟩

theorem HasField.unique {X : MulAut (adjointGroup Tag.D4 K)} {σ τ : K ≃+* K} (h : HasField X σ)
    (h' : HasField X τ) : σ = τ := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact (normal_inj (ha.symm.trans hb)).2

theorem hasField_diag (d : Fin Tag.D4.rank → Kˣ) : HasField (diagAut d) (1 : K ≃+* K) := ⟨d, rfl⟩

theorem HasField.graph_mul {X : MulAut (adjointGroup Tag.D4 K)} {σ : K ≃+* K} (h : HasField X σ)
    (ε : ℕ) : ∃ X', HasField X' σ ∧ d4Graph K ε * X = X' * d4Graph K ε := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, ⟨_, rfl⟩, graph_mul_normal ε a σ⟩

theorem normal_relation {g c c' : adjointGroup Tag.D4 K} {βt β β' : MulAut (adjointGroup Tag.D4 K)}
    (hβt : βt ∈ unipotentPairAut Tag.D4 K) (hβ : β ∈ unipotentPairAut Tag.D4 K)
    (hβ' : β' ∈ unipotentPairAut Tag.D4 K)
    (h : (MulAut.conj g * βt) * (MulAut.conj c * β) =
      (MulAut.conj c' * β') * (MulAut.conj g * βt)) :
    ∃ d : Fin Tag.D4.rank → Kˣ, βt * β = diagAut d * (β' * βt) := by
  have e1 : (MulAut.conj g * βt) * (MulAut.conj c * β) = MulAut.conj (g * βt c) * (βt * β) := by
    calc (MulAut.conj g * βt) * (MulAut.conj c * β)
        = MulAut.conj g * (βt * MulAut.conj c) * β := by group
      _ = MulAut.conj g * (MulAut.conj (βt c) * βt) * β := by rw [mul_conj_eq]
      _ = MulAut.conj (g * βt c) * (βt * β) := by rw [map_mul]; group
  have e2 : (MulAut.conj c' * β') * (MulAut.conj g * βt) =
      MulAut.conj (c' * β' g) * (β' * βt) := by
    calc (MulAut.conj c' * β') * (MulAut.conj g * βt)
        = MulAut.conj c' * (β' * MulAut.conj g) * βt := by group
      _ = MulAut.conj c' * (MulAut.conj (β' g) * β') * βt := by rw [mul_conj_eq]
      _ = MulAut.conj (c' * β' g) * (β' * βt) := by rw [map_mul]; group
  obtain ⟨y, hy⟩ : ∃ y : adjointGroup Tag.D4 K, y = (g * βt c)⁻¹ * (c' * β' g) := ⟨_, rfl⟩
  have hyy : βt * β = MulAut.conj y * (β' * βt) := by
    have h' := h
    rw [e1, e2] at h'
    rw [hy, map_mul, map_inv]
    calc βt * β = (MulAut.conj (g * βt c))⁻¹ * (MulAut.conj (g * βt c) * (βt * β)) := by group
      _ = (MulAut.conj (g * βt c))⁻¹ * (MulAut.conj (c' * β' g) * (β' * βt)) := by rw [h']
      _ = _ := (mul_assoc _ _ _).symm
  have hyA : MulAut.conj y ∈ unipotentPairAut Tag.D4 K := by
    have : MulAut.conj y = (βt * β) * (β' * βt)⁻¹ := by rw [hyy]; group
    rw [this]
    exact mul_mem (mul_mem hβt hβ) (inv_mem (mul_mem hβ' hβt))
  obtain ⟨d, hd⟩ := exists_conj_eq_exactNormalAut_diag hyA
  exact ⟨d, by rw [hyy]; exact congrArg (· * (β' * βt)) hd⟩

theorem normal_of_perm_one {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ unipotentPairAut Tag.D4 K)
    (hp : simplePermHom Tag.D4 K ⟨β, hβ⟩ = 1) :
    ∃ (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K), β = exactNormalAut Tag.D4 K a σ 0 := by
  have hmap : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have := simplePerm_spec ⟨β, hβ⟩ i
    have e : simplePerm Tag.D4 K ⟨β, hβ⟩ = 1 := hp
    rw [e] at this
    simpa using this
  obtain ⟨a, σ, h⟩ := exists_normalAut_mul_graph hmap
  rw [d3z_d4Graph_zero, mul_one] at h
  exact ⟨a, σ, h⟩

theorem a4_inndiag {ε : ℕ} (hε : ε = 1 ∨ ε = 2) {g : adjointGroup Tag.D4 K}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {t₁ t₂ : MulAut (adjointGroup Tag.D4 K)}
    (h₁ : t₁ * t₁ = 1)
    (hb₁ : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) * t₁ =
      t₂ * (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)))
    (hb₂ : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) * t₂ =
      (t₁ * t₂) * (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) :
    ∃ (c₁ c₂ : adjointGroup Tag.D4 K) (a₁ a₂ : Fin Tag.D4.rank → Kˣ),
      t₁ = MulAut.conj c₁ * diagAut a₁ ∧ t₂ = MulAut.conj c₂ * diagAut a₂ := by
  classical
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c₁, β₁, hU₁, hV₁, ht₁⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 t₁
  obtain ⟨c₂, β₂, hU₂, hV₂, ht₂⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 t₂
  have hβ₁ : β₁ ∈ unipotentPairAut Tag.D4 K := ⟨hU₁, hV₁⟩
  have hβ₂ : β₂ ∈ unipotentPairAut Tag.D4 K := ⟨hU₂, hV₂⟩
  subst ht₁ ht₂
  obtain ⟨hp₁, hp₂⟩ := a4_perm_trivial hε hβ₁ hβ₂ h₁ hb₁ hb₂
  obtain ⟨a₁, σ₁, hN₁⟩ := normal_of_perm_one hβ₁ hp₁
  obtain ⟨a₂, σ₂, hN₂⟩ := normal_of_perm_one hβ₂ hp₂
  set N : MulAut (adjointGroup Tag.D4 K) := exactNormalAut Tag.D4 K a σ 0 with hNdef
  set βt : MulAut (adjointGroup Tag.D4 K) := N * d4Graph K ε with hβt
  have hβtA : βt ∈ unipotentPairAut Tag.D4 K := mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  have hNf : HasField N σ := ⟨a, rfl⟩
  have hN₁f : HasField β₁ σ₁ := ⟨a₁, hN₁⟩
  have hN₂f : HasField β₂ σ₂ := ⟨a₂, hN₂⟩
  obtain ⟨d, hd⟩ := normal_relation hβtA hβ₁ hβ₂ hb₁
  have e3 : (MulAut.conj c₁ * β₁) * (MulAut.conj c₂ * β₂) =
      MulAut.conj (c₁ * β₁ c₂) * (β₁ * β₂) := by
    calc (MulAut.conj c₁ * β₁) * (MulAut.conj c₂ * β₂)
        = MulAut.conj c₁ * (β₁ * MulAut.conj c₂) * β₂ := by group
      _ = MulAut.conj c₁ * (MulAut.conj (β₁ c₂) * β₁) * β₂ := by rw [mul_conj_eq]
      _ = MulAut.conj (c₁ * β₁ c₂) * (β₁ * β₂) := by rw [map_mul]; group
  have hβ₁₂ : β₁ * β₂ ∈ unipotentPairAut Tag.D4 K := mul_mem hβ₁ hβ₂
  obtain ⟨d', hd'⟩ := normal_relation hβtA hβ₂ hβ₁₂ (by rw [← e3]; exact hb₂)
  have key1 : σ * σ₁ = σ₂ * σ := by
    obtain ⟨X', hX'f, hX'⟩ := hN₁f.graph_mul ε
    have hl : βt * β₁ = (N * X') * d4Graph K ε := by
      rw [hβt, mul_assoc, hX', ← mul_assoc]
    have hr : diagAut d * (β₂ * βt) = ((diagAut d * β₂) * N) * d4Graph K ε := by
      rw [hβt]; simp only [mul_assoc]
    have hcancel : N * X' = (diagAut d * β₂) * N := mul_right_cancel (hl.symm.trans (hd.trans hr))
    have h1 : HasField (N * X') (σ * σ₁) := hNf.mul hX'f
    have h2 : HasField ((diagAut d * β₂) * N) ((1 * σ₂) * σ) :=
      ((hasField_diag d).mul hN₂f).mul hNf
    rw [hcancel] at h1
    simpa using h1.unique h2
  have key2 : σ * σ₂ = σ₁ * σ₂ * σ := by
    obtain ⟨X', hX'f, hX'⟩ := hN₂f.graph_mul ε
    have hl : βt * β₂ = (N * X') * d4Graph K ε := by
      rw [hβt, mul_assoc, hX', ← mul_assoc]
    have hr : diagAut d' * ((β₁ * β₂) * βt) = (((diagAut d' * β₁) * β₂) * N) * d4Graph K ε := by
      rw [hβt]; simp only [mul_assoc]
    have hcancel : N * X' = ((diagAut d' * β₁) * β₂) * N :=
      mul_right_cancel (hl.symm.trans (hd'.trans hr))
    have h1 : HasField (N * X') (σ * σ₂) := hNf.mul hX'f
    have h2 : HasField (((diagAut d' * β₁) * β₂) * N) (((1 * σ₁) * σ₂) * σ) :=
      (((hasField_diag d').mul hN₁f).mul hN₂f).mul hNf
    rw [hcancel] at h1
    simpa using h1.unique h2
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcomm : ∀ ρ τ : K ≃+* K, ρ * τ = τ * ρ := fun ρ τ =>
    (IsCyclic.commGroup (α := RingAut K)).mul_comm ρ τ
  have hσ₂₁ : σ₂ = σ₁ := by
    have h : σ₂ * σ = σ₁ * σ := by rw [← key1, hcomm σ σ₁]
    exact mul_right_cancel h
  have hσ₁ : σ₁ = 1 := by
    have h : σ₂ * σ = σ₁ * σ₂ * σ := by rw [← hcomm σ σ₂, key2]
    have h' : σ₂ = σ₁ * σ₂ := mul_right_cancel h
    have h'' : 1 * σ₂ = σ₁ * σ₂ := by rw [one_mul]; exact h'
    exact (mul_right_cancel h'').symm
  have hσ₂ : σ₂ = 1 := hσ₂₁.trans hσ₁
  refine ⟨c₁, c₂, a₁, a₂, ?_, ?_⟩
  · rw [hN₁, hσ₁]; rfl
  · rw [hN₂, hσ₂]; rfl

end Field

end CFSG.LocalAnalysis.GLTheoremA
