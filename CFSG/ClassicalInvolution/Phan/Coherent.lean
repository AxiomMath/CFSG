module

public import CFSG.ClassicalInvolution.Phan.StandardPair
public import CFSG.ClassicalInvolution.Phan.TorusAgree
public import CFSG.ClassicalInvolution.Phan.AutSU3

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Iso

theorem exists_mulEquiv_comp_eq {G H X : Type*} [Group G] [Group H] [Group X] {a₁ : G →* X}
    {a₂ : H →* X} (h₁ : Function.Injective a₁) (h₂ : Function.Injective a₂)
    (hr : a₁.range = a₂.range) : ∃ α : G ≃* H, ∀ g, a₂ (α g) = a₁ g := by
  refine ⟨(MonoidHom.ofInjective h₁).trans
    ((MulEquiv.subgroupCongr hr).trans (MonoidHom.ofInjective h₂).symm), fun g => ?_⟩
  simp [MonoidHom.apply_ofInjective_symm, MonoidHom.ofInjective_apply]

theorem map_eq_of_le_of_finite {G : Type*} [Group G] (β : G ≃* G) {H : Subgroup G} [Finite H]
    (h : H.map β.toMonoidHom ≤ H) : H.map β.toMonoidHom = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective β.injective])

end Iso

section Glue

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

variable (K p f) in
@[expose] def AutExtends : Prop :=
  ∀ α : MulAut (Su K p f 2), (diagTorus2 K p f).map α.toMonoidHom = diagTorus2 K p f →
    ∃ β : MulAut (Su K p f 3),
      (∀ A, β (embSUid (unitaryInvolution K p f) 2 A) =
        embSUid (unitaryInvolution K p f) 2 (α A)) ∧
      (B23 K p f).map β.toMonoidHom ≤ B23 K p f

theorem exists_glue (hK : Nat.card K = (p ^ f) ^ 2) (hext : AutExtends K p f)
    {θ₁ θ₂ : Su K p f 3 →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (Su K p f 3)) (h₂ : θ₂.ker ≤ Subgroup.center (Su K p f 3))
    (hM : (B23 K p f).map θ₁ = (B12 K p f).map θ₂)
    (hcomm : ∀ x ∈ (B12 K p f).map θ₁, ∀ y ∈ (B23 K p f).map θ₂, x * y = y * x) :
    ∃ θ : Su K p f 3 →* X, θ.ker ≤ Subgroup.center (Su K p f 3) ∧ θ.range = θ₂.range ∧
      (B12 K p f).map θ = (B12 K p f).map θ₂ ∧ (B23 K p f).map θ = (B23 K p f).map θ₂ ∧
      θ.comp (embSUid (unitaryInvolution K p f) 2) =
        θ₁.comp (embSUid (unitaryInvolution K p f) 0) := by
  have ha₁ : Function.Injective (θ₁.comp (embSUid (unitaryInvolution K p f) 0)) :=
    comp_embSUid_injective hK h₁ 0
  have ha₂ : Function.Injective (θ₂.comp (embSUid (unitaryInvolution K p f) 2)) :=
    comp_embSUid_injective hK h₂ 2
  have hr : (θ₁.comp (embSUid (unitaryInvolution K p f) 0)).range =
      (θ₂.comp (embSUid (unitaryInvolution K p f) 2)).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp]
    exact hM
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq ha₁ ha₂ hr
  have htor : (diagTorus2 K p f).map α.toMonoidHom = diagTorus2 K p f := by
    have hτ := torus_agree hK h₁ h₂ hM hcomm
    rw [map_D23, map_D12] at hτ
    have e : θ₁.comp (embSUid (unitaryInvolution K p f) 0) =
        (θ₂.comp (embSUid (unitaryInvolution K p f) 2)).comp α.toMonoidHom :=
      MonoidHom.ext fun A => (hα A).symm
    rw [e, ← Subgroup.map_map] at hτ
    exact Subgroup.map_injective ha₂ hτ
  obtain ⟨β, hβ2, hβ23⟩ := hext α htor
  have hB12 : (B12 K p f).map β.toMonoidHom = B12 K p f := by
    refine map_eq_of_le_of_finite β ?_
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨α A, (hβ2 A).symm⟩
  have hB23 : (B23 K p f).map β.toMonoidHom = B23 K p f := map_eq_of_le_of_finite β hβ23
  refine ⟨θ₂.comp β.toMonoidHom, ker_comp_mulEquiv_le_center h₂ β, range_comp_mulEquiv _ _, ?_, ?_,
    MonoidHom.ext fun A => ?_⟩
  · rw [map_comp_mulEquiv, hB12]
  · rw [map_comp_mulEquiv, hB23]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ2]
    exact hα A

end Glue

section Chain

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem coherent_chain (hK : Nat.card K = (p ^ f) ^ 2) (hext : AutExtends K p f)
    (u w : ℕ → Subgroup X) (N : ℕ)
    (hpair : ∀ i, i < N → UnitaryBlockStandardPair K p f (w i) (u i) (u (i + 1)))
    (hcomm : ∀ i, i + 1 < N → ∀ x ∈ u i, ∀ y ∈ u (i + 2), x * y = y * x) :
    ∃ θ : ℕ → (Su K p f 3 →* X), ∀ i, i < N →
      (θ i).ker ≤ Subgroup.center (Su K p f 3) ∧ (θ i).range = w i ∧
      (B12 K p f).map (θ i) = u i ∧ (B23 K p f).map (θ i) = u (i + 1) ∧
      (i + 1 < N → (θ (i + 1)).comp (embSUid (unitaryInvolution K p f) 2) =
        (θ i).comp (embSUid (unitaryInvolution K p f) 0)) := by
  induction N with
  | zero => exact ⟨fun _ => 1, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨θ, hθ⟩ := ih (fun i hi => hpair i (by omega)) (fun i hi => hcomm i (by omega))
    obtain ⟨θ₀, hr₀, hk₀, h12₀, h23₀⟩ := pair_normalize (hpair N (by omega))
    rcases N with _ | k
    · refine ⟨fun _ => θ₀, fun i hi => ?_⟩
      obtain rfl : i = 0 := by omega
      exact ⟨hk₀, hr₀, h12₀, h23₀, fun h => absurd h (by omega)⟩
    · obtain ⟨hk, hr, h12, h23, -⟩ := hθ k (by omega)
      obtain ⟨θn, hn1, hn2, hn3, hn4, hn5⟩ := exists_glue hK hext hk hk₀
        (h23.trans h12₀.symm) (by
          rw [h12, h23₀]
          exact hcomm k (by omega))
      refine ⟨Function.update θ (k + 1) θn, fun i hi => ?_⟩
      by_cases hik : i = k + 1
      · subst hik
        simp only [Function.update_self]
        exact ⟨hn1, hn2.trans hr₀, hn3.trans h12₀, hn4.trans h23₀, fun h => absurd h (by omega)⟩
      · have hi' : i < k + 1 := by omega
        obtain ⟨hk', hr', h12', h23', h4'⟩ := hθ i hi'
        simp only [Function.update_of_ne hik]
        refine ⟨hk', hr', h12', h23', fun h => ?_⟩
        by_cases hi'' : i + 1 = k + 1
        · obtain rfl : i = k := by omega
          simp only [Function.update_self]
          exact hn5
        · simp only [Function.update_of_ne hi'']
          exact h4' (by omega)

end Chain

section Family

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem coherent_family_of_autExtends (hK : Nat.card K = (p ^ f) ^ 2) (hext : AutExtends K p f)
    {n : ℕ} (hn : 2 ≤ n) {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}
    (hW : WeakPhanA K p f n U W) :
    ∃ F : PhanFamily K p f X n, (∀ i, (F.ι i).range = U i) ∧ (∀ i, Function.Injective (F.ι i)) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), (F.θ i).range = W i ⟨i + 1, h⟩ ∧
        (F.θ i).ker ≤ Subgroup.center (Su K p f 3) := by
  classical
  let u : ℕ → Subgroup X := fun i => if h : i < n then U ⟨i, h⟩ else ⊥
  let w : ℕ → Subgroup X := fun i => if h : i + 1 < n then W ⟨i, by omega⟩ ⟨i + 1, h⟩ else ⊥
  have hu : ∀ (i : ℕ) (h : i < n), u i = U ⟨i, h⟩ := fun i h => dite_eq_left h
  have hw : ∀ (i : ℕ) (h : i + 1 < n), w i = W ⟨i, by omega⟩ ⟨i + 1, h⟩ :=
    fun i h => dite_eq_left h
  obtain ⟨θ, hθ⟩ := coherent_chain hK hext u w (n - 1)
    (fun i hi => by
      have h1 : i < n := by omega
      have h2 : i + 1 < n := by omega
      rw [hu i h1, hw i h2, hu (i + 1) h2]
      exact hW.pair ⟨i, h1⟩ ⟨i + 1, h2⟩ rfl)
    (fun i hi => by
      have h1 : i < n := by omega
      have h2 : i + 2 < n := by omega
      rw [hu i h1, hu (i + 2) h2]
      exact hW.comm ⟨i, h1⟩ ⟨i + 2, h2⟩ (by show i + 1 < i + 2; omega))
  let ι₀ : Fin n → (Su K p f 2 →* X) := fun i =>
    if (i : ℕ) + 1 < n then (θ i).comp (embSUid (unitaryInvolution K p f) 2)
    else (θ (n - 2)).comp (embSUid (unitaryInvolution K p f) 0)
  have hι : ∀ i : Fin n, (ι₀ i).range = U i ∧ Function.Injective (ι₀ i) := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · obtain ⟨hk, -, h12, h23, -⟩ := hθ i (by omega)
      have := pair_block_inj hK hk h12 h23
      simp only [ι₀, ite_eq_left hi]
      rw [← hu i i.2]
      exact ⟨this.2.1, this.1⟩
    · obtain ⟨hk, -, h12, h23, -⟩ := hθ (n - 2) (by omega)
      have := pair_block_inj hK hk h12 h23
      simp only [ι₀, ite_eq_right hi]
      have hi' : i = ⟨n - 2 + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hi', ← hu (n - 2 + 1) (by omega)]
      exact ⟨this.2.2.2, this.2.2.1⟩
  have hleft : ∀ i : Fin n, (i : ℕ) + 1 < n →
      (θ i).comp (embSUid (unitaryInvolution K p f) 2) = ι₀ i := fun i hi => by
    simp only [ι₀, ite_eq_left hi]
  have hright : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      (θ i).comp (embSUid (unitaryInvolution K p f) 0) = ι₀ ⟨i + 1, h⟩ := by
    intro i hi
    by_cases h2 : (i : ℕ) + 1 + 1 < n
    · obtain ⟨-, -, -, -, h4⟩ := hθ i (by omega)
      simp only [ι₀, ite_eq_left h2]
      exact (h4 (by omega)).symm
    · simp only [ι₀, ite_eq_right h2]
      have : (i : ℕ) = n - 2 := by omega
      rw [this]
  have hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ a b, ι₀ i a * ι₀ j b = ι₀ j b * ι₀ i a := by
    intro i j hij a b
    have ha : ι₀ i a ∈ U i := (hι i).1 ▸ ⟨a, rfl⟩
    have hb : ι₀ j b ∈ U j := (hι j).1 ▸ ⟨b, rfl⟩
    exact hW.comm i j hij _ ha _ hb
  refine ⟨⟨ι₀, fun i => θ i, hleft, hright, hcomm⟩, fun i => (hι i).1, fun i => (hι i).2,
    fun i hi => ?_⟩
  obtain ⟨hk, hr, -, -, -⟩ := hθ i (by omega)
  exact ⟨hr.trans (hw i hi), hk⟩

theorem autExtends (hK : Nat.card K = (p ^ f) ^ 2) : AutExtends K p f := by
  intro α hα
  obtain ⟨β, h2, -, h23⟩ := exists_mulAut_extend hK α hα.le
  exact ⟨β, h2, h23.le⟩

theorem coherent_family (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    ∃ F : PhanFamily K p f X n, (∀ i, (F.ι i).range = U i) ∧ (∀ i, Function.Injective (F.ι i)) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), (F.θ i).range = W i ⟨i + 1, h⟩ ∧
        (F.θ i).ker ≤ Subgroup.center (Su K p f 3) :=
  coherent_family_of_autExtends hK (autExtends hK) hn hW

end Family

end CFSG.ClassicalInvolution.Phan
