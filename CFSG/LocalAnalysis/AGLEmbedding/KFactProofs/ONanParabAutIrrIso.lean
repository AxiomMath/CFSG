module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTower

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

section Iso

variable {X X' : Type*} [Group X] [Group X']

theorem congr_conj (e : X ≃* X') (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_inn_congr (e : X ≃* X') :
    (inn X).map (MulAut.congr e).toMonoidHom = inn X' := by
  ext β
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (congr_conj e x).symm⟩
  · rintro ⟨x', rfl⟩
    refine ⟨MulAut.conj (e.symm x'), ⟨e.symm x', rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm x')) = MulAut.conj x'
    rw [congr_conj, MulEquiv.apply_symm_apply]

theorem OutPTwoGen.of_mulEquiv {p : ℕ} (e : X ≃* X') (h : OutPTwoGen X p) : OutPTwoGen X' p := by
  intro P' hP'
  set Φ : MulAut X ≃* MulAut X' := MulAut.congr e with hΦ
  set P : Subgroup (MulAut X) := P'.comap Φ.toMonoidHom with hP
  have hPp : IsPGroup p P := hP'.comap_of_injective Φ.toMonoidHom Φ.injective
  obtain ⟨a, ha, b, hb, hle⟩ := h P hPp
  refine ⟨Φ a, ha, Φ b, hb, ?_⟩
  have hmap : P.map Φ.toMonoidHom = P' := Subgroup.map_comap_eq_self_of_surjective Φ.surjective P'
  rw [← hmap]
  refine (Subgroup.map_mono hle).trans ?_
  rw [Subgroup.map_sup, MonoidHom.map_closure, hΦ, map_inn_congr]
  refine sup_le_sup_right (le_of_eq ?_) _
  congr 1
  simp

theorem OutPInner.of_mulEquiv {p : ℕ} (e : X ≃* X') (h : OutPInner X p) : OutPInner X' p := by
  intro P' hP'
  set Φ : MulAut X ≃* MulAut X' := MulAut.congr e with hΦ
  set P : Subgroup (MulAut X) := P'.comap Φ.toMonoidHom with hP
  have hPp : IsPGroup p P := hP'.comap_of_injective Φ.toMonoidHom Φ.injective
  have hmap : P.map Φ.toMonoidHom = P' := Subgroup.map_comap_eq_self_of_surjective Φ.surjective P'
  rw [← hmap, ← map_inn_congr e]
  exact Subgroup.map_mono (h P hPp)

end Iso

section Sylow

open scoped Pointwise

variable {Y : Type*} [Group Y]

theorem map_aut_eq_of_iff {J : Subgroup Y} {α : MulAut Y} (h : ∀ z, z ∈ J ↔ α z ∈ J) :
    J.map α.toMonoidHom = J := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h z).1 hz
  · intro hw
    exact ⟨α.symm w, (h _).2 (by simpa using hw), by simp⟩

theorem forall_iff_of_map_eq {J : Subgroup Y} {α : MulAut Y} (h : J.map α.toMonoidHom = J) :
    ∀ z, z ∈ J ↔ α z ∈ J := by
  intro z
  constructor
  · intro hz
    rw [← h]
    exact ⟨z, hz, rfl⟩
  · intro hz
    rw [← h] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    have : y = z := α.injective hyz
    rwa [this] at hy

theorem aut_mul_conj_mul_inv (α : MulAut Y) (z : Y) :
    α * MulAut.conj z * α⁻¹ = MulAut.conj (α z) := by
  ext w
  simp [MulAut.conj_apply]

theorem exists_conj_mem_iff [Finite Y] (S₁ S₀ : Sylow 2 Y) :
    ∃ g : Y, ∀ x, x ∈ (S₀ : Subgroup Y) ↔ g⁻¹ * x * g ∈ (S₁ : Subgroup Y) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₁ S₀
  refine ⟨g, fun x => ?_⟩
  rw [← hg]
  change x ∈ (MulAut.conj g • (S₁ : Subgroup Y)) ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

theorem AutScalarTorus.of_sylow [Finite Y] (S₁ : Sylow 2 Y)
    (h : ∀ α : MulAut Y, (S₁ : Subgroup Y).map α.toMonoidHom = S₁ →
      (∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ α ^ e ∈ inn Y) →
        ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y),
          α b * (b ^ k)⁻¹ ∈ (S₁ : Subgroup Y)) : AutScalarTorus Y := by
  intro S₀ α hα ⟨e, he, he6, heinn⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_iff S₁ S₀
  have hαi := forall_iff_of_map_eq hα
  set α' : MulAut Y := (MulAut.conj g)⁻¹ * α * MulAut.conj g with hα'
  have happ : ∀ x, α' x = g⁻¹ * α (g * x * g⁻¹) * g := by
    intro x
    simp [hα', MulAut.conj_apply]
  have hS₁ : (S₁ : Subgroup Y).map α'.toMonoidHom = S₁ := by
    refine map_aut_eq_of_iff fun x => ?_
    have h1 := hg (α (g * x * g⁻¹))
    have h2 := hg (g * x * g⁻¹)
    have h3 := hαi (g * x * g⁻¹)
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e] at h2
    rw [happ]
    exact h2.symm.trans (h3.trans h1)
  have hinn' : α' ^ e ∈ inn Y := by
    have h1 : α' ^ e = (MulAut.conj g)⁻¹ * α ^ e * ((MulAut.conj g)⁻¹)⁻¹ := by
      rw [← conj_pow]
      simp [hα']
    rw [h1]
    exact (inn_normal (Y := Y)).conj_mem _ heinn _
  obtain ⟨k, hk⟩ := h α' hS₁ ⟨e, he, he6, hinn'⟩
  refine ⟨k, fun b hb => ?_⟩
  have hb' : g⁻¹ * b * g ∈ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff] at hb ⊢
    intro y
    have h1 := hg (g * y * g⁻¹)
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e] at h1
    have h2 := hg (b * (g * y * g⁻¹) * b⁻¹)
    have e2 : g⁻¹ * (b * (g * y * g⁻¹) * b⁻¹) * g = g⁻¹ * b * g * y * (g⁻¹ * b * g)⁻¹ := by group
    rw [e2] at h2
    exact h1.symm.trans ((hb _).trans h2)
  have hkb := hk _ hb'
  refine (hg _).2 ?_
  have e3 : α' (g⁻¹ * b * g) * ((g⁻¹ * b * g) ^ k)⁻¹ = g⁻¹ * (α b * (b ^ k)⁻¹) * g := by
    rw [happ]
    have e4 : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    have e5 : (g⁻¹ * b * g) ^ k = g⁻¹ * b ^ k * g := by
      have := conj_pow (a := g⁻¹) (b := b) (i := k)
      simpa using this
    rw [e4, e5]
    group
  rw [← e3]
  exact hkb

end Sylow

section Iso2

variable {X X' : Type*} [Group X] [Group X']

theorem AutScalarTorus.of_mulEquiv [Finite X] (e : X ≃* X') (h : AutScalarTorus X) :
    AutScalarTorus X' := by
  intro S₀' α' hα' ⟨m, hm, hm6, hinn⟩
  set S₀ : Sylow 2 X := S₀'.comapOfInjective e.toMonoidHom e.injective (by simp) with hS₀def
  have hS₀ : ∀ x, x ∈ (S₀ : Subgroup X) ↔ e x ∈ (S₀' : Subgroup X') := fun x => Iff.rfl
  set Φ : MulAut X' ≃* MulAut X := MulAut.congr e.symm with hΦ
  set α : MulAut X := Φ α' with hα
  have hαx : ∀ x, e (α x) = α' (e x) := by
    intro x
    simp [hα, hΦ, MulAut.congr_apply]
  have hα'i := forall_iff_of_map_eq hα'
  have hαS : (S₀ : Subgroup X).map α.toMonoidHom = S₀ := by
    refine map_aut_eq_of_iff fun x => ?_
    rw [hS₀, hS₀, hαx]
    exact hα'i _
  have hαinn : ∃ m : ℕ, 0 < m ∧ Nat.Coprime m 6 ∧ α ^ m ∈ inn X := by
    refine ⟨m, hm, hm6, ?_⟩
    have h1 : α ^ m = Φ (α' ^ m) := by rw [hα, map_pow]
    rw [h1, ← map_inn_congr e.symm]
    exact ⟨α' ^ m, hinn, rfl⟩
  obtain ⟨k, hk⟩ := h S₀ α hαS hαinn
  refine ⟨k, fun b' hb' => ?_⟩
  set b : X := e.symm b' with hb
  have hbn : b ∈ Subgroup.normalizer ((S₀ : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at hb' ⊢
    intro x
    rw [hS₀, hS₀]
    have := hb' (e x)
    simpa [hb] using this
  have h1 := hk b hbn
  rw [hS₀] at h1
  simpa [hαx, hb] using h1

end Iso2

end CFSG.AGLEmbedding.ParabAutIrr
