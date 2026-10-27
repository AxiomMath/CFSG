module

public import CFSG.GF2Type.Smith1979.IdxFourIdentSix
public import CFSG.GF2Type.Smith1979.IdxFourIdentFrame
public import CFSG.GF2Type.Smith1979.IdxFourIdentMon

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.Case25.U43Weights

instance : Finite G12 := Finite.of_injective (fun e : G12 => (e : V12 → V12))
  fun _ _ h => LinearEquiv.ext (congrFun h)

namespace FrameData

theorem exists_beta {A : Type} [CommGroup A] [Finite A] {ρ : A →* G12}
    (hρ : Function.Injective ρ) {ψ : A →* A4} (b : Gen → G12)
    (hbn : ∀ (k : Gen) (a : A), ∃ a' : A, b k * ρ a * (b k)⁻¹ = ρ a' ∧ ψ a' = sg k (ψ a)) :
    ∃ β : Gen → (A ≃* A), (∀ k a, b k * ρ a * (b k)⁻¹ = ρ (β k a)) ∧
      ∀ k a, ψ (β k a) = sg k (ψ a) := by
  choose f hf1 hf2 using hbn
  have hmul : ∀ k (a a' : A), f k (a * a') = f k a * f k a' := fun k a a' => by
    apply hρ
    rw [← hf1, map_mul, map_mul, ← hf1, ← hf1]
    group
  let g : Gen → (A →* A) := fun k => MonoidHom.mk' (f k) (hmul k)
  have hinj : ∀ k, Function.Injective (f k) := fun k a a' h => by
    apply hρ
    have := hf1 k a
    rw [h, ← hf1 k a'] at this
    have h' := mul_right_cancel (mul_left_cancel this)
    exact h'
  refine ⟨fun k => MulEquiv.ofBijective (g k) ((Finite.injective_iff_bijective).1 (hinj k)),
    fun k a => hf1 k a, fun k a => hf2 k a⟩

theorem eps_zero_of_commute {c : Fin 6 → ZMod 3} {π : Equiv.Perm (Fin 6)} {ε : ZMod 2}
    (h : (diagE c * permE π * frobE ^ ε.val) * theta0e =
      theta0e * (diagE c * permE π * frobE ^ ε.val)) : ε = 0 := by
  rcases MonAux.zmod2_cases ε with rfl | rfl
  · rfl
  · exfalso
    rw [MonAux.frobPow_one] at h
    have hm : (diagE c * permE π) * theta0e = theta0e * (diagE c * permE π) := by
      calc diagE c * permE π * theta0e = diagE c * (permE π * theta0e) := mul_assoc _ _ _
        _ = diagE c * (theta0e * permE π) := by rw [permE_mul_theta0e]
        _ = (diagE c * theta0e) * permE π := (mul_assoc _ _ _).symm
        _ = (theta0e * diagE c) * permE π := by rw [diagE_mul_theta0e]
        _ = theta0e * (diagE c * permE π) := mul_assoc _ _ _
    apply MonAux.frobE_not_comm
    have h2 : (diagE c * permE π) * (frobE * theta0e) =
        (diagE c * permE π) * (theta0e * frobE) := by
      calc (diagE c * permE π) * (frobE * theta0e) = diagE c * permE π * frobE * theta0e := by
            simp only [mul_assoc]
        _ = theta0e * (diagE c * permE π * frobE) := h
        _ = theta0e * (diagE c * permE π) * frobE := by simp only [mul_assoc]
        _ = (diagE c * permE π) * theta0e * frobE := by rw [hm]
        _ = (diagE c * permE π) * (theta0e * frobE) := by simp only [mul_assoc]
    exact mul_left_cancel h2

theorem exists_perm {A : Type} [Group A] (H : Fin 6 → Subgroup A) (hHinj : Function.Injective H)
    (β : A ≃* A) (h : ∀ i, ∃ j, (H i).map β.toMonoidHom = H j) :
    ∃ p : Equiv.Perm (Fin 6), ∀ i, (H i).map β.toMonoidHom = H (p i) := by
  choose f hf using h
  have hinj : Function.Injective f := fun i i' hii' => by
    apply hHinj
    have h1 : (H i).map β.toMonoidHom = (H i').map β.toMonoidHom := by rw [hf, hf, hii']
    exact Subgroup.map_injective β.injective h1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => hf i⟩

theorem conj_plane {A : Type} [CommGroup A] [Finite A] (hA3 : ∀ a : A, a ^ 3 = 1) {ρ : A →* G12}
    (g : G12) (H : Fin 6 → Subgroup A)
    (hplane : ∀ i x, x ∈ plane i ↔ g x ∈ LemmaW.weightSpace (rep ρ) (H i))
    (b : G12) (β : A ≃* A) (hb : ∀ a, b * ρ a * b⁻¹ = ρ (β a)) (p : Equiv.Perm (Fin 6))
    (hp : ∀ i, (H i).map β.toMonoidHom = H (p i)) :
    ∀ i, ∀ x ∈ plane i, (g⁻¹ * b * g) x ∈ plane (p i) := by
  intro i x hx
  have hb' : ∀ a v, rep ρ (β a) (b v) = b (rep ρ a v) := fun a v => by
    have := congrArg (fun m : G12 => m (b v)) (hb a)
    simpa using this.symm
  have hmap := LemmaW.map_weightSpace (rep ρ) hA3 (b := b) (σ := β) hb' (H i)
  have h1 : g x ∈ LemmaW.weightSpace (rep ρ) (H i) := (hplane i x).1 hx
  have h2 : b (g x) ∈ LemmaW.weightSpace (rep ρ) (H (p i)) := by
    rw [← hp i, ← hmap]
    exact Submodule.mem_map_of_mem (f := (b : V12 →ₗ[ZMod 2] V12)) h1
  rw [hplane (p i) ((g⁻¹ * b * g) x)]
  have h3 : g ((g⁻¹ * b * g) x) = b (g x) := by
    simp [LinearEquiv.mul_apply]
  rw [h3]
  exact h2


theorem theta0e_pow_three : theta0e ^ 3 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show theta0e (theta0e (theta0e x)) = x
  simp only [theta0e_apply]
  exact theta0_theta0_theta0 x

theorem theta0e_pow_plane (n : ℕ) {i : Fin 6} {x : V12} (hx : x ∈ plane i) :
    (theta0e ^ n) x ∈ plane i := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih (theta0_mem_plane hx)

theorem theta0e_zpow_plane (m : ℤ) {i : Fin 6} {x : V12} (hx : x ∈ plane i) :
    (theta0e ^ m) x ∈ plane i := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, m % 3 = r :=
    ⟨(m % 3).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm⟩
  have h1 : m = 3 * (m / 3) + (r : ℤ) := by
    have := Int.mul_ediv_add_emod m 3
    omega
  have h2 : theta0e ^ m = theta0e ^ r := by
    rw [h1, zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
      theta0e_pow_three, one_zpow, one_mul, zpow_natCast]
  rw [h2]
  exact theta0e_pow_plane _ hx

theorem pow_plane {m : G12} {p : Equiv.Perm (Fin 6)}
    (hm : ∀ i, ∀ x ∈ plane i, m x ∈ plane (p i)) (n : ℕ) :
    ∀ i, ∀ x ∈ plane i, (m ^ n) x ∈ plane ((p ^ n) i) := by
  induction n with
  | zero => intro i x hx; simpa using hx
  | succ n ih =>
    intro i x hx
    rw [pow_succ m n, LinearEquiv.mul_apply, pow_succ p n, Equiv.Perm.mul_apply]
    exact ih _ _ (hm i x hx)

end FrameData

theorem frame_data
    {A : Type} [CommGroup A] [Finite A] (hA3 : ∀ a : A, a ^ 3 = 1) (hcard : Nat.card A = 243)
    {ρ : A →* G12} (hρ : Function.Injective ρ) (hρg : ∀ a, ρ a ∈ gammaU) {θ : A}
    (hθ : ρ θ = theta0e)
    (ψ : A →* A4) (hψs : Function.Surjective ψ) (hψk : ∀ a, ψ a = 1 ↔ a ∈ Subgroup.zpowers θ)
    (b : Gen → G12) (hbg : ∀ k, b k ∈ gammaU) (hbu : ∀ k, b k * theta0e = theta0e * b k)
    (hb3 : ∀ k, (b k) ^ 3 ∈ Subgroup.zpowers theta0e)
    (hbn : ∀ (k : Gen) (a : A), ∃ a' : A, b k * ρ a * (b k)⁻¹ = ρ a' ∧ ψ a' = sg k (ψ a)) :
    ∃ (g : G12) (c : Gen → Fin 6 → ZMod 3) (p : Gen → Equiv.Perm (Fin 6)) (ψ' : D5 →* A4),
      g ∈ gammaU ∧ g * theta0e = theta0e * g ∧
      (∀ a, g⁻¹ * ρ a * g ∈ D5) ∧ (∀ d ∈ D5, ∃ a, g⁻¹ * ρ a * g = d) ∧
      (∀ k, g⁻¹ * b k * g = diagE (c k) * permE (p k)) ∧ (∀ k, p k ^ 3 = 1) ∧
      (∀ (a : A) (h : g⁻¹ * ρ a * g ∈ D5), ψ' ⟨g⁻¹ * ρ a * g, h⟩ = ψ a) ∧
      Function.Surjective ψ' ∧
      (∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e) ∧
      (∀ (k : Gen) (d : D5) (h : permE (p k) * (d : G12) * (permE (p k))⁻¹ ∈ D5),
        ψ' ⟨permE (p k) * (d : G12) * (permE (p k))⁻¹, h⟩ = sg k (ψ' d)) := by
  obtain ⟨β, hβb, hβψ⟩ := FrameData.exists_beta hρ b hbn
  obtain ⟨H, hH3, hθH, hHinj, hHdim, hHtop, hHall, hHinv⟩ :=
    six_weights hA3 hcard hρ hρg hθ ψ hψs hψk β b hβb hβψ
  obtain ⟨g, c, hgg, hgu, hgplane, hgconj, hgH⟩ :=
    exists_frame hA3 hρg hθ H hH3 hθH hHinj hHdim hHtop
  have hperm : ∀ k, ∃ p : Equiv.Perm (Fin 6), ∀ i, (H i).map (β k).toMonoidHom = H (p i) :=
    fun k => FrameData.exists_perm H hHinj (β k) (hHinv k)
  choose p hp using hperm
  have hplane' : ∀ k i, ∀ x ∈ plane i, (g⁻¹ * b k * g) x ∈ plane (p k i) :=
    fun k => FrameData.conj_plane hA3 g H hgplane (b k) (β k) (hβb k) (p k) (hp k)
  have hb'g : ∀ k, g⁻¹ * b k * g ∈ gammaU := fun k =>
    mul_mem (mul_mem (inv_mem hgg) (hbg k)) hgg
  have hcomm_g : Commute g theta0e := hgu
  have hb'comm : ∀ k, (g⁻¹ * b k * g) * theta0e = theta0e * (g⁻¹ * b k * g) := fun k =>
    (((hcomm_g.inv_left).mul_left (hbu k)).mul_left hcomm_g)
  have hdec : ∀ k, ∃ c' : Fin 6 → ZMod 3, g⁻¹ * b k * g = diagE c' * permE (p k) := by
    intro k
    obtain ⟨c', ε, h⟩ := exists_diag_perm_of_planes (hb'g k) (hplane' k)
    have hc := hb'comm k
    rw [h] at hc
    have hε := FrameData.eps_zero_of_commute hc
    refine ⟨c', ?_⟩
    rw [h, hε]
    simp
  choose c' hc' using hdec
  have hp3 : ∀ k, p k ^ 3 = 1 := by
    intro k
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hb3 k)
    have hconj3 : (g⁻¹ * b k * g) ^ 3 = g⁻¹ * (b k) ^ 3 * g := by
      have := conj_pow (a := g⁻¹) (b := b k) (i := 3)
      simpa using this
    have hz : (g⁻¹ * b k * g) ^ 3 = theta0e ^ m := by
      rw [hconj3, ← hm]
      have hcg : Commute g (theta0e ^ m) := hcomm_g.zpow_right m
      have := hcg.inv_left
      rw [this.eq, mul_assoc, inv_mul_cancel, mul_one]
    refine Equiv.ext fun i => ?_
    have hmem1 := FrameData.pow_plane (hplane' k) 3 i (MonAux.pairVec i (1, 0))
      (MonAux.pairVec_mem_plane i _)
    have hmem2 : ((g⁻¹ * b k * g) ^ 3) (MonAux.pairVec i (1, 0)) ∈ plane i := by
      rw [hz]
      exact FrameData.theta0e_zpow_plane m (MonAux.pairVec_mem_plane i _)
    have hne : ((g⁻¹ * b k * g) ^ 3) (MonAux.pairVec i (1, 0)) ≠ 0 := by
      intro h0
      exact MonAux.pairVec_ne_zero i (p := (1, 0)) (by decide)
        ((LinearEquiv.map_eq_zero_iff _).1 h0)
    exact MonAux.eq_of_mem_plane_of_mem_plane hmem1 hmem2 hne
  have hconjβ : ∀ k a, (c (β k a)).toAdd = fun i => (c a).toAdd ((p k).symm i) := by
    intro k a
    apply diagE_injective
    rw [← hgconj (β k a), ← hβb k a]
    have : g⁻¹ * (b k * ρ a * (b k)⁻¹) * g =
        (g⁻¹ * b k * g) * (g⁻¹ * ρ a * g) * (g⁻¹ * b k * g)⁻¹ := by group
    rw [this, hgconj a, hc' k, MonAux.conj_mon_zero]
  let Sm : Multiplicative (Fin 6 → ZMod 3) →* Multiplicative (ZMod 3) :=
    MonoidHom.mk' (fun v => Multiplicative.ofAdd (∑ i, v.toAdd i)) (fun v w => by
      simp [Finset.sum_add_distrib])
  let f : A →* Multiplicative (ZMod 3) := Sm.comp c
  have hf_apply : ∀ a, f a = Multiplicative.ofAdd (∑ i, (c a).toAdd i) := fun a => rfl
  have hf_inv : ∀ k a, f (β k a) = f a := by
    intro k a
    rw [hf_apply, hf_apply, hconjβ k a]
    congr 1
    exact Equiv.sum_comp (p k).symm (fun i => (c a).toAdd i)
  have hf_theta : f θ = 1 := by
    have h1 : g⁻¹ * ρ θ * g = diagE (fun _ => 1) := by
      rw [hθ, diagE_const_one, (hcomm_g.inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
    have h2 := hgconj θ
    rw [h1] at h2
    have h3 := diagE_injective h2
    rw [hf_apply, ← h3]
    simp
    decide
  have hker_le : ψ.ker ≤ f.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ((hψk a).1 ha)
    rw [map_zpow, hf_theta, one_zpow]
  have hfbar_apply : ∀ a, (MonoidHom.liftOfSurjective ψ hψs ⟨f, hker_le⟩) (ψ a) = f a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨f, hker_le⟩ a
  have hfbar_inv : ∀ (k : Gen) (x : A4),
      (MonoidHom.liftOfSurjective ψ hψs ⟨f, hker_le⟩) (sg k x) =
        (MonoidHom.liftOfSurjective ψ hψs ⟨f, hker_le⟩) x := by
    intro k x
    obtain ⟨a, rfl⟩ := hψs x
    rw [← hβψ k a, hfbar_apply, hfbar_apply, hf_inv]
  have hfbar1 := eq_one_of_invariant (MonoidHom.liftOfSurjective ψ hψs ⟨f, hker_le⟩) hfbar_inv
  have hsum0 : ∀ a, ∑ i, (c a).toAdd i = 0 := by
    intro a
    have h1 : f a = 1 := by
      rw [← hfbar_apply, hfbar1]
      rfl
    rw [hf_apply] at h1
    exact Multiplicative.ofAdd.injective h1
  have hD5 : ∀ a, g⁻¹ * ρ a * g ∈ D5 := fun a => ⟨(c a).toAdd, hsum0 a, hgconj a⟩
  let Φ : A →* D5 :=
    { toFun := fun a => ⟨g⁻¹ * ρ a * g, hD5 a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a a' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }
  have hΦ_coe : ∀ a, ((Φ a : D5) : G12) = g⁻¹ * ρ a * g := fun a => rfl
  have hΦinj : Function.Injective Φ := by
    intro a a' h
    have h1 := congrArg Subtype.val h
    simp only [hΦ_coe] at h1
    exact hρ (mul_left_cancel (mul_right_cancel h1))
  have hΦbij : Function.Bijective Φ :=
    Function.Injective.bijective_of_nat_card_le hΦinj (by rw [card_D5, hcard]; norm_num)
  let Φe : A ≃* D5 := MulEquiv.ofBijective Φ hΦbij
  have hΦe_apply : ∀ a, Φe a = Φ a := fun a => rfl
  let ψ' : D5 →* A4 := ψ.comp Φe.symm.toMonoidHom
  have hψ'Φ : ∀ a, ψ' (Φ a) = ψ a := fun a => by
    show ψ (Φe.symm (Φ a)) = ψ a
    rw [← hΦe_apply, MulEquiv.symm_apply_apply]
  have hconj_theta : ∀ n : ℤ, g⁻¹ * theta0e ^ n * g = theta0e ^ n := fun n => by
    rw [((hcomm_g.zpow_right n).inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
  have hΦθ : ∀ n : ℤ, ((Φ (θ ^ n) : D5) : G12) = theta0e ^ n := fun n => by
    rw [hΦ_coe, map_zpow, hθ, hconj_theta]
  refine ⟨g, c', p, ψ', hgg, hgu, hD5, ?_, hc', hp3, ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨a, ha⟩ := hΦbij.2 ⟨d, hd⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · intro a h
    exact hψ'Φ a
  · intro x
    obtain ⟨a, rfl⟩ := hψs x
    exact ⟨Φ a, hψ'Φ a⟩
  · intro d
    obtain ⟨a, rfl⟩ := hΦbij.2 d
    rw [hψ'Φ, hψk]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hΦθ n, hn]⟩
    · intro hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      refine Subgroup.mem_zpowers_iff.2 ⟨n, hΦinj (Subtype.ext ?_)⟩
      rw [hΦθ n, hn]
  · intro k d h
    obtain ⟨a, rfl⟩ := hΦbij.2 d
    have hcalc : permE (p k) * ((Φ a : D5) : G12) * (permE (p k))⁻¹ =
        ((Φ (β k a) : D5) : G12) := by
      rw [hΦ_coe a, hΦ_coe (β k a), hgconj a, hgconj (β k a), permE_mul_diagE_mul_inv,
        hconjβ k a]
    have h2 : (⟨permE (p k) * ((Φ a : D5) : G12) * (permE (p k))⁻¹, h⟩ : D5) = Φ (β k a) :=
      Subtype.ext hcalc
    rw [h2, hψ'Φ, hψ'Φ, hβψ]

end CFSG.GF2Type.Smith1979.IdxFour
