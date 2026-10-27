module

public import CFSG.ClassicalInvolution.WeakCT.EdgeSL3
public import CFSG.ClassicalInvolution.WeakCT.A2Intrinsic

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

section Sl3

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {i j : Fin D.rank}

theorem exists_sl3_signed' [Finite F] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) F →* K, ∀ c, ρ (tv 0 1 c) = x (sroot i) c ∧
      ρ (tv 1 0 c) = x (-sroot i) c ∧ ρ (tv 1 2 c) = x (sroot j) c ∧
      ρ (tv 2 1 c) = x (-sroot j) c ∧ ρ (tv 0 2 c) = x (sroot i + sroot j) (epsPos F C i j * c) ∧
      ρ (tv 2 0 c) = x (-(sroot i + sroot j)) (epsNeg F C i j * c) := by
  have hr := pair_mem_roots_zEdge hcij hcji
  have hadd : ∀ z ∈ zEdge, ∀ s t, x (pair i j z) (s + t) = x (pair i j z) s * x (pair i j z) t :=
    fun z hz => (hE.param _ (hr z hz)).2.1
  have hrel := fun z w u (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w = u) (hu : u ∈ zEdge) s t =>
    rel_A2 hdiv hcij hcji hE hij hz hw hzw hu s t
  have hcomm := fun z w (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w ≠ 0)
      (hu : z + w ∉ zEdge) s t => commute_A2 hdiv hcij hcji hE hij hz hw hzw hu s t
  have hA := sign_A hdiv hcij hcji hE hij
  have hB := sign_B hdiv hcij hcji hE hij
  have hC' := sign_C hdiv hcij hcji hE hij
  have hD := sign_D hdiv hcij hcji hE hij
  have hεp : Nz F C i j (1, 0) (0, 1) * Nz F C i j (1, 0) (0, 1) = 1 :=
    Nz_pos_sq hE hdiv hij hcij hcji
  have hM : Nz F C i j (-1, 0) (0, -1) * Nz F C i j (-1, 0) (0, -1) = 1 :=
    Nz_neg_sq hE hdiv hij hcij hcji
  have hεm : epsNeg F C i j = -Nz F C i j (-1, 0) (0, -1) := rfl
  have hεp' : epsPos F C i j = Nz F C i j (1, 0) (0, 1) := rfl
  let a : F → K := fun s => x (pair i j (1, 0)) s
  let b : F → K := fun s => x (pair i j (0, 1)) s
  let c : F → K := fun s => x (pair i j (1, 1)) (epsPos F C i j * s)
  let a' : F → K := fun s => x (pair i j (-1, 0)) s
  let b' : F → K := fun s => x (pair i j (0, -1)) s
  let c' : F → K := fun s => x (pair i j (-1, -1)) (epsNeg F C i j * s)
  have ha : ∀ s t, a (s + t) = a s * a t := hadd (1, 0) (by decide)
  have hb : ∀ s t, b (s + t) = b s * b t := hadd (0, 1) (by decide)
  have hc : ∀ s t, c (s + t) = c s * c t := fun s t => by
    show x (pair i j (1, 1)) (epsPos F C i j * (s + t)) = _
    rw [mul_add]
    exact hadd (1, 1) (by decide) _ _
  have ha' : ∀ s t, a' (s + t) = a' s * a' t := hadd (-1, 0) (by decide)
  have hb' : ∀ s t, b' (s + t) = b' s * b' t := hadd (0, -1) (by decide)
  have hc' : ∀ s t, c' (s + t) = c' s * c' t := fun s t => by
    show x (pair i j (-1, -1)) (epsNeg F C i j * (s + t)) = _
    rw [mul_add]
    exact hadd (-1, -1) (by decide) _ _
  obtain ⟨ρ, hρ⟩ := ARS.FrameSL3.exists_hom_of_steinberg (ARS.FrameSL3.fam_add ha hb hc ha' hb' hc')
    (fam_comm_signed ha hb hc ha' hb' hc'
      (fun s t => hcomm (1, 0) (1, 1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (1, 0) (0, -1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (0, 1) (1, 1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (0, 1) (-1, 0) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (-1, 0) (-1, -1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (0, -1) (-1, -1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => by
        show ⁅x (pair i j (1, 0)) s, x (pair i j (0, 1)) t⁆ =
          x (pair i j (1, 1)) (epsPos F C i j * (s * t))
        rw [hrel (1, 0) (0, 1) (1, 1) (by decide) (by decide) (by decide) (by decide)]
        congr 1
        rw [hεp']
        ring)
      (fun s t => by
        show ⁅x (pair i j (-1, 0)) s, x (pair i j (1, 1)) (epsPos F C i j * t)⁆ =
          x (pair i j (0, 1)) (s * t)
        rw [hrel (-1, 0) (1, 1) (0, 1) (by decide) (by decide) (by decide) (by decide), hA]
        congr 1
        rw [hεp']
        linear_combination (s * t) * hεp)
      (fun s t => by
        show ⁅x (pair i j (1, 0)) s, x (pair i j (-1, -1)) (epsNeg F C i j * t)⁆ =
          x (pair i j (0, -1)) (-(s * t))
        rw [hrel (1, 0) (-1, -1) (0, -1) (by decide) (by decide) (by decide) (by decide), hB]
        congr 1
        rw [hεm]
        linear_combination (-(s * t)) * hM)
      (fun s t => by
        show ⁅x (pair i j (-1, 0)) s, x (pair i j (0, -1)) t⁆ =
          x (pair i j (-1, -1)) (epsNeg F C i j * (-(s * t)))
        rw [hrel (-1, 0) (0, -1) (-1, -1) (by decide) (by decide) (by decide) (by decide)]
        congr 1
        rw [hεm]
        ring)
      (fun s t => by
        show ⁅x (pair i j (0, -1)) s, x (pair i j (1, 1)) (epsPos F C i j * t)⁆ =
          x (pair i j (1, 0)) (-(s * t))
        rw [hrel (0, -1) (1, 1) (1, 0) (by decide) (by decide) (by decide) (by decide), hD]
        congr 1
        rw [hεp']
        linear_combination (-(s * t)) * hεp)
      (fun s t => by
        show ⁅x (pair i j (0, 1)) s, x (pair i j (-1, -1)) (epsNeg F C i j * t)⁆ =
          x (pair i j (-1, 0)) (s * t)
        rw [hrel (0, 1) (-1, -1) (-1, 0) (by decide) (by decide) (by decide) (by decide), hC']
        congr 1
        rw [hεm]
        linear_combination (s * t) * hM))
  refine ⟨ρ, fun c => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tv_of_ne (by decide), hρ, ← pair_one_zero i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_neg_one_zero i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_zero_one i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_zero_neg_one i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_one_one i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_neg_one_neg_one i j]
    rfl


theorem pairing_single (k j : Fin D.rank) : ∑ m, D.cartan k m * (sroot j) m = D.cartan k j := by
  rw [← coroot_apply]
  exact coroot_single _ _ _

theorem weylElement_mk0_eq (k : Fin D.rank) {t : F} (ht : t ≠ 0) :
    Steinberg.weylElement x k (Units.mk0 t ht) =
      x (sroot k) t * x (-sroot k) (-t⁻¹) * x (sroot k) t := by
  simp [Steinberg.weylElement, sroot]

theorem weylElement_neg_one_eq' (k : Fin D.rank) :
    Steinberg.weylElement x k (-1) =
      x (sroot k) (-1) * x (-sroot k) 1 * x (sroot k) (-1) := by
  simp [Steinberg.weylElement, sroot]


section Torus

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem weyl_pair_conj (k : Fin D.rank) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) {t : F}
    (ht : t ≠ 0) (u : F) :
    (Steinberg.weylElement x k (Units.mk0 t ht) * Steinberg.weylElement x k (-1)) * x β u *
      (Steinberg.weylElement x k (Units.mk0 t ht) * Steinberg.weylElement x k (-1))⁻¹ =
      x β (t ^ (∑ m, D.cartan k m * β m) * u) := by
  have hk : D.cartan k k = 2 := D.isFiniteType.apply_self k
  have hβ' : reflection D.cartan k β ∈ D.roots := reflection_mem_roots k hβ
  have hss : reflection D.cartan k (reflection D.cartan k β) = β := by
    have := congrArg (fun f => f β) (reflection_mul_self hk)
    simpa using this
  have hn' : ∑ m, D.cartan k m * (reflection D.cartan k β) m = -∑ m, D.cartan k m * β m := by
    rw [← coroot_apply, coroot_reflection hk, coroot_apply]
  set p := ∑ m, D.cartan k m * β m with hp
  have e1 : ∀ g h y : K, g * h * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ := fun g h y => by group
  rw [e1, (wsign_spec hE hβ).2 (-1) u, (wsign_spec hE hβ').2 (Units.mk0 t ht), hss, hn']
  have hsq := wsign_mul_self hE (k := k) hβ
  have h2 : ((Units.mk0 t ht ^ (-(-p)) : Fˣ) : F) = t ^ p := by
    rw [neg_neg]; simp
  rcases Int.even_or_odd p with hev | hodd
  · rw [wsign_reflection_even hE hβ (hp ▸ hev)]
    have h1 : (((-1 : Fˣ) ^ (-p) : Fˣ) : F) = 1 := by
      rw [hev.neg.neg_one_zpow]; simp
    rw [h1, h2]
    congr 1
    linear_combination (t ^ p * u) * hsq
  · rw [wsign_reflection hE hβ (hp ▸ hodd)]
    have h1 : (((-1 : Fˣ) ^ (-p) : Fˣ) : F) = -1 := by
      rw [hodd.neg.neg_one_zpow]; simp
    rw [h1, h2]
    congr 1
    linear_combination (t ^ p * u) * hsq

end Torus

section Inj

theorem hElt_tv01_eq {t : F} (ht : t ≠ 0) :
    (hElt (tv 0 1) (tv 1 0) t : SL(3, F)) =
      (tv 0 1 t * tv 1 0 (-t⁻¹) * tv 0 1 t) * (tv 0 1 (-1) * tv 1 0 1 * tv 0 1 (-1)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  rw [cm_h01 ht]
  simp only [map_mul, cm_tv01, cm_tv10, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem hElt_tv12_eq {t : F} (ht : t ≠ 0) :
    (hElt (tv 1 2) (tv 2 1) t : SL(3, F)) =
      (tv 1 2 t * tv 2 1 (-t⁻¹) * tv 1 2 t) * (tv 1 2 (-1) * tv 2 1 1 * tv 1 2 (-1)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  rw [cm_h12 ht]
  simp only [map_mul, cm_tv12, cm_tv21, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem injective_of_sl3_torus {i j k : Fin D.rank} {ρ : SL(3, F) →* K}
    (hi : ∀ c, ρ (tv 0 1 c) = x (sroot i) c ∧ ρ (tv 1 0 c) = x (-sroot i) c)
    (hj : ∀ c, ρ (tv 1 2 c) = x (sroot j) c ∧ ρ (tv 2 1 c) = x (-sroot j) c)
    (hk : ¬ (3 : ℤ) ∣ D.cartan i k + 2 * D.cartan j k) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt : ∃ g, ρ g ≠ 1 := by
    refine ⟨tv 0 1 1, ?_⟩
    rw [(hi 1).1]
    intro h
    have := x_injective' hE (single_mem_roots i) (h.trans (x_zero hE (single_mem_roots i)).symm)
    exact one_ne_zero this
  have hker : g ∈ Subgroup.center SL(3, F) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) hnt hg
  obtain ⟨ω, hω0, hω3, rfl, h1⟩ := exists_eq_of_mem_center hker
  apply h1
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  rw [hElt_tv01_eq hω0, hElt_tv12_eq hω2] at hg
  simp only [map_mul, (hi _).1, (hi _).2, (hj _).1, (hj _).2] at hg
  have hg' : (Steinberg.weylElement x i (Units.mk0 ω hω0) * Steinberg.weylElement x i (-1)) *
      (Steinberg.weylElement x j (Units.mk0 (ω ^ 2) hω2) * Steinberg.weylElement x j (-1)) = 1 := by
    rw [weylElement_mk0_eq i hω0, weylElement_mk0_eq j hω2, weylElement_neg_one_eq',
      weylElement_neg_one_eq']
    exact hg
  have hβ : (sroot k : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots k
  have hconj : ∀ u : F, (Steinberg.weylElement x i (Units.mk0 ω hω0) *
        Steinberg.weylElement x i (-1)) *
      ((Steinberg.weylElement x j (Units.mk0 (ω ^ 2) hω2) * Steinberg.weylElement x j (-1)) *
        x (sroot k) u * (Steinberg.weylElement x j (Units.mk0 (ω ^ 2) hω2) *
          Steinberg.weylElement x j (-1))⁻¹) *
      (Steinberg.weylElement x i (Units.mk0 ω hω0) * Steinberg.weylElement x i (-1))⁻¹ =
      x (sroot k) u := by
    intro u
    have e1 : ∀ a b y : K, a * (b * y * b⁻¹) * a⁻¹ = (a * b) * y * (a * b)⁻¹ := fun a b y => by
      group
    rw [e1, hg', inv_one, one_mul, mul_one]
  have hu := hconj 1
  rw [weyl_pair_conj hE j hβ hω2 1, weyl_pair_conj hE i hβ hω0 _, pairing_single,
    pairing_single] at hu
  have hexp := x_injective' hE hβ hu
  have hzp : ω ^ (D.cartan i k + 2 * D.cartan j k) = 1 := by
    rw [zpow_add₀ hω0, zpow_mul, show (ω : F) ^ (2 : ℤ) = ω ^ 2 from zpow_ofNat ω 2]
    simpa using hexp
  set ωu : Fˣ := Units.mk0 ω hω0 with hωu
  have hu3 : ωu ^ 3 = 1 := Units.ext (by simpa [hωu] using hω3)
  have hue : ωu ^ (D.cartan i k + 2 * D.cartan j k) = 1 :=
    Units.ext (by rw [Units.val_zpow_eq_zpow_val]; simpa [hωu] using hzp)
  have hord : orderOf ωu ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
  · have := orderOf_eq_one_iff.1 h
    simpa [hωu] using congrArg (fun u : Fˣ => (u : F)) this
  · exfalso
    apply hk
    have := orderOf_dvd_iff_zpow_eq_one.2 hue
    rw [h] at this
    exact_mod_cast this

end Inj

end Sl3

end CFSG.ClassicalInvolution.WeakCT
