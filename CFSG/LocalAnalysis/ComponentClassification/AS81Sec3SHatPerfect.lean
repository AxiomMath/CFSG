module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatLift
import all CFSG.Fischer.F4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.Fischer Sec3Theta Census
open scoped commutatorElement

namespace Sec3Perfect

@[expose] noncomputable def linHom : OV →* Module.End F4 V₀ where
  toFun g := ((g : V₀ ≃ₗ[F4] V₀) : V₀ →ₗ[F4] V₀)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem linHom_apply (g : OV) (v : V₀) :
    linHom g v = ((g : OV) : V₀ ≃ₗ[F4] V₀) v :=
  rfl

theorem linHom_injective : Function.Injective linHom := fun _ _ hgh =>
  Subtype.ext (LinearEquiv.ext fun v => LinearMap.congr_fun hgh v)

theorem linHom_ofArr {M : Array ℕ} (hM : isomOK M = true) : linHom (ofArr M hM) = toLin M :=
  LinearMap.ext fun v => ofArr_apply hM v

theorem linHom_inv_eq {g : OV} {M Mi : Array ℕ} (hg : linHom g = toLin M)
    (hi : matMul M Mi = idMat) : linHom g⁻¹ = toLin Mi := by
  calc linHom g⁻¹ = linHom g⁻¹ * (toLin M * toLin Mi) := by
        rw [Sec3Lift.toLin_mul, hi, Sec3Lift.toLin_idMat_eq_one, mul_one]
    _ = linHom (g⁻¹ * g) * toLin Mi := by rw [map_mul, hg, mul_assoc]
    _ = toLin Mi := by rw [inv_mul_cancel, map_one, one_mul]

theorem comm_word_a {a b : OV} (ha : linHom a = toLin g1M)
    (hb : linHom b = toLin #[5, 1361, 1029, 261, 80, 69]) :
    ⁅a * a, b * b * a * b * b * b * b * b * a * a * b⁆ = a := by
  have h : a * (b * b * a * b * b * b * b * b * a * a * b) * (a * a) =
      a * a * (b * b * a * b * b * b * b * b * a * a * b) := by
    apply linHom_injective
    simp only [map_mul, ha, hb, Sec3Lift.toLin_mul]
    exact congrArg toLin (by decide +kernel)
  rw [commutatorElement_def, ← h]
  group

theorem comm_word_b {a b : OV} (ha : linHom a = toLin g1M)
    (hb : linHom b = toLin #[5, 1361, 1029, 261, 80, 69]) :
    ⁅b * b, a * a * b * a * a * a * a * a * b * b * a⁆ = b := by
  have h : b * (a * a * b * a * a * a * a * a * b * b * a) * (b * b) =
      b * b * (a * a * b * a * a * a * a * a * b * b * a) := by
    apply linHom_injective
    simp only [map_mul, ha, hb, Sec3Lift.toLin_mul]
    exact congrArg toLin (by decide +kernel)
  rw [commutatorElement_def, ← h]
  group

theorem toLin_g1_inv_add (v : V₀) :
    toLin g1iM (toLin #[5, 321, 257, 320, 1280, 337] v) +
      toLin #[5, 321, 257, 320, 1280, 337] v = v := by
  have h : toLin (matMul g1iM #[5, 321, 257, 320, 1280, 337]) +
      toLin #[5, 321, 257, 320, 1280, 337] = LinearMap.id := by
    refine linMap_ext fun i => ?_
    rw [LinearMap.add_apply, toLin_single, toLin_single, LinearMap.id_apply]
    fin_cases i <;> decide
  have h1 := LinearMap.congr_fun h v
  rwa [LinearMap.add_apply, toLin_matMul, LinearMap.comp_apply, LinearMap.id_apply] at h1

theorem eq_one_of_pow_seven {p : Equiv.Perm (Fin 6)} {k : ℕ} (hp : p ^ 7 ^ k = 1) : p = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hp
  have h2 : orderOf p ∣ 720 := by
    have h := orderOf_dvd_card (x := p)
    rwa [Fintype.card_perm, Fintype.card_fin] at h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp h1
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · exfalso
    rw [hj] at h2
    have h7 : 7 ∣ 720 := (dvd_pow_self 7 (Nat.succ_ne_zero j)).trans h2
    norm_num at h7


theorem linHom_G1 : linHom G1 = toLin g1M := linHom_ofArr isom_g1

theorem linHom_G2 : linHom G2 = toLin g2M := linHom_ofArr isom_g2

theorem linHom_G1_inv : linHom G1⁻¹ = toLin g1iM := linHom_inv_eq linHom_G1 mats_parts.2.1

theorem linHom_G2_inv : linHom G2⁻¹ = toLin g2iM := linHom_inv_eq linHom_G2 mats_parts.2.2.1

theorem linHom_conj : linHom (G2 * G1 * G2⁻¹) = toLin #[5, 1361, 1029, 261, 80, 69] := by
  rw [map_mul, map_mul, linHom_G2, linHom_G1, linHom_G2_inv, Sec3Lift.toLin_mul,
    Sec3Lift.toLin_mul]
  exact congrArg toLin (by decide)

theorem G1_pow_seven : G1 ^ 7 = 1 := by
  apply linHom_injective
  rw [map_pow, linHom_G1, Sec3Lift.toLin_g1_pow, map_one]

end Sec3Perfect

namespace Sec38Hyp

namespace ThetaHyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  {H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀}
  {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G} (hT : H.ThetaHyp e b t)
include hT

theorem exists_lift_seven {γ : Census.OV} (hγ : γ ∈ hT.hN.range) (hγ7 : γ ^ 7 = 1) :
    ∃ f : ↥(nSHat Q₀ Q Zs), hT.hN f = γ ∧ ∃ k : ℕ, f ^ 7 ^ k = 1 := by
  obtain ⟨n, rfl⟩ := hγ
  obtain ⟨k, r, hr, hkr⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 7 (by norm_num)
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hr).symm (by norm_num : 1 < 7)
  refine ⟨n ^ (r * c), ?_, k, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hγ7, hc, pow_one]
  · rw [← pow_mul, show r * c * 7 ^ k = 7 ^ k * r * c by ring, pow_mul, ← hkr,
      pow_orderOf_eq_one, one_pow]

theorem exists_goldschmidtN :
    ∃ N : Subgroup G, N ≤ nSHat Q₀ Q Zs ∧
      (∀ B : Subgroup G, Zs ≤ B → B < sec3SHat (Q₀ ⊔ Q) Zs → ∀ n : ℕ,
        ∃ k ∈ (derivedSeries N n).map N.subtype, ∃ s ∈ sec3SHat (Q₀ ⊔ Q) Zs,
          k⁻¹ * s * k * s⁻¹ ∉ B) ∧
      (∀ φ : ↥N →* Equiv.Perm (Fin 6), ∃ n : ℕ, derivedSeries ↥N n ≤ φ.ker) := by
  obtain ⟨c, hc⟩ : ∃ c : Census.OV, c = G2 * G1 * G2⁻¹ := ⟨_, rfl⟩
  have hcM : Sec3Perfect.linHom c = toLin #[5, 1361, 1029, 261, 80, 69] := by
    rw [hc]
    exact Sec3Perfect.linHom_conj
  have hc7 : c ^ 7 = 1 := by
    rw [hc, conj_pow, Sec3Perfect.G1_pow_seven, mul_one, mul_inv_cancel]
  have hcR : c ∈ hT.hN.range := by
    rw [hc]
    exact mul_mem (mul_mem hT.G2_mem_range hT.G1_mem_range) (inv_mem hT.G2_mem_range)
  obtain ⟨f₁, hf₁, k₁, hk₁⟩ := hT.exists_lift_seven hT.G1_mem_range Sec3Perfect.G1_pow_seven
  obtain ⟨f₂, hf₂, k₂, hk₂⟩ := hT.exists_lift_seven hcR hc7
  set N := closure ({(f₁ : G), (f₂ : G)} : Set G) with hNdef
  have hNle : N ≤ nSHat Q₀ Q Zs := (closure_le _).mpr (by
    rintro _ (rfl | rfl)
    · exact f₁.2
    · exact f₂.2)
  have hf₁N : (f₁ : G) ∈ N := subset_closure (Set.mem_insert _ _)
  have hf₂N : (f₂ : G) ∈ N := subset_closure (Set.mem_insert_of_mem _ rfl)
  set ψ := hT.hN.comp (Subgroup.inclusion hNle) with hψ
  have hψ₁ : ψ ⟨f₁, hf₁N⟩ = G1 := hf₁
  have hψ₂ : ψ ⟨f₂, hf₂N⟩ = c := hf₂
  have hder : ∀ n : ℕ, G1 ∈ (derivedSeries N n).map ψ ∧ c ∈ (derivedSeries N n).map ψ := by
    intro n
    induction n with
    | zero =>
      rw [derivedSeries_zero]
      exact ⟨⟨_, mem_top _, hψ₁⟩, ⟨_, mem_top _, hψ₂⟩⟩
    | succ n ih =>
      obtain ⟨⟨p, hp, hpa⟩, ⟨q, hq, hqb⟩⟩ := ih
      rw [derivedSeries_succ]
      refine ⟨⟨⁅p * p, q * q * p * q * q * q * q * q * p * p * q⁆,
        commutator_mem_commutator (mul_mem hp hp) (by apply_rules [mul_mem]), ?_⟩,
        ⟨⁅q * q, p * p * q * p * p * p * p * p * q * q * p⁆,
        commutator_mem_commutator (mul_mem hq hq) (by apply_rules [mul_mem]), ?_⟩⟩
      · rw [map_commutatorElement]
        simp only [map_mul, hpa, hqb]
        exact Sec3Perfect.comm_word_a Sec3Perfect.linHom_G1 hcM
      · rw [map_commutatorElement]
        simp only [map_mul, hpa, hqb]
        exact Sec3Perfect.comm_word_b Sec3Perfect.linHom_G1 hcM
  refine ⟨N, hNle, fun B hZB hBS n => ?_, fun φ => ⟨0, ?_⟩⟩
  ·
    obtain ⟨⟨p, hp, hpa⟩, -⟩ := hder n
    refine ⟨(p : G), ⟨p, hp, rfl⟩, ?_⟩
    by_contra hall
    push Not at hall
    set m : ↥(nSHat Q₀ Q Zs) := Subgroup.inclusion hNle p with hm
    have hmp : (m : G) = (p : G) := rfl
    have hm1 : hT.hN m = G1 := hpa
    have hconj : ∀ s ∈ sec3SHat (Q₀ ⊔ Q) Zs, (p : G)⁻¹ * s * p ∈ sec3SHat (Q₀ ⊔ Q) Zs := by
      intro s hs
      have h1 := conj_mem (inv_mem m.2.2) hs
      rwa [inv_inv, hmp] at h1
    have hneg : ∀ v : Census.V₀, -v = v := fun v => by
      funext i
      rw [Pi.neg_apply]
      generalize v i = w
      revert w
      decide
    have hθ : ∀ s ∈ sec3SHat (Q₀ ⊔ Q) Zs, theta z e t ((p : G)⁻¹ * s * p * s⁻¹) =
        toLin g1iM (theta z e t s) + theta z e t s := by
      intro s hs
      rw [hT.theta_mul (hconj s hs) (inv_mem hs), hT.theta_inv hs, hneg]
      have h1 := hT.hN_theta m⁻¹ hs
      have h2 : ((G1⁻¹ : Census.OV) : Census.V₀ ≃ₗ[F4] Census.V₀) (theta z e t s) =
          toLin g1iM (theta z e t s) := by
        rw [← Sec3Perfect.linHom_apply, Sec3Perfect.linHom_G1_inv]
      rw [map_inv, hm1, h2] at h1
      simp only [InvMemClass.coe_inv, inv_inv, hmp] at h1
      rw [h1]
    apply hBS.not_ge
    intro s hs
    obtain ⟨s₀, hs₀, hs₀θ⟩ :=
      hT.theta_surjective (toLin #[5, 321, 257, 320, 1280, 337] (theta z e t s))
    set s' := (p : G)⁻¹ * s₀ * p * s₀⁻¹ with hs'
    have hs'S : s' ∈ sec3SHat (Q₀ ⊔ Q) Zs := mul_mem (hconj s₀ hs₀) (inv_mem hs₀)
    have hθs' : theta z e t s = theta z e t s' := by
      rw [hs', hθ s₀ hs₀, hs₀θ, Sec3Perfect.toLin_g1_inv_add]
    have h1 := mul_mem (hall s₀ hs₀) (hZB ((hT.theta_eq_iff hs hs'S).mp hθs'))
    rwa [mul_inv_cancel_left] at h1
  ·
    rw [derivedSeries_zero]
    have hpow : ∀ (f : ↥(nSHat Q₀ Q Zs)) (hfN : (f : G) ∈ N) (k : ℕ), f ^ 7 ^ k = 1 →
        (⟨f, hfN⟩ : ↥N) ∈ φ.ker := by
      intro f hfN k hk
      have hf' : (f : G) ^ 7 ^ k = 1 := by
        rw [← SubgroupClass.coe_pow, hk, OneMemClass.coe_one]
      have hfk : (⟨f, hfN⟩ : ↥N) ^ 7 ^ k = 1 :=
        Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hf')
      refine Sec3Perfect.eq_one_of_pow_seven (k := k) ?_
      rw [← map_pow, hfk, map_one]
    have hK : N ≤ φ.ker.map N.subtype := (closure_le _).mpr (by
      rintro _ (rfl | rfl)
      · exact ⟨_, hpow f₁ hf₁N k₁ hk₁, rfl⟩
      · exact ⟨_, hpow f₂ hf₂N k₂ hk₂, rfl⟩)
    intro y _
    obtain ⟨y', hy', hyy⟩ := hK y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'

end ThetaHyp

end Sec38Hyp

end CFSG.ComponentClassification.AS81
