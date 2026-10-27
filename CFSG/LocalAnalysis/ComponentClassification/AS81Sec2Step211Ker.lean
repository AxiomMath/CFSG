module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Coord
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Hexa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sec2K_le_normalizer_sec2P (E : Subgroup G) :
    sec2K E ≤ normalizer (sec2P E : Set G) := by
  unfold sec2K oUpperTwo
  exact (closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem mem_sec2K_of_odd {E : Subgroup G} {n : G} (hn : n ∈ normalizer (sec2P E : Set G))
    (hodd : Odd (orderOf n)) : n ∈ sec2K E :=
  subset_closure ⟨hn, hodd⟩

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
  {rep : Fin 64 → G} {e : ↥(sec2PlanesP E F) ≃ Fin 6}
  {ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)}
  (hc : Sec2HexaCoord E A F rep e ψ)

include h11 hE16 hF hL hodd hc

omit hc in
include hx hxS h4 in
theorem conj_mem_inf_of_mem_normalizer {n : G} (hn : n ∈ normalizer (sec2P E : Set G)) {a : G}
    (ha : a ∈ E ⊓ A) : n * a * n⁻¹ ∈ E ⊓ A :=
  (mem_normalizer_iff.mp (normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4 hn) a).mp
    ha

include hx hxS h4 in
theorem psi_eq_one_iff (n : ↥(normalizer (sec2P E : Set G))) :
    ψ n = 1 ↔ ∀ p ∈ sec2P E, p⁻¹ * ((n : G) * p * (n : G)⁻¹) ∈ E ⊓ A := by
  have hconj := fun {a : G} (ha : a ∈ E ⊓ A) =>
    conj_mem_inf_of_mem_normalizer h11 hE16 hF hL hodd hx hxS h4 n.2 ha
  constructor
  · intro h p hp
    obtain ⟨v, hv⟩ := hc.surj p hp
    have h1 := hc.conj n v
    rw [h, Equiv.Perm.one_apply] at h1
    have h2 := hconj (inv_mem hv)
    have : p⁻¹ * ((n : G) * p * (n : G)⁻¹) =
        (p⁻¹ * rep v) * ((rep v)⁻¹ * ((n : G) * rep v * (n : G)⁻¹)) *
          ((n : G) * (p⁻¹ * rep v)⁻¹ * (n : G)⁻¹) := by group
    rw [this]
    exact mul_mem (mul_mem hv h1) h2
  · intro h
    refine Equiv.ext fun v => (hc.inj _ _ ?_).symm
    have h1 := h (rep v) (hc.mem v)
    have h2 := inv_mem (hc.conj n v)
    have : (rep v)⁻¹ * rep (ψ n v) = ((rep v)⁻¹ * ((n : G) * rep v * (n : G)⁻¹)) *
        ((rep (ψ n v))⁻¹ * ((n : G) * rep v * (n : G)⁻¹))⁻¹ := by group
    rw [Equiv.Perm.one_apply, this]
    exact mul_mem h1 h2

theorem psi_mem_oval (n : ↥(normalizer (sec2P E : Set G))) (i : Fin 6) (v : Fin 64)
    (hv : v.val ∈ hexaOval[(i : ℕ)]!) :
    (ψ n v).val ∈ hexaOval[(sec2PlanesActionFin E F e n i : ℕ)]! := by
  set V := e.symm i with hV
  set V' := e.symm (sec2PlanesActionFin E F e n i) with hV'
  have hV'eq := coe_symm_sec2PlanesActionFin_apply E F e n i
  rw [← hV', ← hV] at hV'eq
  have hrepV : rep v ∈ (V : Subgroup G) := by
    rw [hc.plane, hV, Equiv.apply_symm_apply]
    exact hv
  have hEAV' : E ⊓ A ≤ (V' : Subgroup G) := inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd V'.2.1
    V'.2.2
  have h1 : (n : G) * rep v * (n : G)⁻¹ ∈ (V' : Subgroup G) := by
    rw [hV'eq, mem_rightConjugate_iff, inv_inv]
    simpa [mul_assoc] using hrepV
  have h2 : rep (ψ n v) ∈ (V' : Subgroup G) := by
    have h3 := hEAV' (inv_mem (hc.conj n v))
    have : rep (ψ n v) = ((n : G) * rep v * (n : G)⁻¹) *
        ((rep (ψ n v))⁻¹ * ((n : G) * rep v * (n : G)⁻¹))⁻¹ := by group
    rw [this]
    exact mul_mem h1 h3
  rw [hc.plane, hV', Equiv.apply_symm_apply] at h2
  exact h2

theorem psi_eq_of_mem_ker (n : ↥(normalizer (sec2P E : Set G)))
    (hn : sec2PlanesActionFin E F e n = 1) :
    ψ n = 1 ∨ ψ n = omegaPerm ∨ ψ n = omegaPerm * omegaPerm := by
  refine eq_of_fix_ovals (hc.psi_add n) fun i hi y hy => ?_
  have h := psi_mem_oval h11 hE16 hF hL hodd hc n ⟨i, hi⟩ y hy
  rwa [hn, Equiv.Perm.one_apply] at h

theorem psi_commute_of_odd (n k : ↥(normalizer (sec2P E : Set G)))
    (hn : sec2PlanesActionFin E F e n = 1) (hk : Odd (orderOf k)) :
    ψ k * ψ n = ψ n * ψ k := by
  have hcase := psi_eq_of_mem_ker h11 hE16 hF hL hodd hc
  have hconj : ∀ m : ↥(normalizer (sec2P E : Set G)), sec2PlanesActionFin E F e m = 1 →
      ψ m = omegaPerm → ψ k * omegaPerm * (ψ k)⁻¹ = omegaPerm := by
    intro m hm hmω
    have hkm : sec2PlanesActionFin E F e (k * m * k⁻¹) = 1 := by
      rw [map_mul, map_mul, hm, mul_one, map_inv, mul_inv_cancel]
    have hne : ψ (k * m * k⁻¹) ≠ 1 := fun h => by
      rw [map_mul, map_mul, map_inv, hmω] at h
      have : omegaPerm = 1 := by
        have h' := congrArg (fun σ => (ψ k)⁻¹ * σ * ψ k) h
        simpa [mul_assoc] using h'
      exact absurd (congrArg (fun σ : Equiv.Perm (Fin 64) => σ 1) this) (by decide)
    have hτ : ψ k * omegaPerm * (ψ k)⁻¹ = omegaPerm ∨
        ψ k * omegaPerm * (ψ k)⁻¹ = omegaPerm * omegaPerm := by
      rcases hcase _ hkm with h | h | h
      · exact absurd h hne
      · left; rwa [map_mul, map_mul, map_inv, hmω] at h
      · right; rwa [map_mul, map_mul, map_inv, hmω] at h
    refine conj_omegaPerm_eq hk ?_ hτ
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases hcase n hn with h | h | h
  · rw [h, mul_one, one_mul]
  · have := hconj n hn h
    rw [h]
    calc ψ k * omegaPerm = ψ k * omegaPerm * (ψ k)⁻¹ * ψ k := by group
      _ = omegaPerm * ψ k := by rw [this]
  · have hn' : sec2PlanesActionFin E F e n⁻¹ = 1 := by rw [map_inv, hn, inv_one]
    have h' : ψ n⁻¹ = omegaPerm := by rw [map_inv, h, inv_omegaPerm_sq]
    have := hconj n⁻¹ hn' h'
    have hc' : ψ k * ψ n⁻¹ = ψ n⁻¹ * ψ k := by
      rw [h']
      calc ψ k * omegaPerm = ψ k * omegaPerm * (ψ k)⁻¹ * ψ k := by group
        _ = omegaPerm * ψ k := by rw [this]
    rw [map_inv] at hc'
    calc ψ k * ψ n = ψ n * ((ψ n)⁻¹ * ψ k) * ψ n := by group
      _ = ψ n * (ψ k * (ψ n)⁻¹) * ψ n := by rw [hc']
      _ = ψ n * ψ k := by group

theorem psi_commute_of_mem_sec2K (n : ↥(normalizer (sec2P E : Set G)))
    (hn : sec2PlanesActionFin E F e n = 1) {k : G} (hk : k ∈ sec2K E) :
    ψ ⟨k, sec2K_le_normalizer_sec2P E hk⟩ * ψ n = ψ n * ψ ⟨k, sec2K_le_normalizer_sec2P E hk⟩ := by
  set H := ((centralizer ({ψ n} : Set (Equiv.Perm (Fin 64)))).comap ψ).map
    (normalizer (sec2P E : Set G)).subtype with hH
  have hle : sec2K E ≤ H := by
    unfold sec2K oUpperTwo
    refine (closure_le _).mpr fun y hy => ?_
    obtain ⟨hyN, hyo⟩ := hy
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_iff]
    intro σ hσ
    rw [Set.mem_singleton_iff] at hσ
    rw [hσ]
    exact (psi_commute_of_odd h11 hE16 hF hL hodd hc n ⟨y, hyN⟩ hn
      (by rwa [Subgroup.orderOf_mk])).symm
  obtain ⟨k', hk', hkk'⟩ := hle hk
  rw [show (⟨k, sec2K_le_normalizer_sec2P E hk⟩ : ↥(normalizer (sec2P E : Set G))) = k' from
    Subtype.ext hkk'.symm]
  have := mem_centralizer_iff.mp hk' (ψ n) (Set.mem_singleton _)
  exact this.symm

end Frame

end CFSG.ComponentClassification.AS81
