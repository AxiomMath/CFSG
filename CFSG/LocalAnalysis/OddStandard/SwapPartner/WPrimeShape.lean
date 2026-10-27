module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProd
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShapeTable
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

open scoped commutatorElement

private lemma wt_prod_mul_inv_eq_one {u v σ₁ σ₂ : Perm (Fin 8)}
    (hu : u * σ₁ = σ₁ * u) (hv : v * σ₂ = σ₂ * v) :
    (u, v) * (σ₁, σ₂) * (u, v)⁻¹ * (σ₁, σ₂)⁻¹ = 1 := by
  rw [Prod.ext_iff]
  constructor <;>
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Prod.fst_one,
      Prod.snd_one]
  · rw [hu]; group
  · rw [hv]; group

private lemma wt_twisted_eq_one {u v a : Perm (Fin 8)} (hu : u = a * v * a⁻¹) :
    (u, v) * (a, a⁻¹) * (v, u)⁻¹ * (a, a⁻¹)⁻¹ = 1 := by
  subst hu
  rw [Prod.ext_iff]
  constructor <;>
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Prod.fst_one,
      Prod.snd_one]
  · group
  · group

namespace WreathCase

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

theorem theta_mul_self (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    {y : normalizer (K : Set X)} (hy : y * y = 1) :
    (theta H e y).1 * (theta H e y).1 = 1 ∧ (theta H e y).2 * (theta H e y).2 = 1 := by
  have h : theta H e y * theta H e y = 1 := by
    rw [← map_mul, hy, map_one]
  exact ⟨by simpa using congrArg Prod.fst h, by simpa using congrArg Prod.snd h⟩

theorem two_mul_le_card_centralizer_of_not_mem_normalizer [Finite X]
    (H : WreathCase t Sg V K) {x : X} (hx : x * x = 1) (hxN : x ∉ normalizer (K : Set X)) :
    2 * 40320 ≤ Nat.card (centralizer ({x} : Set X)) := by
  obtain ⟨e⟩ := H.iso
  let N : Subgroup X := normalizer (K : Set X)
  have hxtN : x * t ∈ N := by
    rcases (xor_def.mp (H.mem_normalizer_xor x)) with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxN
  let y : N := ⟨x * t, hxtN⟩
  have hy_eq : (y : X) * t = x := by
    change (x * t) * t = x
    rw [mul_assoc, H.t_mul_t, mul_one]
  have hconj : y * conjT H y = 1 := by
    apply Subtype.ext
    have ht : t⁻¹ = t := by simpa using inv_eq_of_mul_eq_one_left H.t_mul_t
    change (x * t) * (t * (x * t) * t⁻¹) = 1
    rw [ht]
    calc (x * t) * (t * (x * t) * t) = (x * (t * t)) * (x * (t * t)) := by group
      _ = 1 := by simp [H.t_mul_t, hx]
  have hΘy_mul : theta H e y * (theta H e y).swap = 1 := by
    have h := congrArg (fun z : N => theta H e z) hconj
    rw [map_mul, map_one] at h
    rw [theta_conjT] at h
    exact h
  let a : Perm (Fin 8) := (theta H e y).1
  let b : Perm (Fin 8) := (theta H e y).2
  have hΘy : theta H e y = (a, b) := Prod.ext rfl rfl
  have hab : a * b = 1 := by
    have h := congrArg Prod.fst hΘy_mul
    simpa [a, b] using h
  have hb : b = a⁻¹ := by
    have h1 : a = b⁻¹ := mul_eq_one_iff_eq_inv.mp hab
    rw [h1, inv_inv]
  let S₀ : Subgroup N := (twistedDiag a).comap (theta H e)
  let S : Subgroup X := S₀.map N.subtype
  let Y : Subgroup X := centralizer (CFSG.layer X : Set X)
  obtain ⟨g₀, hg₀, hg₀s1, hg₀s2⟩ := exists_odd_odd H e
  have htw_le : twistedDiag a ≤ (theta H e).range := by
    intro g hg
    have h := mem_of_sign_eq_of_prod_le (theta H e).range (alt_prod_alt_le_range H e)
      hg₀ hg₀s1 hg₀s2 (u := g.1) (v := g.2) (sign_eq_of_mem_twistedDiag hg)
    simpa using h
  have hcard_S0 : Nat.card S₀ = Nat.card (twistedDiag a) * Nat.card (theta H e).ker :=
    card_comap_eq_of_le_range (theta H e) (twistedDiag a) htw_le
  have hcard_S : Nat.card S = Nat.card S₀ :=
    Subgroup.card_map_of_injective (K := S₀) (f := N.subtype) N.subtype_injective
  have hmem : ∀ z ∈ S, z * x * z⁻¹ * x⁻¹ ∈ Y := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    have hn_tw : theta H e n ∈ twistedDiag a := hn
    have huv : (theta H e n).1 = a * (theta H e n).2 * a⁻¹ :=
      (mem_twistedDiag_iff (a := a)).mp hn_tw
    change (n : X) * x * (n : X)⁻¹ * x⁻¹ ∈ centralizer (CFSG.layer X : Set X)
    have hwx : (n : X) * x * (n : X)⁻¹ * x⁻¹ =
        ((n * y * (conjT H n)⁻¹ * y⁻¹ : N) : X) := by
      have ht : t⁻¹ = t := by simpa using inv_eq_of_mul_eq_one_left H.t_mul_t
      rw [show x = (y : X) * t from hy_eq.symm]
      rw [mul_inv_rev, ht]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjT, mul_inv_rev, ht]
      group
    rw [hwx]
    apply (mem_ker_theta_iff H e (n * y * (conjT H n)⁻¹ * y⁻¹)).mp
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [theta_conjT]
    rw [show theta H e n = ((theta H e n).1, (theta H e n).2) from Prod.ext rfl rfl]
    rw [hΘy, hb]
    exact wt_twisted_eq_one huv
  have hY : Nat.card Y = Nat.card (theta H e).ker := by
    change Nat.card (centralizer (CFSG.layer X : Set X)) = Nat.card (theta H e).ker
    rw [card_ker_theta H e]
  have hpos : 0 < Nat.card (theta H e).ker := by
    haveI : Nonempty (theta H e).ker := ⟨1, by simp⟩
    exact Nat.card_pos
  have hbounds := card_le_card_inf_centralizer_mul S Y x hmem
  let M : Subgroup X := S ⊓ centralizer ({x} : Set X)
  have hM : 40320 ≤ Nat.card M := by
    have h' : 40320 * Nat.card (theta H e).ker ≤
        Nat.card M * Nat.card (theta H e).ker := by
      rw [hcard_S, hcard_S0, card_twistedDiag, hY] at hbounds
      exact hbounds
    exact Nat.le_of_mul_le_mul_right h' hpos
  have hS_le_N : S ≤ N := Subgroup.map_subtype_le S₀
  have htwo : 2 * Nat.card M ≤ Nat.card (centralizer ({x} : Set X)) :=
    two_mul_card_le_card_centralizer M N x (le_trans inf_le_left hS_le_N) inf_le_right hxN
  calc 2 * 40320 ≤ 2 * Nat.card M := Nat.mul_le_mul_left 2 hM
    _ ≤ Nat.card (centralizer ({x} : Set X)) := htwo

theorem altCentCard8_mul_le_card_centralizer_of_mem_normalizer [Finite X]
    (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {x : X}
    (hx : x * x = 1) (hxN : x ∈ normalizer (K : Set X)) :
    altCentCard8 (theta H e ⟨x, hxN⟩).1 * altCentCard8 (theta H e ⟨x, hxN⟩).2 ≤
      Nat.card (centralizer ({x} : Set X)) := by
  let N : Subgroup X := normalizer (K : Set X)
  let y : N := ⟨x, hxN⟩
  let σ₁ : Perm (Fin 8) := (theta H e y).1
  let σ₂ : Perm (Fin 8) := (theta H e y).2
  let C₁ : Subgroup (Perm (Fin 8)) :=
    alternatingGroup (Fin 8) ⊓ centralizer ({σ₁} : Set (Perm (Fin 8)))
  let C₂ : Subgroup (Perm (Fin 8)) :=
    alternatingGroup (Fin 8) ⊓ centralizer ({σ₂} : Set (Perm (Fin 8)))
  let B : Subgroup (Perm (Fin 8) × Perm (Fin 8)) := C₁.prod C₂
  let S₀ : Subgroup N := B.comap (theta H e)
  let S : Subgroup X := S₀.map N.subtype
  let Y : Subgroup X := centralizer (CFSG.layer X : Set X)
  have hΘy : theta H e y = (σ₁, σ₂) := Prod.ext rfl rfl
  have hB_le : B ≤ (theta H e).range := by
    intro g hg
    rw [Subgroup.mem_prod] at hg
    have h := alt_prod_alt_le_range H e g.1 hg.1.1 g.2 hg.2.1
    simpa using h
  have hcard_S0 : Nat.card S₀ = Nat.card B * Nat.card (theta H e).ker :=
    card_comap_eq_of_le_range (theta H e) B hB_le
  have hcard_S : Nat.card S = Nat.card S₀ :=
    Subgroup.card_map_of_injective (K := S₀) (f := N.subtype) N.subtype_injective
  have hcard_B : Nat.card B = altCentCard8 σ₁ * altCentCard8 σ₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv C₁ C₂).toEquiv, Nat.card_prod]
    rfl
  have hmem : ∀ z ∈ S, z * x * z⁻¹ * x⁻¹ ∈ Y := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    have hnB : theta H e n ∈ B := hn
    rw [Subgroup.mem_prod] at hnB
    have hc1 : (theta H e n).1 * σ₁ = σ₁ * (theta H e n).1 :=
      Subgroup.mem_centralizer_singleton_iff.mp hnB.1.2
    have hc2 : (theta H e n).2 * σ₂ = σ₂ * (theta H e n).2 :=
      Subgroup.mem_centralizer_singleton_iff.mp hnB.2.2
    change (n : X) * x * (n : X)⁻¹ * x⁻¹ ∈ centralizer (CFSG.layer X : Set X)
    apply (mem_ker_theta_iff H e (n * y * n⁻¹ * y⁻¹)).mp
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hΘy]
    rw [show theta H e n = ((theta H e n).1, (theta H e n).2) from Prod.ext rfl rfl]
    exact wt_prod_mul_inv_eq_one hc1 hc2
  have hY : Nat.card Y = Nat.card (theta H e).ker := by
    change Nat.card (centralizer (CFSG.layer X : Set X)) = Nat.card (theta H e).ker
    rw [card_ker_theta H e]
  have hpos : 0 < Nat.card (theta H e).ker := by
    haveI : Nonempty (theta H e).ker := ⟨1, by simp⟩
    exact Nat.card_pos
  have hbounds := card_le_card_inf_centralizer_mul S Y x hmem
  let M : Subgroup X := S ⊓ centralizer ({x} : Set X)
  have hB_le_M : Nat.card B ≤ Nat.card M := by
    have h' : Nat.card B * Nat.card (theta H e).ker ≤
        Nat.card M * Nat.card (theta H e).ker := by
      rw [hcard_S, hcard_S0, hY] at hbounds
      exact hbounds
    exact Nat.le_of_mul_le_mul_right h' hpos
  calc altCentCard8 (theta H e ⟨x, hxN⟩).1 * altCentCard8 (theta H e ⟨x, hxN⟩).2
      = Nat.card B := by rw [hcard_B]
    _ ≤ Nat.card M := hB_le_M
    _ ≤ Nat.card (centralizer ({x} : Set X)) := Subgroup.card_le_of_le inf_le_right

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner
