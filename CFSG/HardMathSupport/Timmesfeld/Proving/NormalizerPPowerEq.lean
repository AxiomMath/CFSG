module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Normalizes

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem normalizes_of_pPower_noncentral_elt {X : Type} [Group X] [Finite X] {p : ℕ}
    (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X} (hL : GLAPComponent p ⊤ L)
    {Y : Subgroup X} (hYc : Nat.Coprime p (Nat.card Y)) {x : X} (hxL : x ∈ L)
    (hxY : x ∈ Subgroup.normalizer (Y : Set X)) {n : ℕ} (hxn : x ^ (p ^ n) = 1)
    (hxnc : ∃ l ∈ L, x * l ≠ l * x) : Y ≤ Subgroup.normalizer (L : Set X) := by
  intro y hy
  by_contra hyn
  have hLc := i116n_isComponentOf_of_glaPComponent hO hL
  have hL' : IsComponentOf (GLBConj y L) ⊤ :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hLc (m := y⁻¹) trivial
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hLc hL' with h | hcomm
  · exact hyn (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  · set x' : X := y⁻¹ * x * y with hx'
    have hx'L' : x' ∈ GLBConj y L := by
      rw [mem_gLBConj]; simpa [hx', mul_assoc] using hxL
    have hxx' : x * x' = x' * x := hcomm x hxL x' hx'L'
    have hx'n : x' ^ (p ^ n) = 1 := by
      have : x' = MulAut.conj y⁻¹ x := by simp [hx']
      rw [this, ← map_pow, hxn, map_one]
    have hzY : x⁻¹ * x' ∈ Y := by
      have h1 : x⁻¹ * y⁻¹ * x ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxY) y⁻¹).1 (inv_mem hy)
        simpa using this
      have := mul_mem h1 hy
      simpa [hx', mul_assoc] using this
    have hzn : (x⁻¹ * x') ^ (p ^ n) = 1 := by
      rw [(Commute.inv_left hxx').mul_pow, inv_pow, hxn, hx'n]
      simp
    have hz1 : x⁻¹ * x' = 1 := by
      set z : Y := ⟨x⁻¹ * x', hzY⟩
      have hzn' : z ^ (p ^ n) = 1 := Subtype.ext hzn
      have h1 : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hzn'
      have h2 : orderOf z ∣ Nat.card Y := orderOf_dvd_natCard z
      have h3 : orderOf z = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n hYc) h1 h2
      have : z = 1 := orderOf_eq_one_iff.1 h3
      exact congrArg Subtype.val this
    have hxx : x' = x := by
      have := hz1
      rw [inv_mul_eq_one] at this
      exact this.symm
    obtain ⟨l, hl, hne⟩ := hxnc
    have hxL' : x ∈ GLBConj y L := hxx ▸ hx'L'
    exact hne (hcomm l hl x hxL').symm

theorem normalizes_pPrimeCore_centralizer_of_pPower_noncentral_elt {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X}
    (hL : GLAPComponent p ⊤ L) {B : Subgroup X} {x : X} (hxL : x ∈ L)
    (hxB : x ∈ Subgroup.normalizer (B : Set X)) {n : ℕ} (hxn : x ^ (p ^ n) = 1)
    (hxnc : ∃ l ∈ L, x * l ≠ l * x) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (L : Set X) := by
  have hxY : x ∈ Subgroup.normalizer
      ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, gLBConj_centralizer,
      mem_normalizer_iff_gLBConj_eq.1 hxB]
  refine normalizes_of_pPower_noncentral_elt hO hL ?_ hxL hxY hxn hxnc
  exact (Nat.Prime.coprime_iff_not_dvd hp).2
    (not_dvd_card_glaPPrimeCoreOf hp (Subgroup.centralizer (B : Set X)))

theorem normalizes_pPrimeCore_centralizer_of_pPower_eq_one {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X}
    (hL : GLAPComponent p ⊤ L) {B : Subgroup X} {x : X} (hxL : x ∈ L)
    (hxB : x ∈ Subgroup.normalizer (B : Set X)) (hxp : ∃ n : ℕ, x ^ (p ^ n) = 1)
    (hxnc : ∃ l ∈ L, x * l ≠ l * x) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (L : Set X) := by
  obtain ⟨n, hxn⟩ := hxp
  exact normalizes_pPrimeCore_centralizer_of_pPower_noncentral_elt hp hO hL hxL hxB hxn hxnc

end CFSG.HardMathSupport.Timmesfeld.Proving

end
