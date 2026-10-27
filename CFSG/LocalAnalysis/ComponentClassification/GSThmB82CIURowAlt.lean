module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowsCom
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAltJ
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAltJordan

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv Equiv.Perm

namespace QPUJ6

theorem pow_sixteen_le_factorial {p f : ℕ} (hp3 : 3 ≤ p) (hf : 1 ≤ f) :
    (p ^ f) ^ 16 ≤ ((p - 1) * (6 * f) + 1).factorial := by
  rw [← pow_mul]
  rcases Nat.lt_or_ge p 4 with hp4 | hp4
  ·
    obtain rfl : p = 3 := by omega
    have h1 := Nat.factorial_mul_pow_le_factorial (m := 8) (n := 12 * f - 7)
    have h2 : 8 + (12 * f - 7) = (3 - 1) * (6 * f) + 1 := by omega
    rw [h2] at h1
    refine le_trans ?_ h1
    have h3 : (3 : ℕ) ^ 9 ≤ Nat.factorial 8 := by decide
    have h4 : (8 + 1 : ℕ) ^ (12 * f - 7) = 3 ^ (2 * (12 * f - 7)) := by
      rw [pow_mul]
      norm_num
    rw [h4]
    calc (3 : ℕ) ^ (f * 16) ≤ 3 ^ (9 + 2 * (12 * f - 7)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 ^ 9 * 3 ^ (2 * (12 * f - 7)) := pow_add _ _ _
      _ ≤ Nat.factorial 8 * 3 ^ (2 * (12 * f - 7)) := Nat.mul_le_mul_right _ h3
  ·
    set Y := (p - 1) * (6 * f - 1) with hYdef
    set X := (p - 1) * (6 * f) with hXdef
    have hY : X = Y + (p - 1) := by
      rw [hXdef, hYdef, ← Nat.mul_add_one]
      congr 1
      omega
    have h1 := Nat.factorial_mul_pow_le_factorial (m := p - 1) (n := Y + 1)
    have h2 : p - 1 + (Y + 1) = X + 1 := by omega
    rw [h2, show p - 1 + 1 = p by omega] at h1
    refine le_trans ?_ (le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)) h1)
    apply Nat.pow_le_pow_right (by omega)
    have h3 : 3 * (6 * f - 1) ≤ Y := Nat.mul_le_mul_right _ (by omega)
    omega

theorem factorial_ne_pow_six_mul {p f m A : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hA : ¬ p ∣ A) (hAlt : A < (p ^ f) ^ 10) : m.factorial ≠ (p ^ f) ^ 6 * A := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hA0 : A ≠ 0 := by
    rintro rfl
    exact hA (dvd_zero p)
  have hq6 : (p ^ f) ^ 6 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)
  have hv : padicValNat p m.factorial = 6 * f := by
    rw [h, padicValNat.mul hq6 hA0, padicValNat.eq_zero_of_not_dvd hA, add_zero, ← pow_mul,
      padicValNat.prime_pow]
    ring
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.factorial_zero, padicValNat_one_right] at hv
    omega
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) hm0
  rw [hv] at hlt
  have hlow : (p ^ f) ^ 16 ≤ m.factorial :=
    (pow_sixteen_le_factorial hp3 hf).trans (Nat.factorial_le (by omega))
  have hup : (p ^ f) ^ 6 * A < (p ^ f) ^ 16 := by
    have h2 : (p ^ f) ^ 6 * A < (p ^ f) ^ 6 * (p ^ f) ^ 10 :=
      Nat.mul_lt_mul_of_pos_left hAlt (Nat.pos_of_ne_zero hq6)
    have h3 : (p ^ f) ^ 6 * (p ^ f) ^ 10 = (p ^ f) ^ 16 := by ring
    omega
  omega

theorem two_mul_card_ne_factorial (hO : CatLeaf.LieOrderFormulasInput) {X : Type} [Group X]
    {p f m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : IsL4U4Mod4 X p f) :
    2 * Nat.card X ≠ m.factorial := by
  intro hm
  obtain ⟨A, hc, hA, hAlt, -, -⟩ := order_data hO hp hp2 hf hX
  exact factorial_ne_pow_six_mul hp hp2 hf hA hAlt (by rw [← hm, mul_comm, hc])

theorem false_of_alternating (hO : CatLeaf.LieOrderFormulasInput) {M : Type} [Group M]
    [Finite M] (hZ : IsPGroup 2 (center M)) {n : ℕ} (e : M ⧸ center M ≃* alternatingGroup (Fin n))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {L : Subgroup M}
    (hLie : IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f) {t : M} (ht : t * t = 1)
    {J J₀ : Subgroup M} (hJt : J ≤ centralizer ({t} : Set M))
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M)))) (hJ₀L : J₀ ≤ L)
    (hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) : False := by
  have hs := isSimpleGroup hLie
  obtain ⟨ν, hν, hker⟩ := QPUAlt.exists_hom_of_mulEquiv e
  obtain ⟨hdeg, hO', h3⟩ := QPUAlt.isPComponent_centralizer_of_central hZ ν hν hker ht hJt hJc
  have hJL : J ≤ L := by
    rw [← hJ₀, hO', Subgroup.map_bot, sup_bot_eq]
    exact hJ₀L
  let ψ : L →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp (ν.comp L.subtype)
  obtain ⟨m, -, hm⟩ := QPUAlt.two_mul_card_eq_factorial ψ hs
    {x : Fin n | ((ν t : alternatingGroup (Fin n)) : Perm (Fin n)) x = x} hdeg
    fun a ha b hb c hc hab hac hbc => by
      obtain ⟨j, hj, hjσ⟩ := h3 a b c ha hb hc hab hac hbc
      exact ⟨⟨j, hJL hj⟩, hjσ⟩
  exact two_mul_card_ne_factorial hO hp hp2 hf hLie hm

end QPUJ6

theorem cfQPUJ6Alt_holds :
    CFQPUJ6Alt := by
  rintro M _ _ p f hc ⟨n, -, ⟨e⟩⟩
  obtain ⟨-, hZ, hp, hp2, hf, -, E, L, t, J, J₀, -, -, -, -, hLie, -, ht, -, hJt, hJc, -, hJ₀L,
    -, hJ₀⟩ := hc
  exact QPUJ6.false_of_alternating CatLeafProof.lieOrderFormulasInput hZ e hp hp2 hf hLie ht hJt
    hJc hJ₀L hJ₀

end CFSG.ComponentClassification.GSThmB
