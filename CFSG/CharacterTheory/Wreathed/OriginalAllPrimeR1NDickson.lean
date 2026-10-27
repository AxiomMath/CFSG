module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersTorus

public section

namespace CFSG.Wreathed.OriginalAllPrime.R1NFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers CFSG.Wreathed.CentralSL2
open CFSG.Semidihedral.ProjectiveSL2Cover CFSG.GorensteinWalter

theorem alternatingGroup_four_cases :
    ∀ g : alternatingGroup (Fin 4), g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

theorem perm_four_cases : ∀ g : Equiv.Perm (Fin 4), g ^ 3 = 1 ∨ g ^ 4 = 1 := by
  decide +kernel

theorem alternatingGroup_five_cases :
    ∀ g : alternatingGroup (Fin 5), g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

variable {F : Type} [Field F]

theorem mem_center_of_sq_eq_one (h2 : (2 : F) ≠ 0) {Z : SpecialLinearGroup (Fin 2) F}
    (hZ : Z ^ 2 = 1) : Z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  have hinv : Z⁻¹ = Z := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hZ]
  have hm := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hinv
  simp only [SL_inv_coe, adjugate_fin_two] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    Fin.isValue] at e00 e01 e10
  have hb : Z 0 1 = 0 := by
    have : (2 : F) * Z 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hc : Z 1 0 = 0 := by
    have : (2 : F) * Z 1 0 = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp this).resolve_left h2
  have hdet : Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 = 1 := by
    have h := Z.2
    rw [det_fin_two] at h
    exact h
  rw [hb, hc] at hdet
  have hd : Z 1 1 = Z 0 0 := e00
  rw [hd] at hdet
  have hsq : (Z 0 0 - 1) * (Z 0 0 + 1) = 0 := by linear_combination hdet
  rw [mem_center_iff_eq_one_or_minusIdentity]
  rcases mul_eq_zero.mp hsq with h | h
  · left
    apply SL_ext_entries
    · change Z 0 0 = 1; linear_combination h
    · change Z 0 1 = 0; exact hb
    · change Z 1 0 = 0; exact hc
    · change Z 1 1 = 1; linear_combination hd + h
  · right
    apply SL_ext_entries
    · change Z 0 0 = -1; linear_combination h
    · change Z 0 1 = 0; exact hb
    · change Z 1 0 = 0; exact hc
    · change Z 1 1 = -1; linear_combination hd + h

theorem sq_eq_one_of_mem_center {Z : SpecialLinearGroup (Fin 2) F}
    (hZ : Z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : Z ^ 2 = 1 := by
  rcases (mem_center_iff_eq_one_or_minusIdentity F Z).mp hZ with rfl | rfl
  · rw [one_pow]
  · exact minusIdentity_square F

theorem nativeQuotient_eq_one_iff (Z : SpecialLinearGroup (Fin 2) F) :
    nativeQuotient F Z = 1 ↔ Z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [← MonoidHom.mem_ker, nativeQuotient_ker, center_eq_zpowers_minusIdentity]

theorem upperSL_one_pow (n : ℕ) : upperSL F 1 ^ n = upperSL F n := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, upperSL_zero]
  | succ n ih => rw [pow_succ, ih, ← upperSL_add, Nat.cast_succ]

theorem eq_top_of_torus_le_of_upperSL_mem
    [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ f) (hq : 9 < p ^ f) (hsq : ¬ IsSquare (-1 : F))
    {K : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hT : Subgroup.centralizer {weyl F} ≤ K) (hu : upperSL F 1 ∈ K) : K = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hq; omega
    · exact h
  have : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hq4 : p ^ f % 4 = 3 := by
    have h := FiniteField.isSquare_neg_one_iff (F := F)
    rw [← Nat.card_eq_fintype_card, hcard] at h
    by_contra hne
    apply hsq
    rw [h]
    exact hne
  have hfodd : Odd f := by
    rcases Nat.even_or_odd f with ⟨j, hj⟩ | h
    · exfalso
      obtain ⟨r, hr⟩ := hpodd.pow (n := j)
      have : p ^ f = (p ^ j) ^ 2 := by rw [hj, ← pow_mul]; ring_nf
      rw [this, hr] at hq4
      ring_nf at hq4
      omega
    · exact h
  set q := p ^ f with hqdef
  obtain ⟨t, ht⟩ : ∃ t, q + 1 = 2 * t := ⟨(q + 1) / 2, by omega⟩
  have ht6 : 6 ≤ t := by omega
  have hTcard : Nat.card (Subgroup.centralizer {weyl F}) = q + 1 := by
    have h := CFSG.Wreathed.OddFieldTorus.torus_card_nonsplit (L := F) h2 hsq
    rw [hcard] at h
    exact h
  have : IsCyclic (Subgroup.centralizer {weyl F}) :=
    CFSG.Wreathed.OddFieldTorus.torus_isCyclic (L := F) h2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.centralizer {weyl F})
  have hgord : orderOf (g : SpecialLinearGroup (Fin 2) F) = q + 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hTcard]
  set g' : SpecialLinearGroup (Fin 2) F := (g : SpecialLinearGroup (Fin 2) F) with hg'
  have hgK : g' ∈ K := hT g.2
  set κ := nativeQuotient F
  have hκg : orderOf (κ g') = t := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, nativeQuotient_eq_one_iff]
      apply mem_center_of_sq_eq_one h2
      rw [← pow_mul, mul_comm, ← ht, ← hgord, pow_orderOf_eq_one]
    · have h1 : κ (g' ^ orderOf (κ g')) = 1 := by rw [map_pow, pow_orderOf_eq_one]
      rw [nativeQuotient_eq_one_iff] at h1
      have h2' := sq_eq_one_of_mem_center h1
      rw [← pow_mul] at h2'
      have h3 := orderOf_dvd_of_pow_eq_one h2'
      rw [hgord, ht, mul_comm (orderOf (κ g')) 2] at h3
      exact Nat.dvd_of_mul_dvd_mul_left two_pos h3
  have hκu : orderOf (κ (upperSL F 1)) = p := by
    have hp1 : κ (upperSL F 1) ^ p = 1 := by
      rw [← map_pow, upperSL_one_pow, CharP.cast_eq_zero, upperSL_zero, map_one]
    have hne : κ (upperSL F 1) ≠ 1 := by
      rw [Ne, nativeQuotient_eq_one_iff, mem_center_iff_eq_one_or_minusIdentity]
      rintro (h | h)
      · have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A 0 1) h
        simp [upperSL] at this
      · have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A 0 1) h
        simp [upperSL, minusIdentity] at this
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hp1) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  set H := K.map κ
  have hgH : κ g' ∈ H := Subgroup.mem_map_of_mem κ hgK
  have huH : κ (upperSL F 1) ∈ H := Subgroup.mem_map_of_mem κ hu
  have htH : t ∣ Nat.card H := by
    rw [← hκg, ← Subgroup.orderOf_mk (κ g') hgH]
    exact orderOf_dvd_natCard _
  have hpH : p ∣ Nat.card H := by
    rw [← hκu, ← Subgroup.orderOf_mk (κ (upperSL F 1)) huH]
    exact orderOf_dvd_natCard _
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hcop : Nat.Coprime t p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hpt
    have : p ∣ q + 1 := ht ▸ dvd_mul_of_dvd_right hpt 2
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp this))
  have hpnot : ∀ z : ℕ, z ∣ q - 1 ∨ z ∣ q + 1 → ¬ p ∣ z := by
    intro z hz hpz
    rcases hz with hz | hz
    · have h1 : p ∣ q - 1 := hpz.trans hz
      have h2' : p ∣ q - 1 + 1 := by rw [Nat.sub_add_cancel (by omega)]; exact hpq
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2'))
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp (hpz.trans hz)))
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rw [hcard]
    exact ⟨(q - 1) / 2, by omega⟩
  have hHord : ∀ {X : Type} [Group X] (e : H ≃* X), orderOf (e ⟨κ g', hgH⟩) = t := by
    intro X _ e
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hκg]
  have hfinish : H = ⊤ → K = ⊤ := by
    intro hH
    have hker : κ.ker ≤ K := by
      rw [nativeQuotient_ker, Subgroup.zpowers_le]
      apply hT
      rw [Subgroup.mem_centralizer_singleton_iff, ← weyl_sq]
      group
    rw [← Subgroup.comap_map_eq_self hker]
    change Subgroup.comap κ H = ⊤
    rw [hH, Subgroup.comap_top]
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hcard H with
    hEl | ⟨z, hz, hHz, -⟩ | ⟨z, hz, hHz, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨k, s, -, hs, N, D, hN, -, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨k, hk, hkf, ⟨e⟩⟩ |
      ⟨k, hk, hkf, -⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hk] at htH
    have := (Nat.Coprime.pow_right k hcop).eq_one_of_dvd htH
    omega
  ·
    exfalso
    rw [hgcd, hcard] at hz
    rw [hHz] at hpH
    apply hpnot z _ hpH
    rcases hz with hz | hz
    · exact Or.inl (hz.trans (Nat.div_dvd_of_dvd ⟨(q - 1) / 2, by omega⟩))
    · exact Or.inr (hz.trans (Nat.div_dvd_of_dvd ⟨(q + 1) / 2, by omega⟩))
  ·
    exfalso
    rw [hgcd, hcard] at hz
    rw [hHz] at hpH
    have hpz : p ∣ z := (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) hpH)
    apply hpnot z _ hpz
    rcases hz with hz | hz
    · exact Or.inl (hz.trans (Nat.div_dvd_of_dvd ⟨(q - 1) / 2, by omega⟩))
    · exact Or.inr (hz.trans (Nat.div_dvd_of_dvd ⟨(q + 1) / 2, by omega⟩))
  ·
    exfalso
    have hx := hHord e
    rcases alternatingGroup_four_cases (e ⟨κ g', hgH⟩) with h | h <;>
    · have := Nat.le_of_dvd (by norm_num) (hx ▸ orderOf_dvd_of_pow_eq_one h)
      omega
  ·
    exfalso
    have hx := hHord e
    rcases perm_four_cases (e ⟨κ g', hgH⟩) with h | h <;>
    · have := Nat.le_of_dvd (by norm_num) (hx ▸ orderOf_dvd_of_pow_eq_one h)
      omega
  ·
    exfalso
    have hx := hHord e
    rcases alternatingGroup_five_cases (e ⟨κ g', hgH⟩) with h | h | h <;>
    · have := Nat.le_of_dvd (by norm_num) (hx ▸ orderOf_dvd_of_pow_eq_one h)
      omega
  ·
    exfalso
    have : N.Normal := hN
    have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hHcard : Nat.card H = p ^ k * s := by
      rw [← hcompl.card_mul_card, hNcard, hDcard]
    rw [hHcard] at htH
    have hts : t ∣ s := (Nat.Coprime.pow_right k hcop).dvd_of_dvd_mul_left htH
    have hgcd' : Nat.gcd (p ^ f - 1) 2 = 2 := by rw [← hqdef, ← hcard, hgcd]
    rw [hgcd'] at hs
    have hspos : 0 < s := hDcard ▸ Nat.card_pos
    have h1 := Nat.le_of_dvd hspos hts
    have h2' := Nat.le_of_dvd (by omega) hs
    omega
  ·
    have hK : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp, hpodd, Nat.pos_of_ne_zero hk, GaloisField.card p k hk⟩
    have hcardH : Nat.card H = p ^ k * (p ^ k * p ^ k - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, psl2_card_formula _ hK, GaloisField.card p k hk, pow_two]
    by_cases hkf' : k = f
    · subst hkf'
      apply hfinish
      apply Subgroup.eq_top_of_card_eq
      rw [hcardH, psl2_card_formula F ⟨p, k, hp, hpodd, hf, hcard⟩, hcard, pow_two]
    · exfalso
      obtain ⟨c, hc⟩ := hkf
      have hcodd : Odd c := by
        rcases Nat.even_or_odd c with ⟨j, hj⟩ | h
        · exfalso
          have : Even f := ⟨k * j, by rw [hc, hj]; ring⟩
          exact (Nat.not_even_iff_odd.mpr hfodd) this
        · exact h
      have hc3 : 3 ≤ c := by
        obtain ⟨j, hj⟩ := hcodd
        rcases j with _ | j
        · exfalso; apply hkf'; rw [hc, hj]; ring
        · omega
      have hq0odd : Odd (p ^ k) := hpodd.pow
      have hq03 : 3 ≤ p ^ k := by
        have : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
        obtain ⟨a, ha⟩ := hq0odd
        omega
      have hq0sq : p ^ k * p ^ k * 3 ≤ q := by
        rw [hqdef, hc, ← pow_add]
        calc p ^ (k + k) * 3 ≤ p ^ (k + k) * p ^ k :=
              Nat.mul_le_mul_left _ hq03
          _ = p ^ (k + k + k) := by rw [← pow_add]
          _ ≤ p ^ (k * c) := Nat.pow_le_pow_right hp.pos (by nlinarith)
      have h2k : 2 ∣ p ^ k * p ^ k - 1 := by
        obtain ⟨a, ha⟩ := hq0odd
        exact ⟨2 * a * a + 2 * a, by rw [ha]; ring_nf; omega⟩
      rw [hcardH, Nat.mul_div_assoc _ h2k] at htH
      have hcop0 : Nat.Coprime t (p ^ k) := Nat.Coprime.pow_right k hcop
      have h9 : 9 ≤ p ^ k * p ^ k := Nat.mul_le_mul hq03 hq03
      have := Nat.le_of_dvd (by omega) (hcop0.dvd_of_dvd_mul_left htH)
      omega
  ·
    exfalso
    have : Even f := (even_two_mul k).two_dvd.trans hkf |> even_iff_two_dvd.mpr
    exact (Nat.not_even_iff_odd.mpr hfodd) this

end CFSG.Wreathed.OriginalAllPrime.R1NFacts
