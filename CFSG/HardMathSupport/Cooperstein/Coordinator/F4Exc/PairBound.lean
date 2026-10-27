module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.SepBound

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

section PairBound


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem dim_ge_of_period [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .F4 K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup .F4 K → k} {J : Finset (Fin Tag.F4.rank)}
    (ht : IsChevType .F4 K 2 exists_weyl_neg_F4' ρ y χ J) {s : Fin Tag.F4.rank} (hs : s ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (ht2 : 2 ≤ n / g)
    (hper : ∀ (i : Fin Tag.F4.rank) (z : Kˣ), χ (dC .F4 K i z) ^ (2 ^ g) = χ (dC .F4 K i z)) :
    96 * (n / g) ≤ Module.finrank k V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstr := fun i => string_of_highest (hw := exists_weyl_neg_F4') hK hρ ht i
  choose Jp hJpn hχ hfin hJ0 hwt using hstr
  set a : Fin Tag.F4.rank → ℕ := fun i => ∑ b ∈ Jp i, 2 ^ b with ha
  have hne := string_nonempty hn hK ht hs (hχ s) (hJ0 s)
  have hperJ : ∀ i, (2 ^ n - 1) ∣ (2 ^ g - 1) * a i := fun i => periodic_dvd hK (hχ i) (hper i)
  have hcard := card_ge_of_periodic hg hgn (hJpn s) hne (hperJ s)
  obtain ⟨gh, hgh⟩ := exists_gh hg hgn
  have hghpos : 0 < 2 ^ g - 1 := by
    have : 2 ≤ 2 ^ g := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega
  have hghA : ∀ i, gh ∣ a i := by
    intro i
    have := hperJ i
    rw [hgh] at this
    exact Nat.dvd_of_mul_dvd_mul_left hghpos (by simpa [mul_comm] using this)
  have hgh3 := three_le_gh hn hg hgn ht2 hgh
  have hghodd := gh_odd hn hgh
  have hord := fun j (h0 : 0 < j) (h1 : j < n) => not_dvd_pow_sub_one hg hgn ht2 hgh h0 h1
  have hghM : gh ∣ 2 ^ n - 1 := ⟨2 ^ g - 1, by rw [hgh]; ring⟩
  obtain ⟨-, -, hcont, hmin⟩ := family_props s
  have hy : ∀ i t, ρ (dC .F4 K i t) y = kpow (k := k) K t ((a i : ℕ) : ℤ) • y := by
    intro i t
    rw [ht.2.2.1 _ (dC_mem_H i t), hχ i t]
    unfold kpow
    rw [zpow_natCast]
  have h96 := dim_ge_of_sep hK hρ ht hs a hy (Jp s) (fun b hb => by
      obtain ⟨e, he, he0, hes⟩ := hwt s b hb
      exact ⟨e, he, he0, hes⟩) (fun i i' j j' b b' hb hb' hd => by
    have hlam : ∀ (r : Fin 12) (r' : Fin 8), ∀ c, (gh : ℤ) ∣ (wF s r • (uF s r' • lamF a)) c := by
      intro r r'
      exact weyl_dvdF _ _ _ (weyl_dvdF _ _ _ (lamF_dvd a gh hghA))
    have h3 : ∀ c, (gh : ℤ) ∣ (2 : ℤ) ^ b * (wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) c -
        (2 : ℤ) ^ b' * (wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) c := by
      intro c
      have h4 := dvd_trans (Int.natCast_dvd_natCast.2 hghM) (hd c)
      have h5 : ((((1 : ℤ) • (wF s i • (uF s j • lamF a)) - (2 : ℤ) ^ b • (wF s i •
            (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ))) -
          ((1 : ℤ) • (wF s i' • (uF s j' • lamF a)) - (2 : ℤ) ^ b' • (wF s i' •
            (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)))) c) =
          ((wF s i • (uF s j • lamF a)) c - (wF s i' • (uF s j' • lamF a)) c) -
          ((2 : ℤ) ^ b * (wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) c -
            (2 : ℤ) ^ b' * (wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) c) := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]; ring
      rw [h5] at h4
      have h6 := dvd_sub (hlam i j c) (hlam i' j' c)
      have := dvd_sub h6 h4
      rwa [sub_sub_cancel] at this
    have := sep_gamma hgh3 hghodd hord (ι := Fin 12) (fun r : Fin 12 => wF s r •
        (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) (fun r d m h => hcont r d m h)
      (fun r r' hrr' d hd => hmin r r' hrr' d hd) (hJpn s b hb) (hJpn s b' hb') h3
    exact this)
  calc 96 * (n / g) ≤ 96 * (Jp s).card := Nat.mul_le_mul_left _ hcard
    _ ≤ Module.finrank k V := h96

end PairBound

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
