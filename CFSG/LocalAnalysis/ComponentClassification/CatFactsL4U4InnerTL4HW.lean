module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTLHW

public section

namespace CFSG.ComponentClassification.CatFactsL4U4HW

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.StabL
  CFSG.ComponentClassification.CatFactsL4U4.Blocks Matrix

variable {H : Type} [Group H] [Finite H]

theorem innerT_L4 (h : Hyp52W H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hZ : center (OddBar h.K) = ⊥) (hq : p ^ f % 4 = 3) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = p ^ f) (e : OddBar h.K ≃* StatedProj (StatedSL 4 F)) :
    h.T ≤ h.K ⊔ h.B ∧ IsCyclic ↥(h.T ⊓ h.K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa : conjugate h.K h.a = h.K := by
    obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
    exact hKa
  obtain ⟨ℓ, -, hℓZ, hℓ2, hJC, hJp, hcard, ⟨s, hs, hs2, hsq, hsJbar, hsJ⟩, -⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  have hF' : Fintype.card F % 4 = 3 := by rw [hF]; exact hq
  have hKF : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨y'', hy''⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  have hℓ1 : ℓ ≠ 1 := fun h1 => hℓZ (by rw [h1]; exact one_mem _)
  have hℓ2' : ℓ ^ 2 = 1 := by rw [hZ] at hℓ2; exact mem_bot.1 hℓ2
  obtain ⟨X, hX⟩ := QuotientGroup.mk_surjective (e ℓ)
  have hXX := sq_eq_neg_one_of_comm_orderOf (u := e ℓ) (v := e (y'' : OddBar h.K))
    ⟨Fintype.card F / 2, by omega⟩ (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1)
    (by rw [← map_pow, hℓ2', map_one]) hs hs2 (by rw [hF]; exact hsq)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy''])
    (by rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hJC y''.2)).symm]) X hX
  obtain ⟨e', he'⟩ := exists_normalized_equiv hF' e X hX hXX
  set J' := (imJB h).map e'.toMonoidHom with hJ'
  have hJk : J' ≤ centralizer {LinearFlag.proj 4 F k₀} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← he', ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hJC hy)]
  have hJp' : ⁅J', J'⁆ = J' := by rw [hJ', ← map_commutator, hJp]
  have hcardJ' : Nat.card J' = Nat.card (imJB h) := card_map_of_injective e'.injective
  have hcard' : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J' := by
    rw [hcardJ', hKF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring]
    exact hcard
  have hJ'eq : J' = J₀ F := eq_J₀ hF' hJk hJp' hcard'
  have hU : HasUnipotents J' := by rw [hJ'eq]; exact hasUnipotents_J₀ hF'
  have hO : (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map (jbToK h hKa) = ⊥ := by
    apply map_pPrimeCore_eq_bot hKa
    have h1 := two_mul_card_J₀_le hF'
    rw [← hJ'eq, hcardJ', hKF] at h1
    have h2 : 2 * Nat.card (OddBar h.J) = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
      rw [card_of_lieModel_psl_two hp2 hJ, pow_mul, two_mul_ordA_one]
      · ring_nf
      · exact ((hp.odd_of_ne_two hp2).pow (n := 2)).pow
    omega
  have hsimp : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_center_eq_bot' h.isQuasisimple_K hZ
  have hsK : s ∣ Nat.card (OddBar h.K) := hsJ.trans (card_subgroup_dvd_card _)
  have hTmem : ∀ t ∈ h.T, t ∈ h.W ∧ t ∈ coreActionKernel h.J ∧ ∃ n : ℕ, t ^ 2 ^ n = 1 := by
    intro t ht
    have htS : t ∈ h.S := (mem_inf.1 (mem_inf.1 ht).1).1
    obtain ⟨n, hn⟩ := h.isPGroup_S ⟨t, htS⟩
    exact ⟨(mem_inf.1 (mem_inf.1 ht).1).2, (mem_inf.1 (mem_inf.1 ht).2).2, n,
      by simpa using congrArg Subtype.val hn⟩
  have hinner : ∀ t ∈ h.T, ∀ htW : t ∈ h.W,
      ∃ kb : OddBar h.K, actW h hKa ⟨t, htW⟩ = MulAut.conj kb := by
    intro t ht htW
    obtain ⟨-, htJ, n, hn⟩ := hTmem t ht
    set τ := actW h hKa ⟨t, htW⟩ with hτ
    have hfix := actW_fixes_imJB hKa hO htW htJ
    by_cases hτ1 : τ = 1
    · exact ⟨1, by rw [hτ1, map_one]⟩
    set α := MulAut.congr e' τ with hα
    have hαfix : ∀ x ∈ J', α x = x := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hα, mulAut_congr_apply', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        hfix y hy]
    have hτn : τ ^ 2 ^ n = 1 := by
      have : (⟨t, htW⟩ : h.W) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [hτ, ← map_pow, this, map_one]
    have hα2 : α ^ 2 ^ (n + 1) = 1 := by
      rw [pow_succ, pow_mul, hα, ← map_pow, hτn, map_one, one_pow]
    rcases inner_or_fixed_not_mem_normalizer hF' hp hKF α hα2 hJk hU hαfix with
      ⟨z, hz⟩ | ⟨x, hx, hxN⟩
    · refine ⟨e'.symm z, ?_⟩
      ext y
      have h1 := congrArg (fun φ : MulAut (LinearFlag.projectiveSL 4 F) => φ (e' y)) hz
      simp only [hα, mulAut_congr_apply', MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
      apply e'.injective
      rw [← h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · exfalso
      set x' := e'.symm x with hx'def
      have hx' : τ x' = x' := by
        apply e'.injective
        have h1 : α x = x := hx
        rw [hα, mulAut_congr_apply'] at h1
        rw [hx'def, MulEquiv.apply_symm_apply]
        exact h1
      have hxN' : (1 : OddBar h.K)⁻¹ * x' * 1 ∉ normalizer (imJB h : Set (OddBar h.K)) := by
        rw [inv_one, one_mul, mul_one]
        intro hN
        apply hxN
        have h2 := Subgroup.le_normalizer_map e'.toMonoidHom ⟨x', hN, rfl⟩
        rw [hx'def, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2
        exact h2
      have hW2 : ∃ m : ℕ, (⟨t, htW⟩ : h.W) ^ 2 ^ m = 1 :=
        ⟨n, Subtype.ext (by simpa using hn)⟩
      exact false_of_fixed_conj hKa hsimp hs hs2 hsK hW2 hτ1 (g := 1)
        (fun y hy => by rw [one_mul, inv_one, mul_one]; exact hfix y hy) hx' hxN'
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨htW, -, n, hn⟩ := hTmem t ht
    obtain ⟨kb, hkb⟩ := hinner t ht htW
    exact mem_sup_B_of_inner hKa hZ htW ⟨n, hn⟩ hkb
  ·
    have hcyc := isCyclic_centralizer hF' hU
    have hTK : h.T ⊓ h.K ≤ h.K := inf_le_right
    let φ₀ : ↥(h.T ⊓ h.K) →* LinearFlag.projectiveSL 4 F :=
      e'.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 h.K)).comp (inclusion hTK))
    have hφ₀ : ∀ t, φ₀ t ∈ centralizer (J' : Set (LinearFlag.projectiveSL 4 F)) := by
      intro t
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨htW, htJ, -⟩ := hTmem t (mem_inf.1 t.2).1
      have h1 := actW_fixes_imJB hKa hO htW htJ y hy
      have h2 : actW h hKa ⟨t, htW⟩ = MulAut.conj (QuotientGroup.mk (inclusion hTK t)) :=
        actW_of_mem_K h hKa (inclusion hTK t)
      rw [h2, MulAut.conj_apply] at h1
      simp only [φ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
      rw [← map_mul, ← map_mul]
      congr 1
      calc y * QuotientGroup.mk (inclusion hTK t) =
          QuotientGroup.mk (inclusion hTK t) * y * (QuotientGroup.mk (inclusion hTK t))⁻¹ *
            QuotientGroup.mk (inclusion hTK t) := by rw [h1]
        _ = QuotientGroup.mk (inclusion hTK t) * y := by group
    let φ : ↥(h.T ⊓ h.K) →* ↥(centralizer (J' : Set (LinearFlag.projectiveSL 4 F))) :=
      φ₀.codRestrict _ hφ₀
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro t ht1
      have h1 : φ₀ t = 1 := congrArg Subtype.val ht1
      simp only [φ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      obtain ⟨-, -, n, hn⟩ := hTmem t (mem_inf.1 t.2).1
      have hodd : Odd (orderOf (t : H)) := by
        have h2 := orderOf_dvd_natCard (⟨_, h1⟩ : pPrimeCore 2 ↥h.K)
        rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h2
        have h3 : Odd (Nat.card (pPrimeCore 2 ↥h.K)) := by
          have := (pPrimeCore_coprime_card (p := 2) (G := ↥h.K)).symm
          rwa [Nat.coprime_two_right] at this
        exact Odd.of_dvd_nat h3 h2
      have h4 : orderOf (t : H) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
      have h5 : Nat.Coprime (orderOf (t : H)) (orderOf (t : H)) :=
        Nat.Coprime.coprime_dvd_left h4 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd))
      apply Subtype.ext
      exact orderOf_eq_one_iff.1 ((Nat.coprime_self _).1 h5)
    exact isCyclic_of_injective φ hφ

end CFSG.ComponentClassification.CatFactsL4U4HW
