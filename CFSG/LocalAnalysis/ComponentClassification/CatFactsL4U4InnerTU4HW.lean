module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TypeU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTLHW

public section

namespace CFSG.ComponentClassification.CatFactsL4U4HW

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.StabU
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks
  CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut
  CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj Matrix

variable {H : Type} [Group H] [Finite H]

theorem innerT_U4 (h : Hyp52W H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hZ : center (OddBar h.K) = ⊥) (hq : p ^ f % 4 = 1) {K : Type} [Field K]
    (hU : UnitaryFieldData p f K) (e : OddBar h.K ≃* StatedProj (StatedSU 4 (p ^ f) K)) :
    h.T ≤ h.K ⊔ h.B ∧ IsCyclic ↥(h.T ⊓ h.K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := hU.finite
  have hKa : conjugate h.K h.a = h.K := by
    obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
    exact hKa
  obtain ⟨ℓ, -, hℓZ, hℓ2, hJC, hJp, hcard, ⟨s, hs, hs2, hsq, hsJbar, hsJ⟩, -⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  obtain ⟨y'', hy''⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  have hℓ1 : ℓ ≠ 1 := fun h1 => hℓZ (by rw [h1]; exact one_mem _)
  have hℓ2' : ℓ ^ 2 = 1 := by rw [hZ] at hℓ2; exact mem_bot.1 hℓ2
  obtain ⟨X, hX⟩ := QuotientGroup.mk_surjective (e ℓ)
  have hXX := sq_eq_neg_one_of_comm_orderOf_U4 hU hp2 (u := e ℓ) (v := e (y'' : OddBar h.K))
    (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1) (by rw [← map_pow, hℓ2', map_one]) hs hs2 hsq
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy''])
    (by rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hJC y''.2)).symm]) X hX
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    let : Fintype K := Fintype.ofFinite K
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, hU.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
        rcases Nat.even_or_odd p with he | ho
        · exfalso
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
            (even_iff_two_dvd.1 he)).symm
        · obtain ⟨t, rfl⟩ := ho
          ring_nf
          omega]
      simp
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
    exact ⟨r, by rw [sq, ← hr]⟩
  have hbl : hU.bar l * l = -1 := by
    have := norm_eq_neg_one_of_sq hU hq hl
    rw [UnitaryFieldData.norm, mul_comm] at this
    exact this
  obtain ⟨Pm, hPm, hXP⟩ := exists_hyperbolic_basis hU hp2 hq X hXX hl
  have hPdet : Pm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPm
    have hGd : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
    rw [det_mul, h0, mul_zero, hGd] at this
    exact zero_ne_one this
  set P : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Pm hPdet with hPdef
  have hPv : (P : Matrix (Fin 4) (Fin 4) K) = Pm := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hP : uStar hU (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG := by
    rw [hPv]
    exact hPm
  have hXeq : X = hypSU hU P hP (X1 l) (unitary_X1 hU hbl) (det_X1 hl) := by
    apply eq_of_cP_eq P
    rw [cP_hypSU, cP, Matrix.mul_assoc, hPv, hXP, ← Matrix.mul_assoc, ← hPv, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, X1_eq_stdDl]
  set J' := (imJB h).map e.toMonoidHom with hJ'
  have hJk : J' ≤ centralizer {(QuotientGroup.mk (hypSU hU P hP (X1 l) (unitary_X1 hU hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))} := by
    rw [← hXeq, hX]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hJC hy)]
  have hJp' : ⁅J', J'⁆ = J' := by rw [hJ', ← map_commutator, hJp]
  have hcardJ' : Nat.card J' = Nat.card (imJB h) := card_map_of_injective e.injective
  have hcard' : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J' := by
    rw [hcardJ']
    exact hcard
  obtain ⟨hJU, hJL, hJle⟩ := eq_of_perfect_U4 hU hp2 P hP hl hbl hJk hJp' hcard'
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hμb := bar_ne_of_generator hU hμ
  have hHU : HasUnipU hU P hP (μ : K) J' := ⟨hJU 1, hJL 1, hJU μ⟩
  have hO : (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map (jbToK h hKa) = ⊥ := by
    apply map_pPrimeCore_eq_bot hKa
    have h1 : 2 * Nat.card (imJB h) ≤ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
      rw [← hcardJ', show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring]
      exact hJle
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
    set α := MulAut.congr e τ with hα
    have hαfix : ∀ x ∈ J', α x = x := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hα, mulAut_congr_apply', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        hfix y hy]
    rcases inner_or_fixed hU hp2 hq P hP hμ α (hαfix _ hHU.1) (hαfix _ hHU.2.1)
        (hαfix _ hHU.2.2) with ⟨z, hz⟩ | ⟨g, hgfix, β, γ, hβ, hg⟩
    · refine ⟨e.symm z, ?_⟩
      ext y
      have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K)) => φ (e y)) hz
      simp only [hα, mulAut_congr_apply', MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
      apply e.injective
      rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · exfalso
      have hxN := not_mem_normalizer hU hp2 P hP hl hbl hμb hJk hHU hβ hg
      set x' := e.symm (QuotientGroup.mk g) with hx'def
      have hx' : τ x' = x' := by
        apply e.injective
        have h1 : α (QuotientGroup.mk g) = QuotientGroup.mk g := hgfix
        rw [hα, mulAut_congr_apply'] at h1
        rw [hx'def, MulEquiv.apply_symm_apply]
        exact h1
      have hxN' : (1 : OddBar h.K)⁻¹ * x' * 1 ∉ normalizer (imJB h : Set (OddBar h.K)) := by
        rw [inv_one, one_mul, mul_one]
        intro hN
        apply hxN
        have h2 := Subgroup.le_normalizer_map e.toMonoidHom ⟨x', hN, rfl⟩
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
    have hcyc := isCyclic_centralizer hU hp2 P hP hμb hHU
    have hTK : h.T ⊓ h.K ≤ h.K := inf_le_right
    let φ₀ : ↥(h.T ⊓ h.K) →* StatedProj (StatedSU 4 (p ^ f) K) :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 h.K)).comp (inclusion hTK))
    have hφ₀ : ∀ t, φ₀ t ∈ centralizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K))) := by
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
    let φ : ↥(h.T ⊓ h.K) →* ↥(centralizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K)))) :=
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
