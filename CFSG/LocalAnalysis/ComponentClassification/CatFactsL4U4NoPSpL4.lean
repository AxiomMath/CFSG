module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DarbouxL

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer StabL Blocks
  Matrix

theorem two_mul_ordBC_two {q : ℕ} (hq : Odd q) :
    2 * Open.ordBC 2 q = q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) := by
  obtain ⟨t, rfl⟩ := hq
  have hg : Nat.gcd 2 (2 * t + 1 - 1) = 2 := by
    rw [Nat.add_sub_cancel]
    exact Nat.gcd_mul_right_right t 2
  rw [Open.ordBC, hg, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  have h2 : 2 ∣ (2 * t + 1) ^ (2 * 2) * (((2 * t + 1) ^ (2 * 1) - 1) *
      ((2 * t + 1) ^ (2 * 2) - 1)) := by
    apply Dvd.dvd.mul_left
    apply Dvd.dvd.mul_right
    have : (2 * t + 1) ^ (2 * 1) - 1 = 2 * (2 * t ^ 2 + 2 * t) := by
      have h1 : 1 ≤ (2 * t + 1) ^ (2 * 1) := Nat.one_le_pow _ _ (by omega)
      zify [h1]
      ring
    rw [this]
    exact dvd_mul_right 2 _
  rw [Nat.mul_div_cancel' h2]
  ring_nf

variable {H : Type} [Group H] [Finite H]

theorem noPSp_L4 (h : Hyp52 H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hZ : center (OddBar h.K) = ⊥) (hq : p ^ f % 4 = 3) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = p ^ f) (e : OddBar h.K ≃* StatedProj (StatedSL 4 F))
    (w : H) (hw : w ∈ normalizer (h.K : Set H)) (hwW : w ∈ h.W) (hw2 : w * w = 1)
    (hτ : oddBarConj h.K ⟨w, hw⟩ ≠ 1) :
    ¬ ∃ M : Subgroup (OddBar h.K), (∀ y ∈ M, oddBarConj h.K ⟨w, hw⟩ y = y) ∧
      Blueprint.LieModel ↥M .PSp 2 p f := by
  classical
  rintro ⟨M, hMfix, hM⟩
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
  have hsimp : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_center_eq_bot' h.isQuasisimple_K hZ
  have hsK : s ∣ Nat.card (OddBar h.K) := hsJ.trans (card_subgroup_dvd_card _)
  set τ := actW h hKa ⟨w, hwW⟩ with hτdef
  have hττ : τ = oddBarConj h.K ⟨w, hw⟩ := rfl
  set α := MulAut.congr e' τ with hα
  have hα2 : α ^ 2 = 1 := by
    have : (⟨w, hwW⟩ : h.W) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hw2)
    rw [hα, ← map_pow, hτdef, ← map_pow, this, map_one, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    apply hτ
    rw [← hττ]
    have : τ = (MulAut.congr e').symm α := by rw [hα, MulEquiv.symm_apply_apply]
    rw [this, h1, map_one]
  set M' := M.map e'.toMonoidHom with hM'
  have hM'fix : ∀ x ∈ M', α x = x := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hα, mulAut_congr_apply', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hττ,
      hMfix y hy]
  have hcardM : 2 * Nat.card M = (p ^ f) ^ 4 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := by
    rw [(ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hM)).2.2.1 rfl]
    exact two_mul_ordBC_two (hp.odd_of_ne_two hp2).pow
  have hcardM' : 2 * Nat.card M' =
      Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) := by
    rw [hM', card_map_of_injective e'.injective, hKF, hcardM]
  have hsM : s ∣ Nat.card M := by
    have h1 : s ∣ (p ^ f) ^ 4 - 1 := by
      have : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 + 1) * ((p ^ f) ^ 2 - 1) := by
        have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
        zify [h2, Nat.one_le_pow 4 (p ^ f) (pow_pos hp.pos _)]
        ring
      rw [this]
      exact Dvd.dvd.mul_right hsq _
    have h2 : s ∣ 2 * Nat.card M := by rw [hcardM]; exact Dvd.dvd.mul_left h1 _
    exact (Nat.Coprime.dvd_mul_left ((Nat.coprime_primes hs Nat.prime_two).2 hs2)).1 h2
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := M) s hsM
  have hy₀M' : e' (y₀ : OddBar h.K) ∈ M' := ⟨y₀, y₀.2, rfl⟩
  have hy₀o : orderOf (e' (y₀ : OddBar h.K)) = s := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy₀]
  obtain ⟨A, halt, hαA⟩ := alternating_of_fixed_psp hF' hp hKF hs hs2 (by rw [hF]; exact hsq) α
    hα2 hα1 hM'fix hcardM' hy₀M' hy₀o
  obtain ⟨g₀, hfixS, h₁, hfixh, hne1, hne2⟩ := exists_fixed_conj_of_alternating hF' A halt
  rw [← hαA] at hfixS hfixh
  have hback : ∀ z : OddBar h.K, α (e' z) = e' z → τ z = z := by
    intro z hz
    apply e'.injective
    rw [hα, mulAut_congr_apply', MulEquiv.symm_apply_apply] at hz
    exact hz
  set g := e'.symm (LinearFlag.proj 4 F g₀) with hg
  set x := e'.symm (LinearFlag.proj 4 F (g₀ * h₁ * g₀⁻¹)) with hx
  have hfixJ : ∀ y ∈ imJB h, τ (g * y * g⁻¹) = g * y * g⁻¹ := by
    intro y hy
    apply hback
    have hyJ : e' y ∈ J₀ F := by rw [← hJ'eq]; exact ⟨y, hy, rfl⟩
    obtain ⟨u, hu, hue⟩ := hyJ
    have : e' (g * y * g⁻¹) = LinearFlag.proj 4 F (g₀ * u * g₀⁻¹) := by
      rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, ← hue, map_mul, map_mul,
        map_inv]
    rw [this]
    exact hfixS u hu
  have hfixx : τ x = x := by
    apply hback
    rw [hx, MulEquiv.apply_symm_apply]
    exact hfixh
  have hxN : g⁻¹ * x * g ∉ normalizer (imJB h : Set (OddBar h.K)) := by
    intro hN
    have h2 := Subgroup.le_normalizer_map e'.toMonoidHom ⟨_, hN, rfl⟩
    have h3 : e'.toMonoidHom (g⁻¹ * x * g) = LinearFlag.proj 4 F h₁ := by
      rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, hg, hx, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv]
      group
    rw [h3, ← hJ'] at h2
    rcases conj_k₀_eq_or_neg hF' hJk hU h2 with h4 | h4
    · apply hne1
      have h5 : ((h₁ * k₀ * h₁⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (h₁ : Matrix (Fin 4) (Fin 4) F) * stdJ * ((h₁⁻¹ : SpecialLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) := rfl
      have h6 : ((h₁⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (h₁ : Matrix (Fin 4) (Fin 4) F) = 1 :=
        congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
          (inv_mul_cancel h₁)
      rw [h5] at h4
      calc (h₁ : Matrix (Fin 4) (Fin 4) F) * stdJ = (h₁ : Matrix (Fin 4) (Fin 4) F) * stdJ *
            (((h₁⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (h₁ : Matrix (Fin 4) (Fin 4) F)) := by rw [h6, Matrix.mul_one]
        _ = stdJ * (h₁ : Matrix (Fin 4) (Fin 4) F) := by rw [← Matrix.mul_assoc, h4]
    · apply hne2
      have h5 : ((h₁ * k₀ * h₁⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (h₁ : Matrix (Fin 4) (Fin 4) F) * stdJ * ((h₁⁻¹ : SpecialLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) := rfl
      have h6 : ((h₁⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (h₁ : Matrix (Fin 4) (Fin 4) F) = 1 :=
        congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
          (inv_mul_cancel h₁)
      rw [h5] at h4
      calc (h₁ : Matrix (Fin 4) (Fin 4) F) * stdJ = (h₁ : Matrix (Fin 4) (Fin 4) F) * stdJ *
            (((h₁⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (h₁ : Matrix (Fin 4) (Fin 4) F)) := by rw [h6, Matrix.mul_one]
        _ = -(stdJ * (h₁ : Matrix (Fin 4) (Fin 4) F)) := by
            rw [← Matrix.mul_assoc, h4, Matrix.neg_mul]
  have hW2 : ∃ m : ℕ, (⟨w, hwW⟩ : h.W) ^ 2 ^ m = 1 :=
    ⟨1, Subtype.ext (by simpa [sq] using hw2)⟩
  have hτ1 : τ ≠ 1 := by rw [hττ]; exact hτ
  exact false_of_fixed_conj hKa hsimp hs hs2 hsK hW2 hτ1 hfixJ hfixx hxN

end CFSG.ComponentClassification.CatFactsL4U4
