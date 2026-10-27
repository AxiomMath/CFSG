module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpL4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer StabU HBlocks
  UnitaryOut UnitaryConj Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {H : Type} [Group H] [Finite H]

theorem noPSp_U4 (h : Hyp52 H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hZ : center (OddBar h.K) = ⊥) (hq : p ^ f % 4 = 1) {K : Type} [Field K]
    (hU : UnitaryFieldData p f K) (e : OddBar h.K ≃* StatedProj (StatedSU 4 (p ^ f) K))
    (w : H) (hw : w ∈ normalizer (h.K : Set H)) (hwW : w ∈ h.W) (hw2 : w * w = 1)
    (hτ : oddBarConj h.K ⟨w, hw⟩ ≠ 1) :
    ¬ ∃ M : Subgroup (OddBar h.K), (∀ y ∈ M, oddBarConj h.K ⟨w, hw⟩ y = y) ∧
      Blueprint.LieModel ↥M .PSp 2 p f := by
  classical
  rintro ⟨M, hMfix, hM⟩
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
  obtain ⟨hJU, hJL, -⟩ := eq_of_perfect_U4 hU hp2 P hP hl hbl hJk hJp' hcard'
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hHU : HasUnipU hU P hP (μ : K) J' := ⟨hJU 1, hJL 1, hJU μ⟩
  have hsimp : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_center_eq_bot' h.isQuasisimple_K hZ
  have hsK : s ∣ Nat.card (OddBar h.K) := hsJ.trans (card_subgroup_dvd_card _)
  set τ := actW h hKa ⟨w, hwW⟩ with hτdef
  have hττ : τ = oddBarConj h.K ⟨w, hw⟩ := rfl
  set α := MulAut.congr e τ with hα
  have hαe : ∀ z, α (e z) = e (τ z) := fun z => by
    rw [hα, mulAut_congr_apply', MulEquiv.symm_apply_apply]
  have hα2 : α ^ 2 = 1 := by
    have : (⟨w, hwW⟩ : h.W) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hw2)
    rw [hα, ← map_pow, hτdef, ← map_pow, this, map_one, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    apply hτ
    rw [← hττ]
    have : τ = (MulAut.congr e).symm α := by rw [hα, MulEquiv.symm_apply_apply]
    rw [this, h1, map_one]
  have hαα : ∀ x, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, ← sq, hα2, MulAut.one_apply]
  set M' := M.map e.toMonoidHom with hM'
  have hM'fix : ∀ x ∈ M', α x = x := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hαe, hττ, hMfix y hy]
  have hcardM : 2 * Nat.card M = (p ^ f) ^ 4 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := by
    rw [(ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hM)).2.2.1 rfl]
    exact two_mul_ordBC_two (hp.odd_of_ne_two hp2).pow
  have hcardM' : 2 * Nat.card M' = (p ^ f) ^ 4 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := by
    rw [hM', card_map_of_injective e.injective, hcardM]
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
  have hy₀M' : e (y₀ : OddBar h.K) ∈ M' := ⟨y₀, y₀.2, rfl⟩
  have hy₀o : orderOf (e (y₀ : OddBar h.K)) = s := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy₀]
  set θ : ClassicalGroups.UnitaryFlag.unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (ClassicalGroups.UnitaryFlag.unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := hU.one_le; omega) p
    omega
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    ClassicalInvolution.ModelFacts.UnitaryAut.exists_lift_unitarySU hU hp2 hq5 (d := 4)
      (by norm_num) θ hθ hker α
  obtain ⟨hφ, hcomp⟩ := hinv hαα
  have hlift' : ∀ g : ClassicalGroups.UnitaryFlag.unitarySU p f K 4,
      (QuotientGroup.mk (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) :
        StatedProj (StatedSU 4 (p ^ f) K)) = α (QuotientGroup.mk g) := hlift
  have hcomp' : ∀ g : ClassicalGroups.UnitaryFlag.unitarySU p f K 4,
      ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA
        (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) = g := fun g => by
    have := congrArg (fun F : ClassicalGroups.UnitaryFlag.unitarySU p f K 4 →*
      ClassicalGroups.UnitaryFlag.unitarySU p f K 4 => F g) hcomp
    exact this
  rcases hφ with hφ1 | hφb
  ·
    subst hφ1
    have hgl1 : ∀ Y : GL (Fin 4) K, glAut (RingEquiv.refl K) Y = Y := fun Y => by
      change glAut 1 Y = Y
      rw [map_one]
      rfl
    have hconj : ∀ g : ClassicalGroups.UnitaryFlag.unitarySU p f K 4,
        A * g * A⁻¹ ∈ ClassicalGroups.UnitaryFlag.unitarySU p f K 4 := fun g => by
      have := hA g
      rwa [hgl1] at this
    apply false_of_inner_fixed hU hp2 hq hAu (fun g => ?_) hconj (α := α) (fun g => ?_) hα1
      hM'fix hcardM' hs hs2 hsq hy₀M' hy₀o
    · have e1 := congrArg (fun Y : ClassicalGroups.UnitaryFlag.unitarySU p f K 4 =>
        (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hgl1] at e1
      have e2 : A * A * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (A * A) := by
        calc A * A * (g : GL (Fin 4) K) =
            (A * (A * (g : GL (Fin 4) K) * A⁻¹) * A⁻¹) * (A * A) := by group
          _ = (g : GL (Fin 4) K) * (A * A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e2
      simpa only [Units.val_mul, Matrix.mul_assoc] using e3
    · rw [← hlift']
      congr 1
  ·
    have hφb' : (φ : K → K) = hU.bar := funext hφb
    have hφφ : φ * φ = 1 := RingEquiv.ext fun c => by
      change φ (φ c) = c
      rw [hφb, hφb, hU.bar_bar]
    have hglφ : ∀ Y : GL (Fin 4) K, glAut φ (glAut φ Y) = Y := fun Y => by
      have := congrArg (fun χ : MulAut (GL (Fin 4) K) => χ Y)
        (show glAut φ * glAut φ = 1 by rw [← map_mul, hφφ, map_one])
      exact this
    have hcommA : ∀ g : ClassicalGroups.UnitaryFlag.unitarySU p f K 4,
        (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map hU.bar *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map hU.bar) := by
      intro g
      have e1 := congrArg (fun Y : ClassicalGroups.UnitaryFlag.unitarySU p f K 4 =>
        (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, map_mul, map_inv,
        hglφ] at e1
      have e2 : A * glAut φ A * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (A * glAut φ A) := by
        calc A * glAut φ A * (g : GL (Fin 4) K) =
            (A * (glAut φ A * (g : GL (Fin 4) K) * (glAut φ A)⁻¹) * A⁻¹) * (A * glAut φ A) := by
              group
          _ = (g : GL (Fin 4) K) * (A * glAut φ A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e2
      simp only [Units.val_mul, coe_glAut] at e3
      rw [hφb'] at e3
      simpa only [Matrix.mul_assoc] using e3
    set ψ := ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA with hψdef
    have hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hU.bar *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun g => by
      rw [hψdef, ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, Units.val_mul,
        Units.val_mul, coe_glAut, hφb']
    obtain ⟨ε, hε, hAA, hAt⟩ := symm_or_alt_of_graph hU hp2 hq hAu hcommA
    rcases hε with rfl | rfl
    ·
      exact false_of_graph_symm hU hp2 hq hAu (by rw [hAA, one_smul]) ψ hψv hlift' hM'fix hcardM'
    ·
      obtain ⟨g₀, hfixJ', m, hmfix, hmN⟩ := exists_fixed_of_alt hU hp2 hq P hP hl hbl hμ hJk hJp'
        hHU hAu (by rw [hAA, neg_one_smul]) (by rw [hAt, neg_one_smul]) ψ hψv hlift'
      set g := e.symm (QuotientGroup.mk g₀) with hg
      set x := e.symm (QuotientGroup.mk m) with hx
      have hfixJ : ∀ y ∈ imJB h, τ (g * y * g⁻¹) = g * y * g⁻¹ := by
        intro y hy
        apply e.injective
        have e1 : e (g * y * g⁻¹) = QuotientGroup.mk g₀ * e y * (QuotientGroup.mk g₀)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply]
        rw [← hαe, e1]
        exact hfixJ' (e y) ⟨y, hy, rfl⟩
      have hfixx : τ x = x := by
        apply e.injective
        rw [← hαe, hx, MulEquiv.apply_symm_apply]
        exact hmfix
      have hxN : g⁻¹ * x * g ∉ normalizer (imJB h : Set (OddBar h.K)) := by
        intro hN
        have h2 := Subgroup.le_normalizer_map e.toMonoidHom ⟨_, hN, rfl⟩
        apply hmN
        have h3 : e.toMonoidHom (g⁻¹ * x * g) = (QuotientGroup.mk g₀)⁻¹ * QuotientGroup.mk m *
            QuotientGroup.mk g₀ := by
          rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, hg, hx,
            MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        rw [h3] at h2
        exact h2
      have hW2 : ∃ n : ℕ, (⟨w, hwW⟩ : h.W) ^ 2 ^ n = 1 :=
        ⟨1, Subtype.ext (by simpa [sq] using hw2)⟩
      have hτ1 : τ ≠ 1 := by rw [hττ]; exact hτ
      exact false_of_fixed_conj hKa hsimp hs hs2 hsK hW2 hτ1 hfixJ hfixx hxN

end CFSG.ComponentClassification.CatFactsL4U4
