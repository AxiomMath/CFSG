module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433SameField
import CFSG.Open.StatedCenterThree
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Open.StatedCenterThree Matrix

private theorem exists_of_mulEquiv {Y G : Type} [Group Y] [Group G] (e : Y ≃* G) (g : G)
    (hg : orderOf g = 3) (hgc : g ∉ Subgroup.center G) :
    ∃ y : Y, orderOf y = 3 ∧ y ∉ Subgroup.center Y := by
  refine ⟨e.symm g, (MulEquiv.orderOf_eq e.symm g).trans hg, ?_⟩
  intro hy
  apply hgc
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro k
  have := congrArg e (hy (e.symm k))
  simpa using this

private theorem exists_noncentral_diag {F : Type} [Field F] (H : Subgroup (GL (Fin 3) F))
    (hcyc : (cyc3GL : GL (Fin 3) F) ∈ H) {ω : Fˣ} (hω : orderOf ω = 3)
    (hd : diagGL ω ∈ H) : ∃ g : H, orderOf g = 3 ∧ g ∉ Subgroup.center H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  refine ⟨⟨diagGL ω, hd⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    apply orderOf_eq_prime
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      change (diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1]) ^ 3 = 1
      rw [diagonal_pow, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · simp [← Units.val_pow_eq_pow_val, hω3]
      · simp [← Units.val_pow_eq_pow_val, inv_pow, hω3]
      · simp
    · intro h
      have h00 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
      simp [diagGL] at h00
      exact hω1 h00
  · intro hg
    have hc := Subgroup.mem_center_iff.mp hg ⟨cyc3GL, hcyc⟩
    have hm : (cyc3 : Matrix (Fin 3) (Fin 3) F) * diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1] =
        diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1] * cyc3 := by
      have := congrArg (fun x : H => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hc
      exact this
    obtain ⟨h1, -⟩ := eq_of_diagonal_commute_cyc3 hm.symm
    have h2 : ω⁻¹ = ω := Units.ext (by simpa using h1)
    have h3 : ω ^ 2 = 1 := by
      rw [sq]
      calc ω * ω = ω * ω⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel ω
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hω] at h4
    norm_num at h4

theorem IsSL3EpsOver.exists_noncentral_order_three {Y : Type} [Group Y] {q : ℕ}
    (h : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.IsSL3EpsOver Y q) :
    ∃ y : Y, orderOf y = 3 ∧ y ∉ Subgroup.center Y := by
  obtain ⟨hty, h3⟩ := h
  rcases hty with ⟨F, hF, hfin, hc, ⟨e⟩⟩ | ⟨F, hF, hfin, hc, ⟨e⟩⟩
  ·
    have e' : Matrix.SpecialLinearGroup (Fin 3) F ≃* Y :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).trans e.symm
    have hcard : Nat.card (Subgroup.center Y) = Nat.gcd 3 (Nat.card F - 1) := by
      rw [← Nat.card_congr (Subgroup.centerCongr e').toEquiv]
      exact CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num)
    rw [hcard] at h3
    have hdvd : 3 ∣ Nat.card F - 1 := (Nat.dvd_gcd_iff.1 h3).2
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
    have hcyc : (cyc3GL : GL (Fin 3) F) ∈ StatedSL 3 F := by
      apply Subgroup.subset_closure
      simp [cyc3GL, cyc3, det_fin_three]
    have hd : diagGL ω ∈ StatedSL 3 F := by
      apply Subgroup.subset_closure
      simp [diagGL, det_diagonal, Fin.prod_univ_three]
    obtain ⟨g, hg3, hgc⟩ := exists_noncentral_diag (StatedSL 3 F) hcyc hω hd
    exact exists_of_mulEquiv e g hg3 hgc
  ·
    obtain ⟨p, f, hp, rfl⟩ : ∃ p f : ℕ, p.Prime ∧ q = p ^ f := by
      obtain ⟨p, hp⟩ := CharP.exists F
      letI : Fintype F := Fintype.ofFinite F
      obtain ⟨n, hpp, hn0⟩ := FiniteField.card F p
      have hn : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
      have hqd : q ∣ p ^ (n : ℕ) := by
        rw [← hn, hc]
        exact Dvd.intro_left q (sq q).symm
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
      exact ⟨p, f, hpp, hf⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hq : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have h4 : 3 ∣ p ^ f + 1 := by
      by_cases h2 : p ^ f = 2
      · exact ⟨1, by omega⟩
      · have hnq : (3, p ^ f) ≠ (3, 2) := fun hh => h2 (Prod.mk.inj hh).2
        obtain ⟨-, hcen⟩ :=
          CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hc (le_refl 3) hnq
        have hk := (CFSG.LinearGroups.unitary_scalar_kernel hp hc (by norm_num : 1 ≤ 3)).2.2
        rw [← hcen] at hk
        have hcardY : Nat.card (Subgroup.center Y) =
            Nat.card (Subgroup.center (StatedSU 3 (p ^ f) F)) :=
          Nat.card_congr (Subgroup.centerCongr e).toEquiv
        rw [hcardY, hk] at h3
        exact (Nat.dvd_gcd_iff.1 h3).2
    have hdvd : 3 ∣ Nat.card F - 1 := by
      rw [hc, CFSG.Open.StatedCenterThree.sq_sub_one_eq hq1]
      exact Dvd.dvd.mul_left h4 _
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
    have hωq : ω ^ (p ^ f + 1) = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hω]
      exact h4
    obtain ⟨g, hg3, hgc⟩ :=
      exists_noncentral_diag (StatedSU 3 (p ^ f) F) (cyc3GL_mem hq) hω (diagGL_mem hq hωq)
    exact exists_of_mulEquiv e g hg3 hgc

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
