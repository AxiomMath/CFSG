module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear CFSG.Yardstones.Md0ec50421ce4

section Centre

variable {G H : Type*} [Group G] [Group H]

open scoped commutatorElement in
private theorem mem_center_of_commutator_mem_center (hG : commutator G = ⊤) {g : G}
    (hc : ∀ x : G, ⁅g, x⁆ ∈ Subgroup.center G) : g ∈ Subgroup.center G := by
  have hmul : ∀ x y : G, ⁅g, x * y⁆ = ⁅g, x⁆ * ⁅g, y⁆ := by
    intro x y
    have hxc : x * ⁅g, y⁆ = ⁅g, y⁆ * x := Subgroup.mem_center_iff.mp (hc y) x
    have hcx : ⁅g, y⁆ * x⁻¹ = x⁻¹ * ⁅g, y⁆ := by
      calc ⁅g, y⁆ * x⁻¹ = x⁻¹ * (x * ⁅g, y⁆) * x⁻¹ := by group
        _ = x⁻¹ * (⁅g, y⁆ * x) * x⁻¹ := by rw [hxc]
        _ = x⁻¹ * ⁅g, y⁆ := by group
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc g * (x * y) * g⁻¹ * (x * y)⁻¹
        = g * x * (g⁻¹ * (g * y * g⁻¹ * y⁻¹)) * x⁻¹ := by group
      _ = g * x * g⁻¹ * (⁅g, y⁆ * x⁻¹) := by rw [commutatorElement_def]; group
      _ = g * x * g⁻¹ * (x⁻¹ * ⁅g, y⁆) := by rw [hcx]
      _ = g * x * g⁻¹ * x⁻¹ * (g * y * g⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  have hinv : ∀ u : G, ⁅g, u⁻¹⁆ * ⁅g, u⁆ = 1 := by
    intro u
    have h := hmul u⁻¹ u
    rw [inv_mul_cancel, commutatorElement_one_right] at h
    exact h.symm
  have hpow : ∀ x : G, ⁅g, x⁆ = 1 := by
    intro x
    have hx : x ∈ commutator G := by rw [hG]; exact Subgroup.mem_top x
    change x ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, -, b, -, rfl⟩ := hw
      have hp : ⁅g, a⁆ * ⁅g, b⁆ = ⁅g, b⁆ * ⁅g, a⁆ :=
        Subgroup.mem_center_iff.mp (hc b) _
      have hpi : ⁅g, a⁻¹⁆ = ⁅g, a⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv a)
      have hqi : ⁅g, b⁻¹⁆ = ⁅g, b⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv b)
      rw [commutatorElement_def a b, hmul, hmul, hmul, hpi, hqi]
      calc ⁅g, a⁆ * ⁅g, b⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ = ⁅g, b⁆ * ⁅g, a⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ := by
            rw [hp]
        _ = 1 := by group
    | one => simp
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx =>
      have := hinv x
      rw [hx, mul_one] at this
      exact this
  refine Subgroup.mem_center_iff.mpr fun x => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hpow x)).symm

private theorem center_quot_equiv_of_surjective (hG : commutator G = ⊤) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G) :
    Nonempty (H ⧸ Subgroup.center H ≃* G ⧸ Subgroup.center G) := by
  let φ : G →* H ⧸ Subgroup.center H := (QuotientGroup.mk' (Subgroup.center H)).comp f
  have hφ : Function.Surjective φ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, rfl⟩ := hf x
    exact ⟨g, rfl⟩
  have hker' : φ.ker = Subgroup.center G := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hfx : f x ∈ Subgroup.center H := by
        have hx' : ((f x : H) : H ⧸ Subgroup.center H) = 1 := hx
        exact (QuotientGroup.eq_one_iff (f x)).mp hx'
      apply mem_center_of_commutator_mem_center hG
      intro y
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hfx (f y)).symm
    · intro hx
      rw [MonoidHom.mem_ker]
      have hfx : f x ∈ Subgroup.center H := by
        refine Subgroup.mem_center_iff.mpr fun h => ?_
        obtain ⟨y, rfl⟩ := hf h
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      exact (QuotientGroup.eq_one_iff (f x)).mpr hfx
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker')⟩

end Centre

variable {F : Type} [Field F] {p : ℕ} {μ : F}

private noncomputable def slCast {a b : ℕ} (h : a = b) :
    SpecialLinearGroup (Fin a) F ≃* SpecialLinearGroup (Fin b) F := by
  subst h
  exact MulEquiv.refl _

noncomputable def jhEquivSL3 : ↥(JH F) ≃* SpecialLinearGroup (Fin 3) F :=
  (mapProjEquiv _ le_rfl).symm.trans
    ((((MonoidHom.ofInjective (blockSLOn_injective (k := F) blockJ)).trans
      (MulEquiv.subgroupCongr (range_blockSLOn blockJ))).symm).trans (slCast (by decide)))

section Root

variable [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p) (hF : 4 ≤ Nat.card F)
include hp hp2 hμ hF

theorem glaPPrimeCore_JH_le_center :
    GLAPPrimeCore p ↥(JH F) ≤ Subgroup.center ↥(JH F) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple
    (isQuasisimple_JH hp hp2 hμ hF) (GLAPPrimeCore.normal p _) fun htop => ?_
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥(JH F))) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top] at hcop
  have hdvd : p ∣ Nat.card ↥(JH F) :=
    (dvd_card_JH hp hp2 hμ hF).trans (Subgroup.card_quotient_dvd_card _)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

theorem nonempty_pSimple_JH_equiv :
    Nonempty (PSimple p (JH F) ≃* ProjectiveSpecialLinearGroup (Fin 3) F) := by
  obtain ⟨e₁⟩ := center_quot_equiv_of_surjective
    (isQuasisimple_JH hp hp2 hμ hF).1 (QuotientGroup.mk' (GLAPPrimeCore p ↥(JH F)))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact glaPPrimeCore_JH_le_center hp hp2 hμ hF)
  exact ⟨e₁.trans (QuotientGroup.congr _ _ jhEquivSL3 (Subgroup.map_center_eq _))⟩

theorem center_pQuot_JH_ne_bot (h3 : p = 3) :
    Subgroup.center (PQuot p (JH F)) ≠ ⊥ := by
  subst h3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hμ0 := ne_zero_of_root hp hp2 hμ
  set c : Fin 4 → F := ![1, μ, μ, μ] with hc
  have hcprod : ∏ i, c i = 1 := by
    rw [Fin.prod_univ_four]
    show 1 * μ * μ * μ = 1
    rw [one_mul, ← pow_two, ← pow_succ, hμ.pow_eq_one]
  have hcJ : ∀ i j, i ≠ 0 → j ≠ 0 → c i = c j := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all [hc]
  have hc0 : diagSL c hcprod ∈ coordBlockSL F blockJ := by
    rw [mem_coordBlockSL_iff]
    intro i j hij
    rw [coe_diagSL]
    have hi : i = 0 ∨ j = 0 := by simpa [mem_blockJ] using hij
    by_cases hij' : i = j
    · subst hij'
      rcases hi with rfl | rfl <;> simp [hc]
    · rw [diagonal_apply_ne _ hij', if_neg hij']
  set x : ↥(JH F) := ⟨proj 4 F (diagSL c hcprod), Subgroup.mem_map_of_mem _ hc0⟩ with hx
  have hxZ : x ∈ Subgroup.center ↥(JH F) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hx]
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1
      (coordBlockSL_le_centralizer_diagSL hcJ hm))
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simp only [hx, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, diagSL_pow_eq_one hp hp2 hμ
      (fun i => by fin_cases i <;> simp [hc, hμ.pow_eq_one]), map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 := congrArg Subtype.val h1
    simp only [hx, OneMemClass.coe_one] at h2
    have h3 := eq_one_of_mem_coordBlockSL_of_proj_eq_one hc0 h2
    have h4 := congrArg
      (fun g : SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 1 1) h3
    simp only [coe_diagSL, diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h4
    exact ne_one_of_root hp hp2 hμ h4
  intro hbot
  have hxim : (QuotientGroup.mk x : PQuot 3 (JH F)) ∈ Subgroup.center (PQuot 3 (JH F)) :=
    Subgroup.map_center_le_center (f := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(JH F)))
      (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hxZ)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxim
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥(JH F)) := by
    have h1 : orderOf (⟨x, hxim⟩ : GLAPPrimeCore 3 ↥(JH F)) = 3 := by
      rw [Subgroup.orderOf_mk, hord]
    have h2 := orderOf_dvd_natCard (⟨x, hxim⟩ : GLAPPrimeCore 3 ↥(JH F))
    rwa [h1] at h2
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥(JH F))) := CFSG.pPrimeCore_coprime_card
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

end Root

theorem isSL3Type_JH (Q : TauCeti.PrimePower) [Fact Q.p.Prime] (hQ2 : Q.p ≠ 2)
    {μ : GaloisField Q.p Q.exponent} (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p)
    (hF : 4 ≤ Nat.card (GaloisField Q.p Q.exponent)) :
    IsSL3Type p Q.p (JH (GaloisField Q.p Q.exponent)) := by
  have hv : (TauCeti.LieTypeIndex.A 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
    · omega
    · rw [TauCeti.PrimePower.card_def] at h
      have hdvd : Q.p ∣ 2 := by
        rw [← h]
        exact dvd_pow_self Q.p Q.exponent_pos.ne'
      exact hQ2 ((Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).1 hdvd)
    · omega
  obtain ⟨e⟩ := nonempty_pSimple_JH_equiv hp hp2 hμ hF
  exact ⟨Q, rfl, Or.inl ⟨.lie ⟨.A 2 Q, hv⟩, rfl,
    ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).symm⟩⟩,
    fun h3 => center_pQuot_JH_ne_bot hp hp2 hμ hF h3⟩

end CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
