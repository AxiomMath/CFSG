module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniComp
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
import CFSG.Adapters.CatalogueFieldBridges.UnitarySU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.UniA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
  CFSG.Yardstones.Md0ec50421ce4

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

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

private noncomputable def suCast [Finite K] [Fact ℓ.Prime] [CharP K ℓ] {a b : ℕ} (hab : a = b) :
    Su K ℓ f a ≃* Su K ℓ f b := by
  subst hab
  exact MulEquiv.refl _

noncomputable def juEquivStatedSU [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) : ↥(JU h) ≃* ↥(StatedSU 3 (ℓ ^ f) K) :=
  (mapProjUEquiv _ le_rfl).symm.trans
    ((MulEquiv.subgroupCongr (blockU_eq_map (h := h) blockJ)).trans
      ((Subgroup.equivMapOfInjective _ _ (suEquiv h).injective).symm.trans
        ((MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := ℓ) (f := f) blockJ)).symm.trans
          ((suCast (by decide)).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3))))))

section Root

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ} {μ : K} (hK : Nat.card K = (ℓ ^ f) ^ 2)
  (hq : 5 ≤ ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p) (hpq : p ∣ ℓ ^ f + 1)
include hK hq hp hp2 hμ hpq

theorem glaPPrimeCore_JU_le_center :
    GLAPPrimeCore p ↥(JU h) ≤ Subgroup.center ↥(JU h) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple
    (isQuasisimple_JU hp hp2 hμ hpq hK hq) (GLAPPrimeCore.normal p _) fun htop => ?_
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥(JU h))) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top] at hcop
  have hdvd : p ∣ Nat.card ↥(JU h) :=
    (dvd_card_JU hp hp2 hμ hpq hK hq).trans (Subgroup.card_quotient_dvd_card _)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

theorem nonempty_pSimple_JU_equiv :
    Nonempty (PSimple p (JU h) ≃*
      ↥(StatedSU 3 (ℓ ^ f) K) ⧸ Subgroup.center ↥(StatedSU 3 (ℓ ^ f) K)) := by
  obtain ⟨e₁⟩ := center_quot_equiv_of_surjective
    (isQuasisimple_JU hp hp2 hμ hpq hK hq).1 (QuotientGroup.mk' (GLAPPrimeCore p ↥(JU h)))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact glaPPrimeCore_JU_le_center hK hq hp hp2 hμ hpq)
  exact ⟨e₁.trans (QuotientGroup.congr _ _ (juEquivStatedSU hK) (Subgroup.map_center_eq _))⟩

omit hK hq in
private theorem prod_c3 (h3 : p = 3) : ∏ i, (![1, μ, μ, μ] : Fin 4 → K) i = 1 := by
  rw [Fin.prod_univ_four]
  show 1 * μ * μ * μ = 1
  rw [one_mul, ← pow_two, ← pow_succ]
  subst h3
  exact hμ.pow_eq_one

omit hK hq in
private theorem pow_c3 (h3 : p = 3) (i : Fin 4) : (![1, μ, μ, μ] : Fin 4 → K) i ^ p = 1 := by
  fin_cases i <;> simp [hμ.pow_eq_one]

theorem center_pQuot_JU_ne_bot (h3 : p = 3) :
    Subgroup.center (PQuot p (JU h)) ≠ ⊥ := by
  have hcp := prod_c3 hp hp2 hμ hpq h3
  have hcn := norm_of_pow (h := h) hpq (pow_c3 hp hp2 hμ hpq h3)
  have hcJ : ∀ i ∈ blockJ, ∀ j ∈ blockJ,
      (![1, μ, μ, μ] : Fin 4 → K) i = (![1, μ, μ, μ] : Fin 4 → K) j := by
    intro i hi j hj
    rw [mem_blockJ] at hi hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hc0 : diagU h ![1, μ, μ, μ] hcn hcp ∈ blockU h blockJ := diagU_mem_blockU fun i hi => by
    rw [mem_blockJ, not_not] at hi
    subst hi
    rfl
  set x : ↥(JU h) := ⟨projU h (diagU h ![1, μ, μ, μ] hcn hcp), Subgroup.mem_map_of_mem _ hc0⟩
    with hx
  have hxZ : x ∈ Subgroup.center ↥(JU h) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hx]
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1
      (blockU_le_centralizer hcJ hm))
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    simp only [hx, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, diagU_pow_eq_one (pow_c3 hp hp2 hμ hpq h3), map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 := congrArg Subtype.val h1
    simp only [hx, OneMemClass.coe_one] at h2
    have h3' := eq_one_of_mem_blockU_of_projU_eq_one hc0 h2
    have h4 := congrArg
      (fun g : ↥(SG h) => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1) h3'
    simp only [coe_diagU, diagonal_apply_eq, OneMemClass.coe_one, Units.val_one,
      one_apply_eq] at h4
    exact ne_one_of_root hp hp2 hμ h4
  haveI : Fact p.Prime := ⟨hp⟩
  intro hbot
  have hxim : (QuotientGroup.mk x : PQuot p (JU h)) ∈ Subgroup.center (PQuot p (JU h)) :=
    Subgroup.map_center_le_center (f := QuotientGroup.mk' (GLAPPrimeCore p ↥(JU h)))
      (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hxZ)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxim
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdvd : p ∣ Nat.card (GLAPPrimeCore p ↥(JU h)) := by
    have h1 : orderOf (⟨x, hxim⟩ : GLAPPrimeCore p ↥(JU h)) = p := by
      rw [Subgroup.orderOf_mk, hord]
    have h2 := orderOf_dvd_natCard (⟨x, hxim⟩ : GLAPPrimeCore p ↥(JU h))
    rwa [h1] at h2
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥(JU h))) := CFSG.pPrimeCore_coprime_card
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

theorem isSL3Type_JU : IsSL3Type p ℓ (JU h) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = (ℓ ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨q', hv, hq'p, -, ⟨e₂⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (m := 3) hKc le_rfl (by
        intro he
        have := congrArg Prod.snd he
        simp only at this
        omega)
  obtain ⟨e₁⟩ := nonempty_pSimple_JU_equiv hK hq hp hp2 hμ hpq
  refine ⟨q', by rw [hq'p, ringChar.eq K ℓ], Or.inr ⟨.lie ⟨.twistedA (3 - 1) q', hv⟩, rfl,
    ⟨e₁.trans e₂⟩⟩, fun h3 => center_pQuot_JU_ne_bot hK hq hp hp2 hμ hpq h3⟩

end Root

end CFSG.LocalAnalysis.GLTheoremA.H81.UniA3
