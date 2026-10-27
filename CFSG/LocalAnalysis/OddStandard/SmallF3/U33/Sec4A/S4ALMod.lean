module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AFour6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxSteps

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

section Quotient

variable {G : Type} [Group G] [Finite G]

theorem prime_mul_card_dvd_card {B M : Subgroup G} (hBM : B ≤ M)
    (hN : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B) {p : ℕ} (hp : p.Prime) {r : G}
    (hr : r ∈ M) (hrB : r ∉ B) (hrp : r ^ p ∈ B) : p * Nat.card B ∣ Nat.card M := by
  classical
  haveI hnorm : (B.subgroupOf M).Normal :=
    ⟨fun n hn m => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN m m.2 n hn⟩
  have hq1 : (QuotientGroup.mk (⟨r, hr⟩ : ↥M) : ↥M ⧸ B.subgroupOf M) ≠ 1 := by
    intro h1
    exact hrB (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨r, hr⟩ : ↥M)).mp h1))
  have hqp : (QuotientGroup.mk (⟨r, hr⟩ : ↥M) : ↥M ⧸ B.subgroupOf M) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hrp
  have hord : orderOf (QuotientGroup.mk (⟨r, hr⟩ : ↥M) : ↥M ⧸ B.subgroupOf M) = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hqp) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hq1
    · exact h1
  have h1 : p ∣ Nat.card (↥M ⧸ B.subgroupOf M) := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf M)
  have h3 : Nat.card (B.subgroupOf M) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  rw [h2, h3]
  exact mul_dvd_mul_right h1 _

end Quotient

section Model

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem ctx_lmodel_of (h : Ctx0 t L S x₁ x₂ lam rho) : CtxLModelFacts L x₁ x₂ lam rho := by
  obtain ⟨hx₁L, hx₂L, hlamL⟩ := generators_mem_L h
  obtain ⟨hAbel, -, hBcard⟩ := h.wreath.baseGrp_eq
  obtain ⟨hEeq, hEelem, hEcard⟩ := h.wreath.fourGrp_eq_omega
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hBL : baseGrp x₁ x₂ ≤ L := by
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact hx₁L
    · rw [hg]
      exact hx₂L
  have hyE : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzE : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hEB : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
    rw [hEeq]
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr fun a ha => ha.1
  have hcentE : ∀ k ∈ L ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G),
      k ∈ baseGrp x₁ x₂ := by
    rintro k ⟨hkL, hkC⟩
    have hc := Subgroup.mem_centralizer_iff.mp hkC
    exact cent_fourGrp_of_ctx0 h k hkL (hc _ hyE).symm (hc _ hzE).symm
  have hcent : L ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = baseGrp x₁ x₂ := by
    apply le_antisymm
    · intro k hk
      obtain ⟨hkL, hkC⟩ := Subgroup.mem_inf.mp hk
      refine hcentE k (Subgroup.mem_inf.mpr ⟨hkL, ?_⟩)
      rw [Subgroup.mem_centralizer_iff] at hkC ⊢
      intro e he
      exact hkC e (hEB he)
    · intro b hb
      refine Subgroup.mem_inf.mpr ⟨hBL hb, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      haveI : IsMulCommutative (baseGrp x₁ x₂) := hAbel
      exact congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : baseGrp x₁ x₂) ⟨b, hb⟩)
  refine ⟨hcent, ?_⟩
  have hlamsq : lam * lam = 1 := by
    have := pow_orderOf_eq_one lam
    rw [h.wreath.ord_lam, pow_two] at this
    exact this
  have hlam2 : lam * x₂ * lam⁻¹ = x₁ := by
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
      _ = x₁ := by rw [hlamsq]; group
  have hlamB : ∀ w ∈ baseGrp x₁ x₂, lam * w * lam⁻¹ ∈ baseGrp x₁ x₂ := by
    intro w hw
    have hle : baseGrp x₁ x₂ ≤ (baseGrp x₁ x₂).comap (MulAut.conj lam).toMonoidHom := by
      refine (Subgroup.closure_le
        (K := (baseGrp x₁ x₂).comap (MulAut.conj lam).toMonoidHom)).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg]
        show lam * x₁ * lam⁻¹ ∈ baseGrp x₁ x₂
        rw [h.wreath.conj_x₁]
        exact hx₂B
      · rw [hg]
        show lam * x₂ * lam⁻¹ ∈ baseGrp x₁ x₂
        rw [hlam2]
        exact hx₁B
    exact Subgroup.mem_comap.mp (hle hw)
  have hrhoN : rho ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right (ctxW t x₁ x₂) (zpowers rho)
      (Subgroup.mem_zpowers rho)
    rwa [h.comm_rho] at this
  have hrhoL : rho ∈ L := h.rho_mem
  have hML : closure {x₁, x₂, rho, lam} ≤ L := by
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      exact hx₁L
    · rw [hg]
      exact hx₂L
    · rw [hg]
      exact hrhoL
    · rw [hg]
      exact hlamL
  have hMN : closure {x₁, x₂, rho, lam} ≤
      normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    refine (Subgroup.closure_le (K := normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      exact Subgroup.le_normalizer hx₁B
    · rw [hg]
      exact Subgroup.le_normalizer hx₂B
    · rw [hg]
      exact hrhoN
    · rw [hg]
      exact mem_normalizer_of_conj_mem hlamB
  have hKE : ∀ k ∈ L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G),
      ∀ e ∈ fourGrp x₁ x₂, k * e * k⁻¹ ∈ fourGrp x₁ x₂ := by
    rintro k ⟨-, hkN⟩ e he
    have heB : e ∈ baseGrp x₁ x₂ := hEB he
    have hkB : k * e * k⁻¹ ∈ baseGrp x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hkN e).mp heB
    have hsq : (k * e * k⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hEelem.2 e he]
      group
    rw [hEeq]
    exact Subgroup.subset_closure ⟨hkB, hsq⟩
  have h6 := card_le_six_mul_card_inf_centralizer hEcard hKE
  have hKC : (L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G)) ⊓
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) ≤ baseGrp x₁ x₂ := by
    rintro k ⟨⟨hkL, -⟩, hkC⟩
    exact hcentE k ⟨hkL, hkC⟩
  have h16 : Nat.card ↥((L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G)) ⊓
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) ≤ 16 := by
    rw [← hBcard]
    exact Subgroup.card_le_of_le hKC
  have hK96 : Nat.card ↥(L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G)) ≤ 96 := by
    omega
  have hBM : baseGrp x₁ x₂ ≤ closure {x₁, x₂, rho, lam} := by
    refine (Subgroup.closure_le (K := closure {x₁, x₂, rho, lam})).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
  have hMnorm : ∀ m ∈ closure {x₁, x₂, rho, lam}, ∀ b ∈ baseGrp x₁ x₂,
      m * b * m⁻¹ ∈ baseGrp x₁ x₂ := fun m hm b hb =>
    (Subgroup.mem_normalizer_iff.mp (hMN hm) b).mp hb
  have hrhoM : rho ∈ closure {x₁, x₂, rho, lam} := Subgroup.subset_closure (by simp)
  have hlamM : lam ∈ closure {x₁, x₂, rho, lam} := Subgroup.subset_closure (by simp)
  have hrhoB : rho ∉ baseGrp x₁ x₂ := by
    intro hr
    have h3 := orderOf_dvd_natCard (⟨rho, hr⟩ : ↥(baseGrp x₁ x₂))
    rw [Subgroup.orderOf_mk, h.ord_rho, hBcard] at h3
    omega
  have hlamB' : lam ∉ baseGrp x₁ x₂ := by
    intro hl
    have hc : lam * x₁ = x₁ * lam := by
      haveI : IsMulCommutative (baseGrp x₁ x₂) := hAbel
      exact congrArg Subtype.val (mul_comm' (⟨lam, hl⟩ : baseGrp x₁ x₂) ⟨x₁, hx₁B⟩)
    have h21 : x₂ = x₁ := by
      rw [← h.wreath.conj_x₁, hc]
      group
    have h12 : x₁ ∈ zpowers x₂ := by
      rw [h21]
      exact Subgroup.mem_zpowers x₁
    have hx1 : x₁ ∈ zpowers x₁ ⊓ zpowers x₂ := ⟨Subgroup.mem_zpowers x₁, h12⟩
    rw [h.wreath.inf_eq_bot, Subgroup.mem_bot] at hx1
    have h4 := h.wreath.ord_x₁
    rw [hx1, orderOf_one] at h4
    omega
  have h48 : 3 * Nat.card (baseGrp x₁ x₂) ∣ Nat.card (closure {x₁, x₂, rho, lam}) := by
    refine prime_mul_card_dvd_card hBM hMnorm Nat.prime_three hrhoM hrhoB ?_
    have := pow_orderOf_eq_one rho
    rw [h.ord_rho] at this
    rw [this]
    exact one_mem _
  have h32 : 2 * Nat.card (baseGrp x₁ x₂) ∣ Nat.card (closure {x₁, x₂, rho, lam}) := by
    refine prime_mul_card_dvd_card hBM hMnorm Nat.prime_two hlamM hlamB' ?_
    have := pow_orderOf_eq_one lam
    rw [h.wreath.ord_lam] at this
    rw [this]
    exact one_mem _
  have h48' : 48 ∣ Nat.card (closure {x₁, x₂, rho, lam}) :=
    dvd_trans (by rw [hBcard]) h48
  have h32' : 32 ∣ Nat.card (closure {x₁, x₂, rho, lam}) :=
    dvd_trans (by rw [hBcard]) h32
  have h96 : 96 ∣ Nat.card (closure {x₁, x₂, rho, lam}) := by omega
  have hMK : closure {x₁, x₂, rho, lam} ≤
      L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := le_inf hML hMN
  have h96le : 96 ≤ Nat.card (closure {x₁, x₂, rho, lam}) :=
    Nat.le_of_dvd Nat.card_pos h96
  exact (Subgroup.eq_of_le_of_card_ge hMK (hK96.trans h96le)).symm

end Model

end S4A

theorem ctxLModel_holds : CtxLModelStmt :=
  fun h => S4A.ctx_lmodel_of h

end CFSG.OddStandard.SmallF3.HarrisU33
