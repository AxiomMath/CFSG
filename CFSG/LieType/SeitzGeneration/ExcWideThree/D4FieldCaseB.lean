module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCaseA
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Orders
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Fixed
public import CFSG.RankThree.PartOne.SEITZ6.G2Big

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section CaseB


theorem eq_T_or_sq_of_cube {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (hef : e * 3 = f) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    σ = T ∨ σ = T ^ 2 := by
  obtain ⟨d, T', hd0, hdf, hT', -, hσT'⟩ :=
    exists_frobenius_of_cube (Fact.out : ℓ.Prime) hf K hK σ hσ3 hσ1
  have hde : d = e := by omega
  have hTT : T' = T := RingEquiv.ext fun c => by rw [hT', hT, hde]
  rwa [hTT] at hσT'

theorem eq_or_sq_of_mem_powers {K : Type} [Field K] {T σ σ₁ : K ≃+* K} (hT3 : T ^ 3 = 1)
    (hσ : σ = T ∨ σ = T ^ 2) (hσ₁ : σ₁ = T ∨ σ₁ = T ^ 2) : σ₁ = σ ∨ σ₁ = σ ^ 2 := by
  have hT4 : T ^ 4 = T := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hT3, one_mul]
  have hTT : (T ^ 2) ^ 2 = T := by rw [← pow_mul]; exact hT4
  rcases hσ with rfl | rfl <;> rcases hσ₁ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr hTT.symm
  · exact Or.inl rfl

theorem card_fixSubfield_eq_pow {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (hef : e * 3 = f) (T : K ≃+* K) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) :
    Nat.card (fixSubfield T) = ℓ ^ e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  have h := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow T
  rw [hord, hK, ← hef, pow_mul] at h
  exact (Nat.pow_left_injective (by norm_num : 3 ≠ 0) h).symm

theorem maximal_fixedSubgroup_of_conj {P : Type*} [Group P] {R : Subgroup P}
    (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤) {α ψ : MulAut P}
    (hF : fixedSubgroup (ψ * α * ψ⁻¹) = R) :
    ∀ M : Subgroup P, fixedSubgroup α ≤ M → M = fixedSubgroup α ∨ M = ⊤ := by
  rw [fixedSubgroup_conj] at hF
  intro M hM
  have hle : R ≤ M.map ψ.toMonoidHom := by
    rw [← hF]
    exact Subgroup.map_mono hM
  have hMeq : M = (M.map ψ.toMonoidHom).comap ψ.toMonoidHom :=
    (Subgroup.comap_map_eq_self_of_injective ψ.injective M).symm
  rcases hmax _ hle with h | h
  · left
    rw [hMeq, h, ← hF]
    exact Subgroup.comap_map_eq_self_of_injective ψ.injective _
  · right
    rw [hMeq, h]
    exact Subgroup.comap_top _

theorem card_fixedSubgroup_conj_ctp {P : Type*} [Group P] (ψ α : MulAut P) :
    Nat.card (fixedSubgroup (ψ * α * ψ⁻¹)) = Nat.card (fixedSubgroup α) := by
  rw [fixedSubgroup_conj]
  exact Subgroup.card_map_of_injective ψ.injective

theorem fixedCommutingProduct_fixedSubgroup_eq {P : Type*} [Group P] (α : MulAut P) :
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α = fixedSubgroup α :=
  Subgroup.ext fun _ => Iff.rfl

theorem order_dvd_card_fixedSubgroup_of_normalForm_orient {ℓ f e : ℕ} [Fact ℓ.Prime] (K : Type)
    [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K)
    (he : 1 ≤ e) (hef : e * 3 = f) (T σ : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (hσ : σ = T ∨ σ = T⁻¹) (β : MulAut (adjointGroup Tag.D4 K)) (hβ3 : β ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (hβ : β = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    (ℓ ^ e) ^ 12 * ((ℓ ^ e) ^ 2 - 1) * ((ℓ ^ e) ^ 6 - 1) * ((ℓ ^ e) ^ 8 + (ℓ ^ e) ^ 4 + 1) ∣
      Nat.card (fixedSubgroup β) := by
  rw [← fixedCommutingProduct_fixedSubgroup_eq]
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  rcases hσ with rfl | rfl
  · obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef σ hT β hβ3
      g a ε hβ
    rw [← card_fixedSubgroup_of_conj_eq_mul hψ]
    exact order_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 (Fact.out : ℓ.Prime) he K hK' σ hT
      (ε : ℤ) (by rcases hε with rfl | rfl <;> simp)
  · obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) β hβ3 g a ε hβ
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    rw [hshift] at hψ
    rw [← fixedSubgroup_inv_eq, ← card_fixedSubgroup_of_conj_eq_mul hψ]
    exact order_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 (Fact.out : ℓ.Prime) he K hK' T hT
      (3 - (ε : ℤ)) (by rcases hε with rfl | rfl <;> simp)

theorem exists_graphField_D4 {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (hef : e * 3 = f) (T σ : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hT3 : T ^ 3 = 1) (hσ : σ = T ∨ σ = T ^ 2)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) {α : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hα : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0)
    (hB : ∀ ι ∈ E, ∀ (g' : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ),
      ι = MulAut.conj g' * rootDiagAut Tag.D4 K b → ι = 1) :
    ∃ β ∈ E, β ∉ Subgroup.zpowers α ∧ ∃ (g' : adjointGroup Tag.D4 K)
      (b : Fin Tag.D4.rank → Kˣ) (σ' : K ≃+* K) (ε : ℕ), (ε = 1 ∨ ε = 2) ∧
        (σ' = T ∨ σ' = T ^ 2) ∧
        β = MulAut.conj g' * (exactNormalAut Tag.D4 K b σ' 0 * d4Graph K ε) := by
  classical
  have hσ3 : σ ^ 3 = 1 := by
    rcases hσ with rfl | rfl
    · exact hT3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hT3, one_pow]
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  obtain ⟨β₀, hβ₀E, hβ₀α⟩ : ∃ β₀ ∈ E, β₀ ∉ Subgroup.zpowers α := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers α := fun x hx => h x hx
    have h1 : Nat.card E ∣ Nat.card (Subgroup.zpowers α) := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hEc] at h1
    have h2 := h1.trans (orderOf_dvd_of_pow_eq_one hα3)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    norm_num at h3
  have hβ₀3 : β₀ ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β₀ hβ₀E
  by_cases hin : β₀ ∈ inner (adjointGroup Tag.D4 K)
  · exfalso
    obtain ⟨h, rfl⟩ := hin
    have h1 : MulAut.conj h = MulAut.conj h * rootDiagAut Tag.D4 K 1 := by
      rw [show rootDiagAut Tag.D4 K 1 = 1 from map_one (rootDiagAutHom Tag.D4 K), mul_one]
    exact hβ₀α (by rw [hB _ hβ₀E h 1 h1]; exact one_mem _)
  obtain ⟨g₁, a₁, σ₁, ε₁, hε₁, hβ₀eq, hσ₁3, hcase⟩ := outer_cube_normal_form_cases β₀ hβ₀3 hin
  rcases hcase with ⟨hε0, hσ₁1⟩ | ⟨hε0, hσ₁1⟩ | ⟨hε0, hσ₁⟩
  ·
    exfalso
    subst hε0
    rw [d4Graph_zero, mul_one] at hβ₀eq
    have hσ₁T := eq_T_or_sq_of_cube hK hf hef T hT σ₁ hσ₁3 hσ₁1
    rcases eq_or_sq_of_mem_powers hT3 hσ hσ₁T with hs | hs
    · obtain ⟨g₂, a₂, hα2⟩ := sq_conj_mul_exactNormalAut g a σ
      rw [← hα] at hα2
      obtain ⟨g₃, a₃, hprod⟩ := normalForm_mul g₁ g₂ a₁ a₂ σ₁ (σ ^ 2) 0
      simp only [d4Graph_zero, mul_one] at hprod
      rw [← hβ₀eq, ← hα2] at hprod
      have hsig : σ₁ * σ ^ 2 = 1 := by rw [hs, ← pow_succ']; exact hσ3
      rw [hsig, ← rootDiagAut_eq_normalAut] at hprod
      have h1 : β₀ * α ^ 2 = 1 := hB _ (E.mul_mem hβ₀E (E.pow_mem hαE 2)) g₃ a₃ hprod
      apply hβ₀α
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers α) 2)
    · obtain ⟨g₃, a₃, hprod⟩ := normalForm_mul g₁ g a₁ a σ₁ σ 0
      simp only [d4Graph_zero, mul_one] at hprod
      rw [← hβ₀eq, ← hα] at hprod
      have hsig : σ₁ * σ = 1 := by rw [hs, ← pow_succ]; exact hσ3
      rw [hsig, ← rootDiagAut_eq_normalAut] at hprod
      have h1 : β₀ * α = 1 := hB _ (E.mul_mem hβ₀E hαE) g₃ a₃ hprod
      apply hβ₀α
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers α)
  ·
    exact ⟨β₀, hβ₀E, hβ₀α, g₁, a₁, σ₁, ε₁, by omega,
      eq_T_or_sq_of_cube hK hf hef T hT σ₁ hσ₁3 hσ₁1, hβ₀eq⟩
  ·
    subst hσ₁
    obtain ⟨g₃, a₃, hprod⟩ := normalForm_mul g g₁ a a₁ σ 1 ε₁
    rw [mul_one, ← hβ₀eq, ← hα] at hprod
    refine ⟨α * β₀, E.mul_mem hαE hβ₀E, ?_, g₃, a₃, σ, ε₁, by omega, hσ, hprod⟩
    intro h
    apply hβ₀α
    have h2 : β₀ = α⁻¹ * (α * β₀) := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers α)) h

theorem d4_caseB {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f)
    (T σ : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hσ : σ = T ∨ σ = T ^ 2)
    (hmax : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), subfieldGroup Tag.D4 T ≤ M →
      M = subfieldGroup Tag.D4 T ∨ M = ⊤)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) {α : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hα : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0)
    (hB : ∀ ι ∈ E, ∀ (g' : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ),
      ι = MulAut.conj g' * rootDiagAut Tag.D4 K b → ι = 1) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  have hf : 1 ≤ f := by omega
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  set L := AlgebraicClosure K
  obtain ⟨ψa, -, hFa⟩ :=
    exists_conj_fixedSubgroup_D4_field hK hK4 he hef T σ hT hT3 hσ L g a α hα hα3
  have hmaxα := maximal_fixedSubgroup_of_conj hmax hFa
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [fixedSubgroup_conj_one] at hFa
    exact subfieldGroup_ne_top_D4 hT1 hFa.symm
  obtain ⟨β, hβE, hβα, g', b, σ', ε, hε, hσ', hβ⟩ :=
    exists_graphField_D4 hK hf hef T σ hT hT3 hσ hEc hαE g a hα hB
  have hβ1 : β ≠ 1 := fun h => hβα (h ▸ one_mem _)
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  have hσ'inv : σ' = T ∨ σ' = T⁻¹ := by
    rcases hσ' with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)).symm)
  have hdvd := order_dvd_card_fixedSubgroup_of_normalForm_orient K hK hK4 he hef T σ' hT hσ'inv β
    hβ3 g' b ε hε hβ
  have hq0 : Nat.card (fixSubfield T) = ℓ ^ e := card_fixSubfield_eq_pow hK hef T hT3 hT1
  have hq2 : 2 ≤ ℓ ^ e :=
    (Fact.out : ℓ.Prime).two_le.trans (Nat.le_self_pow (by omega) ℓ)
  obtain ⟨r, hr, hr8, hrC⟩ :=
    exists_prime_dvd_pow_eight_add_not_dvd_card_D4 (K := fixSubfield T) (by rw [hq0]; exact hq2)
  rw [hq0] at hr8
  refine closure_fixUnion_eq_top_of_maximal_escape hαE hα1 hβE hβ1 hmaxα ?_
  intro hle
  have h1 : Nat.card (fixedSubgroup β) ∣ Nat.card (fixedSubgroup α) := Subgroup.card_dvd_of_le hle
  have h2 : r ∣ Nat.card (fixedSubgroup β) := (Dvd.dvd.mul_left hr8 _).trans hdvd
  have h3 : Nat.card (fixedSubgroup α) = Nat.card (adjointGroup Tag.D4 (fixSubfield T)) := by
    rw [← card_fixedSubgroup_conj_ctp ψa α, hFa]
    exact card_subfieldGroup_D4 T hT3
  exact hrC (h3 ▸ h2.trans h1)

end CaseB

end CFSG.LieType.SeitzGeneration.ExcWideThree
