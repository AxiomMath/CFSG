module

public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.Lemma13

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo


section Conj

variable {K : Type} [Group K]

theorem fixedSubgroup_eq_map_of_conj {y f a : MulAut K} (h : a * y * a⁻¹ = f) :
    fixedSubgroup K f = (fixedSubgroup K y).map (a : K ≃* K).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  show f x = x ↔ y (a.symm x) = a.symm x
  rw [← h]
  show a (y (a⁻¹ x)) = x ↔ _
  constructor
  · intro hx
    have := congrArg (fun z => a.symm z) hx
    simpa using this
  · intro hx
    have : a⁻¹ x = a.symm x := rfl
    rw [this, hx]
    simp

@[expose] noncomputable def fixedSubgroupEquivOfConj' {y f a : MulAut K} (h : a * y * a⁻¹ = f) :
    ↥(fixedSubgroup K y) ≃* ↥(fixedSubgroup K f) :=
  ((a : K ≃* K).subgroupMap (fixedSubgroup K y)).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_eq_map_of_conj h).symm)

theorem fixedSubgroup_conj_eq_centralizer (u : K) :
    fixedSubgroup K (MulAut.conj u) = centralizer ({u} : Set K) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  show MulAut.conj u x = x ↔ x * u = u * x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    have := congrArg (fun z => z * u) h
    simpa [mul_assoc] using this.symm
  · intro h
    rw [← h]; group

end Conj

theorem card_of_isDihedralOrder {Y : Type} [Group Y] {d : ℕ} (h : IsDihedralOrder Y d) :
    Nat.card Y = d := by
  obtain ⟨k, hd, hk, ⟨e⟩⟩ := h
  have : NeZero k := ⟨by omega⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card, hd]

theorem exists_eps_d (q : ℕ) (hq : Odd q) (hq3 : 3 < q) :
    ∃ (d₁ d₂ : ℕ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] ∧ (d₁ : ℤ) = q - ε ∧
      (d₂ : ℤ) = q + ε ∧ (d₁ + 1 = q ∨ d₁ = q + 1) ∧ (d₂ + 1 = q ∨ d₂ = q + 1) := by
  have h2 : q % 2 = 1 := Nat.odd_iff.mp hq
  have h4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases h4 with h | h
  · refine ⟨q - 1, q + 1, 1, Or.inl rfl, ?_, ?_, ?_, Or.inl (by omega), Or.inr rfl⟩
    · unfold Int.ModEq; omega
    · omega
    · omega
  · refine ⟨q + 1, q - 1, -1, Or.inr rfl, ?_, ?_, ?_, Or.inr rfl, Or.inl (by omega)⟩
    · unfold Int.ModEq; omega
    · omega
    · omega

section Classify

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

@[expose] noncomputable def pgammaAut (e : K ≃* L2 F) : PGammaL2 F ≃* MulAut K :=
  (semilinearEquivAut F).trans (MulAut.congr (toPSL e)).symm

omit [Finite K] in
theorem pgammaAut_inl (e : K ≃* L2 F) (g : PGL2 F) :
    pgammaAut e (SemidirectProduct.inl g) = innDiagHom e g := by
  rw [innDiagHom_apply']
  show (MulAut.congr (toPSL e)).symm (semilinearEquivAut F (SemidirectProduct.inl g)) = _
  rw [semilinearEquivAut_inl]

omit [Finite K] in
theorem pgammaAut_inr (e : K ≃* L2 F) (σ : F ≃+* F) :
    pgammaAut e (SemidirectProduct.inr σ) = fieldAutHom e σ := by
  rw [fieldAutHom_apply']
  show (MulAut.congr (toPSL e)).symm (semilinearEquivAut F (SemidirectProduct.inr σ)) = _
  rw [semilinearEquivAut_inr]



theorem fixedSubgroup_classify (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hα1 : α ≠ 1) :
    (∃ d : ℕ, Nat.card ↥(fixedSubgroup K α) = d ∧ (d + 1 = Nat.card F ∨ d = Nat.card F + 1)) ∨
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ * Nat.card F₀ = Nat.card F ∧
      Nonempty (↥(fixedSubgroup K α) ≃* PGL2 F₀) := by
  classical
  set x : PGammaL2 F := (pgammaAut e).symm α with hx
  have hΦx : pgammaAut e x = α := by simp [hx]
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) hα1
  have hord : orderOf x = 2 := by
    have h := MulEquiv.orderOf_eq (pgammaAut e) x
    rw [hΦx, hα2] at h
    exact h.symm
  obtain ⟨d₁, d₂, ε, hε, hmod, hd₁, hd₂, hd₁'', hd₂''⟩ := exists_eps_d (Nat.card F) hF.1 hF.2
  by_cases hσ : x.right = 1
  · left
    obtain ⟨g, hg⟩ : ∃ g, x = SemidirectProduct.inl g :=
      ⟨x.left, SemidirectProduct.ext (by simp) (by simpa using hσ)⟩
    rw [hg, pgammaAut_inl] at hΦx
    have hαD : α ∈ innDiagSub e := ⟨g, hΦx⟩
    by_cases hin : α ∈ innAut K
    · obtain ⟨u, hu⟩ := hin
      have hu2 : u * u = 1 := by
        have h1 : MulAut.conj (u * u) = (1 : MulAut K) := by rw [map_mul, hu]; exact hα
        exact (conj_injective_of_L2 e) (h1.trans (map_one _).symm)
      have hu1 : u ≠ 1 := by
        rintro rfl
        exact hα1 (by rw [← hu]; simp)
      have hordu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
      have hdih := (ivk_1_3a F hF K e ε hε hmod d₁ hd₁ u hordu).2.1
      refine ⟨d₁, ?_, hd₁''⟩
      rw [← hu, fixedSubgroup_conj_eq_centralizer]
      exact card_of_isDihedralOrder hdih
    · have hαo : orderOf α = 2 := hα2
      have hdih := (ivk_1_3b F hF K e ε hε hmod d₂ hd₂ α hαD hin hαo).2.1
      exact ⟨d₂, card_of_isDihedralOrder hdih, hd₂''⟩
  · right
    set σ : F ≃+* F := x.right with hσdef
    have hσ2 : orderOf σ = 2 := by
      have hdvd : orderOf σ ∣ orderOf x := orderOf_map_dvd (SemidirectProduct.rightHom) x
      rw [hord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hσ
      · exact h
    obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr x hord hσ
    have hαconj : (innDiagHom e C)⁻¹ * α * (innDiagHom e C)⁻¹⁻¹ = fieldAutHom e σ := by
      rw [inv_inv, ← hΦx, ← pgammaAut_inl, ← pgammaAut_inr, ← map_inv, ← map_mul, ← map_mul, hC]
    obtain ⟨F₀, _, _, hq₀, ⟨eP⟩⟩ := isPGL2_fixedSubgroup e σ ⟨1, by rw [hσ2]⟩
    rw [hσ2] at hq₀
    exact ⟨F₀, inferInstance, inferInstance, by rw [← hq₀]; ring,
      ⟨(fixedSubgroupEquivOfConj' hαconj).trans eP⟩⟩

omit [Finite K] in
theorem ringChar_dvd_card (F : Type) [Field F] [Finite F] : ringChar F ∣ Nat.card F := by
  have := Fintype.ofFinite F
  have hc : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self _ n.ne_zero

theorem fixedSubgroup_card_ge (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hα1 : α ≠ 1) : Nat.card F - 1 ≤ Nat.card ↥(fixedSubgroup K α) := by
  rcases fixedSubgroup_classify hF e α hα hα1 with ⟨d, hd, hd'⟩ | ⟨F₀, _, _, hq₀, ⟨eP⟩⟩
  · rw [hd]; omega
  · rw [Nat.card_congr eP.toEquiv, pgl2_card_formula, ← hq₀]
    have hpos : 0 < Nat.card F₀ := Nat.card_pos
    have hsq : Nat.card F₀ * Nat.card F₀ = Nat.card F₀ ^ 2 := (sq _).symm
    rw [hsq]
    exact Nat.le_mul_of_pos_left _ hpos

theorem fixedSubgroup_coprime_or_pgl (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K)
    (hα : α * α = 1) (hα1 : α ≠ 1) :
    ¬ ringChar F ∣ Nat.card ↥(fixedSubgroup K α) ∨
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), 3 ≤ Nat.card F₀ ∧
      Nat.card F₀ * Nat.card F₀ = Nat.card F ∧ Nonempty (↥(fixedSubgroup K α) ≃* PGL2 F₀) := by
  rcases fixedSubgroup_classify hF e α hα hα1 with ⟨d, hd, hd'⟩ | ⟨F₀, _, _, hq₀, hP⟩
  · left
    rw [hd]
    intro hdvd
    have hq := ringChar_dvd_card F
    have hp : (ringChar F).Prime := by
      have := Fintype.ofFinite F
      have hc : CharP F (ringChar F) := ringChar.charP F
      exact CharP.char_is_prime F _
    rcases hd' with h | h
    · have : ringChar F ∣ 1 := by
        have h2 : ringChar F ∣ d + 1 := h ▸ hq
        exact (Nat.dvd_add_right hdvd).mp h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · have : ringChar F ∣ 1 := by
        have h2 : ringChar F ∣ d := hdvd
        rw [h] at h2
        exact (Nat.dvd_add_right hq).mp h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · right
    refine ⟨F₀, inferInstance, inferInstance, ?_, hq₀, hP⟩
    have h3 := hF.2
    have hpos : 0 < Nat.card F₀ := Nat.card_pos
    by_contra hlt
    have hlt' : Nat.card F₀ ≤ 2 := by omega
    have h4 : Nat.card F ≤ 2 * 2 := by rw [← hq₀]; exact Nat.mul_le_mul hlt' hlt'
    obtain ⟨k, hk⟩ := hF.1
    omega

end Classify

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
