module

public import CFSG.RankThree.PartOne.SEITZ6.G2Close

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6
open scoped commutatorElement

variable {K : Type} [Field K]

theorem weylElement_conj_xp_sign (i : Fin (Tag.rank .G2)) {p q : ℕ} (hp : p < 12)
    (h : reflect .G2 i (rt p) = rt q) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      weylElement .G2 K i * xp p c * (weylElement .G2 K i)⁻¹ = xp q (ε * c) := by
  have hγ : IsRoot .G2 (rt p) := isRoot_rt hp
  have hq : IsRoot .G2 (rt q) := h ▸ IsRoot.reflect i hγ
  have e : simple .G2 i • (⟨rt p, hγ⟩ : Root .G2) = ⟨rt q, hq⟩ := by
    rw [simple_smul_eq_sRoot]
    exact Subtype.ext h
  refine ⟨(((rootOperatorFamily .G2).sign i ⟨rt p, hγ⟩ : ℤ) : K), ?_, fun c => ?_⟩
  · rcases (rootOperatorFamily .G2).sign_eq i ⟨rt p, hγ⟩ with h1 | h1 <;> rw [h1] <;> simp
  · have hF := (rootOperatorFamily .G2).weylElement_mul_eltElement_mul_inv (K := K) i
      ⟨rt p, hγ⟩ c
    rw [e] at hF
    simpa [xp, xPar_of_isRoot hγ, xPar_of_isRoot hq] using hF

theorem full_conj_sign {H : Subgroup (adjointGroup .G2 K)} (i : Fin (Tag.rank .G2))
    {p q : ℕ} (hp : p < 12) (h : reflect .G2 i (rt p) = rt q)
    (hw : weylElement .G2 K i ∈ H) (hF : Full H p) : Full H q := fun c => by
  obtain ⟨ε, hε, he⟩ := weylElement_conj_xp_sign (K := K) i hp h
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have := H.mul_mem (H.mul_mem hw (hF (ε⁻¹ * c))) (H.inv_mem hw)
  rwa [he, mul_inv_cancel_left₀ hε0] at this

theorem comm_xp_11_7_gen (s t : K) :
    ⁅xp 11 s, xp 7 t⁆ = xp 4 (-(s * t)) * xp 5 (-(s ^ 2 * t)) * xp 6 (-(s ^ 3 * t)) *
      xp 0 (-2 * (s ^ 3 * t ^ 2)) := by
  have h : RootOps.repCheck .G2 11 7 [(1, 1, 4, -1), (2, 1, 5, -1), (3, 1, 6, -1), (3, 2, 0, -2)] =
      true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  show _ = _
  rw [this]
  have e1 : ((-1 : ℤ) : K) * s ^ 1 * t ^ 1 = -(s * t) := by push_cast; ring
  have e2 : ((-1 : ℤ) : K) * s ^ 2 * t ^ 1 = -(s ^ 2 * t) := by push_cast; ring
  have e3 : ((-1 : ℤ) : K) * s ^ 3 * t ^ 1 = -(s ^ 3 * t) := by push_cast; ring
  have e4 : ((-2 : ℤ) : K) * s ^ 3 * t ^ 2 = -2 * (s ^ 3 * t ^ 2) := by push_cast; ring
  rw [e1, e2, e3, e4, mul_assoc, mul_assoc]

theorem xp_inv_gen (p : ℕ) (c : K) : (xp p c)⁻¹ = xp p (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [← xp_add, add_neg_cancel, xp_zero])

theorem full_five_of_long_gen {H : Subgroup (adjointGroup .G2 K)}
    (h0 : Full H 0) (h6 : Full H 6) (h7 : Full H 7) (h11 : xp 11 (1 : K) ∈ H)
    {τ : adjointGroup .G2 K} (hτ : τ ∈ H) {a₁ a₂ : K} (h12 : a₁ ≠ a₂)
    (ha₁ : ∀ c, τ * xp 4 c * τ⁻¹ = xp 4 (a₁ * c))
    (ha₂ : ∀ c, τ * xp 5 c * τ⁻¹ = xp 5 (a₂ * c)) : Full H 5 := by
  have hz : ∀ t : K, xp 4 t * xp 5 t ∈ H := fun t => by
    have hy : ⁅xp 11 (1 : K), xp 7 (-t)⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h11 (h7 _)) (H.inv_mem h11)) (H.inv_mem (h7 _))
    rw [comm_xp_11_7_gen] at hy
    simp only [one_mul, one_pow, neg_neg] at hy
    have h1 := H.mul_mem hy (H.inv_mem (h0 (-2 * (-t) ^ 2)))
    rw [mul_inv_cancel_right] at h1
    have h2 := H.mul_mem h1 (H.inv_mem (h6 t))
    rwa [mul_inv_cancel_right] at h2
  intro c
  have hs : a₂ - a₁ ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  set t := c / (a₂ - a₁)
  have key : xp 5 ((a₂ - a₁) * t) ∈ H := by
    have h1 := hz t
    have h2 := hz (a₁ * t)
    have h3 := H.mul_mem (H.inv_mem h2) (H.mul_mem (H.mul_mem hτ h1) (H.inv_mem hτ))
    have e : τ * (xp 4 t * xp 5 t) * τ⁻¹ = xp 4 (a₁ * t) * xp 5 (a₂ * t) := by
      rw [show τ * (xp 4 t * xp 5 t) * τ⁻¹ = (τ * xp 4 t * τ⁻¹) * (τ * xp 5 t * τ⁻¹) by group,
        ha₁, ha₂]
    rw [e] at h3
    have e2 : (xp 4 (a₁ * t) * xp 5 (a₁ * t))⁻¹ * (xp 4 (a₁ * t) * xp 5 (a₂ * t)) =
        xp 5 ((a₂ - a₁) * t) := by
      calc (xp 4 (a₁ * t) * xp 5 (a₁ * t))⁻¹ * (xp 4 (a₁ * t) * xp 5 (a₂ * t))
          = (xp 5 (a₁ * t))⁻¹ * ((xp 4 (a₁ * t))⁻¹ * xp 4 (a₁ * t)) * xp 5 (a₂ * t) := by group
        _ = xp 5 (-(a₁ * t)) * xp 5 (a₂ * t) := by rw [inv_mul_cancel, mul_one, xp_inv_gen]
        _ = xp 5 ((a₂ - a₁) * t) := by rw [← xp_add]; congr 1; ring
    rwa [e2] at h3
  rwa [show (a₂ - a₁) * t = c from mul_div_cancel₀ _ hs] at key

theorem eq_top_of_full_seven_of_weyl_gen
    {H : Subgroup (adjointGroup .G2 K)} (hw0 : weylElement .G2 K e0 ∈ H)
    (hw1 : weylElement .G2 K e1 ∈ H) (h7 : Full H 7) (h11 : xp 11 (1 : K) ∈ H)
    {τ : adjointGroup .G2 K} (hτ : τ ∈ H) {a₁ a₂ : K} (h12 : a₁ ≠ a₂)
    (ha₁ : ∀ c, τ * xp 4 c * τ⁻¹ = xp 4 (a₁ * c))
    (ha₂ : ∀ c, τ * xp 5 c * τ⁻¹ = xp 5 (a₂ * c)) : H = ⊤ := by
  have h3 : Full H 3 := full_conj_sign e0 (by norm_num) reflect_7 hw0 h7
  have h0 : Full H 0 := full_conj_sign e1 (by norm_num) reflect_3 hw1 h3
  have h2 : Full H 2 := full_conj_sign e0 (by norm_num) reflect_0 hw0 h0
  have h6 : Full H 6 := full_conj_sign e1 (by norm_num) reflect_2 hw1 h2
  have h5 : Full H 5 := full_five_of_long_gen h0 h6 h7 h11 hτ h12 ha₁ ha₂
  have h1 : Full H 1 := full_conj_sign e1 (by norm_num) reflect_5 hw1 h5
  exact eq_top_of_full h0 h1 h2 h5

theorem eq_top_of_subfield_gen (k : Subfield K) {t : K} (htk : t ∈ k)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) {H : Subgroup (adjointGroup .G2 K)}
    (hH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) (h7 : Full H 7) : H = ⊤ := by
  have hneg : ∀ {c : K}, c ∈ k → -c ∈ k := fun hc => k.neg_mem hc
  have hw0 : weylElement .G2 K e0 ∈ H := by
    rw [weylElement_e0_eq]
    exact H.mul_mem (H.mul_mem (hH 0 (by norm_num) 1 k.one_mem)
      (hH 2 (by norm_num) (-1) (hneg k.one_mem))) (hH 0 (by norm_num) 1 k.one_mem)
  have hw1 : weylElement .G2 K e1 ∈ H := by
    rw [weylElement_e1_eq]
    exact H.mul_mem (H.mul_mem (hH 1 (by norm_num) 1 k.one_mem)
      (hH 5 (by norm_num) (-1) (hneg k.one_mem))) (hH 1 (by norm_num) 1 k.one_mem)
  set u : Kˣ := Units.mk0 t ht0 with hu
  have hτ : torusElement .G2 K e1 u ∈ H := by
    rw [torusElement_e1_eq]
    refine H.mul_mem (H.mul_mem (H.mul_mem (hH 1 (by norm_num) _ htk)
      (hH 5 (by norm_num) _ (hneg ?_))) (hH 1 (by norm_num) _ htk)) (H.inv_mem hw1)
    simpa [hu] using k.inv_mem htk
  have ha₁ := fun c : K => torusElement_e1_conj_xp (K := K) (p := 4) (by norm_num) u c
  have ha₂ := fun c : K => torusElement_e1_conj_xp (K := K) (p := 5) (by norm_num) u c
  rw [cartan_e1_rt4] at ha₁
  rw [cartan_e1_rt5] at ha₂
  refine eq_top_of_full_seven_of_weyl_gen hw0 hw1 h7 (hH 11 (by norm_num) 1 k.one_mem) hτ
    (a₁ := ((u ^ (-1 : ℤ) : Kˣ) : K)) (a₂ := ((u ^ (-2 : ℤ) : Kˣ) : K)) ?_ ha₁ ha₂
  intro h
  have h' : u ^ (-1 : ℤ) = u ^ (-2 : ℤ) := Units.ext h
  have h'' : u = 1 := by
    have : u ^ (-1 : ℤ) * u ^ (-1 : ℤ) = u ^ (-1 : ℤ) * 1 := by
      rw [mul_one, ← zpow_add, show (-1 : ℤ) + -1 = -2 by norm_num, ← h']
    have := mul_left_cancel this
    simpa using this
  exact ht1 (by simpa [hu] using congrArg Units.val h'')

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
