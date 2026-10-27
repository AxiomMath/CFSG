module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour
public import CFSG.ClassicalInvolution.AschTight.S1911P3b

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.ClassicalInvolution
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups commutatorElement

section SL2

variable {F : Type*} [Field F]

theorem sl2_sq_eq (A : SL(2, F)) :
    (A : Matrix (Fin 2) (Fin 2) F) * A =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) • (A : Matrix (Fin 2) (Fin 2) F) - 1 := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

theorem sl2_pow_twelve [Fintype F] (hF : Fintype.card F ≤ 3) (A : SL(2, F)) : A ^ 12 = 1 := by
  set M := (A : Matrix (Fin 2) (Fin 2) F) with hM
  set t := Matrix.trace M with ht
  have hsq := sl2_sq_eq A
  rw [← hM, ← ht] at hsq
  have hcard : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have ht3 : t ^ 3 = t := by
    have hp := FiniteField.pow_card t
    rcases (show Fintype.card F = 2 ∨ Fintype.card F = 3 by omega) with h | h
    · rw [h] at hp
      calc t ^ 3 = t ^ 2 * t := by ring
        _ = t * t := by rw [hp]
        _ = t ^ 2 := by ring
        _ = t := hp
    · rw [h] at hp
      exact hp
  have hcases : t = 0 ∨ t = 1 ∨ t = -1 := by
    have h0 : t * (t - 1) * (t + 1) = 0 := by linear_combination ht3
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))
  have hM12 : M ^ 12 = 1 := by
    rcases hcases with h | h | h
    · rw [h, zero_smul, zero_sub] at hsq
      have h4 : M ^ 4 = 1 := by
        calc M ^ 4 = (M * M) * (M * M) := by noncomm_ring
          _ = 1 := by rw [hsq]; noncomm_ring
      calc M ^ 12 = (M ^ 4) ^ 3 := by rw [← pow_mul]
        _ = 1 := by rw [h4, one_pow]
    · rw [h, one_smul] at hsq
      have h3 : M ^ 3 = -1 := by
        calc M ^ 3 = M * (M * M) := by noncomm_ring
          _ = M * (M - 1) := by rw [hsq]
          _ = M * M - M := by noncomm_ring
          _ = -1 := by rw [hsq]; noncomm_ring
      calc M ^ 12 = (M ^ 3) ^ 4 := by rw [← pow_mul]
        _ = 1 := by rw [h3]; noncomm_ring
    · rw [h, neg_smul, one_smul] at hsq
      have h3 : M ^ 3 = 1 := by
        calc M ^ 3 = M * (M * M) := by noncomm_ring
          _ = M * (-M - 1) := by rw [hsq]
          _ = -(M * M) - M := by noncomm_ring
          _ = 1 := by rw [hsq]; noncomm_ring
      calc M ^ 12 = (M ^ 3) ^ 4 := by rw [← pow_mul]
        _ = 1 := by rw [h3, one_pow]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact hM12

theorem sl2_comm_of_comm {x a b : SL(2, F)} (hx : x ∉ Subgroup.center SL(2, F))
    (ha : a * x = x * a) (hb : b * x = x * b) : a * b = b * a := by
  have hns : ¬ ∃ c : F, (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := by
    rintro ⟨c, hc⟩
    apply hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc]
    exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).symm
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine CFSG.ComponentClassification.CatalogueBLinearTwo.nonscalar_matrix_centralizer_commutative
    (x : Matrix (Fin 2) (Fin 2) F) _ _ hns ?_ ?_
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) ha
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this.symm
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hb
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this.symm

end SL2


section Act

variable {G : Type} [Group G] (H : Subgroup G)

theorem conj_mem_of_mem_normalizer {n : G} (hn : n ∈ Subgroup.normalizer (H : Set G)) {y : G}
    (hy : y ∈ H) : n * y * n⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hn y).mp hy

@[expose] noncomputable def normAut : ↥(Subgroup.normalizer (H : Set G)) →* MulAut ↥H where
  toFun n :=
    { toFun := fun y => ⟨(n : G) * y * (n : G)⁻¹, conj_mem_of_mem_normalizer H n.2 y.2⟩
      invFun := fun y => ⟨(n : G)⁻¹ * y * (n : G), by
        have := conj_mem_of_mem_normalizer H (Subgroup.inv_mem _ n.2) y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext y
    simp
  map_mul' := fun a b => by
    ext y
    simp [mul_assoc]

theorem normAut_apply (n : ↥(Subgroup.normalizer (H : Set G))) (y : ↥H) :
    ((normAut H n y : ↥H) : G) = (n : G) * y * (n : G)⁻¹ := rfl

@[expose] noncomputable def quotAct :
    ↥(Subgroup.normalizer (H : Set G)) →* MulAut (↥H ⧸ classicalInvolutionOddCore ↥H) :=
  (Disconnected.AschTight.S1911.quotAut H).comp (normAut H)

theorem quotAct_mk (n : ↥(Subgroup.normalizer (H : Set G))) (y : ↥H) :
    quotAct H n (QuotientGroup.mk y) = QuotientGroup.mk (normAut H n y) := rfl

theorem quotAct_of_mem (n : ↥(Subgroup.normalizer (H : Set G))) (hn : (n : G) ∈ H) :
    quotAct H n = MulAut.conj (QuotientGroup.mk (⟨n, hn⟩ : ↥H)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

theorem quotAct_eq_one (n : ↥(Subgroup.normalizer (H : Set G)))
    (h : ∀ y ∈ H, (n : G) * y * (n : G)⁻¹ * y⁻¹ ∈ oddCoreOf H) : quotAct H n = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotAct_mk, MulAut.one_apply, QuotientGroup.eq]
    have h1 := h _ (H.inv_mem y.2)
    obtain ⟨hmem, hO⟩ := mem_oddCoreOf_iff.mp h1
    have e : (normAut H n y)⁻¹ * y = ⟨_, hmem⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, normAut_apply]
      group
    rw [e]
    exact hO

end Act

section Fix

variable {H Q : Type} [Group H] [Group Q] {F : Type} [Field F] [Finite F]

theorem fix_of_second_derived [Finite Q] (hodd : Odd (Nat.card F)) (e : Q ≃* SL(2, F))
    (ρ : H →* MulAut Q) (S : Subgroup H) {x : Q} (hx : orderOf x = 4)
    (hcomm : ∀ h ∈ S, ρ h * MulAut.conj x = MulAut.conj x * ρ h) {w : Q}
    (hw : ∃ n : ℕ, w ^ 2 ^ n = 1) (hwx : w * x = x * w) :
    ∀ h ∈ ⁅⁅S, S⁆, ⁅S, S⁆⁆, ρ h w = w := by
  have hx4 : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hei : e (x * x) = -1 := by
    have h1 : orderOf (e x) = 4 := by rw [MulEquiv.orderOf_eq]; exact hx
    have h2 : orderOf (e x ^ 2) = 2 := by
      rw [orderOf_pow' _ (by norm_num), h1]
      norm_num
    rw [map_mul, ← pow_two]
    exact (sl2_orderOf_eq_two_iff hodd _).mp h2
  have hcen : ∀ y : Q, (∀ q : Q, y * q = q * y) → y = 1 ∨ y = x * x := by
    intro y hy
    have hmem : e y ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hy q]
    rcases (mem_center_sl2_iff _).mp hmem with h | h
    · left
      exact e.injective (by rw [h, map_one])
    · right
      exact e.injective (by rw [h, hei])
  have hsign : ∀ h ∈ S, ρ h x = x ∨ ρ h x = x⁻¹ := by
    intro h hhS
    have key : ∀ q : Q, ρ h x * q * (ρ h x)⁻¹ = x * q * x⁻¹ := by
      intro q
      have h1 := congrArg (fun φ : MulAut Q => φ ((ρ h).symm q)) (hcomm h hhS)
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply] at h1
      exact h1
    have hy : ∀ q : Q, (x⁻¹ * ρ h x) * q = q * (x⁻¹ * ρ h x) := by
      intro q
      calc (x⁻¹ * ρ h x) * q = x⁻¹ * (ρ h x * q * (ρ h x)⁻¹) * ρ h x := by group
        _ = x⁻¹ * (x * q * x⁻¹) * ρ h x := by rw [key q]
        _ = q * (x⁻¹ * ρ h x) := by group
    rcases hcen _ hy with h1 | h1
    · left
      calc ρ h x = x * (x⁻¹ * ρ h x) := by group
        _ = x := by rw [h1, mul_one]
    · right
      calc ρ h x = x * (x⁻¹ * ρ h x) := by group
        _ = x * (x * x) := by rw [h1]
        _ = x⁻¹ := by
          rw [eq_inv_iff_mul_eq_one]
          calc x * (x * x) * x = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := hx4
  have hback : ∀ (h : H) (q : Q), ρ h⁻¹ (ρ h q) = q := by
    intro h q
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hfix : ∀ c : H, ρ c x = x → ρ c x⁻¹ = x⁻¹ := fun c hc => by
    rw [map_inv (ρ c) x, hc]
  have hflip : ∀ c : H, ρ c x = x⁻¹ → ρ c x⁻¹ = x := fun c hc => by
    rw [map_inv (ρ c) x, hc, inv_inv]
  have hinv : ∀ c : H, (ρ c x = x → ρ c⁻¹ x = x) ∧ (ρ c x = x⁻¹ → ρ c⁻¹ x = x⁻¹) := by
    intro c
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · have := hback c x
      rwa [hc] at this
    · have := hback c x⁻¹
      rw [map_inv (ρ c) x, hc, inv_inv] at this
      exact this
  have hcom1 : ∀ a ∈ S, ∀ b ∈ S, ρ ⁅a, b⁆ x = x := by
    intro a haS b hbS
    have hρ : ρ ⁅a, b⁆ = ρ a * ρ b * ρ a⁻¹ * ρ b⁻¹ := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul]
    rw [hρ]
    simp only [MulAut.mul_apply]
    rcases hsign a haS with ha | ha <;> rcases hsign b hbS with hb | hb
    · rw [(hinv b).1 hb, (hinv a).1 ha, hb, ha]
    · rw [(hinv b).2 hb, hfix a⁻¹ ((hinv a).1 ha), hflip b hb, ha]
    · rw [(hinv b).1 hb, (hinv a).2 ha, hfix b hb, hflip a ha]
    · rw [(hinv b).2 hb, hflip a⁻¹ ((hinv a).2 ha), hb, hflip a ha]
  let S₁ : Subgroup H :=
    { carrier := {h | ρ h x = x}
      mul_mem' := fun {a b} ha hb => by
        show ρ (a * b) x = x
        rw [map_mul, MulAut.mul_apply]
        rw [show ρ b x = x from hb]
        exact ha
      one_mem' := by
        show ρ 1 x = x
        rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha => by
        show ρ a⁻¹ x = x
        have := hback a x
        rwa [show ρ a x = x from ha] at this }
  have hS₁ : ⁅S, S⁆ ≤ S₁ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hcom1 a ha b hb
  have hnc : e x ∉ Subgroup.center SL(2, F) := by
    intro hmem
    rcases (mem_center_sl2_iff _).mp hmem with h | h
    · have : x = 1 := e.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · have h2 : e (x * x) = 1 := by rw [map_mul, h]; simp
      rw [hei] at h2
      exact sl2_neg_one_ne_one hodd h2
  have hTcomm : ∀ s t : Q, s * x = x * s → t * x = x * t → s * t = t * s := by
    intro s t hs ht
    apply e.injective
    rw [map_mul, map_mul]
    refine sl2_comm_of_comm hnc ?_ ?_
    · rw [← map_mul, ← map_mul, hs]
    · rw [← map_mul, ← map_mul, ht]
  let T₂ : Subgroup Q :=
    { carrier := {t | t * x = x * t ∧ ∃ n : ℕ, t ^ 2 ^ n = 1}
      mul_mem' := fun {s t} hs ht => by
        obtain ⟨hs1, n, hn⟩ := hs
        obtain ⟨ht1, k, hk⟩ := ht
        refine ⟨?_, n + k, ?_⟩
        · calc s * t * x = s * (t * x) := by group
            _ = s * (x * t) := by rw [ht1]
            _ = (s * x) * t := by group
            _ = (x * s) * t := by rw [hs1]
            _ = x * (s * t) := by group
        · have hc : Commute s t := hTcomm s t hs1 ht1
          rw [hc.mul_pow, pow_add, pow_mul, pow_mul', hn, hk, one_pow, one_pow, mul_one]
      one_mem' := ⟨by group, 0, by simp⟩
      inv_mem' := fun {t} ht => by
        obtain ⟨ht1, n, hn⟩ := ht
        refine ⟨?_, n, by rw [inv_pow, hn, inv_one]⟩
        calc t⁻¹ * x = t⁻¹ * (x * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * x) * t⁻¹ := by rw [ht1]
          _ = x * t⁻¹ := by group }
  have hwT : w ∈ T₂ := ⟨hwx, hw⟩
  have hT₂cyc : IsCyclic ↥T₂ := by
    let _ : CommGroup ↥T₂ :=
      { (inferInstance : Group ↥T₂) with
        mul_comm := fun a b => Subtype.ext (hTcomm _ _ a.2.1 b.2.1) }
    refine CFSG.ComponentClassification.FooteLit.isCyclic_of_unique_involution ?_ ?_
    · intro g
      obtain ⟨n, hn⟩ := g.2.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · intro a b ha hb
      by_cases ha1 : a = 1
      · exact Or.inl ha1
      by_cases hb1 : b = 1
      · exact Or.inr (Or.inl hb1)
      right; right
      have hinvol : ∀ c : ↥T₂, c ^ 2 = 1 → c ≠ 1 → e (c : Q) = -1 := by
        intro c hc hc1
        refine (sl2_orderOf_eq_two_iff hodd _).mp ?_
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
        exact orderOf_eq_prime hc hc1
      apply Subtype.ext
      exact e.injective ((hinvol a ha ha1).trans (hinvol b hb hb1).symm)
  have hpres : ∀ h ∈ ⁅S, S⁆, ∀ t ∈ T₂, ρ h t ∈ T₂ := by
    intro h hh t ht
    have hhx : ρ h x = x := hS₁ hh
    obtain ⟨ht1, n, hn⟩ := ht
    refine ⟨?_, n, ?_⟩
    · rw [← hhx, ← map_mul, ← map_mul, ht1]
    · rw [← map_pow, hn, map_one]
  obtain ⟨⟨g, hgT⟩, hg⟩ := hT₂cyc.exists_generator
  have hgen : ∀ t ∈ T₂, ∃ k : ℤ, t = g ^ k := by
    intro t ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨t, ht⟩)
    exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩
  have hpow : ∀ h ∈ ⁅S, S⁆, ∃ k : ℤ, ρ h g = g ^ k := fun h hh =>
    hgen _ (hpres h hh g hgT)
  have hcomm2 : ∀ a ∈ ⁅S, S⁆, ∀ b ∈ ⁅S, S⁆, ρ ⁅a, b⁆ g = g := by
    intro a ha b hb
    have key : ∀ a ∈ ⁅S, S⁆, ∀ b ∈ ⁅S, S⁆,
        ρ (a * b) g = ρ (b * a) g := by
      intro a ha b hb
      obtain ⟨k, hk⟩ := hpow a ha
      obtain ⟨l, hl⟩ := hpow b hb
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hk, hl, map_zpow, map_zpow, hk,
        hl, ← zpow_mul, ← zpow_mul, mul_comm]
    have hinvmem : ∀ c ∈ ⁅S, S⁆, c⁻¹ ∈ ⁅S, S⁆ :=
      fun c hc => Subgroup.inv_mem _ hc
    have h1 := key a⁻¹ (hinvmem a ha) b⁻¹ (hinvmem b hb)
    have e1 : ⁅a, b⁆ = (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹)⁻¹⁻¹ := by
      rw [commutatorElement_def]; group
    have h2 : ρ ((b⁻¹ * a⁻¹)⁻¹) (ρ (b⁻¹ * a⁻¹) g) = g := hback _ g
    rw [e1, inv_inv, map_mul, MulAut.mul_apply, h1]
    exact h2
  let S₂ : Subgroup H :=
    { carrier := {h | ∀ t ∈ T₂, ρ h t = t}
      mul_mem' := fun {a b} ha hb t ht => by
        show ρ (a * b) t = t
        rw [map_mul, MulAut.mul_apply, hb t ht, ha t ht]
      one_mem' := fun t _ => by
        show ρ 1 t = t
        rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha t ht => by
        show ρ a⁻¹ t = t
        have := hback a t
        rwa [ha t ht] at this }
  have hS₂ : ⁅⁅S, S⁆, ⁅S, S⁆⁆ ≤ S₂ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb t ht
    obtain ⟨k, rfl⟩ := hgen t ht
    rw [map_zpow, hcomm2 a ha b hb]
  exact fun h hh => hS₂ hh w hwT

end Fix

section SL2Copy

variable {C : Type} [Group C] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem sq_eq_one_of_central_sl2 (e : C ≃* SL(2, F)) {y : C} (hy : ∀ q : C, y * q = q * y) :
    y * y = 1 := by
  have hmem : e y ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hy q]
  apply e.injective
  rw [map_mul, map_one]
  rcases (mem_center_sl2_iff _).mp hmem with h | h
  · rw [h, one_mul]
  · rw [h]
    simp

theorem eq_bot_of_odd_normal_sl2 [Finite C] (h4 : 4 ≤ Nat.card F) (e : C ≃* SL(2, F))
    (N : Subgroup C) (hN : N.Normal) (hodd : Odd (Nat.card N)) {t : C} (ht : orderOf t = 2) :
    N = ⊥ := by
  have hodd1 : ∀ y ∈ N, y * y = 1 → y = 1 := by
    intro y hy hy2
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    have h2 : orderOf (⟨y, hy⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    have h3 : Odd (orderOf y) := Odd.of_dvd_nat hodd h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h3
      exact absurd h3 (by decide)
  rcases normal_cases_of_equiv_sl2 h4 e N hN with h | h | h
  · exact h
  · rw [eq_bot_iff]
    intro y hy
    have hyc : y ∈ Subgroup.center C := h ▸ hy
    exact Subgroup.mem_bot.mpr (hodd1 y hy (sq_eq_one_of_central_sl2 e
      (fun q => (Subgroup.mem_center_iff.mp hyc q).symm)))
  · exfalso
    have htN : t ∈ N := h ▸ Subgroup.mem_top t
    have h1 := hodd1 t htN (by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t)
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)

end SL2Copy

end CFSG.ClassicalInvolution.Asc77.S24
