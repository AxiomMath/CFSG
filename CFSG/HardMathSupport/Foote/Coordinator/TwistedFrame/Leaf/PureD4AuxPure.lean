module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureD4AuxDich

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PureD4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


section SL2

variable {K : Type} [Field K]

theorem coe_comm_vSL_uSL (s t : K) :
    ((⁅vSL s, uSL t⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      !![1 - s * t, s * t ^ 2; -(s ^ 2 * t), 1 + s * t + s ^ 2 * t ^ 2] := by
  rw [commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL, uSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_comm_vSL_uSL_sub_one (s t : K) :
    (((⁅vSL s, uSL t⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) - 1).det = -(s * t) ^ 2 := by
  rw [coe_comm_vSL_uSL, Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.one_apply]
  ring

theorem comm_vSL_uSL_pow_ne_one (p : ℕ) [Fact p.Prime] [CharP K p] {s t : K} (h : s * t ≠ 0)
    (k : ℕ) : (⁅vSL s, uSL t⁆ : SL2 K) ^ p ^ k ≠ 1 := by
  intro h1
  have hM : (((⁅vSL s, uSL t⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K)) ^ p ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h1]
    rfl
  have hN : (((⁅vSL s, uSL t⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) - 1) ^ p ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right _), hM, one_pow, sub_self]
  have hd := congrArg Matrix.det hN
  rw [Matrix.det_pow, Matrix.det_zero, det_comm_vSL_uSL_sub_one] at hd
  have : (-(s * t) ^ 2 : K) = 0 := pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero) |>.1 hd
  exact h (pow_eq_zero_iff two_ne_zero |>.1 (neg_eq_zero.1 this))

end SL2

section E8

variable {K : Type} [Field K]

open CFSG.RankThree.Chevalley in
theorem comm_Uneg_Uθ_pow_ne_one (p : ℕ) [Fact p.Prime] [CharP K p] {a w : K} (ha : a ≠ 0)
    (hw : w ≠ 0) (k : ℕ) :
    ⁅pinnedX Tag.E8 K (-highRoot Tag.E8) a, pinnedX Tag.E8 K (highRoot Tag.E8) w⁆ ^ p ^ k ≠ 1 := by
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) (isRoot_hr)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, zero_mul] at hε; exact zero_ne_one hε
  set e := (pinnedData Tag.E8 (highRoot Tag.E8)).2.2 with he
  have hee : e • (e • w) = w := by
    rcases pinnedSign_eq Tag.E8 (highRoot Tag.E8) with h | h <;> rw [← he] at h <;> rw [h] <;> simp
  have hew : e • w ≠ 0 := by
    intro h0
    apply hw
    rw [← hee, h0, smul_zero]
  have h1 : pinnedX Tag.E8 K (-highRoot Tag.E8) a =
      rootSL2 Tag.E8 K (highRoot Tag.E8) (vSL (ε * a)) := by
    rw [hv, ← mul_assoc, hε, one_mul]
  have h2 : pinnedX Tag.E8 K (highRoot Tag.E8) w =
      rootSL2 Tag.E8 K (highRoot Tag.E8) (uSL (e • w)) := by
    rw [rootSL2_uSL_eq, hee]
  rw [h1, h2, ← map_commutatorElement, ← map_pow]
  intro h
  exact comm_vSL_uSL_pow_ne_one p (mul_ne_zero (mul_ne_zero hε0 ha) hew) k
    (rootSL2_injective_of_field _ (by rwa [map_one]))

theorem mirror_dichotomy (K : Type) [Field K] {m₀ : ModGL Tag.E8 K}
    (hm₀ : m₀ ∈ adjointGroup Tag.E8 K) (hconj : conjSub m₀ (Uθ Tag.E8 K) = Heis.Uneg Tag.E8 K)
    {B : Subgroup (ModGL Tag.E8 K)} (hB : IsLongRootSubgroup Tag.E8 K B) :
    (∀ u ∈ Heis.Uneg Tag.E8 K, ∀ d ∈ B, ⁅u, d⁆ ∈ conjSub m₀ (Qθ Tag.E8 K)) ∨
      ∃ m ∈ Heis.Uneg Tag.E8 K ⊔ B, conjSub m (Heis.Uneg Tag.E8 K) = B := by
  obtain ⟨g, hg, rfl⟩ := hB
  have hD : IsLongRootSubgroup Tag.E8 K (conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K)) :=
    ⟨m₀⁻¹ * g, mul_mem (inv_mem hm₀) hg, rfl⟩
  have hBD : conjSub g (Uθ Tag.E8 K) = conjSub m₀ (conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K)) := by
    rw [← conjSub_mul, mul_inv_cancel_left]
  rcases theta_dichotomy' K hD with h | ⟨m, hm, hmD⟩
  · left
    intro u hu d hd
    rw [← hconj] at hu
    have hu' : m₀⁻¹ * u * m₀ ∈ Uθ Tag.E8 K := mem_conjSub_iff.1 hu
    have hd' : m₀⁻¹ * d * m₀ ∈ conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K) := by
      rw [hBD] at hd
      exact mem_conjSub_iff.1 hd
    have := h _ hu' _ hd'
    rw [mem_conjSub_iff]
    have e : m₀⁻¹ * ⁅u, d⁆ * m₀ = ⁅m₀⁻¹ * u * m₀, m₀⁻¹ * d * m₀⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact this
  · right
    refine ⟨m₀ * m * m₀⁻¹, ?_, ?_⟩
    · have h1 : m₀ * m * m₀⁻¹ ∈ conjSub m₀ (Uθ Tag.E8 K ⊔ conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K)) := by
        rw [mem_conjSub_iff]
        have e : m₀⁻¹ * (m₀ * m * m₀⁻¹) * m₀ = m := by group
        rw [e]
        exact hm
      have h2 : conjSub m₀ (Uθ Tag.E8 K ⊔ conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K)) =
          conjSub m₀ (Uθ Tag.E8 K) ⊔ conjSub m₀ (conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K)) := by
        unfold conjSub
        rw [Subgroup.map_sup]
      rw [h2, hconj, ← hBD] at h1
      exact h1
    · rw [hBD, ← hconj]
      calc conjSub (m₀ * m * m₀⁻¹) (conjSub m₀ (Uθ Tag.E8 K))
          = conjSub m₀ (conjSub m (Uθ Tag.E8 K)) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub m₀ (conjSub (m₀⁻¹ * g) (Uθ Tag.E8 K)) := by rw [hmD]

theorem commute_of_special_special (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {Qm : Subgroup (ModGL Tag.E8 K)} (hQm : ∀ x ∈ Qm, ∃ k : ℕ, x ^ p ^ k = 1)
    {C : Subgroup (ModGL Tag.E8 K)} (hCQ : C ≤ Qθ Tag.E8 K) {r : ModGL Tag.E8 K}
    (hr : r ∈ Qθ Tag.E8 K)
    (hC : ∀ u ∈ Heis.Uneg Tag.E8 K, ∀ d ∈ C, ⁅u, d⁆ ∈ Qm)
    (hCr : ∀ u ∈ Heis.Uneg Tag.E8 K, ∀ d ∈ conjSub r⁻¹ C, ⁅u, d⁆ ∈ Qm) :
    ∀ d ∈ C, r * d = d * r := by
  intro d hd
  have hs := heisCoord_spec Tag.E8 K
  have hdQ : d ∈ Qθ Tag.E8 K := hCQ hd
  have hrinv : r⁻¹ ∈ Qθ Tag.E8 K := inv_mem hr
  have hrd : r⁻¹ * d ∈ Qθ Tag.E8 K := mul_mem hrinv hdQ
  have hd₂Q : r⁻¹ * d * r ∈ Qθ Tag.E8 K := mul_mem hrd hr
  have hd₂ : r⁻¹ * d * r ∈ conjSub r⁻¹ C := by
    rw [mem_conjSub_iff]
    have e : (r⁻¹)⁻¹ * (r⁻¹ * d * r) * r⁻¹ = d := by group
    rw [e]
    exact hd
  have hcoord₂ : heisCoord Tag.E8 K (r⁻¹ * d * r) = heisCoord Tag.E8 K d := by
    rw [hs.mul _ hrd _ hr, hs.mul _ hrinv _ hdQ, heisCoord_inv hr]
    abel
  have hyU : d⁻¹ * (r⁻¹ * d * r) ∈ Uθ Tag.E8 K := by
    refine (hs.eq_zero_iff _ (mul_mem (inv_mem hdQ) hd₂Q)).1 ?_
    rw [hs.mul _ (inv_mem hdQ) _ hd₂Q, heisCoord_inv hdQ, hcoord₂]
    abel
  obtain ⟨w, hw⟩ := mem_rootSubgroup.1 hyU
  by_cases hw0 : w = 0
  · subst hw0
    rw [pinnedX_zero] at hw
    have : r⁻¹ * d * r = d := by
      calc r⁻¹ * d * r = d * (d⁻¹ * (r⁻¹ * d * r)) := by group
        _ = d := by rw [← hw]; group
    calc r * d = r * (r⁻¹ * d * r) := by rw [this]
      _ = d * r := by group
  · exfalso
    have hu : pinnedX Tag.E8 K (-highRoot Tag.E8) (1 : K) ∈ Heis.Uneg Tag.E8 K :=
      mem_rootSubgroup.2 ⟨1, rfl⟩
    have h1 := hC _ hu d hd
    have h2 := hCr _ hu _ hd₂
    set u := pinnedX Tag.E8 K (-highRoot Tag.E8) (1 : K) with hu_def
    set y := d⁻¹ * (r⁻¹ * d * r) with hy_def
    have hd₂eq : r⁻¹ * d * r = d * y := by rw [hy_def]; group
    have key : d * ⁅u, y⁆ * d⁻¹ = ⁅u, d⁆⁻¹ * ⁅u, r⁻¹ * d * r⁆ := by
      rw [hd₂eq]
      simp only [commutatorElement_def]
      group
    have hmem : d * ⁅u, y⁆ * d⁻¹ ∈ Qm := by
      rw [key]
      exact mul_mem (inv_mem h1) h2
    obtain ⟨k, hk⟩ := hQm _ hmem
    rw [conj_pow] at hk
    have hk' : ⁅u, y⁆ ^ p ^ k = 1 := by
      have : d * ⁅u, y⁆ ^ p ^ k * d⁻¹ = 1 := hk
      calc ⁅u, y⁆ ^ p ^ k = d⁻¹ * (d * ⁅u, y⁆ ^ p ^ k * d⁻¹) * d := by group
        _ = 1 := by rw [this]; group
    rw [← hw] at hk'
    exact comm_Uneg_Uθ_pow_ne_one p one_ne_zero hw0 k hk'

theorem pPower_of_mem_conj_Qθ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (m₀ : ModGL Tag.E8 K) :
    ∀ x ∈ conjSub m₀ (Qθ Tag.E8 K), ∃ k : ℕ, x ^ p ^ k = 1 := by
  intro x hx
  have hq : m₀⁻¹ * x * m₀ ∈ Qθ Tag.E8 K := mem_conjSub_iff.1 hx
  have hpos : m₀⁻¹ * x * m₀ ∈ posUnipotent Tag.E8 K := parabolicRadical_le_posUnipotent _ hq
  have hpg := ((positive_root_triangularity.{0, 0} Tag.E8).2 K p).2.1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hpg) ⟨m₀⁻¹ * x * m₀, hpos⟩
  refine ⟨k, ?_⟩
  have h1 : (⟨m₀⁻¹ * x * m₀, hpos⟩ : posUnipotent Tag.E8 K) ^ p ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have h2 : (m₀⁻¹ * x * m₀) ^ p ^ k = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  have e : x = m₀ * (m₀⁻¹ * x * m₀) * m₀⁻¹ := by group
  rw [e, conj_pow, h2]
  group

theorem pure_of_center (K : Type) [Field K] [Finite K]
    {X : Subgroup (ModGL Tag.E8 K)} (hU : Uθ Tag.E8 K ≤ X) (hV : Heis.Uneg Tag.E8 K ≤ X)
    (hZ : ∀ d ∈ X ⊓ Qθ Tag.E8 K, (∀ r ∈ X ⊓ Qθ Tag.E8 K, r * d = d * r) → d ∈ Uθ Tag.E8 K)
    {g : ModGL Tag.E8 K} (hg : g ∈ adjointGroup Tag.E8 K)
    (hC : conjSub g (Uθ Tag.E8 K) ≤ X ⊓ Qθ Tag.E8 K) :
    ∃ x ∈ X, conjSub g (Uθ Tag.E8 K) = conjSub x (Uθ Tag.E8 K) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨m₀, hm₀mem, hconj⟩ := exists_weyl_Uθ K
  have hm₀G : m₀ ∈ adjointGroup Tag.E8 K := by
    have h1 : Uθ Tag.E8 K ≤ adjointGroup Tag.E8 K := rootSubgroup_le_adjointGroup _
    have h2 : Heis.Uneg Tag.E8 K ≤ adjointGroup Tag.E8 K := rootSubgroup_le_adjointGroup _
    exact (sup_le h1 h2) hm₀mem
  have hm₀X : m₀ ∈ X := (sup_le hU hV) hm₀mem
  have hQm := pPower_of_mem_conj_Qθ K p m₀
  by_cases hall : ∀ d ∈ conjSub g (Uθ Tag.E8 K), d ∈ Uθ Tag.E8 K
  ·
    refine ⟨1, one_mem _, ?_⟩
    have hgP : g ∈ Pθ Tag.E8 K := mem_Pθ_of_conj_le Tag.E8 K hg fun d hd => hall d hd
    rw [conjSub_one]
    exact Heis.conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.E8 K hgP)
  · push Not at hall
    obtain ⟨d, hd, hdU⟩ := hall
    have hdXQ : d ∈ X ⊓ Qθ Tag.E8 K := hC hd
    obtain ⟨r, hrXQ, hrd⟩ : ∃ r ∈ X ⊓ Qθ Tag.E8 K, r * d ≠ d * r := by
      by_contra hcon
      push Not at hcon
      exact hdU (hZ d hdXQ hcon)
    have hrX : r ∈ X := hrXQ.1
    have hrQ : r ∈ Qθ Tag.E8 K := hrXQ.2
    have hCX : conjSub g (Uθ Tag.E8 K) ≤ X := fun x hx => (hC hx).1
    have hCQ : conjSub g (Uθ Tag.E8 K) ≤ Qθ Tag.E8 K := fun x hx => (hC hx).2
    have hCrX : conjSub r⁻¹ (conjSub g (Uθ Tag.E8 K)) ≤ X :=
      conjSub_le_of_mem_of_le (inv_mem hrX) hCX
    have hLong1 : IsLongRootSubgroup Tag.E8 K (conjSub g (Uθ Tag.E8 K)) := ⟨g, hg, rfl⟩
    have hrG : r ∈ adjointGroup Tag.E8 K := Qθ_le_adjointGroup Tag.E8 K hrQ
    have hLong2 : IsLongRootSubgroup Tag.E8 K (conjSub r⁻¹ (conjSub g (Uθ Tag.E8 K))) :=
      ⟨r⁻¹ * g, mul_mem (inv_mem hrG) hg, by rw [conjSub_mul]⟩
    have hopp : ∀ {B : Subgroup (ModGL Tag.E8 K)}, B ≤ X →
        (∃ m ∈ Heis.Uneg Tag.E8 K ⊔ B, conjSub m (Heis.Uneg Tag.E8 K) = B) →
        ∃ x ∈ X, B = conjSub x (Uθ Tag.E8 K) := by
      intro B hBX ⟨m, hm, hmB⟩
      refine ⟨m * m₀, mul_mem ((sup_le hV hBX) hm) hm₀X, ?_⟩
      rw [conjSub_mul, hconj, hmB]
    rcases mirror_dichotomy K hm₀G hconj hLong1 with h1 | h1
    · rcases mirror_dichotomy K hm₀G hconj hLong2 with h2 | h2
      · exact absurd (commute_of_special_special K p hQm hCQ hrQ h1 h2 d hd) hrd
      · obtain ⟨x, hx, hxe⟩ := hopp hCrX h2
        refine ⟨r * x, mul_mem hrX hx, ?_⟩
        rw [conjSub_mul, ← hxe, ← conjSub_mul, mul_inv_cancel, conjSub_one]
    · obtain ⟨x, hx, hxe⟩ := hopp hCX h1
      exact ⟨x, hx, hxe⟩

end E8

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let N : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have e : b * a' = a' * b := (h a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [e]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have e : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := (h a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)).symm
        rw [mul_inv_rev, e] }
  have hAN : A ≤ N := fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩
  have hBN : B ≤ N := fun b hb => ⟨1, one_mem _, b, hb, by simp⟩
  exact (sup_le hAN hBN) hx

theorem pure_of_center_sup (K : Type) [Field K] [Finite K] {X₁ X₂ : Subgroup (ModGL Tag.E8 K)}
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) (hU : Uθ Tag.E8 K ≤ X₁)
    (hV : Heis.Uneg Tag.E8 K ≤ X₁)
    (hZ : ∀ d ∈ (X₁ ⊔ X₂) ⊓ Qθ Tag.E8 K,
      (∀ r ∈ (X₁ ⊔ X₂) ⊓ Qθ Tag.E8 K, r * d = d * r) → d ∈ Uθ Tag.E8 K)
    {g : ModGL Tag.E8 K} (hg : g ∈ adjointGroup Tag.E8 K)
    (hC : conjSub g (Uθ Tag.E8 K) ≤ (X₁ ⊔ X₂) ⊓ Qθ Tag.E8 K) :
    ∃ x ∈ X₁, conjSub g (Uθ Tag.E8 K) = conjSub x (Uθ Tag.E8 K) := by
  obtain ⟨x, hx, hxe⟩ := pure_of_center K (le_sup_of_le_left hU) (le_sup_of_le_left hV) hZ hg hC
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  refine ⟨a, ha, ?_⟩
  have hbU : conjSub b (Uθ Tag.E8 K) = Uθ Tag.E8 K :=
    conjSub_eq_of_mem_normalizer (mem_normalizer_of_forall_mul_eq fun u hu =>
      (hcomm u (hU hu) b hb).symm)
  rw [hxe, conjSub_mul, hbU]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PureD4Aux

