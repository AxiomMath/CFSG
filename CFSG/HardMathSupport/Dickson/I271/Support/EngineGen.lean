module

public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem exists_fixed_in_coset {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {a w : X}
    {S₀ : Subgroup X} (hap : a ^ p = 1) (hS₀ : Nat.Coprime p (Nat.card S₀))
    (hT : ∀ x, w⁻¹ * x ∈ S₀ ↔ w⁻¹ * (a * x * a⁻¹) ∈ S₀) :
    ∃ x, w⁻¹ * x ∈ S₀ ∧ a * x * a⁻¹ = x := by
  classical
  let α := {x : X // w⁻¹ * x ∈ S₀}
  haveI : Fintype α := Fintype.ofFinite α
  let σ : Equiv.Perm α := Equiv.subtypeEquiv (MulAut.conj a).toEquiv hT
  have hpow : ∀ (n : ℕ) (x : α), ((σ ^ n) x : X) = a ^ n * (x : X) * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      have h1 : ((σ ((σ ^ n) x) : α) : X) = a * (((σ ^ n) x : α) : X) * a⁻¹ := rfl
      rw [h1, ih, pow_succ']
      group
  have hσ : σ ^ p ^ 1 = 1 := by
    ext x
    simp only [pow_one, Equiv.Perm.coe_one, id_eq]
    rw [hpow p x, hap]
    simp
  have hα : ¬ p ∣ Fintype.card α := by
    have hcard : Fintype.card α = Nat.card S₀ := by
      rw [← Nat.card_eq_fintype_card]
      refine Nat.card_congr ⟨fun x => ⟨w⁻¹ * x.1, x.2⟩, fun y => ⟨w * y.1, by simp⟩, ?_, ?_⟩
      · intro x; ext; simp
      · intro y; ext; simp
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hS₀
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hα hσ
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

theorem comm_mem_normalizer_component {G : Type*} [Group G] [Finite G] {p : ℕ} {N B : Subgroup G}
    {w b : G} (hwN : w ∈ Subgroup.normalizer (N : Set G)) (hb : b ∈ B)
    (hcomp : ∀ J : Subgroup G, GLAPComponent p N J → B ≤ Subgroup.normalizer (J : Set G))
    {J : Subgroup G} (hJ : GLAPComponent p N J) : w * b * w⁻¹ * b⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
  have hJ₁ : GLAPComponent p N (GLBConj w J) := by
    have := glaPComponent_gLBConj (p := p) w hJ
    rwa [mem_normalizer_iff_gLBConj_eq.1 hwN] at this
  have hbJ := hcomp J hJ hb
  have hbJ₁ := hcomp (GLBConj w J) hJ₁ hb
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have h1 : b⁻¹ * y * b ∈ J := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbJ) y).1 hy
    simpa using this
  have h2 : w⁻¹ * (b⁻¹ * y * b) * w ∈ GLBConj w J := by
    rw [mem_gLBConj]
    have : w * (w⁻¹ * (b⁻¹ * y * b) * w) * w⁻¹ = b⁻¹ * y * b := by group
    rw [this]
    exact h1
  have h3 : b * (w⁻¹ * (b⁻¹ * y * b) * w) * b⁻¹ ∈ GLBConj w J :=
    (Subgroup.mem_normalizer_iff.1 hbJ₁ _).1 h2
  have h4 : w * (b * (w⁻¹ * (b⁻¹ * y * b) * w) * b⁻¹) * w⁻¹ ∈ J := mem_gLBConj.1 h3
  have : w * b * w⁻¹ * b⁻¹ * y * (w * b * w⁻¹ * b⁻¹)⁻¹ =
      w * (b * (w⁻¹ * (b⁻¹ * y * b) * w) * b⁻¹) * w⁻¹ := by group
  rw [this]
  exact h4

theorem commutator_mem_sup_sup {X : Type*} [Group X] {K W B : Subgroup X}
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hBW : B ≤ Subgroup.normalizer (W : Set X)) :
    ∀ x ∈ K ⊔ W ⊔ B, ∀ y ∈ K ⊔ W ⊔ B, ⁅x, y⁆ ∈ K ⊔ W := by
  set X₁ := K ⊔ W ⊔ B with hX₁
  have hMX : K ⊔ W ≤ X₁ := le_sup_left
  have hBX : B ≤ X₁ := le_sup_right
  have hBM : B ≤ Subgroup.normalizer ((K ⊔ W : Subgroup X) : Set X) := fun b hb =>
    mem_normalizer_sup (hBK hb) (hBW hb)
  haveI hMn : ((K ⊔ W).subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).2
      (sup_le Subgroup.le_normalizer hBM)
  have hMB : (K ⊔ W).subgroupOf X₁ ⊔ B.subgroupOf X₁ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMX hBX]
    exact Subgroup.subgroupOf_self X₁
  intro x hx y hy
  have := commutator_mem_of_sup_eq_top hMB
    (fun a ha b hb => Subtype.ext (hBab _ ((Subgroup.mem_subgroupOf).1 ha) _
      ((Subgroup.mem_subgroupOf).1 hb))) ⟨x, hx⟩ ⟨y, hy⟩
  exact (Subgroup.mem_subgroupOf).1 this

theorem isSCp_sup_of_isSCp {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K W B : Subgroup X} (hBel : IsElemAbelian p B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hWK : W ≤ Subgroup.normalizer (K : Set X)) (hWp : Nat.Coprime p (Nat.card W))
    (hBW : B ≤ Subgroup.normalizer (W : Set X)) (hSC : IsSCp p (K ⊔ B) B) :
    IsSCp p (K ⊔ W ⊔ B) B := by
  haveI : Fact p.Prime := ⟨hp⟩
  set X₁ := K ⊔ W ⊔ B with hX₁
  have hKX : K ≤ X₁ := le_sup_left.trans le_sup_left
  have hWX : W ≤ X₁ := le_sup_right.trans le_sup_left
  have hBX : B ≤ X₁ := le_sup_right
  have hMX : K ⊔ W ≤ X₁ := le_sup_left
  have hX₁N : X₁ ≤ Subgroup.normalizer (K : Set X) :=
    sup_le (sup_le Subgroup.le_normalizer hWK) hBK
  haveI hKn : (K.subgroupOf X₁).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hX₁N
  have hBM : B ≤ Subgroup.normalizer ((K ⊔ W : Subgroup X) : Set X) := fun b hb =>
    mem_normalizer_sup (hBK hb) (hBW hb)
  haveI hMn : ((K ⊔ W).subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).2 (sup_le Subgroup.le_normalizer hBM)
  refine ⟨hBX, hBel, ?_⟩
  intro E hEX hEel hBE
  have hEK : E ≤ K ⊔ B := by
    intro x hx
    set x' : ↥X₁ := ⟨x, hEX hx⟩ with hx'
    have hx'mem : x' ∈ (K ⊔ W).subgroupOf X₁ ⊔ B.subgroupOf X₁ := by
      rw [← Subgroup.subgroupOf_sup hMX hBX]
      exact (Subgroup.mem_subgroupOf).2 (hEX hx)
    obtain ⟨m, hm, b, hb, hmb⟩ := Subgroup.mem_sup_of_normal_left.1 hx'mem
    have hm' : m ∈ K.subgroupOf X₁ ⊔ W.subgroupOf X₁ := by
      rw [← Subgroup.subgroupOf_sup hKX hWX]
      exact hm
    obtain ⟨k, hk, s, hs, hks⟩ := Subgroup.mem_sup_of_normal_left.1 hm'
    set ρ := QuotientGroup.mk' (K.subgroupOf X₁) with hρ
    have hρk : ρ k = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hk
    have hρx : ρ x' = ρ s * ρ b := by
      rw [← hmb, ← hks, map_mul, map_mul, hρk, one_mul]
    have hbB : (b : X) ∈ B := (Subgroup.mem_subgroupOf).1 hb
    have hcomm : ∀ b' ∈ B.subgroupOf X₁, x' * b' = b' * x' := fun b' hb' =>
      Subtype.ext (CFSG.Open.IsElemAbelian.comm hEel hx (hBE ((Subgroup.mem_subgroupOf).1 hb')))
    have hBc : ∀ b₁ ∈ B.subgroupOf X₁, ∀ b₂ ∈ B.subgroupOf X₁, b₁ * b₂ = b₂ * b₁ := fun b₁ h₁ b₂ h₂ =>
      Subtype.ext (CFSG.Open.IsElemAbelian.comm hBel ((Subgroup.mem_subgroupOf).1 h₁)
        ((Subgroup.mem_subgroupOf).1 h₂))
    have hsc : ∀ b' ∈ B.subgroupOf X₁, ρ s * ρ b' = ρ b' * ρ s := by
      intro b' hb'
      have h1 := congrArg ρ (hcomm b' hb')
      rw [map_mul, map_mul, hρx] at h1
      have h2 : ρ b * ρ b' = ρ b' * ρ b := by rw [← map_mul, ← map_mul, hBc b hb b' hb']
      have h3 : (ρ s * ρ b') * ρ b = (ρ b' * ρ s) * ρ b := by
        calc (ρ s * ρ b') * ρ b = ρ s * (ρ b' * ρ b) := mul_assoc _ _ _
          _ = ρ s * (ρ b * ρ b') := by rw [h2]
          _ = (ρ s * ρ b) * ρ b' := (mul_assoc _ _ _).symm
          _ = ρ b' * (ρ s * ρ b) := h1
          _ = (ρ b' * ρ s) * ρ b := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    have hsb : ρ s * ρ b = ρ b * ρ s := hsc b hb
    have hxp : x' ^ p = 1 := Subtype.ext (hEel.2 x hx)
    have hbp : b ^ p = 1 := Subtype.ext (hBel.2 _ hbB)
    have hsp : (ρ s) ^ p = 1 := by
      have h1 : (ρ s * ρ b) ^ p = 1 := by rw [← hρx, ← map_pow, hxp, map_one]
      rw [Commute.mul_pow hsb, ← map_pow ρ b, hbp, map_one, mul_one] at h1
      exact h1
    have hsW : (ρ s) ^ Nat.card W = 1 := by
      have hc : Nat.card (W.subgroupOf X₁) = Nat.card W :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv
      have := pow_card_eq_one' (G := ↥(W.subgroupOf X₁)) (x := ⟨s, hs⟩)
      rw [hc] at this
      have hsn : s ^ Nat.card W = 1 := by
        have := congrArg Subtype.val this
        simpa using this
      rw [← map_pow, hsn, map_one]
    have hs1 : ρ s = 1 := by
      have h1 : orderOf (ρ s) ∣ p := orderOf_dvd_of_pow_eq_one hsp
      have h2 : orderOf (ρ s) ∣ Nat.card W := orderOf_dvd_of_pow_eq_one hsW
      exact orderOf_eq_one_iff.1 ((Nat.Coprime.coprime_dvd_left h1 hWp).eq_one_of_dvd h2)
    have hmem : x' * b⁻¹ ∈ K.subgroupOf X₁ := by
      have h : ρ (x' * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hρx, hs1, one_mul, mul_inv_cancel]
      have := MonoidHom.mem_ker.2 h
      rwa [hρ, QuotientGroup.ker_mk'] at this
    have : x' ∈ K.subgroupOf X₁ ⊔ B.subgroupOf X₁ := by
      have := Subgroup.mul_mem_sup hmem hb
      rwa [inv_mul_cancel_right] at this
    rw [← Subgroup.subgroupOf_sup hKX hBX] at this
    exact (Subgroup.mem_subgroupOf).1 this
  exact hSC.2.2 E hEK hEel hBE

section Main

variable {X : Type} [Group X] [Finite X]

theorem conj_mem_centralizer {K : Subgroup X} {g y : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    (hy : y ∈ Subgroup.centralizer (K : Set X)) : g * y * g⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : g⁻¹ * k * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) k).1 hk
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 hy _ h1
  calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [h2]
    _ = g * y * g⁻¹ * k := by group

@[expose] def commModC (K B : Subgroup X) : Subgroup X where
  carrier := {w | w ∈ Subgroup.normalizer (K : Set X) ∧
    ∀ b ∈ B, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X)}
  one_mem' := ⟨Subgroup.one_mem _, fun b _ => by simp⟩
  mul_mem' := by
    rintro w₁ w₂ ⟨hw₁, hc₁⟩ ⟨hw₂, hc₂⟩
    refine ⟨Subgroup.mul_mem _ hw₁ hw₂, fun b hb => ?_⟩
    have : w₁ * w₂ * b * (w₁ * w₂)⁻¹ * b⁻¹ =
        (w₁ * (w₂ * b * w₂⁻¹ * b⁻¹) * w₁⁻¹) * (w₁ * b * w₁⁻¹ * b⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (conj_mem_centralizer hw₁ (hc₂ b hb)) (hc₁ b hb)
  inv_mem' := by
    rintro w ⟨hw, hc⟩
    refine ⟨Subgroup.inv_mem _ hw, fun b hb => ?_⟩
    have : w⁻¹ * b * w⁻¹⁻¹ * b⁻¹ = w⁻¹ * (w * b * w⁻¹ * b⁻¹)⁻¹ * w⁻¹⁻¹ := by group
    rw [this]
    exact conj_mem_centralizer (Subgroup.inv_mem _ hw) (Subgroup.inv_mem _ (hc b hb))

theorem mem_commModC {K B : Subgroup X} {w : X} :
    w ∈ commModC K B ↔ w ∈ Subgroup.normalizer (K : Set X) ∧
      ∀ b ∈ B, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X) := Iff.rfl

end Main

section Engine

variable {X : Type} [Group X] [Finite X]

structure EngineHyp (p : ℕ) (K B A : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  quasi : CFSG.Open.IsQuasisimple ↥K
  dvd : p ∣ Nat.card K
  norm : B ≤ Subgroup.normalizer (K : Set X)
  elem : IsElemAbelian p B
  sc : IsSCp p (K ⊔ B) B
  sub : A ≤ B
  noncyc : ¬ IsCyclic ↥A
  loc : IsCompLocallyBalanced p 1 A K
  comp : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
    GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J

theorem normal_subgroupOf_sup_sup {K W B : Subgroup X} (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hWK : W ≤ Subgroup.normalizer (K : Set X)) : (K.subgroupOf (K ⊔ W ⊔ B)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left.trans le_sup_left)).2
    (sup_le (sup_le Subgroup.le_normalizer hWK) hBK)

theorem local_step_S {p : ℕ} {K B A S : Subgroup X} (h : EngineHyp p K B A)
    (hSK : S ≤ Subgroup.normalizer (K : Set X)) (hSp : Nat.Coprime p (Nat.card S))
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) {a : X} (ha : a ∈ A) (ha1 : a ≠ 1) :
    (S ⊓ Subgroup.centralizer ({a} : Set X)) ⊓
        (⨅ (J : Subgroup X) (_ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J),
          Subgroup.normalizer (J : Set X)) ≤ Subgroup.centralizer (K : Set X) := by
  set W := S ⊓ Subgroup.centralizer ({a} : Set X) with hW
  have hWK : W ≤ Subgroup.normalizer (K : Set X) := inf_le_left.trans hSK
  have hWp : Nat.Coprime p (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hSp
  have hBa : ∀ b ∈ B, b ∈ Subgroup.centralizer ({a} : Set X) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2
      (CFSG.Open.IsElemAbelian.comm h.elem hb (h.sub ha))
  have hBW : B ≤ Subgroup.normalizer (W : Set X) := fun b hb =>
    mem_normalizer_inf (hBS hb) (Subgroup.le_normalizer (hBa b hb))
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm h.elem hx hy
  have hKX : K ≤ K ⊔ W ⊔ B := le_sup_left.trans le_sup_left
  exact local_step h.prime h.odd h.quasi h.dvd hKX (normal_subgroupOf_sup_sup h.norm hWK)
    le_sup_right (le_sup_right.trans le_sup_left) h.elem
    (isSCp_sup_of_isSCp h.prime h.elem h.norm hWK hWp hBW h.sc) h.sub ha ha1 h.loc
    (h.comp a ha ha1) hWK inf_le_right hWp hBW (commutator_mem_sup_sup hBab h.norm hBW)

theorem engine_comm {p : ℕ} {K B A S : Subgroup X} (h : EngineHyp p K B A)
    (hSK : S ≤ Subgroup.normalizer (K : Set X)) (hSp : Nat.Coprime p (Nat.card S))
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) : S ≤ commModC K B := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hAel : IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono h.elem h.sub
  haveI : IsElementaryAbelian p ↥A :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.isElementaryAbelian_of_isElemAbelian
      hAel
  have hcard : p ^ 2 ≤ Nat.card A := by
    obtain ⟨k, hk⟩ := i271_exists_card_eq h.prime hAel
    rw [hk]
    by_contra hlt
    have hk2 : k ≤ 1 := by
      by_contra hk2
      exact hlt (Nat.pow_le_pow_right h.prime.pos (by omega))
    apply h.noncyc
    interval_cases k
    · have : Nat.card A = 1 := by simpa using hk
      haveI : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.1 this).1
      exact isCyclic_of_subsingleton
    · haveI : Fact (Nat.card A).Prime := ⟨by simpa [hk] using h.prime⟩
      exact isCyclic_of_prime_card (p := Nat.card A) rfl
  have hgen := CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.le_iSup_centralizer_of_coprime
    (p := p) (A := A) (U := S) hcard ((Nat.Prime.coprime_iff_not_dvd h.prime).1 hSp)
    (fun x hx => hBS (h.sub hx))
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  intro w hw
  refine ⟨hSK hw.1, fun b hb => ?_⟩
  set W := S ⊓ Subgroup.centralizer ({a} : Set X) with hW
  have hBa : ∀ b ∈ B, b ∈ Subgroup.centralizer ({a} : Set X) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2
      (CFSG.Open.IsElemAbelian.comm h.elem hb (h.sub ha))
  have hBW : B ≤ Subgroup.normalizer (W : Set X) := fun b hb =>
    mem_normalizer_inf (hBS hb) (Subgroup.le_normalizer (hBa b hb))
  have hwN : w ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) :
      Set X) :=
    mem_normalizer_inf (hSK hw.1) (Subgroup.le_normalizer hw.2)
  refine local_step_S h hSK hSp hBS ha ha1 ⟨?_, ?_⟩
  ·
    have h1 : b * w⁻¹ * b⁻¹ ∈ W := by
      have := (Subgroup.mem_normalizer_iff.1 (hBW hb) w⁻¹).1 (W.inv_mem hw)
      exact this
    have : w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) := by group
    rw [this]
    exact W.mul_mem hw h1
  · refine Subgroup.mem_iInf.2 fun J => Subgroup.mem_iInf.2 fun hJ => ?_
    exact comm_mem_normalizer_component hwN hb (fun J' hJ' => (h.comp a ha ha1 J' hJ').1) hJ

theorem mem_normalizer_centralizer {K : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (K : Set X) : Subgroup X) : Set X) :=
  Subgroup.mem_normalizer_fintype fun _ hy => conj_mem_centralizer hg hy

theorem engine_full {p : ℕ} {K B A : Subgroup X} (h : EngineHyp p K B A)
    (hc : ∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
        (∀ b ∈ B, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X)) →
          ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
            w ∈ Subgroup.normalizer (J : Set X)) :
    IsStronglyBalancedIn p B K := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro S hSK hSp hBS'
  have hBS : B ≤ Subgroup.normalizer (S : Set X) := fun b hb => hBS' ⟨hb, h.norm hb⟩
  have hcomm := engine_comm h hSK hSp hBS
  obtain ⟨a, haA, ha1, hca⟩ := hc
  intro w hw
  set S0 := S ⊓ Subgroup.centralizer (K : Set X) with hS0
  have haB : a ∈ B := h.sub haA
  have hap : a ^ p = 1 := h.elem.2 a haB
  have haN : a ∈ Subgroup.normalizer (S0 : Set X) :=
    mem_normalizer_inf (hBS haB) (mem_normalizer_centralizer (h.norm haB))
  have hwN : w ∈ Subgroup.normalizer (S0 : Set X) :=
    mem_normalizer_inf (Subgroup.le_normalizer hw) (mem_normalizer_centralizer (hSK hw))
  have hu : w * a * w⁻¹ * a⁻¹ ∈ S0 := by
    refine ⟨?_, ((mem_commModC.1 (hcomm hw)).2 a haB)⟩
    have h1 : a * w⁻¹ * a⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (hBS haB) w⁻¹).1 (S.inv_mem hw)
      exact this
    have : w * a * w⁻¹ * a⁻¹ = w * (a * w⁻¹ * a⁻¹) := by group
    rw [this]
    exact S.mul_mem hw h1
  have hv : w⁻¹ * a * w * a⁻¹ ∈ S0 := by
    have h1 : a * w * a⁻¹ * w⁻¹ ∈ S0 := by
      have : a * w * a⁻¹ * w⁻¹ = (w * a * w⁻¹ * a⁻¹)⁻¹ := by group
      rw [this]
      exact S0.inv_mem hu
    have h2 := (Subgroup.mem_normalizer_iff.1 (inv_mem hwN) _).1 h1
    have : w⁻¹ * a * w * a⁻¹ = w⁻¹ * (a * w * a⁻¹ * w⁻¹) * w⁻¹⁻¹ := by group
    rw [this]
    exact h2
  have hT : ∀ x, w⁻¹ * x ∈ S0 ↔ w⁻¹ * (a * x * a⁻¹) ∈ S0 := by
    intro x
    have e1 : w⁻¹ * (a * x * a⁻¹) = (w⁻¹ * a * w * a⁻¹) * (a * (w⁻¹ * x) * a⁻¹) := by group
    rw [e1, Subgroup.mul_mem_cancel_left S0 hv]
    exact (Subgroup.mem_normalizer_iff.1 haN _)
  have hS0p : Nat.Coprime p (Nat.card S0) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hSp
  obtain ⟨x, hx1, hx2⟩ := exists_fixed_in_coset hap hS0p hT
  obtain ⟨c, hcS0, rfl⟩ : ∃ c ∈ S0, x = w * c := ⟨w⁻¹ * x, hx1, by group⟩
  have hxS : w * c ∈ S := S.mul_mem hw hcS0.1
  have hxN : w * c ∈ Subgroup.normalizer (K : Set X) :=
    Subgroup.mul_mem _ (hSK hw) (Subgroup.centralizer_le_normalizer (K : Set X) hcS0.2)
  have hxcop : Nat.Coprime p (orderOf (w * c)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard S hxS) hSp
  have hxcomm : ∀ b ∈ B, w * c * b * (w * c)⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
    intro b hb
    have h1 : c * b * c⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
      have : c * b * c⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hcS0.2
        (conj_mem_centralizer (h.norm hb) (Subgroup.inv_mem _ hcS0.2))
    have h2 := conj_mem_centralizer (hSK hw) h1
    have e : w * c * b * (w * c)⁻¹ * b⁻¹ =
        (w * (c * b * c⁻¹ * b⁻¹) * w⁻¹) * (w * b * w⁻¹ * b⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h2 ((mem_commModC.1 (hcomm hw)).2 b hb)
  have hJ := hca (w * c) hxN hxcop hxcomm
  have hxCa : w * c ∈ Subgroup.centralizer ({a} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hx2).symm
  have hxK := local_step_S h hSK hSp hBS haA ha1
    (show w * c ∈ (S ⊓ Subgroup.centralizer ({a} : Set X)) ⊓
        (⨅ (J : Subgroup X) (_ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J),
          Subgroup.normalizer (J : Set X)) from
      ⟨⟨hxS, hxCa⟩, Subgroup.mem_iInf.2 fun J => Subgroup.mem_iInf.2 fun hJ' => hJ J hJ'⟩)
  have : w = (w * c) * c⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ hxK (Subgroup.inv_mem _ hcS0.2)

end Engine

end CFSG.HardMathSupport.Dickson.I271
