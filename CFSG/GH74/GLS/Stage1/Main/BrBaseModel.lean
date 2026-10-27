module

public import CFSG.GH74.GLS.Stage1.Main.BrBaseFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped Pointwise

section ModelSylow

variable {Gs : Type} [Group Gs] [Finite Gs]

omit [Finite Gs] in
theorem isPGroup_zpowers_of_pow_four {x : Gs} (hx : x ^ 4 = 1) : IsPGroup 2 ↥(zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨2, ?_⟩
  apply Subtype.ext
  show (g : Gs) ^ (2 ^ 2) = 1
  have h4 : (x ^ k) ^ (4 : ℕ) = (x ^ (4 : ℕ)) ^ k := by
    rw [← zpow_natCast (x ^ k) 4, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  rw [← hk]
  show (x ^ k) ^ (4 : ℕ) = 1
  rw [h4, hx, one_zpow]

omit [Finite Gs] in
theorem mem_normalizer_zpowers_quat {a b z' : Gs} (haa : a * a = z') (hsq : z' * z' = 1)
    (hba : b * a = z' * (a * b)) (haz : a * z' = z' * a) :
    b ∈ normalizer (zpowers a : Set Gs) := by
  have hainv : a⁻¹ = a * z' := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, haa, hsq]
  have h1 : b * a * b⁻¹ = a⁻¹ := by
    rw [hainv]
    calc b * a * b⁻¹ = z' * (a * b) * b⁻¹ := by rw [hba]
      _ = z' * a := by group
      _ = a * z' := haz.symm
  have h2 : b⁻¹ * a * b = a⁻¹ := by
    have : a = b⁻¹ * a⁻¹ * b := by
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = b⁻¹ * a⁻¹ * b := by rw [h1]
    calc b⁻¹ * a * b = (b⁻¹ * a⁻¹ * b)⁻¹ := by group
      _ = a⁻¹ := by rw [← this]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
    rw [← hk, ← conj_zpow, h1, zpow_neg, inv_zpow]
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
    have hc : (b⁻¹ * a * b) ^ k = b⁻¹ * a ^ k * b := by
      have := conj_zpow (a := b⁻¹) (b := a) (i := k)
      simpa only [inv_inv] using this
    calc a ^ (-k) = (a⁻¹) ^ k := by rw [zpow_neg, inv_zpow]
      _ = (b⁻¹ * a * b) ^ k := by rw [h2]
      _ = b⁻¹ * a ^ k * b := hc
      _ = b⁻¹ * (b * h * b⁻¹) * b := by rw [hk]
      _ = h := by group

theorem quat_pair_in_sylow {q : ℕ} (hodd : Odd q) {z' : Gs} {S' E₁ E₂ : Subgroup Gs}
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 S' (centralizer ({z'} : Set Gs)))
    (hsl2 : HasSL2Model ↥E₁ (fun r => r = q)) (hz'sq : z' * z' = 1) (hz'1 : z' ≠ 1)
    (hinter : E₁ ⊓ E₂ = zpowers z') (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (hEz : IVK.Ez z' = E₁ ⊔ E₂) :
    ∃ a ∈ S', a ∈ E₁ ∧ ∃ b ∈ S', b ∈ E₁ ∧ a * a = z' ∧ b * b = z' ∧ b * a = z' * (a * b) := by
  obtain ⟨hz'E₁, hz'E₂⟩ : z' ∈ E₁ ∧ z' ∈ E₂ := by
    have : z' ∈ E₁ ⊓ E₂ := by rw [hinter]; exact mem_zpowers z'
    exact this
  obtain ⟨a₀, ha₀, b₀, hb₀, haa, hbb, hba⟩ :=
    exists_quat_pair hodd hsl2 hz'E₁ hz'sq hz'1 (fun x hx => hcomm x hx z' hz'E₂)
  have hz'a : a₀ * z' = z' * a₀ := hcomm a₀ ha₀ z' hz'E₂
  have ha4 : a₀ ^ 4 = 1 := by
    calc a₀ ^ 4 = (a₀ * a₀) * (a₀ * a₀) := by simp [pow_succ, mul_assoc]
      _ = z' * z' := by rw [haa]
      _ = 1 := hz'sq
  have hb4 : b₀ ^ 4 = 1 := by
    calc b₀ ^ 4 = (b₀ * b₀) * (b₀ * b₀) := by simp [pow_succ, mul_assoc]
      _ = z' * z' := by rw [hbb]
      _ = 1 := hz'sq
  have hQp : IsPGroup 2 ↥(zpowers b₀ ⊔ zpowers a₀) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_four hb4)
      (isPGroup_zpowers_of_pow_four ha4)
      (Subgroup.zpowers_le.2 (mem_normalizer_zpowers_quat haa hz'sq hba hz'a))
  have hQE : zpowers b₀ ⊔ zpowers a₀ ≤ E₁ :=
    sup_le (Subgroup.zpowers_le.2 hb₀) (Subgroup.zpowers_le.2 ha₀)
  have hEzC : IVK.Ez z' ≤ centralizer ({z'} : Set Gs) := Subgroup.map_subtype_le _
  have hCnorm : centralizer ({z'} : Set Gs) ≤ normalizer ((IVK.Ez z' : Subgroup Gs) : Set Gs) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact Ez_conj_mem hy hh
    · intro hh
      have := Ez_conj_mem (inv_mem hy) hh
      have e : y⁻¹ * (y * h * y⁻¹) * (y⁻¹)⁻¹ = h := by group
      rw [e] at this
      exact this
  have hS1 := hsyl.inf_of_le_normalizer hEzC hCnorm
  have hE₁Ez : E₁ ≤ IVK.Ez z' := by rw [hEz]; exact le_sup_left
  have hEzn : IVK.Ez z' ≤ normalizer (E₁ : Set Gs) := by
    intro y hy
    rw [hEz] at hy
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hy
    have h1 : e₁ ∈ normalizer (E₁ : Set Gs) := Subgroup.le_normalizer he₁
    have h2 : e₂ ∈ normalizer (E₁ : Set Gs) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hcomm h hh e₂ he₂
    exact mul_mem h1 h2
  have hS2 := hS1.inf_of_le_normalizer hE₁Ez hEzn
  rw [inf_assoc, inf_eq_right.2 hE₁Ez] at hS2
  obtain ⟨c, hcE, hcle⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
      hS2 hQp hQE
  have hcz : c⁻¹ * z' * c = z' := by
    have := hcomm c hcE z' hz'E₂
    calc c⁻¹ * z' * c = c⁻¹ * (z' * c) := by group
      _ = c⁻¹ * (c * z') := by rw [this]
      _ = z' := by group
  have ha : c⁻¹ * a₀ * c ∈ S' ⊓ E₁ :=
    hcle (CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate
      (Subgroup.mem_sup_right (mem_zpowers a₀)) c)
  have hb : c⁻¹ * b₀ * c ∈ S' ⊓ E₁ :=
    hcle (CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate
      (Subgroup.mem_sup_left (mem_zpowers b₀)) c)
  refine ⟨c⁻¹ * a₀ * c, ha.1, ha.2, c⁻¹ * b₀ * c, hb.1, hb.2, ?_, ?_, ?_⟩
  · calc c⁻¹ * a₀ * c * (c⁻¹ * a₀ * c) = c⁻¹ * (a₀ * a₀) * c := by group
      _ = z' := by rw [haa, hcz]
  · calc c⁻¹ * b₀ * c * (c⁻¹ * b₀ * c) = c⁻¹ * (b₀ * b₀) * c := by group
      _ = z' := by rw [hbb, hcz]
  · calc c⁻¹ * b₀ * c * (c⁻¹ * a₀ * c) = c⁻¹ * (b₀ * a₀) * c := by group
      _ = c⁻¹ * (z' * (a₀ * b₀)) * c := by rw [hba]
      _ = (c⁻¹ * z' * c) * ((c⁻¹ * a₀ * c) * (c⁻¹ * b₀ * c)) := by group
      _ = z' * ((c⁻¹ * a₀ * c) * (c⁻¹ * b₀ * c)) := by rw [hcz]

end ModelSylow

section ModelCases

variable {Gs : Type} [Group Gs] [Finite Gs]

omit [Finite Gs] in
theorem swap_case_false {z' u a : Gs} {S' E₁ E₂ : Subgroup Gs} (hinter : E₁ ⊓ E₂ = zpowers z')
    (hsq : z' * z' = 1) (hz'1 : z' ≠ 1) (hz'E₁ : z' ∈ E₁) (haS : a ∈ S') (haE : a ∈ E₁)
    (haa : a * a = z') (hu2 : u * u = 1) (huswap : E₁.map (MulAut.conj u).toMonoidHom = E₂)
    (hcomm : ∀ x ∈ S', x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * z') : False := by
  have hnotz : a ∉ zpowers z' := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers_sq hsq hmem with h | h
    · rw [h, mul_one] at haa
      exact hz'1 haa.symm
    · rw [h, hsq] at haa
      exact hz'1 haa.symm
  have hua : u * a * u⁻¹ ∈ E₂ := by
    rw [← huswap]
    exact ⟨a, haE, by simp [MulAut.conj_apply]⟩
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rcases hcomm a haS with h | h
  · have h' : a * u = u * a := by
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [h]
    have h3 : u * a * u⁻¹ = a := by
      rw [← h']
      group
    rw [h3] at hua
    have : a ∈ E₁ ⊓ E₂ := ⟨haE, hua⟩
    rw [hinter] at this
    exact hnotz this
  · have h' : a * u = u * z' * a := by
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * z' * a := by rw [h]
    have h3 : u * a * u⁻¹ = z' * a := by
      calc u * a * u⁻¹ = u * a * u := by rw [huinv]
        _ = u * (a * u) := by group
        _ = u * (u * z' * a) := by rw [h']
        _ = (u * u) * z' * a := by group
        _ = z' * a := by rw [hu2, one_mul]
    rw [h3] at hua
    have hza : z' * a ∈ E₁ ⊓ E₂ := ⟨E₁.mul_mem hz'E₁ haE, hua⟩
    rw [hinter] at hza
    apply hnotz
    have : a = z' * (z' * a) := by rw [← mul_assoc, hsq, one_mul]
    rw [this]
    exact mul_mem (mem_zpowers z') hza

end ModelCases

section ModelFix

variable {Gs : Type} [Group Gs] [Finite Gs]

omit [Finite Gs] in
theorem S_le_normalizer_inf {z' : Gs} {S' : Subgroup Gs} (hz'c : ∀ x ∈ S', x * z' = z' * x) :
    S' ≤ normalizer ((S' ⊓ IVK.Ez z' : Subgroup Gs) : Set Gs) := by
  have key : ∀ s ∈ S', ∀ h ∈ S' ⊓ IVK.Ez z', s * h * s⁻¹ ∈ S' ⊓ IVK.Ez z' := by
    intro s hs h hh
    refine ⟨S'.mul_mem (S'.mul_mem hs hh.1) (S'.inv_mem hs), ?_⟩
    exact Ez_conj_mem (Subgroup.mem_centralizer_singleton_iff.2 (hz'c s hs)) hh.2
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key s hs h hh
  · intro hh
    have := key s⁻¹ (S'.inv_mem hs) _ hh
    have e : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
    rw [e] at this
    exact this

theorem fix_case_false
    {q : ℕ} (hodd : Odd q) {z' t' w' u a b : Gs} {S' E₁ E₂ : Subgroup Gs}
    (hD : Dat410 q z' S' t' w' E₁ E₂) (hw1 : w' ≠ 1) (hsq : z' * z' = 1) (hz'1 : z' ≠ 1)
    (hz'c : ∀ x ∈ S', x * z' = z' * x) (haS : a ∈ S') (haE : a ∈ E₁) (hbS : b ∈ S')
    (hbE : b ∈ E₁) (haa : a * a = z') (hbb : b * b = z') (hba : b * a = z' * (a * b))
    (huS : u ∈ S') (huE : u ∉ IVK.Ez z') (hu2 : u * u = 1)
    (hunorm : u ∈ normalizer (E₁ : Set Gs))
    (hcomm : ∀ x ∈ S', x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * z') : False := by
  obtain ⟨hz'E₁, hz'E₂⟩ : z' ∈ E₁ ∧ z' ∈ E₂ := by
    have : z' ∈ E₁ ⊓ E₂ := by rw [hD.inter_E]; exact mem_zpowers z'
    exact this
  have hcommE := hD.comm_E
  have hEz := hD.Ez_eq
  have hw2 : w' * w' = 1 := by
    have ho : orderOf w' = 2 := hD.w_ord.resolve_left hw1
    have := pow_orderOf_eq_one w'
    rwa [ho, pow_two] at this
  have hw'S : w' ∈ S' := hD.w_mem
  have hw'N : w' ∈ normalizer (E₁ : Set Gs) := by
    have : w' ∈ normalizer (E₁ : Set Gs) ⊓ S' := by
      rw [hD.norm_E]
      exact Subgroup.mem_sup_right (mem_zpowers w')
    exact this.1
  have hu : u ∈ (S' ⊓ IVK.Ez z') ⊔ zpowers w' := by
    rw [← hD.norm_E]
    exact ⟨hunorm, huS⟩
  have hwle : zpowers w' ≤ normalizer ((S' ⊓ IVK.Ez z' : Subgroup Gs) : Set Gs) :=
    Subgroup.zpowers_le.2 (S_le_normalizer_inf hz'c hw'S)
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (S' ⊓ IVK.Ez z') (zpowers w') hwle
  have hu' : u ∈ ((S' ⊓ IVK.Ez z' : Subgroup Gs) : Set Gs) * (zpowers w' : Set Gs) := by
    rw [← hmul]
    exact hu
  obtain ⟨p, hp, r, hr, hpr⟩ := Set.mem_mul.1 hu'
  have hpEz : p ∈ IVK.Ez z' := hp.2
  rcases eq_one_or_eq_of_mem_zpowers_sq hw2 hr with hr1 | hrw
  · exfalso
    apply huE
    rw [← hpr, hr1, mul_one]
    exact hpEz
  rw [hrw] at hpr
  rw [hEz] at hpEz
  obtain ⟨e₁, he₁, e₂, he₂, hpe⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcommE hpEz
  have hu_eq : u = e₁ * e₂ * w' := by rw [← hpr, hpe]
  have hact : ∀ x ∈ E₁, u * x * u⁻¹ = (e₁ * w') * x * (e₁ * w')⁻¹ := by
    intro x hx
    have hy : w' * x * w'⁻¹ ∈ E₁ := (Subgroup.mem_normalizer_iff.1 hw'N x).1 hx
    have h2 : e₂ * (w' * x * w'⁻¹) * e₂⁻¹ = w' * x * w'⁻¹ := by
      have := hcommE _ hy e₂ he₂
      calc e₂ * (w' * x * w'⁻¹) * e₂⁻¹ = (e₂ * (w' * x * w'⁻¹)) * e₂⁻¹ := by group
        _ = ((w' * x * w'⁻¹) * e₂) * e₂⁻¹ := by rw [← this]
        _ = w' * x * w'⁻¹ := by group
    calc u * x * u⁻¹ = e₁ * (e₂ * (w' * x * w'⁻¹) * e₂⁻¹) * e₁⁻¹ := by rw [hu_eq]; group
      _ = e₁ * (w' * x * w'⁻¹) * e₁⁻¹ := by rw [h2]
      _ = (e₁ * w') * x * (e₁ * w')⁻¹ := by group
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hux : ∀ x ∈ S', u * x * u⁻¹ = x ∨ u * x * u⁻¹ = z' * x := by
    intro x hx
    rcases hcomm x hx with h | h
    · left
      have h' : x * u = u * x := by
        calc x * u = (x * u * x⁻¹) * x := by group
          _ = u * x := by rw [h]
      rw [← h']
      group
    · right
      have h' : x * u = u * z' * x := by
        calc x * u = (x * u * x⁻¹) * x := by group
          _ = u * z' * x := by rw [h]
      calc u * x * u⁻¹ = u * x * u := by rw [huinv]
        _ = u * (x * u) := by group
        _ = u * (u * z' * x) := by rw [h']
        _ = (u * u) * z' * x := by group
        _ = z' * x := by rw [hu2, one_mul]
  obtain ⟨hN, hP⟩ := hD.pgl hw1 E₁ (by simp)
  set A : Subgroup Gs := E₁ ⊔ zpowers w' with hA
  have hE₁A : E₁ ≤ A := le_sup_left
  have hz'A : z' ∈ A := hE₁A hz'E₁
  have hmkone : ∀ (g : Gs) (hg : g ∈ A),
      (QuotientGroup.mk (⟨g, hg⟩ : ↥A) : ↥A ⧸ (zpowers z').subgroupOf A) = 1 ↔ g ∈ zpowers z' := by
    intro g hg
    rw [QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hnotz : ∀ g : Gs, g * g = z' → g ∉ zpowers z' := by
    intro g hg hmem
    rcases eq_one_or_eq_of_mem_zpowers_sq hsq hmem with h | h
    · rw [h, mul_one] at hg
      exact hz'1 hg.symm
    · rw [h, hsq] at hg
      exact hz'1 hg.symm
  have haA : a ∈ A := hE₁A haE
  have hbA : b ∈ A := hE₁A hbE
  set x : ↥A ⧸ (zpowers z').subgroupOf A := QuotientGroup.mk ⟨a, haA⟩ with hx
  set y : ↥A ⧸ (zpowers z').subgroupOf A := QuotientGroup.mk ⟨b, hbA⟩ with hy
  have hzmk : (QuotientGroup.mk (⟨z', hz'A⟩ : ↥A) : ↥A ⧸ (zpowers z').subgroupOf A) = 1 :=
    (hmkone z' hz'A).2 (mem_zpowers z')
  have hxx : x * x = 1 := by
    rw [hx, ← QuotientGroup.mk_mul]
    have : (⟨a, haA⟩ * ⟨a, haA⟩ : ↥A) = ⟨z', hz'A⟩ := Subtype.ext haa
    rw [this]
    exact hzmk
  have hyy : y * y = 1 := by
    rw [hy, ← QuotientGroup.mk_mul]
    have : (⟨b, hbA⟩ * ⟨b, hbA⟩ : ↥A) = ⟨z', hz'A⟩ := Subtype.ext hbb
    rw [this]
    exact hzmk
  have hx1 : x ≠ 1 := fun h => hnotz a haa ((hmkone a haA).1 h)
  have hy1 : y ≠ 1 := fun h => hnotz b hbb ((hmkone b hbA).1 h)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  have hxy : x * y = y * x := by
    have h1 : (⟨b, hbA⟩ * ⟨a, haA⟩ : ↥A) = ⟨z', hz'A⟩ * (⟨a, haA⟩ * ⟨b, hbA⟩) := Subtype.ext hba
    have h2 : (QuotientGroup.mk (⟨b, hbA⟩ * ⟨a, haA⟩ : ↥A) :
        ↥A ⧸ (zpowers z').subgroupOf A) = QuotientGroup.mk (⟨a, haA⟩ * ⟨b, hbA⟩ : ↥A) := by
      rw [h1, QuotientGroup.mk_mul, hzmk, one_mul]
    rw [hx, hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact h2.symm
  have hne : x ≠ y := by
    intro h
    rw [hx, hy, QuotientGroup.eq] at h
    have h' : a⁻¹ * b ∈ zpowers z' := h
    have hcab : b * a = a * b := by
      rcases eq_one_or_eq_of_mem_zpowers_sq hsq h' with h1 | h1
      · have hb' : b = a := by
          calc b = a * (a⁻¹ * b) := by group
            _ = a := by rw [h1, mul_one]
        rw [hb']
      · have hb' : b = a * z' := by
          calc b = a * (a⁻¹ * b) := by group
            _ = a * z' := by rw [h1]
        have hza : a * z' = z' * a := hcommE a haE z' hz'E₂
        rw [hb']
        calc a * z' * a = a * (z' * a) := by group
          _ = a * (a * z') := by rw [hza]
    have hab : a * b = z' * (a * b) := by
      calc a * b = b * a := hcab.symm
        _ = z' * (a * b) := hba
    exact hz'1 (mul_right_cancel (show z' * (a * b) = 1 * (a * b) by rw [one_mul]; exact hab.symm))
  have hu'A : e₁ * w' ∈ A := A.mul_mem (hE₁A he₁) (Subgroup.mem_sup_right (mem_zpowers w'))
  set c : ↥A ⧸ (zpowers z').subgroupOf A := QuotientGroup.mk ⟨e₁ * w', hu'A⟩ with hc
  have hact' : ∀ g ∈ E₁, (e₁ * w') * g * (e₁ * w')⁻¹ = u * g * u⁻¹ := fun g hg => (hact g hg).symm
  have hcomm_aux : ∀ (g : Gs) (hgA : g ∈ A) (hgE : g ∈ E₁) (hgS : g ∈ S'),
      c * QuotientGroup.mk ⟨g, hgA⟩ = QuotientGroup.mk ⟨g, hgA⟩ * c := by
    intro g hgA hgE hgS
    rw [hc, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rcases hux g hgS with h | h
    · have h1 : (e₁ * w') * g = g * (e₁ * w') := by
        calc (e₁ * w') * g = ((e₁ * w') * g * (e₁ * w')⁻¹) * (e₁ * w') := by group
          _ = g * (e₁ * w') := by rw [hact' g hgE, h]
      have : (⟨e₁ * w', hu'A⟩ * ⟨g, hgA⟩ : ↥A) = ⟨g, hgA⟩ * ⟨e₁ * w', hu'A⟩ := Subtype.ext h1
      rw [this]
    · have h1 : (e₁ * w') * g = z' * g * (e₁ * w') := by
        calc (e₁ * w') * g = ((e₁ * w') * g * (e₁ * w')⁻¹) * (e₁ * w') := by group
          _ = z' * g * (e₁ * w') := by rw [hact' g hgE, h]
      have : (⟨e₁ * w', hu'A⟩ * ⟨g, hgA⟩ : ↥A) =
          ⟨z', hz'A⟩ * (⟨g, hgA⟩ * ⟨e₁ * w', hu'A⟩) := Subtype.ext (by
        show (e₁ * w') * g = z' * (g * (e₁ * w'))
        rw [h1, mul_assoc])
      rw [this, QuotientGroup.mk_mul, hzmk, one_mul]
  have hcx : c * x = x * c := hcomm_aux a haA haE haS
  have hcy : c * y = y * c := hcomm_aux b hbA hbE hbS
  have hcl := kfour_apply hodd hP hxo hyo hxy hne hcx hcy
  have hmem : c ∈ (E₁.subgroupOf A).map (QuotientGroup.mk' ((zpowers z').subgroupOf A)) := by
    have hle : Subgroup.closure ({x, y} : Set (↥A ⧸ (zpowers z').subgroupOf A)) ≤
        (E₁.subgroupOf A).map (QuotientGroup.mk' ((zpowers z').subgroupOf A)) := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact ⟨⟨a, haA⟩, haE, rfl⟩
      · exact ⟨⟨b, hbA⟩, hbE, rfl⟩
    exact hle hcl
  obtain ⟨e, he, hec⟩ := hmem
  have hec' : (QuotientGroup.mk e : ↥A ⧸ (zpowers z').subgroupOf A) =
      QuotientGroup.mk ⟨e₁ * w', hu'A⟩ := hec
  rw [QuotientGroup.eq] at hec'
  have h3 : (e : Gs)⁻¹ * (e₁ * w') ∈ zpowers z' := hec'
  have h4 : (e : Gs)⁻¹ * (e₁ * w') ∈ E₁ := Subgroup.zpowers_le.2 hz'E₁ h3
  have heE : (e : Gs) ∈ E₁ := he
  have h5 : e₁ * w' ∈ E₁ := by
    have : e₁ * w' = (e : Gs) * ((e : Gs)⁻¹ * (e₁ * w')) := by group
    rw [this]
    exact E₁.mul_mem heE h4
  have h6 : w' ∈ E₁ := by
    have : w' = e₁⁻¹ * (e₁ * w') := by group
    rw [this]
    exact E₁.mul_mem (E₁.inv_mem he₁) h5
  have h7 : w' ∈ IVK.Ez z' := by
    rw [hEz]
    exact Subgroup.mem_sup_left h6
  have h8 : w' ∈ IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') :=
    ⟨h7, Subgroup.mem_sup_right (mem_zpowers w')⟩
  rw [hD.inter, Subgroup.mem_bot] at h8
  exact hw1 h8

end ModelFix

section ModelMain

variable {Gs : Type} [Group Gs] [Finite Gs]

theorem model_normal_four_le
    {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q) {z' t' w' : Gs}
    {S' V E₁ E₂ : Subgroup Gs} (hSp : IsPGroup 2 ↥S')
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 S' (centralizer ({z'} : Set Gs)))
    (hz'o : orderOf z' = 2) (hz'c : ∀ x ∈ S', x * z' = z' * x)
    (hctr : (center ↥S').map S'.subtype = zpowers z') (hD : Dat410 q z' S' t' w' E₁ E₂)
    (hVS : V ≤ S') (hV4 : IVK.IsFourSubgroup V) (hVn : ∀ s ∈ S', ∀ v ∈ V, s * v * s⁻¹ ∈ V) :
    V ≤ IVK.Ez z' := by
  have hsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'o, pow_two] at this
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'o
    omega
  obtain ⟨hz'E₁, hz'E₂⟩ : z' ∈ E₁ ∧ z' ∈ E₂ := by
    have : z' ∈ E₁ ⊓ E₂ := by rw [hD.inter_E]; exact mem_zpowers z'
    exact this
  have hz'Ez : z' ∈ IVK.Ez z' := by
    rw [hD.Ez_eq]
    exact Subgroup.mem_sup_left hz'E₁
  intro u huV
  by_contra huE
  have hz'V : z' ∈ V := z_mem_four hSp hVS hV4 hVn hctr hsq
  have hu1 : u ≠ 1 := fun h => huE (h ▸ one_mem _)
  have huz : u ≠ z' := fun h => huE (h ▸ hz'Ez)
  have hu2 : u * u = 1 := by
    have : IsElementaryAbelian 2 ↥V := hV4.1
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) u huV
    rwa [pow_two] at h2
  have hcomm := four_conj hz'V huV hV4 hsq hz'1 hu1 huz hVn hz'c
  obtain ⟨a, haS, haE, b, hbS, hbE, haa, hbb, hba⟩ :=
    quat_pair_in_sylow hodd hsyl hD.sl2 hsq hz'1 hD.inter_E hD.comm_E hD.Ez_eq
  have hq₁ : IsQuasisimple ↥E₁ := quasi_of_hasSL2 h5 hD.sl2
  have hq₂ : IsQuasisimple ↥E₂ := by
    rw [hD.E₂_eq]
    exact (isQuasisimple_congr (E₁.equivMapOfInjective _ (MulAut.conj t').injective)).1 hq₁
  have huS : u ∈ S' := hVS huV
  have huC : u ∈ centralizer ({z'} : Set Gs) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hz'c u huS)
  rcases conj_perm hq₁ hq₂ hD.Ez_eq hD.comm_E huC with hfix | hswap
  · have hunorm : u ∈ normalizer (E₁ : Set Gs) := mem_normalizer_of_map_eq hfix
    by_cases hw1 : w' = 1
    · apply huE
      have hh : u ∈ normalizer (E₁ : Set Gs) ⊓ S' := ⟨hunorm, huS⟩
      rw [hD.norm_E, hw1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hh
      exact hh.2
    · exact fix_case_false hodd hD hw1 hsq hz'1 hz'c haS haE hbS hbE haa hbb hba huS huE hu2
        hunorm hcomm
  · exact swap_case_false hD.inter_E hsq hz'1 hz'E₁ haS haE haa hu2 hswap hcomm

end ModelMain

end CFSG.GH74.GLS.Stage1.Main
