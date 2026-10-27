module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
import CFSG.GH74.Generic.BProg.B2.GenLocL2SL
import CFSG.GH74.Generic.BProg.B2.GenLocG2SL2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup
open scoped MatrixGroups

namespace GenLocG2Inner

section Klein

variable {X : Type} [Group X] {a b : X}

theorem klein_aab (ha : a * a = 1) : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]

theorem klein_bab (hb : b * b = 1) (hc : a * b = b * a) : b * (a * b) = a := by
  rw [← mul_assoc, ← hc, mul_assoc, hb, mul_one]

theorem klein_aba (ha : a * a = 1) (hc : a * b = b * a) : a * b * a = b := by
  rw [mul_assoc, ← hc, ← mul_assoc, ha, one_mul]

theorem klein_abb (hb : b * b = 1) : a * b * b = a := by rw [mul_assoc, hb, mul_one]

theorem klein_abab (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) : a * b * (a * b) = 1 := by
  rw [← mul_assoc, klein_aba ha hc, hb]

@[expose] def kleinSub (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) : Subgroup X where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, hc.symm, klein_aab ha, klein_bab hb hc, klein_aba ha hc, klein_abb hb,
        klein_abab ha hb hc]
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · right; left; exact inv_eq_of_mul_eq_one_right ha
    · right; right; left; exact inv_eq_of_mul_eq_one_right hb
    · right; right; right
      exact inv_eq_of_mul_eq_one_right (klein_abab ha hb hc)

theorem mem_kleinSub (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) {x : X} :
    x ∈ kleinSub ha hb hc ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem isEA_kleinSub (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) :
    CFSG.IsElementaryAbelian 2 ↥(kleinSub ha hb hc) := by
  refine CFSG.GH74.Generic.BProg.B2.WeakSigGen.isElementaryAbelian_of_forall (U := kleinSub ha hb hc)
    ?_ ?_
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, hc.symm, klein_aab ha, klein_bab hb hc, klein_aba ha hc, klein_abb hb,
        klein_abab ha hb hc]
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact ha
    · exact hb
    · exact klein_abab ha hb hc

theorem card_kleinSub_le (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) :
    Nat.card ↥(kleinSub ha hb hc) ≤ 4 := by
  classical
  change Nat.card ((kleinSub ha hb hc : Subgroup X) : Set X) ≤ 4
  rw [Nat.card_coe_set_eq]
  have hsub : ((kleinSub ha hb hc : Subgroup X) : Set X) ⊆ {1, a, b, a * b} := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
  rw [Set.ncard_singleton]

theorem card_kleinSub (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) (h1 : a ≠ 1)
    (h2 : b ≠ 1) (h3 : a ≠ b) : Nat.card ↥(kleinSub ha hb hc) = 4 := by
  classical
  have h4 : a * b ≠ 1 := fun h => h3 (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right ha])
  have h5 : a * b ≠ a := fun h => h2 (by simpa using h)
  have h6 : a * b ≠ b := fun h => h1 (by simpa using h)
  have e : ((kleinSub ha hb hc : Subgroup X) : Set X) = ↑({1, a, b, a * b} : Finset X) := by
    ext x
    simp [mem_kleinSub ha hb hc]
  change Nat.card ((kleinSub ha hb hc : Subgroup X) : Set X) = 4
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  all_goals simp [h3, h1.symm, h2.symm, h4.symm, h5.symm, h6.symm]

end Klein


section Core

variable {X : Type} [Group X] [Finite X]

open CFSG.GH74.Generic.BProg.B2.GenLocL2SL in
theorem normalSL2_le_sup_centralizers {F : Type} [Field F] [Finite F]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h11 : 11 ≤ p ^ f)
    (K : Subgroup X) [K.Normal] (e : ↥K ≃* SL(2, F))
    {u₁ u₂ : X} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (hc : u₁ * u₂ = u₂ * u₁)
    (hn₁ : u₁ ≠ 1) (hn₂ : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    K ≤ centralizer ({u₁} : Set X) ⊔ centralizer ({u₂} : Set X) ⊔
      centralizer ({u₁ * u₂} : Set X) := by
  classical
  set U := kleinSub h₁ h₂ hc with hU
  have hA : CFSG.IsElementaryAbelian 2 ↥U := isEA_kleinSub h₁ h₂ hc
  have h4 : Nat.card ↥U = 4 := card_kleinSub h₁ h₂ hc hn₁ hn₂ hne
  let α : ↥U →* MulAut SL(2, F) :=
    (MulAut.congr e).toMonoidHom.comp ((MulAut.conjNormal (H := K)).comp U.subtype)
  have hα : ∀ (c : ↥U) (k : ↥K), α c (e k) = e (MulAut.conjNormal (c : X) k) := by
    intro c k
    simp [α, MulAut.congr_apply]
  have hcore := gammaAct_sl2_core hp hp2 hF (by omega) hA h4 α
  have htop : gammaAct α = ⊤ := by
    rcases hcore with h | ⟨h, -⟩
    · exact h
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      omega
  set Y := centralizer ({u₁} : Set X) ⊔ centralizer ({u₂} : Set X) ⊔
      centralizer ({u₁ * u₂} : Set X) with hY
  have hcen : ∀ c : X, c ∈ U → c ≠ 1 → centralizer ({c} : Set X) ≤ Y := by
    intro c hcU hc1
    rcases (mem_kleinSub h₁ h₂ hc).1 hcU with rfl | rfl | rfl | rfl
    · exact absurd rfl hc1
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  let φ : SL(2, F) →* X := K.subtype.comp e.symm.toMonoidHom
  have hle : gammaAct α ≤ Y.comap φ := by
    refine iSup₂_le fun E hE => ?_
    intro x hx
    have hidx : E.index ≤ 2 := (GenLocBasic.adm_iff_index hA E).1 hE
    obtain ⟨c, hcE, hc1⟩ : ∃ c ∈ E, c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : E = ⊥ := eq_bot_iff.2 fun c hc => (mem_bot).2 (hcon c hc)
      rw [this, index_bot, h4] at hidx
      omega
    have hfix : α c x = x := (GenLocBasic.mem_fixedIn_map α E x).1 hx c hcE
    have hxk : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hxk, hα] at hfix
    have hk : MulAut.conjNormal (c : X) (e.symm x) = e.symm x := e.injective hfix
    have hk' : (c : X) * (e.symm x : X) * (c : X)⁻¹ = (e.symm x : X) := by
      rw [← MulAut.conjNormal_apply]; exact congrArg Subtype.val hk
    have hmem : (e.symm x : X) ∈ centralizer ({(c : X)} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      symm
      calc (c : X) * (e.symm x : X) = (c : X) * (e.symm x : X) * (c : X)⁻¹ * (c : X) := by group
        _ = (e.symm x : X) * (c : X) := by rw [hk']
    exact hcen (c : X) c.2 (fun h => hc1 (Subtype.ext h)) hmem
  intro k hk
  have hek : e ⟨k, hk⟩ ∈ gammaAct α := htop ▸ Subgroup.mem_top _
  have := hle hek
  simpa [φ] using this

end Core


section ShapeFacts

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

variable {X : Type} [Group X] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape X F₁ F₂)

theorem z_comm_I₁ {i : X} (hi : i ∈ S.I₁) : S.z * i = i * S.z := by
  have h := Subgroup.mem_center_iff.1 (neg_one_mem_center (F := F₁)) (S.e₁ ⟨i, hi⟩)
  have : S.e₁ (⟨S.z, S.z_mem₁⟩ * ⟨i, hi⟩) = S.e₁ (⟨i, hi⟩ * ⟨S.z, S.z_mem₁⟩) := by
    rw [map_mul, map_mul, S.e₁_z]; exact h.symm
  exact congrArg Subtype.val (S.e₁.injective this)

theorem z_comm_I₂ {i : X} (hi : i ∈ S.I₂) : S.z * i = i * S.z := by
  have h := Subgroup.mem_center_iff.1 (neg_one_mem_center (F := F₂)) (S.e₂ ⟨i, hi⟩)
  have : S.e₂ (⟨S.z, S.z_mem₂⟩ * ⟨i, hi⟩) = S.e₂ (⟨i, hi⟩ * ⟨S.z, S.z_mem₂⟩) := by
    rw [map_mul, map_mul, S.e₂_z]; exact h.symm
  exact congrArg Subtype.val (S.e₂.injective this)

theorem z_comm_t : S.z * S.t = S.t * S.z := by
  obtain ⟨y, hy, hey⟩ := S.act₁ ⟨S.z, S.z_mem₁⟩
  have hyz : y = ⟨S.z, S.z_mem₁⟩ := by
    apply S.e₁.injective
    apply Subtype.ext
    rw [hey, S.e₁_z, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    simp
  have h2 : S.z = S.t * S.z * S.t⁻¹ := by
    have := congrArg Subtype.val hyz
    rw [hy] at this
    exact this.symm
  calc S.z * S.t = S.t * S.z * S.t⁻¹ * S.t := by rw [← h2]
    _ = S.t * S.z := by group

theorem z_comm (x : X) : S.z * x = x * S.z := by
  have hle : (⊤ : Subgroup X) ≤ centralizer ({S.z} : Set X) := by
    rw [← S.gen]
    refine sup_le (sup_le (fun i hi => ?_) (fun i hi => ?_)) ?_
    · rw [mem_centralizer_singleton_iff]; exact (z_comm_I₁ S hi).symm
    · rw [mem_centralizer_singleton_iff]; exact (z_comm_I₂ S hi).symm
    · rw [Subgroup.zpowers_le, mem_centralizer_singleton_iff]; exact (z_comm_t S).symm
  have := hle (Subgroup.mem_top x)
  rw [mem_centralizer_singleton_iff] at this
  exact this.symm

end ShapeFacts


section NFacts

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

variable {X : Type} [Group X] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape X F₁ F₂)

theorem mem_N_or_mul_t (x : X) : x ∈ S.I₁ ⊔ S.I₂ ∨ x * S.t ∈ S.I₁ ⊔ S.I₂ := by
  have := S.normal₁
  have := S.normal₂
  have hx : x ∈ (S.I₁ ⊔ S.I₂) ⊔ Subgroup.zpowers S.t := by rw [S.gen]; exact Subgroup.mem_top x
  obtain ⟨h, hh, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  rcases mem_zpowers_of_sq S.t_sq hk with rfl | rfl
  · left; simpa using hh
  · right; rw [mul_assoc, S.t_sq, mul_one]; exact hh

theorem mul_mem_N_of_not_mem {x y : X} (hx : x ∉ S.I₁ ⊔ S.I₂) (hy : y ∉ S.I₁ ⊔ S.I₂) :
    x * y ∈ S.I₁ ⊔ S.I₂ := by
  have := S.normal₁
  have := S.normal₂
  have hxt : x * S.t ∈ S.I₁ ⊔ S.I₂ := (mem_N_or_mul_t S x).resolve_left hx
  have hyt : y * S.t ∈ S.I₁ ⊔ S.I₂ := (mem_N_or_mul_t S y).resolve_left hy
  have h1 : S.t * (y * S.t) * S.t⁻¹ ∈ S.I₁ ⊔ S.I₂ := (inferInstance : (S.I₁ ⊔ S.I₂).Normal).conj_mem _ hyt S.t
  have h2 : x * y = (x * S.t) * (S.t * (y * S.t) * S.t⁻¹) := by
    calc x * y = x * (S.t * S.t) * y := by rw [S.t_sq, mul_one]
      _ = (x * S.t) * (S.t * (y * S.t) * S.t⁻¹) := by group
  rw [h2]
  exact (S.I₁ ⊔ S.I₂).mul_mem hxt h1

theorem eq_top_of_N_le {Y : Subgroup X} (hN : S.I₁ ⊔ S.I₂ ≤ Y) {x : X} (hx : x ∈ Y)
    (hxN : x ∉ S.I₁ ⊔ S.I₂) : Y = ⊤ := by
  have := S.normal₁
  have := S.normal₂
  rw [eq_top_iff]
  intro y _
  have hxt : x * S.t ∈ Y := by
    rcases mem_N_or_mul_t S x with h | h
    · exact absurd h hxN
    · exact hN h
  have ht : S.t ∈ Y := by
    have := Y.mul_mem (Y.inv_mem hx) hxt
    simpa using this
  rcases mem_N_or_mul_t S y with h | h
  · exact hN h
  · have := Y.mul_mem (hN h) ht
    rwa [mul_assoc, S.t_sq, mul_one] at this

theorem e₁_t_conj {i : X} (hi : i ∈ S.I₁) (hi' : S.t * i * S.t⁻¹ ∈ S.I₁) :
    S.e₁ ⟨S.t * i * S.t⁻¹, hi'⟩ = conjSLAut S.g₁ (S.e₁ ⟨i, hi⟩) := by
  obtain ⟨y, hy, hey⟩ := conjData_iff.1 S.act₁ ⟨i, hi⟩
  have : y = ⟨S.t * i * S.t⁻¹, hi'⟩ := Subtype.ext hy
  rw [← this]; exact hey


section L3Step

variable [Finite F₁] {p f : ℕ} [Fact p.Prime]

theorem exists_conj_fix (hF : Nat.card F₁ = p ^ f) (hp2 : p ≠ 2) {a : X} (ha : a ∈ S.I₁)
    (hord : orderOf (S.e₁ ⟨a, ha⟩) = 4) : ∃ i ∈ S.I₁, S.t * (i * a * i⁻¹) * S.t⁻¹ = a := by
  set A := S.e₁ ⟨a, ha⟩ with hA
  have hA' : orderOf (conjSLAut S.g₁⁻¹ A) = 4 := by
    rw [MulEquiv.orderOf_eq]; exact hord
  obtain ⟨c, hc⟩ := isConj_iff.1 (sl2_order_four_isConj hF hp2 hord hA')
  set i : S.I₁ := S.e₁.symm c with hi
  refine ⟨i, i.2, ?_⟩
  have hj : (i : X) * a * (i : X)⁻¹ ∈ S.I₁ :=
    S.I₁.mul_mem (S.I₁.mul_mem i.2 ha) (S.I₁.inv_mem i.2)
  have hjv : S.e₁ ⟨(i : X) * a * (i : X)⁻¹, hj⟩ = conjSLAut S.g₁⁻¹ A := by
    have h1 : (⟨(i : X) * a * (i : X)⁻¹, hj⟩ : S.I₁) = i * ⟨a, ha⟩ * i⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hi, MulEquiv.apply_symm_apply]
    exact hc
  have ht : S.t * ((i : X) * a * (i : X)⁻¹) * S.t⁻¹ ∈ S.I₁ := S.act₁.conj_mem hj
  have h2 := e₁_t_conj S hj ht
  rw [hjv] at h2
  have h3 : conjSLAut S.g₁ (conjSLAut S.g₁⁻¹ A) = A := cf_cf_inv S.g₁ A
  have h4 : (⟨S.t * ((i : X) * a * (i : X)⁻¹) * S.t⁻¹, ht⟩ : S.I₁) = ⟨a, ha⟩ :=
    S.e₁.injective (h2.trans h3)
  exact congrArg Subtype.val h4

end L3Step


section Sq

theorem eq_one_or_z_of_sq₁ (h2 : (2 : F₁) ≠ 0) {a : X} (ha : a ∈ S.I₁) (hsq : a * a = 1) :
    a = 1 ∨ a = S.z := by
  have hA : (S.e₁ ⟨a, ha⟩) ^ 2 = 1 := by
    rw [← map_pow, pow_two]
    have : (⟨a, ha⟩ : S.I₁) * ⟨a, ha⟩ = 1 := Subtype.ext hsq
    rw [this, map_one]
  by_cases h1 : S.e₁ ⟨a, ha⟩ = 1
  · left
    have : (⟨a, ha⟩ : S.I₁) = 1 := S.e₁.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · right
    have h3 := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ hA h1
    have h4 : S.e₁ ⟨a, ha⟩ = S.e₁ ⟨S.z, S.z_mem₁⟩ := by
      rw [S.e₁_z]
      apply Subtype.ext
      rw [h3, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    exact congrArg Subtype.val (S.e₁.injective h4)

end Sq


section Fix

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] (T : Shape X F F)

theorem exists_mem_centralizer_not_mem_N (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {u : X}
    (hu : u * u = 1) (huN : u ∈ T.I₁ ⊔ T.I₂) (hu1 : u ≠ 1) (huz : u ≠ T.z) :
    ∃ x ∈ centralizer ({u} : Set X), x ∉ T.I₁ ⊔ T.I₂ := by
  have h2 : (2 : F) ≠ 0 := by
    have : Fintype F := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
    have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
    exact Ring.two_ne_zero hchar
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute T.comm huN
  have hba : b * a = a * b := (T.comm a ha b hb).symm
  have hsq : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hba]
      _ = a * b * (a * b) := by group
      _ = 1 := hu
  have hmem : a * a ∈ T.I₁ ⊓ T.I₂ := by
    refine ⟨T.I₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact T.I₂.inv_mem (T.I₂.mul_mem hb hb)
  rw [T.inter] at hmem
  rcases mem_zpowers_of_sq T.z_sq hmem with h1 | h1
  ·
    exfalso
    have hb1 : b * b = 1 := by rw [h1, one_mul] at hsq; exact hsq
    rcases eq_one_or_z_of_sq₁ T h2 ha h1 with h | h <;>
      rcases eq_one_or_z_of_sq₁ T.swap h2 hb hb1 with h' | h'
    · exact hu1 (by rw [h, h', one_mul])
    · have h'' : b = T.z := h'
      exact huz (by rw [h, h'', one_mul])
    · have h'' : b = 1 := h'
      exact huz (by rw [h, h'', mul_one])
    · have h'' : b = T.z := h'
      exact hu1 (by rw [h, h'']; exact T.z_sq)
  ·
    have hb2 : b * b = T.z := by
      have : b * b = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right hsq
      rw [this, h1]
      exact inv_eq_of_mul_eq_one_right T.z_sq
    have hne1 : (-1 : SL(2, F)) ≠ 1 := by
      intro h
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp at this
      apply h2
      linear_combination -this
    have hord : ∀ {K : Type} [Field K] (A : SL(2, K)), A ^ 2 = -1 → (-1 : SL(2, K)) ≠ 1 →
        orderOf A = 4 := by
      intro K _ A hA hne
      have h4 : A ^ 2 ^ (1 + 1) = 1 := by
        rw [pow_succ 2 1, pow_one, pow_mul, hA]; simp
      exact (orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [hA] using hne) h4)
    have hA4 : orderOf (T.e₁ ⟨a, ha⟩) = 4 := by
      refine hord _ ?_ hne1
      rw [← map_pow, pow_two]
      have : (⟨a, ha⟩ : T.I₁) * ⟨a, ha⟩ = ⟨T.z, T.z_mem₁⟩ := Subtype.ext h1
      rw [this, T.e₁_z]
    have hB4 : orderOf (T.e₂ ⟨b, hb⟩) = 4 := by
      refine hord _ ?_ hne1
      rw [← map_pow, pow_two]
      have : (⟨b, hb⟩ : T.I₂) * ⟨b, hb⟩ = ⟨T.z, T.z_mem₂⟩ := Subtype.ext hb2
      rw [this, T.e₂_z]
    obtain ⟨i₁, hi₁, hfix₁⟩ := exists_conj_fix T hF hp2 ha hA4
    obtain ⟨i₂, hi₂, hfix₂⟩ := exists_conj_fix T.swap hF hp2 hb hB4
    have hfix₂' : T.t * (i₂ * b * i₂⁻¹) * T.t⁻¹ = b := hfix₂
    refine ⟨T.t * (i₁ * i₂), ?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have hw : i₂ * b * i₂⁻¹ ∈ T.I₂ :=
        T.I₂.mul_mem (T.I₂.mul_mem hi₂ hb) (T.I₂.inv_mem hi₂)
      have hca : i₂ * a = a * i₂ := (T.comm a ha i₂ hi₂).symm
      have e2 : i₂ * (a * b) * i₂⁻¹ = a * (i₂ * b * i₂⁻¹) := by
        calc i₂ * (a * b) * i₂⁻¹ = (i₂ * a) * b * i₂⁻¹ := by group
          _ = (a * i₂) * b * i₂⁻¹ := by rw [hca]
          _ = a * (i₂ * b * i₂⁻¹) := by group
      have e3 : i₁ * (i₂ * b * i₂⁻¹) * i₁⁻¹ = i₂ * b * i₂⁻¹ := by
        have := T.comm i₁ hi₁ _ hw
        rw [this, mul_inv_cancel_right]
      have hconj : (T.t * (i₁ * i₂)) * (a * b) * (T.t * (i₁ * i₂))⁻¹ = a * b := by
        calc (T.t * (i₁ * i₂)) * (a * b) * (T.t * (i₁ * i₂))⁻¹
            = T.t * (i₁ * (i₂ * (a * b) * i₂⁻¹) * i₁⁻¹) * T.t⁻¹ := by group
          _ = T.t * (i₁ * (a * (i₂ * b * i₂⁻¹)) * i₁⁻¹) * T.t⁻¹ := by rw [e2]
          _ = T.t * ((i₁ * a * i₁⁻¹) * (i₁ * (i₂ * b * i₂⁻¹) * i₁⁻¹)) * T.t⁻¹ := by group
          _ = T.t * ((i₁ * a * i₁⁻¹) * (i₂ * b * i₂⁻¹)) * T.t⁻¹ := by rw [e3]
          _ = (T.t * (i₁ * a * i₁⁻¹) * T.t⁻¹) * (T.t * (i₂ * b * i₂⁻¹) * T.t⁻¹) := by group
          _ = a * b := by rw [hfix₁, hfix₂']
      exact mul_inv_eq_iff_eq_mul.1 hconj
    · intro hx
      have hi : i₁ * i₂ ∈ T.I₁ ⊔ T.I₂ :=
        (T.I₁ ⊔ T.I₂).mul_mem (Subgroup.mem_sup_left hi₁) (Subgroup.mem_sup_right hi₂)
      apply T.t_not_mem
      have h3 := (T.I₁ ⊔ T.I₂).mul_mem hx ((T.I₁ ⊔ T.I₂).inv_mem hi)
      rwa [mul_inv_cancel_right] at h3

end Fix

end NFacts


section G5a

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

variable {X : Type} [Group X] [Finite X]

theorem card_closure_triple_le {z w u₁ u₂ : X} (hz : z * z = 1) (hw : w * w = 1)
    (hzw : z * w = w * z) (hz' : z ∈ kleinSub hz hw hzw) (h₁ : u₁ ∈ kleinSub hz hw hzw)
    (h₂ : u₂ ∈ kleinSub hz hw hzw) : Nat.card ↥(closure ({z, u₁, u₂} : Set X)) ≤ 4 := by
  refine (Subgroup.card_le_of_le (K := kleinSub hz hw hzw) ?_).trans (card_kleinSub_le hz hw hzw)
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact hz'
  · exact h₁
  · exact h₂

theorem ne_of_card_eq_eight {z u₁ u₂ : X} (hz : z * z = 1) (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (hz₁ : z * u₁ = u₁ * z) (hz₂ : z * u₂ = u₂ * z)
    (hE : Nat.card ↥(closure ({z, u₁, u₂} : Set X)) = 8) :
    u₁ ≠ 1 ∧ u₁ ≠ z ∧ u₂ ≠ 1 ∧ u₂ ≠ z ∧ u₁ * u₂ ≠ 1 ∧ u₁ * u₂ ≠ z := by
  have hbound : ∀ {w : X} (hw : w * w = 1) (hzw : z * w = w * z), u₁ ∈ kleinSub hz hw hzw →
      u₂ ∈ kleinSub hz hw hzw → False := by
    intro w hw hzw h1 h2
    have hzK : z ∈ kleinSub hz hw hzw := (mem_kleinSub hz hw hzw).2 (Or.inr (Or.inl rfl))
    have := card_closure_triple_le hz hw hzw hzK h1 h2
    omega
  have e1 : u₂ ∈ kleinSub hz h₂ hz₂ := (mem_kleinSub hz h₂ hz₂).2 (Or.inr (Or.inr (Or.inl rfl)))
  have e2 : z ∈ kleinSub hz h₂ hz₂ := (mem_kleinSub hz h₂ hz₂).2 (Or.inr (Or.inl rfl))
  have e3 : u₁ ∈ kleinSub hz h₁ hz₁ := (mem_kleinSub hz h₁ hz₁).2 (Or.inr (Or.inr (Or.inl rfl)))
  have e4 : z ∈ kleinSub hz h₁ hz₁ := (mem_kleinSub hz h₁ hz₁).2 (Or.inr (Or.inl rfl))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hbound h₂ hz₂ (by rw [h]; exact one_mem _) e1
  · intro h
    exact hbound h₂ hz₂ (by rw [h]; exact e2) e1
  · intro h
    exact hbound h₁ hz₁ e3 (by rw [h]; exact one_mem _)
  · intro h
    exact hbound h₁ hz₁ e3 (by rw [h]; exact e4)
  · intro h
    have : u₂ = u₁ := by
      have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]; exact inv_eq_of_mul_eq_one_right h₁
    exact hbound h₁ hz₁ e3 (by rw [this]; exact e3)
  · intro h
    have : u₂ = z * u₁ := by
      calc u₂ = u₁ * (u₁ * u₂) := by rw [← mul_assoc, h₁, one_mul]
        _ = u₁ * z := by rw [h]
        _ = z * u₁ := hz₁.symm
    exact hbound h₁ hz₁ e3 (by rw [this]; exact (mem_kleinSub hz h₁ hz₁).2 (Or.inr (Or.inr (Or.inr rfl))))

end G5a

section G5b

variable {J : Type} [Group J] [Finite J]

theorem exists_mem_not_mem {H K : Subgroup J} (h : Nat.card ↥H < Nat.card ↥K) : ∃ x ∈ K, x ∉ H := by
  by_contra hcon
  push Not at hcon
  have : K ≤ H := fun x hx => hcon x hx
  have := Subgroup.card_le_of_le this
  omega

omit [Finite J] in
theorem map_centralizer_le_klein {t u : J} (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t)
    (u' : ↥(centralizer ({t} : Set J))) (hu' : (u' : J) = u) :
    (centralizer ({u'} : Set ↥(centralizer ({t} : Set J)))).map (centralizer ({t} : Set J)).subtype ≤
      centralizer ((kleinSub ht hu htu : Subgroup J) : Set J) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxu : (x : J) * u = u * (x : J) := by
    have := mem_centralizer_singleton_iff.1 hx
    rw [← hu']
    exact congrArg Subtype.val this
  have hxt : (x : J) * t = t * (x : J) := mem_centralizer_singleton_iff.1 x.2
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases (mem_kleinSub ht hu htu).1 hh with rfl | rfl | rfl | rfl
  · simp
  · exact hxt.symm
  · exact hxu.symm
  · show (t * u) * (x : J) = (x : J) * (t * u)
    rw [mul_assoc, ← hxu, ← mul_assoc, ← hxt, mul_assoc]

end G5b

end GenLocG2Inner

section G5a

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab GenLocG2Inner

variable {X : Type} [Group X] [Finite X]

theorem shape_eq_sup_centralizers {F₁ : Type} [Field F₁] [Finite F₁]
    (S : Shape X F₁ F₁) (hq : 27 ≤ Nat.card F₁)
    {u₁ u₂ : X} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (hc : u₁ * u₂ = u₂ * u₁)
    (hE : Nat.card ↥(Subgroup.closure ({S.z, u₁, u₂} : Set X)) = 8) :
    centralizer ({u₁} : Set X) ⊔ centralizer ({u₂} : Set X) ⊔ centralizer ({u₁ * u₂} : Set X) =
      ⊤ := by
  classical
  obtain ⟨p, f, hp, hF, hpc⟩ : ∃ p f : ℕ, p.Prime ∧ Nat.card F₁ = p ^ f ∧ ringChar F₁ = p := by
    have : Fintype F₁ := Fintype.ofFinite F₁
    obtain ⟨n, hp, h⟩ := FiniteField.card F₁ (ringChar F₁)
    exact ⟨ringChar F₁, n, hp, by rw [Nat.card_eq_fintype_card]; exact h, rfl⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact S.ns₁ (FiniteField.isSquare_of_char_two hpc _)
  have : Fact p.Prime := ⟨hp⟩
  have hu₁₂ : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [hc]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [h₁, h₂, one_mul]
  obtain ⟨hn1, hn1z, hn2, hn2z, hn12, hn12z⟩ :=
    ne_of_card_eq_eight S.z_sq h₁ h₂ (z_comm S u₁) (z_comm S u₂) hE
  have hne : u₁ ≠ u₂ := by
    intro h
    apply hn12
    rw [← h]; exact h₁
  set Y := centralizer ({u₁} : Set X) ⊔ centralizer ({u₂} : Set X) ⊔
      centralizer ({u₁ * u₂} : Set X) with hY
  have hN : S.I₁ ⊔ S.I₂ ≤ Y := by
    have := S.normal₁
    have := S.normal₂
    have h11 : 11 ≤ p ^ f := by rw [← hF]; omega
    exact sup_le
      (normalSL2_le_sup_centralizers hp hp2 hF h11 S.I₁ S.e₁ h₁ h₂ hc hn1 hn2 hne)
      (normalSL2_le_sup_centralizers hp hp2 hF h11 S.I₂ S.e₂ h₁ h₂ hc hn1 hn2 hne)
  have hC1 : centralizer ({u₁} : Set X) ≤ Y := le_sup_left.trans le_sup_left
  have hC2 : centralizer ({u₂} : Set X) ≤ Y := le_sup_right.trans le_sup_left
  have hC3 : centralizer ({u₁ * u₂} : Set X) ≤ Y := le_sup_right
  by_cases hu1N : u₁ ∈ S.I₁ ⊔ S.I₂
  · obtain ⟨x, hx, hxN⟩ := exists_mem_centralizer_not_mem_N S hF hp2 h₁ hu1N hn1 hn1z
    exact eq_top_of_N_le S hN (hC1 hx) hxN
  by_cases hu2N : u₂ ∈ S.I₁ ⊔ S.I₂
  · obtain ⟨x, hx, hxN⟩ := exists_mem_centralizer_not_mem_N S hF hp2 h₂ hu2N hn2 hn2z
    exact eq_top_of_N_le S hN (hC2 hx) hxN
  have hu12N : u₁ * u₂ ∈ S.I₁ ⊔ S.I₂ := mul_mem_N_of_not_mem S hu1N hu2N
  obtain ⟨x, hx, hxN⟩ := exists_mem_centralizer_not_mem_N S hF hp2 hu₁₂ hu12N hn12 hn12z
  exact eq_top_of_N_le S hN (hC3 hx) hxN


end G5a

section G5bMain

open CFSG.Blueprint CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab GenLocG2Inner


variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem g2_centralizer_le_iSup_four (hf : 3 ≤ f) (hJ : LieModel J .G2 0 3 f) {E : Subgroup J}
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hcard : Nat.card ↥E = 8) {t : J} (htE : t ∈ E)
    (ht : t ≠ 1) :
    centralizer ({t} : Set J) ≤
      ⨆ (V : Subgroup J) (_ : V ≤ E) (_ : t ∈ V) (_ : Nat.card ↥V = 4), centralizer (V : Set J) := by
  classical
  obtain ⟨hcomm, hsq⟩ := CFSG.GH74.Generic.BProg.B2.WeakSigGen.forall_of_isElementaryAbelian hE
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact hsq t htE) ht
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, _, S, hcardF, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 Nat.prime_three (by norm_num) hJ t ht2
  have hq : 27 ≤ Nat.card F := by
    rw [hcardF]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hEC : ∀ u ∈ E, u ∈ centralizer ({t} : Set J) := fun u hu => by
    rw [mem_centralizer_singleton_iff]; exact hcomm u hu t htE
  have ht1sq : t * t = 1 := hsq t htE
  have hzp : Nat.card ↥(zpowers t) < Nat.card ↥E := by
    rw [Nat.card_zpowers, ht2, hcard]; norm_num
  obtain ⟨u₁, hu₁E, hu₁z⟩ := exists_mem_not_mem hzp
  have hu₁1 : u₁ ≠ 1 := fun h => hu₁z (h ▸ one_mem _)
  have hu₁t : u₁ ≠ t := fun h => hu₁z (h ▸ mem_zpowers t)
  have h₁ : u₁ * u₁ = 1 := hsq u₁ hu₁E
  have htu₁ : t * u₁ = u₁ * t := hcomm t htE u₁ hu₁E
  have hK : Nat.card ↥(kleinSub ht1sq h₁ htu₁) < Nat.card ↥E := by
    have := card_kleinSub_le ht1sq h₁ htu₁; omega
  obtain ⟨u₂, hu₂E, hu₂K⟩ := exists_mem_not_mem hK
  have h₂ : u₂ * u₂ = 1 := hsq u₂ hu₂E
  have htu₂ : t * u₂ = u₂ * t := hcomm t htE u₂ hu₂E
  have hu₁u₂ : u₁ * u₂ = u₂ * u₁ := hcomm u₁ hu₁E u₂ hu₂E
  have hcl : Nat.card ↥(closure ({t, u₁, u₂} : Set J)) = 8 := by
    have hle : closure ({t, u₁, u₂} : Set J) ≤ E := by
      rw [closure_le]
      rintro x (rfl | rfl | rfl)
      exacts [htE, hu₁E, hu₂E]
    have hK_le : kleinSub ht1sq h₁ htu₁ ≤ closure ({t, u₁, u₂} : Set J) := by
      intro x hx
      have ht' : t ∈ closure ({t, u₁, u₂} : Set J) := subset_closure (by simp)
      have hu' : u₁ ∈ closure ({t, u₁, u₂} : Set J) := subset_closure (by simp)
      rcases (mem_kleinSub ht1sq h₁ htu₁).1 hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact ht'
      · exact hu'
      · exact mul_mem ht' hu'
    have hlt : kleinSub ht1sq h₁ htu₁ < closure ({t, u₁, u₂} : Set J) := by
      refine lt_of_le_of_ne hK_le fun h => hu₂K ?_
      rw [h]
      exact subset_closure (by simp)
    have hcardlt := Subgroup.card_lt_of_lt hlt
    have hdvd := Subgroup.card_dvd_of_le hK_le
    have hle8 := Subgroup.card_le_of_le hle
    have h4 := card_kleinSub ht1sq h₁ htu₁ ht hu₁1 hu₁t.symm
    rw [h4] at hdvd hcardlt
    omega
  obtain ⟨hn1, hn1t, hn2, hn2t, hn12, hn12t⟩ :=
    ne_of_card_eq_eight ht1sq h₁ h₂ htu₁ htu₂ hcl
  let ι := (centralizer ({t} : Set J)).subtype
  let u₁' : ↥(centralizer ({t} : Set J)) := ⟨u₁, hEC u₁ hu₁E⟩
  let u₂' : ↥(centralizer ({t} : Set J)) := ⟨u₂, hEC u₂ hu₂E⟩
  have h₁' : u₁' * u₁' = 1 := Subtype.ext h₁
  have h₂' : u₂' * u₂' = 1 := Subtype.ext h₂
  have hc' : u₁' * u₂' = u₂' * u₁' := Subtype.ext hu₁u₂
  have hE' : Nat.card ↥(closure ({S.z, u₁', u₂'} : Set ↥(centralizer ({t} : Set J)))) = 8 := by
    have himg : (closure ({S.z, u₁', u₂'} : Set ↥(centralizer ({t} : Set J)))).map ι =
        closure ({t, u₁, u₂} : Set J) := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq, ι, u₁', u₂', hSz]
    rw [← hcl, ← himg, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hmain := shape_eq_sup_centralizers S hq h₁' h₂' hc' hE'
  have hu12sq : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [hu₁u₂]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [h₁, h₂, one_mul]
  have hu12E : u₁ * u₂ ∈ E := E.mul_mem hu₁E hu₂E
  have htu12 : t * (u₁ * u₂) = (u₁ * u₂) * t := by
    rw [← mul_assoc, htu₁, mul_assoc, htu₂, mul_assoc]
  have hbound : ∀ {u : J} (hu : u ∈ E) (hsqu : u * u = 1) (htu : t * u = u * t), u ≠ 1 → u ≠ t →
      centralizer ((kleinSub ht1sq hsqu htu : Subgroup J) : Set J) ≤
        ⨆ (V : Subgroup J) (_ : V ≤ E) (_ : t ∈ V) (_ : Nat.card ↥V = 4),
          centralizer (V : Set J) := by
    intro u hu hsqu htu hu1 hut
    have hVE : kleinSub ht1sq hsqu htu ≤ E := by
      intro x hx
      rcases (mem_kleinSub ht1sq hsqu htu).1 hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact htE
      · exact hu
      · exact E.mul_mem htE hu
    have htV : t ∈ kleinSub ht1sq hsqu htu :=
      (mem_kleinSub ht1sq hsqu htu).2 (Or.inr (Or.inl rfl))
    have hV4 : Nat.card ↥(kleinSub ht1sq hsqu htu) = 4 :=
      card_kleinSub ht1sq hsqu htu ht hu1 hut.symm
    exact le_iSup₂_of_le _ hVE (le_iSup₂_of_le htV hV4 le_rfl)
  have hmap : (⊤ : Subgroup ↥(centralizer ({t} : Set J))).map ι = centralizer ({t} : Set J) := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  rw [← hmap, ← hmain, Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (map_centralizer_le_klein ht1sq h₁ htu₁ u₁' rfl).trans (hbound hu₁E h₁ htu₁ hn1 hn1t)
  · exact (map_centralizer_le_klein ht1sq h₂ htu₂ u₂' rfl).trans (hbound hu₂E h₂ htu₂ hn2 hn2t)
  · exact (map_centralizer_le_klein ht1sq hu12sq htu12 (u₁' * u₂') rfl).trans
      (hbound hu12E hu12sq htu12 hn12 hn12t)

end G5bMain


end CFSG.GH74.Generic.BProg.B2
