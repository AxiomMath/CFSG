module

public import CFSG.CGT.Stroth77.Extension22FourC4
public import CFSG.CGT.Stroth76.TModel

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

theorem fuv_fixed_two_torsion : ∀ v : Co, v + v = 0 → fuv v = v →
    v = (0, 0, 0) ∨ v = (0, 2, 0) ∨ v = (0, 0, 2) ∨ v = (0, 2, 2) := by
  decide +kernel

theorem ft_fixed_two_torsion : ∀ v : Co, v + v = 0 → ft v = v →
    v = (0, 0, 0) ∨ v = (0, 2, 0) ∨ v = (0, 0, 2) ∨ v = (0, 2, 2) := by
  decide +kernel

theorem mem_normalizer_of_mul_self {X : Type*} [Group X] {H : Subgroup X} {z : X}
    (hz : z * z = 1) (h : ∀ n ∈ H, z * n * z⁻¹ ∈ H) : z ∈ Subgroup.normalizer (H : Set X) := by
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  have := h _ hn
  rwa [show z * (z * n * z⁻¹) * z⁻¹ = n by
    rw [hinv, ← mul_assoc, ← mul_assoc, hz, one_mul, mul_assoc, hz, mul_one]] at this

section Config

variable {X : Type*} [Group X] (K : Config X)

theorem x_sq_mem_closureE : K.x ^ 2 ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} :=
  Subgroup.subset_closure (by simp)

theorem y_sq_mem_closureE : K.y ^ 2 ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} :=
  Subgroup.subset_closure (by simp)

theorem uv_mem_closureE : K.uv ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} :=
  Subgroup.subset_closure (by simp)

theorem t_mem_closureE : K.t ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} :=
  Subgroup.subset_closure (by simp)

theorem mem_closureE_of_fixed {β : X} (hβ : β ∈ K.A) (hβ2 : β * β = 1) {g : X}
    (hg : g = K.uv ∨ g = K.t) (hfix : g⁻¹ * β * g = β) :
    β ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} := by
  obtain ⟨v, rfl⟩ := K.exists_ev hβ
  have h2 : v + v = 0 := K.ev_injective (by rw [K.ev_add, hβ2, K.ev_zero])
  have hcases : v = (0, 0, 0) ∨ v = (0, 2, 0) ∨ v = (0, 0, 2) ∨ v = (0, 2, 2) := by
    rcases hg with rfl | rfl
    · exact fuv_fixed_two_torsion v h2 (K.ev_injective (by rw [← K.conj_uv_ev, hfix]))
    · exact ft_fixed_two_torsion v h2 (K.ev_injective (by rw [← K.conj_t_ev, hfix]))
  have hx := x_sq_mem_closureE K
  have hy := y_sq_mem_closureE K
  have h0 : (0 : ZMod 2).val = 0 := rfl
  have h20 : (0 : ZMod 4).val = 0 := rfl
  have h22 : (2 : ZMod 4).val = 2 := rfl
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa [Config.ev, h0, h20] using
      (Subgroup.one_mem (Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}))
  · simpa [Config.ev, h0, h20, h22] using hx
  · simpa [Config.ev, h0, h20, h22] using hy
  · simpa [Config.ev, h0, h22] using mul_mem hx hy

theorem conj_mul_mem_closureE {B : Subgroup X} (hAB : K.A ≤ B)
    (hB2 : ∀ b ∈ B, b * b = 1 → b ∈ K.A) {z : X} (hz : z * z = 1)
    (hzB : z ∈ Subgroup.centralizer (B : Set X)) {g : X} (hg : g = K.uv ∨ g = K.t)
    (hgB : z⁻¹ * (g⁻¹ * z * g) ∈ B) :
    z * g * z⁻¹ ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} := by
  have hg2 : g * g = 1 := by
    rcases hg with rfl | rfl
    · exact uv_mul_self K
    · exact t_mul_self K
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set β := z⁻¹ * (g⁻¹ * z * g) with hβdef
  have hβz : β * z = z * β := Subgroup.mem_centralizer_iff.mp hzB β hgB
  have hzβ : z * β = g⁻¹ * z * g := by rw [hβdef]; group
  have hβ2 : β * β = 1 := by
    have h1 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      rw [show (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hz]; group
    rw [← hzβ] at h1
    calc β * β = z * z * (β * β) := by rw [hz, one_mul]
      _ = z * (z * β) * β := by group
      _ = z * (β * z) * β := by rw [hβz]
      _ = z * β * (z * β) := by group
      _ = 1 := h1
  have hβA : β ∈ K.A := hB2 β hgB hβ2
  have hβfix : g⁻¹ * β * g = β := by
    have h1 : g⁻¹ * (z * β) * g = z := by
      rw [hzβ, show g⁻¹ * (g⁻¹ * z * g) * g = (g * g)⁻¹ * z * (g * g) by group, hg2]; group
    have h2 : g⁻¹ * (z * β) * g = (g⁻¹ * z * g) * (g⁻¹ * β * g) := by group
    rw [h2, ← hzβ] at h1
    have h3 : g⁻¹ * β * g = β⁻¹ := by
      calc g⁻¹ * β * g = (z * β)⁻¹ * (z * β * (g⁻¹ * β * g)) := by group
        _ = (z * β)⁻¹ * z := by rw [h1]
        _ = β⁻¹ := by group
    rw [h3, inv_eq_of_mul_eq_one_right hβ2]
  have hβE := mem_closureE_of_fixed K hβA hβ2 hg hβfix
  have hgE : g ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} := by
    rcases hg with rfl | rfl
    · exact uv_mem_closureE K
    · exact t_mem_closureE K
  have hconj : z * g * z⁻¹ = g * β := by
    have h1 : z * g = g * (z * β) := by
      rw [hzβ, ← mul_assoc, ← mul_assoc, ← hginv, mul_inv_cancel, one_mul, hginv]
    rw [h1, mul_assoc, ← hβz, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact mul_mem hgE hβE

theorem mem_normalizer_E_of_conj_mem {B : Subgroup X} (hAB : K.A ≤ B)
    (hB2 : ∀ b ∈ B, b * b = 1 → b ∈ K.A) {z : X} (hz : z * z = 1)
    (hzB : z ∈ Subgroup.centralizer (B : Set X))
    (huv : z⁻¹ * (K.uv⁻¹ * z * K.uv) ∈ B) (ht : z⁻¹ * (K.t⁻¹ * z * K.t) ∈ B) :
    z ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) := by
  refine mem_normalizer_of_mul_self hz fun n hn => ?_
  have hle : Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} ≤
      (Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}).comap (MulAut.conj z).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, SetLike.mem_coe]
    have hcomm : ∀ a ∈ K.A, z * a * z⁻¹ = a := fun a ha => by
      rw [(Subgroup.mem_centralizer_iff.mp hzB a (hAB ha)).symm, mul_inv_cancel_right]
    rcases hg with rfl | rfl | rfl | rfl
    · rw [hcomm _ (pow_mem K.x_mem 2)]; exact x_sq_mem_closureE K
    · rw [hcomm _ (pow_mem K.y_mem 2)]; exact y_sq_mem_closureE K
    · exact conj_mul_mem_closureE K hAB hB2 hz hzB (Or.inl rfl) huv
    · exact conj_mul_mem_closureE K hAB hB2 hz hzB (Or.inr rfl) ht
  simpa using hle hn

theorem noInvolutionsCentralizing_of_conj_mem {B C : Subgroup X} (hAB : K.A ≤ B)
    (hB2 : ∀ b ∈ B, b * b = 1 → b ∈ K.A)
    (hNE : ∀ z ∈ C, z ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) → z ∈ K.A)
    (huv : ∀ z ∈ C, z⁻¹ * (K.uv⁻¹ * z * K.uv) ∈ B)
    (ht : ∀ z ∈ C, z⁻¹ * (K.t⁻¹ * z * K.t) ∈ B) :
    NoInvolutionsCentralizing C B :=
  fun z hzC hz2 hzB =>
    hAB (hNE z hzC (mem_normalizer_E_of_conj_mem K hAB hB2 hz2 hzB (huv z hzC) (ht z hzC)))

end Config

@[expose] def permRelCheck {k : ℕ} (f g r : Equiv.Perm (Fin k)) : Bool :=
  !(f * f == 1 && f * g == g * f && g == r * f * r⁻¹ && g * f == r * g * r⁻¹) || f == 1

theorem permRelCheck_all : ∀ {k : ℕ}, k ≤ 3 → ∀ f g r : Equiv.Perm (Fin k),
    permRelCheck f g r = true := by
  intro k hk
  interval_cases k <;> decide

theorem perm_eq_one_of_rels {k : ℕ} (hk : k ≤ 3) (f g r : Equiv.Perm (Fin k))
    (hf : f * f = 1) (hfg : f * g = g * f) (hg : g = r * f * r⁻¹) (hgf : g * f = r * g * r⁻¹) :
    f = 1 := by
  have h := permRelCheck_all hk f g r
  simp only [permRelCheck, hf, hfg, ← hg, hgf, beq_self_eq_true, Bool.and_self, Bool.not_true,
    Bool.false_or, beq_iff_eq] at h
  exact h

@[expose] def autRestrictNeOne (M : Type*) [Group M] : MulAut M →* Equiv.Perm {m : M // m ≠ 1} where
  toFun σ := σ.toEquiv.subtypeEquiv (fun m => by simp)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem autRestrictNeOne_injective (M : Type*) [Group M] :
    Function.Injective (autRestrictNeOne M) := by
  intro σ τ h
  ext m
  by_cases hm : m = 1
  · subst hm; simp
  · have := congrArg (fun π : Equiv.Perm {m : M // m ≠ 1} => ((π ⟨m, hm⟩ : {m : M // m ≠ 1}) : M)) h
    simpa [autRestrictNeOne] using this

theorem mulAut_eq_one_of_rels {M : Type*} [Group M] [Finite M] (hM : Nat.card M ≤ 4)
    {f g r : MulAut M} (hf : f * f = 1) (hfg : f * g = g * f) (hg : g = r * f * r⁻¹)
    (hgf : g * f = r * g * r⁻¹) : f = 1 := by
  classical
  haveI := Fintype.ofFinite M
  have hk : Nat.card {m : M // m ≠ 1} ≤ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [Nat.card_eq_fintype_card] at hM
    omega
  set k := Nat.card {m : M // m ≠ 1}
  let e : {m : M // m ≠ 1} ≃ Fin k := Finite.equivFin _
  let F : MulAut M →* Equiv.Perm (Fin k) :=
    e.permCongrHom.toMonoidHom.comp (autRestrictNeOne M)
  have hF : Function.Injective F :=
    e.permCongrHom.injective.comp (autRestrictNeOne_injective M)
  have h := perm_eq_one_of_rels hk (F f) (F g) (F r)
    (by rw [← map_mul, hf, map_one]) (by rw [← map_mul, ← map_mul, hfg])
    (by rw [hg, map_mul, map_mul, map_inv]) (by rw [← map_mul, hgf, map_mul, map_mul, map_inv])
  exact hF (h.trans (map_one F).symm)

section Quotient

variable {X : Type*} [Group X] [Finite X] {B C : Subgroup X}

theorem conjByAutQuotient_congr [(B.subgroupOf C).Normal] {g h : X} (hgh : g = h)
    {hgC : g ∈ Subgroup.normalizer C} {hgB : g ∈ Subgroup.normalizer B} :
    conjByAutQuotient g hgC hgB = conjByAutQuotient h (hgh ▸ hgC) (hgh ▸ hgB) := by
  subst hgh; rfl

theorem conj_mul_mem_of_conjByAutQuotient_eq_one [(B.subgroupOf C).Normal] {g : X}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (h1 : conjByAutQuotient g hgC hgB = 1) {z : X} (hz : z ∈ C) :
    z⁻¹ * (g⁻¹ * z * g) ∈ B := by
  have hmk := congrArg (fun σ : MulAut (C ⧸ B.subgroupOf C) =>
    σ (QuotientGroup.mk (⟨z, hz⟩ : C))) h1
  simp only [conjByAutQuotient_apply_mk, MulAut.one_apply] at hmk
  have h2 := QuotientGroup.eq.mp hmk
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : ((conjByHom g hgC ⟨z, hz⟩)⁻¹ * ⟨z, hz⟩ : C) = (g⁻¹ * z * g)⁻¹ * z := by
    simp [conjByHom, conjBy]
  rw [h3] at h2
  have h4 := B.inv_mem h2
  rwa [mul_inv_rev, inv_inv] at h4

theorem conj_mem_of_card_le_four (hBC : B ≤ C) (hCB : C ≤ Subgroup.centralizer (B : Set X))
    (hcard : Nat.card C ≤ 4 * Nat.card B) {uv t ρ : X}
    (huvC : uv ∈ Subgroup.normalizer C) (huvB : uv ∈ Subgroup.normalizer B)
    (htC : t ∈ Subgroup.normalizer C) (htB : t ∈ Subgroup.normalizer B)
    (hρC : ρ ∈ Subgroup.normalizer C) (hρB : ρ ∈ Subgroup.normalizer B)
    (huv2 : uv * uv = 1) (huvt : uv * t = t * uv) (hρuv : ρ⁻¹ * uv * ρ = t)
    (hρt : ρ⁻¹ * t * ρ = uv * t) :
    ∀ z ∈ C, z⁻¹ * (uv⁻¹ * z * uv) ∈ B ∧ z⁻¹ * (t⁻¹ * z * t) ∈ B := by
  haveI hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hCB)
  have hM : Nat.card (C ⧸ B.subgroupOf C) ≤ 4 := by
    have h1 := (B.subgroupOf C).card_mul_index
    have h2 : Nat.card (B.subgroupOf C) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
    rw [h2, Subgroup.index_eq_card] at h1
    have hpos : 0 < Nat.card B := Nat.card_pos
    exact Nat.le_of_mul_le_mul_left (by rw [h1, mul_comm]; exact hcard) hpos
  set f := conjByAutQuotient uv huvC huvB
  set g := conjByAutQuotient t htC htB
  set r := conjByAutQuotient ρ hρC hρB
  have hρinv : conjByAutQuotient ρ⁻¹ (Subgroup.inv_mem _ hρC) (Subgroup.inv_mem _ hρB) = r⁻¹ := by
    have h := conjByAutQuotient_mul ρ ρ⁻¹ hρC (Subgroup.inv_mem _ hρC) hρB
      (Subgroup.inv_mem _ hρB)
    rw [conjByAutQuotient_congr (mul_inv_cancel ρ), conjByAutQuotient_one] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hconj : ∀ {a b : X} (haC : a ∈ Subgroup.normalizer C) (haB : a ∈ Subgroup.normalizer B)
      (hbC : b ∈ Subgroup.normalizer C) (hbB : b ∈ Subgroup.normalizer B)
      (hab : ρ⁻¹ * a * ρ = b),
      conjByAutQuotient b hbC hbB = r * conjByAutQuotient a haC haB * r⁻¹ := by
    intro a b haC haB hbC hbB hab
    subst hab
    rw [conjByAutQuotient_mul (ρ⁻¹ * a) ρ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hρC) haC) hρC
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hρB) haB) hρB,
      conjByAutQuotient_mul ρ⁻¹ a (Subgroup.inv_mem _ hρC) haC (Subgroup.inv_mem _ hρB) haB,
      hρinv, mul_assoc]
  have hf2 : f * f = 1 := by
    rw [← conjByAutQuotient_mul uv uv huvC huvC huvB huvB, conjByAutQuotient_congr huv2]
    exact conjByAutQuotient_one
  have hfg : f * g = g * f := by
    rw [← conjByAutQuotient_mul t uv htC huvC htB huvB, conjByAutQuotient_congr huvt.symm,
      conjByAutQuotient_mul uv t huvC htC huvB htB]
  have hg : g = r * f * r⁻¹ := hconj huvC huvB htC htB hρuv
  have hgf : g * f = r * g * r⁻¹ := by
    have h := hconj htC htB (Subgroup.mul_mem _ huvC htC) (Subgroup.mul_mem _ huvB htB) hρt
    rw [conjByAutQuotient_mul uv t huvC htC huvB htB] at h
    exact h
  have hf1 : f = 1 := mulAut_eq_one_of_rels hM hf2 hfg hg hgf
  have hg1 : g = 1 := by rw [hg, hf1, mul_one, mul_inv_cancel]
  intro z hz
  exact ⟨conj_mul_mem_of_conjByAutQuotient_eq_one huvC huvB hf1 hz,
    conj_mul_mem_of_conjByAutQuotient_eq_one htC htB hg1 hz⟩

end Quotient

end CFSG.CGT.Stroth76
