module

public import CFSG.LargeExtraspecial.DWSm77One
public import CFSG.LargeExtraspecial.DWSm77Aut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

omit [Finite G] in
theorem mem_normalizer_B {m : G} (hm : m ∈ S.M) : m ∈ normalizer (D.B : Set G) :=
  mem_normalizer_of_conj_mem (fun x hx => D.conj_B m hm x hx)
    (fun x hx => D.conj_B m⁻¹ (S.M.inv_mem hm) x hx)

theorem conj_z_mem_conj_B (g : G) : g * S.z * g⁻¹ ∈ (D.conj g).B := (D.conj g).z_mem_B

omit [Finite G] in
theorem mem_conjBy_M_iff' {g m : G} :
    m ∈ (S.conjBy g).M ↔ m * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * m := by
  rw [(S.conjBy g).mem_M_iff, Setting.conjBy_z]

theorem commute_of_disjoint_conj_B {g : G} {N : Subgroup G}
    (hN : ∀ p ∈ (D.conj g).B, ∀ c ∈ N, p * c * p⁻¹ ∈ N)
    (hdis : ∀ t ∈ N, t ∈ (D.conj g).B → t = 1) {c : G} (hc : c ∈ N)
    (hcx : c * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * c) {p : G} (hp : p ∈ (D.conj g).B) :
    c * p = p * c := by
  have h1 : c * p * c⁻¹ * p⁻¹ ∈ (D.conj g).B :=
    (D.conj g).B.mul_mem ((D.conj g).conj_B c (mem_conjBy_M_iff'.mpr hcx) p hp)
      ((D.conj g).B.inv_mem hp)
  have h2 : c * p * c⁻¹ * p⁻¹ ∈ N := by
    rw [show c * p * c⁻¹ * p⁻¹ = c * (p * c⁻¹ * p⁻¹) by group]
    exact N.mul_mem hc (hN p hp c⁻¹ (N.inv_mem hc))
  have h3 := hdis _ h2 h1
  calc c * p = c * p * c⁻¹ * p⁻¹ * (p * c) := by group
    _ = p * c := by rw [h3, one_mul]

theorem conj_x_of_commute_conj_B {g : G} (hle : (D.conj g).B ≤ S.M) {F : Subgroup G}
    (hFQ : F ≤ S.QG) (hFB : ∀ p ∈ (D.conj g).B, ∀ f ∈ F, p * f * p⁻¹ ∈ F)
    (hcomm : ∀ c ∈ F, c * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * c → ∀ p ∈ (D.conj g).B,
      c * p = p * c) {f : G} (hf : f ∈ F) :
    g * S.z * g⁻¹ * f * (g * S.z * g⁻¹)⁻¹ = f ∨
      g * S.z * g⁻¹ * f * (g * S.z * g⁻¹)⁻¹ = f * S.z := by
  obtain ⟨k, hk, hk2⟩ := (D.conj g).swap.exists_sq_eq_z_A
  change k ∈ (D.conj g).B at hk
  change k ^ 2 = g * S.z * g⁻¹ at hk2
  have hx2 : (g * S.z * g⁻¹) * (g * S.z * g⁻¹) = 1 := (S.conjBy g).z_mul_z
  have h := conj_sq_of_centralizer_le S hFQ (hle hk) (hFB k hk) ?_ ?_ hf
  · rwa [hk2] at h
  · intro f _
    rw [show k ^ 4 = (k ^ 2) ^ 2 by rw [← pow_mul], hk2, pow_two, hx2]
    group
  · intro f hf hf'
    rw [hk2] at hf'
    have hfx : f * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * f := by
      calc f * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * f * (g * S.z * g⁻¹)⁻¹ * (g * S.z * g⁻¹) := by
            rw [hf']
        _ = g * S.z * g⁻¹ * f := by group
    rw [← hcomm f hf hfx k hk]
    group

theorem commute_of_conj_x {g : G} (hle : (D.conj g).B ≤ S.M) {F : Subgroup G}
    (hFQ : F ≤ S.QG) (hFB : ∀ p ∈ (D.conj g).B, ∀ f ∈ F, p * f * p⁻¹ ∈ F)
    (hcomm : ∀ c ∈ F, c * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * c → ∀ p ∈ (D.conj g).B,
      c * p = p * c) {f : G} (hf : f ∈ F) : g * S.z * g⁻¹ * f = f * (g * S.z * g⁻¹) := by
  set x := g * S.z * g⁻¹ with hx
  have h23 := fun f (hf : f ∈ F) => D.conj_x_of_commute_conj_B hle hFQ hFB hcomm hf
  by_contra hfx
  have hcz : x * f * x⁻¹ = f * S.z := (h23 f hf).resolve_left fun h => hfx (by
    calc x * f = x * f * x⁻¹ * x := by group
      _ = f * x := by rw [h])
  set X := F ⊓ centralizer ({x} : Set G) with hX
  have hcov : ∀ f' ∈ F, f' ∈ X ∨ f⁻¹ * f' ∈ X := by
    intro f' hf'
    rcases h23 f' hf' with h | h
    · refine Or.inl ⟨hf', mem_centralizer_singleton_iff.mpr ?_⟩
      calc f' * x = x * f' * x⁻¹ * x := by rw [h]
        _ = x * f' := by group
    · refine Or.inr ⟨F.mul_mem (F.inv_mem hf) hf', mem_centralizer_singleton_iff.mpr ?_⟩
      have h' : x * f' * x⁻¹ = f' * S.z := h
      have hw : f⁻¹ * f' ∈ S.QG := S.QG.mul_mem (S.QG.inv_mem (hFQ hf)) (hFQ hf')
      have e : x * (f⁻¹ * f') * x⁻¹ = f⁻¹ * f' := by
        calc x * (f⁻¹ * f') * x⁻¹ = (x * f * x⁻¹)⁻¹ * (x * f' * x⁻¹) := by group
          _ = S.z⁻¹ * (f⁻¹ * f' * S.z) := by rw [hcz, h']; group
          _ = f⁻¹ * f' := by rw [S.z_comm_QG hw, ← mul_assoc, inv_mul_cancel, one_mul]
      calc f⁻¹ * f' * x = x * (f⁻¹ * f') * x⁻¹ * x := by rw [e]
        _ = x * (f⁻¹ * f') := by group
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := (D.conj g).swap.exists_commutator_eq_z_A
  change t₁ ∈ (D.conj g).B at ht₁
  change t₂ ∈ (D.conj g).B at ht₂
  change t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = x at ht
  have hn : ∀ t ∈ (D.conj g).B, t ∈ normalizer (F : Set G) := fun t ht =>
    mem_normalizer_of_conj_mem (hFB t ht) (fun y hy => by
      simpa using hFB t⁻¹ ((D.conj g).B.inv_mem ht) y hy)
  have hfix := conj_commutator_eq_of_fix (F := F) (X := X) inf_le_left hf hcov (hn t₁ ht₁)
    (hn t₂ ht₂) (fun y hy => (hcomm y hy.1 (mem_centralizer_singleton_iff.mp hy.2) t₁ ht₁).symm)
    (fun y hy => (hcomm y hy.1 (mem_centralizer_singleton_iff.mp hy.2) t₂ ht₂).symm) hf
  rw [ht, hcz] at hfix
  exact S.z_ne_one (by simpa using hfix)

theorem mem_A_of_conj_B_le_M_of_not_mem_B {g : G} (hle : (D.conj g).B ≤ S.M)
    (hxB : g * S.z * g⁻¹ ∉ D.B) : g * S.z * g⁻¹ ∈ D.A := by
  have hxM : g * S.z * g⁻¹ ∈ S.M := hle (D.conj_z_mem_conj_B g)
  have hNB : ∀ p ∈ (D.conj g).B, ∀ c ∈ D.B, p * c * p⁻¹ ∈ D.B := fun p hp c hc =>
    D.conj_B p (hle hp) c hc
  have hdisB : ∀ t ∈ D.B, t ∈ (D.conj g).B → t = 1 := by
    intro t ht ht'
    by_contra ht1
    exact hxB ((D.conj g).z_mem_of_normalized hNB ht ht' ht1)
  have hcommB : ∀ c ∈ D.B, c * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * c → ∀ p ∈ (D.conj g).B,
      c * p = p * c := fun c hc hcx p hp => D.commute_of_disjoint_conj_B hNB hdisB hc hcx hp
  have hxQ : g * S.z * g⁻¹ ∈ S.QG := by
    by_contra hxQ
    have hNQ : ∀ p ∈ (D.conj g).B, ∀ c ∈ S.QG, p * c * p⁻¹ ∈ S.QG := fun p hp c hc =>
      S.conj_mem_QG (hle hp) hc
    have hdisQ : ∀ t ∈ S.QG, t ∈ (D.conj g).B → t = 1 := by
      intro t ht ht'
      by_contra ht1
      exact hxQ ((D.conj g).z_mem_of_normalized hNQ ht ht' ht1)
    have hcommQ : ∀ c ∈ S.QG, c * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * c → ∀ p ∈ (D.conj g).B,
        c * p = p * c := fun c hc hcx p hp => D.commute_of_disjoint_conj_B hNQ hdisQ hc hcx hp
    refine hxQ (S.mem_QG_of_cl_conj hxM fun y hy => ?_)
    rcases D.conj_x_of_commute_conj_B hle le_rfl hNQ hcommQ hy with h | h
    · rw [h]
    · rw [h, S.cl_mul_z hy]
  exact D.mem_A_of_commute hxQ fun b hb => D.commute_of_conj_x hle D.B_le hNB hcommB hb

section Fusion

variable (hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z)

include hB

theorem mem_A_of_conj_B_le_M {g : G} (hle : (D.conj g).B ≤ S.M) : g * S.z * g⁻¹ ∈ D.A := by
  by_cases hxB : g * S.z * g⁻¹ ∈ D.B
  · rw [hB g hxB]
    exact D.z_mem_A
  · exact D.mem_A_of_conj_B_le_M_of_not_mem_B hle hxB

theorem mem_A_of_conj_A_le_M {g : G} (hle : (D.conj g).A ≤ S.M) : g * S.z * g⁻¹ ∈ D.A := by
  by_contra hxA
  have hxB : g * S.z * g⁻¹ ∈ D.B := D.swap.mem_A_of_conj_B_le_M_of_not_mem_B (g := g) hle hxA
  exact hxA (by rw [hB g hxB]; exact D.z_mem_A)

theorem inv_conj_mem_A_of_conj_B_le_M {g : G} (hle : (D.conj g).B ≤ S.M) :
    g⁻¹ * S.z * g ∈ D.A := by
  have hxA := D.mem_A_of_conj_B_le_M hB hle
  by_cases hxz : g * S.z * g⁻¹ = S.z
  · have e : g⁻¹ * S.z * g = S.z := by
      calc g⁻¹ * S.z * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hxz]
        _ = S.z := by group
    rw [e]
    exact D.z_mem_A
  · exact D.mem_conj_A.mp (D.z_mem_conj_A hxA hxz)

theorem mem_A_of_commute_B {g : G}
    (h : ∀ b ∈ D.B, g * S.z * g⁻¹ * b = b * (g * S.z * g⁻¹)) : g * S.z * g⁻¹ ∈ D.A := by
  have hle : (D.conj g⁻¹).B ≤ S.M := by
    intro y hy
    rw [D.mem_conj_B, inv_inv] at hy
    rw [S.mem_M_iff]
    have e := h _ hy
    calc y * S.z = g⁻¹ * ((g * y * g⁻¹) * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * (g * y * g⁻¹)) * g := by rw [e]
      _ = S.z * y := by group
  have := D.inv_conj_mem_A_of_conj_B_le_M hB hle
  simpa using this

theorem mem_A_of_mem_QG (h8 : 8 < Nat.card D.A) {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) :
    g * S.z * g⁻¹ ∈ D.A := by
  set x := g * S.z * g⁻¹ with hx
  by_contra hxA
  have hxB : x ∉ D.B := fun h => hxA (by rw [hx, hB g h]; exact D.z_mem_A)
  have hxz : x ≠ S.z := fun h => hxA (h ▸ D.z_mem_A)
  have hzQx : S.z ∈ (S.conjBy g).QG := S.z_mem_Qa_of_mem_QG rfl hxQ hxz
  have hzAx : S.z ∉ (D.conj g).A := fun h => hxA (D.mem_A_of_conj_B_le_M hB fun b hb =>
    S.mem_M_iff.mpr ((D.conj g).comm S.z h b hb).symm)
  have hzBx : S.z ∉ (D.conj g).B := fun h => hxA (D.mem_A_of_conj_A_le_M hB fun a ha =>
    S.mem_M_iff.mpr ((D.conj g).comm a ha S.z h))
  have hxBx : x ∈ (D.conj g).B := D.conj_z_mem_conj_B g
  obtain ⟨a', ha', b', hb', hzab⟩ := (D.conj g).mul S.z hzQx
  have ha'1 : a' ≠ 1 := by
    rintro rfl
    rw [one_mul] at hzab
    exact hzBx (hzab ▸ hb')
  have ha'x : a' ≠ x := by
    rintro rfl
    exact hzBx (hzab ▸ (D.conj g).B.mul_mem hxBx hb')
  obtain ⟨c, hc, hca⟩ := (D.conj g).exists_not_commute_A ha' ha'1 ha'x
  have hcov := cover_of_not_commute (S.conjBy g) (D.conj g).A_le ((D.conj g).A_le ha') hc
    (fun h => hca h.symm)
  have h8' : 8 < Nat.card (D.conj g).A := by rw [D.card_conj_A]; exact h8
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := (D.conj g).exists_commutator_eq_z_of_cover inf_le_left hc
    hcov h8'
  change t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = x at ht
  have htM : ∀ t ∈ (D.conj g).A ⊓ centralizer ({a'} : Set G), t ∈ S.M := by
    intro t ht
    rw [S.mem_M_iff, hzab]
    have h1 := mem_centralizer_singleton_iff.mp ht.2
    have h2 := (D.conj g).comm t ht.1 b' hb'
    calc t * (a' * b') = a' * (t * b') := by rw [← mul_assoc, h1, mul_assoc]
      _ = a' * b' * t := by rw [h2, mul_assoc]
  have hQxx : ∀ y ∈ (S.conjBy g).QG, y * x = x * y := fun y hy =>
    mem_conjBy_M_iff'.mp ((S.conjBy g).QG_le_M hy)
  have hdis : ∀ t ∈ D.B, t * x = x * t → t ∈ (D.conj g).A → t = 1 := by
    intro t htB htx htA
    have htQ := D.B_le htB
    have hcent : t ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) :
        Set G) := by
      refine ⟨htQ, mem_centralizer_iff.mpr fun c hc => ?_⟩
      have hcQ := hc.1
      have hcx := mem_centralizer_singleton_iff.mp hc.2
      have hk : c * t * c⁻¹ * t⁻¹ ∈ (D.conj g).A :=
        (D.conj g).A.mul_mem ((D.conj g).conj_A c (mem_conjBy_M_iff'.mpr hcx) t htA)
          ((D.conj g).A.inv_mem htA)
      rcases S.commutator_eq_one_or_z hcQ htQ with h | h
      · calc c * t = c * t * c⁻¹ * t⁻¹ * (t * c) := by group
          _ = t * c := by rw [h, one_mul]
      · exact absurd (h ▸ hk) hzAx
    rcases (S.mem_centralizer_centralizer_iff hxQ).mp hcent with h | h | h | h
    · exact h
    · exact absurd (h ▸ htA) hzAx
    · exact absurd (h ▸ htB) hxB
    · exact absurd (by simpa [h, mul_assoc, S.z_mul_z] using D.B.mul_mem htB D.z_mem_B) hxB
  have hcommY : ∀ y ∈ (D.conj g).A, y ∈ S.M → ∀ c ∈ D.B, c * x = x * c → y * c = c * y := by
    intro y hyA hyM c hcB hcx
    have hyx := hQxx y ((D.conj g).A_le hyA)
    have hk1 : y * c * y⁻¹ * c⁻¹ ∈ D.B :=
      D.B.mul_mem (D.conj_B y hyM c hcB) (D.B.inv_mem hcB)
    have hk2 : y * c * y⁻¹ * c⁻¹ ∈ (D.conj g).A := by
      rw [show y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) by group]
      exact (D.conj g).A.mul_mem hyA
        ((D.conj g).conj_A c (mem_conjBy_M_iff'.mpr hcx) y⁻¹ ((D.conj g).A.inv_mem hyA))
    have hkx : y * c * y⁻¹ * c⁻¹ * x = x * (y * c * y⁻¹ * c⁻¹) := by
      have hy : Commute y x := hyx
      have hc : Commute c x := hcx
      exact (((hy.mul_left hc).mul_left hy.inv_left).mul_left hc.inv_left).eq
    have h1 := hdis _ hk1 hkx hk2
    calc y * c = y * c * y⁻¹ * c⁻¹ * (c * y) := by group
      _ = c * y := by rw [h1, one_mul]
  obtain ⟨b₀, hb₀, hb₀x⟩ : ∃ b₀ ∈ D.B, b₀ * x ≠ x * b₀ := by
    by_contra h
    push Not at h
    exact hxA (D.mem_A_of_commute hxQ fun b hb => (h b hb).symm)
  have hcovB := cover_of_not_commute S D.B_le hxQ hb₀ hb₀x
  have hfix := conj_commutator_eq_of_fix (F := D.B) (X := D.B ⊓ centralizer ({x} : Set G))
    inf_le_left hb₀ hcovB (D.mem_normalizer_B (htM t₁ ht₁)) (D.mem_normalizer_B (htM t₂ ht₂))
    (fun y hy => hcommY t₁ ht₁.1 (htM t₁ ht₁) y hy.1 (mem_centralizer_singleton_iff.mp hy.2))
    (fun y hy => hcommY t₂ ht₂.1 (htM t₂ ht₂) y hy.1 (mem_centralizer_singleton_iff.mp hy.2))
    hb₀
  rw [ht] at hfix
  apply hb₀x
  calc b₀ * x = x * b₀ * x⁻¹ * x := by rw [hfix]
    _ = x * b₀ := by group

end Fusion

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW
