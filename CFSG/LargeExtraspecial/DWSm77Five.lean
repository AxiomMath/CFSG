module

public import CFSG.LargeExtraspecial.DWSm77Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

section Cover

variable {G : Type*} [Group G]

theorem cover_of_conj_eq_mul_z (S : Setting G) {F : Subgroup G} (hFQ : F ≤ S.QG) {w c : G}
    (hw : ∀ f ∈ F, w * f * w⁻¹ = f ∨ w * f * w⁻¹ = f * S.z) (hcF : c ∈ F)
    (hc : w * c * w⁻¹ = c * S.z) :
    ∀ f ∈ F, f ∈ F ⊓ centralizer ({w} : Set G) ∨
      c⁻¹ * f ∈ F ⊓ centralizer ({w} : Set G) := by
  intro f hf
  rcases hw f hf with h | h
  · refine Or.inl ⟨hf, mem_centralizer_singleton_iff.mpr ?_⟩
    calc f * w = w * f * w⁻¹ * w := by rw [h]
      _ = w * f := by group
  · refine Or.inr ⟨F.mul_mem (F.inv_mem hcF) hf, mem_centralizer_singleton_iff.mpr ?_⟩
    have hv : c⁻¹ * f ∈ S.QG := S.QG.mul_mem (S.QG.inv_mem (hFQ hcF)) (hFQ hf)
    have e : w * (c⁻¹ * f) * w⁻¹ = c⁻¹ * f := by
      calc w * (c⁻¹ * f) * w⁻¹ = (w * c * w⁻¹)⁻¹ * (w * f * w⁻¹) := by group
        _ = S.z⁻¹ * (c⁻¹ * f * S.z) := by rw [hc, h]; group
        _ = c⁻¹ * f := by rw [S.z_comm_QG hv, ← mul_assoc, inv_mul_cancel, one_mul]
    calc c⁻¹ * f * w = w * (c⁻¹ * f) * w⁻¹ * w := by rw [e]
      _ = w * (c⁻¹ * f) := by group

end Cover

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

theorem five_core {g : G} (D' : Decomp (S.conjBy g)) (h8' : 8 < Nat.card D'.A)
    (hyB : ∀ b ∈ D.B, g * S.z * g⁻¹ * b * (g * S.z * g⁻¹)⁻¹ = b ∨
      g * S.z * g⁻¹ * b * (g * S.z * g⁻¹)⁻¹ = b * S.z)
    {c : G} (hcB : c ∈ D.B) (hcy : g * S.z * g⁻¹ * c * (g * S.z * g⁻¹)⁻¹ = c * S.z)
    (hdis : ∀ t ∈ D.B, t * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * t → t ∈ D'.A → t = 1)
    (hnot : ¬ ∀ a ∈ D'.A, a * S.z = S.z * a)
    {k : G} (hkB : k ∈ D.B) (hky : k * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * k)
    (hk2 : k ^ 2 = S.z) : False := by
  set y := g * S.z * g⁻¹ with hydef
  have hTM : ∀ m, m ∈ (S.conjBy g).M ↔ m * y = y * m := fun m => mem_conjBy_M_iff'
  have hcomm : ∀ a ∈ D'.A, a ∈ S.M → ∀ s ∈ D.B, s * y = y * s → a * s = s * a := by
    intro a haA haM s hsB hsy
    have hay : a * y = y * a := (hTM a).mp ((S.conjBy g).QG_le_M (D'.A_le haA))
    have hk1 : a * s * a⁻¹ * s⁻¹ ∈ D.B := D.B.mul_mem (D.conj_B a haM s hsB) (D.B.inv_mem hsB)
    have hk2' : a * s * a⁻¹ * s⁻¹ ∈ D'.A := by
      rw [show a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) by group]
      exact D'.A.mul_mem haA (D'.conj_A s ((hTM s).mpr hsy) a⁻¹ (D'.A.inv_mem haA))
    have hkx : a * s * a⁻¹ * s⁻¹ * y = y * (a * s * a⁻¹ * s⁻¹) := by
      have ha : Commute a y := hay
      have hs : Commute s y := hsy
      exact (((ha.mul_left hs).mul_left ha.inv_left).mul_left hs.inv_left).eq
    have h1 := hdis _ hk1 hkx hk2'
    calc a * s = a * s * a⁻¹ * s⁻¹ * (s * a) := by group
      _ = s * a := by rw [h1, one_mul]
  have hkM : k ∈ (S.conjBy g).M := (hTM k).mpr hky
  have h23 : ∀ f ∈ D'.A,
      k ^ 2 * f * (k ^ 2)⁻¹ = f ∨ k ^ 2 * f * (k ^ 2)⁻¹ = f * (S.conjBy g).z := by
    intro f hf
    refine conj_sq_of_centralizer_le (S.conjBy g) D'.A_le hkM
      (fun f hf => D'.conj_A k hkM f hf) ?_ ?_ hf
    · intro f _
      rw [show k ^ 4 = (k ^ 2) ^ 2 by rw [← pow_mul], hk2, pow_two, S.z_mul_z]
      group
    · intro f hf hf'
      rw [hk2] at hf'
      have hfM : f ∈ S.M := by
        rw [S.mem_M_iff]
        calc f * S.z = S.z * f * S.z⁻¹ * S.z := by rw [hf']
          _ = S.z * f := by group
      rw [← hcomm f hf hfM k hkB hky]
      group
  rw [hk2] at h23
  push Not at hnot
  obtain ⟨c₀, hc₀, hc₀z⟩ := hnot
  have hc₀y : S.z * c₀ * S.z⁻¹ = c₀ * (S.conjBy g).z := by
    rcases h23 c₀ hc₀ with h | h
    · exfalso
      apply hc₀z
      calc c₀ * S.z = S.z * c₀ * S.z⁻¹ * S.z := by rw [h]
        _ = S.z * c₀ := by group
    · exact h
  have hcov := cover_of_conj_eq_mul_z (S.conjBy g) D'.A_le h23 hc₀ hc₀y
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := D'.exists_commutator_eq_z_of_cover inf_le_left hc₀ hcov h8'
  change t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = y at ht
  have ht₁M : t₁ ∈ S.M := S.mem_M_iff.mpr (mem_centralizer_singleton_iff.mp ht₁.2)
  have ht₂M : t₂ ∈ S.M := S.mem_M_iff.mpr (mem_centralizer_singleton_iff.mp ht₂.2)
  have hcovB := cover_of_conj_eq_mul_z S D.B_le hyB hcB hcy
  have hfix := conj_commutator_eq_of_fix (F := D.B) (X := D.B ⊓ centralizer ({y} : Set G))
    inf_le_left hcB hcovB (D.mem_normalizer_B ht₁M) (D.mem_normalizer_B ht₂M)
    (fun s hs => hcomm t₁ ht₁.1 ht₁M s hs.1 (mem_centralizer_singleton_iff.mp hs.2))
    (fun s hs => hcomm t₂ ht₂.1 ht₂M s hs.1 (mem_centralizer_singleton_iff.mp hs.2)) hcB
  rw [ht, hcy] at hfix
  exact S.z_ne_one (by simpa using hfix)

theorem exists_ne_of_cover_B {X : Subgroup G} {c : G} (hcB : c ∈ D.B)
    (hcov : ∀ f ∈ D.B, f ∈ X ∨ c⁻¹ * f ∈ X) : ∃ k ∈ X, k ≠ 1 ∧ k ≠ S.z := by
  by_contra h
  push Not at h
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := D.swap.exists_commutator_eq_z_A
  change t₁ ∈ D.B at ht₁
  change t₂ ∈ D.B at ht₂
  have hcQ := D.B_le hcB
  have hcl : ∀ f ∈ D.B, S.cl f = 0 ∨ S.cl f = S.cl c := by
    intro f hf
    have hfQ := D.B_le hf
    rcases hcov f hf with h1 | h1
    · left
      rw [S.cl_eq_zero_iff hfQ]
      by_cases hf1 : f = 1
      · exact Or.inl hf1
      · exact Or.inr (h f h1 hf1)
    · right
      have e : S.cl f = S.cl c + S.cl (c⁻¹ * f) := by
        rw [← S.cl_mul hcQ (S.QG.mul_mem (S.QG.inv_mem hcQ) hfQ)]
        congr 1
        group
      have h0 : S.cl (c⁻¹ * f) = 0 := by
        rw [S.cl_eq_zero_iff (S.QG.mul_mem (S.QG.inv_mem hcQ) hfQ)]
        by_cases hf1 : c⁻¹ * f = 1
        · exact Or.inl hf1
        · exact Or.inr (h _ h1 hf1)
      rw [e, h0, add_zero]
  have hpol : polar S.q (S.cl t₁) (S.cl t₂) = 0 := by
    rcases hcl t₁ ht₁ with h1 | h1 <;> rcases hcl t₂ ht₂ with h2 | h2
    · rw [h1, polar_zero_left]
    · rw [h1, polar_zero_left]
    · rw [h2, polar_zero_right]
    · rw [h1, h2, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero]
  have hc := (S.polar_cl_eq_zero_iff (D.B_le ht₁) (D.B_le ht₂)).mp hpol
  apply S.z_ne_one
  rw [← ht]
  calc t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = t₂ * t₁ * t₁⁻¹ * t₂⁻¹ := by rw [hc]
    _ = 1 := by group

section Five

variable (hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z) (h8 : 8 < Nat.card D.A)
  (hB8 : 8 < Nat.card D.B ∨ ∀ b ∈ D.B, b ^ 2 = 1 → b = 1 ∨ b = S.z)

include hB h8 hB8 in
theorem mem_A_of_conj_B {g : G}
    (hy : ∀ b ∈ D.B, g * S.z * g⁻¹ * b * (g * S.z * g⁻¹)⁻¹ = b ∨
      g * S.z * g⁻¹ * b * (g * S.z * g⁻¹)⁻¹ = b * S.z) : g * S.z * g⁻¹ ∈ D.A := by
  set y := g * S.z * g⁻¹ with hydef
  by_contra hyA
  have hyQ : y ∉ S.QG := fun h => hyA (D.mem_A_of_mem_QG hB h8 h)
  obtain ⟨c, hcB, hcy⟩ : ∃ c ∈ D.B, y * c * y⁻¹ = c * S.z := by
    by_contra h
    push Not at h
    refine hyA (D.mem_A_of_commute_B hB fun b hb => ?_)
    have := (hy b hb).resolve_right (h b hb)
    calc y * b = y * b * y⁻¹ * y := by group
      _ = b * y := by rw [this]
  have hcQ := D.B_le hcB
  have hzQy : S.z ∉ (S.conjBy g).QG := by
    intro h
    have hw : g⁻¹ * S.z * g⁻¹⁻¹ ∈ S.QG := by
      have := (mem_conjBy_QG_iff S).mp h
      simpa using this
    have hwA := D.mem_A_of_mem_QG hB h8 hw
    by_cases hwz : g⁻¹ * S.z * g⁻¹⁻¹ = S.z
    · apply hyA
      have e : y = S.z := by
        calc y = g * S.z * g⁻¹ := hydef
          _ = g * (g⁻¹ * S.z * g⁻¹⁻¹) * g⁻¹ := by rw [hwz]
          _ = S.z := by group
      rw [e]
      exact D.z_mem_A
    · have hcM := D.conj_B_le_M hwA hwz (conj_mem_map_conj g⁻¹ hcB)
      rw [S.mem_M_iff] at hcM
      have hcy' : y * c * y⁻¹ = c := by
        calc y * c * y⁻¹ = g * (S.z * (g⁻¹ * c * g⁻¹⁻¹)) * g⁻¹ * y⁻¹ := by rw [hydef]; group
          _ = g * (g⁻¹ * c * g⁻¹⁻¹ * S.z) * g⁻¹ * y⁻¹ := by rw [hcM]
          _ = c := by rw [hydef]; group
      rw [hcy'] at hcy
      exact S.z_ne_one (by simpa using hcy.symm)
  have hXc : ∀ t ∈ D.B, t ∈ (S.conjBy g).QG → ∀ s ∈ D.B, s * y = y * s → t * s = s * t := by
    intro t htB htQ s hsB hsy
    rcases S.commutator_eq_one_or_z (D.B_le hsB) (D.B_le htB) with h | h
    · calc t * s = s * t * s⁻¹ * t⁻¹ * (t * s) := by rw [h, one_mul]
        _ = s * t := by group
    · exfalso
      apply hzQy
      rw [← h]
      exact (S.conjBy g).QG.mul_mem
        ((S.conjBy g).conj_mem_QG (mem_conjBy_M_iff'.mpr hsy) htQ) ((S.conjBy g).QG.inv_mem htQ)
  have hcovB := cover_of_conj_eq_mul_z S D.B_le hy hcB hcy
  have hBall : ∀ t : G, t * c = c * t → (∀ s ∈ D.B, s * y = y * s → t * s = s * t) →
      ∀ f ∈ D.B, t * f = f * t := by
    intro t htc htX f hf
    rcases hcovB f hf with h | h
    · exact htX f h.1 (mem_centralizer_singleton_iff.mp h.2)
    · have e := htX _ h.1 (mem_centralizer_singleton_iff.mp h.2)
      calc t * f = t * c * (c⁻¹ * f) := by group
        _ = c * (t * (c⁻¹ * f)) := by rw [htc, mul_assoc]
        _ = f * t := by rw [e]; group
  have hnc : ∀ t ∈ D.B, t ∈ (S.conjBy g).QG → t ≠ 1 → t * c ≠ c * t := by
    intro t htB htQ ht1 htc
    have htA := D.mem_A_of_commute (D.B_le htB) (hBall t htc (hXc t htB htQ))
    rcases D.inter t htA htB with h | h
    · exact ht1 h
    · exact hzQy (h ▸ htQ)
  have hnotboth : ∀ t₁ ∈ D.B, t₁ ∈ (D.conj g).A → t₁ ≠ 1 →
      ∀ t₂ ∈ D.B, t₂ ∈ (D.conj g).B → t₂ ≠ 1 → False := by
    intro t₁ ht₁B ht₁A ht₁1 t₂ ht₂B ht₂B' ht₂1
    have ht₁Q := (D.conj g).A_le ht₁A
    have ht₂Q := (D.conj g).B_le ht₂B'
    have h1 := (S.polar_cl_eq_one_iff (D.B_le ht₁B) hcQ).mpr (hnc t₁ ht₁B ht₁Q ht₁1)
    have h2 := (S.polar_cl_eq_one_iff (D.B_le ht₂B) hcQ).mpr (hnc t₂ ht₂B ht₂Q ht₂1)
    have h12c : t₁ * t₂ * c = c * (t₁ * t₂) := by
      have hp : polar S.q (S.cl (t₁ * t₂)) (S.cl c) = 0 := by
        rw [S.cl_mul (D.B_le ht₁B) (D.B_le ht₂B), polar_add_left, h1, h2]
        decide
      exact (S.polar_cl_eq_zero_iff (S.QG.mul_mem (D.B_le ht₁B) (D.B_le ht₂B)) hcQ).mp hp
    have h12X : ∀ s ∈ D.B, s * y = y * s → t₁ * t₂ * s = s * (t₁ * t₂) := by
      intro s hsB hsy
      rw [mul_assoc, hXc t₂ ht₂B ht₂Q s hsB hsy, ← mul_assoc, hXc t₁ ht₁B ht₁Q s hsB hsy,
        mul_assoc]
    have h12B := D.B.mul_mem ht₁B ht₂B
    have h12A := D.mem_A_of_commute (D.B_le h12B) (hBall _ h12c h12X)
    rcases D.inter _ h12A h12B with h | h
    · have e : t₁ = t₂⁻¹ := eq_inv_of_mul_eq_one_left h
      rcases (D.conj g).inter t₁ ht₁A (e ▸ (D.conj g).B.inv_mem ht₂B') with h' | h'
      · exact ht₁1 h'
      · have h'' := D.B_le ht₁B
        rw [h'] at h''
        exact hyQ h''
    · exact hzQy (h ▸ (S.conjBy g).QG.mul_mem ht₁Q ht₂Q)
  have hnotA : ¬ ∀ a ∈ (D.conj g).A, a * S.z = S.z * a := fun h =>
    hyA (D.mem_A_of_conj_A_le_M hB fun a ha => S.mem_M_iff.mpr (h a ha))
  have hnotB : ¬ ∀ b ∈ (D.conj g).B, b * S.z = S.z * b := fun h =>
    hyA (D.mem_A_of_conj_B_le_M hB fun b hb => S.mem_M_iff.mpr (h b hb))
  have hk : ∃ k ∈ D.B ⊓ centralizer ({y} : Set G), k ^ 2 = S.z := by
    rcases hB8 with h | h
    · exact D.swap.exists_sq_eq_z_of_cover (X := D.B ⊓ centralizer ({y} : Set G)) inf_le_left
        hcB hcovB h
    · obtain ⟨k, hk, hk1, hkz⟩ := D.exists_ne_of_cover_B hcB hcovB
      refine ⟨k, hk, ?_⟩
      rcases S.sq_eq_one_or_z (D.B_le hk.1) with h2 | h2
      · rcases h k hk.1 h2 with h3 | h3
        exacts [absurd h3 hk1, absurd h3 hkz]
      · exact h2
  obtain ⟨k, hkX, hk2⟩ := hk
  have hky : k * y = y * k := mem_centralizer_singleton_iff.mp hkX.2
  by_cases hA' : ∀ t ∈ D.B, t * y = y * t → t ∈ (D.conj g).A → t = 1
  · exact D.five_core (D.conj g) (by rw [D.card_conj_A]; exact h8) hy hcB hcy hA' hnotA
      hkX.1 hky hk2
  push Not at hA'
  obtain ⟨t₁, ht₁B, -, ht₁A, ht₁1⟩ := hA'
  have hB' : ∀ t ∈ D.B, t * y = y * t → t ∈ (D.conj g).swap.A → t = 1 := fun t htB _ htB' => by
    by_contra ht1
    exact hnotboth t₁ ht₁B ht₁A ht₁1 t htB htB' ht1
  have hB8' : 8 < Nat.card D.B := by
    rcases hB8 with h | h
    · exact h
    · exfalso
      have ht₁Q := (D.conj g).A_le ht₁A
      have ht₁z : t₁ ≠ S.z := fun h' => hzQy (h' ▸ ht₁Q)
      rcases S.sq_eq_one_or_z (D.B_le ht₁B) with h2 | h2
      · rcases h t₁ ht₁B h2 with h3 | h3
        exacts [ht₁1 h3, ht₁z h3]
      · exact hzQy (h2 ▸ (S.conjBy g).QG.pow_mem ht₁Q 2)
  exact D.five_core (D.conj g).swap (by rw [swap_A, D.card_conj_B]; exact hB8') hy hcB hcy hB'
    hnotB hkX.1 hky hk2

omit h8 in
include hB in
theorem conj_hB (g : G) : ∀ k : G, k * (S.conjBy g).z * k⁻¹ ∈ (D.conj g).B →
    k * (S.conjBy g).z * k⁻¹ = (S.conjBy g).z := by
  intro k hk
  rw [Setting.conjBy_z] at hk ⊢
  rw [D.mem_conj_B] at hk
  have e : g⁻¹ * (k * (g * S.z * g⁻¹) * k⁻¹) * g = g⁻¹ * k * g * S.z * (g⁻¹ * k * g)⁻¹ := by
    group
  rw [e] at hk
  have h' := hB _ hk
  calc k * (g * S.z * g⁻¹) * k⁻¹ = g * (g⁻¹ * k * g * S.z * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
    _ = g * S.z * g⁻¹ := by rw [h']

omit hB h8 in
include hB8 in
theorem conj_hB8 (g : G) : 8 < Nat.card (D.conj g).B ∨
    ∀ b ∈ (D.conj g).B, b ^ 2 = 1 → b = 1 ∨ b = (S.conjBy g).z := by
  rcases hB8 with h' | h'
  · left
    rw [D.card_conj_B]
    exact h'
  · right
    intro b hb hb2
    rw [D.mem_conj_B] at hb
    have hb2' : (g⁻¹ * b * g) ^ 2 = 1 := by
      rw [show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hb2]
      group
    rcases h' _ hb hb2' with e | e
    · left
      calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    · right
      rw [Setting.conjBy_z]
      calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = g * S.z * g⁻¹ := by rw [e]

include hB h8 hB8 in
theorem mem_conj_A_of_commute {g h : G} (hxA : g * S.z * g⁻¹ ∈ D.A) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyA : h * S.z * h⁻¹ ∈ D.A)
    (hxy : g * S.z * g⁻¹ * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * (g * S.z * g⁻¹)) :
    h * S.z * h⁻¹ ∈ (D.conj g).A := by
  have e : h * g⁻¹ * (S.conjBy g).z * (h * g⁻¹)⁻¹ = h * S.z * h⁻¹ := by
    rw [Setting.conjBy_z]
    group
  have hyM : h * S.z * h⁻¹ ∈ (S.conjBy g).M := mem_conjBy_M_iff'.mpr hxy.symm
  have hle := D.conj_B_le_M hxA hxz
  have key := (D.conj g).mem_A_of_conj_B (D.conj_hB hB g) (by rw [D.card_conj_A]; exact h8)
    (D.conj_hB8 hB8 g) (g := h * g⁻¹) ?_
  · rwa [e] at key
  intro b hb
  rw [e]
  have hbM := hle hb
  have ht : h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹ * b⁻¹ ∈ D.A := by
    rw [show h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹ * b⁻¹ =
      h * S.z * h⁻¹ * (b * (h * S.z * h⁻¹)⁻¹ * b⁻¹) by group]
    exact D.A.mul_mem hyA (D.conj_A b hbM _ (D.A.inv_mem hyA))
  have ht' : h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹ * b⁻¹ ∈ (D.conj g).B :=
    (D.conj g).B.mul_mem ((D.conj g).conj_B _ hyM b hb) ((D.conj g).B.inv_mem hb)
  have hbx : b * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * b :=
    mem_conjBy_M_iff'.mp ((S.conjBy g).QG_le_M ((D.conj g).B_le hb))
  rcases D.conj_B_inf_QG hxA hxz ht' (D.A_le ht) with h1 | h1
  · left
    calc h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹
        = h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹ * b⁻¹ * b := by group
      _ = b := by rw [h1, one_mul]
  · right
    rw [Setting.conjBy_z]
    calc h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹
        = h * S.z * h⁻¹ * b * (h * S.z * h⁻¹)⁻¹ * b⁻¹ * b := by group
      _ = g * S.z * g⁻¹ * b := by rw [h1]
      _ = b * (g * S.z * g⁻¹) := hbx.symm

end Five

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW
