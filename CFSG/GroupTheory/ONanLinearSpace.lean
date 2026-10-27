module

public import CFSG.GroupTheory.ONanTheoremB

import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

namespace CFSG.GroupTheory.ONan

open MulAction Subgroup
open scoped Pointwise

private theorem onanL_disjoint_diffs {Ω : Type*} (Γ : Ω → Ω → Set Ω)
    (hmem : ∀ u v, u ≠ v → u ∈ Γ u v ∧ v ∈ Γ u v)
    (hsymm : ∀ u v, u ≠ v → Γ u v = Γ v u)
    (hline : ∀ u v w, u ≠ v → w ∈ Γ u v → w ≠ u → Γ u w = Γ u v)
    {u v p : Ω} (huv : u ≠ v) (hp : p ∉ Γ u v)
    {q q' : Ω} (hq : q ∈ Γ u v) (hq' : q' ∈ Γ u v) (hqq' : q ≠ q') :
    Disjoint (Γ p q \ {p}) (Γ p q' \ {p}) := by
  rw [Set.disjoint_left]
  rintro r ⟨hrq, hrp⟩ ⟨hrq', -⟩
  rw [Set.mem_singleton_iff] at hrp
  have hpq : p ≠ q := fun h => hp (h ▸ hq)
  have hpq' : p ≠ q' := fun h => hp (h ▸ hq')
  have hEq : Γ p q = Γ p q' :=
    (hline p q r hpq hrq hrp).symm.trans (hline p q' r hpq' hrq' hrp)
  have hq'Γ : q' ∈ Γ p q := hEq ▸ (hmem p q' hpq').2
  have hq'Γqp : q' ∈ Γ q p := by
    rw [← hsymm p q hpq]
    exact hq'Γ
  have hpΓqp : p ∈ Γ q p := (hmem q p hpq.symm).2
  have hEqL : Γ q q' = Γ u v := by
    by_cases hqu : q = u
    · rw [hqu]
      exact hline u v q' huv hq' (fun h => hqq' (hqu.trans h.symm))
    · have hLq : Γ u q = Γ u v := hline u v q huv hq hqu
      have hLqu : Γ q u = Γ u v := by
        rw [← hsymm u q (Ne.symm hqu)]
        exact hLq
      have hq'Γqu : q' ∈ Γ q u := by rw [hLqu]; exact hq'
      exact (hline q u q' hqu hq'Γqu hqq'.symm).trans hLqu
  have hpL : p ∈ Γ u v := by
    rw [← hEqL, hline q p q' hpq.symm hq'Γqp hqq'.symm]
    exact hpΓqp
  exact hp hpL

private theorem onanL_ncard_biUnion_diffs {Ω : Type*} [Finite Ω] (Γ : Ω → Ω → Set Ω) {s : ℕ}
    (hmem : ∀ u v, u ≠ v → u ∈ Γ u v ∧ v ∈ Γ u v)
    (hsymm : ∀ u v, u ≠ v → Γ u v = Γ v u)
    (hline : ∀ u v w, u ≠ v → w ∈ Γ u v → w ≠ u → Γ u w = Γ u v)
    (hcard : ∀ u v, u ≠ v → (Γ u v).ncard = s + 1)
    {u v p : Ω} (huv : u ≠ v) (hp : p ∉ Γ u v) :
    (⋃ q ∈ Γ u v, (Γ p q \ {p})).ncard = (s + 1) * s := by
  have hdisj : (Γ u v).PairwiseDisjoint (fun q => Γ p q \ {p}) :=
    fun q hq q' hq' hne => onanL_disjoint_diffs Γ hmem hsymm hline huv hp hq hq' hne
  have hdiff : ∀ q ∈ Γ u v, (Γ p q \ {p}).ncard = s := by
    intro q hq
    have hpq : p ≠ q := fun h => hp (h ▸ hq)
    rw [Set.ncard_diff_singleton_of_mem (hmem p q hpq).1, hcard p q hpq]
    omega
  have hcount : (⋃ q ∈ Γ u v, (Γ p q \ {p})).ncard =
      ∑ᶠ q ∈ Γ u v, (Γ p q \ {p}).ncard :=
    Set.Finite.ncard_biUnion (Set.toFinite (Γ u v)) (fun _ _ => Set.toFinite _) hdisj
  have hsum : (∑ᶠ q ∈ Γ u v, (Γ p q \ {p}).ncard) = s * (Γ u v).ncard := by
    have h1 : (∑ᶠ q ∈ Γ u v, (Γ p q \ {p}).ncard) = ∑ᶠ q ∈ Γ u v, s :=
      finsum_mem_congr rfl fun q hq => hdiff q hq
    rw [h1, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite (Γ u v)), Finset.sum_const,
      ← Set.ncard_eq_toFinset_card (Γ u v) (Set.toFinite (Γ u v))]
    simp [smul_eq_mul, mul_comm]
  rw [hcount, hsum, hcard u v huv]
  ring

theorem mul_add_one_le_natCard_of_lines {Ω : Type*} [Finite Ω] (Γ : Ω → Ω → Set Ω) {s : ℕ}
    (hmem : ∀ u v, u ≠ v → u ∈ Γ u v ∧ v ∈ Γ u v)
    (hsymm : ∀ u v, u ≠ v → Γ u v = Γ v u)
    (hline : ∀ u v w, u ≠ v → w ∈ Γ u v → w ≠ u → Γ u w = Γ u v)
    (hcard : ∀ u v, u ≠ v → (Γ u v).ncard = s + 1)
    {u v w : Ω} (huv : u ≠ v) (hw : w ∉ Γ u v) :
    (s + 1) * s + 1 ≤ Nat.card Ω := by
  classical
  haveI : Nonempty Ω := ⟨w⟩
  have hUcard := onanL_ncard_biUnion_diffs Γ hmem hsymm hline hcard huv hw
  have hsub : (⋃ q ∈ Γ u v, (Γ w q \ {w})) ⊆ ({w}ᶜ : Set Ω) := by
    rintro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    exact hxq.2
  have hcompl : ({w}ᶜ : Set Ω).ncard = Nat.card Ω - 1 := by
    rw [Set.ncard_compl, Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hUcard, hcompl] at hle
  have hpos : 0 < Nat.card Ω := Nat.card_pos
  omega

private def onanL_conjAt {X Ω : Type*} [Group X] [MulAction X Ω] (α : Ω) (A : Subgroup X)
    (u : Ω) : Subgroup X where
  carrier := {x | ∀ g : X, g • α = u → g⁻¹ * x * g ∈ A}
  mul_mem' := by
    intro x y hx hy g hg
    have h := A.mul_mem (hx g hg) (hy g hg)
    convert h using 1
    group
  one_mem' := by
    intro g _
    simpa using A.one_mem
  inv_mem' := by
    intro x hx g hg
    have h := A.inv_mem (hx g hg)
    convert h using 1
    group

private def onanL_K {X Ω : Type*} [Group X] [MulAction X Ω] (α : Ω) (A : Subgroup X)
    (u v : Ω) : Subgroup X := onanL_conjAt α A u ⊓ stabilizer X v

private def onanL_Gamma {X Ω : Type*} [Group X] [MulAction X Ω] (α : Ω) (A : Subgroup X)
    (u v : Ω) : Set Ω := {γ | ∀ k ∈ onanL_K α A u v, k • γ = γ}

private theorem onanL_exists_smul_eq {X Ω : Type*} [Group X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (α u : Ω) : ∃ g : X, g • α = u := by
  by_cases h : u = α
  · exact ⟨1, by rw [h, one_smul]⟩
  · obtain ⟨g, hg, -⟩ := h2 α u u α (Ne.symm h) h
    exact ⟨g, hg⟩

private theorem onanL_conjAt_self {X Ω : Type*} [Group X] [MulAction X Ω] {α : Ω}
    {A : Subgroup X} (hAN : stabilizer X α ≤ Subgroup.normalizer (A : Set X)) :
    onanL_conjAt α A α = A := by
  ext x
  constructor
  · intro hx
    simpa using hx 1 (one_smul X α)
  · intro hx g hg
    have hgN : g ∈ Subgroup.normalizer (A : Set X) := hAN hg
    exact (Subgroup.mem_set_normalizer_iff''.mp hgN x).mp hx

private theorem onanL_mem_K_conj {X Ω : Type*} [Group X] [MulAction X Ω] {α : Ω}
    {A : Subgroup X} (g : X) (u v : Ω) (k : X) :
    k ∈ onanL_K α A u v ↔ g * k * g⁻¹ ∈ onanL_K α A (g • u) (g • v) := by
  constructor
  · rintro ⟨hk1, hk2⟩
    refine ⟨?_, ?_⟩
    · intro h hh
      have hhu : (g⁻¹ * h) • α = u := by
        rw [mul_smul, hh, inv_smul_smul]
      have hx := hk1 (g⁻¹ * h) hhu
      have heq : (g⁻¹ * h)⁻¹ * k * (g⁻¹ * h) = h⁻¹ * (g * k * g⁻¹) * h := by
        group
      rwa [heq] at hx
    · refine MulAction.mem_stabilizer_iff.mpr ?_
      have hkv : k • v = v := MulAction.mem_stabilizer_iff.mp hk2
      calc (g * k * g⁻¹) • (g • v) = g • (k • v) := by
            rw [mul_smul, mul_smul, inv_smul_smul]
        _ = g • v := by rw [hkv]
  · rintro ⟨hk1, hk2⟩
    refine ⟨?_, ?_⟩
    · intro h hh
      have hh' : (g * h) • α = g • u := by rw [mul_smul, hh]
      have hx := hk1 (g * h) hh'
      have heq : (g * h)⁻¹ * (g * k * g⁻¹) * (g * h) = h⁻¹ * k * h := by
        group
      rwa [heq] at hx
    · refine MulAction.mem_stabilizer_iff.mpr ?_
      have h := congrArg (fun ω => g⁻¹ • ω) (MulAction.mem_stabilizer_iff.mp hk2)
      simpa [mul_smul] using h

private theorem onanL_K_fixes {X Ω : Type*} [Group X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    {α : Ω} {A : Subgroup X} (hAα : A ≤ stabilizer X α)
    {u v : Ω} {k : X} (hk : k ∈ onanL_K α A u v) :
    k • u = u ∧ k • v = v := by
  constructor
  · obtain ⟨g, hg⟩ := onanL_exists_smul_eq h2 α u
    have hfix : (g⁻¹ * k * g) • α = α := hAα (hk.1 g hg)
    calc k • u = k • (g • α) := by rw [hg]
      _ = (k * g) • α := (mul_smul k g α).symm
      _ = (g * (g⁻¹ * k * g)) • α := by
            rw [show k * g = g * (g⁻¹ * k * g) by group]
      _ = g • ((g⁻¹ * k * g) • α) := mul_smul g (g⁻¹ * k * g) α
      _ = g • α := by rw [hfix]
      _ = u := hg
  · exact MulAction.mem_stabilizer_iff.mp hk.2

private theorem onanL_isPGroup_K {X Ω : Type*} [Group X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    {α : Ω} {A : Subgroup X} {p : ℕ} (hAp : IsPGroup p A) {u v : Ω} :
    IsPGroup p (onanL_K α A u v) := by
  obtain ⟨g, hg⟩ := onanL_exists_smul_eq h2 α u
  refine IsPGroup.to_le (IsPGroup.map hAp (MulAut.conj g).toMonoidHom) ?_
  intro k hk
  rw [Subgroup.mem_map]
  refine ⟨g⁻¹ * k * g, hk.1 g hg, ?_⟩
  change (MulAut.conj g) (g⁻¹ * k * g) = k
  rw [MulAut.conj_apply]
  group

private theorem onanL_Gamma_facts {X : Type} {Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    {α : Ω} {A : Subgroup X} (hAα : A ≤ stabilizer X α)
    {p : ℕ} [Fact p.Prime] (hAp : IsPGroup p A) :
    (∀ u v, u ≠ v → u ∈ onanL_Gamma α A u v ∧ v ∈ onanL_Gamma α A u v) ∧
      (∀ u v, u ≠ v → onanL_Gamma α A u v = onanL_Gamma α A v u) ∧
      (∀ u v w, u ≠ v → w ∈ onanL_Gamma α A u v → w ≠ u →
        onanL_Gamma α A u w = onanL_Gamma α A u v) := by
  have hKconj : ∀ (g : X) (u v : Ω) (k : X),
      k ∈ onanL_K α A u v ↔ g * k * g⁻¹ ∈ onanL_K α A (g • u) (g • v) :=
    fun g u v k => onanL_mem_K_conj g u v k
  have hKp : ∀ u v, u ≠ v → IsPGroup p (onanL_K α A u v) :=
    fun _ _ _ => onanL_isPGroup_K h2 hAp
  have hKfix : ∀ u v, u ≠ v → ∀ k ∈ onanL_K α A u v, k • u = u ∧ k • v = v :=
    fun _ _ _ k hk => onanL_K_fixes h2 hAα hk
  have hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ onanL_K α A u v,
      k • w = w → k ∈ onanL_K α A u w :=
    fun _ _ _ _ _ _ k hk hkw => ⟨hk.1, MulAction.mem_stabilizer_iff.mpr hkw⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact ⟨fun k hk => (hKfix u v huv k hk).1, fun k hk => (hKfix u v huv k hk).2⟩
  · intro u v huv
    ext γ
    constructor
    · intro hγ
      have hγ' : ∀ k ∈ onanL_K α A u v, k • γ = γ := hγ
      exact fixed_of_fixed_of_isPGroup (X := X) (Ω := Ω) (K := onanL_K α A)
        (z := γ) h2 hKp hKfix hKconj hKsc (Ne.symm huv) hγ'
    · intro hγ
      have hγ' : ∀ k ∈ onanL_K α A v u, k • γ = γ := hγ
      exact fixed_of_fixed_of_isPGroup (X := X) (Ω := Ω) (K := onanL_K α A)
        (z := γ) h2 hKp hKfix hKconj hKsc huv hγ'
  · intro u v w huv hw hwu
    have hw' : ∀ k ∈ onanL_K α A u v, k • w = w := hw
    have hKuw : onanL_K α A u w = onanL_K α A u v :=
      eq_of_fixed (X := X) (Ω := Ω) (K := onanL_K α A) (u := u) (v := v) (w := w)
        h2 hKconj hKsc huv hwu hw'
    ext γ
    simp only [onanL_Gamma, hKuw]

private theorem onanL_Gamma_conj {X Ω : Type*} [Group X] [MulAction X Ω] {α : Ω}
    {A : Subgroup X} (g : X) (u v : Ω) :
    onanL_Gamma α A (g • u) (g • v) = g • onanL_Gamma α A u v := by
  ext γ
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hγ k hk
    have hk' : g * k * g⁻¹ ∈ onanL_K α A (g • u) (g • v) :=
      (onanL_mem_K_conj g u v k).mp hk
    have h := congrArg (fun ω => g⁻¹ • ω) (hγ (g * k * g⁻¹) hk')
    simpa [mul_smul] using h
  · intro hγ k hk
    have hk' : g⁻¹ * k * g ∈ onanL_K α A u v := by
      have h := (onanL_mem_K_conj g⁻¹ (g • u) (g • v) k).mp hk
      simpa using h
    have h := congrArg (fun ω => g • ω) (hγ (g⁻¹ * k * g) hk')
    simpa [mul_smul] using h

private theorem onanL_Gamma_ncard_eq {X Ω : Type*} [Group X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    {α β : Ω} (hαβ : α ≠ β) {A : Subgroup X} {u v : Ω} (huv : u ≠ v) :
    (onanL_Gamma α A u v).ncard = (onanL_Gamma α A α β).ncard := by
  obtain ⟨g, hgu, hgv⟩ := h2 α β u v hαβ huv
  calc (onanL_Gamma α A u v).ncard = (g • onanL_Gamma α A α β).ncard := by
        rw [← hgu, ← hgv, onanL_Gamma_conj]
    _ = (onanL_Gamma α A α β).ncard := Set.ncard_smul_set g _

private theorem onanL_orbit_subset_Gamma {X Ω : Type*} [Group X] [MulAction X Ω] {α β : Ω}
    {A P : Subgroup X} (hPA : ∀ x ∈ P, ∀ a ∈ A, Commute x a)
    (hAself : onanL_conjAt α A α = A) :
    orbit P β ⊆ onanL_Gamma α A α β := by
  rintro γ ⟨x, rfl⟩
  intro k hk
  change k • ((x : X) • β) = (x : X) • β
  have hkA : k ∈ A := by
    rw [← hAself]
    exact hk.1
  have hkβ : k • β = β := MulAction.mem_stabilizer_iff.mp hk.2
  have hcomm : Commute (x : X) k := hPA x x.2 k hkA
  calc k • ((x : X) • β) = (k * (x : X)) • β := (mul_smul k (x : X) β).symm
    _ = ((x : X) * k) • β := by rw [hcomm.eq]
    _ = (x : X) • (k • β) := mul_smul (x : X) k β
    _ = (x : X) • β := by rw [hkβ]

private theorem onanL_notMem_orbit {X Ω : Type*} [Group X] [MulAction X Ω] {α β : Ω}
    {P : Subgroup X} (hPα : P ≤ stabilizer X α) (hβ : β ≠ α) :
    α ∉ orbit P β := by
  rintro ⟨x, hxβ⟩
  change (x : X) • β = α at hxβ
  have hxα : (x : X) • α = α := MulAction.mem_stabilizer_iff.mp (hPα x.2)
  have hxinv : (x : X)⁻¹ • α = α := by
    calc (x : X)⁻¹ • α = (x : X)⁻¹ • ((x : X) • α) := by rw [hxα]
      _ = ((x : X)⁻¹ * (x : X)) • α := (mul_smul (x : X)⁻¹ (x : X) α).symm
      _ = α := by rw [inv_mul_cancel, one_smul]
  apply hβ
  calc β = (x : X)⁻¹ • ((x : X) • β) := (inv_smul_smul (x : X) β).symm
    _ = (x : X)⁻¹ • α := by rw [hxβ]
    _ = α := hxinv

private theorem onanL_m_le_s {X Ω : Type*} [Group X] [Finite Ω] [MulAction X Ω] {α β : Ω}
    {A P : Subgroup X} {m : ℕ} (hPA : ∀ x ∈ P, ∀ a ∈ A, Commute x a)
    (hPα : P ≤ stabilizer X α) (hAself : onanL_conjAt α A α = A)
    (hαΓ : α ∈ onanL_Gamma α A α β) (hβ : β ≠ α)
    (horb : m ≤ (orbit P β).ncard) :
    m ≤ (onanL_Gamma α A α β).ncard - 1 := by
  have hsub : orbit P β ⊆ onanL_Gamma α A α β :=
    onanL_orbit_subset_Gamma hPA hAself
  have hnot : α ∉ orbit P β := onanL_notMem_orbit hPα hβ
  have hins : (insert α (orbit P β)).ncard = (orbit P β).ncard + 1 :=
    Set.ncard_insert_of_notMem hnot (Set.toFinite _)
  have hle : (orbit P β).ncard + 1 ≤ (onanL_Gamma α A α β).ncard := by
    rw [← hins]
    exact Set.ncard_le_ncard (Set.insert_subset hαΓ hsub) (Set.toFinite _)
  omega

theorem semiregular_of_isPGroup_of_commute {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] [Finite Ω] [FaithfulSMul X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d) {α : Ω}
    {p : ℕ} [Fact p.Prime] {A : Subgroup X} (hAα : A ≤ stabilizer X α)
    (hAN : stabilizer X α ≤ normalizer (A : Set X)) (hAp : IsPGroup p A)
    {P : Subgroup X} (hPα : P ≤ stabilizer X α) (hPA : ∀ x ∈ P, ∀ a ∈ A, Commute x a) {m : ℕ}
    (horb : ∀ β : Ω, β ≠ α → m ≤ (orbit P β).ncard) (hlt : Nat.card Ω < m ^ 2 + 1) :
    ∀ a ∈ A, ∀ β : Ω, a • β = β → β ≠ α → a = 1 := by
  classical
  intro a haA β hβfix hβne
  by_contra ha1
  have hαβ : α ≠ β := hβne.symm
  obtain ⟨hmem, hsymm, hline⟩ := onanL_Gamma_facts h2 hAα hAp
  have hAself : onanL_conjAt α A α = A := onanL_conjAt_self hAN
  have hαΓ : α ∈ onanL_Gamma α A α β := (hmem α β hαβ).1
  let s : ℕ := (onanL_Gamma α A α β).ncard - 1
  have hcard : ∀ u v, u ≠ v → (onanL_Gamma α A u v).ncard = s + 1 := by
    intro u v huv
    rw [onanL_Gamma_ncard_eq h2 hαβ huv]
    have hpos : 0 < (onanL_Gamma α A α β).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨α, hαΓ⟩
    simp only [s]
    omega
  have haK : a ∈ onanL_K α A α β := by
    refine ⟨?_, MulAction.mem_stabilizer_iff.mpr hβfix⟩
    rw [hAself]
    exact haA
  obtain ⟨w, hwne⟩ : ∃ w : Ω, a • w ≠ w := by
    by_contra h
    have hall : ∀ w : Ω, a • w = w := fun w => by
      by_contra hw
      exact h ⟨w, hw⟩
    exact ha1 (FaithfulSMul.eq_of_smul_eq_smul (m₁ := a) (m₂ := 1) (fun w => by
      rw [hall w, one_smul]))
  have hwΓ : w ∉ onanL_Gamma α A α β := fun hw => hwne (hw a haK)
  have hlines := mul_add_one_le_natCard_of_lines (onanL_Gamma α A) hmem hsymm hline hcard
    hαβ hwΓ
  have hmle : m ≤ s := by
    have h := onanL_m_le_s hPA hPα hAself hαΓ hβne (horb β hβne)
    simpa only [s] using h
  have hmul : m * m ≤ (s + 1) * s := by
    calc m * m ≤ s * s := Nat.mul_le_mul hmle hmle
      _ ≤ s * (s + 1) := Nat.mul_le_mul_left s (Nat.le_succ s)
      _ = (s + 1) * s := by ring
  have hlt' : Nat.card Ω < m * m + 1 := by simpa [pow_two] using hlt
  omega

end CFSG.GroupTheory.ONan
