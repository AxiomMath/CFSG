module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Six

open Equiv

@[expose] def idxT (RT : List (List ℕ)) (a : List ℕ) : ℕ :=
  RT.findIdx (fun r => decide (r = a ∨ mulT r a = mulT a r))

@[expose] def actT (RT : List (List ℕ)) (s : List ℕ) : List ℕ :=
  RT.map (fun r => idxT RT (cjT s r))

@[expose] def idx (R : List (Perm (Fin 6))) (d : Perm (Fin 6)) : ℕ := idxT (R.map tab) (tab d)

@[expose] def rep (R : List (Perm (Fin 6))) (i : ℕ) : Perm (Fin 6) := R.getD i 1

@[expose] def IsoOk (C R : List (Perm (Fin 6))) : Prop :=
  R.length = 5 ∧ (∀ r ∈ R.map tab, r ∈ C.map tab) ∧
  (∀ a ∈ C.map tab, idxT (R.map tab) a < 5) ∧
  (∀ a ∈ C.map tab, ∀ b ∈ C.map tab,
    (idxT (R.map tab) a = idxT (R.map tab) b ↔ (a = b ∨ mulT a b = mulT b a))) ∧
  (∀ i < 5, idxT (R.map tab) ((R.map tab).getD i []) = i) ∧
  (∀ s ∈ allT 6, (∀ r ∈ R.map tab,
      cjT s r ∈ C.map tab ∧ idxT (R.map tab) (cjT s r) = idxT (R.map tab) r) → s = oneT 6) ∧
  (∀ g ∈ allT 5, suppT 5 g = 3 → ∃ t₁ ∈ (C.map tab).map (actT (R.map tab)),
    ∃ t₂ ∈ (C.map tab).map (actT (R.map tab)), g = mulT t₁ t₂)

theorem rep_mem {R : List (Perm (Fin 6))} {i : ℕ} (hi : i < R.length) : rep R i ∈ R := by
  have : rep R i = R[i] := by simp [rep, hi]
  rw [this]
  exact List.getElem_mem hi

theorem exists_rep_of_mem {R : List (Perm (Fin 6))} {r : Perm (Fin 6)} (hr : r ∈ R) :
    ∃ i, i < R.length ∧ rep R i = r := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  exact ⟨i, hi, by simp [rep, hi]⟩

theorem tab_rep {R : List (Perm (Fin 6))} {i : ℕ} (hi : i < R.length) :
    tab (rep R i) = (R.map tab)[i]'(by simpa using hi) := by
  simp [rep, hi]

section IsoOk

variable {C R : List (Perm (Fin 6))}

theorem IsoOk.idx_lt (hok : IsoOk C R) {a : Perm (Fin 6)} (ha : a ∈ C) : idx R a < 5 :=
  hok.2.2.1 (tab a) (List.mem_map_of_mem ha)

theorem IsoOk.idx_eq_iff (hok : IsoOk C R) {a b : Perm (Fin 6)} (ha : a ∈ C) (hb : b ∈ C) :
    idx R a = idx R b ↔ a = b ∨ a * b = b * a := by
  have := hok.2.2.2.1 (tab a) (List.mem_map_of_mem ha) (tab b) (List.mem_map_of_mem hb)
  rw [tab_injective.eq_iff, ← tab_mul, ← tab_mul, tab_injective.eq_iff] at this
  exact this

theorem IsoOk.rep_mem_C (hok : IsoOk C R) {i : ℕ} (hi : i < 5) : rep R i ∈ C := by
  have hi' : i < R.length := by rw [hok.1]; exact hi
  have := hok.2.1 (tab (rep R i)) (List.mem_map_of_mem (rep_mem hi'))
  exact mem_map_tab_iff.1 this

theorem IsoOk.idx_rep (hok : IsoOk C R) {i : ℕ} (hi : i < 5) : idx R (rep R i) = i := by
  have hi' : i < R.length := by rw [hok.1]; exact hi
  have h := hok.2.2.2.2.1 i hi
  have e : tab (rep R i) = (R.map tab).getD i [] := by
    rw [tab_rep hi']
    simp [hi']
  unfold idx
  rw [e]
  exact h

theorem IsoOk.idx_conj_mul (hok : IsoOk C R) {σ τ : Perm (Fin 6)}
    (hσ : ∀ c ∈ C, σ * c * σ⁻¹ ∈ C) (hτ : ∀ c ∈ C, τ * c * τ⁻¹ ∈ C) {i : ℕ} (hi : i < 5) :
    idx R (σ * τ * rep R i * (σ * τ)⁻¹) =
      idx R (σ * rep R (idx R (τ * rep R i * τ⁻¹)) * σ⁻¹) := by
  have hr : rep R i ∈ C := hok.rep_mem_C hi
  have hcC : τ * rep R i * τ⁻¹ ∈ C := hτ _ hr
  set c := τ * rep R i * τ⁻¹ with hc
  have hj : idx R c < 5 := hok.idx_lt hcC
  have hrj : rep R (idx R c) ∈ C := hok.rep_mem_C hj
  have hcomm := (hok.idx_eq_iff hcC hrj).1 (hok.idx_rep hj).symm
  have hx : σ * c * σ⁻¹ ∈ C := hσ _ hcC
  have hy : σ * rep R (idx R c) * σ⁻¹ ∈ C := hσ _ hrj
  have key : idx R (σ * c * σ⁻¹) = idx R (σ * rep R (idx R c) * σ⁻¹) := by
    rw [hok.idx_eq_iff hx hy]
    rcases hcomm with h | h
    · exact Or.inl (congrArg (fun t => σ * t * σ⁻¹) h)
    · right
      calc σ * c * σ⁻¹ * (σ * rep R (idx R c) * σ⁻¹)
          = σ * (c * rep R (idx R c)) * σ⁻¹ := by group
        _ = σ * (rep R (idx R c) * c) * σ⁻¹ := by rw [h]
        _ = σ * rep R (idx R c) * σ⁻¹ * (σ * c * σ⁻¹) := by group
  have e : σ * τ * rep R i * (σ * τ)⁻¹ = σ * c * σ⁻¹ := by rw [hc]; group
  rw [e]
  exact key

end IsoOk

theorem range_eq_or_top {H : Subgroup (Perm (Fin 5))} (h : alternatingGroup (Fin 5) ≤ H) :
    H = alternatingGroup (Fin 5) ∨ H = ⊤ := by
  by_cases hle : H ≤ alternatingGroup (Fin 5)
  · exact Or.inl (le_antisymm hle h)
  · right
    obtain ⟨x, hxH, hxA⟩ := SetLike.not_le_iff_exists.1 hle
    rw [Equiv.Perm.mem_alternatingGroup] at hxA
    have hx : Equiv.Perm.sign x = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | h1
      · exact absurd h1 hxA
      · exact h1
    refine eq_top_iff.2 fun g _ => ?_
    by_cases hg : Equiv.Perm.sign g = 1
    · exact h (Equiv.Perm.mem_alternatingGroup.2 hg)
    · have hg' : Equiv.Perm.sign g = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h1 | h1
        · exact absurd h1 hg
        · exact h1
      have : g * x⁻¹ ∈ H := h (Equiv.Perm.mem_alternatingGroup.2 (by simp [hg', hx]))
      simpa using H.mul_mem this hxH

theorem iso_of_blocks {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6))
    (hι : Function.Injective ι) {C R : List (Perm (Fin 6))} (hok : IsoOk C R)
    (hnorm : ∀ q : Q, ∀ c ∈ C, ι q * c * (ι q)⁻¹ ∈ C) (hgen : ∀ c ∈ C, ∃ q : Q, ι q = c) :
    Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Q ≃* Perm (Fin 5)) := by
  have hlen : R.length = 5 := hok.1
  let act : Q → Fin 5 → Fin 5 := fun q i =>
    ⟨idx R (ι q * rep R i * (ι q)⁻¹), hok.idx_lt (hnorm q _ (hok.rep_mem_C i.2))⟩
  have act_mul : ∀ q₁ q₂ i, act (q₁ * q₂) i = act q₁ (act q₂ i) := by
    intro q₁ q₂ i
    refine Fin.ext ?_
    simp only [act, map_mul]
    exact hok.idx_conj_mul (hnorm q₁) (hnorm q₂) i.2
  have act_one : ∀ i, act 1 i = i := by
    intro i
    refine Fin.ext ?_
    simp only [act, map_one, one_mul, inv_one, mul_one]
    exact hok.idx_rep i.2
  let f : Q → Perm (Fin 5) := fun q =>
    { toFun := act q
      invFun := act q⁻¹
      left_inv := fun i => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun i => by rw [← act_mul, mul_inv_cancel, act_one] }
  let ψ : Q →* Perm (Fin 5) := MonoidHom.mk' f (fun q₁ q₂ => Equiv.ext fun i => act_mul q₁ q₂ i)
  have hψ : ∀ q i, ψ q i = act q i := fun q i => rfl
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 fun q hq => ?_
    have hfix : ∀ i : Fin 5, act q i = i := fun i => by rw [← hψ, hq]; rfl
    have h1 := hok.2.2.2.2.2.1 (tab (ι q)) (mem_allT _) ?_
    · exact hι (tab_injective (h1.trans tab_one.symm) |>.trans (map_one ι).symm)
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      obtain ⟨i, hi, rfl⟩ := exists_rep_of_mem hr'
      have hi5 : i < 5 := by rw [← hlen]; exact hi
      have hrC : rep R i ∈ C := hok.rep_mem_C hi5
      rw [← tab_conj]
      refine ⟨List.mem_map_of_mem (hnorm q _ hrC), ?_⟩
      have h2 : idx R (ι q * rep R i * (ι q)⁻¹) = i := congrArg Fin.val (hfix ⟨i, hi5⟩)
      exact h2.trans (hok.idx_rep hi5).symm
  have htab : ∀ q, tab (ψ q) = actT (R.map tab) (tab (ι q)) := by
    intro q
    refine List.ext_getElem (by simp [tab, actT, hlen]) fun k h1 h2 => ?_
    have hk : k < 5 := by simpa [tab] using h1
    have hk' : k < R.length := by rw [hlen]; exact hk
    have e1 : (tab (ψ q))[k]'h1 = idx R (ι q * rep R k * (ι q)⁻¹) := by
      simp only [tab, List.getElem_ofFn]
      rfl
    have e2 : (actT (R.map tab) (tab (ι q)))[k]'h2 =
        idxT (R.map tab) (cjT (tab (ι q)) ((R.map tab)[k]'(by simpa using hk'))) := by
      simp [actT]
    rw [e1, e2, ← tab_rep hk', ← tab_conj]
    rfl
  have hrange : alternatingGroup (Fin 5) ≤ ψ.range := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    have hs : suppT 5 (tab g) = 3 := by
      rw [suppT_tab]
      exact card_support_eq_three_iff.2 hg
    obtain ⟨t₁, ht₁, t₂, ht₂, hgt⟩ := hok.2.2.2.2.2.2 (tab g) (mem_allT g) hs
    obtain ⟨a₁, ha₁, rfl⟩ := List.mem_map.1 ht₁
    obtain ⟨a₂, ha₂, rfl⟩ := List.mem_map.1 ht₂
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 ha₁
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.1 ha₂
    obtain ⟨q₁, rfl⟩ := hgen c₁ hc₁
    obtain ⟨q₂, rfl⟩ := hgen c₂ hc₂
    refine ⟨q₁ * q₂, ?_⟩
    apply tab_injective
    rw [map_mul, tab_mul, htab, htab, hgt]
  rcases range_eq_or_top hrange with h | h
  · exact Or.inl ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr h)⟩
  · exact Or.inr ⟨(MonoidHom.ofInjective hinj).trans
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.Six
