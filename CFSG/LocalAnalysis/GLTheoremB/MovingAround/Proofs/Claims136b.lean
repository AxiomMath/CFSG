module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims136
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims126
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltWeakBalance
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input183
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

section Perm

open Equiv Equiv.Perm
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126 (altOn mem_altOn altOn_le_sup_erase
  altOn_insert_le)

variable {α : Type} [Fintype α] [DecidableEq α]

theorem altOn_le_gLBConj {Z T' : Finset α} {g : Perm α} (hg : ∀ z ∈ T', g z ∈ Z) :
    altOn T' ≤ GLBConj g (altOn Z) := by
  intro π hπ
  obtain ⟨hA, hs⟩ := mem_altOn.1 hπ
  rw [mem_gLBConj]
  refine mem_altOn.2 ⟨?_, ?_⟩
  · rw [Perm.mem_alternatingGroup] at hA ⊢
    rw [Perm.sign_mul, Perm.sign_mul, hA, mul_one, ← Perm.sign_mul, mul_inv_cancel, map_one]
  · rw [Perm.support_conj]
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact hg t (hs ht)

theorem cyc_apply {y f w : α} (hyf : y ≠ f) (hyw : y ≠ w) (hfw : f ≠ w) :
    (swap y w * swap y f) y = f ∧ (swap y w * swap y f) f = w ∧ (swap y w * swap y f) w = y ∧
      ∀ z, z ≠ y → z ≠ f → z ≠ w → (swap y w * swap y f) z = z := by
  refine ⟨?_, ?_, ?_, fun z h1 h2 h3 => ?_⟩
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hyf.symm hfw]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hyw.symm hfw.symm, swap_apply_right]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]

theorem cyc_mem_altOn {Y : Finset α} {y f w : α} (hyf : y ≠ f) (hyw : y ≠ w) (hfw : f ≠ w)
    (hy : y ∈ Y) (hf : f ∈ Y) (hw : w ∈ Y) : swap y w * swap y f ∈ altOn Y := by
  refine mem_altOn.2 ⟨(Perm.isThreeCycle_swap_mul_swap_same hyw hyf hfw.symm).mem_alternatingGroup, ?_⟩
  intro z hz
  have h1 := Perm.support_mul_le (swap y w) (swap y f) hz
  rw [Perm.support_swap hyw, Perm.support_swap hyf] at h1
  simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at h1
  rcases h1 with (h | h) | (h | h) <;> (subst h; assumption)

theorem altOn_insert_le_of_mem {Z : Finset α} (h4 : 4 ≤ Z.card) {y f w : α} (hyZ : y ∉ Z)
    (hfZ : f ∈ Z) (hwZ : w ∈ Z) (hfw : f ≠ w) :
    altOn (insert y Z) ≤ altOn Z ⊔ GLBConj (swap y w * swap y f) (altOn Z) := by
  have hyf : y ≠ f := fun h => hyZ (h ▸ hfZ)
  have hyw : y ≠ w := fun h => hyZ (h ▸ hwZ)
  obtain ⟨h1, h2, -, h4'⟩ := cyc_apply hyf hyw hfw
  have h5 : 5 ≤ (insert y Z).card := by
    rw [Finset.card_insert_of_notMem hyZ]
    omega
  refine (altOn_le_sup_erase h5 hyw).trans (sup_le ?_ ?_)
  · rw [Finset.erase_insert hyZ]
    exact le_sup_left
  · refine (altOn_le_gLBConj fun z hz => ?_).trans le_sup_right
    rw [Finset.mem_erase, Finset.mem_insert] at hz
    obtain ⟨hzw, hz⟩ := hz
    rcases hz with rfl | hz
    · rw [h1]; exact hfZ
    · by_cases hzf : z = f
      · subst hzf; rw [h2]; exact hwZ
      · rw [h4' z (fun h => hyZ (h ▸ hz)) hzf hzw]; exact hz

theorem alternatingGroup_le_sup {F : Finset α} (h4 : 4 ≤ F.card) {f : α} (hf : f ∈ F)
    (h2 : 2 ≤ Fᶜ.card) : alternatingGroup α ≤ altOn F ⊔ altOn (insert f Fᶜ) := by
  set H := altOn F ⊔ altOn (insert f Fᶜ) with hH
  have key : ∀ S : Finset α, S ⊆ Fᶜ → altOn (F ∪ S) ≤ H := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; rw [Finset.union_empty]; exact le_sup_left
    | @insert y S hyS ih =>
      intro hsub
      have hyc : y ∈ Fᶜ := hsub (Finset.mem_insert_self y S)
      have hSc : S ⊆ Fᶜ := fun z hz => hsub (Finset.mem_insert_of_mem hz)
      have hZH := ih hSc
      have hyF : y ∉ F := Finset.mem_compl.1 hyc
      have hyZ : y ∉ F ∪ S := by
        rw [Finset.mem_union]
        rintro (h | h)
        · exact hyF h
        · exact hyS h
      have hZ4 : 4 ≤ (F ∪ S).card := h4.trans (Finset.card_le_card Finset.subset_union_left)
      have heq : F ∪ insert y S = insert y (F ∪ S) := by
        ext z; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [heq]
      have hyf : y ≠ f := fun h => hyF (h ▸ hf)
      obtain ⟨w, hwc, hwy, hwcase⟩ : ∃ w ∈ Fᶜ, w ≠ y ∧ (w ∈ S ∨ S = ∅) := by
        by_cases hS : S = ∅
        · obtain ⟨w, hw, hwy⟩ := Finset.exists_mem_ne (by omega : 1 < Fᶜ.card) y
          exact ⟨w, hw, hwy, Or.inr hS⟩
        · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hS
          exact ⟨w, hSc hw, fun h => hyS (h ▸ hw), Or.inl hw⟩
      have hwF : w ∉ F := Finset.mem_compl.1 hwc
      have hfw : f ≠ w := fun h => hwF (h ▸ hf)
      have hgH : swap y w * swap y f ∈ H :=
        Subgroup.mem_sup_right (cyc_mem_altOn hyf hwy.symm hfw (Finset.mem_insert_of_mem hyc)
          (Finset.mem_insert_self f _) (Finset.mem_insert_of_mem hwc))
      have hconj : GLBConj (swap y w * swap y f) (altOn (F ∪ S)) ≤ H :=
        Lemma136.l136_gLBConj_le hZH hgH
      rcases hwcase with hwS | hS
      · exact (altOn_insert_le_of_mem hZ4 hyZ (Finset.mem_union_left _ hf)
          (Finset.mem_union_right _ hwS) hfw).trans (sup_le hZH hconj)
      · subst hS
        rw [Finset.union_empty] at hZH hconj hyZ hZ4 ⊢
        obtain ⟨h1, -, -, h4'⟩ := cyc_apply hyf hwy.symm hfw
        exact (altOn_insert_le hZ4 hf hyF h1 (fun z hz hzf =>
          h4' z (fun h => hyF (h ▸ hz)) hzf (fun h => hwF (h ▸ hz)))).trans (sup_le hZH hconj)
  have h := key Fᶜ (subset_refl _)
  rw [Finset.union_compl] at h
  refine le_trans (fun g hg => mem_altOn.2 ⟨hg, Finset.subset_univ _⟩) h

theorem exists_mem_alternatingGroup_orderOf_nine (h9 : 9 ≤ Fintype.card α) :
    ∃ g ∈ alternatingGroup α, orderOf g = 9 := by
  obtain ⟨g, hg⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := α) (m := {9})).2
    ⟨by simpa using h9, by simp⟩
  refine ⟨g, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, hg]
    decide
  · rw [← Perm.lcm_cycleType, hg]
    simp

theorem exists_fixed_of_isPGroup {P : Subgroup (Perm α)} (hP : IsPGroup 3 ↥P) {F : Finset α}
    (hPF : ∀ g ∈ P, g.support ⊆ F) (h3 : ¬ 3 ∣ F.card) : ∃ f ∈ F, ∀ g ∈ P, g f = f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints ↥P α = ((Fᶜ : Finset α) : Set α) := by
    ext z
    rw [MulAction.mem_fixedPoints, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
    constructor
    · intro hz hzF
      obtain ⟨g, hg, hgz⟩ := hcon z hzF
      exact hgz (hz ⟨g, hg⟩)
    · intro hzF g
      show (g : Perm α) z = z
      by_contra hgz
      exact hzF (hPF g g.2 (Perm.mem_support.2 hgz))
  have hmod := hP.card_modEq_card_fixedPoints α
  rw [hfix, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_eq_fintype_card,
    ← Finset.card_compl_add_card F] at hmod
  have h0 : Fᶜ.card + F.card ≡ Fᶜ.card + 0 [MOD 3] := by rw [add_zero]; exact hmod
  exact h3 (Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' _ h0))

@[expose] def orbSubH (H : Subgroup (Perm α)) : Subgroup (Perm α) where
  carrier := {π | (∀ h ∈ H, π * h = h * π) ∧ ∀ v, ∃ h ∈ H, π v = h v}
  mul_mem' := by
    rintro π₁ π₂ ⟨hc₁, hv₁⟩ ⟨hc₂, hv₂⟩
    refine ⟨fun h hh => by rw [mul_assoc, hc₂ h hh, ← mul_assoc, hc₁ h hh, mul_assoc], fun v => ?_⟩
    obtain ⟨h₂, hh₂, e₂⟩ := hv₂ v
    obtain ⟨h₁, hh₁, e₁⟩ := hv₁ v
    refine ⟨h₂ * h₁, H.mul_mem hh₂ hh₁, ?_⟩
    rw [Perm.mul_apply, e₂, ← Perm.mul_apply, hc₁ h₂ hh₂, Perm.mul_apply, e₁, Perm.mul_apply]
  one_mem' := ⟨fun h _ => by rw [one_mul, mul_one], fun v => ⟨1, H.one_mem, rfl⟩⟩
  inv_mem' := by
    rintro π ⟨hc, hv⟩
    refine ⟨fun h hh => ?_, fun v => ?_⟩
    · calc π⁻¹ * h = π⁻¹ * (h * π) * π⁻¹ := by group
        _ = π⁻¹ * (π * h) * π⁻¹ := by rw [hc h hh]
        _ = h * π⁻¹ := by group
    · obtain ⟨h, hh, e⟩ := hv (π⁻¹ v)
      refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
      have h1 : v = h (π⁻¹ v) := by rw [← e]; simp
      calc π⁻¹ v = h⁻¹ (h (π⁻¹ v)) := by simp
        _ = h⁻¹ v := by rw [← h1]

theorem mem_orbSubH {H : Subgroup (Perm α)} {π : Perm α} :
    π ∈ orbSubH H ↔ (∀ h ∈ H, π * h = h * π) ∧ ∀ v, ∃ h ∈ H, π v = h v := Iff.rfl

theorem orbSubH_props {H : Subgroup (Perm α)} (hHab : ∀ g ∈ H, ∀ h ∈ H, g * h = h * g)
    (hH3 : ∀ h ∈ H, h ^ 3 = 1) :
    (∀ π ∈ orbSubH H, π ^ 3 = 1) ∧ ∀ π₁ ∈ orbSubH H, ∀ π₂ ∈ orbSubH H, π₁ * π₂ = π₂ * π₁ := by
  refine ⟨fun π hπ => ?_, fun π₁ hπ₁ π₂ hπ₂ => ?_⟩
  · ext v
    obtain ⟨h, hh, e⟩ := hπ.2 v
    have key : ∀ k : ℕ, (π ^ k) v = (h ^ k) v := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        have hc : π * h ^ k = h ^ k * π := hπ.1 _ (H.pow_mem hh k)
        rw [pow_succ', Perm.mul_apply, ih, ← Perm.mul_apply, hc, Perm.mul_apply, e,
          ← Perm.mul_apply, ← pow_succ]
    rw [key 3, hH3 h hh]
  · ext v
    obtain ⟨h₁, hh₁, e₁⟩ := hπ₁.2 v
    obtain ⟨h₂, hh₂, e₂⟩ := hπ₂.2 v
    rw [Perm.mul_apply, Perm.mul_apply, e₂, e₁, ← Perm.mul_apply, ← Perm.mul_apply,
      hπ₁.1 h₂ hh₂, hπ₂.1 h₁ hh₁, Perm.mul_apply, Perm.mul_apply, e₁, e₂, ← Perm.mul_apply,
      ← Perm.mul_apply, hHab h₁ hh₁ h₂ hh₂]

theorem conj_mem_orbSubH {H : Subgroup (Perm α)} {β : Perm α} (hβ : ∀ h ∈ H, β * h = h * β)
    {π : Perm α} (hπ : π ∈ orbSubH H) : β * π * β⁻¹ ∈ orbSubH H := by
  refine ⟨fun h hh => ?_, fun v => ?_⟩
  · have h1 : β⁻¹ * h = h * β⁻¹ := by
      calc β⁻¹ * h = β⁻¹ * (h * β) * β⁻¹ := by group
        _ = β⁻¹ * (β * h) * β⁻¹ := by rw [hβ h hh]
        _ = h * β⁻¹ := by group
    calc β * π * β⁻¹ * h = β * π * (h * β⁻¹) := by rw [mul_assoc, h1]
      _ = β * (π * h) * β⁻¹ := by group
      _ = β * (h * π) * β⁻¹ := by rw [hπ.1 h hh]
      _ = (β * h) * π * β⁻¹ := by group
      _ = h * β * π * β⁻¹ := by rw [hβ h hh]
      _ = h * (β * π * β⁻¹) := by group
  · obtain ⟨h, hh, e⟩ := hπ.2 (β⁻¹ v)
    refine ⟨h, hh, ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, e, ← Perm.mul_apply, hβ h hh, Perm.mul_apply]
    simp

theorem exists_mem_orbSubH_comm_ne {H : Subgroup (Perm α)} (hHab : ∀ g ∈ H, ∀ h ∈ H, g * h = h * g)
    {ω : α} {c β : Perm α} (hc : c ∈ H) (hβ3 : β ^ 3 = 1) (hcω : c ω ≠ ω)
    (hβω : ∀ h ∈ H, h ω ≠ β ω) (hβω' : ∀ h ∈ H, h ω ≠ β⁻¹ ω) :
    ∃ x ∈ orbSubH H, ⁅⁅x, β⁆, β⁆ ≠ 1 := by
  classical
  set O : Finset α := Finset.univ.filter (fun v => ∃ h ∈ H, h ω = v) with hO
  have hmemO : ∀ v, v ∈ O ↔ ∃ h ∈ H, h ω = v := by intro v; simp [hO]
  have hHO : ∀ h ∈ H, ∀ v, h v ∈ O ↔ v ∈ O := by
    intro h hh v
    rw [hmemO, hmemO]
    constructor
    · rintro ⟨g, hg, e⟩
      refine ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) hg, ?_⟩
      rw [Perm.mul_apply, e]
      simp
    · rintro ⟨g, hg, e⟩
      exact ⟨h * g, H.mul_mem hh hg, by rw [Perm.mul_apply, e]⟩
  set x : Perm α := Perm.ofSubtype (c.subtypePerm (hHO c hc)) with hx
  have hx1 : ∀ v ∈ O, x v = c v := fun v hv => by
    rw [hx, Perm.ofSubtype_apply_of_mem _ hv, Perm.subtypePerm_apply]
  have hx2 : ∀ v ∉ O, x v = v := fun v hv => by
    rw [hx]
    exact Perm.ofSubtype_apply_of_not_mem _ hv
  have hxi : ∀ v ∉ O, x⁻¹ v = v := fun v hv => by rw [Perm.inv_eq_iff_eq, hx2 v hv]
  have hωO : ω ∈ O := (hmemO ω).2 ⟨1, H.one_mem, rfl⟩
  have hβωO : β ω ∉ O := fun h => by obtain ⟨g, hg, e⟩ := (hmemO _).1 h; exact hβω g hg e
  have hβωO' : β⁻¹ ω ∉ O := fun h => by obtain ⟨g, hg, e⟩ := (hmemO _).1 h; exact hβω' g hg e
  have hinv : β⁻¹ = β * β := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hβ3)
  have h3 : ∀ w, β (β (β w)) = w := fun w => by
    have := congrArg (fun π : Perm α => π w) hβ3
    simpa [pow_three, Perm.mul_apply] using this
  have hββ : ∀ v, β⁻¹ (β⁻¹ v) = β v := by
    intro v
    rw [hinv]
    simp only [Perm.mul_apply]
    rw [h3]
  have hββ' : ∀ v, β (β v) = β⁻¹ v := by
    intro v
    rw [hinv]
    rfl
  have hbi : ∀ v, β (β⁻¹ v) = v := fun v => by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  refine ⟨x, ⟨fun h hh => ?_, fun v => ?_⟩, ?_⟩
  · ext v
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hv : v ∈ O
    · rw [hx1 _ ((hHO h hh v).2 hv), hx1 v hv, ← Perm.mul_apply, ← Perm.mul_apply, hHab c hc h hh]
    · rw [hx2 _ (fun h' => hv ((hHO h hh v).1 h')), hx2 v hv]
  · by_cases hv : v ∈ O
    · exact ⟨c, hc, hx1 v hv⟩
    · exact ⟨1, H.one_mem, hx2 v hv⟩
  · intro h1
    have h2 := congrArg (fun π : Perm α => π ω) h1
    simp only [Perm.one_apply] at h2
    set y : Perm α := ⁅x, β⁆ with hy
    have hyω : y ω = c ω := by
      rw [hy, commutatorElement_def]
      simp only [Perm.mul_apply]
      rw [hxi _ hβωO', hbi, hx1 ω hωO]
    have hyfix : y (β⁻¹ ω) = β⁻¹ ω := by
      rw [hy, commutatorElement_def]
      simp only [Perm.mul_apply]
      rw [hββ, hxi _ hβωO, hββ', hx2 _ hβωO']
    have hyinv : y⁻¹ (β⁻¹ ω) = β⁻¹ ω := by rw [Perm.inv_eq_iff_eq, hyfix]
    have hz : ⁅y, β⁆ ω = c ω := by
      rw [commutatorElement_def]
      simp only [Perm.mul_apply]
      rw [hyinv, hbi, hyω]
    exact hcω (hz.symm.trans h2)

end Perm

section Family

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_le_of_family {𝓛 : Set (Subgroup Y)} {B : Subgroup Y} (hB : IsPGroup 3 ↥B)
    (hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (hcen : ∀ X ∈ 𝓛, ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x = 1)
    (hcard : ∀ X ∈ 𝓛, ∃ c : ℕ, Nat.card X = 9 * c ∧ ¬ 3 ∣ c)
    (hBX : ∀ X ∈ 𝓛, 9 ≤ Nat.card ↥(B ⊓ X))
    {P : Subgroup Y} (hP : IsPGroup 3 ↥P) (hPL : P ≤ sSup 𝓛) :
    ∃ g ∈ sSup 𝓛, GLBConj g P ≤ B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ↥𝓛 := Fintype.ofFinite _
  set H : ↥𝓛 → Subgroup Y := fun X => (X : Subgroup Y) with hHdef
  set H' : ↥𝓛 → Subgroup Y := fun X => B ⊓ (X : Subgroup Y) with hH'def
  have hcommP : Pairwise fun i j : ↥𝓛 => ∀ x y : Y, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j hij x y hx hy => hcomm i i.2 j j.2 (fun h => hij (Subtype.ext h)) x hx y hy
  have hcommP' : Pairwise fun i j : ↥𝓛 => ∀ x y : Y, x ∈ H' i → y ∈ H' j → Commute x y :=
    fun i j hij x y hx hy => hcommP hij x y hx.2 hy.2
  have hind : iSupIndep H := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxi, hxs⟩
    have hle : (⨆ (j) (_ : j ≠ i), H j) ≤ Subgroup.centralizer (H i : Set Y) :=
      iSup₂_le fun j hj y hy => Subgroup.mem_centralizer_iff.2 fun z hz =>
        (hcommP hj y z hy hz).symm.eq
    have hx1 := hcen i i.2 x hxi fun y hy => ((Subgroup.mem_centralizer_iff.1 (hle hxs)) y hy).symm
    exact Subgroup.mem_bot.2 hx1
  have hind' : iSupIndep H' := hind.mono fun i => inf_le_right
  set φ := Subgroup.noncommPiCoprod hcommP with hφ
  set φ' := Subgroup.noncommPiCoprod hcommP' with hφ'
  have hφi : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hφ'i : Function.Injective φ' := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind'
  have hsSup : sSup 𝓛 = ⨆ i : ↥𝓛, H i := sSup_eq_iSup' 𝓛
  have hrange : φ.range = sSup 𝓛 := by rw [hsSup]; exact Subgroup.noncommPiCoprod_range
  have hrange' : φ'.range = ⨆ i : ↥𝓛, H' i := Subgroup.noncommPiCoprod_range
  have hcardS : Nat.card ↥(sSup 𝓛) = ∏ i : ↥𝓛, Nat.card ↥(H i) := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv, Nat.card_pi]
  have hcardR : ∏ i : ↥𝓛, Nat.card ↥(H' i) = Nat.card ↥φ'.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ'i).toEquiv, Nat.card_pi]
  choose c hc hc3 using fun i : ↥𝓛 => hcard i i.2
  have hprod : ∏ i : ↥𝓛, Nat.card ↥(H i) = 9 ^ Fintype.card ↥𝓛 * ∏ i : ↥𝓛, c i := by
    rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hcop : Nat.Coprime 3 (∏ i : ↥𝓛, c i) :=
    Nat.Coprime.prod_right fun i _ => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (hc3 i)
  have hRge : 9 ^ Fintype.card ↥𝓛 ≤ Nat.card ↥φ'.range := by
    rw [← hcardR, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun i _ => hBX i i.2
  have hRB : φ'.range ≤ B := by
    rw [hrange']
    exact iSup_le fun i => inf_le_left
  have hRS : φ'.range ≤ sSup 𝓛 := by
    rw [hrange', hsSup]
    exact iSup_mono fun i => inf_le_right
  set S : Subgroup Y := sSup 𝓛 with hS
  have hRp : IsPGroup 3 ↥(φ'.range.subgroupOf S) :=
    (hB.to_le hRB).of_equiv (Subgroup.subgroupOfEquivOfLe hRS).symm
  obtain ⟨T, hRT⟩ := hRp.exists_le_sylow
  have hTcard : Nat.card ↥(T : Subgroup ↥S) ≤ 9 ^ Fintype.card ↥𝓛 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 T.isPGroup'
    have hdvd : Nat.card ↥(T : Subgroup ↥S) ∣ 9 ^ Fintype.card ↥𝓛 * ∏ i : ↥𝓛, c i := by
      rw [← hprod, ← hcardS]
      exact Subgroup.card_subgroup_dvd_card _
    rw [ha] at hdvd ⊢
    exact Nat.le_of_dvd (by positivity)
      (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left a hcop) hdvd)
  have hcardR' : Nat.card ↥(φ'.range.subgroupOf S) = Nat.card ↥φ'.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv
  have hTeq : (T : Subgroup ↥S) = φ'.range.subgroupOf S :=
    (Subgroup.eq_of_le_of_card_ge hRT (by rw [hcardR']; omega)).symm
  have hPp : IsPGroup 3 ↥(P.subgroupOf S) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  obtain ⟨T₂, hPT₂⟩ := hPp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥S T T₂
  refine ⟨(g : Y), g.2, fun z hz => ?_⟩
  rw [mem_gLBConj] at hz
  have hzS : (g : Y) * z * (g : Y)⁻¹ ∈ S := hPL hz
  have h1 : (⟨_, hzS⟩ : ↥S) ∈ (T₂ : Subgroup ↥S) := hPT₂ (Subgroup.mem_subgroupOf.2 hz)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (g⁻¹ * ⟨_, hzS⟩ * g : ↥S) ∈ (T : Subgroup ↥S) := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  rw [hTeq, Subgroup.mem_subgroupOf] at h2
  have h3 : ((g⁻¹ * ⟨_, hzS⟩ * g : ↥S) : Y) = z := by simp [mul_assoc]
  rw [h3] at h2
  exact hRB h2

end Family

section AnBranch

variable {G : Type} [Group G] [Finite G]

open Equiv
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem three_dvd_card_support {α : Type} [Fintype α] [DecidableEq α] {σ : Perm α}
    (hσ : σ ^ 3 = 1) : 3 ∣ σ.support.card := by
  have hall : ∀ c ∈ σ.cycleType, c = 3 := by
    intro c hc
    have h1 : c ∣ orderOf σ := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hc
    have h2 : c ∣ 3 := h1.trans (orderOf_dvd_of_pow_eq_one hσ)
    have h3' : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
    have : c ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases c
    · exact absurd h2 (by norm_num)
    · rfl
  rw [← Equiv.Perm.sum_cycleType, Multiset.eq_replicate.2 ⟨rfl, hall⟩, Multiset.sum_replicate,
    smul_eq_mul]
  exact dvd_mul_left 3 _

theorem an_branch_false {d b : G} (hbC : b ∈ Cg d) (hb3 : b ^ 3 = 1)
    {L' J V W : Subgroup G} (hL' : GLAPComponent 3 (Cg d) L')
    (hbN : b ∈ Subgroup.normalizer (L' : Set G))
    (hJ : GLAPComponent 3 (L' ⊓ Cg b) J) (eJ : barOf 3 J ≃* alternatingGroup (Fin 7))
    {n : ℕ} (hn : 10 ≤ n) (hn3 : n % 3 = 1)
    (e : ↥(barX 3 (Cg d) L') ≃* alternatingGroup (Fin n))
    (hnc : ∃ q ∈ barX 3 (Cg d) L', QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b, hbC⟩ * q ≠
      q * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b, hbC⟩)
    (hJV : J ≤ V) (hVW : IsSubnormal V W)
    (hexp : ∀ u ∈ V, u ^ 9 = 1 → u ^ 3 = 1)
    (hnorm : ∀ Q : Subgroup G, Q ≤ V → IsElemAbelian 3 Q → Nat.card Q = 9 →
      Subgroup.normalizer (Q : Set G) ≤ W) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set C : Subgroup G := Cg d with hCdef
  set Kb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C L' with hKb
  set z : ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩ with hz
  have hLC : L' ≤ C := hL'.1
  have hJL : J ≤ L' := hJ.1.trans inf_le_left
  have hJC : J ≤ C := hJL.trans hLC
  have hzN : z ∈ Subgroup.normalizer ((Kb : Subgroup _) : Set _) := by
    have h1 := l119_barX_gLBConj (p := 3) (C := C) (H := L') hbC hLC
    rw [mem_normalizer_iff_gLBConj_eq.1 hbN] at h1
    exact mem_normalizer_iff_gLBConj_eq.2 h1.symm
  let x : MulAut ↥Kb := Kb.normalizerMonoidHom ⟨z, hzN⟩
  have hxk : ∀ k : ↥Kb, ((x k : ↥Kb) : _) = z * (k : _) * z⁻¹ := fun k =>
    Kb.normalizerMonoidHom_apply_apply_coe ⟨z, hzN⟩ k
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← map_pow]
    have : (⟨b, hbC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hx3 : x ^ 3 = 1 := by
    have h13 : (⟨z, hzN⟩ : ↥(Subgroup.normalizer ((Kb : Subgroup _) : Set _))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    show Kb.normalizerMonoidHom ⟨z, hzN⟩ ^ 3 = 1
    rw [← map_pow, h13, map_one]
  have hx1 : x ≠ 1 := by
    intro hx1
    obtain ⟨q, hq, hqne⟩ := hnc
    apply hqne
    have := congrArg Subtype.val (DFunLike.congr_fun hx1 ⟨q, hq⟩)
    rw [hxk] at this
    calc z * q = (z * q * z⁻¹) * z := by group
      _ = q * z := by
        have h' : z * q * z⁻¹ = q := this
        rw [h']
  have h5 : 5 ≤ n := by omega
  have h6 : n ≠ 6 := by omega
  set σ : Perm (Fin n) := AltWeakBalance.autPerm e h5 h6 x with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hx1 ((AltWeakBalance.autPerm e h5 h6).injective (by rw [map_one]; exact h))
  set ι : ↥Kb →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hι
  have hιi : Function.Injective ι := fun a a' h => e.injective (Subtype.ext h)
  have hιapp : ∀ k : ↥Kb, ι k = ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) := fun _ => rfl
  have hιx : ∀ k : ↥Kb, ι (x k) = σ * ι k * σ⁻¹ := fun k => AltWeakBalance.autPerm_spec e h5 h6 x k
  have hιrange : ι.range = alternatingGroup (Fin n) := by
    ext π
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).2
    · intro hπ
      exact ⟨e.symm ⟨π, hπ⟩, by rw [hιapp, MulEquiv.apply_symm_apply]⟩
  set A₁ : Subgroup ↥Kb := (Kb ⊓ Subgroup.centralizer ({z} : Set _)).subgroupOf Kb with hA₁
  have hA₁map : A₁.map ι = Claims126.cA σ := by
    ext π
    rw [Claims126.mem_cA]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(e k).2, ?_⟩
      have hkz : z * (k : _) = (k : _) * z := by
        have := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2
        exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
      have hxkk : x k = k := by
        apply Subtype.ext
        rw [hxk, hkz]
        group
      have h1 := hιx k
      rw [hxkk] at h1
      calc ι k * σ = (σ * ι k * σ⁻¹) * σ := by rw [← h1]
        _ = σ * ι k := by group
    · rintro ⟨hπA, hπσ⟩
      refine ⟨e.symm ⟨π, hπA⟩, ?_, by rw [hιapp, MulEquiv.apply_symm_apply]⟩
      set k := e.symm ⟨π, hπA⟩ with hkdef
      have hιk : ι k = π := by rw [hιapp, hkdef, MulEquiv.apply_symm_apply]
      have hxkk : x k = k := by
        apply hιi
        rw [hιx, hιk]
        calc σ * π * σ⁻¹ = (π * σ) * σ⁻¹ := by rw [hπσ]
          _ = π := by group
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨k.2, ?_⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val hxkk
      rw [hxk] at this
      calc (k : _) * z = (z * (k : _) * z⁻¹) * z := by rw [this]
        _ = z * (k : _) := by group
  set Jb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C J with hJb
  have hJbK : Jb ≤ Kb := barX_mono_of_le 3 hJL
  set J₁ : Subgroup ↥Kb := Jb.subgroupOf Kb with hJ₁def
  have hJ₁ : GLAPComponent 3 A₁ J₁ := by
    have hd : IsPGroup 3 (Subgroup.zpowers b) := l119_isPGroup_zpowers hb3
    have h1 := Prop126b.glaPComponent_barX_inf_centralizer hp (M := C) hbC hLC hbN hd hJ
    exact Prop126b.glaPComponent_subgroupOf hp inf_le_left h1
  have hker : Nat.Coprime 3 (Nat.card ↥(A₁ ⊓ ι.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff ι).2 hιi, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hJ₁' : GLAPComponent 3 (Claims126.cA σ) (J₁.map ι) := by
    have := glaPComponent_map hp ι hker hJ₁
    rwa [hA₁map] at this
  obtain ⟨hJ₁alt, hF5⟩ := Claims126.glaPComponent_cA hσ3 hJ₁'
  set F : Finset (Fin n) := σ.supportᶜ with hF
  have hFc : Fᶜ = σ.support := by rw [hF, compl_compl]
  have hsupp3 : 3 ∣ σ.support.card := three_dvd_card_support hσ3
  have hsupp2 : 2 ≤ Fᶜ.card := by
    rw [hFc]
    have hne : σ.support.Nonempty := Finset.nonempty_iff_ne_empty.2 (fun h => hσ1
      (Equiv.Perm.support_eq_empty_iff.1 h))
    have h0 : 0 < σ.support.card := Finset.card_pos.2 hne
    obtain ⟨j, hj⟩ := hsupp3
    omega
  have hF3 : ¬ 3 ∣ F.card := by
    have htot : Fᶜ.card + F.card = n := by
      rw [Finset.card_compl_add_card, Fintype.card_fin]
    rw [hFc] at htot
    obtain ⟨j, hj⟩ := hsupp3
    omega
  obtain ⟨hTA, hTel, hTc⟩ := Claims136.T_facts
  set T' : Subgroup (barOf 3 J) :=
    (CFSG.LocalAnalysis.GLTheoremB.S7.T.subgroupOf (alternatingGroup (Fin 7))).map
      eJ.symm.toMonoidHom with hT'
  have hT'el : IsElemAbelian 3 T' :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hTel _) _
  have hT'c : Nat.card ↥T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective eJ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, hTc]
  obtain ⟨S0, hS0el, -, hS0c⟩ := exists_elemAbelian_lift (GLAPPrimeCore 3 ↥J)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card) hT'el
  set Q₀ : Subgroup G := S0.map J.subtype with hQ₀
  have hQ₀J : Q₀ ≤ J := Subgroup.map_subtype_le _
  have hQ₀el : IsElemAbelian 3 Q₀ := CFSG.SectionRank.isElemAbelian_map hS0el _
  have hQ₀c : Nat.card ↥Q₀ = 9 := by
    rw [hQ₀, Subgroup.card_map_of_injective J.subtype_injective, hS0c, hT'c]
  have hQ₀p : IsPGroup 3 ↥Q₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hQ₀el.2 g.1 g.2)⟩
  have hQ₀N : Subgroup.normalizer (Q₀ : Set G) ≤ W := hnorm Q₀ (hQ₀J.trans hJV) hQ₀el hQ₀c
  set Qb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C Q₀ with hQb
  have hQbJ : Qb ≤ Jb := barX_mono_of_le 3 hQ₀J
  set Q₁ : Subgroup ↥Kb := Qb.subgroupOf Kb with hQ₁
  have hQ₁J : Q₁ ≤ J₁ := fun q hq => Subgroup.mem_subgroupOf.2 (hQbJ (Subgroup.mem_subgroupOf.1 hq))
  have hQbp : IsPGroup 3 ↥Qb := by
    have h1 : IsPGroup 3 ↥(Q₀.subgroupOf C) :=
      hQ₀p.of_equiv (Subgroup.subgroupOfEquivOfLe (hQ₀J.trans hJC)).symm
    exact h1.map _
  have hQ₁p : IsPGroup 3 ↥Q₁ :=
    hQbp.of_equiv (Subgroup.subgroupOfEquivOfLe (hQbJ.trans hJbK)).symm
  set P : Subgroup (Perm (Fin n)) := Q₁.map ι with hP
  have hPalt : P ≤ Claims126.altOn F := by rw [← hJ₁alt]; exact Subgroup.map_mono hQ₁J
  obtain ⟨f, hfF, hfP⟩ := exists_fixed_of_isPGroup (hQ₁p.map ι)
    (fun g hg => (Claims126.mem_altOn.1 (hPalt hg)).2) hF3
  have hgen := alternatingGroup_le_sup (by omega : 4 ≤ F.card) hfF hsupp2
  set N₁ : Subgroup ↥Kb := (Claims126.altOn (insert f Fᶜ)).comap ι with hN₁
  have hN₁c : ∀ k ∈ N₁, ∀ q ∈ Q₁, k * q = q * k := by
    intro k hk q hq
    apply hιi
    rw [map_mul, map_mul]
    have hkY := (Claims126.mem_altOn.1 hk).2
    have hqP : ι q ∈ P := Subgroup.mem_map_of_mem ι hq
    have hqF := (Claims126.mem_altOn.1 (hPalt hqP)).2
    refine (Equiv.Perm.Disjoint.commute ?_).eq
    intro a
    by_cases hka : ι k a = a
    · exact Or.inl hka
    · right
      have haY := hkY (Equiv.Perm.mem_support.2 hka)
      rw [Finset.mem_insert, Finset.mem_compl] at haY
      rcases haY with rfl | haF
      · exact hfP _ hqP
      · by_contra hqa
        exact haF (hqF (Equiv.Perm.mem_support.2 hqa))
  have htop : (⊤ : Subgroup ↥Kb) ≤ J₁ ⊔ N₁ := by
    rw [← Subgroup.map_le_map_iff_of_injective hιi, ← MonoidHom.range_eq_map, hιrange,
      Subgroup.map_sup, hJ₁alt, hN₁, Subgroup.map_comap_eq, hιrange]
    refine hgen.trans (sup_le_sup_left ?_ _)
    exact le_inf (Claims126.altOn_le_alt _) le_rfl
  have hcov : Kb ≤ barX 3 C (W ⊓ C) := by
    intro y hy
    have hy1 : (⟨y, hy⟩ : ↥Kb) ∈ J₁ ⊔ N₁ := htop (Subgroup.mem_top _)
    have hy2 : y ∈ (J₁ ⊔ N₁).map Kb.subtype := ⟨⟨y, hy⟩, hy1, rfl⟩
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJbK] at hy2
    have hN₁sub : N₁.map Kb.subtype ≤ Subgroup.normalizer ((Qb : Subgroup _) : Set _) := by
      rintro _ ⟨k, hk, rfl⟩
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun q hq => ?_)
      have hqK : q ∈ Kb := hQbJ.trans hJbK hq
      have := hN₁c k hk ⟨q, hqK⟩ (Subgroup.mem_subgroupOf.2 hq)
      exact (congrArg Subtype.val this).symm
    have hfr : Subgroup.normalizer ((Qb : Subgroup _) : Set _) ≤
        barX 3 C (Subgroup.normalizer (Q₀ : Set G) ⊓ C) := by
      have hNc : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥C) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
      have hE : IsPGroup 3 ↥(Q₀.subgroupOf C) :=
        hQ₀p.of_equiv (Subgroup.subgroupOfEquivOfLe (hQ₀J.trans hJC)).symm
      refine (normalizer_map_quotient_le (GLAPPrimeCore 3 ↥C) hNc hE).trans ?_
      rintro _ ⟨m, hm, rfl⟩
      refine ⟨m, Subgroup.mem_subgroupOf.2 ⟨?_, m.2⟩, rfl⟩
      show (m : G) ∈ Subgroup.normalizer (Q₀ : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have hmn := Subgroup.mem_normalizer_iff.1 (show m ∈ Subgroup.normalizer
        ((Q₀.subgroupOf C : Subgroup ↥C) : Set ↥C) from hm)
      constructor
      · intro hq
        have hqC : q ∈ C := (hQ₀J.trans hJC) hq
        have h1 := (hmn ⟨q, hqC⟩).1 (Subgroup.mem_subgroupOf.2 hq)
        simpa using Subgroup.mem_subgroupOf.1 h1
      · intro hq
        have hqC' : (m : G) * q * (m : G)⁻¹ ∈ C := (hQ₀J.trans hJC) hq
        have hqC : q ∈ C := by
          have := C.mul_mem (C.mul_mem (C.inv_mem m.2) hqC') m.2
          simpa [mul_assoc] using this
        have h1 : (m * ⟨q, hqC⟩ * m⁻¹ : ↥C) ∈ Q₀.subgroupOf C :=
          Subgroup.mem_subgroupOf.2 (by simpa using hq)
        exact Subgroup.mem_subgroupOf.1 ((hmn ⟨q, hqC⟩).2 h1)
    have hVW' : V ≤ W := isSubnormal_le' hVW
    refine (sup_le (barX_mono_of_le 3 (le_inf (hJV.trans hVW') hJC))
      ((hN₁sub.trans hfr).trans (barX_mono_of_le 3 (inf_le_inf_right _ hQ₀N)))) hy2
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  haveI hKs : IsSimpleGroup ↥Kb := e.isSimpleGroup
  have hsn : IsSubnormal (barX 3 C (V ⊓ C) ⊓ Kb) (barX 3 C (W ⊓ C) ⊓ Kb) :=
    isSubnormal_inf (isSubnormal_barX 3 (isSubnormal_inf hVW C)) Kb
  rw [inf_eq_right.2 hcov] at hsn
  have hJbV : Jb ≤ barX 3 C (V ⊓ C) ⊓ Kb := le_inf (barX_mono_of_le 3 (le_inf hJV hJC)) hJbK
  have hJb0 : Jb ≠ ⊥ := by
    intro h0
    apply Input183.glaPComponent_ne_bot' hJ₁
    rw [hJ₁def, h0, Subgroup.bot_subgroupOf]
  have hVK : Kb ≤ barX 3 C (V ⊓ C) := by
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn hKs with h0 | h0
    · exact absurd (eq_bot_iff.2 (h0 ▸ hJbV)) hJb0
    · exact h0 ▸ inf_le_left
  obtain ⟨g₉, hg₉A, hg₉⟩ := exists_mem_alternatingGroup_orderOf_nine (α := Fin n)
    (by rw [Fintype.card_fin]; omega)
  set k₉ : ↥Kb := e.symm ⟨g₉, hg₉A⟩ with hk₉
  have hk₉o : orderOf (k₉ : ↥C ⧸ GLAPPrimeCore 3 ↥C) = 9 := by
    rw [Subgroup.orderOf_coe, hk₉, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hg₉]
  obtain ⟨v, hvVC, hvk⟩ := (mem_barX_iff 3 _).1 (hVK k₉.2)
  have h9 : 9 ∣ orderOf (v : G) := by
    rw [← hk₉o, ← hvk, Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ v
  have hvo : orderOf (v : G) ≠ 0 := (orderOf_pos (v : G)).ne'
  set u : G := (v : G) ^ (orderOf (v : G) / 9) with hu
  have huo : orderOf u = 9 := orderOf_pow_orderOf_div hvo h9
  have huV : u ∈ V := V.pow_mem hvVC.1 _
  have hu3 := hexp u huV (by rw [← huo]; exact pow_orderOf_eq_one u)
  have := orderOf_dvd_of_pow_eq_one hu3
  rw [huo] at this
  norm_num at this

end AnBranch

section Cex

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem conj_comp {m : ℕ} {B M E A D T L : Subgroup G} (hcomp : Sec13_compStatement)
    (h : Cex134 G m 3 B M E A D T L) {g : G} (hgM : g ∈ M) :
    GLAPComponent 3 M (GLBConj g L) ∧ GLAPComponent 3 (Istar 3 M D) (GLBConj g L) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hcg := Claims136.glaPComponent_conj_of_mem hLc hgM
  have hle : GLBConj g L ≤ Istar 3 M D :=
    (gLBConj_mono g h.hL.1).trans (le_iSup₂_of_le (f := fun g' (_ : g' ∈ M) => GLBConj g' (Iof 3 M D))
      g hgM le_rfl)
  exact ⟨hcg, glaPComponent_of_le hp hcg hle (istar_le_M 3 M D)⟩

theorem fam_props (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L) (A0 : Subgroup ↥M) :
    ∀ X ∈ Lemma136.l136Fam M L A0,
      Nonempty (↥X ≃* alternatingGroup (Fin 7)) ∧ 9 ≤ Nat.card ↥(barX 3 M B ⊓ X) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  obtain ⟨-, eM, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  rintro X ⟨z, -, rfl⟩
  have eX : ↥(GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) z) (barX 3 M L)) ≃*
      alternatingGroup (Fin 7) := (conjEquiv _ (barX 3 M L)).symm.trans eM
  refine ⟨⟨eX⟩, ?_⟩
  obtain ⟨hcg, hcgI⟩ := conj_comp hcomp h z.2
  obtain ⟨-, -, -, -, hrk⟩ := (h133 h.toSec13).2 _ hcgI
  have hbarg := l119_barX_gLBConj (p := 3) (C := M) (H := L) z.2 hLM
  have eL : barOf 3 (GLBConj (z : G) L) ≃* alternatingGroup (Fin 7) :=
    ((quotEquivBarX hp hcg.1 hcg.2.1).trans (MulEquiv.subgroupCongr hbarg)).trans eX
  have h2 := Claims136.two_le_pRank_of_alt7 eL
  have hBel : IsElemAbelian 3 (B ⊓ GLBConj (z : G) L) :=
    CFSG.Open.IsElemAbelian.mono h.uniq.elemAbelian inf_le_left
  have hcard : 9 ≤ Nat.card ↥(B ⊓ GLBConj (z : G) L) := by
    rw [Claims136.card_eq_pow_pRank3 hBel, hrk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (GLBConj (z : G) L) := Nat.pow_le_pow_right (by norm_num) h2
  have hBp : IsPGroup 3 ↥(B ⊓ GLBConj (z : G) L) :=
    fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hBel.2 g.1 g.2)⟩
  have hc := card_barX_of_isPGroup hp hBp (inf_le_right.trans hcg.1)
  rw [← hc] at hcard
  refine hcard.trans (Subgroup.card_le_of_le (le_inf (barX_mono_of_le 3 inf_le_left) ?_))
  rw [← hbarg]
  exact barX_mono_of_le 3 inf_le_right

theorem lstarBar_conj_le (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {D' : Subgroup G} (hD'M : D' ≤ M)
    {P : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)} (hP : IsPGroup 3 ↥P)
    (hPL : P ≤ barX 3 M (Lstarsub D' L)) :
    ∃ g ∈ barX 3 M (Lstarsub D' L), GLBConj g P ≤ barX 3 M B := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hfam := fam_props hP95 h111 h121 hcomp h133 h (D'.subgroupOf M)
  rw [Lemma136.l136_barX_lstar_eq_sSup hD'M hLM] at hPL ⊢
  have hBp : IsPGroup 3 ↥(barX 3 M B) := by
    have h1 : IsPGroup 3 ↥B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (h.uniq.elemAbelian.2 g.1 g.2)⟩
    exact (h1.of_equiv (Subgroup.subgroupOfEquivOfLe h.uniq.le).symm).map _
  refine exists_conj_le_of_family hBp (Lemma136.l136_fam_comm hLc _) ?_ ?_
    (fun X hX => (hfam X hX).2) hP hPL
  · intro X hX x hx hxc
    obtain ⟨⟨eX⟩, -⟩ := hfam X hX
    have hz : eX ⟨x, hx⟩ ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := eX.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc k k.2).symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz
    have := congrArg Subtype.val (eX.injective (hz.trans (map_one eX).symm))
    exact this
  · intro X hX
    obtain ⟨⟨eX⟩, -⟩ := hfam X hX
    refine ⟨280, ?_, by norm_num⟩
    rw [Nat.card_congr eX.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl

theorem isPGroup_barX_of_le {M P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup 3 ↥P) :
    IsPGroup 3 ↥(barX 3 M P) :=
  (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm).map _

theorem lstarsub_le {M D L : Subgroup G} (hDM : D ≤ M) (hLM : L ≤ M) : Lstarsub D L ≤ M :=
  iSup₂_le fun _ hg => Lemma136.l136_gLBConj_le hLM (hDM hg)

theorem barX_B_pow_three {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {w : ↥M ⧸ GLAPPrimeCore 3 ↥M} (hw : w ∈ barX 3 M B) : w ^ 3 = 1 := by
  obtain ⟨b', hb', rfl⟩ := (mem_barX_iff 3 _).1 hw
  rw [← map_pow]
  have : b' ^ 3 = 1 := Subtype.ext (by simpa using h.uniq.elemAbelian.2 _ hb')
  rw [this, map_one]

theorem lstar_bar_conj (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {D' : Subgroup G} (hD'M : D' ≤ M)
    {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hPL : P ≤ Lstarsub D' L) :
    ∃ g : ↥M, GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) g : ↥M ⧸ GLAPPrimeCore 3 ↥M)
      (barX 3 M P) ≤ barX 3 M B := by
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLsM : Lstarsub D' L ≤ M := lstarsub_le hD'M hLc.1
  obtain ⟨g, -, hg⟩ := lstarBar_conj_le hP95 h111 h121 hcomp h133 h hD'M
    (isPGroup_barX_of_le (hPL.trans hLsM) hP) (barX_mono_of_le 3 hPL)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨g₀, hg⟩

theorem lstar_pow_three (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L) :
    ∀ u ∈ Lstarsub D L, u ^ 9 = 1 → u ^ 3 = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hDM : D ≤ M := h.hD.1.trans h.pair.1.2.1.1.1.1
  have hLsM : Lstarsub D L ≤ M := lstarsub_le hDM hLc.1
  intro u hu hu9
  have hup : IsPGroup 3 ↥(Subgroup.zpowers u) := by
    have h1 : orderOf u ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hu9)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hPL : Subgroup.zpowers u ≤ Lstarsub D L := (Subgroup.zpowers_le).2 hu
  obtain ⟨g₀, hg⟩ := lstar_bar_conj hP95 h111 h121 hcomp h133 h hDM hup hPL
  set gb : ↥M ⧸ GLAPPrimeCore 3 ↥M := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) g₀ with hgb
  set ub : ↥M ⧸ GLAPPrimeCore 3 ↥M := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨u, hLsM hu⟩ with hub
  have hubP : ub ∈ barX 3 M (Subgroup.zpowers u) :=
    (mem_barX_iff 3 _).2 ⟨⟨u, hLsM hu⟩, Subgroup.mem_zpowers u, rfl⟩
  have hw : gb⁻¹ * ub * gb ∈ barX 3 M B := hg (mem_gLBConj.2 (by group; exact hubP))
  have hw3 := barX_B_pow_three h hw
  have hub3 : ub ^ 3 = 1 := by
    have : (gb⁻¹ * ub * gb) ^ 3 = gb⁻¹ * ub ^ 3 * gb := by
      have h' := conj_pow (a := gb⁻¹) (b := ub) (i := 3)
      rwa [inv_inv] at h'
    rw [this] at hw3
    have h2 : ub ^ 3 = gb * (gb⁻¹ * ub ^ 3 * gb) * gb⁻¹ := by group
    rw [h2, hw3]
    group
  have hcore : ((⟨u, hLsM hu⟩ : ↥M) ^ 3) ∈ GLAPPrimeCore 3 ↥M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hub3
  have hcore' : u ^ 3 ∈ GLAPPrimeCoreOf 3 M :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff 3 M _).2
      ⟨M.pow_mem (hLsM hu) 3, by simpa using hcore⟩
  exact Claims136.eq_one_of_mem_core_of_isPGroup hup (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) 3)
    hcore'

theorem lstar_comm (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {D' : Subgroup G} (hD'M : D' ≤ M)
    {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hPL : P ≤ Lstarsub D' L) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hPM : P ≤ M := hPL.trans (lstarsub_le hD'M hLc.1)
  obtain ⟨g₀, hg⟩ := lstar_bar_conj hP95 h111 h121 hcomp h133 h hD'M hP hPL
  set gb : ↥M ⧸ GLAPPrimeCore 3 ↥M := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) g₀ with hgb
  have hBab : ∀ w₁ ∈ barX 3 M B, ∀ w₂ ∈ barX 3 M B, w₁ * w₂ = w₂ * w₁ := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨b₁, hb₁, rfl⟩ := (mem_barX_iff 3 _).1 hw₁
    obtain ⟨b₂, hb₂, rfl⟩ := (mem_barX_iff 3 _).1 hw₂
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (b₁ : G) * b₂ = b₂ * b₁
    exact congrArg Subtype.val (h.uniq.elemAbelian.1.is_comm.comm ⟨_, hb₁⟩ ⟨_, hb₂⟩)
  intro x hx y hy
  have hmem : ∀ z (hz : z ∈ P), gb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨z, hPM hz⟩ * gb ∈
      barX 3 M B := fun z hz =>
    hg (mem_gLBConj.2 (by
      group
      exact (mem_barX_iff 3 _).2 ⟨⟨z, hPM hz⟩, hz, rfl⟩))
  have h1 := hBab _ (hmem x hx) _ (hmem y hy)
  refine Lemma136b.commute_of_bar (hPM hx) (hPM hy) hP hx hy ?_
  have h2 : gb⁻¹ * (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨x, hPM hx⟩ *
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hPM hy⟩) * gb = gb⁻¹ *
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hPM hy⟩ *
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨x, hPM hx⟩) * gb := by
    calc _ = (gb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨x, hPM hx⟩ * gb) *
          (gb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hPM hy⟩ * gb) := by group
      _ = (gb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hPM hy⟩ * gb) *
          (gb⁻¹ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨x, hPM hx⟩ * gb) := h1
      _ = _ := by group
  simpa using h2

theorem lstar_normalizer_le (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {Q : Subgroup G} (hQL : Q ≤ Lstarsub D L) (hQel : IsElemAbelian 3 Q) (hQc : Nat.card Q = 9) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hDM : D ≤ M := h.hD.1.trans h.pair.1.2.1.1.1.1
  have hQM : Q ≤ M := hQL.trans (lstarsub_le hDM hLc.1)
  have hQp : IsPGroup 3 ↥Q := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hQel.2 g.1 g.2)⟩
  have hBp : IsPGroup 3 ↥B :=
    fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (h.uniq.elemAbelian.2 g.1 g.2)⟩
  obtain ⟨g₀, hg⟩ := lstar_bar_conj hP95 h111 h121 hcomp h133 h hDM hQp hQL
  set Q₁ : Subgroup G := GLBConj (g₀ : G) Q with hQ₁
  have hQ₁M : Q₁ ≤ M := Lemma136.l136_gLBConj_le hQM g₀.2
  have hQ₁bar : barX 3 M Q₁ ≤ barX 3 M B := by
    rw [hQ₁, l119_barX_gLBConj (p := 3) g₀.2 hQM]
    exact hg
  have hQ₁p : IsPGroup 3 ↥Q₁ := hQp.of_equiv (conjEquiv (g₀ : G) Q)
  set W : Subgroup G := ((barX 3 M B).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M))).map M.subtype
    with hW
  have hWM : W ≤ M := Subgroup.map_subtype_le _
  have hBW : B ≤ W := fun b hb =>
    ⟨⟨b, h.uniq.le hb⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hQ₁W : Q₁ ≤ W := fun q hq =>
    ⟨⟨q, hQ₁M hq⟩, hQ₁bar (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hq)), rfl⟩
  obtain ⟨x, hxW, S, hSp, hSW, hBS, hQS⟩ := exists_conj_le_pGroup' hBW hBp hQ₁W hQ₁p
  have hSB : S = B := by
    have h1 : barX 3 M S ≤ barX 3 M B := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨s', hs', hss'⟩ := hSW (Subgroup.mem_subgroupOf.1 hs)
      have : s' = s := Subtype.ext hss'
      rw [← this]
      exact hs'
    have h2 : Nat.card ↥S ≤ Nat.card ↥B := by
      rw [← card_barX_of_isPGroup hp hSp (hSW.trans hWM), ← card_barX_of_isPGroup hp hBp h.uniq.le]
      exact Subgroup.card_le_of_le h1
    exact (Subgroup.eq_of_le_of_card_ge hBS h2).symm
  rw [hSB, hQ₁, gLBConj_gLBConj] at hQS
  set c : G := (g₀ : G) * x with hc
  have hcM : c ∈ M := M.mul_mem g₀.2 (hWM hxW)
  have hQ₂el : IsElemAbelian 3 (GLBConj c Q) := CFSG.Open.IsElemAbelian.mono h.uniq.elemAbelian hQS
  have hQ₂c : Nat.card ↥(GLBConj c Q) = 3 ^ 2 := by
    rw [← Nat.card_congr (conjEquiv c Q).toEquiv, hQc]
    norm_num
  have hrk : 2 ≤ CFSG.Open.pRank 3 (GLBConj c Q) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQ₂el hQ₂c
  have hN₂' : Subgroup.normalizer ((GLBConj c Q : Subgroup G) : Set G) ≤ GLBCore 3 2 B :=
    le_sSup ⟨_, hQS, hrk, rfl⟩
  have hN₂ : Subgroup.normalizer ((GLBConj c Q : Subgroup G) : Set G) ≤ M :=
    hN₂'.trans h.uniq.clause_d
  intro y hy
  have hy' : c⁻¹ * y * c ∈ Subgroup.normalizer ((GLBConj c Q : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq] at hy ⊢
    rw [gLBConj_gLBConj, show c * (c⁻¹ * y * c) = y * c by group, ← gLBConj_gLBConj, hy]
  have := hN₂ hy'
  have e : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hcM this) (M.inv_mem hcM)

theorem mem_normalizer_inf' {A B : Subgroup G} {k : G}
    (hA : k ∈ Subgroup.normalizer (A : Set G)) (hB : k ∈ Subgroup.normalizer (B : Set G)) :
    k ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_iff.2 fun x =>
    and_congr (Subgroup.mem_normalizer_iff.1 hA x) (Subgroup.mem_normalizer_iff.1 hB x)

theorem center_eq_bot_of_comm_sylow {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hO : GLAPPrimeCore 3 Y = ⊥) (S : Sylow 3 Y)
    (hS : ∀ x ∈ (S : Subgroup Y), ∀ y ∈ (S : Subgroup Y), x * y = y * x) :
    Subgroup.center Y = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hpg := SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_three hO
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3
    (SchurFacts.prime_dvd_card_of_isPGroup Nat.prime_three hpg hne)
  have hz1 : (z : Y) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzp : (z : Y) ^ 3 = 1 := by
    have h1 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact congrArg Subtype.val h1
  exact CFSG.LocalAnalysis.RankThreeTheoremC.not_isMulCommutative_sylow_of_isPerfect ⟨hperf⟩ S z.2
    hz1 hzp ⟨⟨fun a b => Subtype.ext (hS a a.2 b b.2)⟩⟩

theorem center_barOf_eq_bot (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {X J : Subgroup G} (hJ : GLAPComponent 3 X J) (hJL : J ≤ Lstarsub D L) :
    Subgroup.center (barOf 3 J) = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hq := l119_isQuasisimple_barOf hp hJ
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥J))
  set f : ↥J →* barOf 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hSc : ∀ x ∈ (S : Subgroup ↥J), ∀ y ∈ (S : Subgroup ↥J), x * y = y * x := by
    have hS' : IsPGroup 3 ↥((S : Subgroup ↥J).map J.subtype) := S.isPGroup'.map _
    have hDM : D ≤ M := h.hD.1.trans h.pair.1.2.1.1.1.1
    have hcomm := lstar_comm hP95 h111 h121 hcomp h133 h hDM hS'
      ((Subgroup.map_subtype_le _).trans hJL)
    intro x hx y hy
    exact Subtype.ext (hcomm _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy))
  refine center_eq_bot_of_comm_sylow hq.1 (glaPPrimeCore_quotient_eq_bot hp) (S.mapSurjective hfs) ?_
  rw [Sylow.coe_mapSurjective]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hSc x hx y hy]

noncomputable def quotCenterEquivOfBot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    (X ⧸ Subgroup.center X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem bd_facts (hcomp : Sec13_compStatement) {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (b : ↥M) (hbB : (b : G) ∈ B)
    (hb1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b ≠ 1)
    (hbc : ∀ y ∈ barX 3 M D ⊔ barX 3 M (Lstarsub D L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b * y = y * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b)
    (d : ↥M) (hdD : (d : G) ∈ D) (hd1 : (d : G) ≠ 1) :
    (b : G) * d = d * b ∧ orderOf (b : G) = 3 ∧ orderOf (d : G) = 3 ∧
      (b : G) ∈ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) ∧
      (d : G) ∈ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) ∧
      (∀ g ∈ D, (b : G) ∈ Subgroup.normalizer ((GLBConj g L : Subgroup G) : Set G)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hDA : D ≤ A := h.hD.1
  have hDM : D ≤ M := hDA.trans h.pair.1.2.1.1.1.1
  have hbP : (b : G) ∈ A ⊔ B := Subgroup.mem_sup_right hbB
  have hdP : (d : G) ∈ A ⊔ B := Subgroup.mem_sup_left (hDA hdD)
  have hdbar : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) d ∈ barX 3 M D :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hdD)
  have hbd : (b : G) * d = d * b :=
    Lemma136b.commute_of_bar b.2 d.2 h.hAB hbP hdP (hbc _ (Subgroup.mem_sup_left hdbar))
  have hb1' : (b : G) ≠ 1 := fun h1 => hb1 (by rw [show b = 1 from Subtype.ext h1, map_one])
  have hbo : orderOf (b : G) = 3 := orderOf_eq_prime (h.uniq.elemAbelian.2 _ hbB) hb1'
  have hdo : orderOf (d : G) = 3 := orderOf_eq_prime (h.hD.2.1.2 _ hdD) hd1
  have hcompg : ∀ g ∈ D, GLAPComponent 3 M (GLBConj g L) := fun g hg =>
    Claims136.glaPComponent_conj_of_mem hLc (hDM hg)
  have hLgL : ∀ g ∈ D, GLBConj g L ≤ Lstarsub D L := fun g hg =>
    le_iSup₂_of_le (f := fun d' (_ : d' ∈ D) => GLBConj d' L) g hg le_rfl
  have hbN : ∀ g ∈ D, (b : G) ∈ Subgroup.normalizer ((GLBConj g L : Subgroup G) : Set G) := by
    intro g hg
    refine Lemma136.l136_mem_normalizer_of_bar (hcompg g hg) b
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_))
    exact (hbc y (Subgroup.mem_sup_right (barX_mono_of_le 3 (hLgL g hg) hy))).symm
  have hbNs : (b : G) ∈ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq, Lstarsub, Claims136.gLBConj_iSup₂]
    exact iSup_congr fun g => iSup_congr fun hg => gLBConj_eq_of_mem_normalizer (hbN g hg)
  have hconj : ∀ y ∈ D, GLBConj y (Lstarsub D L) ≤ Lstarsub D L := by
    intro y hy
    rw [Lstarsub, Claims136.gLBConj_iSup₂]
    refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (f := fun g' (_ : g' ∈ D) => GLBConj g' L) (g * y) (D.mul_mem hg hy) le_rfl
  have hdNs : (d : G) ∈ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) :=
    Lemma135.mem_normalizer_of_gLBConj_le (hconj _ hdD) (hconj _ (D.inv_mem hdD))
  exact ⟨hbd, hbo, hdo, hbNs, hdNs, hbN⟩

theorem type_of_J (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L) (b : ↥M) (hbB : (b : G) ∈ B)
    (hb1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b ≠ 1)
    (hbc : ∀ y ∈ barX 3 M D ⊔ barX 3 M (Lstarsub D L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b * y = y * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b)
    (d : ↥M) (hdD : (d : G) ∈ D) (hd1 : (d : G) ≠ 1)
    (hJd : ¬ (d : G) ∈ Subgroup.normalizer (L : Set G) ∨ (d : G) ∈ centBar 3 ⊤ L)
    {J : Subgroup G} (hJL : J ≤ Lstarsub D L)
    (hJc : GLAPComponent 3 (Subgroup.centralizer ({(b : G), (d : G)} : Set G)) J) :
    Nonempty (barOf 3 J ≃* alternatingGroup (Fin 7)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hLsn : IsSubnormal L M := hLc.2.1
  have hDA : D ≤ A := h.hD.1
  have hDM : D ≤ M := hDA.trans h.pair.1.2.1.1.1.1
  have hLsM : Lstarsub D L ≤ M := lstarsub_le hDM hLM
  obtain ⟨hbd, hbo, hdo, hbNs, hdNs, -⟩ := bd_facts hcomp h b hbB hb1 hbc d hdD hd1
  have hfam := fam_props hP95 h111 h121 hcomp h133 h (D.subgroupOf M)
  have hb3 : IsPGroup 3 ↥(Subgroup.zpowers (b : G)) := l119_isPGroup_zpowers (hbo ▸ pow_orderOf_eq_one _)
  have hd3 : IsPGroup 3 ↥(Subgroup.zpowers (d : G)) := l119_isPGroup_zpowers (hdo ▸ pow_orderOf_eq_one _)
  set Mb := ↥M ⧸ GLAPPrimeCore 3 ↥M
  set db : Mb := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) d with hdb
  set 𝓛 := Lemma136.l136Fam M L (D.subgroupOf M) with h𝓛
  have hLbar : barX 3 M (Lstarsub D L) = sSup 𝓛 := Lemma136.l136_barX_lstar_eq_sSup hDM hLM
  have hJbd : J ≤ Cg (b : G) ⊓ Cg (d : G) := by
    rw [← Claims136.centralizer_pair]; exact hJc.1
  have hdCb : (d : G) ∈ Cg (b : G) := Subgroup.mem_centralizer_singleton_iff.2 hbd.symm
  have hJY : GLAPComponent 3 ((Lstarsub D L ⊓ Cg (b : G)) ⊓ Cg (d : G)) J := by
    refine glaPComponent_of_le hp hJc (le_inf (le_inf hJL (le_inf_iff.1 hJbd).1)
      (le_inf_iff.1 hJbd).2) ?_
    rw [Claims136.centralizer_pair]
    exact inf_le_inf_right _ inf_le_right
  have hdNY : (d : G) ∈ Subgroup.normalizer
      ((Lstarsub D L ⊓ Cg (b : G) : Subgroup G) : Set G) :=
    mem_normalizer_inf' hdNs (Subgroup.le_normalizer hdCb)
  have hJbar := Prop126b.glaPComponent_barX_inf_centralizer hp (M := M) d.2
    (inf_le_left.trans hLsM) hdNY hd3 hJY
  have hbarb : barX 3 M (Lstarsub D L ⊓ Cg (b : G)) = barX 3 M (Lstarsub D L) := by
    rw [barX_inf_centralizer hp b.2 hLsM hbNs hb3]
    exact inf_eq_left.2 fun y hy => Subgroup.mem_centralizer_singleton_iff.2
      (hbc y (Subgroup.mem_sup_right hy)).symm
  rw [hbarb, hLbar] at hJbar
  have hdbo : orderOf db = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hdb, ← map_pow]
      have : d ^ 3 = 1 := Subtype.ext (by simpa using hdo ▸ pow_orderOf_eq_one (d : G))
      rw [this, map_one]
    · intro h0
      apply hd1
      have hO : (d : G) ∈ GLAPPrimeCoreOf 3 M :=
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff 3 M _).2
          ⟨d.2, (QuotientGroup.eq_one_iff _).1 h0⟩
      exact Claims136.eq_one_of_mem_core_of_isPGroup hd3 (Subgroup.mem_zpowers _) hO
  have hdbN : db ∈ Subgroup.normalizer ((sSup 𝓛 : Subgroup Mb) : Set Mb) := by
    rw [← hLbar]
    exact Lemma136.l136_mk_mem_normalizer_barX hLsM d.2 hdNs
  have hcompX : ∀ X ∈ 𝓛, IsComponentOf X (sSup 𝓛) := by
    intro X hX
    obtain ⟨hXle, hXsn, hXq⟩ := Lemma136.l136_fam_comp hLc _ X hX
    exact ⟨le_sSup hX, isSubnormal_of_le_of_le hXsn (le_sSup hX) le_top, hXq⟩
  have hcase : db ∈ Subgroup.centralizer ((sSup 𝓛 : Subgroup Mb) : Set Mb) ∨
      ∀ X ∈ 𝓛, db ∉ Subgroup.normalizer ((X : Subgroup Mb) : Set Mb) := by
    rcases hJd with hnN | hcent
    · right
      rintro X ⟨z, hz, rfl⟩ hXN
      have hzD : (z : G) ∈ D := Subgroup.mem_subgroupOf.1 hz
      have hcg := Claims136.glaPComponent_conj_of_mem hLc z.2
      have hbarz := l119_barX_gLBConj (p := 3) (C := M) (H := L) z.2 hLM
      rw [← hbarz] at hXN
      have hdz := Lemma136.l136_mem_normalizer_of_bar hcg d hXN
      apply hnN
      rw [mem_normalizer_iff_gLBConj_eq] at hdz ⊢
      have hzd : (z : G) * d = d * z :=
        congrArg Subtype.val (h.hD.2.1.1.is_comm.comm ⟨_, hzD⟩ ⟨_, hdD⟩)
      rw [gLBConj_gLBConj, hzd, ← gLBConj_gLBConj] at hdz
      have := congrArg (GLBConj (z : G)⁻¹) hdz
      rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this
    · left
      have hdL := Lemma136.l136_centralizes_barX_of_centBar hp hLM hLsn d.2 hcent
      suffices hle : sSup 𝓛 ≤ Subgroup.centralizer ({db} : Set Mb) by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
      refine sSup_le fun X hX => ?_
      obtain ⟨z, hz, rfl⟩ := hX
      have hzD : (z : G) ∈ D := Subgroup.mem_subgroupOf.1 hz
      have hzd : (z : G) * d = d * z :=
        congrArg Subtype.val (h.hD.2.1.1.is_comm.comm ⟨_, hzD⟩ ⟨_, hdD⟩)
      have hzdb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) z * db = db * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) z := by
        rw [hdb, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hzd
      intro w hw
      rw [mem_gLBConj] at hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      set zb := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) z
      have h1 := hdL _ hw
      have e : w = zb⁻¹ * (zb * w * zb⁻¹) * zb := by group
      rw [e]
      have hzdb' : zb⁻¹ * db = db * zb⁻¹ := by
        calc zb⁻¹ * db = zb⁻¹ * (db * zb) * zb⁻¹ := by group
          _ = zb⁻¹ * (zb * db) * zb⁻¹ := by rw [hzdb]
          _ = db * zb⁻¹ := by group
      calc zb⁻¹ * (zb * w * zb⁻¹) * zb * db = zb⁻¹ * (zb * w * zb⁻¹) * (db * zb) := by
            rw [mul_assoc, hzdb, ← mul_assoc]
        _ = zb⁻¹ * ((zb * w * zb⁻¹) * db) * zb := by group
        _ = zb⁻¹ * (db * (zb * w * zb⁻¹)) * zb := by rw [← h1]
        _ = (zb⁻¹ * db) * (zb * w * zb⁻¹) * zb := by group
        _ = (db * zb⁻¹) * (zb * w * zb⁻¹) * zb := by rw [hzdb']
        _ = db * (zb⁻¹ * (zb * w * zb⁻¹) * zb) := by group
  obtain ⟨X, hX, ⟨eX⟩⟩ := input18_3_diag_holds Mb 3 hp (sSup 𝓛) 𝓛 db hdbo hdbN rfl hcompX
    (Lemma136.l136_fam_comm hLc _) hcase _ hJbar
  obtain ⟨⟨fX⟩, -⟩ := hfam X hX
  have hXc : Subgroup.center ↥X = ⊥ := by
    have := Subgroup.map_center_eq fX
    rw [alternatingGroup.center_eq_bot (by simp)] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ fX.injective).1 this
  have e1 : barOf 3 J ⧸ Subgroup.center (barOf 3 J) ≃* alternatingGroup (Fin 7) :=
    ((l119_centerQuot_equiv (Prop126b.barOfBarX hp (hJL.trans hLsM))).trans eX).trans
      ((quotCenterEquivOfBot hXc).trans fX)
  have hZ := center_barOf_eq_bot hP95 h111 h121 hcomp h133 h hJc hJL
  exact ⟨(quotCenterEquivOfBot hZ).symm.trans e1⟩

end Cex

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf) in
@[expose] def Input14_15A7 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 3 K = ⊥ → ∀ x : MulAut K, orderOf x = 3 →
      ∀ J₁ : Subgroup K, GLAPComponent 3 (Prop126.autFixSub x) J₁ →
        MovingAround.IsAltType 7 (barOf 3 J₁) →
          ∃ k : ℕ, 1 ≤ k ∧ MovingAround.IsAltType (7 + 3 * k) (K ⧸ Subgroup.center K)

section Pumpup

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem pumpup_type' (hI : Input14_15A7) (hkp : CFSG.Open.IsKProper G)
    {a z : G} (hC : Cg a ≠ ⊤) (hzC : z ∈ Cg a) (hz3 : z ^ 3 = 1)
    {L J₀ : Subgroup G} (hL : GLAPComponent 3 (Cg a) L)
    (hzL : z ∈ Subgroup.normalizer (L : Set G))
    (hJ₀ : GLAPComponent 3 (L ⊓ Cg z) J₀)
    (hJty : MovingAround.IsAltType 7 (barOf 3 J₀))
    (hnc : ∃ q ∈ barX 3 (Cg a) L, QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨z, hzC⟩ * q ≠
      q * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨z, hzC⟩) :
    ∃ k : ℕ, 1 ≤ k ∧ MovingAround.IsAltType (7 + 3 * k)
      (↥(barX 3 (Cg a) L) ⧸ Subgroup.center ↥(barX 3 (Cg a) L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set zb : ↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a) := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨z, hzC⟩
    with hzb
  have hKbc : IsComponentOf (barX 3 (Cg a) L) ⊤ := hL.2.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg a) L) := hKbc.2.2
  have hKG : CFSG.Open.IsKGroup ↥(barX 3 (Cg a) L) :=
    ((isKGroup_of_isKProper hkp hC).quotient _).subgroup _
  have hcore : GLAPPrimeCore 3 ↥(barX 3 (Cg a) L) = ⊥ :=
    Prop126b.primeCore_sub_eq_bot Nat.prime_three (glaPPrimeCore_quotient_eq_bot Nat.prime_three)
      hKbc.2.1
  have hLC : L ≤ Cg a := hL.1
  have hzN : zb ∈ Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _) := by
    have h1 := l119_barX_gLBConj (p := 3) (C := Cg a) (H := L) hzC hLC
    rw [mem_normalizer_iff_gLBConj_eq.1 hzL] at h1
    exact mem_normalizer_iff_gLBConj_eq.2 h1.symm
  let x : MulAut ↥(barX 3 (Cg a) L) := (barX 3 (Cg a) L).normalizerMonoidHom ⟨zb, hzN⟩
  have hxk : ∀ k : ↥(barX 3 (Cg a) L), ((x k : ↥(barX 3 (Cg a) L)) : _) = zb * (k : _) * zb⁻¹ :=
    fun k => (barX 3 (Cg a) L).normalizerMonoidHom_apply_apply_coe ⟨zb, hzN⟩ k
  have hfix : Prop126.autFixSub x = ((barX 3 (Cg a) L) ⊓ Subgroup.centralizer
      ({zb} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))).subgroupOf (barX 3 (Cg a) L) := by
    ext k
    show x k = k ↔ _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨k.2, ?_⟩
      have := congrArg Subtype.val h
      rw [hxk] at this
      calc (k : _) * zb = (zb * (k : _) * zb⁻¹) * zb := by rw [this]
        _ = zb * (k : _) := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hxk]
      calc zb * (k : _) * zb⁻¹ = (k : _) * zb * zb⁻¹ := by rw [h]
        _ = k := by group
  have hxord : orderOf x = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have h3 : zb ^ 3 = 1 := by
        rw [hzb, ← map_pow]
        have : (⟨z, hzC⟩ : ↥(Cg a)) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
        rw [this, map_one]
      have h13 : (⟨zb, hzN⟩ : ↥(Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _))) ^ 3 = 1 :=
        Subtype.ext (by simpa using h3)
      show (barX 3 (Cg a) L).normalizerMonoidHom ⟨zb, hzN⟩ ^ 3 = 1
      rw [← map_pow, h13, map_one]
    · intro hx1
      obtain ⟨q, hq, hqne⟩ := hnc
      apply hqne
      have := congrArg Subtype.val (DFunLike.congr_fun hx1 ⟨q, hq⟩)
      rw [hxk] at this
      calc zb * q = (zb * q * zb⁻¹) * zb := by group
        _ = q * zb := by
          have h' : zb * q * zb⁻¹ = q := this
          rw [h']
  have hJ₁ : GLAPComponent 3 (Prop126.autFixSub x)
      ((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L)) := by
    have hd : IsPGroup 3 (Subgroup.zpowers z) := l119_isPGroup_zpowers hz3
    have h1 := Prop126b.glaPComponent_barX_inf_centralizer (p := 3) Nat.prime_three (M := Cg a) hzC hLC
      hzL hd hJ₀
    rw [hfix]
    exact Prop126b.glaPComponent_subgroupOf Nat.prime_three inf_le_left h1
  have hJ₀C : J₀ ≤ Cg a := hJ₀.1.trans (inf_le_left.trans hLC)
  have hJ₁le : barX 3 (Cg a) J₀ ≤ barX 3 (Cg a) L := barX_mono_of_le 3 (hJ₀.1.trans inf_le_left)
  have e : (↥J₀ ⧸ GLAPPrimeCore 3 ↥J₀) ≃*
      (↥((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L)) ⧸
        GLAPPrimeCore 3 ↥((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L))) :=
    (Prop126b.barOfBarX Nat.prime_three hJ₀C).trans
      (Prop126b.barCongr 3 (Subgroup.subgroupOfEquivOfLe hJ₁le)).symm
  exact hI ↥(barX 3 (Cg a) L) hKq hKG hcore x hxord _ hJ₁ (l119_isAltType_congr 7 e hJty)

end Pumpup

section Core

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem isPiGroup_congr {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsPiGroup p X) :
    IsPiGroup p Y :=
  Lemma1313Z.isPiGroup_of_center_quot_equiv h
    (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e h.1)
    (by rw [← glaPPrimeCore_map_iso p e, h.2.1, Subgroup.map_bot]) (l119_centerQuot_equiv e)

theorem le_piOf_of_quot {d : G} {L' : Subgroup G} (hL' : GLAPComponent 3 (Cg d) L')
    (e : ↥(barX 3 (Cg d) L') ⧸ Subgroup.center ↥(barX 3 (Cg d) L') ≃* alternatingGroup (Fin 7)) :
    L' ≤ piOf 3 d := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hKbc : IsComponentOf (barX 3 (Cg d) L') ⊤ := hL'.2.2.1
  have hcore : GLAPPrimeCore 3 ↥(barX 3 (Cg d) L') = ⊥ :=
    Prop126b.primeCore_sub_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp) hKbc.2.1
  have hpi : IsPiGroup 3 ↥(barX 3 (Cg d) L') := ⟨hKbc.2.2, hcore, Or.inr (Or.inr ⟨rfl, ⟨e⟩⟩)⟩
  have hpi' : IsPiGroup 3 (↥L' ⧸ GLAPPrimeCore 3 ↥L') :=
    isPiGroup_congr (quotEquivBarX hp hL'.1 hL'.2.1).symm hpi
  show L' ≤ piLayer 3 (Subgroup.centralizer ({d} : Set G))
  exact le_iSup_of_le L' (le_iSup_of_le ⟨hL', hpi'⟩ le_rfl)

noncomputable def barXQuotEquiv {C J : Subgroup G} (hJC : J ≤ C) (eJ : barOf 3 J ≃* alternatingGroup (Fin 7)) :
    barOf 3 (barX 3 C J) ⧸ Subgroup.center (barOf 3 (barX 3 C J)) ≃* alternatingGroup (Fin 7) :=
  (l119_centerQuot_equiv (Prop126b.barOfBarX Nat.prime_three hJC).symm).trans
    ((quotCenterEquivOfBot (Prop126b.center_eq_bot_of_isAltType_seven ⟨eJ⟩)).trans eJ)

theorem orderOf_bar {d b : G} (hbC : b ∈ Cg d) (hbo : orderOf b = 3) :
    orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b, hbC⟩) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : b ^ 3 = 1 := hbo ▸ pow_orderOf_eq_one b
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨b, hbC⟩ : ↥(Cg d)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  · intro h0
    have hO : b ∈ GLAPPrimeCoreOf 3 (Cg d) :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff 3 (Cg d) _).2
        ⟨hbC, (QuotientGroup.eq_one_iff _).1 h0⟩
    have h1 := Claims136.eq_one_of_mem_core_of_isPGroup (l119_isPGroup_zpowers hb3)
      (Subgroup.mem_zpowers b) hO
    rw [h1, orderOf_one] at hbo
    exact absurd hbo (by norm_num)

theorem p1GCore_of_inputs (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement) (hI183 : Prop115.Input18_3Gen)
    (hPump : Input14_15A7) (hAC : Prop126b.InputAltCentre) : Lemma136b.P1GCore := by
  intro G _ _ m B M E A D T L h b hbB hb1 hbc d hdD hd1 hJd J hJL hJc
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hDM : D ≤ M := h.hD.1.trans h.pair.1.2.1.1.1.1
  have hLsM : Lstarsub D L ≤ M := lstarsub_le hDM hLM
  obtain ⟨hbd, hbo, hdo, -, -, -⟩ := bd_facts hcomp h b hbB hb1 hbc d hdD hd1
  obtain ⟨eJ⟩ := type_of_J hP95 h111 h121 hcomp h133 h b hbB hb1 hbc d hdD hd1 hJd hJL hJc
  have hb3 : (b : G) ^ 3 = 1 := hbo ▸ pow_orderOf_eq_one _
  have hbC : (b : G) ∈ Cg (d : G) := Subgroup.mem_centralizer_singleton_iff.2 hbd
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers (b : G)) := l119_isPGroup_zpowers hb3
  have hCd : Cg (d : G) ≠ ⊤ := centralizer_singleton_ne_top h.standing hd1
  have hbbo := orderOf_bar hbC hbo
  set bb : ↥(Cg (d : G)) ⧸ GLAPPrimeCore 3 ↥(Cg (d : G)) :=
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg (d : G))) ⟨b, hbC⟩ with hbb
  haveI : IsSimpleGroup G := h.standing.simple
  rcases Prop126.jstar3_dichotomy h.standing.simple h.standing.nonabelian h.standing.kProper hI183
      input18_3_2_holds hbo hdo hbd hJc with
    ⟨L', hL', hJs, hbL', hJL'⟩ | ⟨Lc, hLc', hinj, hcyc, hJs, hJL'⟩
  ·
    rw [hJs] at hJL'
    have hbNL' : (b : G) ∈ Subgroup.normalizer (L' : Set G) := mem_normalizer_iff_gLBConj_eq.2 hbL'
    refine (hJL'.1.trans inf_le_left).trans ?_
    by_cases hnc : ∃ q ∈ barX 3 (Cg (d : G)) L', bb * q ≠ q * bb
    ·
      exfalso
      obtain ⟨k, hk1, hkalt⟩ := pumpup_type' hPump h.standing.kProper hCd hbC hb3 hL' hbNL' hJL'
        ⟨eJ⟩ hnc
      have hKbc : IsComponentOf (barX 3 (Cg (d : G)) L') ⊤ := hL'.2.2.1
      obtain ⟨eK⟩ := hAC ↥(barX 3 (Cg (d : G)) L') (7 + 3 * k) (by omega) hKbc.2.2
        (Prop126b.primeCore_sub_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp) hKbc.2.1) hkalt
      have hLsn : IsSubnormal (Lstarsub D L) M := by
        have hcompg : ∀ g ∈ D, GLAPComponent 3 M (GLBConj g L) := fun g hg =>
          Claims136.glaPComponent_conj_of_mem hLc (hDM hg)
        have hL0eq : Lstarsub D L = sSup ((fun g => GLBConj g L) '' (D : Set G)) := by
          rw [sSup_image]
          rfl
        rw [hL0eq]
        refine Claims136.isSubnormal_sSup _ ?_
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨(hcompg g hg).1, (hcompg g hg).2.1⟩
      exact an_branch_false hbC hb3 hL' hbNL' hJL' eJ (by omega) (by omega) eK hnc hJL hLsn
        (lstar_pow_three hP95 h111 h121 hcomp h133 h)
        (fun Q hQ hQel hQc => lstar_normalizer_le hP95 h111 h121 hcomp h133 h hQ hQel hQc)
    ·
      push Not at hnc
      set Kb := barX 3 (Cg (d : G)) L' with hKb
      have hKbc : IsComponentOf Kb ⊤ := hL'.2.2.1
      have hJbar := Prop126b.glaPComponent_barX_inf_centralizer hp (M := Cg (d : G)) hbC hL'.1 hbNL'
        hbp hJL'
      have hbbC : bb ∈ Subgroup.centralizer ((Kb : Subgroup _) : Set _) :=
        Subgroup.mem_centralizer_iff.2 fun q hq => (hnc q hq).symm
      obtain ⟨X, hX, ⟨eX⟩⟩ := input18_3_diag_holds _ 3 hp Kb {Kb} bb hbbo
        (Subgroup.centralizer_le_normalizer _ hbbC) sSup_singleton.symm
        (fun X hX => by
          rw [Set.mem_singleton_iff] at hX
          subst hX
          exact ⟨le_rfl, IsSubnormal.refl _, hKbc.2.2⟩)
        (fun X hX X' hX' hne => absurd ((Set.mem_singleton_iff.1 hX).trans
          (Set.mem_singleton_iff.1 hX').symm) hne)
        (Or.inl hbbC) _ hJbar
      rw [Set.mem_singleton_iff] at hX
      subst hX
      exact le_piOf_of_quot hL' (eX.symm.trans (barXQuotEquiv (hJL'.1.trans
        (inf_le_left.trans hL'.1)) eJ))
  ·
    rw [hJs] at hJL'
    refine (hJL'.1.trans inf_le_left).trans (iSup_le fun i => ?_)
    have hLcC : ∀ i, Lc i ≤ Cg (d : G) := fun i => (hLc' i).1
    have hsupC : (⨆ i, Lc i) ≤ Cg (d : G) := iSup_le hLcC
    have hbNs : (b : G) ∈ Subgroup.normalizer (((⨆ i, Lc i) : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_gLBConj_eq]
      unfold GLBConj
      rw [Subgroup.map_iSup]
      have h1 : ∀ i, (Lc i).map (MulAut.conj (b : G)⁻¹).toMonoidHom = Lc (i + 1) := hcyc
      simp_rw [h1]
      exact (Equiv.addRight (1 : ZMod 3)).iSup_comp (g := Lc)
    have hJbar := Prop126b.glaPComponent_barX_inf_centralizer hp (M := Cg (d : G)) hbC hsupC hbNs
      hbp hJL'
    rw [Prop126b.barX_iSup_eq 3 Lc hLcC] at hJbar
    set 𝓛 := Set.range fun i => barX 3 (Cg (d : G)) (Lc i) with h𝓛
    have hsup : (⨆ i, barX 3 (Cg (d : G)) (Lc i)) = sSup 𝓛 := (sSup_range).symm
    rw [hsup] at hJbar
    have hbbN : bb ∈ Subgroup.normalizer ((sSup 𝓛 : Subgroup _) : Set _) := by
      rw [← hsup, ← Prop126b.barX_iSup_eq 3 Lc hLcC]
      exact Lemma136.l136_mk_mem_normalizer_barX hsupC hbC hbNs
    have hcompX : ∀ X ∈ 𝓛, IsComponentOf X (sSup 𝓛) := by
      rintro _ ⟨j, rfl⟩
      obtain ⟨-, hXsn, hXq⟩ := (hLc' j).2.2.1
      exact ⟨le_sSup ⟨j, rfl⟩, isSubnormal_of_le_of_le hXsn (le_sSup ⟨j, rfl⟩) le_top, hXq⟩
    have hcommX : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
      rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩ hne x hx y hy
      exact CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.components_commute
        (hLc' j).2.2.1 (hLc' j').2.2.1 hne x hx y hy
    have hcase : ∀ X ∈ 𝓛, bb ∉ Subgroup.normalizer ((X : Subgroup _) : Set _) := by
      rintro _ ⟨j, rfl⟩ hN
      have hbN := Lemma136.l136_mem_normalizer_of_bar (hLc' j) ⟨b, hbC⟩ hN
      have h1 : GLBConj (b : G) (Lc j) = Lc j := mem_normalizer_iff_gLBConj_eq.1 hbN
      rw [hcyc j] at h1
      have h2 := hinj h1
      have h3 : (1 : ZMod 3) = 0 := by
        have := congrArg (· - j) h2
        simpa using this
      exact absurd h3 Prop126b.zmod3_one_ne_zero
    obtain ⟨X, ⟨i₀, rfl⟩, ⟨eX⟩⟩ := input18_3_diag_holds _ 3 hp (sSup 𝓛) 𝓛 bb hbbo hbbN rfl hcompX
      hcommX (Or.inr hcase) _ hJbar
    have hJC : J ≤ Cg (d : G) := hJL'.1.trans (inf_le_left.trans hsupC)
    have hi₀ : IsPiGroup 3 (barOf 3 (Lc i₀)) := by
      have e := eX.symm.trans (barXQuotEquiv hJC eJ)
      have hKbc : IsComponentOf (barX 3 (Cg (d : G)) (Lc i₀)) ⊤ := (hLc' i₀).2.2.1
      have hcore : GLAPPrimeCore 3 ↥(barX 3 (Cg (d : G)) (Lc i₀)) = ⊥ :=
        Prop126b.primeCore_sub_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp) hKbc.2.1
      exact isPiGroup_congr (quotEquivBarX hp (hLc' i₀).1 (hLc' i₀).2.1).symm
        ⟨hKbc.2.2, hcore, Or.inr (Or.inr ⟨rfl, ⟨e⟩⟩)⟩
    have hnext : ∀ j, IsPiGroup 3 (barOf 3 (Lc j)) → IsPiGroup 3 (barOf 3 (Lc (j + 1))) := by
      intro j hj
      have e := Prop126b.barCongr 3 (conjEquiv (b : G) (Lc j))
      rw [hcyc] at e
      exact isPiGroup_congr e hj
    have hstep : ∀ n : ℕ, IsPiGroup 3 (barOf 3 (Lc (i₀ + n))) := by
      intro n
      induction n with
      | zero => rw [Nat.cast_zero, add_zero]; exact hi₀
      | succ n ih =>
        rw [Nat.cast_succ, ← add_assoc]
        exact hnext _ ih
    have hpi : IsPiGroup 3 (barOf 3 (Lc i)) := by
      have := hstep (i - i₀).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    show Lc i ≤ piLayer 3 (Subgroup.centralizer ({(d : G)} : Set G))
    exact le_iSup_of_le (Lc i) (le_iSup_of_le ⟨hLc' i, hpi⟩ le_rfl)

end Core

section CaseB

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf)

theorem card_sup_zpowers_le {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ 9 := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    refine (Subgroup.zpowers_le).2 (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    exact ((Commute.zpow_left (show Commute y x from hxy.symm) i)).eq
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
  let f : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y) → ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hz
    rw [hcoe] at hz'
    obtain ⟨u, hu, v, hv, rfl⟩ := hz'
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers] at h1
  have hx3 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx)
  have hy3 : orderOf y ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy)
  nlinarith

theorem exists_plane_not_mem {E : Subgroup G} (hE : IsElemAbelian 3 E) {r : ℕ} (hr : 3 ≤ r)
    (hc : Nat.card ↥E = 3 ^ r) {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    ∃ A : Subgroup G, A ≤ E ∧ Nat.card ↥A = 9 ∧ b ∉ A ∧ ∃ c ∈ A, c ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h27 : 27 ≤ Nat.card ↥E := by
    rw [hc]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hpow : ∀ H : Subgroup G, H ≤ E → ∃ k : ℕ, Nat.card ↥H = 3 ^ k := fun H hH =>
    IsPGroup.iff_card.1 (hEp.to_le hH)
  have hcardb : Nat.card ↥(Subgroup.zpowers b) ≤ 3 := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hE.2 b hbE))
  obtain ⟨c₁, hc₁E, hc₁b⟩ : ∃ c₁ ∈ E, c₁ ∉ Subgroup.zpowers b := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers b from hcon)
    omega
  have hE₂ : Subgroup.zpowers b ⊔ Subgroup.zpowers c₁ ≤ E :=
    sup_le ((Subgroup.zpowers_le).2 hbE) ((Subgroup.zpowers_le).2 hc₁E)
  have hcardE₂ := card_sup_zpowers_le (hcomm b hbE c₁ hc₁E) (hE.2 b hbE) (hE.2 c₁ hc₁E)
  obtain ⟨c₂, hc₂E, hc₂E₂⟩ : ∃ c₂ ∈ E, c₂ ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers c₁ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers c₁ from hcon)
    omega
  set A := Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ with hA
  have hAE : A ≤ E := sup_le ((Subgroup.zpowers_le).2 hc₁E) ((Subgroup.zpowers_le).2 hc₂E)
  have hcardA := card_sup_zpowers_le (hcomm c₁ hc₁E c₂ hc₂E) (hE.2 c₁ hc₁E) (hE.2 c₂ hc₂E)
  have hc₁1 : c₁ ≠ 1 := fun h => hc₁b (h ▸ Subgroup.one_mem _)
  have key : ∀ (H : Subgroup G) (u : G), H ≤ E → Nat.card ↥H ≤ 9 → Subgroup.zpowers u < H →
      u ^ 3 = 1 → u ≠ 1 → Nat.card ↥H = 9 := by
    intro H u hHE hH9 hlt hu3 hu1
    obtain ⟨k, hk⟩ := hpow H hHE
    have h1 := card_lt_of_lt' hlt
    have hu : Nat.card ↥(Subgroup.zpowers u) = 3 := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime hu3 hu1
    rw [hk] at h1 hH9 ⊢
    have hk1 : 1 ≤ k := by
      by_contra h0
      push Not at h0
      interval_cases k
      omega
    have hk2 : k ≤ 2 := by
      by_contra h3
      push Not at h3
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h3
      omega
    interval_cases k
    · omega
    · rfl
  have hc₂c₁ : c₂ ∉ Subgroup.zpowers c₁ := fun h => hc₂E₂ (Subgroup.mem_sup_right h)
  have hA9 : Nat.card ↥A = 9 := key A c₁ hAE hcardA
    (lt_of_le_of_ne le_sup_left fun h => hc₂c₁ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂)))
    (hE.2 c₁ hc₁E) hc₁1
  refine ⟨A, hAE, hA9, fun hbA => ?_, c₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers c₁), hc₁1⟩
  have hE₂A : Subgroup.zpowers b ⊔ Subgroup.zpowers c₁ ≤ A :=
    sup_le ((Subgroup.zpowers_le).2 hbA) le_sup_left
  have hE₂9 : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c₁) = 9 := key _ b hE₂ hcardE₂
    (lt_of_le_of_ne le_sup_left fun h => hc₁b (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)))
    (hE.2 b hbE) hb1
  have heq : Subgroup.zpowers b ⊔ Subgroup.zpowers c₁ = A :=
    Subgroup.eq_of_le_of_card_ge hE₂A (by rw [hA9, hE₂9])
  exact hc₂E₂ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂))

theorem exists_lift_centralizer {K A : Subgroup G} (hA : IsPGroup 3 ↥A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (k : ↥K)
    (hfix : ∀ a (ha : a ∈ A), barAut 3 K ⟨a, hAK ha⟩ (QuotientGroup.mk k) = QuotientGroup.mk k) :
    ∃ v ∈ GLAPPrimeCoreOf 3 K, ∀ a ∈ A, a * ((k : G) * v) * a⁻¹ = (k : G) * v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOLN : ∀ u ∈ Subgroup.normalizer (K : Set G),
      u ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) := fun u hu => by
    rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, gLBConj_eq_of_mem_normalizer hu]
  refine exists_fixed_in_coset' hA (not_dvd_card_glaPPrimeCoreOf Nat.prime_three K)
    (fun a ha => hOLN a (hAK ha)) (le_normalizer_glaPPrimeCoreOf 3 K k.2) fun a ha => ?_
  have h1 := hfix a ha
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h1
  have hwL : a * (k : G) * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hAK ha) _).1 k.2
  have heq : K.normalizerMonoidHom ⟨a, hAK ha⟩ k = ⟨a * (k : G) * a⁻¹, hwL⟩ := Subtype.ext rfl
  rw [heq, QuotientGroup.eq_iff_div_mem] at h1
  refine (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff 3 K _).2
    ⟨K.mul_mem hwL (K.inv_mem k.2), ?_⟩
  rw [div_eq_mul_inv] at h1
  exact h1

theorem comm_comm_eq_one (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup 3 ↥S) {x y : G} (hx : x ∈ S) (hy : y ∈ S)
    (hyN : y ∈ Lstarsub M L) : ⁅⁅x, y⁆, y⁆ = 1 := by
  have hconj : ∀ g ∈ M, GLBConj g (Lstarsub M L) ≤ Lstarsub M L := by
    intro g hg
    rw [Lstarsub, Claims136.gLBConj_iSup₂]
    refine iSup₂_le fun g' hg' => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (f := fun g'' (_ : g'' ∈ M) => GLBConj g'' L) (g' * g) (M.mul_mem hg' hg) le_rfl
  have hnorm : ∀ g ∈ M, ∀ n ∈ Lstarsub M L, g * n * g⁻¹ ∈ Lstarsub M L := by
    intro g hg n hn
    refine hconj _ (M.inv_mem hg) (mem_gLBConj.2 ?_)
    simpa [mul_assoc] using hn
  have huN : ⁅x, y⁆ ∈ Lstarsub M L := by
    rw [commutatorElement_def]
    exact (Lstarsub M L).mul_mem (hnorm x (hSM hx) y hyN) ((Lstarsub M L).inv_mem hyN)
  have huS : ⁅x, y⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
  have hc := lstar_comm hP95 h111 h121 hcomp h133 h le_rfl (hS.to_le inf_le_left) inf_le_right
    _ ⟨huS, huN⟩ _ ⟨hy, hyN⟩
  rw [commutatorElement_def (⁅x, y⁆), hc]
  group

theorem altMain_three_false (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hfix : pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥) {b : G} {B1 : Subgroup G}
    (hP : Lemma136c.IIHardPrinted B L D hN hd b B1) {r : ℕ} (hr : 3 ≤ r)
    (hEk : IsEkIn 3 r (Cg d) (Lemma136c.bStarOf B L D b)) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg d) K)
    (hBsN : Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (K : Set G))
    (hcent : centBar 3 (Lemma136c.bStarOf B L D b) K = ⊥)
    (halt : Lemma129.Alt1916 3 r (autBar 3 (Lemma136c.bStarOf B L D b) K)) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set Bs := Lemma136c.bStarOf B L D b with hBs
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hLsn : IsSubnormal L M := hLc.2.1
  have hdA : d ∈ A := h.hD.1 hd
  have hBM : B ≤ M := h.uniq.le
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  obtain ⟨hbBL, hσb, -, -, -⟩ := hP
  have hBsB : Bs ≤ B := sup_le ((Subgroup.zpowers_le).2 hbBL.1) (inf_le_left.trans inf_le_right)
  have hbBs : b ∈ Bs := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hb3 : b ^ 3 = 1 := hBel.2 b hbBL.1
  obtain ⟨-, eM, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  have eL : barOf 3 L ≃* alternatingGroup (Fin 7) := (quotEquivBarX hp hLM hLsn).trans eM
  have hd3 : d ^ 3 = 1 := h.hD.2.1.2 d hd
  have hσ3 : barAut 3 L ⟨d, hN hd⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hN hd⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext (by simp [hd3])
    rw [this, map_one]
  obtain ⟨hσd1, -⟩ := Claims136.exists_klein eL _ hσ3 hfix
  have hb1 : b ≠ 1 := by
    intro h1
    apply hσd1
    rw [← hσb (Subgroup.le_normalizer hbBL.2)]
    have : (⟨b, Subgroup.le_normalizer hbBL.2⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 :=
      Subtype.ext h1
    rw [this, map_one]
  set Ab : Subgroup (MulAut (barOf 3 K)) := autBar 3 Bs K with hAb
  have hmemAb : ∀ y (hy : y ∈ Bs), barAut 3 K ⟨y, hBsN hy⟩ ∈ Ab := fun y hy =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨hy, hBsN hy⟩)
  have hAbcases : ∀ g ∈ Ab, ∃ y, ∃ hy : y ∈ Bs, g = barAut 3 K ⟨y, hBsN hy⟩ := by
    rintro _ ⟨⟨y, hyN⟩, hy, rfl⟩
    exact ⟨y, (Subgroup.mem_subgroupOf.1 hy).1, rfl⟩
  have hinjBs : ∀ y (hy : y ∈ Bs), barAut 3 K ⟨y, hBsN hy⟩ = 1 → y = 1 := by
    intro y hy h1
    have hmem : y ∈ centBar 3 Bs K := ⟨⟨⟨y, hBsN hy⟩, h1, rfl⟩, hy⟩
    rw [hcent] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hAbcomm : ∀ g ∈ Ab, ∀ g' ∈ Ab, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨y, hy, rfl⟩ := hAbcases g hg
    obtain ⟨y', hy', rfl⟩ := hAbcases g' hg'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show y * y' = y' * y
    exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨y, hBsB hy⟩ ⟨y', hBsB hy'⟩)
  have hAb3 : ∀ g ∈ Ab, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hAbcases g hg
    rw [← map_pow]
    have : (⟨y, hBsN hy⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hBel.2 y (hBsB hy))
    rw [this, map_one]
  obtain ⟨m', δ, hm', hδ, φ, ρ, Ω₀, hact, hΩ, hsemi⟩ := halt
  obtain ⟨-, hBsel, hBsc⟩ := hEk
  obtain ⟨A₀, hA₀Bs, hA₀c, hbA₀, c₁, hc₁A₀, hc₁1⟩ := exists_plane_not_mem hBsel hr hBsc hbBs hb1
  have hA₀B : A₀ ≤ B := hA₀Bs.trans hBsB
  have hA₀el : IsElemAbelian 3 A₀ := CFSG.Open.IsElemAbelian.mono hBel hA₀B
  have hA₀p : IsPGroup 3 ↥A₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hA₀el.2 g.1 g.2)⟩
  have hA₀rk : 2 ≤ CFSG.Open.pRank 3 A₀ :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hA₀el (by rw [hA₀c]; norm_num)
  have hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ M := by
    have h1 : Subgroup.normalizer (A₀ : Set G) ≤ GLBCore 3 2 B := le_sSup ⟨A₀, hA₀B, hA₀rk, rfl⟩
    exact h1.trans h.uniq.clause_d
  have hCA₀ : Subgroup.centralizer (A₀ : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans hNA₀
  set H : Subgroup (Equiv.Perm (Fin (m' * 3 ^ r + δ))) := ((autBar 3 A₀ K).subgroupOf Ab).map ρ
    with hH
  have hHmem : ∀ a (ha : a ∈ A₀),
      ρ ⟨barAut 3 K ⟨a, hBsN (hA₀Bs ha)⟩, hmemAb a (hA₀Bs ha)⟩ ∈ H := by
    intro a ha
    refine Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 ?_)
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨ha, hBsN (hA₀Bs ha)⟩)
  have hHcases : ∀ π ∈ H, ∃ g : ↥Ab, (g : MulAut (barOf 3 K)) ∈ autBar 3 A₀ K ∧ ρ g = π := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, Subgroup.mem_subgroupOf.1 hg, rfl⟩
  have hHab : ∀ π ∈ H, ∀ π' ∈ H, π * π' = π' * π := by
    rintro _ ⟨g, -, rfl⟩ _ ⟨g', -, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAbcomm _ g.2 _ g'.2)
  have hH3 : ∀ π ∈ H, π ^ 3 = 1 := by
    rintro _ ⟨g, -, rfl⟩
    rw [← map_pow]
    have : g ^ 3 = 1 := Subtype.ext (by simpa using hAb3 _ g.2)
    rw [this, map_one]
  set bA : ↥Ab := ⟨barAut 3 K ⟨b, hBsN hbBs⟩, hmemAb b hbBs⟩ with hbA
  set β := ρ bA with hβ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : bA ^ 3 = 1 := Subtype.ext (by simpa using hAb3 _ bA.2)
    rw [this, map_one]
  have hβH : ∀ π ∈ H, β * π = π * β := by
    rintro _ ⟨g, -, rfl⟩
    rw [hβ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAbcomm _ bA.2 _ g.2)
  have hβH' : ∀ π ∈ H, β⁻¹ * π = π * β⁻¹ := by
    intro π hπ
    calc β⁻¹ * π = β⁻¹ * (π * β) * β⁻¹ := by group
      _ = β⁻¹ * (β * π) * β⁻¹ := by rw [hβH π hπ]
      _ = π * β⁻¹ := by group
  have hbnot : ∀ g : ↥Ab, (g : MulAut (barOf 3 K)) ∈ autBar 3 A₀ K → g ≠ bA := by
    intro g hg hgb
    obtain ⟨⟨a, haN⟩, ha, hga⟩ := hg
    have haA₀ : a ∈ A₀ := (Subgroup.mem_subgroupOf.1 ha).1
    have hab : a⁻¹ * b ∈ Bs := Bs.mul_mem (Bs.inv_mem (hA₀Bs haA₀)) hbBs
    have h1 : barAut 3 K ⟨a, haN⟩ = barAut 3 K ⟨b, hBsN hbBs⟩ := by
      rw [hga]; exact congrArg Subtype.val hgb
    have h2 : barAut 3 K ⟨a⁻¹ * b, hBsN hab⟩ = 1 := by
      have : (⟨a⁻¹ * b, hBsN hab⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ * ⟨b, hBsN hbBs⟩ := Subtype.ext rfl
      rw [this, map_mul, map_inv, h1, inv_mul_cancel]
    exact hbA₀ ((inv_mul_eq_one.1 (hinjBs _ hab h2)) ▸ haA₀)
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ Ω₀ := by
    by_contra hcon
    push Not at hcon
    have huniv : Ω₀ = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hΩ
    have : 0 < m' * 3 ^ r := Nat.mul_pos hm' (by positivity)
    omega
  set cA : ↥Ab := ⟨barAut 3 K ⟨c₁, hBsN (hA₀Bs hc₁A₀)⟩, hmemAb c₁ (hA₀Bs hc₁A₀)⟩ with hcA
  have hcA1 : cA ≠ 1 := fun h1 => hc₁1 (hinjBs _ (hA₀Bs hc₁A₀) (congrArg Subtype.val h1))
  have hcH : ρ cA ∈ H := hHmem c₁ hc₁A₀
  have hcω : ρ cA ω ≠ ω := hsemi.2 cA hcA1 ω hω
  have hβω : ∀ π ∈ H, π ω ≠ β ω := by
    intro π hπ hπω
    obtain ⟨g, hg, rfl⟩ := hHcases π hπ
    have h1 : ρ (g⁻¹ * bA) ω = ω := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← hβ, ← hπω, ← Equiv.Perm.mul_apply,
        inv_mul_cancel, Equiv.Perm.one_apply]
    by_cases h2 : g⁻¹ * bA = 1
    · exact hbnot g hg (inv_mul_eq_one.1 h2)
    · exact hsemi.2 _ h2 ω hω h1
  have hβω' : ∀ π ∈ H, π ω ≠ β⁻¹ ω := by
    intro π hπ hπω
    obtain ⟨g, hg, rfl⟩ := hHcases π hπ
    have h1 : ρ (bA * g) ω = ω := by
      rw [map_mul, Equiv.Perm.mul_apply, hπω, ← hβ, ← Equiv.Perm.mul_apply, mul_inv_cancel,
        Equiv.Perm.one_apply]
    by_cases h2 : bA * g = 1
    · have hg' : g⁻¹ = bA := (eq_inv_of_mul_eq_one_left h2).symm ▸ inv_inv bA
      exact hbnot g⁻¹ ((autBar 3 A₀ K).inv_mem hg) hg'
    · exact hsemi.2 _ h2 ω hω h1
  obtain ⟨x, hxU, hxne⟩ := exists_mem_orbSubH_comm_ne hHab hcH hβ3 hcω hβω hβω'
  have hU := orbSubH_props hHab hH3
  have hx3 : x ^ 3 = 1 := hU.1 x hxU
  have hxA : x ∈ alternatingGroup (Fin (m' * 3 ^ r + δ)) :=
    Equiv.Perm.mem_alternatingGroup.2 (AltWeakBalance.sign_eq_one_of_pow_prime hp (by norm_num) hx3)
  set ι : barOf 3 K →* Equiv.Perm (Fin (m' * 3 ^ r + δ)) :=
    (alternatingGroup (Fin (m' * 3 ^ r + δ))).subtype.comp φ.toMonoidHom with hι
  have hιi : Function.Injective ι := fun u v huv => φ.injective (Subtype.ext huv)
  have hιact : ∀ (g : ↥Ab) (k : barOf 3 K), ι ((g : MulAut (barOf 3 K)) k) = ρ g * ι k * (ρ g)⁻¹ :=
    fun g k => hact g k
  set xt : barOf 3 K := φ.symm ⟨x, hxA⟩ with hxt
  have hιxt : ι xt = x := by
    show ((φ (φ.symm ⟨x, hxA⟩) : alternatingGroup (Fin _)) : Equiv.Perm _) = x
    rw [MulEquiv.apply_symm_apply]
  set Ut : Subgroup (barOf 3 K) := (orbSubH H).comap ι with hUt
  have hxtU : xt ∈ Ut := by show ι xt ∈ orbSubH H; rw [hιxt]; exact hxU
  have hUtel : IsElemAbelian 3 Ut := by
    refine ⟨⟨⟨fun u v => Subtype.ext (hιi ?_)⟩⟩, fun u hu => hιi ?_⟩
    · show ι ((u : barOf 3 K) * v) = ι ((v : barOf 3 K) * u)
      rw [map_mul, map_mul]
      exact hU.2 _ u.2 _ v.2
    · rw [map_pow, map_one]
      exact hU.1 _ hu
  have hUtfix : ∀ k ∈ Ut, ∀ a (ha : a ∈ A₀), barAut 3 K ⟨a, hBsN (hA₀Bs ha)⟩ k = k := by
    intro k hk a ha
    apply hιi
    have h1 := hιact ⟨_, hmemAb a (hA₀Bs ha)⟩ k
    have h2 := hk.1 _ (hHmem a ha)
    rw [h1, ← h2]
    group
  have hUtb : ∀ k ∈ Ut, barAut 3 K ⟨b, hBsN hbBs⟩ k ∈ Ut := by
    intro k hk
    show ι _ ∈ orbSubH H
    rw [hιact bA k]
    exact conj_mem_orbSubH hβH hk
  have hUtbi : ∀ k ∈ Ut, (barAut 3 K ⟨b, hBsN hbBs⟩)⁻¹ k ∈ Ut := by
    intro k hk
    show ι _ ∈ orbSubH H
    have h1 := hιact bA⁻¹ k
    rw [show ((bA⁻¹ : ↥Ab) : MulAut (barOf 3 K)) = (barAut 3 K ⟨b, hBsN hbBs⟩)⁻¹ from rfl, map_inv,
      ← hβ, inv_inv] at h1
    rw [h1]
    have := conj_mem_orbSubH hβH' hk
    simpa using this
  have hKqM : GLAPPrimeCoreOf 3 K ≤ M :=
    (glaPPrimeCoreOf_le_of_isSubnormal hp hK.2.1).trans (h111 h.toSec11 hdA hd1)
  set Ut' : Subgroup G := (Ut.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))).map K.subtype with hUt'
  have hmemUt' : ∀ z, z ∈ Ut' ↔ ∃ hz : z ∈ K, (QuotientGroup.mk (⟨z, hz⟩ : ↥K) : barOf 3 K) ∈ Ut := by
    intro z
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨⟨z, hz⟩, hz', rfl⟩
  have hUt'M : Ut' ≤ M := by
    intro z hz
    obtain ⟨hzK, hzU⟩ := (hmemUt' z).1 hz
    obtain ⟨v, hvO, hv⟩ := exists_lift_centralizer hA₀p (fun a ha => hBsN (hA₀Bs ha)) ⟨z, hzK⟩
      (fun a ha => hUtfix _ hzU a ha)
    have hzvC : z * v ∈ Subgroup.centralizer (A₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := hv a ha
      calc a * (z * v) = (a * (z * v) * a⁻¹) * a := by group
        _ = (z * v) * a := by rw [this]
    have e : z = (z * v) * v⁻¹ := by group
    rw [e]
    exact M.mul_mem (hCA₀ hzvC) (M.inv_mem (hKqM hvO))
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := hBsN hbBs
  have hbUt' : b ∈ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨hzK, hzU⟩ := (hmemUt' z).1 hz
      have hbz : b * z * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hbK z).1 hzK
      refine (hmemUt' _).2 ⟨hbz, ?_⟩
      have h1 := hUtb _ hzU
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h1
      exact h1
    · intro hz
      obtain ⟨hbzK, hbzU⟩ := (hmemUt' _).1 hz
      have hzK : z ∈ K := (Subgroup.mem_normalizer_iff.1 hbK z).2 hbzK
      refine (hmemUt' z).2 ⟨hzK, ?_⟩
      have h1 := hUtbi _ hbzU
      have h2 : barAut 3 K ⟨b, hBsN hbBs⟩ (QuotientGroup.mk ⟨z, hzK⟩) =
          QuotientGroup.mk ⟨b * z * b⁻¹, hbzK⟩ := by
        rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
        rfl
      rw [← h2, MulAut.inv_apply_self] at h1
      exact h1
  set W : Subgroup G := Ut' ⊔ Subgroup.zpowers b with hW
  have hWM : W ≤ M := sup_le hUt'M ((Subgroup.zpowers_le).2 (hBM hbBL.1))
  have hWN : W ≤ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hbUt')
  have hUt'K : Ut' ≤ K := Subgroup.map_subtype_le _
  have hWK : W ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (hUt'K.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).2 hbK)
  obtain ⟨S0, hS0el, hS0map, -⟩ := exists_elemAbelian_lift (GLAPPrimeCore 3 ↥K)
    ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hUtel
  set R : Subgroup G := S0.map K.subtype with hR
  have hRU : R ≤ Ut' := by
    rintro _ ⟨s, hs, rfl⟩
    refine (hmemUt' _).2 ⟨s.2, ?_⟩
    rw [← hS0map]
    exact ⟨s, hs, rfl⟩
  have hRp : IsPGroup 3 ↥R := by
    have hel := CFSG.SectionRank.isElemAbelian_map hS0el K.subtype
    exact fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hel.2 g.1 g.2)⟩
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers b) := l119_isPGroup_zpowers hb3
  obtain ⟨w, hwW, S, hSp, hSW, hbS, hRS⟩ := exists_conj_le_pGroup' (K := W)
    ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))) hbp
    (hRU.trans le_sup_left) hRp
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective xt
  have hx₁U : (x₁ : G) ∈ Ut' := (hmemUt' _).2 ⟨x₁.2, by rw [hx₁]; exact hxtU⟩
  have hwN := hWN hwW
  have hwK := hWK hwW
  have hwx₁ : w * x₁ * w⁻¹ ∈ Ut' := (Subgroup.mem_normalizer_iff.1 hwN _).1 hx₁U
  obtain ⟨hwx₁K, hwx₁U⟩ := (hmemUt' _).1 hwx₁
  rw [← hS0map] at hwx₁U
  obtain ⟨s, hs, hsx⟩ := hwx₁U
  have hx'K : w⁻¹ * (s : G) * w ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (K : Set G)).inv_mem hwK) _).1 s.2
    simpa using this
  have hx'S : w⁻¹ * (s : G) * w ∈ S := hRS (mem_gLBConj.2 (by
    have : w * (w⁻¹ * (s : G) * w) * w⁻¹ = s := by group
    rw [this]
    exact ⟨s, hs, rfl⟩))
  have hx'img : (QuotientGroup.mk (⟨w⁻¹ * (s : G) * w, hx'K⟩ : ↥K) : barOf 3 K) = xt := by
    have h1 : (QuotientGroup.mk (⟨w⁻¹ * (s : G) * w, hx'K⟩ : ↥K) : barOf 3 K) =
        barAut 3 K ⟨w⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hwK⟩ (QuotientGroup.mk s) := by
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      congr 1
      apply Subtype.ext
      show w⁻¹ * (s : G) * w = w⁻¹ * (s : G) * w⁻¹⁻¹
      rw [inv_inv]
    have h2 : (QuotientGroup.mk s : barOf 3 K) = barAut 3 K ⟨w, hwK⟩ (QuotientGroup.mk x₁) := by
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      exact hsx
    rw [h1, h2, ← MulAut.mul_apply, ← map_mul,
      show (⟨w⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hwK⟩ : ↥(Subgroup.normalizer (K : Set G))) *
        ⟨w, hwK⟩ = 1 from Subtype.ext (inv_mul_cancel w), map_one, MulAut.one_apply, hx₁]
  have hbS' : b ∈ S := hbS (Subgroup.mem_zpowers b)
  have hbN' : b ∈ Lstarsub M L := Lemma136.l136_le_lstar hbBL.2
  have hcc := comm_comm_eq_one hP95 h111 h121 hcomp h133 h (hSW.trans hWM) hSp hx'S hbS' hbN'
  have himg : ∀ (k : G) (hk : k ∈ K), ∃ hk' : ⁅k, b⁆ ∈ K,
      ι (QuotientGroup.mk (⟨⁅k, b⁆, hk'⟩ : ↥K)) = ⁅ι (QuotientGroup.mk (⟨k, hk⟩ : ↥K)), β⁆ := by
    intro k hk
    have hbk : b * k⁻¹ * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hbK _).1 (K.inv_mem hk)
    have hk' : ⁅k, b⁆ ∈ K := by
      rw [commutatorElement_def, show k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) by group]
      exact K.mul_mem hk hbk
    refine ⟨hk', ?_⟩
    have e1 : (⟨⁅k, b⁆, hk'⟩ : ↥K) = ⟨k, hk⟩ * ⟨b * k⁻¹ * b⁻¹, hbk⟩ := by
      apply Subtype.ext
      show ⁅k, b⁆ = k * (b * k⁻¹ * b⁻¹)
      rw [commutatorElement_def]
      group
    have e2 : (QuotientGroup.mk (⟨b * k⁻¹ * b⁻¹, hbk⟩ : ↥K) : barOf 3 K) =
        (barAut 3 K ⟨b, hbK⟩) (QuotientGroup.mk (⟨k, hk⟩ : ↥K))⁻¹ := by
      rw [← QuotientGroup.mk_inv, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      rfl
    rw [e1, QuotientGroup.mk_mul, map_mul, e2]
    have h3 := hιact bA (QuotientGroup.mk (⟨k, hk⟩ : ↥K))⁻¹
    rw [show ((bA : ↥Ab) : MulAut (barOf 3 K)) = barAut 3 K ⟨b, hbK⟩ from rfl] at h3
    rw [h3, ← hβ, map_inv, commutatorElement_def]
    group
  obtain ⟨hk₁, hk₁img⟩ := himg _ hx'K
  rw [hx'img, hιxt] at hk₁img
  obtain ⟨hk₂, hk₂img⟩ := himg _ hk₁
  rw [hk₁img] at hk₂img
  apply hxne
  rw [← hk₂img]
  have : (⟨⁅⁅w⁻¹ * (s : G) * w, b⁆, b⁆, hk₂⟩ : ↥K) = 1 := Subtype.ext hcc
  rw [this, QuotientGroup.mk_one, map_one]

end CaseB

section MainCases

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf)

@[expose] def IIHardCaseAltMain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
    ∀ (b : G) (B1 : Subgroup G), Lemma136c.IIHardPrinted B L D hN hd b B1 →
    Lemma136c.IIHardSetupData B L D d (Lemma136c.bStarOf B L D b) (Lemma136c.s1Of B L D d b B1) →
    ∀ (r : ℕ), 2 ≤ r → IsEkIn 3 r (Cg d) (Lemma136c.bStarOf B L D b) →
    ∀ (K : Subgroup G), GLAPComponent 3 (Cg d) K →
      ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) →
      Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (K : Set G) →
      centBar 3 (Lemma136c.bStarOf B L D b) K = ⊥ →
      ¬ IsCompLocallyOTwoBalanced 3 r (Lemma136c.bStarOf B L D b) K →
      ¬ Lemma129.Alt1916 3 r (autBar 3 (Lemma136c.bStarOf B L D b) K)

@[expose] def IIHardCaseAltMainTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
    ∀ (b : G) (B1 : Subgroup G), Lemma136c.IIHardPrinted B L D hN hd b B1 →
    Lemma136c.IIHardSetupData B L D d (Lemma136c.bStarOf B L D b) (Lemma136c.s1Of B L D d b B1) →
    IsEkIn 3 2 (Cg d) (Lemma136c.bStarOf B L D b) →
    ∀ (K : Subgroup G), GLAPComponent 3 (Cg d) K →
      ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) →
      Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (K : Set G) →
      centBar 3 (Lemma136c.bStarOf B L D b) K = ⊥ →
      ¬ IsCompLocallyOTwoBalanced 3 2 (Lemma136c.bStarOf B L D b) K →
      ¬ Lemma129.Alt1916 3 2 (autBar 3 (Lemma136c.bStarOf B L D b) K)

theorem iiHardCaseAltMain_of_two (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    (hTwo : IIHardCaseAltMainTwo) : IIHardCaseAltMain := by
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix b B1 hP hS r hr hEk K hK hnot hBsN hcent hnb halt
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact hTwo G m h hN hd hd1 hfix b B1 hP hS hEk K hK hnot hBsN hcent hnb halt
  · exact altMain_three_false hP95 h111 h121 hcomp h133 h hN hd hd1 hfix hP hr3 hEk hK hBsN hcent halt

@[expose] def IIHardCaseLieMain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
    ∀ (b : G) (B1 : Subgroup G), Lemma136c.IIHardPrinted B L D hN hd b B1 →
    Lemma136c.IIHardSetupData B L D d (Lemma136c.bStarOf B L D b) (Lemma136c.s1Of B L D d b B1) →
    ∀ (r : ℕ), 2 ≤ r → IsEkIn 3 r (Cg d) (Lemma136c.bStarOf B L D b) →
    ∀ (K : Subgroup G), GLAPComponent 3 (Cg d) K →
      ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) →
      Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (K : Set G) →
      centBar 3 (Lemma136c.bStarOf B L D b) K = ⊥ →
      ¬ IsCompLocallyOTwoBalanced 3 r (Lemma136c.bStarOf B L D b) K →
      ¬ Lemma129.Lie1916 3 r (autBar 3 (Lemma136c.bStarOf B L D b) K)

theorem iiHard_of_main (hI191 : Lemma129.Input19_1_two) (hI1916 : Lemma129.Input19_16Main)
    (hRed : Lemma136c.IIHardReduction) (hAlt : IIHardCaseAltMain) (hLie : IIHardCaseLieMain) :
    Lemma136.IIHardInput := by
  have hF := Claims136.centralizerFStarFact_holds
  have hI191' := Claims136.input19_1_O2_of_input19_1_two hI191
  unfold Lemma136c.IIHardReduction at hRed
  unfold Lemma136c.CentralizerFStarFact at hF
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix
  haveI : IsSimpleGroup G := h.standing.simple
  obtain ⟨b, B1, hPD, hsetup⟩ := hRed G m h hN hd hd1 hfix
  have hs := hsetup
  obtain ⟨-, ⟨r, hr, hEk⟩, hS1Δ, hS1P, hS1C, hred⟩ := hsetup
  have hX : Cg d ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top h.standing.nonabelian hd1
  have hI := hI191' G h.standing.kProper 3 Nat.prime_three (by norm_num) r (by omega) (Cg d)
    (Lemma136c.bStarOf B L D b) hX hEk
  have hS1O : Lemma136c.s1Of B L D d b B1 ≤ GLAPPrimeCoreOf 3 (Cg d) := by
    by_contra hne
    obtain ⟨K, hK, hnot⟩ : ∃ K : Subgroup G, GLAPComponent 3 (Cg d) K ∧
        ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) := by
      by_contra hall
      push Not at hall
      exact hne (hF G (Cg d) (Lemma136c.s1Of B L D d b B1) hS1C hS1P
        (fun K hK => hS1Δ.trans (hI.1 K hK))
        (fun y hy z hz => hI.2.1 y (hS1Δ hy) z hz) hall)
    have hnotΔ : ¬ ⁅K, localDeltaTwoIn (Cg d) (Lemma136c.bStarOf B L D b)⁆ ≤
        GLAPPrimeCoreOf 3 (Cg d) :=
      fun hle => hnot ((Subgroup.commutator_mono le_rfl hS1Δ).trans hle)
    obtain ⟨hBsN, hcent, hnb⟩ := hI.2.2 K hK hnotΔ
    have hKtop : K ≠ ⊤ := fun htop => hX (top_le_iff.1 (htop ▸ hK.1))
    have hKG : CFSG.Open.IsKGroup (barOf 3 K) :=
      (CFSG.Open.IsKProper.isKGroup h.standing.kProper K hKtop).quotient (GLAPPrimeCore 3 ↥K)
    haveI : Finite (barOf 3 K) := by unfold barOf; infer_instance
    have hq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quot_of_component Nat.prime_three hK
    have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
    obtain ⟨-, hel, hcard⟩ := Lemma136c.l136c_isEkIn_autBar hEk hBsN hcent
    rcases hI1916 3 r Nat.prime_three (by norm_num) hr (barOf 3 K) hKG hq hO _ hel hcard with
      hb | ha | hs5 | hc
    · exact hnb hb
    · exact hAlt G m h hN hd hd1 hfix b B1 hPD hs r hr hEk K hK hnot hBsN hcent hnb ha
    · exact absurd hs5.1 (by norm_num)
    · exact hLie G m h hN hd hd1 hfix b B1 hPD hs r hr hEk K hK hnot hBsN hcent hnb hc
  exact hred.trans (sup_le hS1O le_rfl)

end MainCases

theorem lemma136_of_main (hI191 : Lemma129.Input19_1_two) (hI1916 : Lemma129.Input19_16Main)
    (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement)
    (h133 : Lemma133Statement) (h135 : Lemma135_iStatement) (h91 : Lemma91ii)
    (h912 : Lemma912Statement) (hI183 : Prop115.Input18_3Gen) (hPump : Input14_15A7)
    (hAC : Prop126b.InputAltCentre) (hAltTwo : IIHardCaseAltMainTwo) (hLie : IIHardCaseLieMain) :
    Lemma136Statement :=
  lemma136_of_inputs hP95 h111 h121 hcomp input22_3_2_holds
    (Claims136.p1BarInput_of_inputs' h135 h912 hO2 hP95 h111 h121 hcomp
      (p1GCore_of_inputs hP95 h111 h121 hcomp h133 hI183 hPump hAC)) hO2 h121c
    (iiHard_of_main hI191 hI1916
      (Claims136.iiHardReduction_of_inputs hP95 h111 h121 hcomp hO2 h121c h133 h135 h91 h912)
      (iiHardCaseAltMain_of_two hP95 h111 h121 hcomp h133 hAltTwo) hLie)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136b

end
