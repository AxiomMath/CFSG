module

public import CFSG.LocalAnalysis.OddStandard.Harada75Aut

public section

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

@[expose] def invMap (E : Subgroup S) (a : S) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEa : ∀ x ∈ E, a * x * a⁻¹ ∈ E) : E →* E where
  toFun x := ⟨x.1 * (a * x.1 * a⁻¹), E.mul_mem x.2 (hEa _ x.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    show x.1 * y.1 * (a * (x.1 * y.1) * a⁻¹) =
      x.1 * (a * x.1 * a⁻¹) * (y.1 * (a * y.1 * a⁻¹))
    have hc : y.1 * (a * x.1 * a⁻¹) = (a * x.1 * a⁻¹) * y.1 := hEc _ y.2 _ (hEa _ x.2)
    have e1 : a * (x.1 * y.1) * a⁻¹ = (a * x.1 * a⁻¹) * (a * y.1 * a⁻¹) := by group
    rw [e1]
    calc x.1 * y.1 * ((a * x.1 * a⁻¹) * (a * y.1 * a⁻¹))
        = x.1 * (y.1 * (a * x.1 * a⁻¹)) * (a * y.1 * a⁻¹) := by group
      _ = x.1 * ((a * x.1 * a⁻¹) * y.1) * (a * y.1 * a⁻¹) := by rw [hc]
      _ = x.1 * (a * x.1 * a⁻¹) * (y.1 * (a * y.1 * a⁻¹)) := by group


theorem mem_ker_invMap (E : Subgroup S) (a : S) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) (hEa : ∀ x ∈ E, a * x * a⁻¹ ∈ E) (x : E) :
    x ∈ (invMap E a hEc hEa).ker ↔ a * x.1 = x.1 * a := by
  rw [MonoidHom.mem_ker]
  have h1 : (invMap E a hEc hEa x) = 1 ↔ x.1 * (a * x.1 * a⁻¹) = 1 := by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [h1]
  have hxi : x.1⁻¹ = x.1 := (inv_eq_of_mul_eq_one_right (hE2 _ x.2)).symm ▸ rfl
  constructor
  · intro h
    have h2 : a * x.1 * a⁻¹ = x.1⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hxi] at h2
    calc a * x.1 = a * x.1 * a⁻¹ * a := by group
      _ = x.1 * a := by rw [h2]
  · intro h
    have h2 : a * x.1 * a⁻¹ = x.1 := by
      calc a * x.1 * a⁻¹ = x.1 * a * a⁻¹ := by rw [h]
        _ = x.1 := by group
    rw [h2]
    exact hE2 _ x.2

theorem range_invMap_le_ker (E : Subgroup S) (a : S) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) (ha2 : a * a = 1) (hEa : ∀ x ∈ E, a * x * a⁻¹ ∈ E) :
    (invMap E a hEc hEa).range ≤ (invMap E a hEc hEa).ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  show (x.1 * (a * x.1 * a⁻¹)) * (a * (x.1 * (a * x.1 * a⁻¹)) * a⁻¹) = 1
  have hxx' := hE2 _ (hEa _ x.2)
  have e1 : a * (x.1 * (a * x.1 * a⁻¹)) * a⁻¹ = (a * x.1 * a⁻¹) * x.1 := by
    have : a * a = 1 := ha2
    calc a * (x.1 * (a * x.1 * a⁻¹)) * a⁻¹ = (a * x.1 * a⁻¹) * (a * a * x.1 * (a * a)⁻¹) := by
          group
      _ = (a * x.1 * a⁻¹) * x.1 := by rw [this]; group
  rw [e1]
  have hx2 := hE2 _ x.2
  calc x.1 * (a * x.1 * a⁻¹) * ((a * x.1 * a⁻¹) * x.1)
      = x.1 * ((a * x.1 * a⁻¹) * (a * x.1 * a⁻¹)) * x.1 := by group
    _ = x.1 * x.1 := by rw [hxx', mul_one]
    _ = 1 := hx2

theorem card_centralizer_involution [Finite S] {E : Subgroup S} {a : S}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hE8 : Nat.card E = 8) (hEa : ∀ x ∈ E, a * x * a⁻¹ ∈ E) (ha2 : a * a = 1)
    (hna : ∃ x ∈ E, a * x ≠ x * a) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set S)) = 4 := by
  have h1 := Subgroup.card_ker_mul_card_range (invMap E a hEc hEa)
  have h2 := Subgroup.card_le_of_le (range_invMap_le_ker E a hEc hE2 ha2 hEa)
  have hker : Nat.card (invMap E a hEc hEa).ker =
      Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set S)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
          ((mem_ker_invMap E a hEc hE2 hEa x.1).mp x.2).symm⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, (mem_ker_invMap E a hEc hE2 hEa ⟨x.1, x.2.1⟩).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [hE8] at h1
  have hr : 0 < Nat.card (invMap E a hEc hEa).range := Nat.card_pos
  have hk : 0 < Nat.card (invMap E a hEc hEa).ker := Nat.card_pos
  have hr2 : Nat.card (invMap E a hEc hEa).range ≤ 2 := by nlinarith
  have hk8 : Nat.card (invMap E a hEc hEa).ker ≠ 8 := by
    intro h8
    have htop : (invMap E a hEc hEa).ker = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h8, hE8])
    obtain ⟨x, hx, hxa⟩ := hna
    apply hxa
    have := (mem_ker_invMap E a hEc hE2 hEa ⟨x, hx⟩).mp (by rw [htop]; exact Subgroup.mem_top _)
    exact this
  rw [← hker]
  interval_cases (Nat.card (invMap E a hEc hEa).range) <;> omega


theorem inv_mul_mem_of_card [Finite S] {H K : Subgroup S} (hHK : H ≤ K)
    (hcard : Nat.card K = 2 * Nat.card H) {x y : S} (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H)
    (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_eq_left.mpr hHK, hcard] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h2 : H.relIndex K = 2 := by
    have : H.relIndex K * Nat.card H = 2 * Nat.card H := h1
    exact Nat.eq_of_mul_eq_mul_right hpos this
  obtain ⟨a, ha, hall⟩ := Subgroup.relIndex_eq_two_iff'.mp h2
  have hax : a * x ∈ H := by
    rcases hall x hx with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxH
  have hay : a * y ∈ H := by
    rcases hall y hy with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hyH
  have := H.mul_mem (H.inv_mem hax) hay
  simpa [mul_assoc] using this


theorem exists_mem_normalizer_not_mem [Finite S] (hS : IsPGroup 2 S) {W C : Subgroup S}
    (hWC : W ≤ C) (hne : W ≠ C) :
    ∃ t ∈ C, t ∉ W ∧ ∀ w ∈ C, (w ∈ W ↔ t * w * t⁻¹ ∈ W) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent C := (hS.to_subgroup C).isNilpotent
  have hnc : NormalizerCondition C := Group.normalizerCondition_of_isNilpotent
  let W' : Subgroup C := W.subgroupOf C
  have hW' : W' ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hWC fun x hx => ?_
    have : (⟨x, hx⟩ : C) ∈ W' := by rw [h]; trivial
    exact this
  have hnot : Subgroup.normalizer (W' : Set C) ≠ W' := fun h =>
    hW' ((normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ h)
  obtain ⟨t', ht'N, ht'W⟩ : ∃ t' ∈ Subgroup.normalizer (W' : Set C), t' ∉ W' := by
    by_contra hall
    push Not at hall
    exact hnot (le_antisymm (fun x hx => hall x hx) Subgroup.le_normalizer)
  refine ⟨t'.1, t'.2, ht'W, fun w hw => ?_⟩
  exact Subgroup.mem_normalizer_iff.mp ht'N ⟨w, hw⟩

structure Cfg (S : Type) [Group S] (A E : Subgroup S) : Prop where
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A_sq : ∀ a ∈ A, a * a = 1
  A_card : Nat.card A = 8
  A_cent : ∀ x : S, (∀ a ∈ A, x * a = a * x) → x ∈ A
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  E_sq : ∀ a ∈ E, a * a = 1
  E_card : Nat.card E = 8
  E_norm : ∀ s : S, ∀ e ∈ E, s * e * s⁻¹ ∈ E

namespace Cfg

variable {A E : Subgroup S} (h : Cfg S A E)

include h in
theorem E_normal : E.Normal := ⟨fun n hn g => h.E_norm g n hn⟩

include h in
theorem E_inv {e : S} (he : e ∈ E) : e⁻¹ = e := inv_eq_of_mul_eq_one_right (h.E_sq e he)

include h in
theorem A_inv {a : S} (ha : a ∈ A) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.A_sq a ha)

include h in
theorem centralizer_eq : Subgroup.centralizer (A : Set S) = A := by
  apply le_antisymm
  · intro x hx
    refine h.A_cent x fun a ha => ?_
    exact (Subgroup.mem_centralizer_iff.mp hx a ha).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.A_comm a ha x hx

include h in
theorem exists_z [Finite S] (hS : IsPGroup 2 S) :
    ∃ z ∈ E, z ≠ 1 ∧ (∀ s : S, s * z = z * s) := by
  have := h.E_normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hEne : E ≠ ⊥ := by
    intro h'
    have := h.E_card
    rw [h', Subgroup.card_bot] at this
    omega
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hEne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨z.1, z.2.1, fun h1 => hz1 (Subtype.ext h1), fun s => ?_⟩
  exact (Subgroup.mem_center_iff.mp z.2.2 s)


include h in
theorem caseI_cent_iff [Finite S] (hcard : Nat.card ↥(A ⊓ E) = 4) {a : S} (ha : a ∈ A)
    (haE : a ∉ E) {x : S} (hx : x ∈ E) : a * x = x * a ↔ x ∈ A := by
  constructor
  · intro hax
    apply h.A_cent
    intro a' ha'
    by_cases ha'E : a' ∈ E
    · exact h.E_comm x hx a' ha'E
    · have hmem : a⁻¹ * a' ∈ A ⊓ E :=
        inv_mul_mem_of_card (H := A ⊓ E) (K := A) inf_le_left (by rw [h.A_card, hcard])
          ha ha' (fun h' => haE h'.2) (fun h' => ha'E h'.2)
      obtain ⟨e, he, rfl⟩ : ∃ e ∈ E, a' = a * e := ⟨a⁻¹ * a', hmem.2, by group⟩
      calc x * (a * e) = (x * a) * e := by group
        _ = (a * x) * e := by rw [← hax]
        _ = a * (x * e) := by group
        _ = a * (e * x) := by rw [h.E_comm x hx e he]
        _ = a * e * x := by group
  · intro hxA
    exact h.A_comm a ha x hxA

include h in
theorem caseI_noncomm [Finite S] (hcard : Nat.card ↥(A ⊓ E) = 4) {a : S} (ha : a ∈ A)
    (haE : a ∉ E) : ∃ x ∈ E, a * x ≠ x * a := by
  by_contra hno
  push Not at hno
  have hEA : E ≤ A := fun x hx => (h.caseI_cent_iff hcard ha haE hx).mp (hno x hx)
  have : A ⊓ E = E := inf_eq_right.mpr hEA
  rw [this, h.E_card] at hcard
  omega

include h in
theorem caseI_comm_mem [Finite S] (hcard : Nat.card ↥(A ⊓ E) = 4) {a x : S} (ha : a ∈ A)
    (hx : x ∈ E) : x * a * x⁻¹ * a⁻¹ ∈ A ⊓ E := by
  by_cases haE : a ∈ E
  · have h1 : x * a = a * x := h.E_comm x hx a haE
    have h2 : x * a * x⁻¹ * a⁻¹ = 1 := by rw [h1]; group
    rw [h2]
    exact (A ⊓ E).one_mem
  · have hai : a⁻¹ = a := h.A_inv ha
    have hxi : x⁻¹ = x := h.E_inv hx
    have hy : a * x * a ∈ E := by
      have := h.E_norm a x hx
      rwa [hai] at this
    have hcE : x * a * x⁻¹ * a⁻¹ ∈ E := by
      rw [hai, hxi]
      have := E.mul_mem hx hy
      have e : x * (a * x * a) = x * a * x * a := by group
      rwa [e] at this
    have hcomm : a * (x * a * x⁻¹ * a⁻¹) = (x * a * x⁻¹ * a⁻¹) * a := by
      rw [hai, hxi]
      have h1 := h.E_comm _ hy x hx
      calc a * (x * a * x * a) = (a * x * a * x) * a := by group
        _ = (x * (a * x * a)) * a := by rw [h1]
        _ = (x * a * x * a) * a := by group
    exact ⟨(h.caseI_cent_iff hcard ha haE hcE).mp hcomm, hcE⟩

include h in
theorem caseI_E_le_normalizer [Finite S] (hcard : Nat.card ↥(A ⊓ E) = 4) :
    E ≤ Subgroup.normalizer (A : Set S) := by
  have key : ∀ x ∈ E, ∀ g ∈ A, x * g * x⁻¹ ∈ A := by
    intro x hx g hg
    have h1 := (h.caseI_comm_mem hcard hg hx).1
    have e : x * g * x⁻¹ = (x * g * x⁻¹ * g⁻¹) * g := by group
    rw [e]
    exact A.mul_mem h1 hg
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key x hx g hg, fun hg => ?_⟩
  have h1 := key x⁻¹ (E.inv_mem hx) _ hg
  have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
  rwa [e] at h1

include h in
theorem caseI_mem_normalizer [Finite S] (hcard : Nat.card ↥(A ⊓ E) = 4) {a : S} (ha : a ∈ A)
    (haE : a ∉ E) {x : S} (hx : x * a * x⁻¹ * a⁻¹ ∈ E) :
    x ∈ Subgroup.normalizer (A : Set S) := by
  have key : ∀ x : S, x * a * x⁻¹ * a⁻¹ ∈ E → ∀ g ∈ A, x * g * x⁻¹ ∈ A := by
    intro x hx g hg
    obtain ⟨e, he_def⟩ : ∃ e, e = x * a * x⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have heE : e ∈ E := by rw [he_def]; exact hx
    have hxa : x * a * x⁻¹ = e * a := by rw [he_def]; group
    have hsq : (e * a) * (e * a) = 1 := by
      calc (e * a) * (e * a) = (x * a * x⁻¹) * (x * a * x⁻¹) := by rw [hxa]
        _ = x * (a * a) * x⁻¹ := by group
        _ = 1 := by rw [h.A_sq a ha]; group
    have hea : a * e = e * a := by
      have h1 : e * (a * e * a) = 1 := by
        calc e * (a * e * a) = (e * a) * (e * a) := by group
          _ = 1 := hsq
      have h2 : a * e * a = e⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h.E_inv heE] at h2
      calc a * e = a * e * a * a := by rw [mul_assoc (a * e) a a, h.A_sq a ha, mul_one]
        _ = e * a := by rw [h2]
    have heA : e ∈ A := (h.caseI_cent_iff hcard ha haE heE).mp hea
    have hE : ∀ g ∈ A ⊓ E, x * g * x⁻¹ ∈ A := by
      intro g hg
      have hyE : x * g * x⁻¹ ∈ E := h.E_norm x g hg.2
      have hga : g * a = a * g := h.A_comm g hg.1 a ha
      have hcomm1 : (x * g * x⁻¹) * (e * a) = (e * a) * (x * g * x⁻¹) := by
        rw [← hxa]
        calc x * g * x⁻¹ * (x * a * x⁻¹) = x * (g * a) * x⁻¹ := by group
          _ = x * (a * g) * x⁻¹ := by rw [hga]
          _ = x * a * x⁻¹ * (x * g * x⁻¹) := by group
      have hcomm2 : a * (x * g * x⁻¹) = (x * g * x⁻¹) * a := by
        have hye : (x * g * x⁻¹) * e = e * (x * g * x⁻¹) := h.E_comm _ hyE e heE
        have h3 : e * ((x * g * x⁻¹) * a) = e * (a * (x * g * x⁻¹)) := by
          calc e * ((x * g * x⁻¹) * a) = (e * (x * g * x⁻¹)) * a := by group
            _ = ((x * g * x⁻¹) * e) * a := by rw [hye]
            _ = (x * g * x⁻¹) * (e * a) := by group
            _ = (e * a) * (x * g * x⁻¹) := hcomm1
            _ = e * (a * (x * g * x⁻¹)) := by group
        exact (mul_left_cancel h3).symm
      exact (h.caseI_cent_iff hcard ha haE hyE).mp hcomm2
    by_cases hgE : g ∈ E
    · exact hE g ⟨hg, hgE⟩
    · have hmem : a⁻¹ * g ∈ A ⊓ E :=
        inv_mul_mem_of_card (H := A ⊓ E) (K := A) inf_le_left (by rw [h.A_card, hcard])
          ha hg (fun h' => haE h'.2) (fun h' => hgE h'.2)
      have hconj := hE _ hmem
      have e1 : x * g * x⁻¹ = (x * a * x⁻¹) * (x * (a⁻¹ * g) * x⁻¹) := by group
      rw [e1, hxa]
      exact A.mul_mem (A.mul_mem heA ha) hconj
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key x hx g hg, fun hg => ?_⟩
  have hx' : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ ∈ E := by
    have := h.E_norm x⁻¹ (x * a * x⁻¹ * a⁻¹)⁻¹ (E.inv_mem hx)
    have e : x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x⁻¹⁻¹ = x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ := by group
    rwa [e] at this
  have h1 := key x⁻¹ hx' _ hg
  have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
  rwa [e] at h1

include h in
theorem card_normalizer_le [Finite S] (hS : IsPGroup 2 S) :
    Nat.card ↥(Subgroup.normalizer (A : Set S)) ≤ 64 := by
  have hX : IsPGroup 2 (Subgroup.normalizer (A : Set S)) := hS.to_subgroup _
  have hXA : ∀ x ∈ Subgroup.normalizer (A : Set S), ∀ a ∈ A, x * a * x⁻¹ ∈ A :=
    fun x hx a ha => (Subgroup.mem_normalizer_iff.mp hx a).mp ha
  have h1 := card_le_eight_mul_card_inf_centralizer h.A_comm
    (fun a ha => by rw [pow_two]; exact h.A_sq a ha) h.A_card hX hXA
  rw [h.centralizer_eq] at h1
  have h2 : Nat.card ↥(Subgroup.normalizer (A : Set S) ⊓ A) ≤ 8 := by
    have := Subgroup.card_le_of_le (inf_le_right : Subgroup.normalizer (A : Set S) ⊓ A ≤ A)
    rwa [h.A_card] at this
  omega

end Cfg

end CFSG.OddStandard.Harada75
