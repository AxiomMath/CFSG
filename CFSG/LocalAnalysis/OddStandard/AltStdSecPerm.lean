module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section Cyc

variable {α : Type*} [DecidableEq α]

@[expose] def cyc3 (x y z : α) : Perm α := swap x y * swap y z

theorem cyc3_apply_left {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) : cyc3 x y z x = y := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]; grind

theorem cyc3_apply_mid {x y z : α} (hyz : y ≠ z) (hxz : x ≠ z) : cyc3 x y z y = z := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]; grind

theorem cyc3_apply_right (x y z : α) : cyc3 x y z z = x := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]; grind

theorem cyc3_apply_of_ne {x y z w : α} (hx : w ≠ x) (hy : w ≠ y) (hz : w ≠ z) :
    cyc3 x y z w = w := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]; grind

theorem cyc3_apply_ne_iff {x y z : α} (w : α) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    cyc3 x y z w ≠ w ↔ w = x ∨ w = y ∨ w = z := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]
  grind

end Cyc

section Comm

variable {α : Type*}

theorem comm_apply_ne_iff {σ c : Perm α} (h : σ * c = c * σ) (w : α) :
    c (σ w) ≠ σ w ↔ c w ≠ w := by
  have h1 : σ (c w) = c (σ w) := by
    have := congrArg (fun f : Perm α => f w) h
    simpa using this
  rw [← h1, Ne, Ne, σ.injective.eq_iff]

end Comm

section F2

variable {α : Type*} [DecidableEq α]

theorem fixes_of_comm_cyc3 {S : Finset α} (hS : 4 ≤ S.card) {σ : Perm α}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
      σ * cyc3 x y z = cyc3 x y z * σ) : ∀ i ∈ S, σ i = i := by
  intro i hi
  have hcard : 2 < (S.erase i).card := by
    rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j, l, m, hj, hl, hm, hjl, hjm, hlm⟩ := Finset.two_lt_card_iff.1 hcard
  rw [Finset.mem_erase] at hj hl hm
  have key : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
      σ x = x ∨ σ x = y ∨ σ x = z := by
    intro x hx y hy z hz hxy hyz hxz
    by_contra hcon
    push Not at hcon
    have h1 := (comm_apply_ne_iff (h x hx y hy z hz hxy hyz hxz) x).2
      (by rw [cyc3_apply_left hxy hxz]; exact Ne.symm hxy)
    have : σ x = x ∨ σ x = y ∨ σ x = z :=
      (cyc3_apply_ne_iff (σ x) hxy hyz hxz).1 h1
    grind
  have h1 := key i hi j hj.2 l hl.2 (Ne.symm hj.1) hjl (Ne.symm hl.1)
  have h2 := key i hi j hj.2 m hm.2 (Ne.symm hj.1) hjm (Ne.symm hm.1)
  have h3 := key i hi l hl.2 m hm.2 (Ne.symm hl.1) hlm (Ne.symm hm.1)
  grind

end F2

section Alt

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_cyc3 {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) : Perm.sign (cyc3 x y z) = 1 := by
  simp [cyc3, Perm.sign_mul, Perm.sign_swap hxy, Perm.sign_swap hyz]

theorem mem_alt_cyc3 {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) :
    cyc3 x y z ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup]; exact sign_cyc3 hxy hyz

@[expose] def altSub (S : Finset α) : Subgroup (Perm α) :=
  (alternatingGroup.ofSubtype S).range.map (alternatingGroup α).subtype

theorem mem_altSub {S : Finset α} {g : Perm α} :
    g ∈ altSub S ↔ Perm.sign g = 1 ∧ ∀ i, i ∉ S → g i = i := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hsupp := (alternatingGroup.mem_range_ofSubtype_iff S k).1 hk
    refine ⟨Perm.mem_alternatingGroup.1 k.2, fun i hi => ?_⟩
    by_contra hne
    exact hi (hsupp (Perm.mem_support.2 hne))
  · rintro ⟨hs, hfix⟩
    refine ⟨⟨g, Perm.mem_alternatingGroup.2 hs⟩, ?_, rfl⟩
    refine (alternatingGroup.mem_range_ofSubtype_iff S _).2 ?_
    intro i hi
    by_contra hiS
    exact (Perm.mem_support.1 hi) (hfix i hiS)

theorem altSub_le_alternatingGroup (S : Finset α) : altSub S ≤ alternatingGroup α := by
  intro g hg
  exact Perm.mem_alternatingGroup.2 (mem_altSub.1 hg).1

theorem cyc3_mem_altSub {S : Finset α} {x y z : α} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : cyc3 x y z ∈ altSub S := by
  refine mem_altSub.2 ⟨sign_cyc3 hxy hyz, fun i hi => cyc3_apply_of_ne ?_ ?_ ?_⟩
  · rintro rfl; exact hi hx
  · rintro rfl; exact hi hy
  · rintro rfl; exact hi hz

noncomputable def altSubEquiv (S : Finset α) : altSub S ≃* alternatingGroup (Fin S.card) :=
  (((Equiv.altCongrHom S.equivFin.symm).trans
    ((MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := S))).trans
      (Subgroup.equivMapOfInjective _ _ (alternatingGroup α).subtype_injective))).symm)

theorem comm_of_altSub_disjoint {S T : Finset α} (hST : Disjoint S T) {g h : Perm α}
    (hg : g ∈ altSub S) (hh : h ∈ altSub T) : g * h = h * g := by
  have hg' := (mem_altSub.1 hg).2
  have hh' := (mem_altSub.1 hh).2
  refine Perm.Disjoint.commute (fun x => ?_)
  by_cases hx : x ∈ S
  · right
    exact hh' x (Finset.disjoint_left.1 hST hx)
  · left
    exact hg' x hx

theorem mem_centralizer_altSub_iff {S : Finset α} (hS : 4 ≤ S.card) {σ : Perm α} :
    σ ∈ centralizer ((altSub S : Subgroup (Perm α)) : Set (Perm α)) ↔ ∀ i ∈ S, σ i = i := by
  constructor
  · intro hσ
    refine fixes_of_comm_cyc3 hS fun x hx y hy z hz hxy hyz hxz => ?_
    exact (mem_centralizer_iff.1 hσ _ (cyc3_mem_altSub hx hy hz hxy hyz hxz)).symm
  · intro hσ
    rw [mem_centralizer_iff]
    intro g hg
    have hg' := (mem_altSub.1 hg).2
    refine (Perm.Disjoint.commute (fun x => ?_))
    by_cases hx : x ∈ S
    · exact Or.inr (hσ x hx)
    · exact Or.inl (hg' x hx)

theorem centralizer_altSub_inf_alt {S : Finset α} (hS : 4 ≤ S.card) :
    centralizer ((altSub S : Subgroup (Perm α)) : Set (Perm α)) ⊓ alternatingGroup α =
      altSub Sᶜ := by
  ext σ
  rw [Subgroup.mem_inf, mem_centralizer_altSub_iff hS, mem_altSub, Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun i hi => h1 i ?_⟩
    simpa using hi
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h2 i (by simpa using hi), h1⟩

theorem mem_normalizer_altSub {T : Finset α} {σ : Perm α} (hσ : ∀ i, i ∈ T ↔ σ i ∈ T) :
    σ ∈ normalizer ((altSub T : Subgroup (Perm α)) : Set (Perm α)) := by
  have key : ∀ τ : Perm α, (∀ i, i ∈ T ↔ τ i ∈ T) → ∀ g ∈ altSub T, τ * g * τ⁻¹ ∈ altSub T := by
    intro τ hτ g hg
    obtain ⟨hs, hfix⟩ := mem_altSub.1 hg
    refine mem_altSub.2 ⟨by simp [hs], fun i hi => ?_⟩
    have hi' : τ⁻¹ i ∉ T := by
      intro hT
      apply hi
      have := (hτ (τ⁻¹ i)).1 hT
      simpa using this
    show τ (g (τ⁻¹ i)) = i
    rw [hfix _ hi']
    simp
  have hinv : ∀ i, i ∈ T ↔ σ⁻¹ i ∈ T := fun i =>
    (by simpa using hσ (σ⁻¹ i) : σ⁻¹ i ∈ T ↔ i ∈ T).symm
  rw [mem_normalizer_iff]
  intro g
  refine ⟨key σ hσ g, fun hg => ?_⟩
  have := key σ⁻¹ hinv _ hg
  simpa [mul_assoc] using this


theorem altSub_comm_of_card_three {S : Finset α} (hS : S.card = 3) {g h : Perm α}
    (hg : g ∈ altSub S) (hh : h ∈ altSub S) : g * h = h * g := by
  have hc : IsMulCommutative (alternatingGroup (Fin S.card)) :=
    alternatingGroup.isMulCommutative_of_card_le_three (by simp [hS])
  have h1 : (altSubEquiv S) (⟨g, hg⟩ * ⟨h, hh⟩) = (altSubEquiv S) (⟨h, hh⟩ * ⟨g, hg⟩) := by
    rw [map_mul, map_mul]
    exact hc.is_comm.comm _ _
  have h2 := (altSubEquiv S).injective h1
  exact congrArg Subtype.val h2

theorem card_altSub_of_card_three {S : Finset α} (hS : S.card = 3) : Nat.card (altSub S) = 3 := by
  have h := Nat.card_congr (altSubEquiv S).toEquiv
  have : Nontrivial (Fin S.card) := by
    rw [hS]; infer_instance
  rw [h, nat_card_alternatingGroup]
  simp [hS, Nat.factorial]

theorem mem_altSub_of_card_three {S : Finset α} (hS : S.card = 3) {σ : Perm α}
    (hfix : ∀ i, i ∉ S → σ i = i)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
      σ * cyc3 x y z = cyc3 x y z * σ) : σ ∈ altSub S := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hS
  have hmem : ∀ x ∈ ({a, b, c} : Finset α), x = a ∨ x = b ∨ x = c := by simp
  have hσ := hcomm a (by simp) b (by simp) c (by simp) hab hbc hac
  set κ := cyc3 a b c with hκ
  have hκa : κ a = b := cyc3_apply_left hab hac
  have hκb : κ b = c := cyc3_apply_mid hbc hac
  have hκc : κ c = a := cyc3_apply_right a b c
  have hcomm' : ∀ w, σ (κ w) = κ (σ w) := fun w => by
    have := congrArg (fun f : Perm α => f w) hσ
    simpa using this
  have hσa : σ a = a ∨ σ a = b ∨ σ a = c := by
    have h1 := (comm_apply_ne_iff hσ a).2 (by rw [hκa]; exact hab.symm)
    exact (cyc3_apply_ne_iff (σ a) hab hbc hac).1 h1
  have hb : σ b = κ (σ a) := by rw [← hcomm' a, hκa]
  have hc : σ c = κ (σ b) := by rw [← hcomm' b, hκb]
  rcases hσa with h | h | h
  · have hσ1 : σ = 1 := by
      ext i
      by_cases hi : i = a ∨ i = b ∨ i = c
      · rcases hi with rfl | rfl | rfl
        · simpa using h
        · rw [hb, h, hκa]; rfl
        · rw [hc, hb, h, hκa, hκb]; rfl
      · exact hfix i (by simpa using hi)
    rw [hσ1]; exact one_mem _
  · have hσ1 : σ = κ := by
      ext i
      by_cases hi : i = a ∨ i = b ∨ i = c
      · rcases hi with rfl | rfl | rfl
        · rw [h, hκa]
        · rw [hb, h, hκb]
        · rw [hc, hb, h, hκb, hκc]
      · rw [hfix i (by simpa using hi), cyc3_apply_of_ne (by grind) (by grind) (by grind)]
    rw [hσ1]
    exact cyc3_mem_altSub (by simp) (by simp) (by simp) hab hbc hac
  · have hσ1 : σ = cyc3 a c b := by
      ext i
      by_cases hi : i = a ∨ i = b ∨ i = c
      · rcases hi with rfl | rfl | rfl
        · rw [h, cyc3_apply_left hac hab]
        · rw [hb, h, hκc, cyc3_apply_right]
        · rw [hc, hb, h, hκc, hκa, cyc3_apply_mid hbc.symm hab]
      · rw [hfix i (by simpa using hi), cyc3_apply_of_ne (by grind) (by grind) (by grind)]
    rw [hσ1]
    exact cyc3_mem_altSub (by simp) (by simp) (by simp) hac hbc.symm hab

theorem compl_iff_of_fixes {S : Finset α} {σ : Equiv.Perm α} (h : ∀ i ∈ S, σ i = i) (i : α) :
    i ∈ Sᶜ ↔ σ i ∈ Sᶜ := by
  simp only [Finset.mem_compl]
  constructor
  · intro hi hσ
    apply hi
    have h1 := h _ hσ
    rwa [σ.injective h1] at hσ
  · intro hσ hi
    exact hσ (by rw [h i hi]; exact hi)

theorem mem_iff_of_centralizer_altSub_card_three {S : Finset α} (hS : S.card = 3)
    {σ : Equiv.Perm α}
    (hσ : σ ∈ centralizer ((altSub S : Subgroup (Equiv.Perm α)) : Set (Equiv.Perm α))) (i : α) :
    i ∈ S ↔ σ i ∈ S := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hS
  have hκ : σ * cyc3 a b c = cyc3 a b c * σ :=
    (mem_centralizer_iff.1 hσ _
      (cyc3_mem_altSub (by simp) (by simp) (by simp) hab hbc hac)).symm
  have h1 := comm_apply_ne_iff hκ i
  rw [cyc3_apply_ne_iff _ hab hbc hac, cyc3_apply_ne_iff _ hab hbc hac] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact h1.symm

end Alt

end CFSG.OddStandard.AltStdSec
