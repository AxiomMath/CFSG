module

public import CFSG.ClassicalInvolution.Q3.Q3CSBase
public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.Balance.PassTwo

public section

namespace CFSG.ClassicalInvolution.Q3.Q3C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

section Closure

variable {G : Type} [Group G]

@[expose] def centralizerClosure (b : G) (L : Subgroup G) : Subgroup G :=
  ⨆ c ∈ Subgroup.centralizer ({b} : Set G), conjSub c L

theorem conjSub_le_centralizerClosure {b c : G} (hc : c ∈ Subgroup.centralizer ({b} : Set G))
    (L : Subgroup G) : conjSub c L ≤ centralizerClosure b L :=
  le_iSup₂ (f := fun (c : G) (_ : c ∈ Subgroup.centralizer ({b} : Set G)) => conjSub c L) c hc

theorem le_centralizerClosure (b : G) (L : Subgroup G) : L ≤ centralizerClosure b L := by
  have := conjSub_le_centralizerClosure (Subgroup.one_mem (Subgroup.centralizer ({b} : Set G))) L
  rwa [conjSub_one] at this

theorem centralizerClosure_le_centralizer {b : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({b} : Set G)) :
    centralizerClosure b L ≤ Subgroup.centralizer ({b} : Set G) := by
  refine iSup₂_le fun c hc x hx => ?_
  rw [mem_conjSub_iff] at hx
  have hyb : Commute (c⁻¹ * x * c) b := Subgroup.mem_centralizer_singleton_iff.mp (hL hx)
  have hcb : Commute c b := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hx' : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := (hcb.mul_left hyb).mul_left hcb.inv_left
  rw [← hx'] at this
  exact this

theorem conj_mem_centralizerClosure {b c : G} (hc : c ∈ Subgroup.centralizer ({b} : Set G))
    {L : Subgroup G} {h : G} (hh : h ∈ centralizerClosure b L) :
    c * h * c⁻¹ ∈ centralizerClosure b L := by
  have key : centralizerClosure b L ≤
      (centralizerClosure b L).comap (MulAut.conj c).toMonoidHom := by
    refine iSup₂_le fun c' hc' x hx => ?_
    show c * x * c⁻¹ ∈ centralizerClosure b L
    rw [mem_conjSub_iff] at hx
    have hmem : c * x * c⁻¹ ∈ conjSub (c * c') L := by
      rw [mem_conjSub_iff]
      simpa [mul_assoc] using hx
    exact conjSub_le_centralizerClosure (Subgroup.mul_mem _ hc hc') L hmem
  exact key hh

end Closure

section Datum

variable {G : Type} [Group G]

@[expose] def SBaseDatumL (B : Subgroup G) (b : G) : Prop :=
  ∃ (L : Subgroup G) (w : G) (hw : w ∈ L), L ≤ Subgroup.centralizer ({b} : Set G) ∧
    IsClassicalMember3 (L.subgroupOf (centralizerClosure b L))
      ⟨w, le_centralizerClosure b L hw⟩ ∧
    B ≤ centralizerClosure b L ∧
    ∀ X : Subgroup G, X ≤ Subgroup.centralizer ({b} : Set G) → Odd (Nat.card X) →
      X ≤ centralizerClosure b L

end Datum

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_mem_of_not_mem_of_not_mem {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hA8 : Nat.card A = 8) (hBA : B ≤ A) (hB4 : Nat.card B = 4) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) (hxB : x ∉ B) (hyB : y ∉ B) : x * y ∈ B := by
  have hidx : (B.subgroupOf A).index = 2 := by
    have h1 := Subgroup.card_mul_index (B.subgroupOf A)
    have h2 : Nat.card ↥(B.subgroupOf A) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, hB4]
    rw [h2, hA8] at h1
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hxB' : (⟨x, hx⟩ : A) ∉ B.subgroupOf A := fun h => hxB h
  have hyB' : (⟨y, hy⟩ : A) ∉ B.subgroupOf A := fun h => hyB h
  have hx1 : (⟨x, hx⟩ : A) * a ∈ B.subgroupOf A := by
    rcases ha ⟨x, hx⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxB'
  have hy1 : (⟨y, hy⟩ : A) * a ∈ B.subgroupOf A := by
    rcases ha ⟨y, hy⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hyB'
  have h3 : ((⟨x, hx⟩ : A) * a) * ((⟨y, hy⟩ : A) * a)⁻¹ ∈ B.subgroupOf A :=
    Subgroup.mul_mem _ hx1 (Subgroup.inv_mem _ hy1)
  have h4 : ((⟨x, hx⟩ : A) * a) * ((⟨y, hy⟩ : A) * a)⁻¹ = ⟨x, hx⟩ * (⟨y, hy⟩ : A)⁻¹ := by group
  rw [h4] at h3
  have h5 : x * y⁻¹ ∈ B := h3
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (elem_sq hA hy)
  rwa [hyi] at h5

theorem sBaseDatum_of_datumL [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hBelow : CIT3Below (Nat.card G)) {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hA8 : Nat.card A = 8) (hBA : B ≤ A) (hB4 : Nat.card B = 4) {b : G} (hbA : b ∈ A)
    (hbB : b ∉ B) (h : SBaseDatumL B b) : SBaseDatum A b := by
  obtain ⟨L, w, hw, hLb, hcl, hBH, hodd⟩ := h
  set H := centralizerClosure b L with hH
  have hHb : H ≤ Subgroup.centralizer ({b} : Set G) := centralizerClosure_le_centralizer hLb
  have hHn : ∀ c ∈ Subgroup.centralizer ({b} : Set G), ∀ h ∈ H, c * h * c⁻¹ ∈ H :=
    fun c hc h hh => conj_mem_centralizerClosure hc hh
  have hAH : ∀ x ∈ A, x ∈ H ∨ x * b ∈ H := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl (hBH hxB)
    · exact Or.inr (hBH (mul_mem_of_not_mem_of_not_mem hA hA8 hBA hB4 hx hbA hxB hbB))
  refine ⟨H, hHb, hHn, hAH, hodd, ?_⟩
  have hb1 : b ≠ 1 := fun h => hbB (h ▸ B.one_mem)
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hC : Subgroup.centralizer ({b} : Set G) = ⊤ := top_unique (htop ▸ hHb)
    exact not_subset_center_of_ne_one hnab hb1 (Subgroup.centralizer_eq_top_iff_subset.mp hC)
  have hcard : Nat.card ↥H < Nat.card G := card_lt_of_ne_top hHtop
  have hcls : ∀ c ∈ Subgroup.centralizer ({b} : Set G), ∃ z : ↥H,
      IsClassicalMember3 ((conjSub c L).subgroupOf H) z := by
    intro c hc
    let e : ↥H ≃* ↥H :=
      { toFun := fun h => ⟨c * h * c⁻¹, hHn c hc h h.2⟩
        invFun := fun h => ⟨c⁻¹ * h * c, by
          simpa using hHn c⁻¹ ((Subgroup.centralizer ({b} : Set G)).inv_mem hc) h h.2⟩
        left_inv := fun h => Subtype.ext (by simp [mul_assoc])
        right_inv := fun h => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    refine ⟨e ⟨w, le_centralizerClosure b L hw⟩, ?_⟩
    have h1 := IsClassicalMember3.map_mulEquiv e hcl
    have h2 : (L.subgroupOf H).map e.toMonoidHom = (conjSub c L).subgroupOf H := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_subgroupOf, mem_conjSub_iff]
        have hx' : (x : G) ∈ L := hx
        simpa [e, mul_assoc] using hx'
      · intro hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        show e.symm y ∈ L.subgroupOf H
        rw [Subgroup.mem_subgroupOf]
        have hy' : c⁻¹ * (y : G) * c ∈ L := by
          have := hy
          rw [Subgroup.mem_subgroupOf, mem_conjSub_iff] at this
          exact this
        simpa [e, mul_assoc] using hy'
    rw [h2] at h1
    exact h1
  let Γ : Set (Subgroup ↥H) :=
    {L' | ∃ c ∈ Subgroup.centralizer ({b} : Set G), L' = (conjSub c L).subgroupOf H}
  have hΓ : InClass3 Γ := by
    refine ⟨⟨L.subgroupOf H, 1, Subgroup.one_mem _, by simp [conjSub_one]⟩, ?_, ?_, ?_⟩
    · rintro n _ ⟨c, hc, rfl⟩
      refine ⟨(n : G) * c, Subgroup.mul_mem _ (hHb n.2) hc, ?_⟩
      rw [conjSub_subgroupOf, conjSub_mul]
    · have key := iSup_subgroupOf_self (G := G)
        (fun c : {c : G // c ∈ Subgroup.centralizer ({b} : Set G)} => conjSub (c : G) L)
      have hsup : (⨆ c : {c : G // c ∈ Subgroup.centralizer ({b} : Set G)},
          conjSub (c : G) L) = H := by
        rw [hH, centralizerClosure, iSup_subtype']
      rw [hsup] at key
      refine eq_top_iff.mpr (key.symm.le.trans ?_)
      refine iSup_le fun c => ?_
      exact le_iSup₂ (f := fun (L' : Subgroup ↥H) (_ : L' ∈ Γ) => L')
        ((conjSub (c : G) L).subgroupOf H) ⟨c, c.2, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact hcls c hc
  exact ⟨Γ, hBelow _ hcard Γ hΓ⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3C
