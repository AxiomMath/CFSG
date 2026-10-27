module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open Subgroup

namespace CFSG.GH74.Generic.S45

section Corr

variable {G G' : Type*} [Group G] [Group G'] {N : Subgroup G} {W : Subgroup G'}

structure Corr (ψ : ↥N ≃* ↥W) (A : Subgroup G) (A' : Subgroup G') : Prop where
  le : A ≤ N
  le' : A' ≤ W
  mem_iff : ∀ n : ↥N, (n : G) ∈ A ↔ ((ψ n : ↥W) : G') ∈ A'

structure SCorr (ψ : ↥N ≃* ↥W) (S : Set G) (S' : Set G') : Prop where
  subset : S ⊆ N
  subset' : S' ⊆ W
  mem_iff : ∀ n : ↥N, (n : G) ∈ S ↔ ((ψ n : ↥W) : G') ∈ S'

variable {ψ : ↥N ≃* ↥W}

theorem Corr.symm {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') : Corr ψ.symm A' A where
  le := h.le'
  le' := h.le
  mem_iff n' := by
    have := h.mem_iff (ψ.symm n')
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm

theorem SCorr.symm {S : Set G} {S' : Set G'} (h : SCorr ψ S S') : SCorr ψ.symm S' S where
  subset := h.subset'
  subset' := h.subset
  mem_iff n' := by
    have := h.mem_iff (ψ.symm n')
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm

theorem Corr.scorr {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') :
    SCorr ψ (A : Set G) (A' : Set G') := ⟨h.le, h.le', h.mem_iff⟩

theorem Corr.nonempty_mulEquiv {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') :
    Nonempty (↥A ≃* ↥A') := by
  refine ⟨{ toFun := fun a => ⟨((ψ ⟨a, h.le a.2⟩ : ↥W) : G'), (h.mem_iff ⟨a, h.le a.2⟩).1 a.2⟩
            invFun := fun a => ⟨((ψ.symm ⟨a, h.le' a.2⟩ : ↥N) : G),
              (h.symm.mem_iff ⟨a, h.le' a.2⟩).1 a.2⟩
            left_inv := fun a => by apply Subtype.ext; simp
            right_inv := fun a => by apply Subtype.ext; simp
            map_mul' := fun a b => by
              apply Subtype.ext
              show ((ψ ⟨(a : G) * (b : G), _⟩ : ↥W) : G') = _
              rw [show (⟨(a : G) * (b : G), _⟩ : ↥N) = ⟨a, h.le a.2⟩ * ⟨b, h.le b.2⟩ from rfl,
                map_mul]
              rfl }⟩

theorem Corr.card_eq {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') :
    Nat.card ↥A = Nat.card ↥A' := by
  obtain ⟨f⟩ := h.nonempty_mulEquiv
  exact Nat.card_congr f.toEquiv

theorem IsElementaryAbelian.of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (h : IsElementaryAbelian p B) : IsElementaryAbelian p A :=
  CFSG.IsElementaryAbelian.of_mulEquiv f.symm h

theorem Corr.isElementaryAbelian_iff {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') {p : ℕ} :
    IsElementaryAbelian p ↥A ↔ IsElementaryAbelian p ↥A' := by
  obtain ⟨f⟩ := h.nonempty_mulEquiv
  exact ⟨fun hA => IsElementaryAbelian.of_mulEquiv f.symm hA,
    fun hA => IsElementaryAbelian.of_mulEquiv f hA⟩

theorem Corr.exists_of_le (ψ : ↥N ≃* ↥W) {A' : Subgroup G'} (h : A' ≤ W) :
    ∃ A : Subgroup G, Corr ψ A A' := by
  refine ⟨((A'.subgroupOf W).comap ψ.toMonoidHom).map N.subtype, ⟨?_, h, fun n => ?_⟩⟩
  · rintro _ ⟨m, -, rfl⟩
    exact m.2
  · constructor
    · rintro ⟨m, hm, hmn⟩
      have : m = n := Subtype.ext hmn
      subst this
      exact hm
    · intro hn
      exact ⟨n, hn, rfl⟩

theorem Corr.top : Corr ψ N W := ⟨le_rfl, le_rfl, fun n => ⟨fun _ => (ψ n).2, fun _ => n.2⟩⟩

theorem SCorr.mem_centralizer_of {S : Set G} {S' : Set G'} (h : SCorr ψ S S') {n : ↥N}
    (hn : (n : G) ∈ centralizer S) : ((ψ n : ↥W) : G') ∈ centralizer S' := by
  rw [mem_centralizer_iff]
  intro s' hs'
  have hsW : s' ∈ W := h.subset' hs'
  have hmS : ((ψ.symm ⟨s', hsW⟩ : ↥N) : G) ∈ S :=
    (h.mem_iff _).2 (by rw [MulEquiv.apply_symm_apply]; exact hs')
  have hcomm : ψ.symm ⟨s', hsW⟩ * n = n * ψ.symm ⟨s', hsW⟩ :=
    Subtype.ext (mem_centralizer_iff.1 hn _ hmS)
  have := congrArg (fun z : ↥N => ((ψ z : ↥W) : G')) hcomm
  simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using this

theorem SCorr.centralizer {S : Set G} {S' : Set G'} (h : SCorr ψ S S') :
    Corr ψ (centralizer S ⊓ N) (centralizer S' ⊓ W) :=
  ⟨inf_le_right, inf_le_right, fun n => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine ⟨fun ⟨hn, _⟩ => ⟨h.mem_centralizer_of hn, (ψ n).2⟩, fun ⟨hn, _⟩ => ⟨?_, n.2⟩⟩
    have := h.symm.mem_centralizer_of (n := ψ n) hn
    simpa only [MulEquiv.symm_apply_apply] using this⟩

theorem SCorr.singleton {a : G} {a' : G'} (ha : a ∈ N) (h : ((ψ ⟨a, ha⟩ : ↥W) : G') = a') :
    SCorr ψ {a} {a'} :=
  ⟨Set.singleton_subset_iff.2 ha, Set.singleton_subset_iff.2 (h ▸ (ψ ⟨a, ha⟩).2), fun n => by
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hn
      have : n = ⟨a, ha⟩ := Subtype.ext hn
      rw [this, h]
    · intro hn
      have : ψ n = ψ ⟨a, ha⟩ := Subtype.ext (hn.trans h.symm)
      exact congrArg Subtype.val (ψ.injective this)⟩

theorem Corr.mem_normalizer_of {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') {n : ↥N}
    (hn : (n : G) ∈ normalizer (A : Set G)) : ((ψ n : ↥W) : G') ∈ normalizer (A' : Set G') := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro y'
  constructor
  · intro hy'
    have hyW : y' ∈ W := h.le' hy'
    have hm : ((ψ.symm ⟨y', hyW⟩ : ↥N) : G) ∈ A :=
      (h.mem_iff _).2 (by rw [MulEquiv.apply_symm_apply]; exact hy')
    have h1 := (hn _).1 hm
    have h2 := (h.mem_iff (n * ψ.symm ⟨y', hyW⟩ * n⁻¹)).1 (by simpa using h1)
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] using h2
  · intro hy'
    have hyW : ((ψ n : ↥W) : G') * y' * ((ψ n : ↥W) : G')⁻¹ ∈ W := h.le' hy'
    have hyW' : y' ∈ W := by
      have := W.mul_mem (W.mul_mem (W.inv_mem (ψ n).2) hyW) (ψ n).2
      simpa [mul_assoc] using this
    have h3 : ((n * ψ.symm ⟨y', hyW'⟩ * n⁻¹ : ↥N) : G) ∈ A := by
      rw [h.mem_iff]
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] using hy'
    have h4 := (hn ((ψ.symm ⟨y', hyW'⟩ : ↥N) : G)).2 (by simpa using h3)
    have := (h.mem_iff _).1 h4
    simpa only [MulEquiv.apply_symm_apply] using this

theorem Corr.normalizer {A : Subgroup G} {A' : Subgroup G'} (h : Corr ψ A A') :
    Corr ψ (normalizer (A : Set G) ⊓ N) (normalizer (A' : Set G') ⊓ W) :=
  ⟨inf_le_right, inf_le_right, fun n => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine ⟨fun ⟨hn, _⟩ => ⟨h.mem_normalizer_of hn, (ψ n).2⟩, fun ⟨hn, _⟩ => ⟨?_, n.2⟩⟩
    have := h.symm.mem_normalizer_of (n := ψ n) hn
    simpa only [MulEquiv.symm_apply_apply] using this⟩

theorem orderOf_corr (ψ : ↥N ≃* ↥W) (n : ↥N) : orderOf ((ψ n : ↥W) : G') = orderOf (n : G) := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]

end Corr

end CFSG.GH74.Generic.S45
