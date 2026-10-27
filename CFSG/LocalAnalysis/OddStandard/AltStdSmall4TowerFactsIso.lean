module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFacts
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCheckFacts

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

variable {X G : Type*} [Group X] [Group G] {φ : X →* G}

section Transfer

variable (hφ : Function.Injective φ)
include hφ

theorem map_centralizer_eq (x : X) :
    (centralizer {x}).map φ = φ.range ⊓ centralizer {φ x} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine mem_inf.2 ⟨⟨w, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hw]
  · intro hz
    obtain ⟨⟨w, rfl⟩, hc⟩ := mem_inf.1 hz
    refine ⟨w, mem_centralizer_singleton_iff.2 (hφ ?_), rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.1 hc

noncomputable def centEquiv (x : X) :
    (centralizer {x} : Subgroup X) ≃* (φ.range ⊓ centralizer {φ x} : Subgroup G) :=
  ((centralizer {x}).equivMapOfInjective φ hφ).trans
    (MulEquiv.subgroupCongr (map_centralizer_eq hφ x))

theorem card_cent_map (x : X) :
    Nat.card (φ.range ⊓ centralizer {φ x} : Subgroup G) = Nat.card (centralizer {x}) :=
  (Nat.card_congr (centEquiv hφ x).toEquiv).symm

theorem pinv_map_iff (x : X) :
    PInv (φ.range ⊓ centralizer {φ x} : Subgroup G) ↔ PInv (centralizer {x} : Subgroup X) :=
  ⟨pinv_of_mulEquiv (centEquiv hφ x).symm, pinv_of_mulEquiv (centEquiv hφ x)⟩

theorem isPInv_map_iff (x : X) : IsPInvol φ.range (φ x) ↔ IsPInv x := by
  rw [IsPInvol, ← map_pow, Ne, map_eq_one_iff φ hφ, map_eq_one_iff φ hφ, pinv_map_iff hφ]
  exact ⟨fun h => h.2, fun h => ⟨⟨x, rfl⟩, h⟩⟩

theorem conj_map {x y : X} (h : Conj x y) : ∃ k ∈ φ.range, φ x = k * φ y * k⁻¹ := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨φ k, ⟨k, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

theorem relIndex_map_range (Q : Subgroup X) : (Q.map φ).relIndex φ.range = Q.index := by
  rw [MonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ hφ, relIndex_top_right]

theorem isPGroup_range {n : ℕ} (hX : Nat.card X = 2 ^ n) : IsPGroup 2 φ.range :=
  IsPGroup.of_card ((Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans hX)

end Transfer

section OfConj

variable (hφ : Function.Injective φ) {c : G}

noncomputable def pull {y : G} (hy : y ∈ φ.range) : X := (MonoidHom.ofInjective hφ).symm ⟨y, hy⟩

theorem map_pull {y : G} (hy : y ∈ φ.range) : φ (pull hφ hy) = y := by
  have h := congrArg Subtype.val ((MonoidHom.ofInjective hφ).apply_symm_apply ⟨y, hy⟩)
  rwa [MonoidHom.ofInjective_apply] at h

theorem conj_mem_range (hcN : c ∈ normalizer (φ.range : Set G)) (x : X) :
    c * φ x * c⁻¹ ∈ φ.range :=
  (mem_normalizer_iff.1 hcN (φ x)).1 ⟨x, rfl⟩

noncomputable def conjPull (hcN : c ∈ normalizer (φ.range : Set G)) (x : X) : X :=
  pull hφ (conj_mem_range hcN x)

theorem map_conjPull (hcN : c ∈ normalizer (φ.range : Set G)) (x : X) :
    φ (conjPull hφ hcN x) = c * φ x * c⁻¹ :=
  map_pull hφ _

noncomputable def conjAut (hcN : c ∈ normalizer (φ.range : Set G)) : MulAut X where
  toFun := conjPull hφ hcN
  invFun := conjPull hφ (inv_mem hcN)
  left_inv x := hφ (by rw [map_conjPull, map_conjPull]; group)
  right_inv x := hφ (by rw [map_conjPull, map_conjPull]; group)
  map_mul' a b := hφ (by rw [map_mul, map_conjPull, map_conjPull, map_conjPull, map_mul]; group)

variable (hcN : c ∈ normalizer (φ.range : Set G)) (hc2 : c ^ 2 ∈ φ.range)

noncomputable def ExtData.ofConj : ExtData X where
  α := conjAut hφ hcN
  g := pull hφ hc2
  hαg := hφ (by
    change φ (conjPull hφ hcN _) = _
    rw [map_conjPull, map_pull]
    group)
  hα2 k := hφ (by
    change φ (conjPull hφ hcN (conjPull hφ hcN k)) = _
    rw [map_conjPull, map_conjPull, map_mul, map_mul, map_inv, map_pull, sq]
    group)

theorem map_ofConj_α (x : X) : φ ((ExtData.ofConj hφ hcN hc2).α x) = c * φ x * c⁻¹ :=
  map_conjPull hφ hcN x

theorem map_ofConj_g : φ (ExtData.ofConj hφ hcN hc2).g = c ^ 2 :=
  map_pull hφ hc2

@[expose] noncomputable def cycHom : CycExt (ExtData.ofConj hφ hcN hc2) →* G where
  toFun a := φ a.k * if a.d then c else 1
  map_one' := by simp [CycExt.one_def]
  map_mul' a b := by
    obtain ⟨k, d⟩ := a
    obtain ⟨k', d'⟩ := b
    cases d <;> cases d' <;>
      simp only [CycExt.mk_mul_mk, CycExt.pw, CycExt.sq, map_mul, map_one, map_ofConj_α,
        map_ofConj_g, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
        Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ite_true, ite_false, mul_one] <;> group

theorem cycHom_mk (k : X) (d : Bool) :
    cycHom hφ hcN hc2 ⟨k, d⟩ = φ k * if d then c else 1 := rfl

theorem cycHom_incl (k : X) : cycHom hφ hcN hc2 (CycExt.incl _ k) = φ k := by
  change φ k * (if false then c else 1) = φ k
  simp

theorem cycHom_injective (hcK : c ∉ φ.range) : Function.Injective (cycHom hφ hcN hc2) := by
  rintro ⟨k, d⟩ ⟨k', d'⟩ h
  rw [cycHom_mk, cycHom_mk] at h
  cases d <;> cases d' <;> simp only [Bool.false_eq_true, ite_true, ite_false, mul_one] at h
  · rw [hφ h]
  · exact absurd ⟨k'⁻¹ * k, by rw [map_mul, map_inv, h]; group⟩ hcK
  · exact absurd ⟨k⁻¹ * k', by rw [map_mul, map_inv, ← h]; group⟩ hcK
  · rw [hφ (mul_right_cancel h)]

theorem range_le_cycHom : φ.range ≤ (cycHom hφ hcN hc2).range := by
  rintro _ ⟨k, rfl⟩
  exact ⟨CycExt.incl _ k, cycHom_incl hφ hcN hc2 k⟩

theorem mem_range_cycHom : c ∈ (cycHom hφ hcN hc2).range :=
  ⟨⟨1, true⟩, by rw [cycHom_mk]; simp⟩

end OfConj

theorem CycExt.card (D : ExtData X) : Nat.card (CycExt D) = Nat.card X * 2 := by
  have e : CycExt D ≃ X × Bool :=
    ⟨fun a => (a.k, a.d), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

end CFSG.OddStandard.AltStdSmall4.Tower
