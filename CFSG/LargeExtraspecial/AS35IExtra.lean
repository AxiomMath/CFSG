module

public import CFSG.LargeExtraspecial.AS35IProd
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCBInvolutionTrichotomy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77 CFSG.RankThree.Literature.FSmith
open CFSG.LocalAnalysis.GorensteinLyons.InvolutionTrichotomy

abbrev extraModule {P : Type} [Group P] [Finite P] (hP : IsExtraspecialPGroup 2 P) :
    Module (ZMod 2) (Additive (Abelianization P)) :=
  AddCommGroup.zmodModule fun v => by
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [← ofMul_pow, ← map_pow]
    have hx : x ^ 2 ∈ commutator P := hP.2.1 ▸ sq_mem_center hP x
    rw [← Abelianization.ker_of] at hx
    rw [MonoidHom.mem_ker.1 hx]
    rfl

theorem card_centralizer_mul_card {P : Type} [Group P] [Finite P] (hP : IsExtraspecialPGroup 2 P)
    {A : Subgroup P} (hA : center P ≤ A) :
    Nat.card (centralizer (A : Set P)) * Nat.card A = 2 * Nat.card P := by
  classical
  let _ := extraModule hP
  have : Module.Finite (ZMod 2) (Additive (Abelianization P)) := Module.Finite.of_finite
  set S : Submodule (ZMod 2) (Additive (Abelianization P)) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (A.map Abelianization.of)) with hSdef
  have hmemS : ∀ y : P, Additive.ofMul (Abelianization.of y) ∈ S ↔ y ∈ A := by
    intro y
    rw [hSdef, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, h'⟩
      have h1 : Abelianization.of a = Abelianization.of y := h'
      rw [MonoidHom.eq_iff, Abelianization.ker_of, hP.2.1] at h1
      have := mul_mem ha (inv_mem (hA h1))
      simpa using this
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hA' : preim S = A := by
    ext y
    rw [mem_preim]
    exact hmemS y
  set Bf := (extraspecialQuadForm hP).polarBilin with hBf
  have hC' : preim (LinearMap.BilinForm.orthogonal Bf S) = centralizer (A : Set P) := by
    ext y
    rw [mem_preim, LinearMap.BilinForm.mem_orthogonal_iff, mem_centralizer_iff]
    constructor
    · intro hy a ha
      have h1 := hy _ ((hmemS a).2 ha)
      exact (polar_extraspecialQuadForm_eq_zero_iff hP a y).1 h1
    · intro hy v hv
      obtain ⟨a, rfl⟩ := exists_ofMul_of v
      show QuadraticMap.polar (extraspecialQuadForm hP) (Additive.ofMul (Abelianization.of a))
        (Additive.ofMul (Abelianization.of y)) = 0
      rw [polar_extraspecialQuadForm_eq_zero_iff]
      exact hy a ((hmemS a).1 hv)
  have htop : preim (⊤ : Submodule (ZMod 2) (Additive (Abelianization P))) = ⊤ := by
    ext y
    simp [mem_preim]
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Bf) S
  rw [LinearMap.BilinForm.Nondegenerate.ker_eq_bot (extraspecialQuadForm_nondegenerate hP),
    inf_bot_eq, finrank_bot, add_zero] at hdim
  have h1 := card_preim hP S
  have h2 := card_preim hP (LinearMap.BilinForm.orthogonal Bf S)
  have h3 := card_preim hP (⊤ : Submodule (ZMod 2) (Additive (Abelianization P)))
  rw [hA'] at h1
  rw [hC'] at h2
  rw [htop, card_top, finrank_top] at h3
  rw [h1, h2, h3, ← hdim, pow_add]
  ring

variable {G : Type} [Group G] {N U P : Subgroup G} {z : G}

namespace Hyp

variable (h : Hyp N U P z)
include h

theorem le_normalizer_U {X : Subgroup G} (hX : X ≤ N) : X ≤ normalizer (U : Set G) := by
  intro x hx
  have hxN := hX hx
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [← h.Ucen u hu x hxN]
    simpa using hu
  · intro hw
    have h1 := h.Ucen _ hw x hxN
    have : u = x * u * x⁻¹ := by
      have h3 : x * u = x * (x * u * x⁻¹) := by
        calc x * u = x * u * x⁻¹ * x := by group
          _ = x * (x * u * x⁻¹) := h1
      exact mul_left_cancel h3
    rw [this]
    exact hw

theorem U_le_normalizer {X : Subgroup G} (hX : X ≤ N) : U ≤ normalizer (X : Set G) := by
  intro u hu
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h.Ucen u hu x (hX hx)]
    simpa using hx
  · intro hx
    have hxN : x ∈ N := by
      have := hX hx
      rw [show x = u⁻¹ * (u * x * u⁻¹) * u by group]
      exact N.mul_mem (N.mul_mem (N.inv_mem (h.UN hu)) this) (h.UN hu)
    rw [h.Ucen u hu x hxN] at hx
    simpa using hx

theorem card_sup_eq : Nat.card ↥(U ⊔ P) = Nat.card U * Nat.card P := by
  have hpf := card_sup_mul_card_inf (h.le_normalizer_U h.PN)
  rw [h.UP, card_bot, mul_one] at hpf
  exact hpf

theorem card_inf_kerV [Finite G] :
    Nat.card ↥((U ⊔ P) ⊓ kerV N z) = Nat.card U * Nat.card ↥(P ⊓ kerV N z) := by
  have heq : (U ⊔ P) ⊓ kerV N z = U ⊔ (P ⊓ kerV N z) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨u, hu, p, hp, rfl⟩ := h.mem_sup.1 (mem_inf.1 hx).1
      have hpK : p ∈ kerV N z := by
        have := mul_mem (inv_mem (h.U_le_kerV hu)) (mem_inf.1 hx).2
        simpa using this
      exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_inf.2 ⟨hp, hpK⟩))
    · exact sup_le (le_inf le_sup_left h.U_le_kerV)
        (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  rw [heq]
  have hn : P ⊓ kerV N z ≤ normalizer (U : Set G) :=
    h.le_normalizer_U (inf_le_left.trans h.PN)
  have hpf := card_sup_mul_card_inf hn
  have hbot : U ⊓ (P ⊓ kerV N z) = ⊥ := by
    rw [eq_bot_iff, ← h.UP]
    exact inf_le_inf_left _ inf_le_left
  rw [hbot, card_bot, mul_one] at hpf
  exact hpf

theorem card_centralizer_inf_mul [Finite G] :
    Nat.card ↥(P ⊓ centralizer ((P ⊓ kerV N z : Subgroup G) : Set G)) *
      Nat.card ↥(P ⊓ kerV N z) = 2 * Nat.card P := by
  set A' : Subgroup P := (P ⊓ kerV N z).subgroupOf P with hA'
  have hcen : center P ≤ A' := by
    intro c hc
    rw [hA', mem_subgroupOf, mem_inf]
    refine ⟨c.2, ?_⟩
    rcases h.ZP (c : G) c.2 (fun y hy => by
        have := mem_center_iff.1 hc ⟨y, hy⟩
        exact congrArg Subtype.val this.symm) with h1 | h1
    · rw [h1]
      exact (kerV N z).one_mem
    · rw [h1]
      exact h.z_mem_kerV
  have hX := card_centralizer_mul_card h.ext hcen
  have hcA : Nat.card A' = Nat.card ↥(P ⊓ kerV N z) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcC : Nat.card (centralizer (A' : Set P)) =
      Nat.card ↥(P ⊓ centralizer ((P ⊓ kerV N z : Subgroup G) : Set G)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x : P), mem_inf.2 ⟨(x : P).2, mem_centralizer_iff.2 fun a ha => ?_⟩⟩
        invFun := fun y => ⟨⟨y, (mem_inf.1 y.2).1⟩, mem_centralizer_iff.2 fun a ha => ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := mem_centralizer_iff.1 x.2 ⟨a, (mem_inf.1 ha).1⟩ (by
        rw [SetLike.mem_coe, hA', mem_subgroupOf]
        exact ha)
      exact congrArg Subtype.val this
    · rw [SetLike.mem_coe, hA', mem_subgroupOf] at ha
      exact Subtype.ext (mem_centralizer_iff.1 (mem_inf.1 y.2).2 _ ha)
  rw [hcA, hcC] at hX
  exact hX

theorem card_commutator_sup_mul_le [Finite G] :
    Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) * Nat.card ↥((U ⊔ P) ⊓ kerV N z) ≤
      2 * Nat.card ↥(U ⊔ P) * Nat.card (Asc77.centerIn z N) := by
  set C := Asc77.centerIn z N with hC
  set E := (U ⊔ P) ⊓ genV N z with hE
  set A := P ⊓ kerV N z with hA
  set Y := (U ⊔ P) ⊓ centralizer (A : Set G) with hY
  have hCV : C ≤ genV N z := inf_le_left
  have hEV : E ≤ genV N z := inf_le_right
  have hle1 : ⁅genV N z, U ⊔ P⁆ ⊔ C ≤ E ⊔ C := sup_le_sup_right h.commutator_le_inf _
  have hpf1 := card_sup_mul_card_inf (h.le_normalizer_of_le_V hEV hCV)
  have hEU : E ⊓ U ≤ E ⊓ C := fun x hx =>
    mem_inf.2 ⟨(mem_inf.1 hx).1, h.inf_le_centerIn
      (mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩)⟩
  have hUn : U ≤ normalizer (E : Set G) :=
    h.U_le_normalizer (inf_le_left.trans h.sup_le_N)
  have hpf2 := card_sup_mul_card_inf hUn
  have hEUY : E ⊔ U ≤ Y := by
    refine sup_le (fun x hx => mem_inf.2 ⟨(mem_inf.1 hx).1, mem_centralizer_iff.2 fun a ha => ?_⟩)
      (fun u hu => mem_inf.2 ⟨mem_sup_left hu, mem_centralizer_iff.2 fun a ha =>
        (h.Ucen u hu a (h.PN (mem_inf.1 ha).1)).symm⟩)
    exact (mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 ha).2).2 x (mem_inf.1 hx).2).symm
  have hYle : Y ≤ U ⊔ (P ⊓ centralizer (A : Set G)) := by
    intro y hy
    obtain ⟨u, hu, p, hp, rfl⟩ := h.mem_sup.1 (mem_inf.1 hy).1
    refine mul_mem (mem_sup_left hu) (mem_sup_right (mem_inf.2 ⟨hp, ?_⟩))
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := mem_centralizer_iff.1 (mem_inf.1 hy).2 a ha
    have h2 := h.Ucen u hu a (h.PN (mem_inf.1 ha).1)
    have h3 : u * (a * p) = u * (p * a) := by
      calc u * (a * p) = (u * a) * p := by group
        _ = (a * u) * p := by rw [h2]
        _ = a * (u * p) := by group
        _ = u * p * a := h1
        _ = u * (p * a) := by group
    exact mul_left_cancel h3
  have hn3 : P ⊓ centralizer (A : Set G) ≤ normalizer (U : Set G) :=
    h.le_normalizer_U (inf_le_left.trans h.PN)
  have hpf3 := card_sup_mul_card_inf hn3
  have hY : Nat.card Y ≤ Nat.card U * Nat.card ↥(P ⊓ centralizer (A : Set G)) := by
    have hpos : 0 < Nat.card ↥(U ⊓ (P ⊓ centralizer (A : Set G))) := Nat.card_pos
    calc Nat.card Y ≤ Nat.card ↥(U ⊔ (P ⊓ centralizer (A : Set G))) := card_le_of_le hYle
      _ ≤ Nat.card ↥(U ⊔ (P ⊓ centralizer (A : Set G))) *
          Nat.card ↥(U ⊓ (P ⊓ centralizer (A : Set G))) := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card U * Nat.card ↥(P ⊓ centralizer (A : Set G)) := hpf3
  have hX := h.card_centralizer_inf_mul
  have hQc := h.card_sup_eq
  have hQK := h.card_inf_kerV
  have hEUpos : 0 < Nat.card ↥(E ⊓ U) := Nat.card_pos
  have hUpos : 0 < Nat.card U := Nat.card_pos
  set a := Nat.card ↥(E ⊔ C)
  set b := Nat.card ↥(E ⊓ C)
  set e := Nat.card E
  set c := Nat.card C
  set eu := Nat.card ↥(E ⊔ U)
  set ei := Nat.card ↥(E ⊓ U)
  set u := Nat.card U
  set pc := Nat.card ↥(P ⊓ centralizer (A : Set G))
  set al := Nat.card A
  set p := Nat.card P
  have hei : ei ≤ b := card_le_of_le hEU
  have heuY : eu ≤ u * pc := (card_le_of_le hEUY).trans hY
  have key : a * u * ei ≤ u * pc * c * ei := by
    calc a * u * ei = u * (a * ei) := by ring
      _ ≤ u * (a * b) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hei)
      _ = u * (e * c) := by rw [hpf1]
      _ = (e * u) * c := by ring
      _ = (eu * ei) * c := by rw [hpf2]
      _ ≤ (u * pc * ei) * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ heuY)
      _ = u * pc * c * ei := by ring
  have key2 : a * u ≤ u * pc * c := Nat.le_of_mul_le_mul_right key hEUpos
  calc Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ C) * Nat.card ↥((U ⊔ P) ⊓ kerV N z)
      ≤ a * (u * al) := Nat.mul_le_mul (card_le_of_le hle1) hQK.le
    _ = (a * u) * al := by ring
    _ ≤ (u * pc * c) * al := Nat.mul_le_mul_right _ key2
    _ = u * c * (pc * al) := by ring
    _ = u * c * (2 * p) := by rw [hX]
    _ = 2 * (u * p) * c := by ring
    _ = 2 * Nat.card ↥(U ⊔ P) * c := by rw [hQc]

theorem card_commutator_sup_le [Finite G] :
    Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) ≤
      2 * Nat.card (barOf N z (U ⊔ P)) * Nat.card (Asc77.centerIn z N) := by
  have h1 := h.card_commutator_sup_mul_le
  have h2 := h.card_Qb_mul
  have hpos : 0 < Nat.card ↥((U ⊔ P) ⊓ kerV N z) := Nat.card_pos
  rw [← h2] at h1
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) * Nat.card ↥((U ⊔ P) ⊓ kerV N z)
      ≤ 2 * (Nat.card (barOf N z (U ⊔ P)) * Nat.card ↥((U ⊔ P) ⊓ kerV N z)) *
          Nat.card (Asc77.centerIn z N) := h1
    _ = 2 * Nat.card (barOf N z (U ⊔ P)) * Nat.card (Asc77.centerIn z N) *
          Nat.card ↥((U ⊔ P) ⊓ kerV N z) := by ring

end Hyp

end CFSG.LargeExtraspecial.Asc22
