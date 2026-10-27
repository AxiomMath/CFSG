module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightPointAction
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveOrthogonalGroup
public import CFSG.ClassicalGroups.Alternating.Generation

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₁₀" =>
  (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "ρ₁" => ptAct hzC hsup hinf hz hb hnd hV φ he halt

@[expose] def ptD₁ : Subgroup G :=
  ((translationPerms 𝔼).comap (ptAct hzC hsup hinf hz hb hnd hV φ he halt)).map
    (𝒩₁).subtype

theorem mem_ptD₁_iff {d : G} :
    d ∈ ptD₁ hzC hsup hinf hz hb hnd hV φ he halt ↔
      ∃ h : d ∈ 𝒩₁, ∃ a : 𝔼, ∀ w, ρ₁ ⟨d, h⟩ w = a + w := by
  constructor
  · rintro ⟨m, ⟨a, ha⟩, rfl⟩
    exact ⟨m.2, a, ha⟩
  · rintro ⟨h, a, ha⟩
    exact ⟨⟨d, h⟩, ⟨a, ha⟩, rfl⟩

theorem ptD₁_le : ptD₁ hzC hsup hinf hz hb hnd hV φ he halt ≤ 𝒩₁ := map_subtype_le _

theorem ptAct_of_mem_ptD₁ {d : G} (hd : d ∈ ptD₁ hzC hsup hinf hz hb hnd hV φ he halt) (w : 𝔼) :
    ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hd⟩ w =
      ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hd⟩ 0 + w := by
  obtain ⟨h, a, ha⟩ := (mem_ptD₁_iff hzC hsup hinf hz hb hnd hV φ he halt).1 hd
  rw [ha, ha, add_zero]

theorem mem_ptD₁_iff_ptLin (m : 𝒩₁) :
    (m : G) ∈ ptD₁ hzC hsup hinf hz hb hnd hV φ he halt ↔
      ptLin hzC hsup hinf hz hb hnd hV φ he halt m = 1 := by
  rw [mem_ptD₁_iff]
  constructor
  · rintro ⟨h, a, ha⟩
    refine ptLin_eq hzC hsup hinf hz hb hnd hV φ he halt fun w => ?_
    have ha' : ∀ w, ρ₁ m w = a + w := ha
    rw [ha', ha', add_zero, add_comm]
    rfl
  · intro h
    refine ⟨m.2, ρ₁ m 0, fun w => ?_⟩
    change ρ₁ m w = _
    rw [ptLin_spec hzC hsup hinf hz hb hnd hV φ he halt m w, h, add_comm]
    rfl

theorem ptD₁_subgroupOf : (ptD₁ hzC hsup hinf hz hb hnd hV φ he halt).subgroupOf 𝒩₁ =
    (ptLin hzC hsup hinf hz hb hnd hV φ he halt).ker := by
  ext m
  rw [mem_subgroupOf, MonoidHom.mem_ker, mem_ptD₁_iff_ptLin]

theorem ptSub_le_ptD₁ : ptSub φ z hb e ≤ ptD₁ hzC hsup hinf hz hb hnd hV φ he halt := by
  intro x hx
  have hxN : x ∈ 𝒩₁ := le_normalizer hx
  have hker : (⟨x, hxN⟩ : 𝒩₁) ∈ (ρ₁).ker := by
    rw [ker_ptAct hzC hsup hinf hz hb hnd hV φ he halt, mem_subgroupOf]
    exact hx
  refine (mem_ptD₁_iff hzC hsup hinf hz hb hnd hV φ he halt).2 ⟨hxN, 0, fun w => ?_⟩
  rw [MonoidHom.mem_ker.1 hker, zero_add]
  rfl

@[expose] def ptTr : ptD₁ hzC hsup hinf hz hb hnd hV φ he halt →* Multiplicative 𝔼 :=
  MonoidHom.mk' (fun d => Multiplicative.ofAdd
    (ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ 0)) fun d d' => by
      rw [← ofAdd_add]
      congr 1
      have h : (⟨(d * d' : ptD₁ hzC hsup hinf hz hb hnd hV φ he halt), ptD₁_le hzC hsup hinf hz hb
          hnd hV φ he halt (d * d').2⟩ : 𝒩₁) =
          ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ *
            ⟨d', ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d'.2⟩ := rfl
      rw [h, map_mul, Equiv.Perm.mul_apply, ptAct_of_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
        d.2]

theorem ptAct_eq_ptTr_add (d : ptD₁ hzC hsup hinf hz hb hnd hV φ he halt) (w : 𝔼) :
    ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ w =
      Multiplicative.toAdd (ptTr hzC hsup hinf hz hb hnd hV φ he halt d) + w :=
  ptAct_of_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt d.2 w

theorem ptTr_surjective : Function.Surjective (ptTr hzC hsup hinf hz hb hnd hV φ he halt) := by
  intro a
  obtain ⟨m, hm⟩ := (mem_range_ptAct_iff hzC hsup hinf hz hb hnd hV φ he halt
    (Equiv.addLeft (Multiplicative.toAdd a))).2 ⟨1, Multiplicative.toAdd a, fun w => by
      rw [Equiv.coe_addLeft, OddQuadraticFive.sE_one, add_comm]⟩
  have hmD : (m : G) ∈ ptD₁ hzC hsup hinf hz hb hnd hV φ he halt :=
    (mem_ptD₁_iff hzC hsup hinf hz hb hnd hV φ he halt).2 ⟨m.2, Multiplicative.toAdd a,
      fun w => by
        change ρ₁ m w = _
        rw [hm]
        rfl⟩
  refine ⟨⟨m, hmD⟩, ?_⟩
  change Multiplicative.ofAdd (ρ₁ m 0) = a
  rw [hm]
  change Multiplicative.ofAdd (Multiplicative.toAdd a + 0) = a
  rw [add_zero, ofAdd_toAdd]

theorem ker_ptTr : (ptTr hzC hsup hinf hz hb hnd hV φ he halt).ker =
    (ptSub φ z hb e).subgroupOf (ptD₁ hzC hsup hinf hz hb hnd hV φ he halt) := by
  ext d
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    have h1 : ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ = 1 := Equiv.ext fun w => by
      rw [ptAct_eq_ptTr_add, h, toAdd_one, zero_add]
      rfl
    have h2 := MonoidHom.mem_ker.2 h1
    rw [ker_ptAct hzC hsup hinf hz hb hnd hV φ he halt, mem_subgroupOf] at h2
    exact h2
  · intro h
    have h2 : (⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ : 𝒩₁) ∈ (ρ₁).ker := by
      rw [ker_ptAct hzC hsup hinf hz hb hnd hV φ he halt, mem_subgroupOf]
      exact h
    change Multiplicative.ofAdd (ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ 0) = 1
    rw [MonoidHom.mem_ker.1 h2]
    rfl

theorem card_ptD₁ : Nat.card (ptD₁ hzC hsup hinf hz hb hnd hV φ he halt) = 1024 := by
  have h1 := (ptTr hzC hsup hinf hz hb hnd hV φ he halt).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ptTr_surjective hzC hsup hinf hz hb hnd hV φ
    he halt), Subgroup.card_top, ker_ptTr,
    Nat.card_congr (subgroupOfEquivOfLe
      (ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt)).toEquiv,
    (ptSub_facts he hb hnd φ hzC hinf hz).2.2.1, Nat.card_congr Multiplicative.toAdd,
    card_pairOrth_eq he hb hnd] at h1
  rw [← h1]

theorem ptD₁_normal :
    ((ptD₁ hzC hsup hinf hz hb hnd hV φ he halt).subgroupOf 𝒩₁).Normal := by
  rw [ptD₁_subgroupOf]
  exact MonoidHom.normal_ker _

theorem ptAct_zero_eq_zero_iff (m : 𝒩₁) : ρ₁ m 0 = 0 ↔ (m : G) ∈ 𝒩₁₀ := by
  rw [ptAct_eq_iff, ptGr_zero, mem_inf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩

theorem ptD₁_inf_centralizer :
    ptD₁ hzC hsup hinf hz hb hnd hV φ he halt ⊓ centralizer ({z} : Set G) = ptSub φ z hb e := by
  obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  apply le_antisymm
  · rintro d ⟨hd, hdz⟩
    have h0 : ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hd⟩ 0 = 0 :=
      (ptAct_zero_eq_zero_iff hzC hsup hinf hz hb hnd hV φ he halt _).2
        (mem_inf.2 ⟨ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hd, hdz⟩)
    have h1 : ρ₁ ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hd⟩ = 1 := Equiv.ext fun w => by
      rw [ptAct_of_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt hd, h0, zero_add]
      rfl
    have h2 := MonoidHom.mem_ker.2 h1
    rw [ker_ptAct hzC hsup hinf hz hb hnd hV φ he halt, mem_subgroupOf] at h2
    exact h2
  · intro x hx
    exact ⟨ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt hx,
      mem_centralizer_singleton_iff.2 (mul_comm_of_isElementaryAbelian hBe hx
        (mem_sup_right (mem_zpowers z)))⟩

@[expose] def trMap (a : 𝔼) : (𝔼 × ZMod 2) × ZMod 2 →+ (𝔼 × ZMod 2) × ZMod 2 :=
  AddMonoidHom.mk' (fun x => ((x.1.1 + x.2 • a, x.1.2 + b x.1.1 a + x.2 * ptQuad e a), x.2))
    fun x y => by
      refine Prod.ext (Prod.ext ?_ ?_) rfl
      · simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, LinearMap.add_apply]
        ring

omit [FiniteDimensional (ZMod 2) V] in
theorem trMap_apply (a : 𝔼) (w : 𝔼) (t s : ZMod 2) :
    trMap a ((w, t), s) = ((w + s • a, t + b w a + s * ptQuad e a), s) :=
  rfl

omit [FiniteDimensional (ZMod 2) V] in
include he in
theorem trMap_grV (a w : 𝔼) : trMap a (grV (ptQuad e) w) = grV (ptQuad e) (w + a) := by
  simp only [trMap, AddMonoidHom.mk'_apply, grV, one_smul, one_mul]
  rw [ptQuad_add he, add_right_comm]

theorem inv_mul_ptHom_mul (d : ptD₁ hzC hsup hinf hz hb hnd hV φ he halt)
    (x : (𝔼 × ZMod 2) × ZMod 2) :
    (d : G)⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd x) * d =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd
        (trMap (Multiplicative.toAdd (ptTr hzC hsup hinf hz hb hnd hV φ he halt d)) x)) := by
  set a := Multiplicative.toAdd (ptTr hzC hsup hinf hz hb hnd hV φ he halt d) with ha
  have hd' : (d : G)⁻¹ ∈ 𝒩₁ := inv_mem (ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2)
  have hact : ∀ w, ρ₁ ⟨(d : G)⁻¹, hd'⟩ w = w + a := by
    intro w
    have h : (⟨(d : G)⁻¹, hd'⟩ : 𝒩₁) =
        (⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt d.2⟩ : 𝒩₁)⁻¹ := rfl
    rw [h, map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_eq, ptAct_eq_ptTr_add, ← ha,
      add_comm w a, ← add_assoc, add_self_eq_zero_zmod_two, zero_add]
  have hext : (MulAut.conj (d : G)⁻¹).toMonoidHom.comp (ptHom he hb φ hzC hz) =
      (ptHom he hb φ hzC hz).comp (AddMonoidHom.toMultiplicative (trMap a)) := by
    refine hom_ext_grV (polarBilin_ptQuad he) (restrict_ptE₂_ptF₂ he) fun w => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, trMap_grV he]
    have h := ptGr_ptAct hzC hsup hinf hz hb hnd hV φ he halt ⟨(d : G)⁻¹, hd'⟩ w
    rw [hact] at h
    exact h.symm
  have h := congrArg (fun f => f (Multiplicative.ofAdd x)) hext
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd] at h
  exact h

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
