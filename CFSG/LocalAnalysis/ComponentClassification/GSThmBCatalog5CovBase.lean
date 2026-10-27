module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.GH74.KGroups.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open Subgroup

@[expose] def SmallQ (Y : Type) [Group Y] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel Y .PSL 2 p f) ∨
    Nonempty (Y ≃* alternatingGroup (Fin 7))

theorem card_of_smallQ {Y : Type} [Group Y] (h : SmallQ Y) :
    (∃ q, Nat.card Y = Open.ordA 1 q) ∨ Nat.card Y = 2520 := by
  rcases h with ⟨p, f, -, hp2, -, -, hm⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨p ^ f, (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hm)).1 rfl⟩
  · exact Or.inr ((Nat.card_congr e.toEquiv).trans card_alternatingGroup_seven)

theorem ordA_one_ne_of_lt {N B : ℕ} (hB : 2 * (N + 1) ≤ B * (B ^ 2 - 1))
    (hsmall : ∀ m < B, m * (m ^ 2 - 1) / Nat.gcd 2 (m - 1) ≠ N) (m : ℕ) :
    Open.ordA 1 m ≠ N := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge m B with hm | hm
  · exact hsmall m hm
  · have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (N + 1) ≤ m * (m ^ 2 - 1) := by
      refine hB.trans (Nat.mul_le_mul hm (Nat.sub_le_sub_right ?_ 1))
      exact Nat.pow_le_pow_left hm 2
    exact (lt_div_of_mul_succ_le hg hle hX).ne'

theorem false_of_component_top {G : Type} [Group G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) {M : Subgroup G}
    (hM : CFSG.Assembly.IsComponentOf M ⊤) (hMt : SmallQ (↥M ⧸ center ↥M))
    (hq : ∀ q, Open.ordA 1 q ≠ Nat.card G) (h7 : Nat.card G ≠ 2520) : False := by
  obtain ⟨hGq, hGZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    le_top).1 hM
  have hMq : CFSG.IsQuasisimple ↥M :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hM.2.2
  have htopq : CFSG.IsQuasisimple ↥(⊤ : Subgroup G) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).2 hGq
  have hZtop : center ↥(⊤ : Subgroup G) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv (G := G))
    rw [hGZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).1 h1
  have hMtop : M = ⊤ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups htopq hc.2 with
      h | h
    · rw [← Subgroup.map_subgroupOf_eq_of_le (le_top : M ≤ ⊤), h, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · exfalso
      rw [hZtop, le_bot_iff] at h
      have hbot : M = ⊥ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le (le_top : M ≤ ⊤), h, Subgroup.map_bot]
      obtain ⟨-, -, a, b, hab⟩ := hMq
      apply hab
      have : Subsingleton ↥M := by rw [hbot]; infer_instance
      exact Subsingleton.elim _ _
  subst hMtop
  have hcard : Nat.card (↥(⊤ : Subgroup G) ⧸ center ↥(⊤ : Subgroup G)) = Nat.card G :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZtop).trans
      QuotientGroup.quotientBot).toEquiv).trans (Nat.card_congr Subgroup.topEquiv.toEquiv)
  rcases card_of_smallQ hMt with ⟨q, hq'⟩ | h'
  · exact hq q (hq'.symm.trans hcard)
  · exact h7 (hcard.symm.trans h')

theorem eq_conj_of_comp {L X : Type*} [Group L] [Group X] (hL : Group.IsPerfect L)
    (π : L →* X) (hker : π.ker ≤ center L) (α : MulAut L) (x : L)
    (h : ∀ y, π (α y) = π x * π y * (π x)⁻¹) : α = MulAut.conj x := by
  apply CFSG.GH74.KGroups.inducedHom_injective hL
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [CFSG.GH74.KGroups.inducedHom_mk, CFSG.GH74.KGroups.inducedHom_mk, QuotientGroup.eq]
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group

theorem fixSub_eq_of_inner {L X : Type*} [Group L] [Group X] (π : L →* X)
    (hπ : Function.Surjective π) (α : MulAut L) (β : MulAut X) (hβ : ∀ x, π (α x) = β (π x))
    (Y : L) (hY : ∀ y, α y = Y * y * Y⁻¹) :
    CFSG.Sporadic.Schreier.fixSub β = centralizer ({π Y} : Set X) := by
  have hβc : ∀ z, β z = π Y * z * (π Y)⁻¹ := by
    intro z
    obtain ⟨y, rfl⟩ := hπ z
    rw [← hβ, hY, map_mul, map_mul, map_inv]
  ext z
  rw [CFSG.Sporadic.Schreier.mem_fixSub, hβc, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * π Y = (π Y * z * (π Y)⁻¹) * π Y := by rw [h]
      _ = π Y * z := by group
  · intro h
    rw [← h]
    group

theorem mul_self_mem_center_of_inner {L : Type*} [Group L] (α : MulAut L) (hα : α * α = 1)
    (Y : L) (hY : ∀ y, α y = Y * y * Y⁻¹) : Y * Y ∈ center L := by
  rw [mem_center_iff]
  intro y
  have h1 : α (α y) = y := by rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  rw [hY, hY] at h1
  calc y * (Y * Y) = (Y * (Y * y * Y⁻¹) * Y⁻¹) * (Y * Y) := by rw [h1]
    _ = Y * Y * y := by group

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {a g : G} (ha : a * a = 1)
    (hg : g ∈ zpowers a) : g = 1 ∨ g = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

section Semi

variable {L : Type*} [Group L] (α : MulAut L)

abbrev Semi : Type _ := L ⋊[(zpowers α).subtype] ↥(zpowers α)

abbrev pElt : Semi α := SemidirectProduct.inr ⟨α, mem_zpowers α⟩

abbrev Lsub : Subgroup (Semi α) := (SemidirectProduct.inl : L →* Semi α).range

instance Lsub_normal : (Lsub α).Normal := by
  rw [Lsub, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

@[expose] noncomputable def eL : L ≃* ↥(Lsub α) :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

instance Semi.finite [Finite L] : Finite (Semi α) := by
  have : Finite (MulAut L) :=
    Finite.of_injective (fun e : MulAut L => (e : L → L)) DFunLike.coe_injective
  exact Finite.of_injective (fun x : Semi α => (x.left, x.right)) fun x y h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem coe_eL (y : L) : ((eL α y : ↥(Lsub α)) : Semi α) = SemidirectProduct.inl y := rfl

theorem pElt_conj (l : L) :
    pElt α * SemidirectProduct.inl l * (pElt α)⁻¹ = SemidirectProduct.inl (α l) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem pElt_mul_self (hα : α * α = 1) : pElt α * pElt α = 1 := by
  rw [← map_mul, ← map_one SemidirectProduct.inr]
  congr 1
  exact Subtype.ext hα

theorem pElt_not_mem (hα1 : α ≠ 1) : pElt α ∉ Lsub α := by
  rw [Lsub, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_inr]
  intro h
  exact hα1 (congrArg Subtype.val h)

theorem orderOf_pElt (hα : α * α = 1) (hα1 : α ≠ 1) : orderOf (pElt α) = 2 := by
  refine orderOf_eq_prime (by rw [sq]; exact pElt_mul_self α hα) ?_
  intro h
  apply pElt_not_mem α hα1
  rw [h]
  exact one_mem _

theorem conj_inl (x : Semi α) (y : L) :
    x * SemidirectProduct.inl y * x⁻¹ =
      SemidirectProduct.inl (x.left * (x.right : MulAut L) y * x.left⁻¹) := by
  have h := SemidirectProduct.inl_aut (φ := (zpowers α).subtype) x.right y
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, map_mul, map_inv, show ((zpowers α).subtype x.right) y =
    (x.right : MulAut L) y from rfl] at *
  rw [h, mul_inv_rev, ← map_inv SemidirectProduct.inr]
  group

theorem centralizer_Lsub (hα : α * α = 1) (hout : ∀ n : L, ¬ ∀ y, α y = n * y * n⁻¹) :
    centralizer ((Lsub α : Subgroup (Semi α)) : Set (Semi α)) =
      (center L).map SemidirectProduct.inl := by
  ext x
  constructor
  · intro hx
    rw [mem_centralizer_iff] at hx
    have hc : ∀ y, x.left * (x.right : MulAut L) y * x.left⁻¹ = y := by
      intro y
      have h1 := hx (SemidirectProduct.inl y) ⟨y, rfl⟩
      apply SemidirectProduct.inl_injective (φ := (zpowers α).subtype)
      rw [← conj_inl, ← h1]
      group
    rcases eq_one_or_eq_of_mem_zpowers hα x.right.2 with h | h
    · have hr : x.right = 1 := Subtype.ext h
      refine ⟨x.left, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_center_iff]
        intro y
        have := hc y
        rw [h, MulAut.one_apply] at this
        calc y * x.left = (x.left * y * x.left⁻¹) * x.left := by rw [this]
          _ = x.left * y := by group
      · rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one]
        rfl
    · exfalso
      apply hout x.left⁻¹
      intro y
      have := hc y
      rw [h] at this
      rw [inv_inv]
      calc α y = x.left⁻¹ * (x.left * α y * x.left⁻¹) * x.left := by group
        _ = x.left⁻¹ * y * x.left := by rw [this]
  · rintro ⟨n, hn, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mem_center_iff.mp hn y]

end Semi

end CFSG.ComponentClassification.GSThmB.Cov
