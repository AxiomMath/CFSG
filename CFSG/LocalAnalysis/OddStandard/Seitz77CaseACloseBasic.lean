module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseADefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGen
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

theorem isElemAbelian_of_forall_two {G : Type*} [Group G] {E : Subgroup G}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by rw [sq]; exact hsq x hx⟩

theorem comm_of_isElemAbelian_two {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

namespace SylowA

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F} {φ : G → RingAut F}
  (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

theorem W_le_S₁ : W ≤ S₁ := S.W_le_S₀.trans S.S₀_le_S₁

theorem normal_W {s w : G} (hs : s ∈ S₁) (hw : w ∈ W) : s * w * s⁻¹ ∈ W :=
  (mem_normalizer_iff.mp (S.sylow_S₁.le hs) w).mp hw

theorem ι_one : ι 1 = 0 := by
  have h := S.ι_add 1 (one_mem W) 1 (one_mem W)
  rw [mul_one] at h
  exact add_left_cancel (a := ι 1) (by rw [add_zero]; exact h.symm)

theorem mul_self_of_mem_W {w : G} (hw : w ∈ W) : w * w = 1 := by
  apply S.ι_inj (w * w) (W.mul_mem hw hw) 1 (one_mem W)
  rw [S.ι_add w hw w hw, S.ι_one]
  exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)

theorem comm_of_mem_W {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W) : w * w' = w' * w :=
  S.ι_inj _ (W.mul_mem hw hw') _ (W.mul_mem hw' hw) (by
    rw [S.ι_add w hw w' hw', S.ι_add w' hw' w hw, add_comm])

theorem isElemAbelian_W : IsElemAbelian 2 W :=
  isElemAbelian_of_forall_two (fun _ hx _ hy => S.comm_of_mem_W hx hy)
    (fun _ hx => S.mul_self_of_mem_W hx)

theorem card_W : Nat.card W = 2 ^ 8 := by
  have hbij : Function.Bijective (fun w : W => ι (w : G)) :=
    ⟨fun a b h => Subtype.ext (S.ι_inj a a.2 b b.2 h), fun p => by
      obtain ⟨w, hw, hwp⟩ := S.ι_surj p
      exact ⟨⟨w, hw⟩, hwp⟩⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, S.card_F]
  norm_num

theorem commute_iff {s w : G} (hs : s ∈ S₀) (hw : w ∈ W) :
    s * w = w * s ↔ κ s * (ι w).2 = 0 := by
  have h1 := S.conj_ι s hs w hw
  constructor
  · intro hc
    have h2 : s * w * s⁻¹ = w := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
    rw [h2] at h1
    have h3 := congrArg Prod.fst h1
    simp only at h3
    linear_combination -h3
  · intro hz
    have h2 : s * w * s⁻¹ = w :=
      S.ι_inj _ (S.normal_W (S.S₀_le_S₁ hs) hw) w hw (by rw [h1, hz, add_zero])
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2

theorem mem_W₀_iff {w : G} : w ∈ W₀ ↔ w ∈ W ∧ (ι w).2 = 0 := by
  rw [S.W₀_eq, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨hw, hc⟩
    refine ⟨hw, ?_⟩
    obtain ⟨s, hs, hκ⟩ := S.κ_surj 1
    have := (S.commute_iff hs hw).1 (hc s hs)
    rwa [hκ, one_mul] at this
  · rintro ⟨hw, hy⟩
    exact ⟨hw, fun s hs => (S.commute_iff hs hw).2 (by rw [hy, mul_zero])⟩

theorem W₀_le_W : W₀ ≤ W := fun _ hw => (S.mem_W₀_iff.1 hw).1

theorem commute_of_mem_W₀ {s w : G} (hs : s ∈ S₀) (hw : w ∈ W₀) : s * w = w * s := by
  have h := hw
  rw [S.W₀_eq] at h
  exact mem_centralizer_iff.mp h.2 s hs

theorem inf_centralizer_eq_W₀ {s : G} (hs : s ∈ S₀) (hsW : s ∉ W) :
    W ⊓ centralizer ({s} : Set G) = W₀ := by
  have hκ : κ s ≠ 0 := fun h => hsW ((S.κ_eq_zero_iff s hs).1 h)
  ext w
  rw [mem_inf, mem_centralizer_singleton_iff, S.mem_W₀_iff]
  refine and_congr_right fun hw => ?_
  rw [eq_comm, S.commute_iff hs hw, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hκ, Or.inr⟩

theorem card_W₀ : Nat.card W₀ = 16 := by
  have hbij : Function.Bijective (fun w : W₀ => (ι (w : G)).1) := by
    refine ⟨fun a b h => Subtype.ext ?_, fun x => ?_⟩
    · have ha := (S.mem_W₀_iff.1 a.2)
      have hb := (S.mem_W₀_iff.1 b.2)
      exact S.ι_inj _ ha.1 _ hb.1 (Prod.ext h (by rw [ha.2, hb.2]))
    · obtain ⟨w, hw, hwp⟩ := S.ι_surj (x, 0)
      exact ⟨⟨w, S.mem_W₀_iff.2 ⟨hw, by rw [hwp]⟩⟩, by simp [hwp]⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), S.card_F]

variable [Finite G]

theorem card_S₀ : Nat.card S₀ = 2 ^ 12 := by
  have h := card_eq_card_fiber_mul_ncard_image S₀ (fun x => Multiplicative.ofAdd (κ x))
    (fun x hx y hy => by rw [S.κ_add x hx y hy, ofAdd_add])
  have hfib : Nat.card {x : G // x ∈ S₀ ∧ Multiplicative.ofAdd (κ x) = 1} = Nat.card W := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [ofAdd_eq_one]
    constructor
    · rintro ⟨hx, h0⟩
      exact (S.κ_eq_zero_iff x hx).1 h0
    · intro hx
      exact ⟨S.W_le_S₀ hx, (S.κ_eq_zero_iff x (S.W_le_S₀ hx)).2 hx⟩
  have himg : (fun x => Multiplicative.ofAdd (κ x)) '' (S₀ : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨s, hs, hsb⟩ := S.κ_surj (Multiplicative.toAdd b)
    exact ⟨s, hs, by show Multiplicative.ofAdd (κ s) = b; rw [hsb]; rfl⟩
  rw [himg, Set.ncard_univ, hfib, S.card_W] at h
  have h2 : Nat.card (Multiplicative F) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, S.card_F]
  rw [h2] at h
  rw [h]
  norm_num

theorem card_inf_centralizer_ge {x : G} (hx : x ∈ S₀) :
    256 ≤ Nat.card ↥(S₀ ⊓ centralizer ({x} : Set G)) := by
  set f : G → G := fun s => x * s * x⁻¹ * s⁻¹ with hf
  have hmul : ∀ s ∈ S₀, ∀ s' ∈ S₀, f (s * s') = f s * f s' := by
    intro s hs s' hs'
    have hc : s * f s' = f s' * s := S.commute_of_mem_W₀ hs (S.comm_mem_W₀ x hx s' hs')
    have e1 : s * f s' * s⁻¹ = f s' := by rw [hc]; group
    calc f (s * s') = f s * (s * f s' * s⁻¹) := by simp only [hf]; group
      _ = f s * f s' := by rw [e1]
  have himg : (f '' (S₀ : Set G)).ncard ≤ 16 := by
    have hsub : f '' (S₀ : Set G) ⊆ (W₀ : Set G) := by
      rintro _ ⟨s, hs, rfl⟩
      exact S.comm_mem_W₀ x hx s hs
    calc (f '' (S₀ : Set G)).ncard ≤ (W₀ : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 16 := by rw [← Nat.card_coe_set_eq]; exact S.card_W₀
  have hk := le_card_fiber_of_partial_hom S₀ f hmul (a := 2 ^ 12) (b := 16)
    (by rw [S.card_S₀]) himg
  have hfib : Nat.card {y : G // y ∈ S₀ ∧ f y = 1} =
      Nat.card ↥(S₀ ⊓ centralizer ({x} : Set G)) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ?_
    simp only [hf]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  rw [hfib] at hk
  omega

end SylowA

end CFSG.OddStandard.Seitz77
