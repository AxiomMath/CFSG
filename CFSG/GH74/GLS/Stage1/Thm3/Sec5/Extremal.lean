module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Transport
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem commBar_conj {c w : G} (hc : c ∈ Cz z) (hw : w ∈ commBar z) : c * w * c⁻¹ ∈ commBar z :=
  conj_mem_sup_of (fun _ hw => conj_mem_commutator_self hc hw) (fun _ hw => Oz_conj hc hw) hw

omit [Finite G] in
theorem conj_mem_zpowers {c : G} (hc : c ∈ Cz z) {w : G} (hw : w ∈ zpowers z) :
    c * w * c⁻¹ = w := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hcz : Commute c z := Subgroup.mem_centralizer_singleton_iff.1 hc
  exact (hcz.zpow_right n).mul_inv_cancel

theorem exists_extremal (hII : II4_4_4_center) (h15 : IG_15_16_ext) (hE : P_normal_four)
    (hC : Cfg5 G z S K₁ K₂) {a : G} (ha : Elt5 G z S K₁ K₂ a) (hcomm : a ∈ commBar z) :
    ∃ a' x : G, Ctr5 G z S K₁ K₂ a' x := by
  have hM := m4_of_std hII hC.std
  obtain ⟨x, hxP, hx2, hxz, hxn⟩ := hE G z S K₁ K₂ hC
  have hz2 : orderOf z = 2 := hC.std.orderOf_z
  have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two hz2
  have hz' : ∀ s ∈ S, s * z * s⁻¹ = z := fun s hs => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (S_le_Cz hM hs)
    rw [this]; group
  have hidx := relIndex_centralizer_le_two hz' hz2' hz1 hxn
  obtain ⟨c, hcC, hcQ, hcext⟩ := h15 G (Cz z) S (S ⊓ centralizer ({x} : Set G)) (Oz z) a
    hC.std.sylow inf_le_left hidx (TwoThin.pPrimeCoreOf_le (Cz z)) (fun y hy n hn => Oz_conj hy hn)
    card_Oz_odd ha.mem ha.inv hcomm
  refine ⟨c⁻¹ * a * c, x, ?_⟩
  have hf1 : InducesFAut (c⁻¹ * a * c⁻¹⁻¹) (K₁.map (MulAut.conj c⁻¹).toMonoidHom) :=
    inducesFAut_conj c⁻¹ ha.f₁
  have hf2 : InducesFAut (c⁻¹ * a * c⁻¹⁻¹) (K₂.map (MulAut.conj c⁻¹).toMonoidHom) :=
    inducesFAut_conj c⁻¹ ha.f₂
  rw [inv_inv] at hf1 hf2
  have e1 : K₁.map (MulAut.conj c⁻¹).toMonoidHom = M.cj K₁ c := (cj_eq_conjugate K₁ c).symm
  have e2 : K₂.map (MulAut.conj c⁻¹).toMonoidHom = M.cj K₂ c := (cj_eq_conjugate K₂ c).symm
  rw [e1] at hf1
  rw [e2] at hf2
  have hFA : InducesFAut (c⁻¹ * a * c) K₁ ∧ InducesFAut (c⁻¹ * a * c) K₂ := by
    rcases hM.perm c hcC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hf1; rw [h2] at hf2; exact ⟨hf1, hf2⟩
    · rw [h1] at hf1; rw [h2] at hf2; exact ⟨hf2, hf1⟩
  refine ⟨hC, ⟨hcQ.1, ?_, ?_, hFA.1, hFA.2⟩, ?_, hcext, hxP, hx2, hxz, hxn, ?_⟩
  · have := orderOf_conj_eq c⁻¹ a
    rw [inv_inv] at this
    rw [this]; exact ha.inv
  · intro hmem
    apply ha.ne
    have := conj_mem_zpowers hcC hmem
    have e : c * (c⁻¹ * a * c) * c⁻¹ = a := by group
    rw [e] at this
    rw [this]; exact hmem
  · have := commBar_conj (inv_mem hcC) hcomm
    rwa [inv_inv] at this
  · exact (Subgroup.mem_centralizer_singleton_iff.1 hcQ.2)

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
