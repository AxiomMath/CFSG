module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65A7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Y
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Pump
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327Proof

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Hom

variable {G : Type} [Group G] [Finite G]

theorem exists_bar_hom {C I : Subgroup G} (hIC : I ≤ C) :
    ∃ f : ↥I →* ↥((I.subgroupOf C).map (barMk ↥C)), Function.Surjective f ∧
      Odd (Nat.card f.ker) ∧ ∀ i : ↥I, ((f i : _) : barQ ↥C) = barMk ↥C ⟨(i : G), hIC i.2⟩ := by
  let f : ↥I →* ↥((I.subgroupOf C).map (barMk ↥C)) :=
    (((barMk ↥C).comp (Subgroup.inclusion hIC)).codRestrict _
      (fun i => ⟨⟨(i : G), hIC i.2⟩, i.2, rfl⟩))
  refine ⟨f, ?_, ?_, fun i => rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨(x : G), hx⟩, rfl⟩
  · let ι : f.ker →* ((barMk ↥C).domRestrict (I.subgroupOf C)).ker :=
      { toFun := fun i => ⟨⟨⟨(i.1 : G), hIC i.1.2⟩, i.1.2⟩, by
          have := i.2
          rw [MonoidHom.mem_ker] at this ⊢
          have h2 := congrArg Subtype.val this
          exact h2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective ι := by
      intro a b hab
      have h1 : ((a.1 : ↥I) : G) = ((b.1 : ↥I) : G) :=
        congrArg (fun x => (((x.1 : ↥(I.subgroupOf C)) : ↥C) : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    exact (CFSG.ComponentClassification.OddKernel.odd_card_restriction_kernel (barMk ↥C) odd_card_ker_barMk
      (I.subgroupOf C)).of_dvd_nat (Subgroup.card_dvd_of_injective ι hinj)

end Hom

theorem alt7_simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt7_nonab : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 7)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  exact hnc ⟨⟨fun a b => hcon a b⟩⟩

namespace Cfg65

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem barK₁_doubleCover (hd : IsDoubleCoverOfAlt (HatT K₁) 7) :
    IsDoubleCoverOfAlt ↥((K₁.subgroupOf (centralizer ({z} : Set G))).map
      (barMk ↥(centralizer ({z} : Set G)))) 7 := by
  have hK₁ : IsPCompIn 2 (centralizer ({z} : Set G)) K₁ := h.std.comp_isPCompIn (Or.inl rfl)
  have hsub : (K₁.subgroupOf (centralizer ({z} : Set G))).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      (isPCompIn_two_iff.mp hK₁).2.1 Subgroup.IsSubnormal.top
  obtain ⟨e₁⟩ := hat_equiv_subgroupOf (isPCompIn_two_iff.mp hK₁).1
  obtain ⟨e₂⟩ := hat_equiv_map (Y := ↥(centralizer ({z} : Set G))) hsub
  exact isDoubleCoverOfAlt_of_mulEquiv (e₁.trans e₂) hd

theorem z_side_a7 (hII : II4_4_4_center) (hd : IsDoubleCoverOfAlt (HatT K₁) 7) :
    Nonempty (↥(((IDiag t K₁).subgroupOf (centralizer ({z} : Set G))).map
      (barMk ↥(centralizer ({z} : Set G)))) ≃* alternatingGroup (Fin 7)) := by
  set C := centralizer ({z} : Set G) with hC
  set π := barMk ↥C with hπ
  have hint : IsIntrinsic z K₁ := intrinsic_of_comp (h.m4 hII) h.std (Or.inl rfl)
  have htC : t ∈ C := h.t_mem_cent hII
  obtain ⟨hAB, hΔ⟩ := IG327B.IG_bar h.orderOf_t (h.t_comm hII).symm hint h.t_not_normalizer htC
  set Ab : Subgroup (barQ ↥C) := (K₁.subgroupOf C).map π with hAb
  have hdc := h.barK₁_doubleCover hd
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hz1 : z ∈ K₁ := (h.m4 hII).z_mem_comp (Or.inl rfl)
  set zb : barQ ↥C := π ⟨z, hzC⟩ with hzb
  have hzbAb : zb ∈ Ab := ⟨⟨z, hzC⟩, hz1, rfl⟩
  have hzcen : ∀ y : barQ ↥C, y * zb = zb * y := by
    intro y
    obtain ⟨y', rfl⟩ := barMk_surjective y
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 y'.2
  have hzo : orderOf zb = 2 := orderOf_barMk (orderOf_mk_centralizer hzC h.std.orderOf_z)
  have hzb2 : zb * zb = 1 := mul_self_eq_one_of_orderOf_eq_two hzo
  set zA : ↥Ab := ⟨zb, hzbAb⟩ with hzA
  have hzAo : orderOf zA = 2 := by rw [hzA, Subgroup.orderOf_mk]; exact hzo
  have hzAc : zA ∈ center ↥Ab := Subgroup.mem_center_iff.2 fun g => Subtype.ext (hzcen _)
  have hzp : zpowers zA = center ↥Ab := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzAc) ?_
    rw [Nat.card_zpowers, hzAo, hdc.2.1]
  have htcen : (π ⟨t, htC⟩)⁻¹ * zb * π ⟨t, htC⟩ = zb := by
    have := hzcen ((π ⟨t, htC⟩)⁻¹)
    rw [this]
    group
  have hker : (swapDiag hAB).ker = center ↥Ab := by
    refine le_antisymm (ker_swapDiag_le_center hAB) ?_
    rw [← hzp, Subgroup.zpowers_le]
    rw [MonoidHom.mem_ker, swapDiag_apply, htcen]
    exact hzb2
  obtain ⟨eA⟩ := hdc.2.2
  let e1 : ↥Ab ⧸ (swapDiag hAB).ker ≃* ↥(swapDiag hAB).range :=
    QuotientGroup.quotientKerEquivRange (swapDiag hAB)
  let e2 : ↥Ab ⧸ (swapDiag hAB).ker ≃* ↥Ab ⧸ center ↥Ab := QuotientGroup.quotientMulEquivOfEq hker
  exact ⟨(MulEquiv.subgroupCongr hΔ).trans (e1.symm.trans (e2.trans eA))⟩

theorem ABar_a7 (hII : II4_4_4_center) (h327 : IG_3_27) (hB2 : B_B2_g4)
    (hd : IsDoubleCoverOfAlt (HatT K₁) 7) :
    Nonempty (↥(ABar (IDiag t K₁) (t * z)) ⧸ center ↥(ABar (IDiag t K₁) (t * z)) ≃*
      alternatingGroup (Fin 7)) ∧ Odd (Nat.card (center ↥(ABar (IDiag t K₁) (t * z)))) := by
  have hI := h.I_isPCompIn hII h327
  have hIz : IDiag t K₁ ≤ centralizer ({z} : Set G) := hI.1.trans inf_le_left
  have hIw : IDiag t K₁ ≤ centralizer ({t * z} : Set G) := hI.1.trans inf_le_right
  obtain ⟨f₁, hf₁s, hf₁o, -⟩ := exists_bar_hom hIz
  obtain ⟨f₂, hf₂s, hf₂o, -⟩ := exists_bar_hom hIw
  obtain ⟨eΔ⟩ := h.z_side_a7 hII hd
  have hQ₁ : IsSimpleGroup ↥(((IDiag t K₁).subgroupOf (centralizer ({z} : Set G))).map
      (barMk ↥(centralizer ({z} : Set G)))) := eΔ.isSimpleGroup_congr.2 alt7_simple
  have hQ₁n : ∃ a b : ↥(((IDiag t K₁).subgroupOf (centralizer ({z} : Set G))).map
      (barMk ↥(centralizer ({z} : Set G)))), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt7_nonab
    refine ⟨eΔ.symm a, eΔ.symm b, fun h' => hab ?_⟩
    have := congrArg eΔ h'
    simpa using this
  obtain ⟨g, hgs, hgo, -⟩ := exists_odd_cover_of_two_quotients f₁ f₂ hf₁s hf₂s hf₁o hf₂o hQ₁ hQ₁n
  have hAcomp := ABar_isComponent h.std.simple h.std.gen4 hB2 h.std.orderOf_z
    (h.orderOf_tz hII) (h.z_mem_cent_tz hII) hI
  have hAle := ABar_le_centralizer h.std.orderOf_z (h.z_mem_cent_tz hII) hI
  have hAq : IsQuasisimple ↥(ABar (IDiag t K₁) (t * z)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAle) hAcomp.1
  obtain ⟨-, ⟨e⟩, hodd⟩ := quasisimple_quot_of_odd_cover hAq hQ₁ hQ₁n g hgs hgo
  exact ⟨⟨e.trans eΔ⟩, hodd⟩

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
