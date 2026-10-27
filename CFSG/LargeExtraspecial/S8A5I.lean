module

public import CFSG.LargeExtraspecial.S8A5B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

universe u

theorem commutator_orthogonalGroup_eq_omegaGroup_minus_four {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      omegaGroup Q hQ := by
  obtain ⟨-, -, -, hidx, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inl h4)
      (fun U hU => hmin U (by rw [hU, h4]))
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  set N := ⁅O, O⁆ with hNdef
  have hNΩ : N ≤ omegaGroup Q hQ := by
    rw [hNdef, Subgroup.commutator_le]
    intro g hg h hh
    have hk : (⟨⁅g, h⁆, Subgroup.commutator_le_self O
        (Subgroup.commutator_mem_commutator hg hh)⟩ : O) ∈ (dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨⁅g, h⁆, Subgroup.commutator_le_self O
          (Subgroup.commutator_mem_commutator hg hh)⟩ : O) = ⁅(⟨g, hg⟩ : O), ⟨h, hh⟩⁆ := rfl
      rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hΩ2 := relIndex_omegaGroup Q hQ
  have hΩO : omegaGroup Q hQ ≤ O := omegaGroup_le Q hQ
  have hrel := Subgroup.relIndex_mul_relIndex N (omegaGroup Q hQ) O hNΩ hΩO
  have hidx' : N.relIndex O = 2 := hidx
  rw [hΩ2, hidx'] at hrel
  have h1 : N.relIndex (omegaGroup Q hQ) = 1 := by omega
  exact le_antisymm hNΩ (Subgroup.relIndex_eq_one.mp h1)

theorem isSimpleGroup_omegaGroup_minus_four {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    IsSimpleGroup (omegaGroup Q hQ) ∧ ¬ ∀ x y : omegaGroup Q hQ, x * y = y * x := by
  obtain ⟨hS, -, hnc, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inl h4)
      (fun U hU => hmin U (by rw [hU, h4]))
  rw [← commutator_orthogonalGroup_eq_omegaGroup_minus_four hQ h4 hmin]
  exact ⟨hS, hnc⟩

theorem card_omegaGroup_minus_four {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    Nat.card (omegaGroup Q hQ) = 60 := by
  obtain ⟨-, -, -, -, -, h4', -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inl h4)
      (fun U hU => hmin U (by rw [hU, h4]))
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcard⟩ := h4' h4
  rw [hrange, commutator_orthogonalGroup_eq_omegaGroup_minus_four hQ h4 hmin, Nat.card_zmod]
    at hcard
  rw [hcard]
  norm_num

theorem commutatorElement_mul_mul_of_commute {X : Type*} [Group X] {a b z w : X}
    (hza : Commute z a) (hzb : Commute z b) (hwa : Commute w a) (hwb : Commute w b)
    (hzw : Commute z w) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hzc : Commute z (a * b * a⁻¹ * b⁻¹) :=
    ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have hwc : Commute w (a * b * a⁻¹ * b⁻¹) :=
    ((hwa.mul_right hwb).mul_right hwa.inv_right).mul_right hwb.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹ = z * (a * w) * b * a⁻¹ * z⁻¹ * b⁻¹ * w⁻¹ := by
        group
    _ = z * (w * a) * b * a⁻¹ * z⁻¹ * b⁻¹ * w⁻¹ := by rw [← hwa.eq]
    _ = z * w * (a * b * a⁻¹) * (z⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = z * w * (a * b * a⁻¹) * (b⁻¹ * z⁻¹) * w⁻¹ := by rw [(hzb.inv_inv).eq]
    _ = (z * w) * (a * b * a⁻¹ * b⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = w * (z * (a * b * a⁻¹ * b⁻¹) * z⁻¹) * w⁻¹ := by rw [hzw.eq]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hzc.eq, mul_inv_cancel_right, hwc.eq, mul_inv_cancel_right]

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Rbar_le_commutator_sup_Nbar' (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (hs : IsSimpleGroup (RmodN S g t)) (hnab : ¬ ∀ x y : RmodN S g t, x * y = y * x) :
    Rbar S g t ≤ ⁅Rbar S g t, Rbar S g t⁆ ⊔ Nbar S g t := by
  have hnab' : ¬ IsMulCommutative (RmodN S g t) := fun h => hnab fun x y => h.is_comm.comm x y
  have hperf : ⁅RmodN S g t, RmodN S g t⁆ = RmodN S g t := by
    have h1 := CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hs hnab'
    have h2 : (commutator (RmodN S g t)).map (RmodN S g t).subtype =
        ⁅RmodN S g t, RmodN S g t⁆ := by
      rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [← h2, h1, ← MonoidHom.range_eq_map, range_subtype]
  have himg : (commutator (Rbar S g t)).map (resV haQ t) = RmodN S g t := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_resV, hperf]
  intro r hr
  have hmem : resV haQ t ⟨r, hr⟩ ∈ (commutator (Rbar S g t)).map (resV haQ t) := by
    rw [himg, ← range_resV haQ t]
    exact ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨c, hc, hcr⟩ := hmem
  have h1 : resV haQ t (c⁻¹ * ⟨r, hr⟩) = 1 := by rw [map_mul, map_inv, hcr, inv_mul_cancel]
  rw [resV_eq_one_iff] at h1
  have hc' : (c : S.O) ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
    have h2 : (commutator (Rbar S g t)).map (Rbar S g t).subtype = ⁅Rbar S g t, Rbar S g t⁆ := by
      rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [← h2]
    exact ⟨c, hc, rfl⟩
  have e : r = (c : S.O) * ((c⁻¹ * ⟨r, hr⟩ : Rbar S g t) : S.O) := by simp
  rw [e]
  exact mul_mem (mem_sup_left hc') (mem_sup_right h1)

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem eq_t_of_commute_Rbar (D : Std H C ht ht1 hVQ) {σ : S.O}
    (hσR : ∀ r ∈ Rbar S g t, σ * r = r * σ)
    (hσQ : ∀ x : S.Qt, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t)
    (hσW : ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) (hσ1 : σ ≠ 1) : σ = t := by
  have haQ := H.conj_mem
  set χ := chi H C ht ht1 hVQ with hχ
  set ψ₀ : S.Qt →ₗ[ZMod 2] Vt S g t :=
    LinearMap.codRestrict (Vt S g t) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) hσQ with hψ₀
  have hψ₀ap : ∀ x, (ψ₀ x : S.Qt) = (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := fun x => rfl
  have hker : Wt S g t ≤ LinearMap.ker ψ₀ := by
    intro w hw
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [hψ₀ap, hσW w hw, sub_self]
    rfl
  set ψ := (Wt S g t).liftQ ψ₀ hker with hψ
  set f : Vt S g t →ₗ[ZMod 2] Vt S g t := ψ ∘ₗ χ.symm.toLinearMap with hf
  have hfχ : ∀ x : S.Qt, (f (χ (Submodule.Quotient.mk x)) : S.Qt) =
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := by
    intro x
    rw [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hψ,
      Submodule.liftQ_apply, hψ₀ap]
  have hsurj : ∀ v : Vt S g t, ∃ x : S.Qt, χ (Submodule.Quotient.mk x) = v := by
    intro v
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (χ.symm v)
    exact ⟨x, by rw [hx, LinearEquiv.apply_symm_apply]⟩
  have hcomm : ∀ e ∈ omegaGroup D.Q D.hQ, ∀ v, f (e v) = e (f v) := by
    intro e he v
    rw [← D.hX, ← range_resV haQ t] at he
    obtain ⟨r, rfl⟩ := he
    obtain ⟨x, rfl⟩ := hsurj v
    apply Subtype.ext
    rw [← chi_equivariant H C ht ht1 hVQ r x, hfχ, coe_resV_apply, hfχ, map_sub,
      ← coe_mul_apply, ← coe_mul_apply, hσR r r.2]
  have h4 : 4 ≤ finrank (ZMod 2) (Vt S g t) := by have := D.hdim; have := D.hm; omega
  obtain ⟨c, hc⟩ := S2.timmesfeld_2_4_omegaGroup D.hQ h4 hcomm
  have hval : ∀ x : S.Qt, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
      c • ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by
    intro x
    rw [← hfχ, hc, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
      coe_chi_apply_mk]
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    apply hσ1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have := hval x
    rw [zero_smul, sub_eq_zero] at this
    exact this
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have := hval x
    rw [one_smul] at this
    exact sub_left_injective this

theorem eq_t_of_commSpace_eq_of_comm (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) {σ : S.O} (hσM : σ ∈ S.Mbar) (hσt : σ * t = t * σ) (hσ1 : σ ≠ 1)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hcs : commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    (hN : ∀ n ∈ Nbar S g t, n * σ = σ * n) : σ = t := by
  have haQ := H.conj_mem
  have hfix : fixSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = Wt S g t := by
    rw [fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate σ.2, hcs]
    rfl
  have hσW : ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun w hw =>
    mem_fixSpace.mp (hfix ▸ hw)
  have hσQ : ∀ x : S.Qt, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := fun x => by
    rw [← hcs]; exact sub_mem_commSpace _ x
  have hRz : ∀ r ∈ Rbar S g t, r * σ * r⁻¹ * σ⁻¹ ∈ zpowers t := by
    intro r hr
    have hn := comm_mem_Nbar_of_fix H hσM hσt hσV hr
    refine mem_zpowers_of_mem_Nbar_of_fix_Wt H C ht ht1 hVQ D.hgen D.hN0 D.three_le_finrank hn
      fun w hw => ?_
    have hσinv : ((σ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
      conv_lhs => rw [← hσW w hw]
      exact inv_apply_apply_O σ w
    have hrw := apply_mem_Wt H (inv_mem hr) hw
    rw [coe_mul_apply, hσinv, coe_mul_apply, coe_mul_apply, hσW _ hrw, apply_inv_apply_O]
  obtain ⟨hs, hnc⟩ : IsSimpleGroup (RmodN S g t) ∧ ¬ ∀ x y : RmodN S g t, x * y = y * x := by
    rw [D.hX]
    refine isSimpleGroup_omegaGroup_minus_four D.hQ (by rw [D.hdim, hm2]) fun U hU => ?_
    by_contra hcon
    push Not at hcon
    have := hmin U hcon
    omega
  have hperf := Rbar_le_commutator_sup_Nbar' haQ hs hnc
  have htR : ∀ r ∈ Rbar S g t, r * t = t * r := fun r hr => commute_of_mem_Rbar haQ hr
  have hcent : ⁅Rbar S g t, Rbar S g t⁆ ⊔ Nbar S g t ≤
      Rbar S g t ⊓ centralizer ({σ} : Set S.O) := by
    refine sup_le ?_ fun n hn => ⟨Nbar_le_Rbar hn, mem_centralizer_singleton_iff.mpr (hN n hn)⟩
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨Subgroup.commutator_mem_commutator ha hb |> fun h =>
      Subgroup.commutator_le_self _ h, mem_centralizer_singleton_iff.mpr ?_⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hRz a ha)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hRz b hb)
    have hza : σ * a * σ⁻¹ = (t ^ i)⁻¹ * a := by
      have : a * σ * a⁻¹ * σ⁻¹ = t ^ i := hi.symm
      calc σ * a * σ⁻¹ = (a * σ * a⁻¹ * σ⁻¹)⁻¹ * a := by group
        _ = (t ^ i)⁻¹ * a := by rw [this]
    have hzb : σ * b * σ⁻¹ = (t ^ j)⁻¹ * b := by
      have : b * σ * b⁻¹ * σ⁻¹ = t ^ j := hj.symm
      calc σ * b * σ⁻¹ = (b * σ * b⁻¹ * σ⁻¹)⁻¹ * b := by group
        _ = (t ^ j)⁻¹ * b := by rw [this]
    have hta : Commute t a := (Commute.symm (htR a ha))
    have htb : Commute t b := (Commute.symm (htR b hb))
    have e : σ * ⁅a, b⁆ * σ⁻¹ = ⁅a, b⁆ := by
      have h1 : σ * ⁅a, b⁆ * σ⁻¹ = ⁅σ * a * σ⁻¹, σ * b * σ⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [h1, hza, hzb]
      exact commutatorElement_mul_mul_of_commute (hta.zpow_left i).inv_left
        (htb.zpow_left i).inv_left (hta.zpow_left j).inv_left (htb.zpow_left j).inv_left
        (((Commute.refl t).zpow_zpow i j).inv_left.inv_right)
    calc ⁅a, b⁆ * σ = σ * ⁅a, b⁆ * σ⁻¹ * σ := by rw [e]
      _ = σ * ⁅a, b⁆ := by group
  have hσR : ∀ r ∈ Rbar S g t, σ * r = r * σ := fun r hr =>
    (mem_centralizer_singleton_iff.mp (hcent (hperf hr)).2).symm
  exact eq_t_of_commute_Rbar D hσR hσQ hσW hσ1

theorem apply_sub_mem_Vt_of_comm_Nbar (D : Std H C ht ht1 hVQ) {σ : S.O} (hσM : σ ∈ S.Mbar)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hN : ∀ n ∈ Nbar S g t, n * σ = σ * n) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) {p : S.Qt}
    (hp : p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g))) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ Vt S g t := by
  have haQ := H.conj_mem
  have Hk := H.mul k
  have Ck := C.mul k
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hVQk := not_V_le_Qa_mul H hVQ hk
  have hakQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k.2 haQ
  have hcV : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t := cl_mem_Vt htk
  have hσc := hσV _ hcV
  have hfixA := clSub_inf_fixSub_Abar Hk Ck htk ht1 hVQk (card_Abar_mul H hk D.hA)
  rw [Nbar_mul, Vt_mul] at hfixA
  have hσp : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) :=
    apply_mem_clSub_of_apply_cl_eq hakQ (conj_ne_z' S k.2 H.conj_ne) hσM hσc hp
  have hmem : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓
      fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t) := by
    refine ⟨Submodule.sub_mem _ hσp hp, (mem_fixSub S).mpr fun α hα => ?_⟩
    have hαp := Lbar_apply_sub_mem_span' hakQ hp hα.1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hαp
    have hασ : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) p) =
        (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) p) := by
      rw [← coe_mul_apply, ← coe_mul_apply, hN α hα.2]
    have hαp' : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) p =
        p + c • S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
      rw [hc]; abel
    rw [map_sub, hασ, hαp', map_add, map_smul, hσc]
    abel
  rw [hfixA] at hmem
  exact hmem.2

theorem not_comm_Nbar_of_bad (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ) (hσ1 : σ ≠ t)
    (hbad : ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    ¬ ∀ n ∈ Nbar S g t, n * σ = σ * n := by
  intro hN
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hσV := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7 σ ⟨hσM, hσt, x, hxM, hxσ⟩
  have htop := eq_top_of_le H C ht ht1 hVQ (K := (Vt S g t).comap
    ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) (fun w hw => Submodule.mem_comap.mpr (hbad w hw))
    (fun k hk p hp => Submodule.mem_comap.mpr (apply_sub_mem_Vt_of_comm_Nbar D hσM hσV hN hk hp))
  have hle : commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t := by
    intro v hv
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hv
    have hy : y ∈ (Vt S g t).comap ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) := by
      rw [htop]; exact Submodule.mem_top
    exact hy
  have hdimσ : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxσ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hcs := Submodule.eq_of_le_of_finrank_eq hle hdimσ
  have hσ1' : σ ≠ 1 := by
    rintro rfl
    have h1 := cl_a_mem_Vt ht
    rw [← hcs] at h1
    obtain ⟨y, hy⟩ := mem_commSpace.mp h1
    rw [OneMemClass.coe_one, LinearEquiv.coe_one, id_eq, sub_self] at hy
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne hy.symm
  exact hσ1 (eq_t_of_commSpace_eq_of_comm D hm2 hmin hσM hσt hσ1' hσV hcs hN)

theorem exists_Nbar_conj_eq_mul_of_bad (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ) (hσ1 : σ ≠ t)
    (hbad : ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    ∃ n ∈ Nbar S g t, n * σ * n⁻¹ = σ * t := by
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hσV := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7 σ ⟨hσM, hσt, x, hxM, hxσ⟩
  have hnc := not_comm_Nbar_of_bad hCE hNo hΩ D hm2 hmin hA7 hxM hxσ hσt hσ1 hbad
  push Not at hnc
  obtain ⟨n, hn, hne⟩ := hnc
  have hz := comm_mem_zpowers_of_mem_Nbar H C ht ht1 hVQ D.hgen D.hN0 D.three_le_finrank D.hN
    hσM hσt hσV hbad hn
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hz' : n * σ * n⁻¹ * σ⁻¹ ∈ zpowers t := by
    have := inv_mem hz
    rwa [show (σ * n * σ⁻¹ * n⁻¹)⁻¹ = n * σ * n⁻¹ * σ⁻¹ by group] at this
  rcases eq_one_or_eq_of_mem_zpowers htt hz' with h | h
  · exfalso
    apply hne
    calc n * σ = n * σ * n⁻¹ * σ⁻¹ * (σ * n) := by group
      _ = σ * n := by rw [h, one_mul]
  · refine ⟨n, hn, ?_⟩
    calc n * σ * n⁻¹ = n * σ * n⁻¹ * σ⁻¹ * σ := by group
      _ = t * σ := by rw [h]
      _ = σ * t := hσt.symm

end CFSG.LargeExtraspecial.S8
