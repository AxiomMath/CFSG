module

public import CFSG.GF2Type.SmithTypeE.E7.E23aModel
public import CFSG.GF2Type.SmithTypeE.E7.Qa
public import CFSG.GF2Type.SmithTypeE.E7.IdentFusion
public import CFSG.LargeExtraspecial.S14SMJLoc
public import CFSG.GF2Type.SmithTypeE.DMod.RhoTD6
public import CFSG.GF2Type.SmithTypeE.E7.ModDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.SmithD6 (wt ea7Bits)
open CFSG.GF2Type.SmithTypeE.DMod
open Module (finrank)
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

theorem cqx_eq_cent2_E7 (h25 : SmithE7E25) (h34a : SmithE7E34a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {t u : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (huQ : u ∉ S.QG) (h3 : orderOf (t * u) = 3) :
    S.QG ⊓ centralizer ({t * u} : Set G) = S.QG ⊓ cent2 t u := by
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  · obtain ⟨hqQ, hqθ⟩ := mem_inf.mp hq
    have hqθ' : q * (t * u) = t * u * q := mem_centralizer_singleton_iff.mp hqθ
    have htt : t * t = 1 := SmithQ.mul_self_eq_one_of_isConj S ht
    set v := S.cl q with hv
    have h1 : S.rhoL htM (S.rhoL huM v) = v := by
      rw [hv, S.rhoL_cl huM hqQ, S.rhoL_cl htM (S.conj_mem_QG huM hqQ)]
      congr 1
      calc t * (u * q * u⁻¹) * t⁻¹ = (q * (t * u)) * (t * u)⁻¹ := by rw [hqθ']; group
        _ = q := by group
    have h2 : S.rhoL htM v = S.rhoL huM v := by
      conv_lhs => rw [← h1]
      exact SMJ.rhoL_rhoL S htM htt _
    obtain ⟨-, h3p, -⟩ := h25 G S hw hU t u ht hu htM huM htQ huQ (SMJ.mul_not_mem_QG S h3)
    have hbot := h3p (by rw [← h3, pow_orderOf_eq_one]; exact S.QG.one_mem)
    have hmem : S.rhoL htM v - v ∈ S.commQt t ⊓ S.commQt u := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [S.commQt_of_mem htM]
        exact mem_commSpace.mpr ⟨v, rfl⟩
      · rw [S.commQt_of_mem huM, h2]
        exact mem_commSpace.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    have hmem' : S.rhoL huM v = v := h2 ▸ hmem
    have hfixt : S.cl q ∈ S.fixQt t := by
      rw [S.cl_mem_fixQt_iff htM hqQ, ← S.rhoL_cl htM hqQ]
      exact hmem
    have hfixu : S.cl q ∈ S.fixQt u := by
      rw [S.cl_mem_fixQt_iff huM hqQ, ← S.rhoL_cl huM hqQ]
      exact hmem'
    have hct := S.commute_of_cl_mem_fixQt htM
      (fixQt_eq_of_smithE7E34a h34a S hw hU ht htM htQ) hqQ hfixt
    have hcu := S.commute_of_cl_mem_fixQt huM
      (fixQt_eq_of_smithE7E34a h34a S hw hU hu huM huQ) hqQ hfixu
    exact mem_inf.mpr ⟨hqQ, mem_cent2.mpr ⟨hct.symm, hcu.symm⟩⟩
  · obtain ⟨hqQ, hqc⟩ := mem_inf.mp hq
    obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqc
    exact mem_inf.mpr ⟨hqQ, mem_centralizer_singleton_iff.mpr (hqt.mul_right hqu).eq⟩

theorem isExtraspecialPGroup_cent2_E7 (h25 : SmithE7E25) (h34a : SmithE7E34a) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {t u : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (huQ : u ∉ S.QG) (h3 : orderOf (t * u) = 3)
    (hcard : 2 ^ 17 ≤ Nat.card ↥(S.QG ⊓ cent2 t u)) :
    IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) := by
  have hθM : t * u ∈ S.M := S.M.mul_mem htM huM
  have hθ3 : (t * u) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have heq := cqx_eq_cent2_E7 h25 h34a S hw hU ht hu htM huM htQ huQ h3
  have hfix : fixSpace (S.rhoL hθM) ≠ ⊥ := by
    intro hbot
    have hc := S.card_cqx_of_pow_three hθM hθ3
    rw [hbot, finrank_bot, pow_zero, mul_one, heq] at hc
    rw [hc] at hcard
    norm_num at hcard
  exact CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (MulEquiv.subgroupCongr heq)
    (S.isExtraspecialPGroup_cqx hθM hθ3 hfix)

@[expose] def c16Pos : Fin 16 → Fin 32 :=
  ![2, 3, 4, 5, 8, 9, 14, 15, 16, 17, 22, 23, 26, 27, 28, 29]

theorem c16Pos_injective : Function.Injective c16Pos := by decide

theorem c16Pos_mem (j : Fin 16) : (c16Pos j).val ∈ ea7Bits := by
  fin_cases j <;> decide

theorem exists_c16Pos {m : Fin 32} (hm : m.val ∈ ea7Bits) : ∃ j, c16Pos j = m := by
  revert hm
  fin_cases m <;> decide

theorem C16_eq_span :
    C16 = Submodule.span (ZMod 2) (Set.range fun j : Fin 16 => (Pi.single (c16Pos j) 1 : V)) := by
  refine le_antisymm (C16_le fun m hm => ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨j, rfl⟩ := exists_c16Pos hm
    rw [decode32_two_pow]
    exact Submodule.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩ m hm
    show (Pi.single (c16Pos j) (1 : ZMod 2) : V) m = 0
    rw [Pi.single_apply, if_neg]
    rintro rfl
    exact hm (c16Pos_mem j)

theorem finrank_C16 : finrank (ZMod 2) C16 = 16 := by
  rw [C16_eq_span]
  have hli : LinearIndependent (ZMod 2) fun j : Fin 16 => (Pi.single (c16Pos j) 1 : V) := by
    have h := (Pi.basisFun (ZMod 2) (Fin 32)).linearIndependent.comp c16Pos c16Pos_injective
    convert h using 1
    funext j
    simp [Pi.basisFun_apply]
  rw [finrank_span_eq_card hli, Fintype.card_fin]

section Std


variable {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] V} {ψ : S.Mbar ≃* ↥TD6}
  (hcomp : ∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
      φ (S.cl (c * u * c⁻¹)) = rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u)))

include hcomp in
theorem actsV_of_compat {c : G} (hc : c ∈ S.M) {k : Fin 365211}
    (hψ : ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) {y : G} (hy : y ∈ S.QG) :
    φ (S.cl (c * y * c⁻¹)) = tvEquiv k.val (φ (S.cl y)) := by
  rw [hcomp c hc y hy, hψ, rhoMod_tvP]

include hcomp in
theorem rhoL_of_compat {c : G} (hc : c ∈ S.M) {k : Fin 365211}
    (hψ : ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) (w : S.Qt) :
    φ (S.rhoL hc w) = tvEquiv k.val (φ w) := by
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  rw [S.rhoL_cl hc hy]
  exact actsV_of_compat hcomp hc hψ hy

variable {t u : G} (htM : t ∈ S.M) (huM : u ∈ S.M)
  (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
  (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)

include hcomp hψt hψu in
theorem mem_C16_of_cent2 {q : G} (hq : q ∈ S.QG) (hqt : Commute q t) (hqu : Commute q u) :
    φ (S.cl q) ∈ C16 := by
  have hfix : ∀ {x : G}, Commute q x → x * q * x⁻¹ = q := fun {x} hqx => by
    rw [← hqx.eq, mul_inv_cancel_right]
  rw [mem_C16_iff]
  refine ⟨?_, ?_⟩
  · have e := actsV_of_compat hcomp htM hψt hq
    rw [hfix hqt, fin_val_zero] at e
    exact e.symm
  · have e := actsV_of_compat hcomp huM hψu hq
    rw [hfix hqu] at e
    exact e.symm

include hcomp hψt hψu in
theorem exists_cent2_of_mem_C16 (h34a : SmithE7E34a) [IsSimpleGroup G] (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) {v : V} (hv : v ∈ C16) :
    ∃ q ∈ S.QG, Commute q t ∧ Commute q u ∧ φ (S.cl q) = v := by
  obtain ⟨hv0, hv1⟩ := (mem_C16_iff v).mp hv
  have hfix : ∀ {x : G} (hx : x ∈ S.M) {k : Fin 365211},
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ →
      tvEquiv k.val v = v → φ.symm v ∈ S.fixQt x := by
    intro x hx k hψx hk
    rw [S.fixQt_of_mem hx, mem_fixSpace]
    apply φ.injective
    have e := rhoL_of_compat hcomp hx hψx (φ.symm v)
    rw [LinearEquiv.apply_symm_apply] at e
    exact e.trans (hk.trans (φ.apply_symm_apply v).symm)
  have h1 := hfix htM hψt (k := 0) (by rw [fin_val_zero]; exact hv0)
  have h2 := hfix huM hψu (k := stdOpp) (by rw [stdOpp_val] at hv1 ⊢; exact hv1)
  rw [fixQt_eq_of_smithE7E34a h34a S hw hU ht htM htQ, S.mem_clSub_iff] at h1
  rw [fixQt_eq_of_smithE7E34a h34a S hw hU hu huM huQ, S.mem_clSub_iff] at h2
  obtain ⟨q₁, hq₁, hq₁Q, hq₁v⟩ := h1
  obtain ⟨q₂, hq₂, hq₂Q, hq₂v⟩ := h2
  have hq₁t : Commute q₁ t := mem_centralizer_singleton_iff.mp (mem_inf.mp hq₁).2
  have hq₂u : Commute q₂ u := mem_centralizer_singleton_iff.mp (mem_inf.mp hq₂).2
  have hq₂t : Commute q₂ t := by
    rcases (S.cl_eq_cl_iff hq₁Q hq₂Q).mp (hq₁v.trans hq₂v.symm) with rfl | rfl
    · exact hq₁t
    · exact hq₁t.mul_left (S.z_comm htM).symm
  exact ⟨q₂, hq₂Q, hq₂t, hq₂u, by rw [hq₂v, LinearEquiv.apply_symm_apply]⟩

include hcomp hψt hψu in
theorem cent2_eq_clPre (h34a : SmithE7E34a) [IsSimpleGroup G] (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) :
    S.QG ⊓ cent2 t u = S.clPre (C16.map (φ.symm : V →ₗ[ZMod 2] S.Qt)) := by
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  · obtain ⟨hqQ, hqH⟩ := mem_inf.mp hq
    obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqH
    refine S.mem_clPre.mpr ⟨hqQ, ⟨φ (S.cl q),
      mem_C16_of_cent2 hcomp htM huM hψt hψu hqQ hqt hqu, ?_⟩⟩
    simp
  · obtain ⟨hqQ, v, hv, hvq⟩ := S.mem_clPre.mp hq
    obtain ⟨q', hq'Q, hq't, hq'u, hq'v⟩ :=
      exists_cent2_of_mem_C16 hcomp htM huM hψt hψu h34a hw hU ht hu htQ huQ hv
    have hcl : S.cl q' = S.cl q := by
      rw [← hvq]
      apply φ.injective
      simp [hq'v]
    refine mem_inf.mpr ⟨hqQ, mem_cent2.mpr ?_⟩
    rcases (S.cl_eq_cl_iff hq'Q hqQ).mp hcl with rfl | rfl
    · exact ⟨hq't, hq'u⟩
    · exact ⟨hq't.mul_left (S.z_comm htM).symm, hq'u.mul_left (S.z_comm huM).symm⟩

include hcomp hψt hψu in
theorem card_cent2_std (h34a : SmithE7E34a) [IsSimpleGroup G] (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) : Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ 17 := by
  rw [cent2_eq_clPre hcomp htM huM hψt hψu h34a hw hU ht hu htQ huQ, S.card_clPre,
    S.card_submodule, LinearEquiv.finrank_map_eq, finrank_C16]
  norm_num

include hcomp hψt hψu in
theorem cent2_le_closure_std (h34a : SmithE7E34a) [IsSimpleGroup G] (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (h1235 : SmithE7Clauses1235 S φ) :
    S.QG ⊓ cent2 t u ≤ closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} := by
  obtain ⟨X, hX⟩ : ∃ X, X = closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} :=
    ⟨_, rfl⟩
  rw [← hX]
  have hzX : S.z ∈ X := by
    rw [hX]
    exact subset_closure ⟨IsConj.refl _, S.z_mem_QG, z_mem_cent2 S htM huM⟩
  let N : Submodule (ZMod 2) V := (S.clSub X).map (φ : S.Qt →ₗ[ZMod 2] V)
  have hN : C16 ≤ N := by
    refine C16_le fun m hm => ?_
    obtain ⟨i, hi, hwi⟩ := exists_wt_eq_two_pow hm
    obtain ⟨c, hc, hcQ, hcw⟩ := h1235.2.1 i hi
    have hφc : φ (S.cl c) = decode32 (2 ^ m.val) := by
      rw [← hwi, ← hcw, decode32_code32]
    have hcC16 : φ (S.cl c) ∈ C16 := by
      rw [hφc]
      exact decode32_two_pow_mem_C16 hm
    obtain ⟨c', hc'Q, hc't, hc'u, hc'v⟩ :=
      exists_cent2_of_mem_C16 hcomp htM huM hψt hψu h34a hw hU ht hu htQ huQ hcC16
    have hcl : S.cl c' = S.cl c := φ.injective hc'v
    have hcH : c ∈ cent2 t u := by
      rcases (S.cl_eq_cl_iff hc'Q hcQ).mp hcl with rfl | rfl
      · exact mem_cent2.mpr ⟨hc't, hc'u⟩
      · exact mem_cent2.mpr ⟨hc't.mul_left (S.z_comm htM).symm,
          hc'u.mul_left (S.z_comm huM).symm⟩
    refine ⟨S.cl c, S.mem_clSub_iff.mpr ⟨c, ?_, hcQ, rfl⟩, ?_⟩
    · rw [hX]
      exact subset_closure ⟨hc, hcQ, hcH⟩
    · rw [← hφc]
      rfl
  intro q hq
  obtain ⟨hqQ, hqH⟩ := mem_inf.mp hq
  obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqH
  obtain ⟨w, hw', hwq⟩ := hN (mem_C16_of_cent2 hcomp htM huM hψt hψu hqQ hqt hqu)
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hw'
  have hcl : S.cl x = S.cl q := φ.injective hwq
  rcases (S.cl_eq_cl_iff hxQ hqQ).mp hcl with rfl | rfl
  · exact hxX
  · exact X.mul_mem hxX hzX

end Std

end CFSG.GF2Type.SmithTypeE.E7
