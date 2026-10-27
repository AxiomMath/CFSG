module

public import CFSG.GF2Type.SmithTypeE.E8.E23aMod
public import CFSG.GF2Type.SmithTypeE.E8.Qa
public import CFSG.GF2Type.SmithTypeE.E8.IdentFusion
public import CFSG.LargeExtraspecial.S14SMJLoc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14
open Module (finrank)
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)


variable {G : Type} [Group G] [Finite G]

theorem cqx_eq_cent2_E8 (h25 : SmithE8E25) (h34a : SmithE8E34a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) {t u : G}
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
      (fixQt_eq_of_smithE8E34a h34a S hw hU ht htM htQ) hqQ hfixt
    have hcu := S.commute_of_cl_mem_fixQt huM
      (fixQt_eq_of_smithE8E34a h34a S hw hU hu huM huQ) hqQ hfixu
    exact mem_inf.mpr ⟨hqQ, mem_cent2.mpr ⟨hct.symm, hcu.symm⟩⟩
  · obtain ⟨hqQ, hqc⟩ := mem_inf.mp hq
    obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqc
    exact mem_inf.mpr ⟨hqQ, mem_centralizer_singleton_iff.mpr (hqt.mul_right hqu).eq⟩

theorem isExtraspecialPGroup_cent2_E8 (h25 : SmithE8E25) (h34a : SmithE8E34a) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) {t u : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (huQ : u ∉ S.QG) (h3 : orderOf (t * u) = 3)
    (hcard : 2 ^ 33 ≤ Nat.card ↥(S.QG ⊓ cent2 t u)) :
    IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) := by
  have hθM : t * u ∈ S.M := S.M.mul_mem htM huM
  have hθ3 : (t * u) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have heq := cqx_eq_cent2_E8 h25 h34a S hw hU ht hu htM huM htQ huQ h3
  have hfix : fixSpace (S.rhoL hθM) ≠ ⊥ := by
    intro hbot
    have hc := S.card_cqx_of_pow_three hθM hθ3
    rw [hbot, finrank_bot, pow_zero, mul_one, heq] at hc
    rw [hc] at hcard
    norm_num at hcard
  exact CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (MulEquiv.subgroupCongr heq)
    (S.isExtraspecialPGroup_cqx hθM hθ3 hfix)

section Std

variable {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}

theorem rhoL_of_acts {c : G} (hc : c ∈ S.M) {T : ↥(adjointGroup .E7 (ZMod 2))}
    (hA : Acts S φ c T) (w : S.Qt) :
    φ (S.rhoL hc w) = e7Rep56 (ZMod 2) T (φ w) := by
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  rw [S.rhoL_cl hc hy]
  exact hA y hy

variable {t u : G} (htM : t ∈ S.M) (huM : u ∈ S.M) (hAt : Acts S φ t xT) (hAu : Acts S φ u xTn)

include hAt hAu in
theorem mem_V0_of_cent2 {q : G} (hq : q ∈ S.QG) (hqt : Commute q t) (hqu : Commute q u) :
    φ (S.cl q) ∈ V0 := by
  have hfix : ∀ {x : G}, Commute q x → x * q * x⁻¹ = q := fun {x} hqx => by
    rw [← hqx.eq, mul_inv_cancel_right]
  rw [mem_V0_iff]
  refine ⟨?_, ?_⟩
  · have e := hAt q hq
    rw [hfix hqt] at e
    exact e.symm
  · have e := hAu q hq
    rw [hfix hqu] at e
    exact e.symm

include htM huM hAt hAu in
theorem exists_cent2_of_mem_V0 (h34a : SmithE8E34a) [IsSimpleGroup G] (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) {v : Fin e7Data.d →₀ ZMod 2} (hv : v ∈ V0) :
    ∃ q ∈ S.QG, Commute q t ∧ Commute q u ∧ φ (S.cl q) = v := by
  obtain ⟨hv0, hv1⟩ := (mem_V0_iff v).mp hv
  have hfix : ∀ {x : G} (hx : x ∈ S.M) {T : ↥(adjointGroup .E7 (ZMod 2))},
      Acts S φ x T → e7Rep56 (ZMod 2) T v = v → φ.symm v ∈ S.fixQt x := by
    intro x hx T hA hT
    rw [S.fixQt_of_mem hx, mem_fixSpace]
    apply φ.injective
    have e := rhoL_of_acts hx hA (φ.symm v)
    rw [LinearEquiv.apply_symm_apply] at e
    exact e.trans (hT.trans (φ.apply_symm_apply v).symm)
  have h1 := hfix htM hAt hv0
  have h2 := hfix huM hAu hv1
  rw [fixQt_eq_of_smithE8E34a h34a S hw hU ht htM htQ, S.mem_clSub_iff] at h1
  rw [fixQt_eq_of_smithE8E34a h34a S hw hU hu huM huQ, S.mem_clSub_iff] at h2
  obtain ⟨q₁, hq₁, hq₁Q, hq₁v⟩ := h1
  obtain ⟨q₂, hq₂, hq₂Q, hq₂v⟩ := h2
  have hq₁t : Commute q₁ t := mem_centralizer_singleton_iff.mp (mem_inf.mp hq₁).2
  have hq₂u : Commute q₂ u := mem_centralizer_singleton_iff.mp (mem_inf.mp hq₂).2
  have hq₂t : Commute q₂ t := by
    rcases (S.cl_eq_cl_iff hq₁Q hq₂Q).mp (hq₁v.trans hq₂v.symm) with rfl | rfl
    · exact hq₁t
    · exact hq₁t.mul_left (S.z_comm htM).symm
  exact ⟨q₂, hq₂Q, hq₂t, hq₂u, by rw [hq₂v, LinearEquiv.apply_symm_apply]⟩

include htM huM hAt hAu in
theorem cent2_eq_clPre (h34a : SmithE8E34a) [IsSimpleGroup G] (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) :
    S.QG ⊓ cent2 t u = S.clPre (V0.map (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)) := by
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  · obtain ⟨hqQ, hqH⟩ := mem_inf.mp hq
    obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqH
    refine S.mem_clPre.mpr ⟨hqQ, ⟨φ (S.cl q), mem_V0_of_cent2 hAt hAu hqQ hqt hqu, ?_⟩⟩
    simp
  · obtain ⟨hqQ, v, hv, hvq⟩ := S.mem_clPre.mp hq
    obtain ⟨q', hq'Q, hq't, hq'u, hq'v⟩ :=
      exists_cent2_of_mem_V0 htM huM hAt hAu h34a hw hU ht hu htQ huQ hv
    have hcl : S.cl q' = S.cl q := by
      rw [← hvq]
      apply φ.injective
      simp [hq'v]
    refine mem_inf.mpr ⟨hqQ, mem_cent2.mpr ?_⟩
    rcases (S.cl_eq_cl_iff hq'Q hqQ).mp hcl with rfl | rfl
    · exact ⟨hq't, hq'u⟩
    · exact ⟨hq't.mul_left (S.z_comm htM).symm, hq'u.mul_left (S.z_comm huM).symm⟩

include htM huM hAt hAu in
theorem card_cent2_std (h34a : SmithE8E34a) [IsSimpleGroup G] (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) : Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ 33 := by
  rw [cent2_eq_clPre htM huM hAt hAu h34a hw hU ht hu htQ huQ, S.card_clPre,
    S.card_submodule, LinearEquiv.finrank_map_eq, finrank_V0]
  norm_num

include htM huM hAt hAu in
theorem cent2_le_closure_std (h34a : SmithE8E34a) [IsSimpleGroup G] (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) (ht : IsConj S.z t) (hu : IsConj S.z u)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG)
    (h2b : ∀ w ∈ weightVec, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = w) :
    S.QG ⊓ cent2 t u ≤ closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} := by
  obtain ⟨X, hX⟩ : ∃ X, X = closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} :=
    ⟨_, rfl⟩
  rw [← hX]
  have hzX : S.z ∈ X := by
    rw [hX]
    exact subset_closure ⟨IsConj.refl _, S.z_mem_QG, z_mem_cent2 S htM huM⟩
  let N : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
    (S.clSub X).map (φ : S.Qt →ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
  have hN : V0 ≤ N := by
    rw [V0, Finsupp.supported_eq_span_single]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc, hcQ, hcw⟩ := h2b _ (single_mem_weightVec a)
    have hcV0 : φ (S.cl c) ∈ V0 := by
      rw [hcw]
      exact Finsupp.single_mem_supported (ZMod 2) _ ha
    obtain ⟨c', hc'Q, hc't, hc'u, hc'v⟩ :=
      exists_cent2_of_mem_V0 htM huM hAt hAu h34a hw hU ht hu htQ huQ hcV0
    have hcl : S.cl c' = S.cl c := φ.injective hc'v
    have hcH : c ∈ cent2 t u := by
      rcases (S.cl_eq_cl_iff hc'Q hcQ).mp hcl with rfl | rfl
      · exact mem_cent2.mpr ⟨hc't, hc'u⟩
      · exact mem_cent2.mpr ⟨hc't.mul_left (S.z_comm htM).symm,
          hc'u.mul_left (S.z_comm huM).symm⟩
    refine ⟨S.cl c, S.mem_clSub_iff.mpr ⟨c, ?_, hcQ, rfl⟩, hcw⟩
    rw [hX]
    exact subset_closure ⟨hc, hcQ, hcH⟩
  intro q hq
  obtain ⟨hqQ, hqH⟩ := mem_inf.mp hq
  obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqH
  obtain ⟨w, hw', hwq⟩ := hN (mem_V0_of_cent2 hAt hAu hqQ hqt hqu)
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hw'
  have hcl : S.cl x = S.cl q := φ.injective hwq
  rcases (S.cl_eq_cl_iff hxQ hqQ).mp hcl with rfl | rfl
  · exact hxX
  · exact X.mul_mem hxX hzX

end Std

end CFSG.GF2Type.SmithTypeE.E8
