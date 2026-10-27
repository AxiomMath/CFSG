module

public import CFSG.LargeExtraspecial.AS62O4b
public import CFSG.LargeExtraspecial.AS35DSixThreeC
public import CFSG.LargeExtraspecial.AS35CS64Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem card_QG_of_width_two (hw : S.width = 2) : Nat.card S.QG = 32 := by
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]
  norm_num

theorem finrank_commSpace_le_two (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1) :
    finrank (ZMod 2) (commSpace (S.rhoL hxM)) ≤ 2 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have h := two_mul_finrank_commSpace_le (S.rhoL_mul_self hxM hxx)
  rw [S.finrank_Qt_of_width_two hw] at h
  omega

theorem fixSpace_eq_commSpace_of_finrank_eq_two (hw : S.width = 2) {x : G} (hxM : x ∈ S.M)
    (hxx : x * x = 1) (h2 : finrank (ZMod 2) (commSpace (S.rhoL hxM)) = 2) :
    fixSpace (S.rhoL hxM) = commSpace (S.rhoL hxM) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have h := finrank_commSpace_add_finrank_fixSpace (S.rhoL hxM)
  rw [S.finrank_Qt_of_width_two hw] at h
  exact (Submodule.eq_of_le_of_finrank_eq (commSpace_le_fixSpace (S.rhoL_mul_self hxM hxx))
    (by omega)).symm

theorem not_mem_QG_of_rhoL_ne_one {x : G} (hxM : x ∈ S.M) (h : S.rhoL hxM ≠ 1) : x ∉ S.QG :=
  fun hx => h (congrArg Subtype.val ((S.ρ_eq_one_iff ⟨x, hxM⟩).mpr hx))

theorem cqx_eq_clPre_of_typeA (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1)
    (hxQ : x ∉ S.QG) {m : ℕ} (hA : IsTypeA S.q (S.rhoL hxM) m) :
    S.QG ⊓ centralizer ({x} : Set G) = S.clPre (commSpace (S.rhoL hxM)) := by
  have hm := S.eq_two_of_typeA hw hxM hA
  have hfix := S.fixSpace_eq_commSpace_of_typeA hw hxM hA
  have hdim : finrank (ZMod 2) (commSpace (S.rhoL hxM)) = 2 := hA.2.2.2.1.trans hm
  rcases S.fourFive hxM hxx hxQ with ⟨-, hk, -⟩ | ⟨hBC, -, -, -⟩ | ⟨-, hk, hΩ, -⟩
  · rw [S.cqx_eq_clPre_fixSpace hxM hk hxx, hfix]
  · exfalso
    rcases hBC with hB | hC
    · obtain ⟨-, -, -, hodd⟩ := hB
      rw [hdim] at hodd
      exact absurd hodd (by decide)
    · obtain ⟨-, -, -, -, -, v, hv, hqv⟩ := hC
      exact hqv (hA.2.2.2.2 v hv)
  · exfalso
    rw [hdim, S.card_QG_of_width_two hw, show (2 : ℕ) ^ (2 + 1) = 8 by norm_num] at hk
    have hC4 : ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      omega
    have hsub : {y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
        centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧ y * y = 1} ⊆
        ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := fun y hy => (mem_inf.mp hy.1).1
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hC4] at hle
    rw [hdim] at hΩ
    rcases hΩ with h | h <;> rw [h] at hle <;> norm_num at hle

theorem eq_two_of_typeC (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1) {l : ℕ}
    (hC : IsTypeC S.q (S.rhoL hxM) l) : l = 2 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨-, hσ1, -, hl, ⟨k, hk⟩, -⟩ := hC
  have h1 := one_le_finrank_commSpace hσ1
  have h2 := S.finrank_commSpace_le_two hw hxM hxx
  omega

theorem card_QG_eq_eight_mul_of_typeC (hw : S.width = 2) {x : G} (hxM : x ∈ S.M)
    (hxx : x * x = 1) {l : ℕ} (hC : IsTypeC S.q (S.rhoL hxM) l) :
    Nat.card S.QG = 8 * Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  have hl := S.eq_two_of_typeC hw hxM hxx hC
  obtain ⟨-, hσ1, -, hl', -, v₀, hv₀, hqv₀⟩ := hC
  rcases S.fourFive hxM hxx (S.not_mem_QG_of_rhoL_ne_one hxM hσ1) with ⟨hA, -, -⟩ |
    ⟨-, hk, -, -⟩ | ⟨hA, -, -, -⟩
  · exact absurd (hA.2.2.2.2 v₀ hv₀) hqv₀
  · rw [hk, hl', hl]
    norm_num
  · exact absurd (hA.2.2.2.2 v₀ hv₀) hqv₀

theorem exists_mem_cqx_of_typeC (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1)
    {l : ℕ} (hC : IsTypeC S.q (S.rhoL hxM) l) :
    ∃ w ∈ S.QG ⊓ centralizer ({x} : Set G), w * w = 1 ∧ w ≠ 1 ∧ w ≠ S.z := by
  have hl := S.eq_two_of_typeC hw hxM hxx hC
  obtain ⟨-, hσ1, -, hl', -, v₀, hv₀, hqv₀⟩ := hC
  rcases S.fourFive hxM hxx (S.not_mem_QG_of_rhoL_ne_one hxM hσ1) with ⟨hA, -, -⟩ |
    ⟨-, -, hΩ, -⟩ | ⟨hA, -, -, -⟩
  · exact absurd (hA.2.2.2.2 v₀ hv₀) hqv₀
  · rw [hl', hl] at hΩ
    by_contra! hno
    have hsub : {y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
        centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧ y * y = 1} ⊆
        ({1, S.z} : Set G) := by
      intro y hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr (hno y (mem_inf.mp hy.1).1 hy.2 hy1)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hΩ] at hle
    have h2 : ({1, S.z} : Set G).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  · exact absurd (hA.2.2.2.2 v₀ hv₀) hqv₀

theorem exists_conj_mul_of_typeC_of_mem_clPre (hw : S.width = 2) {x : G} (hxM : x ∈ S.M)
    (hxx : x * x = 1) {l : ℕ} (hC : IsTypeC S.q (S.rhoL hxM) l) {w : G}
    (hwU : w ∈ S.clPre (commSpace (S.rhoL hxM))) : ∃ y ∈ S.QG, y * x * y⁻¹ = x * w := by
  have hl := S.eq_two_of_typeC hw hxM hxx hC
  have hl2 : finrank (ZMod 2) (commSpace (S.rhoL hxM)) = 2 := hC.2.2.2.1.trans hl
  have hcard := S.card_QG_eq_eight_mul_of_typeC hw hxM hxx hC
  obtain ⟨O, hO⟩ : ∃ O : Set G, O = {y | ∃ q ∈ S.QG, q * x * q⁻¹ = y} := ⟨_, rfl⟩
  have hOcard : O.ncard = 8 := by
    have h1 := card_eq_relIndex_mul S.QG (centralizer ({x} : Set G))
    rw [relIndex_centralizer_eq_ncard, ← hO] at h1
    rw [S.card_QG_of_width_two hw] at h1 hcard
    have hpos : 0 < Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans hcard)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hsubset : (fun y => x⁻¹ * y) '' O ⊆ (S.clPre (commSpace (S.rhoL hxM)) : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hO] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hmem : x⁻¹ * (q * x * q⁻¹) = (x * q * x⁻¹) * q⁻¹ := by
      rw [hxinv]
      group
    have hxq : x * q * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM hq
    change x⁻¹ * (q * x * q⁻¹) ∈ S.clPre (commSpace (S.rhoL hxM))
    rw [hmem]
    refine S.mem_clPre.mpr ⟨S.QG.mul_mem hxq (S.QG.inv_mem hq), ?_⟩
    rw [S.cl_mul hxq (S.QG.inv_mem hq), S.cl_inv hq, ← S.rhoL_cl hxM hq,
      ← sub_eq_add_vec (ZMod 2)]
    exact sub_mem_commSpace _ _
  have hU8 : (S.clPre (commSpace (S.rhoL hxM)) : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, S.card_clPre, S.card_submodule, hl2]
    norm_num
  have himg : (fun y => x⁻¹ * y) '' O = (S.clPre (commSpace (S.rhoL hxM)) : Set G) :=
    Set.eq_of_subset_of_ncard_le hsubset
      (by rw [Set.ncard_image_of_injective O (mul_right_injective x⁻¹), hOcard, hU8])
  have hw' : w ∈ (fun y => x⁻¹ * y) '' O := by
    rw [himg]
    exact hwU
  obtain ⟨y, hy, hyw⟩ := hw'
  rw [hO] at hy
  obtain ⟨q, hq, hqy⟩ := hy
  refine ⟨q, hq, ?_⟩
  rw [hqy]
  have hyw' : x⁻¹ * y = w := hyw
  calc y = x * (x⁻¹ * y) := by group
    _ = x * w := by rw [hyw']

theorem exists_conj_mul_of_typeC (hw : S.width = 2) {x : G} (hxM : x ∈ S.M)
    (hxx : x * x = 1) {l : ℕ} (hC : IsTypeC S.q (S.rhoL hxM) l) {w : G}
    (hwC : w ∈ S.QG ⊓ centralizer ({x} : Set G)) : ∃ y ∈ S.QG, y * x * y⁻¹ = x * w := by
  refine S.exists_conj_mul_of_typeC_of_mem_clPre hw hxM hxx hC ?_
  rw [← S.fixSpace_eq_commSpace_of_finrank_eq_two hw hxM hxx
    (hC.2.2.2.1.trans (S.eq_two_of_typeC hw hxM hxx hC))]
  exact S.clPre_mono (S.cqxSub_le_fixSpace hxM) (by rw [S.clPre_cqxSub hxM]; exact hwC)

omit [Finite G] in
theorem inf_Qa_le_center' (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {g : G}
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.QG ⊓ S.Qa g ≤ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) ⊓
      centralizer ((S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) : Subgroup G) : Set G) := by
  intro w hw
  obtain ⟨hwQ, hwQa⟩ := mem_inf.mp hw
  set T := S.conjBy g with hT
  have hwt : w ∈ centralizer ({g * S.z * g⁻¹} : Set G) := T.QG_le_M hwQa
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨hwQ, hwt⟩, mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨hyQ, hyt⟩ := mem_inf.mp hy
  have hyT : y ∈ T.M := hyt
  have h1 : y * w * y⁻¹ * w⁻¹ ∈ S.Qa g := mul_mem (T.conj_mem_QG hyT hwQa) (inv_mem hwQa)
  rcases S.commutator_eq_one_or_z hyQ hwQ with h | h
  · calc y * w = y * w * y⁻¹ * w⁻¹ * (w * y) := by group
      _ = w * y := by rw [h, one_mul]
  · exact absurd (h ▸ h1) (S.z_not_mem_Qa hW hne)

omit [Finite G] in
theorem commute_of_inf_Qa_eq_bot {g : G} (hI : S.QG ⊓ S.Qa g = ⊥) {p r : G}
    (hp : p ∈ S.Qa g ⊓ S.M) (hr : r ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) :
    p * r = r * p := by
  obtain ⟨hpT, hpM⟩ := mem_inf.mp hp
  obtain ⟨hrQ, hrt⟩ := mem_inf.mp hr
  set T := S.conjBy g with hT
  have hrT : r ∈ T.M := hrt
  have h1 : p * r * p⁻¹ * r⁻¹ ∈ S.QG := mul_mem (S.conj_mem_QG hpM hrQ) (inv_mem hrQ)
  have h2 : p * r * p⁻¹ * r⁻¹ ∈ S.Qa g := by
    rw [show p * r * p⁻¹ * r⁻¹ = p * (r * p⁻¹ * r⁻¹) by group]
    exact mul_mem hpT (T.conj_mem_QG hrT (inv_mem hpT))
  have h3 : p * r * p⁻¹ * r⁻¹ ∈ S.QG ⊓ S.Qa g := mem_inf.mpr ⟨h1, h2⟩
  rw [hI, mem_bot] at h3
  calc p * r = p * r * p⁻¹ * r⁻¹ * (r * p) := by group
    _ = r * p := by rw [h3, one_mul]

omit [Finite G] in
theorem conj_z_ne_of_not_mem_M {g : G} (hgM : g ∉ S.M) : g * S.z * g⁻¹ ≠ S.z := fun h =>
  hgM (S.mem_M_iff.mpr (by
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [h]))

theorem isTypeA_of_inf_ne_bot (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {g t : G} (hgM : g ∉ S.M)
    (hgt : g * S.z * g⁻¹ = t) (htM : t ∈ S.M) (hI : S.QG ⊓ S.Qa g ≠ ⊥) :
    IsTypeA S.q (S.rhoL htM) 2 := by
  subst hgt
  have hne := S.conj_z_ne_of_not_mem_M hgM
  have htQ : g * S.z * g⁻¹ ∉ S.QG := fun h => hne (hW g h)
  have htt := S.conj_mul_self g
  obtain ⟨⟨w, hwI⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨hwQ, hwQa⟩ := mem_inf.mp hwI
  have hwZ := S.inf_Qa_le_center' hW hne hwI
  have hww : w * w = 1 := S.mul_self_eq_one_of_mem_Qa hne hwQ hwQa
  have hwz : w ≠ S.z := fun h => S.z_not_mem_Qa hW hne (h ▸ hwQa)
  rcases S.fourFive htM htt htQ with ⟨hA, -, -⟩ | ⟨hBC, -, hΩ, -⟩ | ⟨hA, -, -, -⟩
  · have h2 := S.eq_two_of_typeA hw htM hA
    rw [h2] at hA
    exact hA
  · exfalso
    rcases hBC with hB | hC
    · obtain ⟨-, -, -, hodd⟩ := hB
      have h1 : finrank (ZMod 2) (commSpace (S.rhoL htM)) = 1 := by
        have := S.finrank_commSpace_le_two hw htM htt
        obtain ⟨k, hk⟩ := hodd
        omega
      rw [h1] at hΩ
      have hsub : ({1, S.z, w} : Set G) ⊆ {y | y ∈ S.QG ⊓
          centralizer ({g * S.z * g⁻¹} : Set G) ⊓ centralizer ((S.QG ⊓
          centralizer ({g * S.z * g⁻¹} : Set G) : Subgroup G) : Set G) ∧ y * y = 1} := by
        rintro y (rfl | rfl | rfl)
        · exact ⟨one_mem _, mul_one 1⟩
        · exact ⟨mem_inf.mpr ⟨S.z_mem_cqx htM, mem_centralizer_iff.mpr fun y hy =>
            S.z_comm_QG (mem_inf.mp hy).1⟩, S.z_mul_z⟩
        · exact ⟨hwZ, hww⟩
      have h3 : ({1, S.z, w} : Set G).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hwz.symm]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm S.z_ne_one, Ne.symm hw1'⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [h3, hΩ] at this
      norm_num at this
    · obtain ⟨y, hyQ, hy⟩ := S.exists_conj_mul_of_typeC hw htM htt hC (mem_inf.mp hwZ).1
      have htw : y * (S.conjBy g).z * y⁻¹ ∈ (S.conjBy g).QG := by
        rw [conjBy_z, hy]
        exact mul_mem (S.conjBy g).z_mem_QG hwQa
      have := S.weaklyClosed_conjBy hW g y htw
      rw [conjBy_z, hy] at this
      exact hw1' (mul_eq_left.mp this)
  · have h2 := S.eq_two_of_typeA hw htM hA
    rw [h2] at hA
    exact hA

theorem mirror_data {g : G} (hgM : g ∉ S.M) :
    g⁻¹ ∉ (S.conjBy g).M ∧ g⁻¹ * (S.conjBy g).z * g⁻¹⁻¹ = S.z ∧
      (S.conjBy g).QG ⊓ (S.conjBy g).Qa g⁻¹ = S.QG ⊓ S.Qa g := by
  have hne := S.conj_z_ne_of_not_mem_M hgM
  have hgz : g⁻¹ * (S.conjBy g).z * g⁻¹⁻¹ = S.z := by
    rw [conjBy_z]
    group
  refine ⟨fun h => hne ?_, hgz, ?_⟩
  · have h' : g⁻¹ * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * g⁻¹ :=
      mem_centralizer_singleton_iff.mp h
    calc g * S.z * g⁻¹ = (g * S.z * g⁻¹) * g⁻¹ * g := by group
      _ = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [h']
      _ = S.z := by group
  · have hQa : (S.conjBy g).Qa g⁻¹ = S.QG :=
      QG_eq_of_z_eq ((S.conjBy g).conjBy g⁻¹) S (by rw [conjBy_z]; exact hgz)
    rw [hQa, inf_comm]
    rfl

end Setting

end CFSG.LargeExtraspecial
