module

public import CFSG.GH74.QTGen4.Recog.Ku.NStruct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuA_le_kuN [KuLeaf LeafIsMulCommutativeKuA]
    (h : KuHyp G T M H P z) : kuA P H ≤ kuN P H := by
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [h.kuA_comm hx hy, mul_inv_cancel_right]
    exact hy
  · have hy' : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [hy']
    exact (kuA P H).mul_mem ((kuA P H).mul_mem ((kuA P H).inv_mem hx) hy) hx

theorem conj_mem_kuA (h : KuHyp G T M H P z) {n e : G} (hn : n ∈ kuN P H)
    (he : e ∈ kuA P H) : n * e * n⁻¹ ∈ kuA P H :=
  (Subgroup.mem_normalizer_iff.mp hn e).mp he

theorem conj_inv_mem_kuA (h : KuHyp G T M H P z) {n e : G} (hn : n ∈ kuN P H)
    (he : e ∈ kuA P H) : n⁻¹ * e * n ∈ kuA P H := by
  have := h.conj_mem_kuA ((kuN P H).inv_mem hn) he
  simpa using this

@[expose]
noncomputable def conjKuA (h : KuHyp G T M H P z) : ↥(kuN P H) →* MulAut ↥(kuA P H) :=
  MonoidHom.mk'
    (fun n : ↥(kuN P H) =>
      { toFun := fun e => ⟨(n : G) * e * (n : G)⁻¹, h.conj_mem_kuA n.2 e.2⟩
        invFun := fun e => ⟨(n : G)⁻¹ * e * (n : G), h.conj_inv_mem_kuA n.2 e.2⟩
        left_inv := fun e => Subtype.ext (by simp [mul_assoc])
        right_inv := fun e => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun e f => Subtype.ext (by simp [mul_assoc]) })
    (fun n m => by
      ext e
      simp [mul_assoc])

theorem map_ker_conjKuA [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    (h : KuHyp G T M H P z) :
    h.conjKuA.ker.map (kuN P H).subtype = kuA P H := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hc : (n : G) ∈ Subgroup.centralizer (kuA P H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h1 : (h.conjKuA n) ⟨e, he⟩ = ⟨e, he⟩ :=
        congrArg (fun φ : MulAut ↥(kuA P H) => φ ⟨e, he⟩) (MonoidHom.mem_ker.mp hn)
      have h2 : (n : G) * e * (n : G)⁻¹ = e := congrArg Subtype.val h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [h.centralizer_kuA_eq] at hc
    exact hc
  · intro hx
    refine ⟨⟨x, h.kuA_le_kuN hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext e
    show x * (e : G) * x⁻¹ = (e : G)
    rw [h.kuA_comm hx e.2, mul_inv_cancel_right]

theorem card_kuN_dvd [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : Nat.card (kuN P H) ∣ 16 * 20160 := by
  have hcomm : ∀ a b : ↥(kuA P H), a * b = b * a :=
    fun a b => h.isMulCommutative_kuA.is_comm.comm a b
  have hpow : ∀ a : ↥(kuA P H), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa using h.isElemAbelian_kuA.2 a.1 a.2)
  have hcard : Nat.card ↥(kuA P H) = 2 ^ 4 :=
    h.card_kuA.trans (by norm_num)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  have hAut : Nat.card (MulAut ↥(kuA P H)) = 20160 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 4]
    norm_num [Fin.prod_univ_four]
  have hK : Nat.card h.conjKuA.ker = 16 := by
    rw [← Subgroup.card_map_of_injective (f := (kuN P H).subtype) Subtype.val_injective,
      h.map_ker_conjKuA, h.card_kuA]
  have hidx : Nat.card (kuN P H) = 16 * Nat.card h.conjKuA.range := by
    rw [← Subgroup.card_mul_index (H := h.conjKuA.ker), Subgroup.index_ker, hK]
  have hdvd : Nat.card h.conjKuA.range ∣ 20160 := by
    rw [← hAut]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hidx]
  exact mul_dvd_mul_left 16 hdvd

@[expose] def conjKuNAct (N : Subgroup G) : MulAction N G where
  smul n x := (n : G) * x * (n : G)⁻¹
  one_smul x := by
    show (1 : G) * x * (1 : G)⁻¹ = x
    group
  mul_smul n m x := by
    show ((n : G) * (m : G)) * x * ((n : G) * (m : G))⁻¹
      = (n : G) * ((m : G) * x * (m : G)⁻¹) * (n : G)⁻¹
    group

def kuOrb (P H : Subgroup G) (z : G) : Set G :=
  {x | ∃ n ∈ kuN P H, n * z * n⁻¹ = x}

theorem z_sq [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : z ^ 2 = 1 :=
  h.isElemAbelian_kuA.2 z h.z_mem_kuA

theorem mem_zpowers_of_sq (hz2 : z ^ 2 = 1) {x : G} (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  have hz2' : z ^ (2 : ℤ) = 1 := by simpa using hz2
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, hm | hm⟩ : ∃ m : ℤ, k = 2 * m ∨ k = 2 * m + 1 := ⟨k / 2, by omega⟩
  · left
    rw [hm, zpow_mul, hz2', one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, hz2', one_zpow, one_mul]

theorem card_kuN_eq (h : KuHyp G T M H P z) :
    Nat.card (kuN P H) = 384 * (kuOrb P H z).ncard := by
  letI := conjKuNAct (kuN P H)
  have hstab : Nat.card (MulAction.stabilizer (kuN P H) z) = 384 := by
    have hmap : (MulAction.stabilizer (kuN P H) z).map (kuN P H).subtype = H := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hn
        change (n : G) * z * (n : G)⁻¹ = z at hn
        change (n : G) ∈ H
        have hc : (n : G) ∈ Subgroup.centralizer ({z} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hn)
        rw [← h.hCz] at hc
        exact hc
      · intro hx
        have hxN : x ∈ kuN P H := h.H_le_kuN hx
        have hxc : x ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [← h.hCz]
          exact hx
        have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
        refine ⟨⟨x, hxN⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
        change x * z * x⁻¹ = z
        rw [hxz, mul_inv_cancel_right]
    rw [← Subgroup.card_map_of_injective (f := (kuN P H).subtype) Subtype.val_injective,
      hmap, h.card_H]
  have hO : MulAction.orbit (kuN P H) z = kuOrb P H z := by
    ext x
    simp only [MulAction.mem_orbit_iff, kuOrb, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨(g : G), g.2, hg⟩
    · rintro ⟨n, hn, hx⟩
      exact ⟨⟨n, hn⟩, hx⟩
  have key := Subgroup.card_mul_index (MulAction.stabilizer (kuN P H) z)
  rw [hstab] at key
  rw [← Nat.card_coe_set_eq, ← hO, ← key]
  congr 1
  exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (kuN P H) z)).symm

theorem conj_ne_one {n x : G} (hx : x ≠ 1) : n * x * n⁻¹ ≠ 1 := fun e => hx (by
  have hx' : x = n⁻¹ * (n * x * n⁻¹) * n := by group
  rw [e] at hx'
  simpa using hx')

theorem not_dvd_256 (h : KuHyp G T M H P z) : ¬ 256 ∣ Nat.card (kuN P H) := by
  intro hd
  have hd' : 2 ^ 8 ∣ Nat.card (kuN P H) := by
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num]
    exact hd
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd'
  have hQG : Nat.card (Q.map (kuN P H).subtype) = 2 ^ 8 := by
    rw [Subgroup.card_map_of_injective (f := (kuN P H).subtype) Subtype.val_injective]
    exact hQ
  have hdvd := Subgroup.card_subgroup_dvd_card (Q.map (kuN P H).subtype)
  rw [hQG] at hdvd
  have hT := Subgroup.card_mul_index T
  rw [h.card_T] at hT
  rw [← hT] at hdvd
  have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h256] at hdvd
  have hodd := h.sylow.2
  omega

theorem kuOrb_sub (h : KuHyp G T M H P z) {x : G} (hx : x ∈ kuOrb P H z) :
    x ∈ kuA P H ∧ x ≠ 1 := by
  simp only [kuOrb, Set.mem_setOf_eq] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨h.conj_mem_kuA hn h.z_mem_kuA, conj_ne_one h.z_ne_one⟩

theorem kuOrb_conj {n x : G} (hn : n ∈ kuN P H) (hx : x ∈ kuOrb P H z) :
    n * x * n⁻¹ ∈ kuOrb P H z := by
  simp only [kuOrb, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨n * m, (kuN P H).mul_mem hn hm, by group⟩

theorem exists_yN [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ∃ y ∈ kuN P H, (∀ v ∈ kuV2 T M, y * v * y⁻¹ = v → v = 1) ∧
      y ∈ Subgroup.normalizer (kuV2 T M : Set G) ∧
      (∀ r ∈ kuR T M, y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 M → r ∈ pCoreOf 2 M) := by
  obtain ⟨y, hyM, hyV, -, -, hfixV, -, hfixR⟩ := h.exists_y
  exact ⟨y, h.M_inf_normalizer_V2_le_kuN ⟨oTwoUpper_le M hyM, hyV⟩, hfixV, hyV, hfixR⟩

theorem kuW_diff_ncard (h : KuHyp G T M H P z) : ((kuW P H : Set G) \ {1}).ncard = 7 := by
  have hW : (kuW P H : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuW
  have hd := Set.ncard_sdiff_singleton_of_mem (show (1 : G) ∈ (kuW P H : Set G) from (kuW P H).one_mem)
  omega

theorem kuA_diff_ncard [KuLeaf LeafCardKuA]
    (h : KuHyp G T M H P z) : ((kuA P H : Set G) \ {1}).ncard = 15 := by
  have hA : (kuA P H : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuA
  have hd := Set.ncard_sdiff_singleton_of_mem (show (1 : G) ∈ (kuA P H : Set G) from (kuA P H).one_mem)
  omega

theorem coset_mem [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {w u : G} (hwW : w ∈ kuW P H)
    (hwV : w ∉ kuV2 T M) (huW : u ∈ kuW P H) (huV : u ∉ kuV2 T M) :
    w⁻¹ * u ∈ kuV2 T M := by
  have hVW : (kuV2 T M : Set G) ⊆ (kuW P H : Set G) := h.kuV2_le_kuW
  have hB : (fun v => w * v) '' (kuV2 T M : Set G) ⊆
      (kuW P H : Set G) \ (kuV2 T M : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨(kuW P H).mul_mem hwW (h.kuV2_le_kuW hv), fun hc => hwV ?_⟩
    have hw : w = (w * v) * v⁻¹ := by group
    rw [hw]
    exact (kuV2 T M).mul_mem hc ((kuV2 T M).inv_mem hv)
  have hW8 : (kuW P H : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuW
  have hV4 : (kuV2 T M : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuV2
  have hA : ((kuW P H : Set G) \ (kuV2 T M : Set G)).ncard = 4 := by
    rw [Set.ncard_sdiff hVW, hW8, hV4]
  have hB4 : ((fun v => w * v) '' (kuV2 T M : Set G)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective w), hV4]
  have heq := Set.eq_of_subset_of_ncard_le hB (by omega) (Set.toFinite _)
  have hu : u ∈ (kuW P H : Set G) \ (kuV2 T M : Set G) := ⟨huW, huV⟩
  rw [← heq] at hu
  obtain ⟨v, hv, hwv⟩ := hu
  have hwv' : w * v = u := hwv
  rw [← hwv', inv_mul_cancel_left]
  exact hv

theorem kuW_sub_kuOrb [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {w : G} (hw : w ∈ kuW P H) (hw1 : w ≠ 1) :
    w ∈ kuOrb P H z := by
  obtain ⟨y, hyN, hfixV, hyV, -⟩ := h.exists_yN
  have hzV : z ∈ kuV2 T M := h.z_mem_kuV2
  have hz'V : y * z * y⁻¹ ∈ kuV2 T M := (Subgroup.mem_normalizer_iff.mp hyV z).mp hzV
  have hz'1 : y * z * y⁻¹ ≠ 1 := conj_ne_one h.z_ne_one
  have hz'z : y * z * y⁻¹ ≠ z := fun e => h.z_ne_one (hfixV z hzV e)
  show ∃ n ∈ kuN P H, n * z * n⁻¹ = w
  by_cases hwz : w = z
  · exact ⟨1, (kuN P H).one_mem, by simp [hwz]⟩
  · have hwzp : w ∉ Subgroup.zpowers z := fun hm => (mem_zpowers_of_sq h.z_sq hm).elim hw1 hwz
    have hz'zp : y * z * y⁻¹ ∉ Subgroup.zpowers z :=
      fun hm => (mem_zpowers_of_sq h.z_sq hm).elim hz'1 hz'z
    obtain ⟨g, hg, hgw⟩ := h.H_transitive_kuW (h.kuV2_le_kuW hz'V) hz'zp hw hwzp
    refine ⟨g * y, (kuN P H).mul_mem (h.H_le_kuN hg) hyN, ?_⟩
    rw [show g * y * z * (g * y)⁻¹ = g * (y * z * y⁻¹) * g⁻¹ by group]
    exact hgw

theorem kuW_diff_V2_ncard [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ((kuW P H : Set G) \ kuV2 T M).ncard = 4 := by
  have hVW : (kuV2 T M : Set G) ⊆ (kuW P H : Set G) := h.kuV2_le_kuW
  have hW8 : (kuW P H : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuW
  have hV4 : (kuV2 T M : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuV2
  have hd := Set.ncard_sdiff hVW
  omega

theorem kuOrb_ne_seven [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : (kuOrb P H z).ncard ≠ 7 := by
  intro hk
  have hsub : (kuW P H : Set G) \ {1} ⊆ kuOrb P H z := fun w hw =>
    h.kuW_sub_kuOrb hw.1 (by simpa using hw.2)
  have hW7 := h.kuW_diff_ncard
  have hOeq : kuOrb P H z = (kuW P H : Set G) \ {1} :=
    (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm
  have hWV : ((kuW P H : Set G) \ kuV2 T M).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [h.kuW_diff_V2_ncard]
    norm_num
  obtain ⟨w, hwW, hwV⟩ := hWV
  have hw1 : w ≠ 1 := fun e => hwV (by rw [e]; exact (kuV2 T M).one_mem)
  have hwO : w ∈ kuOrb P H z := by
    rw [hOeq]
    exact ⟨hwW, fun e => hw1 (Set.mem_singleton_iff.mp e)⟩
  obtain ⟨y, hyN, -, hyV, hfixR⟩ := h.exists_yN
  have hu : y * w * y⁻¹ ∈ kuOrb P H z := kuOrb_conj hyN hwO
  rw [hOeq] at hu
  have huW : y * w * y⁻¹ ∈ kuW P H := hu.1
  have huV : y * w * y⁻¹ ∉ kuV2 T M := fun hc =>
    hwV ((Subgroup.mem_normalizer_iff.mp hyV w).mpr hc)
  have hcos := h.coset_mem hwW hwV huW huV
  have hcomm := h.kuA_comm ((kuA P H).inv_mem (h.kuW_le_kuA hwW)) (h.kuW_le_kuA huW)
  have h2 : y * w * y⁻¹ * w⁻¹ ∈ kuV2 T M := by
    rw [← hcomm]
    exact hcos
  have hpC : y * w * y⁻¹ * w⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_inf.mp h2).1
  have hwR : w ∈ pCoreOf 2 M := hfixR w (h.kuA_le_kuR (h.kuW_le_kuA hwW)) hpC
  have hm : w ∈ kuW P H ⊓ pCoreOf 2 M := ⟨hwW, hwR⟩
  rw [h.kuW_inf_pCore_M] at hm
  exact hwV hm

theorem kuOrb_sub_diff (h : KuHyp G T M H P z) :
    kuOrb P H z ⊆ (kuA P H : Set G) \ {1} := fun x hx =>
  ⟨(h.kuOrb_sub hx).1, fun e => (h.kuOrb_sub hx).2 (Set.mem_singleton_iff.mp e)⟩

theorem kuOrb_ncard [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : (kuOrb P H z).ncard = 15 := by
  have hle : (kuOrb P H z).ncard ≤ 15 := by
    have h1 := Set.ncard_le_ncard h.kuOrb_sub_diff (Set.toFinite _)
    have h2 := h.kuA_diff_ncard
    omega
  have hWsub : (kuW P H : Set G) \ {1} ⊆ kuOrb P H z := fun w hw =>
    h.kuW_sub_kuOrb hw.1 (by simpa using hw.2)
  have hge : 7 ≤ (kuOrb P H z).ncard := by
    have h1 := Set.ncard_le_ncard hWsub (Set.toFinite _)
    have h2 := h.kuW_diff_ncard
    omega
  have hd := h.card_kuN_dvd
  rw [h.card_kuN_eq, show (16 : ℕ) * 20160 = 384 * 840 by norm_num] at hd
  have hdiv : (kuOrb P H z).ncard ∣ 840 :=
    (mul_dvd_mul_iff_left (by norm_num : (384 : ℕ) ≠ 0)).mp hd
  have hodd : ¬ 2 ∣ (kuOrb P H z).ncard := by
    rintro ⟨j, hj⟩
    apply h.not_dvd_256
    exact ⟨3 * j, by rw [h.card_kuN_eq, hj]; ring⟩
  have key : ∀ k : ℕ, 7 ≤ k → k ≤ 15 → k ∣ 840 → ¬ 2 ∣ k → k ≠ 7 → k = 15 := by
    intro k a b c d e
    interval_cases k <;> omega
  exact key _ hge hle hdiv hodd h.kuOrb_ne_seven

theorem kuOrb_eq [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : kuOrb P H z = (kuA P H : Set G) \ {1} := by
  refine Set.eq_of_subset_of_ncard_le h.kuOrb_sub_diff ?_ (Set.toFinite _)
  have h1 := h.kuA_diff_ncard
  have h2 := h.kuOrb_ncard
  omega

theorem conj_transitive_kuA [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {e : G} (he : e ∈ kuA P H) (he1 : e ≠ 1) :
    ∃ n ∈ kuN P H, n * z * n⁻¹ = e := by
  have hmem : e ∈ kuOrb P H z := by
    rw [h.kuOrb_eq]
    exact ⟨he, fun e' => he1 (Set.mem_singleton_iff.mp e')⟩
  exact hmem

theorem card_kuN [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : Nat.card (kuN P H) = 5760 := by
  have h1 := h.card_kuN_eq
  have h2 := h.kuOrb_ncard
  omega

end KuHyp

end CFSG.GH74.QTGen4.Ku
