module

public import CFSG.Quasithin.H13.L32AC38d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem card_tildeV_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Nat.card ↥(tildeOf (fsuV1 T V) V) = 4 := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  have hbot : tildeOf (fsuV1 T V) (fsuV1 T V) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨v, hv, rfl⟩ := mem_secImg.mp hy
    exact Subgroup.mem_bot.mpr (secMk_eq_one_iff.mpr hv)
  have h1 := relIndex_secImg_of_inf_le (A := Subgroup.normalizer (fsuV1 T V : Set G))
    (K := fsuV1 T V) hV₁V C.VN inf_le_right
  rw [show secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ from hbot,
    Subgroup.relIndex_bot_left] at h1
  have h2 := Subgroup.relIndex_mul_card (fsuV1 T V) V
  rw [inf_eq_left.mpr hV₁V, hV8, hV12] at h2
  unfold tildeOf
  rw [h1]
  omega

theorem pCoreOf_l1_centralizes_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V))
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    {o : G} (ho : o ∈ pCoreOf 2 (L₁Of L (fsuV1 T V))) {v : G} (hv : v ∈ V) :
    o * v * o⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨⟨-, hV2⟩, -, hLTV, hV12, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  have hL1 : L₁Of L (fsuV1 T V) ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := oTwoRes_le _
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hPL : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ L₁Of L (fsuV1 T V) := pCoreOf_le 2 _
  have hPV : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ Subgroup.normalizer (V : Set G) :=
    hPL.trans (hL1.trans (inf_le_left.trans hLV))
  have hPV1 : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hPL.trans (hL1.trans inf_le_right)
  have hVp : IsPGroup 2 ↥V := fun w => ⟨1, Subtype.ext (by
    simpa using hV2 w.1 w.2)⟩
  have hTp : IsPGroup 2 ↥(pCoreOf 2 (L₁Of L (fsuV1 T V)) ⊔ V) :=
    IsPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 _) hVp hPV
  have hlt : fsuV1 T V < V := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h8 := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).2.1
    rw [← h, hV12] at h8
    omega
  obtain ⟨z, hzV, hzV1, hzfix⟩ := exists_fixed_mod hTp le_sup_right hlt
    (sup_le hPV Subgroup.le_normalizer) (sup_le hPV1 C.VN)

  set Vt := tildeOf (fsuV1 T V) V with hVt
  set Pt := tildeOf (fsuV1 T V) (pCoreOf 2 (L₁Of L (fsuV1 T V))) with hPt
  have hxN : x ∈ Subgroup.normalizer (fsuV1 T V : Set G) := (hL1 hxL).2
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := hLV (hL1 hxL).1
  set xt := secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨x, hxN⟩ with hxt
  set zt := secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨z, C.VN hzV⟩ with hzt
  have hxP : xt ∈ Subgroup.normalizer (Pt : Set
      (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) :=
    secMk_mem_normalizer_secImg (le_normalizer_pCoreOf 2 _ hxL)
  have hxVt : xt ∈ Subgroup.normalizer (Vt : Set
      (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) :=
    mem_normalizer_tildeV hxN hxV
  set X := Vt ⊓ Subgroup.centralizer (Pt : Set
    (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) with hX
  have hzX : zt ∈ X := by
    refine ⟨secMk_mem_secImg hzV, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    obtain ⟨p', hp', rfl⟩ := mem_secImg.mp hp
    exact secMk_comm_of_commutator_mem (hzfix _ (Subgroup.mem_sup_left hp'))
  have hxX : xt * zt * xt⁻¹ ∈ X :=
    ⟨(Subgroup.mem_normalizer_iff.mp hxVt zt).mp hzX.1,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer' hxP) zt).mp hzX.2⟩
  have hz1 : zt ≠ 1 := fun h => hzV1 (secMk_eq_one_iff.mp h)
  have hxz1 : xt * zt * xt⁻¹ ≠ 1 := fun h => hz1 (by
    have : zt = xt⁻¹ * (xt * zt * xt⁻¹) * xt := by group
    rw [this, h]
    group)
  have hne : zt ≠ xt * zt * xt⁻¹ := fun h => hz1 (fix_eq_one hxN hfpf hzX.1 h.symm)
  have hXV : X = Vt :=
    eq_of_two_mem_38 inf_le_left (C.card_tildeV_F4 h1332 h1334) hzX hxX hz1 hxz1 hne
  have hvX : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨v, C.VN hv⟩ ∈ X := by
    rw [hXV]
    exact secMk_mem_secImg hv
  have hoP : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨o, hPV1 ho⟩ ∈ Pt :=
    secMk_mem_secImg ho
  have h1 := Subgroup.mem_centralizer_iff.mp hvX.2 _ hoP
  exact commutator_mem_of_secMk_commute (x := ⟨o, hPV1 ho⟩) (y := ⟨v, C.VN hv⟩) h1

theorem exists_moved_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V))
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    {z : G} (hzL : z ∈ L₁Of L (fsuV1 T V)) (hzO : z ∉ pCoreOf 2 (L₁Of L (fsuV1 T V))) :
    ∃ v ∈ V, z * v * z⁻¹ * v⁻¹ ∉ fsuV1 T V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  set L1 := L₁Of L (fsuV1 T V) with hL1def
  set P := pCoreOf 2 L1 with hPdef

  set Cm := centralizerMod (fsuV1 T V) L1 V with hCm
  have hL1N : L1 ≤ Subgroup.normalizer (fsuV1 T V : Set G) := (oTwoRes_le _).trans inf_le_right
  have hPC : ∀ o ∈ P, o ∈ Cm := fun o ho =>
    ⟨pCoreOf_le 2 L1 ho, hL1N (pCoreOf_le 2 L1 ho),
      fun v hv => C.pCoreOf_l1_centralizes_F4 h1332 h1334 hxL hfpf ho hv⟩

  have hxC : x ∉ Cm := by
    rintro ⟨-, -, hx⟩
    obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
    have hle : V ≤ fsuV1 T V := fun v hv => hfpf v hv (hx v hv)
    have := Subgroup.card_le_of_le hle
    rw [hV8, hV12] at this
    omega

  have : (P.subgroupOf L1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 L1)).mpr
      (le_normalizer_pCoreOf 2 L1)
  have h3 : Nat.card (↥L1 ⧸ P.subgroupOf L1) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact S14.Lp3_F4
  have hz1 : (QuotientGroup.mk ⟨z, hzL⟩ : ↥L1 ⧸ P.subgroupOf L1) ≠ 1 := fun h =>
    hzO (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := P.subgroupOf L1)
      ⟨z, hzL⟩).mp h))
  have htop := zpowers_eq_top_of_prime_card h3 hz1
  have hxm : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L1 ⧸ P.subgroupOf L1) ∈
      Subgroup.zpowers (QuotientGroup.mk ⟨z, hzL⟩ : ↥L1 ⧸ P.subgroupOf L1) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxm
  have ho : (⟨z, hzL⟩ ^ k : ↥L1)⁻¹ * ⟨x, hxL⟩ ∈ P.subgroupOf L1 := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hk]
  by_contra hall
  push Not at hall
  have hzC : z ∈ Cm := ⟨hzL, hL1N hzL, hall⟩
  have hzkC : ((⟨z, hzL⟩ ^ k : ↥L1) : G) ∈ Cm := by
    rw [Subgroup.coe_zpow]
    exact zpow_mem hzC k
  have hoC := hPC _ (Subgroup.mem_subgroupOf.mp ho)
  have : x ∈ Cm := by
    have e : x = ((⟨z, hzL⟩ ^ k : ↥L1) : G) * (((⟨z, hzL⟩ ^ k : ↥L1)⁻¹ * ⟨x, hxL⟩ : ↥L1) : G) := by
      simp
    rw [e]
    exact mul_mem hzkC hoC
  exact hxC this

theorem tildeV_le_Wt_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V))
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    {z : G} (hzL : z ∈ L₁Of L (fsuV1 T V)) (hzO : z ∉ pCoreOf 2 (L₁Of L (fsuV1 T V)))
    (hzW : z ∈ H1 H b ⊔ pCoreOf 2 H) : tildeOf (fsuV1 T V) V ≤ C.Wt := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, hLTV, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  have hL1 : L₁Of L (fsuV1 T V) ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := oTwoRes_le _
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hl1H : L₁Of L (fsuV1 T V) ≤ H := by
    rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _]
    exact le_sup_left.trans C.S.hz.1.1
  obtain ⟨v, hv, hzv⟩ := C.exists_moved_F4 h1222 h1332 h1334 hxL hfpf hzL hzO
  have hzN : z ∈ Subgroup.normalizer (fsuV1 T V : Set G) := (hL1 hzL).2
  have hxN : x ∈ Subgroup.normalizer (fsuV1 T V : Set G) := (hL1 hxL).2
  set zt := secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨z, hzN⟩ with hzt
  set xt := secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨x, hxN⟩ with hxt
  set vt := secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨v, C.VN hv⟩ with hvt
  have hvV : vt ∈ tildeOf (fsuV1 T V) V := secMk_mem_secImg hv
  have hvU : vt ∈ tildeOf (fsuV1 T V) (conjClosure V H) := secMk_mem_secImg (le_conjClosure V H hv)

  set w := zt * vt * zt⁻¹ * vt⁻¹ with hw
  have hzV := mem_normalizer_tildeV hzN (hLV (hL1 hzL).1)
  have hxV := mem_normalizer_tildeV hxN (hLV (hL1 hxL).1)
  have hwV : w ∈ tildeOf (fsuV1 T V) V :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hzV vt).mp hvV) (inv_mem hvV)
  have hwW : w ∈ C.Wt := (C.mem_cmod hzW hzN).2.2 vt hvU
  have hw1 : w ≠ 1 := fun h => hzv (by
    have h' : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
        (⟨z, hzN⟩ * ⟨v, C.VN hv⟩ * ⟨z, hzN⟩⁻¹ * ⟨v, C.VN hv⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact h
    exact secMk_eq_one_iff.mp h')
  have hxW : xt ∈ Subgroup.normalizer (C.Wt : Set
      (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) :=
    C.tH_le (secMk_mem_secImg (hl1H hxL))
  have hX : tildeOf (fsuV1 T V) V ⊓ C.Wt = tildeOf (fsuV1 T V) V := by
    refine eq_of_two_mem_38 inf_le_left (C.card_tildeV_F4 h1332 h1334) (a := w) (b := xt * w * xt⁻¹)
      ⟨hwV, hwW⟩ ⟨(Subgroup.mem_normalizer_iff.mp hxV w).mp hwV,
        (Subgroup.mem_normalizer_iff.mp hxW w).mp hwW⟩ hw1 ?_ ?_
    · intro h
      apply hw1
      have : w = xt⁻¹ * (xt * w * xt⁻¹) * xt := by group
      rw [this, h]
      group
    · intro h
      exact hw1 (fix_eq_one hxN hfpf hwV h.symm)
  exact hX ▸ inf_le_right

end Ctx38

end CFSG.Quasithin.H13.L32A.C
