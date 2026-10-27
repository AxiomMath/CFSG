module

public import CFSG.Quasithin.H13.A6S13721b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710d

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

@[expose] def Input13721K_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → ¬ IsElemAbelian 2 (conjClosure V S.G1) →
    ∃ K : Subgroup G, S.G1 ≤ Subgroup.normalizer (K : Set G) ∧ S.L1 ≤ K ∧ K ⊔ T = S.G1 ∧
      K ≤ Subgroup.centralizer ((conjClosure S.V3 S.G1 ⊓
        Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) : Subgroup G) : Set G) ∧
      (∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
        ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 S.G1) ∧
      (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) ∧
      ∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 →
        (∃ o ∈ pCoreOf 2 S.L1, c * o * c⁻¹ * o⁻¹ ∉ pCoreOf 2 S.G1) ∧
          4 ^ 2 ≤ nu c (conjClosure S.V3 S.G1)

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hab in

theorem L1_le_of_mem_Hz_F4 : S.L1 ≤ H :=
  le_sup_left.trans (S.hypF91_F4 hNS h13315 h1356two hH).L₁T_le_H

omit hab in

theorem QH_le_normalizer_L1_F4 :
    pCoreOf 2 H ≤ Subgroup.normalizer (S.L1 : Set G) :=
  (S.QH_le_T_F4 hNS h13315 h1356two hH).trans S.T_le_normalizer_L1

theorem VH_le_centralizer_UH_F4 :
    conjClosure V H ≤ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
  conjClosure_le fun _ hh _ hv =>
    S.conjSub_le_centralizer_UH_F4 hNS h13315 h1356two hH hab hh (mul_mem_conjSub hv)

omit hab in

theorem VH_not_le_V_sup_UH_F4 (h13314 : Stmt13_3_14_F4) :
    ¬ conjClosure V H ≤ V ⊔ conjClosure S.V3 H := by
  intro hVH
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hVU : V ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    hF.V_le_H.trans (le_normalizer_conjClosure S.V3 H)
  have hle : conjClosure S.V3 H ≤ S.V3 := by
    rw [← S.comm_VH_QH_eq_F4 hNS h13315 h1356two hH h13314, Subgroup.commutator_le]
    intro a ha b hb
    have ha' : a ∈ (V : Set G) * (conjClosure S.V3 H : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V _ hVU]
      exact hVH ha
    obtain ⟨v, hv, u, hu, rfl⟩ := Set.mem_mul.mp ha'
    have h1 : u * b * u⁻¹ * b⁻¹ ∈ fsuV1 T V := hF.commutator_conjClosure_le u hu b hb
    have h2 : v * b * v⁻¹ * b⁻¹ ∈ S.V3 := by
      have hc := S.comm_V_QH_mem_V3_F4 hNS h13315 h1356two hH hv hb
      have e : v * b * v⁻¹ * b⁻¹ = (b * v * b⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact S.V3.inv_mem hc
    have e : ⁅v * u, b⁆ = v * (u * b * u⁻¹ * b⁻¹) * v⁻¹ * (v * b * v⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e, S.conj_V1_of_mem hH (hF.V_le_H hv) h1]
    exact S.V3.mul_mem ((S.V1_le_V2.trans S.V2_le_V3) h1) h2
  exact (S.V3_lt_UH_F4 h13315 hH).ne' (le_antisymm hle (le_conjClosure _ _))

omit hab in

theorem exists_comm_VH_not_mem_UH_F4 (h13314 : Stmt13_3_14_F4)
    {K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hKT : K ⊔ T = H)
    (hα : ∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {c : G} (hcK : c ∈ K) (hcQ : c ∉ pCoreOf 2 H) :
    ∃ x ∈ conjClosure V H, c * x * c⁻¹ * x⁻¹ ∉ conjClosure S.V3 H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨α, hsurj, hker⟩ := hα
  have hKH : K ≤ H := hKT ▸ le_sup_left
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHV : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H

  set C := centralizerMod (conjClosure S.V3 H) K (conjClosure V H) with hCdef
  have hcC : c ∈ C := ⟨hcK, hHU (hKH hcK), hcon⟩
  have hQC : ∀ q ∈ K, q ∈ pCoreOf 2 H → q ∈ C := by
    intro q hqK hqQ
    refine ⟨hqK, hHU (hKH hqK), fun x hx => ?_⟩
    have hc := Subgroup.commutator_mem_commutator hx hqQ
    rw [S.comm_VH_QH_eq_F4 hNS h13315 h1356two hH h13314, commutatorElement_def] at hc
    have e : q * x * q⁻¹ * x⁻¹ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hc
  have hCK : ∀ k ∈ K, ∀ y ∈ C, k * y * k⁻¹ ∈ C := by
    intro k hk y hy
    obtain ⟨hyK, hyN, hyc⟩ := hy
    refine ⟨K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk), hHU (hKH (K.mul_mem (K.mul_mem hk hyK)
      (K.inv_mem hk))), fun x hx => ?_⟩
    have hx' : k⁻¹ * x * k⁻¹⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.mp (hHV (hKH (K.inv_mem hk))) x).mp hx
    have h1 := hyc _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHU (hKH hk)) _).mp h1
    have e : k * (y * (k⁻¹ * x * k⁻¹⁻¹) * y⁻¹ * (k⁻¹ * x * k⁻¹⁻¹)⁻¹) * k⁻¹ =
        k * y * k⁻¹ * x * (k * y * k⁻¹)⁻¹ * x⁻¹ := by group
    rwa [e] at h2

  have hKC : K ≤ C := by
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    let C' : Subgroup ↥K := C.subgroupOf K
    have hC'n : C'.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hCK g g.2 n hn⟩
    have hMn : (C'.map α).Normal := hC'n.map α hsurj
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple (C'.map α) hMn with hbot | htop
    · exfalso
      have hmem : α ⟨c, hcK⟩ ∈ C'.map α :=
        Subgroup.mem_map_of_mem α (show (⟨c, hcK⟩ : ↥K) ∈ C' from hcC)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hcQ ((hker _).mp hmem)
    · intro k hk
      have hmem : α ⟨k, hk⟩ ∈ C'.map α := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hmem
      have h1 : α (y⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hyk, inv_mul_cancel]
      have h2 : (y : G)⁻¹ * k ∈ C := hQC _ (K.mul_mem (K.inv_mem y.2) hk) ((hker _).mp h1)
      have e : k = (y : G) * ((y : G)⁻¹ * k) := by group
      rw [e]
      exact C.mul_mem hy h2

  apply S.VH_not_le_V_sup_UH_F4 hNS h13315 h1356two hH h13314
  refine conjClosure_le fun h hh v hv => ?_
  have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := by rw [hKT]; exact hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K T (hTH.trans hHK)] at hh'
  obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hh'
  have hv' : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.frame.T_le ht) v).mp hv
  have hkv := (hKC hk).2.2 _ (le_conjClosure V H hv')
  have e : k * t * v * (k * t)⁻¹ =
      (k * (t * v * t⁻¹) * k⁻¹ * (t * v * t⁻¹)⁻¹) * (t * v * t⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkv) (Subgroup.mem_sup_left hv')

theorem four_pow_six_le_nu_F4 (h13314 : Stmt13_3_14_F4)
    {K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : S.L1 ≤ K)
    (hKT : K ⊔ T = H)
    (hKU0 : K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    (hα : ∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {c : G} (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1) (hcO : c ∉ pCoreOf 2 S.L1)
    (hO : ∃ o ∈ pCoreOf 2 S.L1, c * o * c⁻¹ * o⁻¹ ∉ pCoreOf 2 H)
    (hU : 4 ^ 2 ≤ nu c (conjClosure S.V3 H)) :
    4 ^ 6 ≤ nu c (pCoreOf 2 S.L1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hL1H := S.L1_le_of_mem_Hz_F4 hNS h13315 h1356two hH
  have hcH : c ∈ H := hL1H hcL
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHV : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hQL1 := S.QH_le_normalizer_L1_F4 hNS h13315 h1356two hH
  have hQO : pCoreOf 2 H ≤ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) :=
    hQL1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)
  have hcO' : c ∈ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) := le_normalizer_pCoreOf 2 S.L1 hcL
  have hOH : pCoreOf 2 S.L1 ≤ H := (pCoreOf_le 2 S.L1).trans hL1H

  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl) (hHQ (hL1H hl))

  have hA : 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) ≤ nu c (pCoreOf 2 S.L1) := by
    obtain ⟨o, ho, hno⟩ := hO
    refine four_mul_nu_le hc3 (pCoreOf_isPGroup 2 S.L1) inf_le_left hcO'
      (mem_normalizer_inf_of hcO' (hHQ hcH)) ?_ ⟨o, ho, fun h => hno h.2⟩
    exact fun x hx => mem_normalizer_inf_of (Subgroup.le_normalizer (mem_cfix.1 hx).1)
      (hHQ (hOH (mem_cfix.1 hx).1))

  have hB : nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) = nu c (pCoreOf 2 H) := by
    have hY3 : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by
      obtain ⟨e, he⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 H).to_le
        (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H))
      rw [he]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hcY : ∀ y ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H, c * y * c⁻¹ ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf_of hcO' (hHQ hcH)) y).mp hy
    have hcX : ∀ q ∈ pCoreOf 2 H, q⁻¹ * (c * q * c⁻¹) ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H := by
      intro q hq
      have h1 : q⁻¹ * c * q⁻¹⁻¹ ∈ S.L1 :=
        (Subgroup.mem_normalizer_iff.mp (hQL1 ((pCoreOf 2 H).inv_mem hq)) _).mp hcL
      have hmem : q⁻¹ * (c * q * c⁻¹) ∈ S.L1 ⊓ pCoreOf 2 H := by
        refine ⟨?_, (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq)
          ((Subgroup.mem_normalizer_iff.mp (hHQ hcH) q).mp hq)⟩
        have e : q⁻¹ * (c * q * c⁻¹) = (q⁻¹ * c * q⁻¹⁻¹) * c⁻¹ := by group
        rw [e]
        exact S.L1.mul_mem h1 (S.L1.inv_mem hcL)
      exact ⟨hL1Q hmem, hmem.2⟩
    have hN : cfix c (pCoreOf 2 H) ≤
        Subgroup.normalizer ((pCoreOf 2 S.L1 ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf_of (hQO (mem_cfix.1 hx).1)
        (Subgroup.le_normalizer (mem_cfix.1 hx).1)
    rw [nu_mul c (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H) hN,
      relIndex_cfix_sup_eq_one hc3 inf_le_right hY3 hcY hcX, one_mul]

  have hHCQ : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) ≤ pCoreOf 2 H :=
    inf_le_left
  have hNHC : cfix c (pCoreOf 2 H) ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure S.V3 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (mem_cfix.1 hx).1
    exact mem_normalizer_inf_of (hHQ hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHU hl) hy) hxH)
  have hU0U : conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      conjClosure S.V3 H := inf_le_left
  have hNU0 : cfix c (conjClosure S.V3 H) ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (hF.conjClosure_Vp_le_pCoreOf (mem_cfix.1 hx).1)
    exact mem_normalizer_inf_of (hHU hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hxH)
  have hnuU0 : nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) = 1 := by
    rw [nu, Subgroup.relIndex_eq_one]
    intro u hu
    refine mem_cfix.2 ⟨hu, ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hKU0 (hL1K hcL)) u hu).symm
  have hdual := nu_dual_F97 hF hab hcH hc3
  have hC : nu c (pCoreOf 2 H) = nu c (conjClosure S.V3 H) *
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
    rw [nu_mul c hHCQ hNHC, hdual, nu_mul c hU0U hNU0, hnuU0, mul_one]

  have hVQ := S.VH_le_QH_F4 hNS h13315 h1356two hH hab
  have hVHC : conjClosure V H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
    le_inf hVQ (S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH hab)
  have hD : nu c (conjClosure V H) ≤
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) :=
    nu_le_nu hVHC fun x hx => hHV (hQH (mem_cfix.1 hx).1.1)

  have hcQ : c ∉ pCoreOf 2 H := fun h => hcO (hL1Q ⟨hcL, h⟩)
  have hE : 4 * nu c (conjClosure S.V3 H) ≤ nu c (conjClosure V H) :=
    four_mul_nu_le hc3 (S.isPGroup_VH_F4 hNS h13315 h1356two hH hab) S.UH_le_VH (hHV hcH) (hHU hcH)
      (fun x hx => hHU (hQH (hVQ (mem_cfix.1 hx).1)))
      (S.exists_comm_VH_not_mem_UH_F4 hNS h13315 h1356two hH h13314 hHK hKT hα (hL1K hcL) hcQ)
  calc 4 ^ 6 = 4 * (4 ^ 2 * (4 * 4 ^ 2)) := by norm_num
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * (4 * nu c (conjClosure S.V3 H))) := by gcongr
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * nu c (conjClosure V H)) := by gcongr
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * nu c (pCoreOf 2 H ⊓
        Subgroup.centralizer (conjClosure S.V3 H : Set G))) := by gcongr
    _ = 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by rw [hB, hC]
    _ ≤ nu c (pCoreOf 2 S.L1) := hA

theorem relIndex_A_le_eight_F4 (hA6 : FactAutA6Rank)
    {K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hKT : K ⊔ T = H)
    (hα : ∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hfaith : ∀ h ∈ H, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → h ∈ pCoreOf 2 H)
    (g : ↥(Subgroup.normalizer (V : Set G))) :
    (conjSub (g : G)⁻¹ (conjClosure V H) ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 H).relIndex
      (conjSub (g : G)⁻¹ (conjClosure V H) ⊓ pCoreOf 2 (L ⊔ T)) ≤ 8 := by
  have hKH : K ≤ H := hKT ▸ le_sup_left
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hAH : conjSub (g : G)⁻¹ (conjClosure V H) ⊓ pCoreOf 2 (L ⊔ T) ≤ H :=
    inf_le_right.trans ((pCoreOf_le_of_sylow S.h13.sylow le_sup_right).trans hTH)
  have hsq : ∀ e ∈ conjSub (g : G)⁻¹ (conjClosure V H) ⊓ pCoreOf 2 (L ⊔ T),
      e * e ∈ pCoreOf 2 H := by
    intro e he
    have he' : (g : G) * e * (g : G)⁻¹ ∈ conjClosure V H := by
      have := mem_conjSub.mp he.1
      rwa [inv_inv] at this
    have h1 := S.sq_VH_mem_V1_F4 hNS h13315 h1356two hH hab he'
    have h2 : (g : G) * e * (g : G)⁻¹ * ((g : G) * e * (g : G)⁻¹) ∈ V :=
      (S.V1_le_V2.trans (S.V2_le_V3.trans S.V3_le_V)) h1
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ g.2) _).mp h2
    have e1 : ((g : G)⁻¹ * ((g : G) * e * (g : G)⁻¹ * ((g : G) * e * (g : G)⁻¹)) *
        (g : G)⁻¹⁻¹) = e * e := by group
    have h3' : e * e ∈ V := by rwa [e1] at h3
    exact S.V_le_QH_F4 hNS h13315 h1356two hH hab h3'
  have h := hA6 G K (pCoreOf 2 H) _ (hKH.trans hHQ) (hAH.trans hHQ) (hAH.trans hHK) hα
    (fun e he hk => hfaith e (hAH he) hk) hsq
  rwa [inf_comm (pCoreOf 2 H)] at h

end NonAb

end Setting4

theorem input13721Six_of_F4 (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h13314 : Stmt13_3_14_F4) (hK : Input13721K_F4)
    (hA6 : FactAutA6Rank) : Input13721Six_F4 := by
  intro G _ _ T L V S hNS hNU hhat hG1 hab hna g _ _
  obtain ⟨K, hHK, hL1K, hKT, hKU0, hα, hfaith, hc⟩ := hK G T L V S hNS hNU hhat hG1 hab hna
  refine ⟨fun c hcL hc3 hcO => ?_, ?_⟩
  · obtain ⟨hO, hU⟩ := hc c hcL hc3 hcO
    exact S.four_pow_six_le_nu_F4 hNS h13315 h1356two hG1 hab h13314 hHK hL1K hKT hKU0 hα hcL hc3
      hcO hO hU
  · exact S.relIndex_A_le_eight_F4 hNS h13315 h1356two hG1 hab hA6 hHK hKT hα hfaith g

end CFSG.Quasithin.H13.A6
