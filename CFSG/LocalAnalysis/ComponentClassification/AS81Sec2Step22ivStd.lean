module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivLbar
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivFus
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2Quot

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mk_eq_of_mem_nbar {W X : Subgroup G}
    {q : ↥(normalizer (W : Set G)) ⧸ W.subgroupOf (normalizer (W : Set G))}
    (hq : q ∈ nbar W X) (hq1 : q ≠ 1) :
    ∃ m : ↥(normalizer (W : Set G)),
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) m = q ∧
      (m : G) ∈ X ∧ (m : G) ≠ 1 ∧ (m : G) ∉ W := by
  obtain ⟨m, hm, rfl⟩ := hq
  have hmW : (m : G) ∉ W := fun h => hq1 ((mk_eq_one_iff m).mpr h)
  refine ⟨m, rfl, mem_subgroupOf.mp hm, fun h => hmW ?_, hmW⟩
  rw [h]
  exact one_mem W

section Wsec

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y))

set_option quotPrecheck false in
local notation "πW" =>
  QuotientGroup.mk' ((sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))

include h11 hE16 hF hL hodd hyA hyE hyU hy3

theorem mk_mem_nbar_R_iff (n : ↥(normalizer (sec2W A E y : Set G))) :
    πW n ∈ nbar (sec2W A E y) R ↔ (n : G) ∈ sec2P E := by
  obtain ⟨-, -, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hRP : R ≤ sec2P E := hF.R_le_E.trans (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  rw [mk_mem_nbar_iff]
  constructor
  · rintro ⟨r, hr, hrn⟩
    have : (n : G) = r * (r⁻¹ * n) := by group
    rw [this]
    exact mul_mem (hRP hr) (hWP hrn)
  · intro hn
    obtain ⟨w, hw, r, hr, hwr⟩ := exists_eq_mul_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 hn
    refine ⟨r, hr, ?_⟩
    rw [hwr]
    have : r⁻¹ * (w * r) = r⁻¹ * w * r⁻¹⁻¹ := by group
    rw [this]
    exact (mem_normalizer_iff.mp (hPW (inv_mem (hRP hr))) w).mp hw

theorem mem_normalizer_sec2P_of_mk {n : ↥(normalizer (sec2W A E y : Set G))}
    (hn : πW n ∈ normalizer (nbar (sec2W A E y) R : Set (↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G))))) :
    (n : G) ∈ normalizer (sec2P E : Set G) := by
  obtain ⟨-, -, -, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  refine AS76b.mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨p, hp, rfl⟩
  have hpN : p ∈ normalizer (sec2W A E y : Set G) := hPW hp
  have h1 : πW ⟨p, hpN⟩ ∈ nbar (sec2W A E y) R :=
    (mk_mem_nbar_R_iff h11 hE16 hF hL hodd hyA hyE hyU hy3 _).mpr hp
  have h2 := (mem_normalizer_iff.mp hn _).mp h1
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_nbar_R_iff h11 hE16 hF hL hodd hyA hyE hyU hy3]
    at h2
  simpa using h2

variable (hW : IsElemAbelian 2 (sec2W A E y))
include hW

theorem mk_mem_normalizer_of_conj_mem
    (q : ↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))
    {r : ↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G))}
    (hr : r ∈ nbar (sec2W A E y) R) (hr1 : r ≠ 1) (hqr : q * r * q⁻¹ ∈ nbar (sec2W A E y) R) :
    q ∈ normalizer (nbar (sec2W A E y) (sec2L A E) : Set (↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))) := by
  obtain ⟨m, rfl, hmR, hm1, hmW⟩ := exists_mk_eq_of_mem_nbar hr hr1
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_nbar_R_iff h11 hE16 hF hL hodd hyA hyE hyU hy3]
    at hqr
  have hnW := n.2
  set x : G := (n : G) * m * (n : G)⁻¹ with hx
  have hxP : x ∈ sec2P E := by rw [hx]; simpa using hqr
  have hxW : x ∉ sec2W A E y := fun h => hmW (by
    have := (mem_normalizer_iff.mp (inv_mem hnW) x).mp h
    simpa [hx, mul_assoc] using this)
  have hx2 : x * x = 1 := by
    have hm2 : (m : G) * m = 1 := by rw [← sq]; exact hF.elemR.2 _ hmR
    calc x * x = n * ((m : G) * m) * (n : G)⁻¹ := by rw [hx]; group
      _ = 1 := by rw [hm2]; group
  obtain ⟨w, hw, hwx, -⟩ :=
    exists_conj_mem_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hxP hxW hx2
  obtain ⟨-, -, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hwN : w ∈ normalizer (sec2W A E y : Set G) := le_normalizer hw
  have hn'A : w * (n : G) ∈ normalizer (A : Set G) := mem_normalizer_of_conj_mem_R hF hmR hm1 (by
    have : w * (n : G) * m * (w * (n : G))⁻¹ = w * x * w⁻¹ := by rw [hx]; group
    rw [this]
    exact hwx)
  have hn'L := mem_normalizer_sec2L h11 hE16 hF hL hodd hyA hyE hyU hy3 hn'A (mul_mem hwN hnW)
  have hq : πW n = πW ⟨w * (n : G), mul_mem hwN hnW⟩ := by
    rw [show (⟨w * (n : G), mul_mem hwN hnW⟩ : ↥(normalizer (sec2W A E y : Set G))) = ⟨w, hwN⟩ * n
      from rfl, map_mul, (mk_eq_one_iff ⟨w, hwN⟩).mpr hw, one_mul]
  rw [hq]
  exact mk_mem_normalizer_nbar hn'L

theorem isSylowOf_nbar_R :
    IsSylowOf 2 (nbar (sec2W A E y) R) (centralizer (nbar (sec2W A E y) (sec2L A E) :
      Set (↥(normalizer (sec2W A E y : Set G)) ⧸
        (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUW, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hW2 : IsPGroup 2 (sec2W A E y) := isPGroup_two_of_isElemAbelian hW
  have hLN := sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hWA := sec2W_inf_eq h11 hE16 hF hL hodd hyA hyE hyU hy3
  refine isSylowOf_of_forall_mem_normalizer
    (nbar_R_le_centralizer hF) (isPGroup_nbar hF.sylowR.isPGroup) fun q hqC hqN hq2 => ?_
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨k, hk⟩ := hq2
  have hs2 := exists_pow_eq_one_of_mk hW2 hk
  have hsP := mem_normalizer_sec2P_of_mk h11 hE16 hF hL hodd hyA hyE hyU hy3 hqN
  have hsE := normalizer_sec2P_le_normalizer h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hsP
  obtain ⟨w, hw, hwsR⟩ := exists_mul_mem_normalizer_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hsE
  have hwN : w ∈ normalizer (sec2W A E y : Set G) := le_normalizer hw
  set s' : G := w * (s : G) with hs'
  have hs'N : s' ∈ normalizer (sec2W A E y : Set G) := mul_mem hwN s.2
  have hs'2 := exists_pow_mul_eq_one hW2 s.2 hs2 hw
  have hq' : πW s = πW ⟨s', hs'N⟩ := by
    rw [show (⟨s', hs'N⟩ : ↥(normalizer (sec2W A E y : Set G))) = ⟨w, hwN⟩ * s from rfl,
      map_mul, (mk_eq_one_iff ⟨w, hwN⟩).mpr hw, one_mul]
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨r₀, hr₀, hr₀1⟩ := hD.exists_ne_one
  have hs'A : s' ∈ normalizer (A : Set G) :=
    mem_normalizer_of_conj_mem_R hF hr₀ hr₀1 ((mem_normalizer_iff.mp hwsR r₀).mp hr₀)
  have hs'U : s' ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    have := inf_normalizer_le_normalizer_inf ⟨hs'N, hs'A⟩
    rwa [hWA] at this
  have hLx : ∀ l ∈ ⁅A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)⁆, s' * l * s'⁻¹ * l⁻¹ ∈ E ⊓ A := by
    intro l hl
    have hlL : l ∈ sec2L A E := hl
    have hlA : l ∈ A := ((sec2L_le A E).trans inf_le_left) hlL
    rw [hq'] at hqC
    have h1 := commutator_mem_of_mk_mem_centralizer hLN hqC hlL
    rw [← hWA]
    refine ⟨h1, A.mul_mem ?_ (A.inv_mem hlA)⟩
    exact (mem_normalizer_iff.mp hs'A l).mp hlA
  obtain ⟨u, hu, hc⟩ := exists_mem_inv_mul_mem_centralizer_of_levi hF hL hodd hs'A hs'U hs'2 hLx
  have huR : u ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r' hr' =>
      congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨r', hF.R_le_E hr'⟩ ⟨u, hu.1⟩))
  have hc2 : ∃ k : ℕ, (u⁻¹ * s') ^ 2 ^ k = 1 :=
    exists_pow_mul_eq_one hW2 hs'N hs'2 ((sec2W A E y).inv_mem (hUW hu))
  have hcR := mem_R_of_mem_centralizer hF hc (mul_mem (inv_mem huR) hwsR) hc2
  have hcN : u⁻¹ * s' ∈ normalizer (sec2W A E y : Set G) :=
    mul_mem (le_normalizer ((sec2W A E y).inv_mem (hUW hu))) hs'N
  have hq'' : πW ⟨s', hs'N⟩ = πW ⟨u⁻¹ * s', hcN⟩ := by
    rw [show (⟨u⁻¹ * s', hcN⟩ : ↥(normalizer (sec2W A E y : Set G))) =
      ⟨u⁻¹, le_normalizer ((sec2W A E y).inv_mem (hUW hu))⟩ * ⟨s', hs'N⟩ from rfl,
      map_mul, (mk_eq_one_iff ⟨u⁻¹, le_normalizer ((sec2W A E y).inv_mem (hUW hu))⟩).mpr
        ((sec2W A E y).inv_mem (hUW hu)), one_mul]
  rw [hq', hq'']
  exact mk_mem_nbar hcR hcN

variable (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E))
  (hW₁ : conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤ sec2W A E y)
include hT hW₁

theorem conj_not_mem_nbar
    (q : ↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))
    {r : ↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G))}
    (hr : r ∈ nbar (sec2W A E y) R) (hr1 : r ≠ 1) :
    q * r * q⁻¹ ∉ nbar (sec2W A E y) (sec2L A E) := by
  intro hqr
  obtain ⟨hsyl, -⟩ := isSylowOf_nbar_inf h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  obtain ⟨m, rfl, hmR, hm1, hmW⟩ := exists_mk_eq_of_mem_nbar hr hr1
  have hm2 : ((q * πW m * q⁻¹) ^ 2 ^ 1) = 1 := by
    rw [pow_one, conj_pow, ← map_pow,
      show m ^ 2 = 1 from Subtype.ext (by simpa using hF.elemR.2 _ hmR), map_one]
    group
  obtain ⟨c, hcL, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hsyl
    (isPGroup_zpowers_of_pow hm2) (zpowers_le.mpr hqr)
  have hcm : c⁻¹ * (q * πW m * q⁻¹) * c ∈ nbar (sec2W A E y) (F ⊓ A) := by
    refine hc ?_
    rw [mem_rightConjugate_iff]
    simp [mul_assoc]
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective _ (c⁻¹ * q)
  have hcm' : πW (n * m * n⁻¹) ∈ nbar (sec2W A E y) (F ⊓ A) := by
    rw [map_mul, map_mul, map_inv, hn]
    simpa [mul_assoc] using hcm
  rw [mk_mem_nbar_iff] at hcm'
  obtain ⟨f, hf, hfw⟩ := hcm'
  set x : G := ((n * m * n⁻¹ : ↥(normalizer (sec2W A E y : Set G))) : G) with hx
  have hxconj : x = (n : G) * m * (n : G)⁻¹ := by simp [hx]
  obtain ⟨-, hUW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hW256 := card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3
  have h64 : 64 < Nat.card (sec2W A E y) := by rw [hW256]; norm_num
  by_cases hfE : f ∈ E
  · have hfW : f ∈ sec2W A E y := hUW ⟨hfE, hf.2⟩
    have hxW : x ∈ sec2W A E y := by
      have : x = f * (f⁻¹ * x) := by group
      rw [this]
      exact mul_mem hfW hfw
    rw [hxconj] at hxW
    exact conj_not_mem_of_card_lt h11 hE16 hF hL hodd hmR hm1 (n : G) hW h64 hxW
  ·
    have hfL : f ∈ sec2L A E := (inf_le_inf_right A le_sup_right).trans
      (sup_inf_le_sec2L hF hL hodd) hf
    have hfN := sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hfL
    have hC16 : Nat.card (sec2W A E y ⊓ centralizer ({f} : Set G) : Subgroup G) = 16 := by
      rw [sec2W_inf_centralizer_eq_of_mem h11 hE16 hF hL hodd hT hyA hyE hyU hy3 hW hW₁ hf hfE,
        card_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT]
    have hx2 : f * (f⁻¹ * x) * (f * (f⁻¹ * x)) = 1 := by
      rw [mul_inv_cancel_left, hxconj]
      have hm2' : (m : G) * m = 1 := by rw [← sq]; exact hF.elemR.2 _ hmR
      calc (n : G) * m * (n : G)⁻¹ * ((n : G) * m * (n : G)⁻¹) = n * ((m : G) * m) * (n : G)⁻¹ := by
            group
        _ = 1 := by rw [hm2']; group
    obtain ⟨v, -, hv⟩ := exists_conj_eq_of_mul_self_eq_one h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
      hf hfN hC16 hfw hx2
    rw [mul_inv_cancel_left, hxconj] at hv
    have hZW : sec2Z A E F ≤ sec2W A E y := by
      rw [hF.sec2Z_eq]
      exact fun z hz => hUW ⟨hz.1.1, hz.2⟩
    have hmem : v * (n : G) * m * (v * (n : G))⁻¹ ∈ A := by
      have : v * (n : G) * m * (v * (n : G))⁻¹ = v * ((n : G) * m * (n : G)⁻¹) * v⁻¹ := by group
      rw [this, hv]
      exact hf.2
    exact conj_not_mem_of_sec2Z_le h11 hE16 hF hL hodd hW h64 hZW hmR hm1 (v * (n : G)) hmem

theorem standardComponentIsStandard_nbar :
    standardComponentIsStandard (nbar (sec2W A E y) (sec2L A E)) := by
  have hR4 := card_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hR1 : nbar (sec2W A E y) R ≠ ⊥ := fun h => by
    rw [h, card_bot] at hR4
    omega
  obtain ⟨f, hf, hfE⟩ := exists_mem_inf_not_mem_E hF hodd
  have hfL : f ∈ sec2L A E := (inf_le_inf_right A le_sup_right).trans
    (sup_inf_le_sec2L hF hL hodd) hf
  have hfN := sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hfL
  have hWA := sec2W_inf_eq h11 hE16 hF hL hodd hyA hyE hyU hy3
  refine standardComponentIsStandard_of_sylow
    (isQuasisimple_nbar_sec2L h11 hE16 hF hL hodd hyA hyE hyU hy3 hW)
    (isSylowOf_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW) hR1
    (fun x r hr hr1 hxr => mk_mem_normalizer_of_conj_mem h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
      x hr hr1 hxr)
    (fun x r hr hr1 => conj_not_mem_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hT hW₁ x hr hr1)
    ⟨πW ⟨f, hfN⟩, mk_mem_nbar hfL hfN, fun h => hfE ?_, ?_⟩
  · have hfW := (mk_eq_one_iff _).mp h
    have : f ∈ E ⊓ A := hWA ▸ ⟨hfW, hf.2⟩
    exact this.1
  · rw [← map_pow]
    rw [show (⟨f, hfN⟩ : ↥(normalizer (sec2W A E y : Set G))) ^ 2 = 1 from
      Subtype.ext (by simpa using hF.elemF.2 f hf.1), map_one]

end Wsec

end CFSG.ComponentClassification.AS81
