module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivStd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivGold
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypII
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicActionHom
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Permutation.AlternatingAutomorphism

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2Quot

variable {G : Type} [Group G] [Finite G]

theorem card_le_eight_of_isPGroup {H : Subgroup (Equiv.Perm (Fin 5))} (hH : IsPGroup 2 H) :
    Nat.card H ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hH.exists_card_eq
  have hdvd : 2 ^ j ∣ 120 := by
    rw [← hj, show (120 : ℕ) = Nat.card (Equiv.Perm (Fin 5)) by
      rw [Nat.card_perm, Nat.card_fin]; decide]
    exact Subgroup.card_subgroup_dvd_card H
  have hj3 : j ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    omega
  rw [hj]
  calc 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
    _ = 8 := by norm_num

section Wsec

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))

set_option quotPrecheck false in
local notation "πW" =>
  QuotientGroup.mk' ((sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))

include h11 hE16 hF hL hodd hyA hyE hyU hy3 hW

theorem card_inf_centralizer_le_of_mem_normalizer {x : G}
    (hxN : x ∈ normalizer (sec2W A E y : Set G)) (hxP : x ∈ normalizer (sec2P E : Set G))
    (hxW : x ∉ sec2W A E y) (hx2 : x ^ 2 = 1) :
    Nat.card (sec2W A E y ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 16 := by
  set W := sec2W A E y with hWdef
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxE := normalizer_sec2P_le_normalizer h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hxP
  obtain ⟨w, hw, hwxR⟩ := exists_mul_mem_normalizer_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hxE
  have hwN : w ∈ normalizer (W : Set G) := le_normalizer hw
  have hx'N : w * x ∈ normalizer (W : Set G) := mul_mem hwN hxN
  have hx'2 := exists_pow_mul_eq_one (isPGroup_two_of_isElemAbelian hW) hxN
    ⟨1, by rwa [pow_one]⟩ hw
  have hx'W : w * x ∉ W := fun h => hxW (by
    have : x = w⁻¹ * (w * x) := by group
    rw [this]
    exact W.mul_mem (W.inv_mem hw) h)
  have hRW := R_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hRW1 := inf_sec2W_eq_bot h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hsq : ∀ r ∈ R, w * x * (w * x) * r * (w * x * (w * x))⁻¹ = r := by
    intro r hr
    set z := w * x * (w * x) with hz
    have hzW : z ∈ W := by
      have : z = w * (x * w * x⁻¹) * (x * x) := by rw [hz]; group
      rw [this, ← sq, hx2, mul_one]
      exact W.mul_mem hw ((mem_normalizer_iff.mp hxN w).mp hw)
    have hzR : z ∈ normalizer (R : Set G) := mul_mem hwxR hwxR
    have h1 : z * r * z⁻¹ * r⁻¹ ∈ R ⊓ W := by
      refine ⟨R.mul_mem ((mem_normalizer_iff.mp hzR r).mp hr) (R.inv_mem hr), ?_⟩
      have : z * r * z⁻¹ * r⁻¹ = z * (r * z⁻¹ * r⁻¹) := by group
      rw [this]
      exact W.mul_mem hzW ((mem_normalizer_iff.mp (hRW hr) _).mp (W.inv_mem hzW))
    rw [hRW1, mem_bot] at h1
    rw [mul_inv_eq_one] at h1
    exact h1
  obtain ⟨r, hr, hr1, hxr⟩ := exists_conj_eq_of_sq_mem hF hwxR hsq
  have hle : W ⊓ centralizer ({x} : Set G) ≤ W ⊓ centralizer ({w * x} : Set G) := by
    intro v hv
    refine ⟨hv.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : v * x = x * v := mem_centralizer_singleton_iff.mp hv.2
    calc v * (w * x) = w * (v * x) := by rw [← mul_assoc, hWc v hv.1 w hw, mul_assoc]
      _ = w * x * v := by rw [h1, mul_assoc]
  exact (card_le_of_le hle).trans
    (card_inf_centralizer_le h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hx'N hwxR hx'2 hx'W hr hr1 hxr)

theorem false_of_nbar_normal (hn : (nbar (sec2W A E y) (sec2L A E)).Normal) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec2W A E y with hWdef
  set M := nbar W (sec2L A E) with hMdef
  obtain ⟨-, hUW, hWP, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hW2 : IsPGroup 2 W := isPGroup_two_of_isElemAbelian hW
  have hW256 := card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hLN := sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hRP : R ≤ sec2P E := hF.R_le_E.trans (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hFL : F ⊓ A ≤ sec2L A E := (inf_le_inf_right A le_sup_right).trans
    (sup_inf_le_sec2L hF hL hodd)
  have hWA := sec2W_inf_eq h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hFP : F ⊓ A ≤ normalizer (sec2P E : Set G) := fun f hf =>
    Sec2.normalizer_le_normalizer_sec2P E (mem_normalizer_of_mem_normalizer_inf hF
      ((sec2L_le A E) (hFL hf)).1 ((sec2L_le A E) (hFL hf)).2)
  have hF2 : IsPGroup 2 (F ⊓ A : Subgroup G) :=
    isPGroup_two_of_isElemAbelian (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
  have hP'2 : IsPGroup 2 (sec2P E ⊔ F ⊓ A : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (Sec2.isPGroup_sec2P E) hF2 hFP
  obtain ⟨T₁, hT₁, hP'T⟩ := AschbacherTheorem3.exists_isSylowOf_le hP'2
    (sup_le hPW (hFL.trans hLN))
  have hPT : sec2P E ≤ T₁ := le_sup_left.trans hP'T
  have hWT : W ≤ T₁ := hWP.trans hPT
  have hRT : R ≤ T₁ := hRP.trans hPT
  have hFT : F ⊓ A ≤ T₁ := le_sup_right.trans hP'T
  have hTN : T₁ ≤ normalizer (W : Set G) := hT₁.le
  set Cb := centralizer (M : Set (↥(normalizer (W : Set G)) ⧸ W.subgroupOf
    (normalizer (W : Set G)))) with hCb
  have hCn : ∀ q, q ∈ normalizer (Cb : Set (↥(normalizer (W : Set G)) ⧸ W.subgroupOf
      (normalizer (W : Set G)))) := fun q =>
    normalizer_le_normalizer_centralizer M (normalizer_eq_top_iff.mpr hn ▸ mem_top q)
  have hRsyl := isSylowOf_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hR4 := card_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  set Tb := nbar W T₁ with hTb
  have hTb2 : IsPGroup 2 Tb := isPGroup_nbar hT₁.isPGroup
  have hTC : Tb ⊓ Cb = nbar W R := by
    refine (eq_of_le_of_card_ge (le_inf (nbar_mono hRT) (nbar_R_le_centralizer hF)) ?_).symm
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hRsyl
      (hTb2.to_le inf_le_left) inf_le_right
    rw [← rightConjugate_card (Tb ⊓ Cb) c]
    exact card_le_of_le hc
  have hTP : ∀ t ∈ T₁, t ∈ normalizer (sec2P E : Set G) := by
    intro t ht
    refine mem_normalizer_sec2P_of_mk h11 hE16 hF hL hodd hyA hyE hyU hy3 (n := ⟨t, hTN ht⟩) ?_
    rw [← hTC]
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer (mk_mem_nbar ht (hTN ht)), hCn _⟩
  have h32 : Nat.card T₁ ≤ 32 * 256 := by
    obtain ⟨hB, -⟩ := isQuasisimple_nbar_sec2L h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
    obtain ⟨e⟩ := nonempty_rankTwoQuot_nbar_equiv h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
    obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom
      (RankTwoAlt.autModel_perm (n := 5) (Or.inl rfl)) hB e
    set T' := Tb.subgroupOf (normalizer (M : Set (↥(normalizer (W : Set G)) ⧸
      W.subgroupOf (normalizer (W : Set G))))) with hT'
    have hTM : Tb ≤ normalizer (M : Set (↥(normalizer (W : Set G)) ⧸
        W.subgroupOf (normalizer (W : Set G)))) := fun q _ =>
      normalizer_eq_top_iff.mpr hn ▸ mem_top q
    have hcount := card_map_mul_card_inf_ker ψ T'
    have hker : T' ⊓ ψ.ker = (nbar W R).subgroupOf (normalizer (M : Set
        (↥(normalizer (W : Set G)) ⧸ W.subgroupOf (normalizer (W : Set G))))) := by
      ext q
      rw [mem_inf, MonoidHom.mem_ker, hψ.eq_one_iff, mem_subgroupOf, mem_subgroupOf, ← hTC]
      exact Iff.rfl
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe (le_inf (nbar_mono hRT)
        (nbar_R_le_centralizer hF) |>.trans inf_le_left |>.trans hTM)).toEquiv, hR4,
      Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv] at hcount
    have h8 := card_le_eight_of_isPGroup (hTb2.comap_subtype.map ψ)
    have hTb32 : Nat.card Tb ≤ 32 := by
      rw [← hcount]
      calc Nat.card (T'.map ψ) * 4 ≤ 8 * 4 := Nat.mul_le_mul_right 4 h8
        _ = 32 := by norm_num
    have h := card_nbar hTN
    rw [inf_eq_right.mpr hWT, hW256] at h
    rw [← h]
    exact Nat.mul_le_mul_right 256 hTb32
  have hC : ∀ x ∈ T₁, x ∉ W → x ^ 2 = 1 →
      Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 16 := fun x hx hxW hx2 =>
    card_inf_centralizer_le_of_mem_normalizer h11 hE16 hF hL hodd hyA hyE hyU hy3 hW (hTN hx)
      (hTP x hx) hxW hx2
  have hRWc : ∀ x ∈ R ⊔ W, x ∉ W → x ^ 2 = 1 → ∃ r ∈ R, ∃ g : G, x = g * r * g⁻¹ := by
    intro x hx hxW hx2
    obtain ⟨w, hw, hwx, -⟩ := exists_conj_mem_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
      (sup_le hRP hWP hx) hxW (by rw [← sq]; exact hx2)
    exact ⟨_, hwx, w⁻¹, by group⟩
  have h64 : 64 < Nat.card W := by rw [hW256]; norm_num
  have hRG : ∀ r ∈ R, r ≠ 1 → ∀ g : G, g * r * g⁻¹ ∉ W := fun r hr hr1 g =>
    conj_not_mem_of_card_lt h11 hE16 hF hL hodd hr hr1 g hW h64
  have hns : ∃ w ∈ W, ∃ g : G, g * w * g⁻¹ ∈ T₁ ∧ g * w * g⁻¹ ∉ W := by
    obtain ⟨f, hf, hfE⟩ := exists_mem_inf_not_mem_E hF hodd
    have hf2 : f ^ 2 = 1 := hF.elemF.2 f hf.1
    have hf1 : f ≠ 1 := fun h => hfE (h ▸ one_mem E)
    obtain ⟨b, -, hb⟩ := exists_conj_mem_sec2Z hF hL hodd hf.2 hf2 hf1
    have hZW : sec2Z A E F ≤ W := by
      rw [hF.sec2Z_eq]
      exact fun z hz => hUW ⟨hz.1.1, hz.2⟩
    refine ⟨b * f * b⁻¹, hZW hb, b⁻¹, ?_, ?_⟩
    · rw [show b⁻¹ * (b * f * b⁻¹) * b⁻¹⁻¹ = f by group]
      exact hFT hf
    · rw [show b⁻¹ * (b * f * b⁻¹) * b⁻¹⁻¹ = f by group]
      intro hfW
      have : f ∈ E ⊓ A := hWA ▸ ⟨hfW, hf.2⟩
      exact hfE this.1
  exact Sec2.false_of_not_stronglyClosed_elem256 hW hW256 hWT hT₁ h32 hRT hF.cardR
    (inf_sec2W_eq_bot h11 hE16 hF hL hodd hyA hyE hyU hy3 hW) hC hRWc hRG hns

end Wsec

end CFSG.ComponentClassification.AS81
