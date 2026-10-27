module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUSyl

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

open CFSG.GH74.GLS.LU.Local in
theorem exists_luSylow' [Finite F] {M : ModelData F} (hG : GoodModel M) (hF : LUFacts M)
    {a₀ : GL (Fin 2) F} (ha₀ : a₀ ∈ M.U2) (ha₀4 : a₀ ^ 4 = 1)
    (hdet : ∀ s : Fˣ, sc4 s ∈ M.K4 → (a₀ : Matrix (Fin 2) (Fin 2) F).det ≠ (s : F) ^ 2)
    (hd : dRefl F ∈ M.U2)
    (hu : dP M (dRefl F) hd ∈ zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M))
    {o : ℕ} (ho : Odd o) (hidx : ((K1 M ⊔ K2 M).subgroupOf (Cg M)).index = 4 * o)
    (hcs : ∀ s ∈ BSsub M, (∃ i : ℕ, s ^ 2 ^ i = 1) → s = 1 ∨ s = yP M) :
    ∃ S : Sylow 2 (PG M), (S : Subgroup (PG M)) ≤ Cg M ∧ dP M a₀ ha₀ ∈ (S : Subgroup (PG M)) ∧
      LUSyl (PG M) (yP M) S (K1 M) (K2 M) (tP M) (dP M (dRefl F) hd) ∧
      ∀ s ∈ (S : Subgroup (PG M)), ∃ k ∈ (S : Subgroup (PG M)) ⊓ (K1 M ⊔ K2 M),
        s = k ∨ s = k * tP M ∨ s = k * dP M a₀ ha₀ ∨ s = k * (tP M * dP M a₀ ha₀) := by
  classical
  have h2 := hG.two_ne_zero
  have hCodd : Odd (Cg M).index := by rw [index_C]; exact hG.odd_index
  have hEn := layer_normal_Cg M h2 hG.qs
  have hEC := E_le_Cg M
  have hb4 : dP M a₀ ha₀ ^ 4 = 1 := dP_pow_four ha₀ ha₀4
  have hbord : ∃ i : ℕ, dP M a₀ ha₀ ^ 2 ^ i = 1 := ⟨2, by simpa using hb4⟩
  have hord : ∃ i : ℕ, tP M ^ 2 ^ i = 1 := ⟨1, by simpa [pow_two] using tP_sq M⟩
  have hzb : IsPGroup 2 ↥(zpowers (dP M a₀ ha₀)) := by
    obtain ⟨j, hj⟩ := ModelSylowQ.card_zpowers_two_pow hbord
    exact IsPGroup.of_card hj
  have hza : IsPGroup 2 ↥(zpowers (tP M)) := by
    obtain ⟨j, hj⟩ := ModelSylowQ.card_zpowers_two_pow hord
    exact IsPGroup.of_card hj
  have hnorm : zpowers (tP M) ≤ Subgroup.normalizer (zpowers (dP M a₀ ha₀) : Set (PG M)) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_zpowers (tP_conj_dP M ha₀) (tP_sq M)
  have hW : IsPGroup 2 ↥(zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M)) :=
    hzb.to_sup_of_normal_left' hza hnorm
  have haW : tP M ∈ zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hbW : dP M a₀ ha₀ ∈ zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hWC : zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) ≤ Cg M :=
    sup_le (Subgroup.zpowers_le.2 (dP_mem_Cg M ha₀)) (Subgroup.zpowers_le.2 (tP_mem_Cg M))
  have haE : tP M ∉ K1 M ⊔ K2 M := tP_not_mem_E M h2
  have hbE : dP M a₀ ha₀ ∉ K1 M ⊔ K2 M := dP_not_mem_E M ha₀ hdet
  have habE : tP M * dP M a₀ ha₀ ∉ K1 M ⊔ K2 M := tP_mul_not_mem_E M h2 (dP_mem_C0 M ha₀)
  have ha2 : tP M * tP M ∈ K1 M ⊔ K2 M := by rw [tP_sq]; exact Subgroup.one_mem _
  obtain ⟨S, hSC, haS, hbS, hcard, hdec⟩ := exists_sylow_le_quot4 (Cg M) (K1 M ⊔ K2 M) hCodd hEC
    hEn ho hidx hW haW hbW hWC ha2 haE hbE habE
  refine ⟨S, hSC, hbS, ?_, hdec⟩
  have hzcen : CenterIs (S : Subgroup (PG M)) (yP M) := sylow_center_of_le_Cg hG S hSC
  have hWS : zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) ≤ (S : Subgroup (PG M)) :=
    sup_le (Subgroup.zpowers_le.2 hbS) (Subgroup.zpowers_le.2 haS)
  have hu2 : dP M (dRefl F) hd * dP M (dRefl F) hd = 1 := dP_mul_self hd dRefl_mul_self
  have hu1 : dP M (dRefl F) hd ≠ 1 := by
    intro h
    have h' : mkP M ⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ =
        mkP M ⟨diagGL 1 1, by rw [diagGL_one]; exact M.K4.one_mem⟩ := by
      rw [show (⟨diagGL 1 1, by rw [diagGL_one]; exact M.K4.one_mem⟩ : ↥M.K4) = 1 from
        Subtype.ext diagGL_one, map_one]
      exact h
    obtain ⟨c, h1, -⟩ := (mkP_diag_eq_iff _ _).1 h'
    apply dRefl_not_scalar h2 c⁻¹
    rw [← sc2_inv]
    have h1' : sc2 c * dRefl F = 1 := h1.symm
    exact eq_inv_of_mul_eq_one_right h1'
  have ht : IsConj (yP M) (tP M) := by
    obtain ⟨k, hk, hkc⟩ := hF.w_conj
    exact isConj_yP_of_ConjMod M.swapGL_mem_K4 (ConjMod.of_conj hk hkc)
  refine ⟨orderOf_yP M h2, (centerIs_iff _ _).2 hzcen, haS, ht, tP_swap M, hWS hu,
    orderOf_eq_prime (by rw [sq]; exact hu2) hu1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcard,
    LUCenAb.mono le_top (luCenAb_K1 hG)⟩
  ·
    intro h
    have h' : mkP M ⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ =
        mkP M ⟨diagGL (-1) 1, M.yGL_mem_K4⟩ := h
    obtain ⟨c, -, h2'⟩ := (mkP_diag_eq_iff _ _).1 h'
    apply dRefl_not_scalar h2 c⁻¹
    rw [← sc2_inv]
    rw [dRefl_inv] at h2'
    exact eq_inv_of_mul_eq_one_right h2'.symm
  ·
    obtain ⟨k, hk, hkc⟩ := hF.perm_conj
    exact isConj_yP_of_ConjMod (diag_inv_mem_K4 M hd)
      (ConjMod.of_conj hk (by rw [dRefl_inv]; exact hkc))
  ·
    have hnd : -dRefl F ∈ M.U2 := dRefl_neg_mem hd
    have hmem : diagGL (-dRefl F) (dRefl F) ∈ M.K4 := by
      have := M.K4.mul_mem (diag_inv_mem_K4 M hd) M.yGL_mem_K4
      have e : diagGL (dRefl F) (dRefl F)⁻¹ * yGL F = diagGL (-dRefl F) (dRefl F) := by
        rw [yGL, diagGL_mul, dRefl_inv, mul_neg, mul_one]
      rwa [e] at this
    have hprod : dP M (dRefl F) hd * yP M = mkP M ⟨diagGL (-dRefl F) (dRefl F), hmem⟩ := by
      rw [dP, ← map_mul]
      congr 1
      apply Subtype.ext
      show diagGL (dRefl F) (dRefl F)⁻¹ * yGL F = diagGL (-dRefl F) (dRefl F)
      rw [yGL, diagGL_mul, dRefl_inv, mul_neg, mul_one]
    rw [hprod]
    refine isConj_yP_of_ConjMod hmem (D_refl hF hnd hd ?_ dRefl_mul_self (neg_dRefl_ne_one h2) ?_
      (dRefl_ne_one h2) (dRefl_ne_neg_one h2))
    · rw [neg_mul_neg]; exact dRefl_mul_self
    · intro h
      exact dRefl_ne_one h2 (neg_inj.1 h)
  ·
    exact normalizer_K1_of_C0 M h2 (dP_mem_C0 M hd)
  ·
    have h := tP_conj_dP M hd
    have hinv : (dP M (dRefl F) hd)⁻¹ = dP M (dRefl F) hd := inv_eq_of_mul_eq_one_right hu2
    rw [hinv, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  ·
    intro s hs hsn
    obtain ⟨k, hk, hcases⟩ := hdec s hs
    have hkE : k ∈ K1 M ⊔ K2 M := hk.2
    have hkC0 : k ∈ C0 M := E_le_C0 M hkE
    have hk' : k⁻¹ ∈ (S : Subgroup (PG M)) ⊓ (K1 M ⊔ K2 M) :=
      ⟨S.inv_mem hk.1, (K1 M ⊔ K2 M).inv_mem hkE⟩
    refine ⟨k⁻¹, hk', ?_⟩
    rcases hcases with h | h | h | h
    · exfalso
      apply hsn
      rw [h]
      exact normalizer_K1_of_C0 M h2 hkC0
    · rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
      exact ht
    · exfalso
      apply hsn
      rw [h]
      exact normalizer_K1_of_C0 M h2 ((C0 M).mul_mem hkC0 (dP_mem_C0 M ha₀))
    · rw [h, ← mul_assoc, inv_mul_cancel, one_mul, tP_mul_dP M ha₀]
      exact isConj_yP_of_ConjMod _ (W_one hF ha₀)
  ·
    intro s hs hcomm
    have hsC : s ∈ Cg M := hSC hs
    obtain ⟨p, hp⟩ := blockScalar_of_cent_E hG hsC hcomm
    have hsB : s ∈ BSsub M := ⟨p, hp⟩
    have hs2 : ∃ i : ℕ, s ^ 2 ^ i = 1 := by
      obtain ⟨i, hi⟩ := S.isPGroup' ⟨s, hs⟩
      exact ⟨i, by have := congrArg Subtype.val hi; simpa using this⟩
    rcases hcs s hsB hs2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
