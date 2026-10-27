module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Siegel
public import CFSG.GroupTheory.WreathThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Centralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath
import CFSG.GroupTheory.WreathThreeIso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LieType.PSp43Local

open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
open CFSG.GH74.Exceptional CFSG.Open CFSG.GroupTheory.WreathThree

theorem levPSp_one_pow_three : levPSp 1 ^ 3 = 1 := by
  have h : levGL 1 ^ 3 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have h' : (⟨levGL 1, levGL_mem 1⟩ : StatedSp 2 (ZMod 3)) ^ 3 = 1 := Subtype.ext h
  change (QuotientGroup.mk (⟨levGL 1, levGL_mem 1⟩ : StatedSp 2 (ZMod 3)) :
    PSp43) ^ 3 = 1
  rw [← QuotientGroup.mk_pow, h', QuotientGroup.mk_one]

private theorem levPSp_one_conj_uPSp :
    levPSp 1 * uPSp (Multiplicative.ofAdd (0, 0, 1)) * (levPSp 1)⁻¹ =
      uPSp (Multiplicative.ofAdd (1, 1, 1)) := by
  rw [levPSp_conj]
  congr 1

private theorem levPSp_one_sq_conj_uPSp :
    levPSp 1 ^ 2 * uPSp (Multiplicative.ofAdd (0, 0, 1)) * (levPSp 1 ^ 2)⁻¹ =
      uPSp (Multiplicative.ofAdd (1, 2, 1)) := by
  calc levPSp 1 ^ 2 * uPSp (Multiplicative.ofAdd (0, 0, 1)) * (levPSp 1 ^ 2)⁻¹
      = levPSp 1 * (levPSp 1 * uPSp (Multiplicative.ofAdd (0, 0, 1)) *
          (levPSp 1)⁻¹) * (levPSp 1)⁻¹ := by
        simp only [pow_two]
        group
    _ = levPSp 1 * uPSp (Multiplicative.ofAdd (1, 1, 1)) * (levPSp 1)⁻¹ := by
        rw [levPSp_one_conj_uPSp]
    _ = uPSp (Multiplicative.ofAdd (1, 2, 1)) := by
        rw [levPSp_conj]
        congr 1

private theorem uPSp_smul_mem_zpowers (c : ZMod 3) (v : T3) :
    uPSp (Multiplicative.ofAdd (c • v)) ∈ Subgroup.zpowers (uPSp (Multiplicative.ofAdd v)) := by
  have hcoef : c • v = c.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) c.val, ZMod.natCast_zmod_val]
  rw [hcoef, ofAdd_nsmul, map_pow]
  exact pow_mem (Subgroup.mem_zpowers _) _

theorem base_zpowers_uPSp_eq_E0 :
    base (Subgroup.zpowers (uPSp (Multiplicative.ofAdd (0, 0, 1)))) (levPSp 1) = E0 := by
  rw [base, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom]
  have hmap1 : (MulAut.conj (levPSp 1)) (uPSp (Multiplicative.ofAdd (0, 0, 1))) =
      uPSp (Multiplicative.ofAdd (1, 1, 1)) := by
    simpa only [MulAut.conj_apply] using levPSp_one_conj_uPSp
  have hmap2 : (MulAut.conj (levPSp 1 ^ 2)) (uPSp (Multiplicative.ofAdd (0, 0, 1))) =
      uPSp (Multiplicative.ofAdd (1, 2, 1)) := by
    simpa only [MulAut.conj_apply] using levPSp_one_sq_conj_uPSp
  rw [hmap1, hmap2]
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      · exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    · exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  · rintro _ ⟨v, rfl⟩
    have hv : v = Multiplicative.ofAdd (Multiplicative.toAdd v) := rfl
    rw [hv]
    obtain ⟨p, q, r⟩ := Multiplicative.toAdd v
    have hspan : ((p, q, r) : T3) = (r - p) • ((0, 0, 1) : T3) +
        (2 * p - q) • ((1, 1, 1) : T3) + (q - p) • ((1, 2, 1) : T3) := by
      ext <;> simp <;> ring
    rw [hspan, ofAdd_add, ofAdd_add, map_mul, map_mul]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup (uPSp_smul_mem_zpowers _ _)
      (uPSp_smul_mem_zpowers _ _)) (uPSp_smul_mem_zpowers _ _)

private theorem uPSp_zero_ne_one : uPSp (Multiplicative.ofAdd (0, 0, 1)) ≠ 1 := by
  intro h
  have hx : Multiplicative.ofAdd (0, 0, 1) = (1 : Multiplicative T3) :=
    uPSp_injective (by rw [h, map_one])
  exact absurd hx (by decide)

private theorem uPSp_zero_pow_three : uPSp (Multiplicative.ofAdd (0, 0, 1)) ^ 3 = 1 := by
  rw [← map_pow]
  show uPSp (Multiplicative.ofAdd (0, 0, 1) ^ 3) = 1
  rw [show (Multiplicative.ofAdd (0, 0, 1) : Multiplicative T3) ^ 3 = 1 by decide,
    map_one]

private theorem card_zpowers_uPSp_zero :
    Nat.card (Subgroup.zpowers (uPSp (Multiplicative.ofAdd (0, 0, 1)))) = 3 := by
  rw [Nat.card_zpowers, orderOf_eq_prime uPSp_zero_pow_three uPSp_zero_ne_one]

theorem isWreathThree_zpowers_uPSp :
    IsWreathThree (Subgroup.zpowers (uPSp (Multiplicative.ofAdd (0, 0, 1)))) (levPSp 1) := by
  refine ⟨IsPGroup.of_card (n := 1) (by rw [card_zpowers_uPSp_zero, pow_one]),
    inferInstance, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : uPSp (Multiplicative.ofAdd (0, 0, 1)) ∈
        (⊥ : Subgroup PSp43) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at hmem
    exact uPSp_zero_ne_one hmem
  · intro a ha b hb
    rw [base_zpowers_uPSp_eq_E0] at ha hb
    exact E0_comm ha hb
  · rw [base_zpowers_uPSp_eq_E0, card_E0, card_zpowers_uPSp_zero]
    norm_num
  · rw [levPSp_one_pow_three]
    exact (base (Subgroup.zpowers (uPSp (Multiplicative.ofAdd (0, 0, 1))))
      (levPSp 1)).one_mem

@[expose] noncomputable def sylowQ0 : Subgroup PSp43 :=
  E0 ⊔ Subgroup.zpowers (levPSp 1)

theorem nonempty_mulEquiv_sylowQ0 : Nonempty (↥sylowQ0 ≃* W3) := by
  obtain ⟨n, -, hcardn, ⟨e⟩⟩ :=
    exists_mulEquiv_regularWreathProduct isWreathThree_zpowers_uPSp levPSp_one_pow_three
  have hpow : 3 ^ n = 3 ^ 1 := by
    rw [← hcardn, card_zpowers_uPSp_zero, pow_one]
  have hn : n = 1 := Nat.pow_right_injective (a := 3) (by norm_num) hpow
  subst hn
  have e' : ↥(base (Subgroup.zpowers (uPSp (Multiplicative.ofAdd (0, 0, 1))))
      (levPSp 1) ⊔ Subgroup.zpowers (levPSp 1)) ≃* W3 :=
    e.trans (MulEquiv.cast (M := fun m : ℕ =>
      Multiplicative (ZMod m) ≀ᵣ Multiplicative (ZMod 3))
      (by norm_num : (3 : ℕ) ^ 1 = 3))
  exact ⟨(MulEquiv.subgroupCongr (by rw [sylowQ0, base_zpowers_uPSp_eq_E0])).symm.trans e'⟩

theorem card_sylowQ0 : Nat.card sylowQ0 = 81 := by
  have h := card_sup_zpowers (G := PSp43) isWreathThree_zpowers_uPSp levPSp_one_pow_three
  rw [sylowQ0, ← base_zpowers_uPSp_eq_E0, h, base_zpowers_uPSp_eq_E0, card_E0]

theorem exists_sylow_eq_sylowQ0 : ∃ P : Sylow 3 PSp43, (P : Subgroup PSp43) = sylowQ0 := by
  have hfac : (Nat.card PSp43).factorization 3 = 4 := by
    rw [card_PSp43]
    decide +kernel
  have hcard : Nat.card sylowQ0 = 3 ^ (Nat.card PSp43).factorization 3 := by
    rw [card_sylowQ0, hfac]
    norm_num
  exact ⟨Sylow.ofCard sylowQ0 hcard, Sylow.coe_ofCard sylowQ0 hcard⟩

theorem thompsonSubgroup_sylowQ0 : CFSG.Open.thompsonSubgroup sylowQ0 = E0 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sylowQ0
  rw [thompsonSubgroup_eq_baseIn e]
  exact (eq_baseIn_of_comm e (A := E0) (by rw [sylowQ0]; exact le_sup_left)
    (fun a ha b hb => E0_comm ha hb) (by rw [card_E0])).symm

theorem nonempty_mulEquiv_W3_of_sylow (Q : Sylow 3 PSp43) :
    Nonempty (↥(Q : Subgroup PSp43) ≃* W3) := by
  obtain ⟨Q0, hQ0⟩ := exists_sylow_eq_sylowQ0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSp43 Q Q0
  have hsub : ((g • Q : Sylow 3 PSp43) : Subgroup PSp43) = (Q0 : Subgroup PSp43) :=
    congrArg (fun P : Sylow 3 PSp43 => (P : Subgroup PSp43)) hg
  obtain ⟨e0⟩ := nonempty_mulEquiv_sylowQ0
  exact ⟨(Q.equivSMul g).trans ((MulEquiv.subgroupCongr hsub).trans
    ((MulEquiv.subgroupCongr hQ0).trans e0))⟩

end CFSG.LieType.PSp43Local
