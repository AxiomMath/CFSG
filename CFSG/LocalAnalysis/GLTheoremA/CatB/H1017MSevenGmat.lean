module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenShape
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Crit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open (IsElemAbelian GLATwoLocalRank)
open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG tG)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (orderOf_dG orderOf_tG isTwoBCentralizer_tG
  tG_eq_xGmat centralizer_pow_eq_of_prime card_isPGroup_seven_le_of_involution)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat (exists_twoB_Gmat)
open CFSG.HardMathSupport.Dickson.I271 (tabMSeven_sylow_quat)
open CFSG.HardMathSupport.Dickson.I271.TabMSeven (qZG qFG orderOf_qZG orderOf_qFG qZG_comm_qFG
  qZG_comm_tG qFG_comm_tG exists_quat_le_cent_qZG tabMSeven_not_two_pow_five_dvd
  tabMSeven_sevenA_facts gmat_seven_bounds tabMSeven_he_le_cent_dG hePE8 orderOf_conj_eq
  card_centralizer_conj)

private theorem card_le_two_of_sylow_quat {C : Type*} [Group C] [Finite C] (P : Sylow 2 C)
    (e : (P : Subgroup C) ≃* QuaternionGroup 4) {A : Subgroup C} (hA : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hA a a.2)
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := 2) (P := A) fun a => ⟨1, by simpa using hA' a⟩
  let φ : A →* QuaternionGroup 4 :=
    (e.toMonoidHom.comp (Sylow.equiv Q P).toMonoidHom).comp (Subgroup.inclusion hQ)
  have hφ : Function.Injective φ :=
    (e.injective.comp (Sylow.equiv Q P).injective).comp (Subgroup.inclusion_injective hQ)
  have hsq : ∀ a : A, φ a ^ 2 = 1 := fun a => by rw [← map_pow, hA' a, map_one]
  have hinj : Function.Injective fun a : A => decide (φ a = 1) := by
    intro a b hab
    dsimp only at hab
    apply hφ
    rcases CFSG.Monster.Existence.QuaternionGroup.eq_one_or_eq_a_of_sq_eq_one (hsq a) with ha | ha
      <;> rcases CFSG.Monster.Existence.QuaternionGroup.eq_one_or_eq_a_of_sq_eq_one (hsq b)
        with hb | hb
    · rw [ha, hb]
    · rw [ha, hb] at hab
      exact absurd hab (by decide)
    · rw [ha, hb] at hab
      exact absurd hab (by decide)
    · rw [ha, hb]
  exact (Nat.card_le_card_of_injective _ hinj).trans (by simp)

private theorem exists_conj_mem_of_card_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {C F : Subgroup G} (hFC : F ≤ C) (hF : Nat.card F = p ^ 2)
    (hC : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ C → Nat.card Q ≤ p ^ 2) {z : G} (hzC : z ∈ C)
    (hz : orderOf z = p) : ∃ h ∈ C, h * z * h⁻¹ ∈ F := by
  have hF' : Nat.card (F.subgroupOf C) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hF]
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hF').exists_le_sylow
  have hQF : (Q : Subgroup C) = F.subgroupOf C := by
    refine (Subgroup.eq_of_le_of_card_ge hQ ?_).symm
    have h := hC _ (Q.isPGroup'.map C.subtype) (Subgroup.map_subtype_le _)
    rwa [Subgroup.card_map_of_injective C.subtype_injective, ← hF'] at h
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (n := 1) (G := Subgroup.zpowers (⟨z, hzC⟩ : C))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz, pow_one])).exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq C P Q
  have hmem := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj h) _
    (hP (Subgroup.mem_zpowers (⟨z, hzC⟩ : C)))
  rw [← Sylow.coe_subgroup_smul, hQF] at hmem
  exact ⟨h, h.2, hmem⟩

private theorem conj_ne_pow_of_five {G : Type*} [Group G] [Finite G] {z f t d : G}
    (hz : orderOf z = 7) (hf : orderOf f = 5) (hd : orderOf d = 7) (ht : orderOf t = 2)
    (hzf : z * f = f * z) (hzt : z * t = t * z) (hft : f * t = t * f)
    (hu : ∀ u : G, orderOf u = 2 → u * d = d * u →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) =
        Nat.card ↥(Subgroup.centralizer ({t} : Set G)) →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) =
        150528)
    (g : G) (m : ℕ) : g * z * g⁻¹ ≠ d ^ m := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro h
  by_cases hm : d ^ m = 1
  · rw [hm] at h
    have h1 : z = 1 := by
      have h' := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using h'
    rw [h1, orderOf_one] at hz
    norm_num at hz
  · have hC := centralizer_pow_eq_of_prime hd hm
    have hud : g * t * g⁻¹ * d = d * (g * t * g⁻¹) := by
      rw [← Subgroup.mem_centralizer_singleton_iff, ← hC, Subgroup.mem_centralizer_singleton_iff,
        ← h]
      exact Commute.conj hzt.symm g
    have hfC : g * f * g⁻¹ ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G) := by
      refine Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (Commute.conj hft g), ?_⟩
      rw [← hC, Subgroup.mem_centralizer_singleton_iff, ← h]
      exact Commute.conj hzf.symm g
    have h5 := Subgroup.orderOf_dvd_natCard _ hfC
    rw [hu _ (by rw [orderOf_conj_eq, ht]) hud (card_centralizer_conj g t), orderOf_conj_eq,
      hf] at h5
    norm_num at h5

theorem seven_sq_not_le_centralizer_Gmat
    {F W : Subgroup Gmat} (hFc : Nat.card F = 7 ^ 2)
    (hW : IsElemAbelian 2 W) (hW8 : 2 ^ 3 ≤ Nat.card W) :
    ¬ F ≤ Subgroup.centralizer (W : Set Gmat) := by
  intro hFW
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hcls, h2A, h2B, hG5⟩ := gmat_seven_bounds
  obtain ⟨hHk, ⟨e⟩⟩ := tabMSeven_he_le_cent_dG
  obtain ⟨-, htA, huB, h2Bd⟩ := tabMSeven_sevenA_facts hePE8 hcls h2A h2B hG5 orderOf_dG hHk e
  have hzd := conj_ne_pow_of_five orderOf_qZG orderOf_qFG orderOf_dG orderOf_tG qZG_comm_qFG
    qZG_comm_tG qFG_comm_tG fun u hu hud huc =>
      h2Bd u hu hud (huc.trans isTwoBCentralizer_tG.2.2.2.2.1)
  obtain ⟨S, hSz, ⟨eS⟩⟩ := exists_quat_le_cent_qZG
  obtain ⟨P, ⟨eP⟩⟩ := tabMSeven_sylow_quat hSz eS (by
    have h := tabMSeven_not_two_pow_five_dvd orderOf_qZG hzd htA huB
    norm_num at h
    exact h)
  obtain ⟨u, huW, hxu⟩ := exists_twoB_Gmat W
    (fun a ha b hb => congrArg Subtype.val (hW.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)) hW.2
    (by simpa using hW8)
  rw [← tG_eq_xGmat] at hxu
  obtain ⟨c, hc⟩ := isConj_iff.1 hxu
  have hF'C : F.map (MulAut.conj c⁻¹).toMonoidHom ≤ Subgroup.centralizer ({tG} : Set Gmat) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show tG = c⁻¹ * u * c⁻¹⁻¹ by rw [← hc]; group]
    exact Commute.conj (Subgroup.mem_centralizer_iff.1 (hFW hf) u huW).symm c⁻¹
  obtain ⟨h, -, f, hfF, hfe⟩ := exists_conj_mem_of_card_eq hF'C
    (by rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hFc])
    (fun Q hQ hle => card_isPGroup_seven_le_of_involution orderOf_tG hQ hle)
    (Subgroup.mem_centralizer_singleton_iff.2 qZG_comm_tG) orderOf_qZG
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfe
  have hgf : (c * h)⁻¹ * f * (c * h)⁻¹⁻¹ = qZG := by
    calc (c * h)⁻¹ * f * (c * h)⁻¹⁻¹ = h⁻¹ * (c⁻¹ * f * c⁻¹⁻¹) * h := by group
      _ = qZG := by rw [hfe]; group
  have hW'C : W.map (MulAut.conj (c * h)⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({qZG} : Set Gmat) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      ← hgf]
    exact Commute.conj (Subgroup.mem_centralizer_iff.1 (hFW hfF) w hw) (c * h)⁻¹
  have h2 := card_le_two_of_sylow_quat P eP
    (A := (W.map (MulAut.conj (c * h)⁻¹).toMonoidHom).subgroupOf _) (by
      rintro a ha
      obtain ⟨w, hw, hwa⟩ := Subgroup.mem_subgroupOf.1 ha
      exact Subtype.ext (by rw [SubgroupClass.coe_pow, ← hwa, ← map_pow, hW.2 w hw, map_one]; rfl))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'C).toEquiv,
    Subgroup.card_map_of_injective (MulAut.conj (c * h)⁻¹).injective] at h2
  norm_num at hW8
  omega

theorem glaTwoLocalRank_seven_Gmat
    : GLATwoLocalRank 7 Gmat ≤ 2 := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  refine H1016M5.twoLocalRankCriterion_holds Gmat 7 2 3 (by norm_num) (by norm_num) ?_
    (fun t ht E hE hEa => card_isPGroup_seven_le_of_involution ht
      (fun g => ⟨1, Subtype.ext (by simpa using hEa.2 g g.2)⟩) hE)
    (fun _ _ _ hFc hW hW8 hFW => seven_sq_not_le_centralizer_Gmat hFc hW hW8 hFW)
  intro j hj0 hj3
  interval_cases j <;> decide

end CFSG.LocalAnalysis.GLTheoremA.H1017
