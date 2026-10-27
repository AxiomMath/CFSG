module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AMComm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma31Elem
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem t_mul_t_mul (h : Ctx t L S x₁ x₂ lam rho tau) (v : G) : t * (t * v) = v := by
  rw [← mul_assoc, t_mul_self h.hyp, one_mul]

private theorem zpowers_t_le_S (h : Ctx t L S x₁ x₂ lam rho tau) : zpowers t ≤ S :=
  Subgroup.zpowers_le.mpr (by
    rw [h.S_eq]
    exact Subgroup.mem_sup_left h.hyp.mem_twoCore)

private theorem zpowers_t_commute_S (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) {g : G} (hg : g ∈ S) : p * g = g * p := by
  have hgt : g * t = t * g := mem_invCent_iff.mp (h.le_invCent hg)
  have hc : Commute t g := (commute_iff_eq t g).mpr hgt.symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  rw [← hk]
  exact hc.zpow_left k

private theorem commutator_mul_left_of_commute {p a b : G}
    (hpa : Commute p a) (hpb : Commute p b) : ⁅p * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, hpb.commutator_eq, mul_one]
  have hpc : Commute p ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((hpa.mul_right hpb).mul_right hpa.inv_right).mul_right hpb.inv_right
  rw [hpc.eq, mul_inv_cancel_right]

private theorem commutator_mul_right_of_commute {p a b : G}
    (hpa : Commute p a) (hpb : Commute p b) : ⁅a, p * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, hpa.symm.commutator_eq, one_mul]
  have hpc : Commute p ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((hpa.mul_right hpb).mul_right hpa.inv_right).mul_right hpb.inv_right
  rw [hpc.eq, mul_inv_cancel_right]

theorem exists_conj_t_mul_four (h : Ctx t L S x₁ x₂ lam rho tau) (h42 : 2 ∣ S.index) :
    ∀ v ∈ fourGrp x₁ x₂, ∃ g : G, g * t * g⁻¹ = t * v := by
  intro v hv
  have hv' : v ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2} := hv
  obtain ⟨n, hn, hnt⟩ := exists_swap_of_l42 h h42
  have hcases := mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
    (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1
    (z_mul_self_ne_one h.toCtx0).1 hv'
  have key : ∀ c : G, c ∈ L → c * (x₁ * x₂) ^ 2 * c⁻¹ = v →
      (c * n) * t * (c * n)⁻¹ = t * v := by
    intro c hcL hcz
    have hct : c * t = t * c := mem_invCent_iff.mp (L_le_invCent h.hyp hcL)
    calc (c * n) * t * (c * n)⁻¹
        = c * (n * t * n⁻¹) * c⁻¹ := by group
      _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hnt]
      _ = (c * t * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
      _ = t * v := by
          have hct' : c * t * c⁻¹ = t := by rw [hct]; group
          rw [hcz, hct']
  rcases hcases with h1 | h1 | h1 | h1
  · subst h1
    exact ⟨1, by simp⟩
  · subst h1
    obtain ⟨c, hcL, hcz⟩ := h.invol_L (x₁ ^ 2) (y_z_mem_L h.toCtx0).1
      (y_mul_self_ne_one h.wreath).1 (y_mul_self_ne_one h.wreath).2
    exact ⟨c * n, key c hcL hcz⟩
  · subst h1
    exact ⟨n, hnt⟩
  · subst h1
    obtain ⟨c, hcL, hcz⟩ := h.invol_L (x₁ ^ 2 * (x₁ * x₂) ^ 2)
      (L.mul_mem (y_z_mem_L h.toCtx0).1 (y_z_mem_L h.toCtx0).2)
      (yz_mul_self_ne_one h.wreath).1 (yz_mul_self_ne_one h.wreath).2
    exact ⟨c * n, key c hcL hcz⟩

theorem lemma4_5_of (h : Ctx t L S x₁ x₂ lam rho tau) (h42 : 2 ∣ S.index)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) : Lemma4_5Concl t S x₁ x₂ tau := by
  intro V hV hVe hV4 hno
  have hM : M12Rel x₁ x₂ lam tau := m12Rel_of_ctx h h44
  have htV : t ∉ V := fun ht => hno 1 t ht (by simp)
  have hV'norm : NormalIn (V ⊔ zpowers t) S := normalIn_sup_zpowers h hV
  have hV'VS : V ⊔ zpowers t ≤ S := hV'norm.1
  have hV'e : CFSG.Open.IsElemAbelian 2 (V ⊔ zpowers t) :=
    isElemAbelian_sup_zpowers h hV.1 hVe
  have htV' : t ∈ V ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hV'card : Nat.card (V ⊔ zpowers t : Subgroup G) = 8 := by
    rw [card_sup_zpowers_of_t_not_mem h hV.1 htV, hV4]
  have hV0norm : NormalIn ((V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau) (m12Grp x₁ x₂ lam tau) :=
    normalIn_inf_m12Grp h hV'norm
  have hV0e : CFSG.Open.IsElemAbelian 2 ((V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau) :=
    CFSG.Open.IsElemAbelian.mono hV'e inf_le_left
  have hV0card : Nat.card ((V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) = 4 := by
    have hc := (eq_sup_inf_of_t_mem h h43 h44 hV'VS htV').2
    rw [hV'card] at hc
    omega
  obtain ⟨hF_le_V0, -⟩ :=
    hM.fourGrp_le_of_normal_elemAbelian hV0e hV0norm hV0card.ge
  have hcardF : Nat.card (fourGrp x₁ x₂) = 4 := (WreathRel.fourGrp_eq_omega h.wreath).2.2
  have hV0_eq_F : fourGrp x₁ x₂ = (V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau :=
    Subgroup.eq_of_le_of_card_ge hF_le_V0 (by rw [hV0card, hcardF])
  have hV_le_F : V ≤ fourGrp x₁ x₂ := by
    intro v hv
    rw [hV0_eq_F]
    rcases mem_m12Grp_or_mul h h43 h44 (hV.1 hv) with hvM | htvM
    · exact ⟨Subgroup.mem_sup_left hv, hvM⟩
    · exfalso
      have htvF : t * v ∈ fourGrp x₁ x₂ := by
        rw [hV0_eq_F]
        exact ⟨(V ⊔ zpowers t).mul_mem htV' (Subgroup.mem_sup_left hv), htvM⟩
      obtain ⟨g, hg⟩ := exists_conj_t_mul_four h h42 (t * v) htvF
      exact hno g v hv (by rw [hg, t_mul_t_mul h v])
  have hV_eq_F : V = fourGrp x₁ x₂ :=
    Subgroup.eq_of_le_of_card_ge hV_le_F (by rw [hV4, hcardF])
  have hbase_le_M : baseGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := by
    rw [baseGrp, m12Grp]
    exact Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have htau_le_M : zpowers tau ≤ m12Grp x₁ x₂ lam tau :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hFM : fourGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := hV0_eq_F.le.trans inf_le_right
  have hB_sup : baseGrp x₁ x₂ ⊔ zpowers tau = closure ({x₁, x₂, tau} : Set G) := by
    rw [baseGrp, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext g
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    tauto
  have hB_le_S : closure ({x₁, x₂, tau} : Set G) ≤ S := by
    rw [← hB_sup]
    exact sup_le (hbase_le_M.trans (m12Grp_le_S h)) (htau_le_M.trans (m12Grp_le_S h))
  have hcentF : S ⊓ centralizer (fourGrp x₁ x₂ : Set G) =
      zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) := by
    rw [centralizer_S_inf h h43 h44 hFM, hM.centralizer_fourGrp, hB_sup]
  have hcommB : ⁅closure ({x₁, x₂, tau} : Set G), closure ({x₁, x₂, tau} : Set G)⁆ =
      fourGrp x₁ x₂ := by
    rw [← hB_sup]
    exact commutator_baseGrp_sup_tau_of hM
  have hcommC : ⁅S ⊓ centralizer (fourGrp x₁ x₂ : Set G),
      S ⊓ centralizer (fourGrp x₁ x₂ : Set G)⁆ = fourGrp x₁ x₂ := by
    have hcomm_zt_B : ∀ p ∈ zpowers t, ∀ b ∈ closure ({x₁, x₂, tau} : Set G),
        p * b = b * p := fun p hp b hb => zpowers_t_commute_S h hp (hB_le_S hb)
    have hB_le_C : closure ({x₁, x₂, tau} : Set G) ≤
        S ⊓ centralizer (fourGrp x₁ x₂ : Set G) := by
      rw [hcentF]
      exact le_sup_right
    have hF_le : fourGrp x₁ x₂ ≤ ⁅S ⊓ centralizer (fourGrp x₁ x₂ : Set G),
        S ⊓ centralizer (fourGrp x₁ x₂ : Set G)⁆ :=
      hcommB.ge.trans (Subgroup.commutator_mono hB_le_C hB_le_C)
    refine le_antisymm ?_ hF_le
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hcentF] at ha hb
    obtain ⟨p, hp, a', ha', rfl⟩ := (mem_sup_iff_of_commute hcomm_zt_B).mp ha
    obtain ⟨q, hq, b', hb', rfl⟩ := (mem_sup_iff_of_commute hcomm_zt_B).mp hb
    have hpa' : Commute p a' := (commute_iff_eq p a').mpr (hcomm_zt_B p hp a' ha')
    have hpb' : Commute p b' := (commute_iff_eq p b').mpr (hcomm_zt_B p hp b' hb')
    have hpq : Commute p q :=
      (commute_iff_eq p q).mpr (zpowers_t_commute_S h hp (zpowers_t_le_S h hq))
    have hqa' : Commute q a' := (commute_iff_eq q a').mpr (hcomm_zt_B q hq a' ha')
    have hqb' : Commute q b' := (commute_iff_eq q b').mpr (hcomm_zt_B q hq b' hb')
    rw [commutator_mul_left_of_commute hpa' (hpq.mul_right hpb')]
    rw [commutator_mul_right_of_commute hqa' hqb']
    rw [← hcommB]
    exact Subgroup.commutator_mem_commutator ha' hb'
  exact ⟨hV_eq_F, by rw [hV_eq_F]; exact hcentF, by rw [hV_eq_F]; exact hcommC⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
