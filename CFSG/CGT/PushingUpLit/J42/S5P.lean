module

public import CFSG.CGT.PushingUpLit.J42.S5Klein
public import CFSG.CGT.PushingUpLit.SolK.RankOne

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.GH74 CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm

theorem qvec_eq_prod : ∀ X Y z : ZMod 2, qvec X Y z =
    (if X + z = 1 then pairVec 0 1 else 1) * (if Y + z = 1 then pairVec 0 2 else 1) *
      (if z = 1 then pairVec 0 3 else 1) := by
  decide +kernel

theorem comm_of_sq_one {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

theorem perm_eq_one_of_fix : ∀ σ : Perm (Fin 5), σ 0 = 0 → σ 1 = 1 → σ 2 = 2 → σ 3 = 3 →
    σ = 1 := by
  decide +kernel

theorem pairVec_zero_one : (pairVec 0 1 : ↥(coreMod 5)) = qvec 1 0 0 := by decide +kernel

theorem pairVec_zero_two : (pairVec 0 2 : ↥(coreMod 5)) = qvec 0 1 0 := by decide +kernel

theorem pairVec_zero_three : (pairVec 0 3 : ↥(coreMod 5)) = qvec 1 1 1 := by decide +kernel

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

structure SolCfg.CaseB : Prop where
  tight : TightData S
  rsmall : RSmall S
  rbot : rOf M X = ⊥
  odd : ∃ m : ↥M, sign (S.θ m) = -1
  notM : ¬ CGOf S.x0 ≤ M

namespace SolCfg

include S

variable {S}

theorem CaseB.qelem (hB : S.CaseB) : QElem S := SolCfg.RSmall.elem S hB.rsmall

theorem vsupp_x0 : vsupp (S.D.β ⟨S.x0, S.x0_mem_W⟩) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  rw [S.β_x0]
  decide

theorem card_vsupp_x0 : (vsupp (S.D.β ⟨S.x0, S.x0_mem_W⟩)).card = 4 := by
  rw [S.vsupp_x0]
  decide

theorem CaseB.notM' (hB : S.CaseB) : ¬ CGOf (S.x0 * 1) ≤ M := by
  rw [mul_one]
  exact hB.notM

@[expose] noncomputable def PP : Subgroup G := pCoreOf 2 (CGOf S.x0)

theorem CaseB.sup_eq (hB : S.CaseB) :
    S.PP ⊔ pCoreOf 2 M = TOf M S.x0 := by
  have := S.sup_eq_TOf hB.tight hB.qelem hB.rsmall S.x0_mem_W (one_mem _) S.card_vsupp_x0
    hB.notM'
  unfold PP
  simpa only [mul_one] using this

theorem CaseB.PP_le_T (hB : S.CaseB) : S.PP ≤ TOf M S.x0 := le_sup_left.trans hB.sup_eq.le

theorem CaseB.PP_le_M (hB : S.CaseB) : S.PP ≤ M := hB.PP_le_T.trans (TOf_le_M M _)

theorem CaseB.not_Q_le_PP (hB : S.CaseB) : ¬ pCoreOf 2 M ≤ S.PP := by
  have := S.not_Q_le_P hB.tight hB.qelem hB.rsmall S.x0_mem_W (one_mem _) S.card_vsupp_x0
    hB.notM'
  unfold PP
  simpa only [mul_one] using this

theorem CaseB.Q_le_CG (hB : S.CaseB) : pCoreOf 2 M ≤ CGOf S.x0 :=
  S.Q_le_CGOf hB.tight (S.W_le_Q S.x0_mem_W)

theorem fourGroup_x0 : FourGroup ({0, 1, 2, 3} : Finset (Fin 5)) (S.TN S.x0) := by
  have hF := S.fourGroup_theta S.x0_mem_W (one_mem _) S.card_vsupp_x0 (TOf_le_M M (S.x0 * 1))
    (TOf_le_C M (S.x0 * 1)) (isPGroup_TOf M (S.x0 * 1))
    (fun k hk u hu => normalized_TOf M (S.x0 * 1) hk hu)
  rw [S.vsupp_x0] at hF
  simpa only [mul_one] using hF

theorem CaseB.theta_PP (hB : S.CaseB) : (S.PP.subgroupOf M).map S.θ = klein := by
  have h1 := S.theta_P_eq hB.tight hB.qelem hB.rsmall S.x0_mem_W (one_mem _) S.card_vsupp_x0
    hB.notM'
  have hN := S.TN_ne_bot hB.tight hB.qelem hB.rsmall S.x0_mem_W (one_mem _) S.card_vsupp_x0
    hB.notM'
  simp only [mul_one] at h1 hN
  unfold PP
  rw [h1]
  exact eq_klein_of_fourGroup S.fourGroup_x0 hN

theorem CaseB.exists_lift (hB : S.CaseB) {σ : Perm (Fin 5)} (hσ : σ ∈ klein) :
    ∃ p ∈ S.PP, ∃ hp : p ∈ M, S.θ ⟨p, hp⟩ = σ := by
  rw [← hB.theta_PP] at hσ
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
  exact ⟨m, Subgroup.mem_subgroupOf.1 hm, m.2, rfl⟩

theorem CaseB.theta_mem_klein (hB : S.CaseB) {p : G} (hp : p ∈ S.PP) (hpM : p ∈ M) :
    S.θ ⟨p, hpM⟩ ∈ klein := by
  rw [← hB.theta_PP]
  exact Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩

@[expose] noncomputable def qG (X Y z : ZMod 2) : G := ((S.D.β.symm (qvec X Y z) : ↥S.D.W) : G)

theorem qG_mem_W (X Y z : ZMod 2) : S.qG X Y z ∈ S.D.W := (S.D.β.symm (qvec X Y z)).2

theorem β_qG (X Y z : ZMod 2) : S.D.β ⟨S.qG X Y z, S.qG_mem_W X Y z⟩ = qvec X Y z :=
  S.D.β.apply_symm_apply _

theorem qG_mul (X Y z X' Y' z' : ZMod 2) :
    S.qG X Y z * S.qG X' Y' z' = S.qG (X + X') (Y + Y') (z + z') := by
  show (((S.D.β.symm (qvec X Y z) * S.D.β.symm (qvec X' Y' z') : ↥S.D.W)) : G) = _
  rw [← map_mul, qvec_mul]
  rfl

theorem qG_zero : S.qG 0 0 0 = 1 := by
  show ((S.D.β.symm (qvec 0 0 0) : ↥S.D.W) : G) = 1
  rw [qvec_zero, map_one]
  rfl

theorem qG_inj {X Y z X' Y' z' : ZMod 2} (h : S.qG X Y z = S.qG X' Y' z') :
    X = X' ∧ Y = Y' ∧ z = z' := by
  have h1 : (S.D.β.symm (qvec X Y z) : ↥S.D.W) = S.D.β.symm (qvec X' Y' z') := Subtype.ext h
  exact qvec_inj (S.D.β.symm.injective h1)

theorem qG_sq (X Y z : ZMod 2) : S.qG X Y z * S.qG X Y z = 1 := by
  rw [qG_mul]
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [this, this, this, qG_zero]

theorem x0_eq : S.x0 = S.qG 0 0 1 := by
  show ((S.D.β.symm xI : ↥S.D.W) : G) = ((S.D.β.symm (qvec 0 0 1) : ↥S.D.W) : G)
  rw [xI_eq]

theorem conj_qG {m : G} (hm : m ∈ M) {σ : Perm (Fin 5)} (hσ : S.θ ⟨m, hm⟩ = σ)
    {X Y z X' Y' z' : ZMod 2} (h : coreAct 5 σ (qvec X Y z) = qvec X' Y' z') :
    m * S.qG X Y z * m⁻¹ = S.qG X' Y' z' := by
  have hW : m * S.qG X Y z * m⁻¹ ∈ S.D.W := S.W_normalized hm (S.qG_mem_W X Y z)
  have h1 := S.θ_spec ⟨m, hm⟩ ⟨S.qG X Y z, S.qG_mem_W X Y z⟩ hW
  rw [hσ, S.β_qG, h] at h1
  have := S.D.β.injective (h1.trans (S.β_qG X' Y' z').symm)
  exact congrArg Subtype.val this

@[expose] noncomputable def BP : Subgroup ↥(coreMod 5) :=
  (S.PP.subgroupOf S.D.W).map S.D.β.toMonoidHom

theorem mem_BP {u : ↥(coreMod 5)} :
    u ∈ S.BP ↔ ∃ g : G, ∃ hg : g ∈ S.D.W, g ∈ S.PP ∧ S.D.β ⟨g, hg⟩ = u := by
  unfold BP
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.1, g.2, Subgroup.mem_subgroupOf.1 hg, rfl⟩
  · rintro ⟨g, hg, hgP, rfl⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 hgP, rfl⟩

theorem mem_PP_of_mem_BP {g : G} (hg : g ∈ S.D.W) (h : S.D.β ⟨g, hg⟩ ∈ S.BP) : g ∈ S.PP := by
  obtain ⟨g', hg', hg'P, he⟩ := S.mem_BP.1 h
  have : (⟨g', hg'⟩ : ↥S.D.W) = ⟨g, hg⟩ := S.D.β.injective he.symm.symm
  have h2 : g' = g := congrArg Subtype.val this
  rw [← h2]
  exact hg'P

theorem CaseB.pairVec_mem_BP (hB : S.CaseB) {σ : Perm (Fin 5)} (hσ : σ ∈ klein)
    (hσ4 : σ 4 = 4) (a : Fin 5) : pairVec a (σ a) ∈ S.BP := by
  obtain ⟨p, hpP, hpM, hθ⟩ := hB.exists_lift hσ
  set q : ↥S.D.W := S.D.β.symm (pairVec a 4) with hq
  have hqQ : (q : G) ∈ pCoreOf 2 M := S.W_le_Q q.2
  have hqK : (q : G) ∈ CGOf S.x0 := hB.Q_le_CG hqQ
  have hconj : p * ((q⁻¹ : ↥S.D.W) : G) * p⁻¹ ∈ S.D.W := S.W_normalized hpM (q⁻¹).2
  have hcP : ((q * ⟨p * ((q⁻¹ : ↥S.D.W) : G) * p⁻¹, hconj⟩ : ↥S.D.W) : G) ∈ S.PP := by
    have e : ((q * ⟨p * ((q⁻¹ : ↥S.D.W) : G) * p⁻¹, hconj⟩ : ↥S.D.W) : G) =
        ((q : G) * p * (q : G)⁻¹) * p⁻¹ := by
      show (q : G) * (p * ((q : G))⁻¹ * p⁻¹) = _
      group
    rw [e]
    exact S.PP.mul_mem (pCoreOf_normalized _ hqK hpP) (S.PP.inv_mem hpP)
  refine S.mem_BP.2 ⟨_, (q * ⟨p * ((q⁻¹ : ↥S.D.W) : G) * p⁻¹, hconj⟩).2, hcP, ?_⟩
  have h1 := S.θ_spec ⟨p, hpM⟩ q⁻¹ hconj
  rw [hθ] at h1
  have hβq : S.D.β q = pairVec a 4 := S.D.β.apply_symm_apply _
  show S.D.β (q * ⟨p * ((q⁻¹ : ↥S.D.W) : G) * p⁻¹, hconj⟩) = _
  have hinv : (pairVec a 4 : ↥(coreMod 5))⁻¹ = pairVec a 4 := coreMod_inv_eq _
  rw [map_mul, h1, map_inv, hβq]
  show pairVec a 4 * coreAct 5 σ (pairVec a 4)⁻¹ = pairVec a (σ a)
  rw [hinv, coreAct_pairVec, hσ4]
  exact pairVec_mul_pairVec_right a (σ a) 4

theorem CaseB.qvec_mem_BP (hB : S.CaseB) (X Y z : ZMod 2) : qvec X Y z ∈ S.BP := by
  have h1 : pairVec 0 1 ∈ S.BP := by
    have := hB.pairVec_mem_BP (σ := sA) (by simp [mem_klein]) sA_fix4 0
    rwa [show (sA : Perm (Fin 5)) 0 = 1 by decide] at this
  have h2 : pairVec 0 2 ∈ S.BP := by
    have := hB.pairVec_mem_BP (σ := sB) (by simp [mem_klein]) sB_fix4 0
    rwa [show (sB : Perm (Fin 5)) 0 = 2 by decide] at this
  have h3 : pairVec 0 3 ∈ S.BP := by
    have := hB.pairVec_mem_BP (σ := sC) (by simp [mem_klein]) sC_fix4 0
    rwa [show (sC : Perm (Fin 5)) 0 = 3 by decide] at this
  rw [qvec_eq_prod]
  refine S.BP.mul_mem (S.BP.mul_mem ?_ ?_) ?_ <;> split_ifs <;>
    first | exact S.BP.one_mem | assumption

theorem CaseB.mem_PP_iff_W (hB : S.CaseB) {g : G} (hg : g ∈ S.D.W) :
    g ∈ S.PP ↔ vcoord (S.D.β ⟨g, hg⟩) 4 = 0 := by
  constructor
  · intro hgP
    by_contra hne
    have h1 : vcoord (S.D.β ⟨g, hg⟩) 4 = 1 := by
      generalize vcoord (S.D.β ⟨g, hg⟩) 4 = c at hne
      revert c
      decide
    have hgB : S.D.β ⟨g, hg⟩ ∈ S.BP := S.mem_BP.2 ⟨g, hg, hgP, rfl⟩
    have hall : ∀ w : ↥S.D.W, (w : G) ∈ S.PP := by
      intro w
      apply S.mem_PP_of_mem_BP w.2
      by_cases h0 : vcoord (S.D.β w) 4 = 0
      · obtain ⟨X, Y, z, hu⟩ := exists_qvec h0
        rw [show (⟨(w : G), w.2⟩ : ↥S.D.W) = w from rfl, hu]
        exact hB.qvec_mem_BP X Y z
      · have h1' : vcoord (S.D.β w) 4 = 1 := by
          generalize vcoord (S.D.β w) 4 = c at h0
          revert c
          decide
        have hprod : S.D.β w * S.D.β ⟨g, hg⟩ ∈ S.BP := by
          obtain ⟨X, Y, z, hu⟩ := exists_qvec (u := S.D.β w * S.D.β ⟨g, hg⟩) (by
            rw [vcoord_mul, h1', h1]
            decide)
          rw [hu]
          exact hB.qvec_mem_BP X Y z
        have := S.BP.mul_mem hprod (S.BP.inv_mem hgB)
        rw [mul_inv_cancel_right] at this
        rwa [show (⟨(w : G), w.2⟩ : ↥S.D.W) = w from rfl]
    apply hB.not_Q_le_PP
    intro q hq
    exact hall ⟨q, S.mem_W_of_rOf_bot hB.rbot hq⟩
  · intro h
    obtain ⟨X, Y, z, hu⟩ := exists_qvec h
    refine S.mem_PP_of_mem_BP hg ?_
    rw [hu]
    exact hB.qvec_mem_BP X Y z

theorem x0_sq : S.x0 * S.x0 = 1 := by
  rw [x0_eq, qG_sq]

theorem qG_zero_zero (c : ZMod 2) : S.qG 0 0 c = 1 ∨ S.qG 0 0 c = S.x0 := by
  have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases this c with rfl | rfl
  · exact Or.inl S.qG_zero
  · exact Or.inr S.x0_eq.symm

theorem mul_eq_iff {e s : G} (he : e = 1 ∨ e = S.x0) :
    (e * s = 1 ∨ e * s = S.x0) ↔ (s = 1 ∨ s = S.x0) := by
  have hx := S.x0_sq
  rcases he with rfl | rfl
  · simp
  · constructor
    · rintro (h | h)
      · right
        have := congrArg (fun t => S.x0 * t) h
        simpa [← mul_assoc, hx] using this
      · left
        have := congrArg (fun t => S.x0 * t) h
        simpa [← mul_assoc, hx] using this
    · rintro (h | h)
      · right
        rw [h, mul_one]
      · left
        rw [h, hx]

theorem CaseB.exists_qG (hB : S.CaseB) {g : G} (hg : g ∈ S.D.W) (hgP : g ∈ S.PP) :
    ∃ X Y z, g = S.qG X Y z := by
  obtain ⟨X, Y, z, hu⟩ := exists_qvec ((hB.mem_PP_iff_W hg).1 hgP)
  refine ⟨X, Y, z, ?_⟩
  have := S.D.β.injective (hu.trans (S.β_qG X Y z).symm)
  exact congrArg Subtype.val this

theorem CaseB.mul_conj_mem (hB : S.CaseB) {p : G} (hpM : p ∈ M) {σ : Perm (Fin 5)}
    (hσ : σ = sA ∨ σ = sB ∨ σ = sC) (hθ : S.θ ⟨p, hpM⟩ = σ) {q : G} (hq : q ∈ S.D.W)
    (hqP : q ∈ S.PP) : q * (p * q * p⁻¹) = 1 ∨ q * (p * q * p⁻¹) = S.x0 := by
  obtain ⟨X, Y, z, rfl⟩ := hB.exists_qG hq hqP
  have hchar : ∀ a : ZMod 2, a + a = 0 := by decide
  have e1 : ∀ z Y : ZMod 2, z + (z + Y) = Y := by decide
  have e2 : ∀ z X Y : ZMod 2, z + (z + X + Y) = X + Y := by decide
  rcases hσ with rfl | rfl | rfl
  · rw [S.conj_qG hpM hθ (coreAct_sA X Y z), qG_mul, hchar, hchar, e1]
    exact S.qG_zero_zero Y
  · rw [S.conj_qG hpM hθ (coreAct_sB X Y z), qG_mul, hchar, hchar, e1]
    exact S.qG_zero_zero X
  · rw [S.conj_qG hpM hθ (coreAct_sC X Y z), qG_mul, hchar, hchar, e2]
    exact S.qG_zero_zero (X + Y)

@[expose] def SqOK (σ : Perm (Fin 5)) : Prop :=
  ∀ p : G, p ∈ S.PP → ∀ hp : p ∈ M, S.θ ⟨p, hp⟩ = σ → (p * p = 1 ∨ p * p = S.x0)

theorem CaseB.sq_iff (hB : S.CaseB) {p p' : G} (hp : p ∈ S.PP) (hp' : p' ∈ S.PP) (hpM : p ∈ M)
    (hp'M : p' ∈ M) {σ : Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB ∨ σ = sC)
    (h1 : S.θ ⟨p, hpM⟩ = σ) (h2 : S.θ ⟨p', hp'M⟩ = σ) :
    (p' * p' = 1 ∨ p' * p' = S.x0) ↔ (p * p = 1 ∨ p * p = S.x0) := by
  have hqM : p' * p⁻¹ ∈ M := M.mul_mem hp'M (M.inv_mem hpM)
  have hθq : S.θ ⟨p' * p⁻¹, hqM⟩ = 1 := by
    have : (⟨p' * p⁻¹, hqM⟩ : ↥M) = ⟨p', hp'M⟩ * ⟨p, hpM⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, h1, h2, mul_inv_cancel]
  have hqQ : p' * p⁻¹ ∈ pCoreOf 2 M := S.mem_Q_of_theta_eq_one hB.rsmall hqM hθq
  have hqW : p' * p⁻¹ ∈ S.D.W := S.mem_W_of_rOf_bot hB.rbot hqQ
  have hqP : p' * p⁻¹ ∈ S.PP := S.PP.mul_mem hp' (S.PP.inv_mem hp)
  have he := hB.mul_conj_mem hpM hσ h1 hqW hqP
  have e : p' * p' = ((p' * p⁻¹) * (p * (p' * p⁻¹) * p⁻¹)) * (p * p) := by group
  rw [e]
  exact S.mul_eq_iff he

theorem CaseB.not_sqOK_conj (_hB : S.CaseB) {σ : Perm (Fin 5)} (hσ : ¬ S.SqOK σ) :
    ¬ S.SqOK (tau3 * σ * tau3⁻¹) := by
  have hτ : tau3 ∈ altOn (vsupp (S.D.β ⟨S.x0, S.x0_mem_W⟩)) := by
    rw [S.vsupp_x0]
    exact tau3_mem
  obtain ⟨c, hcC, hcM, hcθ⟩ := S.exists_lift S.x0_mem_W (one_mem _)
    (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2) (altOn_le_setStab _ hτ)
  simp only [mul_one] at hcC
  have hcK : c ∈ CGOf S.x0 := (Subgroup.mem_inf.1 hcC).2
  have hcx : c * S.x0 * c⁻¹ = S.x0 := mem_centralizer_zpowers_iff.1 hcK
  unfold SqOK at hσ ⊢
  push Not at hσ
  obtain ⟨p, hp, hpM, hθp, hsq⟩ := hσ
  intro hall
  have hp'P : c * p * c⁻¹ ∈ S.PP := pCoreOf_normalized _ hcK hp
  have hp'M : c * p * c⁻¹ ∈ M := M.mul_mem (M.mul_mem hcM hpM) (M.inv_mem hcM)
  have hθ' : S.θ ⟨c * p * c⁻¹, hp'M⟩ = tau3 * σ * tau3⁻¹ := by
    have : (⟨c * p * c⁻¹, hp'M⟩ : ↥M) = ⟨c, hcM⟩ * ⟨p, hpM⟩ * ⟨c, hcM⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hcθ, hθp]
  have h := hall _ hp'P hp'M hθ'
  refine (not_or.2 hsq) ?_
  have e : c * p * c⁻¹ * (c * p * c⁻¹) = c * (p * p) * c⁻¹ := by group
  rw [e] at h
  rcases h with h | h
  · left
    have := congrArg (fun t => c⁻¹ * t * c) h
    simpa [mul_assoc] using this
  · right
    have := congrArg (fun t => c⁻¹ * t * c) h
    have h2 : c⁻¹ * S.x0 * c = S.x0 := by
      have := congrArg (fun t => c⁻¹ * t * c) hcx
      simpa [mul_assoc] using this.symm
    simpa [mul_assoc, h2] using this

theorem CaseB.theta_eq_one_of_cent (hB : S.CaseB) {m : G} (hm : m ∈ M)
    (hc : m ∈ Subgroup.centralizer ((S.D.W ⊓ S.PP : Subgroup G) : Set G)) :
    S.θ ⟨m, hm⟩ = 1 := by
  have hfix : ∀ X Y z : ZMod 2, coreAct 5 (S.θ ⟨m, hm⟩) (qvec X Y z) = qvec X Y z := by
    intro X Y z
    have hW := S.qG_mem_W X Y z
    have hq : S.qG X Y z ∈ S.D.W ⊓ S.PP :=
      ⟨hW, (hB.mem_PP_iff_W hW).2 (by rw [S.β_qG]; rfl)⟩
    have h1 : S.qG X Y z * m = m * S.qG X Y z := Subgroup.mem_centralizer_iff.1 hc _ hq
    have hW' : m * S.qG X Y z * m⁻¹ ∈ S.D.W := S.W_normalized hm hW
    have h2 := S.θ_spec ⟨m, hm⟩ ⟨S.qG X Y z, hW⟩ hW'
    have e : (⟨m * S.qG X Y z * m⁻¹, hW'⟩ : ↥S.D.W) = ⟨S.qG X Y z, hW⟩ :=
      Subtype.ext (by
        show m * S.qG X Y z * m⁻¹ = S.qG X Y z
        rw [← h1]
        group)
    rw [e, S.β_qG] at h2
    exact h2.symm
  set σ := S.θ ⟨m, hm⟩ with hσ
  have hfix0 : ∀ a : Fin 5, a ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      coreAct 5 σ (pairVec 0 a) = pairVec 0 a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · rw [pairVec_self, map_one]
    · rw [pairVec_zero_one]; exact hfix 1 0 0
    · rw [pairVec_zero_two]; exact hfix 0 1 0
    · rw [pairVec_zero_three]; exact hfix 1 1 1
  have hfixab : ∀ a ∈ ({0, 1, 2, 3} : Finset (Fin 5)), ∀ b ∈ ({0, 1, 2, 3} : Finset (Fin 5)),
      coreAct 5 σ (pairVec a b) = pairVec a b := by
    intro a ha b hb
    rw [← pairVec_mul 0 a b, map_mul, hfix0 a ha, hfix0 b hb]
  have hJ := fix_of_fix_pairs (J := ({0, 1, 2, 3} : Finset (Fin 5))) (by decide) hfixab
  exact perm_eq_one_of_fix σ (hJ 0 (by decide)) (hJ 1 (by decide)) (hJ 2 (by decide))
    (hJ 3 (by decide))

theorem CaseB.sqOK_of_sq (hB : S.CaseB) {σ : Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB ∨ σ = sC)
    {p : G} (hp : p ∈ S.PP) (hpM : p ∈ M) (h1 : S.θ ⟨p, hpM⟩ = σ)
    (hpp : p * p = 1 ∨ p * p = S.x0) : S.SqOK σ :=
  fun _ hp' hp'M h2 => (hB.sq_iff hp hp' hpM hp'M hσ h1 h2).2 hpp

theorem CaseB.false_of_not_sqOK (hB : S.CaseB)
    (h : ¬ S.SqOK sA ∧ ¬ S.SqOK sB ∧ ¬ S.SqOK sC) : False := by
  have hinv : ∀ p ∈ S.PP, p * p = 1 → p ∈ S.D.W := by
    intro p hp hp1
    have hpM := hB.PP_le_M hp
    rcases mem_klein.1 (hB.theta_mem_klein hp hpM) with h1 | h1 | h1 | h1
    · exact S.mem_W_of_rOf_bot hB.rbot (S.mem_Q_of_theta_eq_one hB.rsmall hpM h1)
    · exact absurd (hB.sqOK_of_sq (Or.inl rfl) hp hpM h1 (Or.inl hp1)) h.1
    · exact absurd (hB.sqOK_of_sq (Or.inr (Or.inl rfl)) hp hpM h1 (Or.inl hp1)) h.2.1
    · exact absurd (hB.sqOK_of_sq (Or.inr (Or.inr rfl)) hp hpM h1 (Or.inl hp1)) h.2.2
  have hQ0norm : ∀ k ∈ CGOf S.x0, ∀ q ∈ (S.D.W ⊓ S.PP : Subgroup G),
      k * q * k⁻¹ ∈ (S.D.W ⊓ S.PP : Subgroup G) := by
    intro k hk q hq
    have hkP : k * q * k⁻¹ ∈ S.PP := pCoreOf_normalized _ hk hq.2
    refine ⟨hinv _ hkP ?_, hkP⟩
    have hq2 : q * q = 1 := by
      have := hB.qelem q (S.W_le_Q hq.1)
      simpa [pow_two] using this
    calc k * q * k⁻¹ * (k * q * k⁻¹) = k * (q * q) * k⁻¹ := by group
      _ = 1 := by rw [hq2]; group
  have hBQ : (S.D.W ⊓ S.PP : Subgroup G) ≤ pCoreOf 2 M := inf_le_left.trans S.W_le_Q
  have hBne : (S.D.W ⊓ S.PP : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hW := S.qG_mem_W 1 0 0
    have hmem : S.qG 1 0 0 ∈ (S.D.W ⊓ S.PP : Subgroup G) :=
      ⟨hW, (hB.mem_PP_iff_W hW).2 (by rw [S.β_qG]; rfl)⟩
    rw [hbot, Subgroup.mem_bot, ← S.qG_zero] at hmem
    have := (S.qG_inj hmem).1
    revert this
    decide
  have hO2 : pCoreOf 2 (M ⊓ Subgroup.centralizer ((S.D.W ⊓ S.PP : Subgroup G) : Set G)) ≤
      pCoreOf 2 M := by
    intro m hm
    have hm' := pCoreOf_le_self _ hm
    exact S.mem_Q_of_theta_eq_one hB.rsmall hm'.1 (hB.theta_eq_one_of_cent hm'.1 hm'.2)
  have hNM := (S.centralizer_le_M S.hyp.charTwo hB.tight.abelian hBQ hBne hO2).2
  apply hB.notM
  intro k hk
  apply hNM
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    exact hQ0norm k hk q hq
  · intro hq
    have := hQ0norm k⁻¹ ((CGOf S.x0).inv_mem hk) _ hq
    simpa [mul_assoc] using this

theorem CaseB.sqOK_all (hB : S.CaseB) : S.SqOK sA ∧ S.SqOK sB ∧ S.SqOK sC := by
  by_contra hcon
  have hnot : ¬ S.SqOK sA ∨ ¬ S.SqOK sB ∨ ¬ S.SqOK sC := by
    by_contra h'
    push Not at h'
    exact hcon h'
  rcases hnot with h | h | h
  · have h2 : ¬ S.SqOK sB := by simpa [tau3_sA] using hB.not_sqOK_conj h
    have h3 : ¬ S.SqOK sC := by simpa [tau3_sB] using hB.not_sqOK_conj h2
    exact hB.false_of_not_sqOK ⟨h, h2, h3⟩
  · have h3 : ¬ S.SqOK sC := by simpa [tau3_sB] using hB.not_sqOK_conj h
    have h1 : ¬ S.SqOK sA := by simpa [tau3_sC] using hB.not_sqOK_conj h3
    exact hB.false_of_not_sqOK ⟨h1, h, h3⟩
  · have h1 : ¬ S.SqOK sA := by simpa [tau3_sC] using hB.not_sqOK_conj h
    have h2 : ¬ S.SqOK sB := by simpa [tau3_sA] using hB.not_sqOK_conj h1
    exact hB.false_of_not_sqOK ⟨h1, h2, h⟩

theorem CaseB.qG_mem_PP (hB : S.CaseB) (X Y z : ZMod 2) : S.qG X Y z ∈ S.PP :=
  (hB.mem_PP_iff_W (S.qG_mem_W X Y z)).2 (by rw [S.β_qG]; rfl)

theorem CaseB.PP_le_CG (_hB : S.CaseB) : S.PP ≤ CGOf S.x0 := pCoreOf_le_self _

theorem CaseB.exists_invol_lift (hB : S.CaseB) {σ : Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB)
    (hsq : S.SqOK σ) : ∃ p : G, ∃ _ : p ∈ S.PP, ∃ hpM : p ∈ M,
      S.θ ⟨p, hpM⟩ = σ ∧ p * p = 1 := by
  have hσ' : σ = sA ∨ σ = sB ∨ σ = sC := by
    rcases hσ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨p, hp, hpM, hθ⟩ := hB.exists_lift (σ := σ) (by
    rcases hσ with rfl | rfl <;> simp [mem_klein])
  rcases hsq p hp hpM hθ with h1 | h1
  · exact ⟨p, hp, hpM, hθ, h1⟩
  ·
    obtain ⟨X, Y, z, hqx⟩ : ∃ X Y z : ZMod 2, S.qG X Y z * (p * S.qG X Y z * p⁻¹) = S.x0 := by
      rcases hσ with rfl | rfl
      · refine ⟨0, 1, 0, ?_⟩
        rw [S.conj_qG hpM hθ (coreAct_sA 0 1 0), qG_mul, S.x0_eq]
        congr 1
      · refine ⟨1, 0, 0, ?_⟩
        rw [S.conj_qG hpM hθ (coreAct_sB 1 0 0), qG_mul, S.x0_eq]
        congr 1
    have hqP := hB.qG_mem_PP X Y z
    have hqM : S.qG X Y z ∈ M := hB.PP_le_M hqP
    have hθq : S.θ ⟨S.qG X Y z, hqM⟩ = 1 :=
      S.theta_eq_one_of_mem_Q (S.W_le_Q (S.qG_mem_W X Y z))
    have hqpM : S.qG X Y z * p ∈ M := M.mul_mem hqM hpM
    refine ⟨S.qG X Y z * p, S.PP.mul_mem hqP hp, hqpM, ?_, ?_⟩
    · have : (⟨S.qG X Y z * p, hqpM⟩ : ↥M) = ⟨S.qG X Y z, hqM⟩ * ⟨p, hpM⟩ := rfl
      rw [this, map_mul, hθq, hθ, one_mul]
    · have e : S.qG X Y z * p * (S.qG X Y z * p) =
          (S.qG X Y z * (p * S.qG X Y z * p⁻¹)) * (p * p) := by group
      rw [e, hqx, h1, S.x0_sq]

theorem CaseB.exists_lifts (hB : S.CaseB) :
    ∃ p₁ p₂ : G, ∃ (_ : p₁ ∈ S.PP) (_ : p₂ ∈ S.PP) (hM₁ : p₁ ∈ M) (hM₂ : p₂ ∈ M),
      S.θ ⟨p₁, hM₁⟩ = sA ∧ S.θ ⟨p₂, hM₂⟩ = sB ∧ p₁ * p₁ = 1 ∧ p₂ * p₂ = 1 ∧
        p₁ * p₂ = p₂ * p₁ := by
  obtain ⟨hA', hB', hC'⟩ := hB.sqOK_all
  obtain ⟨p₁, h1, hM₁, hθ₁, hs₁⟩ := hB.exists_invol_lift (Or.inl rfl) hA'
  obtain ⟨p₂, h2, hM₂, hθ₂, hs₂⟩ := hB.exists_invol_lift (Or.inr rfl) hB'
  have hM₃ : p₁ * p₂ ∈ M := M.mul_mem hM₁ hM₂
  have hθ₃ : S.θ ⟨p₁ * p₂, hM₃⟩ = sC := by
    have : (⟨p₁ * p₂, hM₃⟩ : ↥M) = ⟨p₁, hM₁⟩ * ⟨p₂, hM₂⟩ := rfl
    rw [this, map_mul, hθ₁, hθ₂, sA_mul_sB]
  rcases hC' (p₁ * p₂) (S.PP.mul_mem h1 h2) hM₃ hθ₃ with h3 | h3
  · exact ⟨p₁, p₂, h1, h2, hM₁, hM₂, hθ₁, hθ₂, hs₁, hs₂, comm_of_sq_one hs₁ hs₂ h3⟩
  ·
    have hqP := hB.qG_mem_PP 0 1 0
    have hqM : S.qG 0 1 0 ∈ M := hB.PP_le_M hqP
    have hθq : S.θ ⟨S.qG 0 1 0, hqM⟩ = 1 :=
      S.theta_eq_one_of_mem_Q (S.W_le_Q (S.qG_mem_W 0 1 0))
    have hM₂' : p₂ * S.qG 0 1 0 ∈ M := M.mul_mem hM₂ hqM
    have hθ₂' : S.θ ⟨p₂ * S.qG 0 1 0, hM₂'⟩ = sB := by
      have : (⟨p₂ * S.qG 0 1 0, hM₂'⟩ : ↥M) = ⟨p₂, hM₂⟩ * ⟨S.qG 0 1 0, hqM⟩ := rfl
      rw [this, map_mul, hθ₂, hθq, mul_one]
    have hs₂' : p₂ * S.qG 0 1 0 * (p₂ * S.qG 0 1 0) = 1 := by
      have e : p₂ * S.qG 0 1 0 * (p₂ * S.qG 0 1 0) =
          (p₂ * S.qG 0 1 0 * p₂⁻¹) * (p₂ * p₂) * S.qG 0 1 0 := by group
      rw [e, S.conj_qG hM₂ hθ₂ (coreAct_sB 0 1 0), hs₂, mul_one, qG_mul, ← S.qG_zero]
      congr 1
    have hc : p₁ * (p₂ * S.qG 0 1 0) = (p₂ * S.qG 0 1 0) * p₁ := by
      refine comm_of_sq_one hs₁ hs₂' ?_
      have e : p₁ * (p₂ * S.qG 0 1 0) * (p₁ * (p₂ * S.qG 0 1 0)) =
          ((p₁ * p₂) * S.qG 0 1 0 * (p₁ * p₂)⁻¹) * ((p₁ * p₂) * (p₁ * p₂)) * S.qG 0 1 0 := by
        group
      rw [e, S.conj_qG hM₃ hθ₃ (coreAct_sC 0 1 0), h3, S.x0_eq, qG_mul, qG_mul, ← S.qG_zero]
      congr 1
    exact ⟨p₁, p₂ * S.qG 0 1 0, h1, S.PP.mul_mem h2 hqP, hM₁, hM₂', hθ₁, hθ₂', hs₁, hs₂', hc⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
