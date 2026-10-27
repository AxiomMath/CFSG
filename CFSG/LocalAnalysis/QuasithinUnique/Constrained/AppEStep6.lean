module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep5

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

@[expose] def cB (S V : Subgroup G) : Subgroup G := baum S ⊓ centralizer (V : Set G)

omit [Finite G] in
theorem mem_cB {S V : Subgroup G} {g : G} :
    g ∈ cB S V ↔ g ∈ baum S ∧ ∀ v ∈ V, v * g = g * v :=
  ⟨fun h => ⟨h.1, fun v hv => Subgroup.mem_centralizer_iff.1 h.2 v hv⟩,
    fun h => ⟨h.1, Subgroup.mem_centralizer_iff.mpr h.2⟩⟩

omit [Finite G] in
theorem cB_le_baum (S V : Subgroup G) : cB S V ≤ baum S := inf_le_left

omit [Finite G] in
theorem baum_le_normalizer_cB {S V : Subgroup G} (hV : baum S ≤ normalizer (V : Set G)) :
    baum S ≤ normalizer ((cB S V : Subgroup G) : Set G) := fun _ hg =>
  C5.mem_normalizer_inf (Subgroup.le_normalizer hg) (C5.mem_normalizer_centralizer (hV hg))

omit [Finite G] in
theorem elemAb_le_baum {S A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ baum S :=
  (GammaExtra.le_thompsonJ hA).trans (C5.thompsonJ_le_baum' S)

theorem card_mul_card_inf {B Qa Qb : Subgroup G} (hsup : Qa ⊔ Qb = B)
    (hN : Qa ≤ normalizer (Qb : Set G)) :
    Nat.card ↥B * Nat.card ↥(Qa ⊓ Qb) = Nat.card ↥Qa * Nat.card ↥Qb := by
  have := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rwa [hsup] at this

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem Q₁_sup_Q₂ : cB S (blockU L) ⊔ cB S (conjSubgroup (blockU L) t) = baum S := by
  refine le_antisymm (sup_le (cB_le_baum S _) (cB_le_baum S _)) ?_
  refine P.kf₁.supQ.symm.le.trans (sup_le ?_ le_sup_left)
  have h := P.Ux_le_Q₂
  rw [P.loc₂.rk.Q_eq] at h
  exact h.trans le_sup_right

theorem Q₁_sup_Q₂' : cB S (blockU L) ⊔ cB S (conjSubgroup (conjSubgroup (blockU L) t) x) =
    baum S := by
  refine le_antisymm (sup_le (cB_le_baum S _) (cB_le_baum S _)) ?_
  refine P.kf₁.supQ.symm.le.trans (sup_le ?_ le_sup_left)
  intro v hv
  refine Subgroup.mem_sup_right ?_
  exact mem_cB.2 ⟨P.kf₁.Ux_le_B hv, fun a ha => (P.comm_U₁x_U₂x v hv a ha).symm⟩

theorem Q₁'_sup_Q₂ : cB S (conjSubgroup (blockU L) x) ⊔ cB S (conjSubgroup (blockU L) t) =
    baum S := by
  refine le_antisymm (sup_le (cB_le_baum S _) (cB_le_baum S _)) ?_
  have hB := P.kf₂.supQ
  rw [P.loc₂.rk.Q_eq] at hB
  refine hB.symm.le.trans (sup_le ?_ le_sup_right)
  intro v hv
  refine Subgroup.mem_sup_left ?_
  exact mem_cB.2 ⟨P.kf₂.Ux_le_B hv, fun a ha => P.comm_U₁x_U₂x a ha v hv⟩

theorem Q₁'_sup_Q₂' : cB S (conjSubgroup (blockU L) x) ⊔
    cB S (conjSubgroup (conjSubgroup (blockU L) t) x) = baum S := by
  have e1 := P.kf₁.Qx
  have e2 := P.kf₂.Qx
  rw [P.loc₂.rk.Q_eq] at e2
  show baum S ⊓ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) ⊔
    baum S ⊓ centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G) =
      baum S
  rw [← e1, ← e2, ← C5.conjSubgroup_sup]
  have := P.Q₁_sup_Q₂
  unfold cB at this
  rw [this, C5.conjSubgroup_eq_self P.hxB]

theorem card_Q₂ : Nat.card ↥(cB S (conjSubgroup (blockU L) t)) = Nat.card ↥(cB S (blockU L)) := by
  show Nat.card ↥(baum S ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)) =
    Nat.card ↥(baum S ⊓ centralizer (blockU L : Set G))
  rw [← P.loc₂.rk.Q_eq, C5.card_conjSubgroup]

theorem card_Q₁' : Nat.card ↥(cB S (conjSubgroup (blockU L) x)) = Nat.card ↥(cB S (blockU L)) := by
  show Nat.card ↥(baum S ⊓ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G)) =
    Nat.card ↥(baum S ⊓ centralizer (blockU L : Set G))
  rw [← P.kf₁.Qx, C5.card_conjSubgroup]

theorem card_Q₂' : Nat.card ↥(cB S (conjSubgroup (conjSubgroup (blockU L) t) x)) =
    Nat.card ↥(cB S (blockU L)) := by
  show Nat.card ↥(baum S ⊓
      centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G)) =
    Nat.card ↥(baum S ⊓ centralizer (blockU L : Set G))
  rw [← P.kf₂.Qx, C5.card_conjSubgroup, C5.card_conjSubgroup]

theorem card_Y :
    Nat.card ↥(cB S (blockU L) ⊓ cB S (conjSubgroup (conjSubgroup (blockU L) t) x)) =
        Nat.card ↥(cB S (blockU L) ⊓ cB S (conjSubgroup (blockU L) t)) ∧
      Nat.card ↥(cB S (conjSubgroup (blockU L) x) ⊓ cB S (conjSubgroup (blockU L) t)) =
        Nat.card ↥(cB S (blockU L) ⊓ cB S (conjSubgroup (blockU L) t)) ∧
      Nat.card ↥(cB S (conjSubgroup (blockU L) x) ⊓
          cB S (conjSubgroup (conjSubgroup (blockU L) t) x)) =
        Nat.card ↥(cB S (blockU L) ⊓ cB S (conjSubgroup (blockU L) t)) := by
  have hB2 : baum S ≤ normalizer ((cB S (conjSubgroup (blockU L) t) : Subgroup G) : Set G) :=
    baum_le_normalizer_cB P.loc₂.rk.B_le_normU
  have hB2' : baum S ≤
      normalizer ((cB S (conjSubgroup (conjSubgroup (blockU L) t) x) : Subgroup G) : Set G) :=
    baum_le_normalizer_cB (P.loc₂.rk.B_le_normU_conj P.hxB)
  have k12 := card_mul_card_inf P.Q₁_sup_Q₂ ((cB_le_baum S _).trans hB2)
  have k12' := card_mul_card_inf P.Q₁_sup_Q₂' ((cB_le_baum S _).trans hB2')
  have k1'2 := card_mul_card_inf P.Q₁'_sup_Q₂ ((cB_le_baum S _).trans hB2)
  have k1'2' := card_mul_card_inf P.Q₁'_sup_Q₂' ((cB_le_baum S _).trans hB2')
  rw [P.card_Q₂] at k12
  rw [P.card_Q₂'] at k12'
  rw [P.card_Q₁', P.card_Q₂] at k1'2
  rw [P.card_Q₁', P.card_Q₂'] at k1'2'
  have hpos : 0 < Nat.card ↥(baum S) := Nat.card_pos
  refine ⟨Nat.eq_of_mul_eq_mul_left hpos (k12'.trans k12.symm),
    Nat.eq_of_mul_eq_mul_left hpos (k1'2.trans k12.symm),
    Nat.eq_of_mul_eq_mul_left hpos (k1'2'.trans k12.symm)⟩

theorem card_elemAb_le {A : Subgroup G} (hA : ElemAb2 A) (hAB : A ≤ baum S) :
    Nat.card ↥A ≤ Nat.card ↥(cB S (blockU L) ⊓ cB S (conjSubgroup (blockU L) t)) := by
  obtain ⟨h12', h1'2, h1'2'⟩ := P.card_Y
  obtain ⟨hd1, hd2⟩ := P.elemAb_dichotomy hA hAB
  rcases hd1 with h1 | h1' <;> rcases hd2 with h2 | h2'
  · exact Subgroup.card_le_of_le (le_inf h1 h2)
  · exact (Subgroup.card_le_of_le (le_inf h1 h2')).trans h12'.le
  · exact (Subgroup.card_le_of_le (le_inf h1' h2)).trans h1'2.le
  · exact (Subgroup.card_le_of_le (le_inf h1' h2')).trans h1'2'.le

theorem Y₁₁_eq : cB S (blockU L) ⊓ cB S (conjSubgroup (blockU L) t) =
    baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) := by
  refine le_antisymm ?_ ?_
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ :=
      P.B_decomp_C (mem_cB.1 hb1).1 (mem_cB.1 hb1).2 (mem_cB.1 hb2).2
    have hWU := P.loc.rk.W_le_U
    have hWU₂ : conjSubgroup W t ≤ conjSubgroup (blockU L) t := conjSubgroup_mono hWU t
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left (hWU hx₁)))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left hu₁))
        (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right (hWU₂ ha)))
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right hu₂))
            (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left (hWU he)))
              (Subgroup.mem_sup_left hf)))))
  · refine sup_le ?_ (sup_le ?_ ?_)
    · intro f hf
      obtain ⟨hfB, hfL, hfL₂⟩ := P.D.mem_baumD_iff.1 hf
      exact ⟨mem_cB.2 ⟨hfB, fun v hv => hfL v (P.U₁_le_L hv)⟩,
        mem_cB.2 ⟨hfB, fun v hv => hfL₂ v (P.U₂_le_L₂ hv)⟩⟩
    · intro u hu
      exact ⟨mem_cB.2 ⟨P.U₁_le_B hu, fun v hv => P.loc.rk.U_comm v hv u hu⟩,
        mem_cB.2 ⟨P.U₁_le_B hu, fun v hv =>
          (P.D.comm_elem u (P.U₁_le_L hu) v (P.U₂_le_L₂ hv)).symm⟩⟩
    · intro u hu
      exact ⟨mem_cB.2 ⟨P.U₂_le_B hu, fun v hv =>
          P.D.comm_elem v (P.U₁_le_L hv) u (P.U₂_le_L₂ hu)⟩,
        mem_cB.2 ⟨P.U₂_le_B hu, fun v hv => P.loc₂.rk.U_comm v hv u hu⟩⟩

theorem Y₂₂_eq : cB S (conjSubgroup (blockU L) x) ⊓
    cB S (conjSubgroup (conjSubgroup (blockU L) t) x) =
    baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := by
  rw [C5.conjSubgroup_sup]
  refine le_antisymm ?_ ?_
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ := P.B_decomp (mem_cB.1 hb1).1
    obtain ⟨-, hX₁, -, hX₂⟩ := P.prod_cent hx₁ hu₁ ha hu₂ he hf
    have hu₁W : u₁ ∈ W := hX₁.1 (Subgroup.mem_centralizer_iff.mpr (mem_cB.1 hb1).2)
    have hu₂W : u₂ ∈ conjSubgroup W t := hX₂.1 (Subgroup.mem_centralizer_iff.mpr (mem_cB.1 hb2).2)
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left hx₁))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left (P.W_le_X hu₁W)))
        (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right ha))
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right (P.W₂_le_Y hu₂W)))
            (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left (P.W_le_X he)))
              (Subgroup.mem_sup_left hf)))))
  · refine sup_le ?_ (sup_le ?_ ?_)
    · intro f hf
      have hfX := P.D_comm_X hf
      exact ⟨mem_cB.2 ⟨(P.D.mem_baumD_iff.1 hf).1, fun v hv => hfX.1 v hv⟩,
        mem_cB.2 ⟨(P.D.mem_baumD_iff.1 hf).1, fun v hv => hfX.2 v hv⟩⟩
    · intro u hu
      exact ⟨mem_cB.2 ⟨P.X_le_B hu, fun v hv => P.loc.rk.conj_comm x v hv u hu⟩,
        mem_cB.2 ⟨P.X_le_B hu, fun v hv => (P.comm_U₁x_U₂x u hu v hv).symm⟩⟩
    · intro a ha
      exact ⟨mem_cB.2 ⟨P.Y_le_B ha, fun v hv => P.comm_U₁x_U₂x v hv a ha⟩,
        mem_cB.2 ⟨P.Y_le_B ha, fun v hv => P.loc₂.rk.conj_comm x v hv a ha⟩⟩

theorem elemAb_DU : ElemAb2 (baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t)) :=
  ElemAb2.sup P.D_elemAb P.elemAb_U fun _ hd u hu =>
    (Subgroup.mem_centralizer_iff.1 (P.D_le_N0 hd).2 u (Subgroup.mem_sup_left hu)).symm

theorem elemAb_DX :
    ElemAb2 (baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) :=
  ElemAb2.sup P.D_elemAb (P.elemAb_U.conjSubgroup x) fun _ hd u hu =>
    (Subgroup.mem_centralizer_iff.1 (P.D_le_N0 hd).2 u (Subgroup.mem_sup_right hu)).symm

theorem DU_le_S : baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ≤ S :=
  sup_le (baumD_le_S S L) (sup_le (P.U₁_le_B.trans inf_le_left) (P.U₂_le_B.trans inf_le_left))

theorem DX_le_S :
    baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x ≤ S := by
  refine sup_le (baumD_le_S S L) ?_
  rw [C5.conjSubgroup_sup]
  exact sup_le (P.X_le_B.trans inf_le_left) (P.Y_le_B.trans inf_le_left)

theorem isMax_DU :
    IsMaxElemAbelian S (baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t)) := by
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian S
  have hcard : Nat.card ↥A₀ ≤
      Nat.card ↥(baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t)) := by
    rw [← P.Y₁₁_eq]
    exact P.card_elemAb_le (isElemAbelian_two_iff.1 hA₀.2.1) (elemAb_le_baum hA₀)
  exact ⟨P.DU_le_S, isElemAbelian_two_iff.2 P.elemAb_DU,
    fun B' hB'S hB'e => (hA₀.2.2 B' hB'S hB'e).trans hcard⟩

theorem isMax_DX :
    IsMaxElemAbelian S (baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) := by
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian S
  have hcard : Nat.card ↥A₀ ≤
      Nat.card ↥(baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) := by
    rw [← P.Y₂₂_eq, P.card_Y.2.2]
    exact P.card_elemAb_le (isElemAbelian_two_iff.1 hA₀.2.1) (elemAb_le_baum hA₀)
  exact ⟨P.DX_le_S, isElemAbelian_two_iff.2 P.elemAb_DX,
    fun B' hB'S hB'e => (hA₀.2.2 B' hB'S hB'e).trans hcard⟩

theorem thompsonJ_eq : thompsonJ S = baum S := by
  refine le_antisymm (C5.thompsonJ_le_baum' S) ?_
  refine P.B_eq_sup.le.trans (sup_le ?_ ?_)
  · exact GammaExtra.le_thompsonJ P.isMax_DU
  · exact le_sup_right.trans (GammaExtra.le_thompsonJ P.isMax_DX)

theorem conj_DU {s : G} (hs : s ∈ S) :
    conjSubgroup (baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t)) s =
      baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) := by
  rw [C5.conjSubgroup_sup, C5.conjSubgroup_eq_self (S_le_normalizer_baumD S L hs),
    P.D.conj_U_sup hs]

theorem conj_DX {s : G} (hs : s ∈ S) :
    conjSubgroup (baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) s =
      baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := by
  have hs' : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 P.hxN s).1 hs
  have e : conjSubgroup (conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) s =
      conjSubgroup (conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) (x * s * x⁻¹)) x := by
    simp only [conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one]
  rw [C5.conjSubgroup_sup, C5.conjSubgroup_eq_self (S_le_normalizer_baumD S L hs), e,
    P.D.conj_U_sup hs']

theorem invariant_members_iff {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    (∀ s ∈ S, conjSubgroup A s = A) ↔
      (A = baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ∨
        A = baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) := by
  constructor
  · intro hinv
    have hinvt := hinv t P.D.ht
    have hAB : A ≤ baum S := elemAb_le_baum hA
    have hAe : ElemAb2 A := isElemAbelian_two_iff.1 hA.2.1
    obtain ⟨hd1, -⟩ := P.elemAb_dichotomy hAe hAB
    rcases hd1 with h1 | h1
    · left
      have h2 : A ≤ cB S (conjSubgroup (blockU L) t) := by
        have := conjSubgroup_mono h1 t
        rw [hinvt, P.loc₂.rk.Q_eq] at this
        exact this
      have hle : A ≤ baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) := by
        rw [← P.Y₁₁_eq]
        exact le_inf h1 h2
      exact Subgroup.eq_of_le_of_card_ge hle (hA.2.2 _ P.DU_le_S (isElemAbelian_two_iff.2 P.elemAb_DU))
    · right
      have h2 : A ≤ cB S (conjSubgroup (conjSubgroup (blockU L) t) x) := by
        have := conjSubgroup_mono h1 t
        rw [hinvt, C5.conjSubgroup_inf, C5.conjSubgroup_eq_self P.D.t_normalizer_baum,
          C5.conjSubgroup_centralizer, P.Ux_t] at this
        exact this
      have h1' : A ≤ cB S (conjSubgroup (blockU L) x) := h1
      have hle : A ≤ baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := by
        rw [← P.Y₂₂_eq]
        exact le_inf h1' h2
      exact Subgroup.eq_of_le_of_card_ge hle (hA.2.2 _ P.DX_le_S (isElemAbelian_two_iff.2 P.elemAb_DX))
  · rintro (rfl | rfl) s hs
    · exact P.conj_DU hs
    · exact P.conj_DX hs

end Setup

end CFSG.QuasithinUnique.AppE
