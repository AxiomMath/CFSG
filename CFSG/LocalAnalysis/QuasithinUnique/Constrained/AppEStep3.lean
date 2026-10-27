module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep2

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

omit [Finite G] in
theorem S_le_normalizer_baumD (S L : Subgroup G) :
    S ≤ normalizer ((baumD S L : Subgroup G) : Set G) := by
  intro g hg
  have hB : g ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg)
  have hK : g ∈ normalizer ((conjJoin S L : Subgroup G) : Set G) :=
    C56.S_le_normalizer_conjJoin L hg
  exact C5.mem_normalizer_inf hB (C5.mem_normalizer_centralizer hK)

omit [Finite G] in
theorem baumD_le_baum (S L : Subgroup G) : baumD S L ≤ baum S := inf_le_left

omit [Finite G] in
theorem baumD_le_S (S L : Subgroup G) : baumD S L ≤ S := (baumD_le_baum S L).trans inf_le_left

omit [Finite G] in
@[expose] def N0 (S L : Subgroup G) (t x : G) : Subgroup G :=
  baum S ⊓ centralizer ((blockU L ⊔ conjSubgroup (blockU L) t ⊔
    conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x : Subgroup G) : Set G)

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem hne : S ≠ M₀ := by
  intro h
  have h2 := P.h2
  rw [← h] at h2
  simp at h2

theorem X_le_B : conjSubgroup (blockU L) x ≤ baum S := P.kf₁.Ux_le_B

theorem Y_le_B : conjSubgroup (conjSubgroup (blockU L) t) x ≤ baum S := P.kf₂.Ux_le_B

theorem U₁_le_B : blockU L ≤ baum S := P.loc.rk.U_le_B

theorem U₂_le_B : conjSubgroup (blockU L) t ≤ baum S := P.loc₂.rk.U_le_B

theorem elemAb_U : ElemAb2 (blockU L ⊔ conjSubgroup (blockU L) t) := by
  have hU₁ : ElemAb2 (blockU L) := ⟨P.loc.rk.U_comm, C1.blockU_sq P.D.hL⟩
  refine ElemAb2.sup hU₁ (hU₁.conjSubgroup t) fun u hu v hv => ?_
  exact P.D.comm_elem u (P.U₁_le_L hu) v (P.U₂_le_L₂ hv)

theorem B_eq_sup : baum S = baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
    conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := by
  apply le_antisymm
  · intro b hb
    obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ := P.B_decomp hb
    have hXU : conjSubgroup (blockU L) x ≤
        conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x :=
      conjSubgroup_mono le_sup_left x
    have hYU : conjSubgroup (conjSubgroup (blockU L) t) x ≤
        conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x :=
      conjSubgroup_mono le_sup_right x
    have h1 : ∀ g ∈ blockU L, g ∈ baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
        conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := fun g hg =>
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_sup_left hg))
    have h2 : ∀ g ∈ conjSubgroup (blockU L) t, g ∈ baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
        conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := fun g hg =>
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_sup_right hg))
    have h3 : ∀ g ∈ conjSubgroup (blockU L) x, g ∈ baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
        conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := fun g hg =>
      Subgroup.mem_sup_right (hXU hg)
    have h4 : ∀ g ∈ conjSubgroup (conjSubgroup (blockU L) t) x,
        g ∈ baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
          conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := fun g hg =>
      Subgroup.mem_sup_right (hYU hg)
    refine Subgroup.mul_mem _ (h3 _ hx₁) (Subgroup.mul_mem _ (h1 _ hu₁)
      (Subgroup.mul_mem _ (h4 _ ha) (Subgroup.mul_mem _ (h2 _ hu₂)
        (Subgroup.mul_mem _ (h1 _ (P.loc.rk.W_le_U he)) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hf))))))
  · refine sup_le (sup_le (baumD_le_baum S L) (sup_le P.U₁_le_B P.U₂_le_B)) ?_
    rw [C5.conjSubgroup_sup]
    exact sup_le P.X_le_B P.Y_le_B

theorem D_le_N0 : baumD S L ≤ N0 S L t x := by
  intro f hf
  obtain ⟨hfB, hfL, hfL₂⟩ := P.D.mem_baumD_iff.1 hf
  have hfX := P.D_comm_X hf
  refine ⟨hfB, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hcen : f ∈ centralizer ((blockU L ⊔ conjSubgroup (blockU L) t ⊔
      conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x : Subgroup G) : Set G) := by
    refine C56.mem_centralizer_sup (A := blockU L ⊔ conjSubgroup (blockU L) t)
      (B := conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x) ?_ ?_
    · intro a ha
      have := C56.mem_centralizer_sup (A := blockU L) (B := conjSubgroup (blockU L) t)
        (u := f) (fun a ha => hfL a (P.U₁_le_L ha)) (fun a ha => hfL₂ a (P.U₂_le_L₂ ha))
      exact (Subgroup.mem_centralizer_iff.1 this a ha)
    · intro a ha
      rw [C5.conjSubgroup_sup] at ha
      have := C56.mem_centralizer_sup (A := conjSubgroup (blockU L) x)
        (B := conjSubgroup (conjSubgroup (blockU L) t) x) (u := f)
        (fun a ha => hfX.1 a ha) (fun a ha => hfX.2 a ha)
      exact (Subgroup.mem_centralizer_iff.1 this a ha)
  exact Subgroup.mem_centralizer_iff.1 hcen v hv

theorem conj_N0 : conjSubgroup (N0 S L t x) x = N0 S L t x := by
  set Uu : Subgroup G := blockU L ⊔ conjSubgroup (blockU L) t with hUu
  have hxx : conjSubgroup Uu (x * x) = Uu := P.D.conj_U_sup P.hxsq
  set Z : Subgroup G := Uu ⊔ conjSubgroup Uu x with hZ
  have e : conjSubgroup (baum S ⊓ centralizer (Z : Set G)) x =
      baum S ⊓ centralizer ((conjSubgroup Z x : Subgroup G) : Set G) := by
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self P.hxB, C5.conjSubgroup_centralizer]
  have hZx : conjSubgroup Z x = Z := by
    rw [hZ, C5.conjSubgroup_sup, conjSubgroup_conjSubgroup, hxx, sup_comm]
  show conjSubgroup (baum S ⊓ centralizer (Z : Set G)) x = baum S ⊓ centralizer (Z : Set G)
  rw [e, hZx]

theorem N0_le : N0 S L t x ≤ baumD S L ⊔ (W ⊔ conjSubgroup W t) := by
  intro b hb
  have hZ : ∀ v ∈ blockU L ⊔ conjSubgroup (blockU L) t ⊔
      conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x, v * b = b * v := fun v hv =>
    Subgroup.mem_centralizer_iff.1 hb.2 v hv
  have hXU : conjSubgroup (blockU L) x ≤
      conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := conjSubgroup_mono le_sup_left x
  have hYU : conjSubgroup (conjSubgroup (blockU L) t) x ≤
      conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x := conjSubgroup_mono le_sup_right x
  refine P.B_decomp_N0 hb.1
    (fun v hv => hZ v (Subgroup.mem_sup_left (Subgroup.mem_sup_left hv)))
    (fun v hv => hZ v (Subgroup.mem_sup_left (Subgroup.mem_sup_right hv)))
    (fun v hv => hZ v (Subgroup.mem_sup_right (hXU hv)))
    (fun v hv => hZ v (Subgroup.mem_sup_right (hYU hv)))

theorem sqSub_N0 : sqSub (N0 S L t x) = sqSub (baumD S L) := by
  apply le_antisymm
  · have hE : ElemAb2 (W ⊔ conjSubgroup W t) := by
      refine (P.elemAb_U).mono ?_
      exact sup_le (P.loc.rk.W_le_U.trans le_sup_left)
        (conjSubgroup_mono P.loc.rk.W_le_U t |>.trans le_sup_right)
    have hc : ∀ u ∈ W ⊔ conjSubgroup W t, ∀ a ∈ baumD S L, u * a = a * u := by
      intro u hu a ha
      obtain ⟨-, haL, haL₂⟩ := P.D.mem_baumD_iff.1 ha
      have hu' : u ∈ blockU L ⊔ conjSubgroup (blockU L) t :=
        (sup_le (P.loc.rk.W_le_U.trans le_sup_left)
          (conjSubgroup_mono P.loc.rk.W_le_U t |>.trans le_sup_right)) hu
      have := C56.mem_centralizer_sup (A := blockU L) (B := conjSubgroup (blockU L) t) (u := a)
        (fun v hv => haL v (P.U₁_le_L hv)) (fun v hv => haL₂ v (P.U₂_le_L₂ hv))
      exact Subgroup.mem_centralizer_iff.1 this u hu'
    calc sqSub (N0 S L t x) ≤ sqSub (baumD S L ⊔ (W ⊔ conjSubgroup W t)) := sqSub_mono P.N0_le
      _ = sqSub ((W ⊔ conjSubgroup W t) ⊔ baumD S L) := by rw [sup_comm]
      _ = sqSub (baumD S L) := sqSub_sup_eq hE.2 hc
  · exact sqSub_mono P.D_le_N0

theorem sqSub_D_eq_bot : sqSub (baumD S L) = ⊥ := by
  have hinv : conjSubgroup (sqSub (baumD S L)) x = sqSub (baumD S L) := by
    rw [← P.sqSub_N0, C5.conjSubgroup_sqSub, P.conj_N0]
  have hC := C56.noCommonNormal P.D.hcs P.hSM P.hMT P.hne
  refine C5.eq_bot_of_noCommonNormal (K := conjJoin S L) (x := x) hC ?_ ?_ ?_ ?_ ?_ ?_
  · exact sqSub_le_self.trans (baumD_le_S S L)
  · exact fun d hd => (sqSub_le_self hd).2
  · intro g hg
    exact conjSubgroup_eq_iff_mem_normalizer.mp
      (C5.conjSubgroup_sqSub_of_mem_normalizer (S_le_normalizer_baumD S L hg))
  · exact conjSubgroup_eq_iff_mem_normalizer.mp hinv
  · exact P.D.hcs.eq_join.le
  · exact le_sup_zpowers_of_relIndex_two P.h2 P.hx P.hxS

theorem D_elemAb : ElemAb2 (baumD S L) := by
  have := sqSub_eq_bot_iff.1 P.sqSub_D_eq_bot
  exact ⟨comm_of_sq_eq_one this, this⟩

theorem D_inf_conj : baumD S L ⊓ conjSubgroup (baumD S L) x = ⊥ := by
  have hC := C56.noCommonNormal P.D.hcs P.hSM P.hMT P.hne
  have hxxD : x * x ∈ normalizer ((baumD S L : Subgroup G) : Set G) := S_le_normalizer_baumD S L P.hxsq
  refine C5.eq_bot_of_noCommonNormal (K := conjJoin S L) (x := x) hC ?_ ?_ ?_ ?_ ?_ ?_
  · exact inf_le_left.trans (baumD_le_S S L)
  · exact fun d hd => hd.1.2
  · intro g hg
    refine C5.mem_normalizer_inf (S_le_normalizer_baumD S L hg) ?_
    rw [← C5.conjSubgroup_normalizer, mem_conjSubgroup_iff]
    exact S_le_normalizer_baumD S L ((Subgroup.mem_normalizer_iff.1 P.hxN g).1 hg)
  · rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_inf, conjSubgroup_conjSubgroup,
      C5.conjSubgroup_eq_self hxxD, inf_comm]
  · exact P.D.hcs.eq_join.le
  · exact le_sup_zpowers_of_relIndex_two P.h2 P.hx P.hxS


end Setup

end CFSG.QuasithinUnique.AppE
