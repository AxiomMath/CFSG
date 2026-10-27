module

public import CFSG.GH74.GLS.C3.Layer2.L5C8
public import CFSG.GH74.GLS.C3.Layer2.L5A3
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C10Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C10Inputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5052
public import Certificates.Certificate5070

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

@[expose] def IsLinG (m : Perm (Fin 16)) : Prop := ∀ i j, m (xor16 i j) = xor16 (m i) (m j)

structure C1Facts : Prop where
  gen : ∀ m : Perm (Fin 16), IsLinG m → QplG.image m ≠ QplG → QplG.image m ∩ QplG = {0} →
    QplG.image m ∩ PplG = {0} → ∀ F : Finset (Finset (Fin 16)), F.card ≤ 4 → QplG ∈ F →
      (∀ V ∈ F, V.image yHat ∈ F ∧ V.image wHat ∈ F ∧ V.image m ∈ F) →
        PplG.image m = PplG ∧
          ((F = fam0G ∧ ∀ A ∈ n24L, A ∈ Subgroup.closure ({yHat, wHat, m} : Set (Perm (Fin 16)))) ∨
           (F = fam1G ∧ ∀ A ∈ n24L,
              twG * A * twG⁻¹ ∈ Subgroup.closure ({yHat, wHat, m} : Set (Perm (Fin 16)))))
  presP : ∀ m : Perm (Fin 16), IsLinG m →
    ((∀ V ∈ fam0G, V.image m ∈ fam0G) ∨ (∀ V ∈ fam1G, V.image m ∈ fam1G)) → PplG.image m = PplG

section Planes

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

open Classical in
@[expose] noncomputable def Coord5.planeOf
    (V : Subgroup G) : Finset (Fin 16) :=
  Finset.univ.filter fun i => c.liftEl i ∈ V

variable {c}

theorem Coord5.mem_planeOf
    {V : Subgroup G} {i : Fin 16} :
    i ∈ c.planeOf V ↔ c.liftEl i ∈ V := by
  classical
  simp only [Coord5.planeOf, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Coord5.planeOf_inf
    {V W : Subgroup G} : c.planeOf (V ⊓ W) = c.planeOf V ∩ c.planeOf W := by
  ext i
  simp only [Coord5.mem_planeOf, Finset.mem_inter, Subgroup.mem_inf]

theorem Coord5.planeOf_bot :
    c.planeOf (⊥ : Subgroup G) = {0} := by
  ext i
  rw [Coord5.mem_planeOf, Subgroup.mem_bot, Finset.mem_singleton]
  constructor
  · intro hi
    exact Coord5.liftEl_inj c (hi.trans c.liftEl_zero.symm)
  · rintro rfl
    exact c.liftEl_zero

theorem Coord5.planeOf_inj
    {V W : Subgroup G} (hV : V ≤ c.lift Rm) (hW : W ≤ c.lift Rm)
    (hVW : c.planeOf V = c.planeOf W) : V = W := by
  apply le_antisymm
  · intro g hg
    have hgR := hV hg
    have hj : idx16 (c.rco g) ∈ c.planeOf V := by
      rw [Coord5.mem_planeOf, ← Coord5.exists_liftEl c hgR]; exact hg
    rw [hVW, Coord5.mem_planeOf, ← Coord5.exists_liftEl c hgR] at hj
    exact hj
  · intro g hg
    have hgR := hW hg
    have hj : idx16 (c.rco g) ∈ c.planeOf W := by
      rw [Coord5.mem_planeOf, ← Coord5.exists_liftEl c hgR]; exact hg
    rw [← hVW, Coord5.mem_planeOf, ← Coord5.exists_liftEl c hgR] at hj
    exact hj

theorem Coord5.planeOf_cj
    {n : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    {V : Subgroup G} (hV : V ≤ c.lift Rm) :
    c.planeOf (cj n V) = (c.planeOf V).image (c.rhoG ⟨n, hn⟩) := by
  ext i
  rw [Coord5.mem_planeOf, Finset.mem_image]
  constructor
  · intro hi
    obtain ⟨z, hz, hzi⟩ := mem_cj.1 hi
    have hzj := Coord5.exists_liftEl c (hV hz)
    refine ⟨idx16 (c.rco z), ?_, ?_⟩
    · rw [Coord5.mem_planeOf, ← hzj]; exact hz
    · apply Coord5.liftEl_inj c
      rw [Coord5.rhoG_spec, ← hzj]
      exact hzi
  · rintro ⟨j, hj, rfl⟩
    rw [Coord5.rhoG_spec]
    exact mem_cj_self ((Coord5.mem_planeOf).1 hj)

theorem el16_Qm_iff_chk : (List.finRange 16).all
    (fun i => decide (el16 i ∈ Qml ↔ i ∈ QplG)) = true :=
  Certificates.certificate5052.1

theorem el16_Pm_iff_chk : (List.finRange 16).all
    (fun i => decide (el16 i ∈ Pml ↔ i ∈ PplG)) = true :=
  Certificates.certificate5052.2

theorem el16_Qm_iff
    (i : Fin 16) : el16 i ∈ Qm ↔ i ∈ QplG := by
  have h := el16_Qm_iff_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem el16_Pm_iff
    (i : Fin 16) : el16 i ∈ Pm ↔ i ∈ PplG := by
  have h := el16_Pm_iff_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem Coord5.planeOf_Q :
    c.planeOf Q = QplG := by
  ext i
  rw [Coord5.mem_planeOf, SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) (c.liftEl i),
    Coord5.mem_lift_rco, c.rco_liftEl]
  constructor
  · rintro ⟨_, hi⟩
    exact (el16_Qm_iff i).1 hi
  · intro hi
    exact ⟨c.liftEl_mem_C i, (el16_Qm_iff i).2 hi⟩

theorem Coord5.planeOf_P :
    c.planeOf (T ⊓ K) = PplG := by
  ext i
  rw [Coord5.mem_planeOf, SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) (c.liftEl i),
    Coord5.mem_lift_rco, c.rco_liftEl]
  constructor
  · rintro ⟨_, hi⟩
    exact (el16_Pm_iff i).1 hi
  · intro hi
    exact ⟨c.liftEl_mem_C i, (el16_Pm_iff i).2 hi⟩

end Planes

section Family

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem Coord5.fam_planeOf_inj
    {V W : Subgroup G} (hV : V ∈ FamQ (c.lift Rm) Q)
    (hW : W ∈ FamQ (c.lift Rm) Q) (hVW : c.planeOf V = c.planeOf W) : V = W :=
  Coord5.planeOf_inj (fam_le_R (Q_le_R h c) hV) (fam_le_R (Q_le_R h c) hW) hVW

theorem exists_famFinset
    (c : Coord5 h) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ F : Finset (Finset (Fin 16)), F.card = 4 ∧
      ∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V := by
  classical
  have hfin : (FamQ (c.lift Rm) Q).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have himg : (c.planeOf '' FamQ (c.lift Rm) Q).Finite := hfin.image _
  refine ⟨himg.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ himg, Set.InjOn.ncard_image, hncard]
    intro V hV W hW hVW
    exact Coord5.fam_planeOf_inj hV hW hVW
  · intro V
    rw [Set.Finite.mem_toFinset, Set.mem_image]

theorem Coord5.fam_stable
    {F : Finset (Finset (Fin 16))}
    (hF : ∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V) {n : G}
    (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G)) :
    ∀ V ∈ F, V.image (c.rhoG ⟨n, hn⟩) ∈ F := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := (hF V).1 hV
  rw [← Coord5.planeOf_cj hn (fam_le_R (Q_le_R h c) hW)]
  exact (hF _).2 ⟨cj n W, fam_cj hn hW, rfl⟩

theorem exists_move
    (c : Coord5 h) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ n : G, n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) ∧ cj n Q ≠ Q := by
  by_contra hcon
  have hsub : FamQ (c.lift Rm) Q ⊆ {Q} := by
    rintro V ⟨g, hg, rfl⟩
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  have := Set.ncard_le_ncard hsub (Set.finite_singleton Q)
  rw [Set.ncard_singleton, hncard] at this
  omega

end Family

section Nbar

variable {h : IsAConfig 5 x K T Q S a}

theorem exists_nbar
    (hF : C1Facts) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    (hP : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ F : Finset (Finset (Fin 16)), F.card = 4 ∧ (F = fam0G ∨ F = fam1G) ∧
      (∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V) ∧
      (∀ n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)), PplG.image (c.rhoG n) = PplG) ∧
      (F = fam0G → ∀ A ∈ n24L,
        ∃ n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)), c.rhoG n = A) ∧
      (F = fam1G → ∀ A ∈ n24L,
        ∃ n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)), c.rhoG n = twG * A * twG⁻¹) := by
  obtain ⟨F, hFcard, hFmem⟩ := exists_famFinset c hncard
  obtain ⟨n, hn, hnQ⟩ := exists_move c hncard
  have hQR : Q ≤ c.lift Rm := Q_le_R h c
  have hQF : QplG ∈ F := by
    refine (hFmem _).2 ⟨Q, Q_mem_fam, ?_⟩
    exact Coord5.planeOf_Q
  obtain ⟨yG, hyT, hy⟩ := c.exists_T_rco yy5_mem
  have hyN : yG ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := Coord5.T_le_N c hyT
  have hρy : c.rhoG ⟨yG, hyN⟩ = yHat := Equiv.ext fun i => by
    rw [Coord5.rhoG_T c hyT, hy, actF_yy5]
  have hwN := w_mem_N h c
  have hρw : c.rhoG ⟨(c.wC : G), hwN⟩ = wHat := Equiv.ext fun i => Coord5.rhoG_wC c i
  set m := c.rhoG ⟨n, hn⟩ with hm
  have hlin : IsLinG m := fun i j => Coord5.rhoG_xor c ⟨n, hn⟩ i j
  have hcjF : cj n Q ∈ FamQ (c.lift Rm) Q := ⟨n, hn, rfl⟩
  have hcjR : cj n Q ≤ c.lift Rm := fam_le_R hQR hcjF
  have hplane : c.planeOf (cj n Q) = QplG.image m := by
    rw [Coord5.planeOf_cj hn hQR, Coord5.planeOf_Q]
  have hmQ : QplG.image m ≠ QplG := by
    intro heq
    apply hnQ
    apply Coord5.planeOf_inj hcjR hQR
    rw [hplane, heq, Coord5.planeOf_Q]
  have hTIQ : QplG.image m ∩ QplG = {0} := by
    have := fam_TI h c hG4 hcjF Q_mem_fam hnQ
    rw [← hplane, ← Coord5.planeOf_Q (c := c), ← Coord5.planeOf_inf, this, Coord5.planeOf_bot]
  have hTIP : QplG.image m ∩ PplG = {0} := by
    have := hP _ hcjF
    rw [← hplane, ← Coord5.planeOf_P (c := c), ← Coord5.planeOf_inf, this, Coord5.planeOf_bot]
  have hstab : ∀ V ∈ F, V.image yHat ∈ F ∧ V.image wHat ∈ F ∧ V.image m ∈ F := by
    intro V hV
    refine ⟨?_, ?_, Coord5.fam_stable hFmem hn V hV⟩
    · have := Coord5.fam_stable hFmem hyN V hV
      rwa [hρy] at this
    · have := Coord5.fam_stable hFmem hwN V hV
      rwa [hρw] at this
  obtain ⟨_, hdis⟩ := hF.gen m hlin hmQ hTIQ hTIP F hFcard.le hQF hstab
  have hFfam : F = fam0G ∨ F = fam1G := hdis.elim (fun h0 => Or.inl h0.1) (fun h1 => Or.inr h1.1)
  have hle : Subgroup.closure ({yHat, wHat, m} : Set (Perm (Fin 16))) ≤ (c.rhoG).range := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨⟨yG, hyN⟩, hρy⟩
    · exact ⟨⟨(c.wC : G), hwN⟩, hρw⟩
    · exact ⟨⟨n, hn⟩, rfl⟩
  refine ⟨F, hFcard, hFfam, hFmem, ?_, ?_, ?_⟩
  · intro n'
    have hlin' : IsLinG (c.rhoG n') := fun i j => Coord5.rhoG_xor c n' i j
    have hst := Coord5.fam_stable hFmem n'.2
    rcases hFfam with hf | hf
    · exact hF.presP _ hlin' (Or.inl (by rw [← hf]; exact hst))
    · exact hF.presP _ hlin' (Or.inr (by rw [← hf]; exact hst))
  · intro hf A hA
    rcases hdis with ⟨h0, hcl⟩ | ⟨h1, _⟩
    · obtain ⟨n', hn'⟩ := hle (hcl A hA)
      exact ⟨n', hn'⟩
    · exact absurd (h1.symm.trans hf) (by decide)
  · intro hf A hA
    rcases hdis with ⟨h0, _⟩ | ⟨h1, hcl⟩
    · exact absurd (h0.symm.trans hf) (by decide)
    · obtain ⟨n', hn'⟩ := hle (hcl A hA)
      exact ⟨n', hn'⟩

end Nbar

end CFSG.GH74.GLS.C3.Layer2.L5
