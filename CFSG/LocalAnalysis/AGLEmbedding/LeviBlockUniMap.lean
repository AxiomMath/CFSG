module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniCuts
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {t s ε : ℕ}

structure IsTopCut (I : Finset ℕ) (t : ℕ) : Prop where
  mem : t ∈ I
  le : ∀ i ∈ I, 1 ≤ i ∧ i ≤ t

@[expose, reducible] def uniBlockGroup (K : Type) [Field K] (s ε : ℕ) (I : Finset ℕ) :
    Option ↥I → Type
  | none => GL (HypIndex s ε) K
  | some b => GL (Fin (b.1 - predCut I b.1)) K

noncomputable instance uniBlockGroup.instGroup {I : Finset ℕ} :
    (j : Option ↥I) → Group (uniBlockGroup K s ε I j)
  | none => inferInstanceAs (Group (GL (HypIndex s ε) K))
  | some b => inferInstanceAs (Group (GL (Fin (b.1 - predCut I b.1)) K))

instance uniBlockGroup.instFinite [Finite K] {I : Finset ℕ} :
    (j : Option ↥I) → Finite (uniBlockGroup K s ε I j)
  | none => inferInstanceAs (Finite (GL (HypIndex s ε) K))
  | some b => inferInstanceAs (Finite (GL (Fin (b.1 - predCut I b.1)) K))

@[expose] noncomputable def uniLeviHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) :
    ↥(flagStabilizer h (t + s) ε ↑I) →* ((j : Option ↥I) → uniBlockGroup K s ε I j) :=
  MonoidHom.pi fun j => match j with
    | none => resBlockHom h hε (Finset.mem_coe.mpr hI.mem)
    | some b => eBlockHom h hε b.2 (hI.le b.1 b.2).1
        ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s))

theorem uniLeviHom_none (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (g : ↥(flagStabilizer h (t + s) ε ↑I)) :
    uniLeviHom h hε hI g none = resBlockHom h hε (Finset.mem_coe.mpr hI.mem) g :=
  rfl

theorem uniLeviHom_some (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (g : ↥(flagStabilizer h (t + s) ε ↑I)) (b : ↥I) :
    uniLeviHom h hε hI g (some b) = eBlockHom h hε b.2 (hI.le b.1 b.2).1
      ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)) g :=
  rfl

theorem exists_block_of_lt {I : Finset ℕ} (hI : IsTopCut I t) {w : ℕ} (hw : w < t) :
    ∃ b ∈ I, predCut I b ≤ w ∧ w < b := by
  have hne : (I.filter (w < ·)).Nonempty := ⟨t, Finset.mem_filter.mpr ⟨hI.mem, hw⟩⟩
  have hbI := Finset.mem_filter.mp (Finset.min'_mem _ hne)
  refine ⟨(I.filter (w < ·)).min' hne, hbI.1, ?_, hbI.2⟩
  rw [predCut, Finset.sup_le_iff]
  intro c hc
  obtain ⟨hcI, hcb⟩ := Finset.mem_filter.mp hc
  by_contra hcw
  have := Finset.min'_le (I.filter (w < ·)) c
    (Finset.mem_filter.mpr ⟨hcI, by simp only [id] at hcw; omega⟩)
  omega

theorem apply_eq_zero_of_mem_ker (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) {g : ↥(flagStabilizer h (t + s) ε ↑I)}
    (hg : g ∈ (uniLeviHom h hε hI).ker) {c : ℕ} (hc : c ≤ t + s) {u w : HypIndex (t + s) ε}
    (hw : fullPos w < c) (hu : c ≤ fullPos u) :
    (((g : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) u w = 0 := by
  have hg1 : uniLeviHom h hε hI g = 1 := hg
  have huw : u ≠ w := fun he => by rw [he] at hu; omega
  by_cases hwt : fullPos w < t
  · obtain ⟨b, hbI, hab, hwb⟩ := exists_block_of_lt hI hwt
    have hb1 := (hI.le b hbI).1
    have hbr : b ≤ t + s := (hI.le b hbI).2.trans (Nat.le_add_right t s)
    by_cases hub : b ≤ fullPos u
    · exact isHypCut_flagStabilizer h hε (Finset.mem_coe.mpr hbI) hbr g g.2 u w hwb hub
    · obtain ⟨k, rfl⟩ := (mem_range_eIdx (a := predCut I b) hbr u).mpr ⟨by omega, by omega⟩
      obtain ⟨k', rfl⟩ := (mem_range_eIdx (a := predCut I b) hbr w).mpr ⟨hab, hwb⟩
      have e := congrArg (fun x : GL _ K => (x : Matrix _ _ K) k k')
        (congrFun hg1 (some ⟨b, hbI⟩))
      simp only [uniLeviHom_some, coe_eBlockHom, submatrix_apply] at e
      rw [e]
      exact one_apply_ne fun he => huw (by rw [he])
  · have hres := (mem_range_resIdx (s := s) (ε := ε) t w).mpr ⟨by omega, by omega⟩
    by_cases hun : 2 * (t + s) + ε - t ≤ fullPos u
    · exact isHypCut_flagStabilizer_orth h hε (Finset.mem_coe.mpr hI.mem)
        (Nat.le_add_right t s) g g.2 u w (by omega) hun
    · obtain ⟨x, rfl⟩ := (mem_range_resIdx (s := s) (ε := ε) t u).mpr ⟨by omega, by omega⟩
      obtain ⟨y, rfl⟩ := hres
      have e := congrArg (fun z : GL _ K => (z : Matrix _ _ K) x y) (congrFun hg1 none)
      simp only [uniLeviHom_none, coe_resBlockHom, submatrix_apply] at e
      rw [e]
      exact one_apply_ne fun he => huw (by rw [he])

theorem apply_self_eq_one_of_mem_ker (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) {g : ↥(flagStabilizer h (t + s) ε ↑I)}
    (hg : g ∈ (uniLeviHom h hε hI).ker) {u : HypIndex (t + s) ε}
    (hu : fullPos u < 2 * (t + s) + ε - t) :
    (((g : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) u u = 1 := by
  have hg1 : uniLeviHom h hε hI g = 1 := hg
  by_cases hut : fullPos u < t
  · obtain ⟨b, hbI, hab, hub⟩ := exists_block_of_lt hI hut
    have hbr : b ≤ t + s := (hI.le b hbI).2.trans (Nat.le_add_right t s)
    obtain ⟨k, rfl⟩ := (mem_range_eIdx (a := predCut I b) hbr u).mpr ⟨hab, hub⟩
    have e := congrArg (fun x : GL _ K => (x : Matrix _ _ K) k k)
      (congrFun hg1 (some ⟨b, hbI⟩))
    simp only [uniLeviHom_some, coe_eBlockHom, submatrix_apply] at e
    rw [e]
    exact one_apply_eq k
  · obtain ⟨x, rfl⟩ := (mem_range_resIdx (s := s) (ε := ε) t u).mpr ⟨by omega, hu⟩
    have e := congrArg (fun z : GL _ K => (z : Matrix _ _ K) x x) (congrFun hg1 none)
    simp only [uniLeviHom_none, coe_resBlockHom, submatrix_apply] at e
    rw [e]
    exact one_apply_eq x

theorem ker_uniLeviHom_le (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) :
    (uniLeviHom h hε hI).ker ≤
      (hypUnitriangular h (t + s) ε).comap (flagStabilizer h (t + s) ε ↑I).subtype := by
  intro g hg
  set G := (((g : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
    Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) with hG
  have hB : (g : hypSU h (t + s) ε) ∈ hypBorel h (t + s) ε := by
    rw [mem_hypBorel]
    intro c _ hc
    have hginv : g⁻¹ ∈ (uniLeviHom h hε hI).ker := Subgroup.inv_mem _ hg
    refine smul_hypFlag_eq_of_apply_eq_zero h hε hc
      (fun u w hw hu => apply_eq_zero_of_mem_ker h hε hI hg hc hw hu) fun u w hw hu => ?_
    have := apply_eq_zero_of_mem_ker h hε hI hginv hc hw hu
    rwa [Subgroup.coe_inv, Subgroup.coe_inv] at this
  have htri := blockTriangular_of_mem_hypBorel h hε hB
  refine ⟨htri, fun a => ?_⟩
  by_cases ha : fullPos a < 2 * (t + s) + ε - t
  · exact apply_self_eq_one_of_mem_ker h hε hI hg ha
  ·
    obtain ⟨i, rfl⟩ : ∃ i : Fin (t + s), a = .inr (.inr i) := by
      rcases a with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩
      · simp only [fullPos_inl] at ha
        omega
      · simp only [fullPos_inr_inl] at ha
        omega
      · exact ⟨⟨i, hi⟩, rfl⟩
    have hi : (i : ℕ) < t := by
      simp only [fullPos_inr_inr] at ha
      omega
    have hgram := congrFun (congrFun ((g : hypSU h (t + s) ε)).2.1 (.inl i)) (.inr (.inr i))
    rw [conjTranspose_hypGram_mul_apply, Finset.sum_eq_single (.inl i)] at hgram
    · rw [hypPartner_inl, hypGram_inl_inr_inr, ite_eq_left rfl,
        apply_self_eq_one_of_mem_ker h hε hI hg (u := .inl i) (by simp; omega), map_one,
        one_mul] at hgram
      exact hgram
    · intro x _ hx
      rcases lt_or_gt_of_ne (fun he => hx (fullPos_injective he)) with hlt | hlt
      · have : fullPos (.inr (.inr i) : HypIndex (t + s) ε) < fullPos (hypPartner x) := by
          rw [fullPos_hypPartner hε]
          have := fullPos_lt x
          simp only [fullPos_inl, fullPos_inr_inr] at hlt ⊢
          omega
        rw [htri this, mul_zero]
      · rw [htri hlt, map_zero, zero_mul]
    · simp

theorem isPGroup_ker_uniLeviHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) : IsPGroup p (uniLeviHom (s := s) h hε hI).ker := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hr : 1 ≤ t + s := (hI.le t hI.mem).1.trans (Nat.le_add_right t s)
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow h hr hε).2.1
  have hU : IsPGroup p (hypUnitriangular h (t + s) ε) := hP ▸ P.isPGroup'
  exact (hU.comap_subtype).to_le (ker_uniLeviHom_le h hε hI)

end CFSG.AGLEmbedding.LeviBlock
