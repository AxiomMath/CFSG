module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp

public section

namespace CFSG.ClassicalInvolution.Balance

open Matrix CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat E pos1 pos2 eq_pos_of_E_ne_zero mat_elt
  mat_injective ne_succ' toStd_single_of_lt' toStd_single_of_not_lt' toStd_neg' elt_injective
  mat_equiv_diagonal)

section SignDiag

variable {n : ℕ} {F : Type} [Field F]

@[expose] def spSignDiag (F : Type) [Field F] (n : ℕ) : Set (StatedSp n F) :=
  {z | ∃ ε : Fin n → Fˣ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
    z = equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal ε)}

theorem diagonal_conj_elt (ε : Fin n → Fˣ) (r : RootSubgroupIndex n) (c : F) :
    equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal ε) * elt r c *
        (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal ε))⁻¹ =
      elt r (((RootSubgroupIndex.character r ε : Fˣ) : F) * c) := by
  simp only [elt]
  rw [← map_inv, ← map_mul, ← map_mul,
    TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv]
  rfl

end SignDiag

section Simple

variable {n : ℕ} {F : Type} [Field F]

@[expose] def simpleIdx (i : Fin n) : RootSubgroupIndex n × RootSubgroupIndex n :=
  if h : i.val + 1 < n then
    (.difference i ⟨i.val + 1, h⟩ (ne_succ' h), .difference ⟨i.val + 1, h⟩ i (ne_succ' h).symm)
  else (.positiveLong i, .negativeLong i)

theorem stdVec_simpleIdx_fst (i : Fin n) :
    stdVec (simpleIdx i).1 = toStd n (Pi.single i 1) := by
  unfold simpleIdx
  split_ifs with h
  · rw [toStd_single_of_lt' h]
    rfl
  · rw [toStd_single_of_not_lt' h]
    rfl

theorem stdVec_simpleIdx_snd (i : Fin n) :
    stdVec (simpleIdx i).2 = toStd n (-Pi.single i 1) := by
  unfold simpleIdx
  split_ifs with h
  · rw [toStd_neg', toStd_single_of_lt' h]
    exact (neg_sub _ _).symm
  · rw [toStd_neg', toStd_single_of_not_lt' h]
    rfl

theorem x_simple_fst (i : Fin n) (c : F) :
    Sp.x n F (Pi.single i 1) c = elt (simpleIdx i).1 c :=
  Sp.x_eq (stdVec_simpleIdx_fst i) c

theorem x_simple_snd (i : Fin n) (c : F) :
    Sp.x n F (-Pi.single i 1) c = elt (simpleIdx i).2 c :=
  Sp.x_eq (stdVec_simpleIdx_snd i) c

@[expose] def simpleChar (ε : Fin n → Fˣ) (i : Fin n) : Fˣ :=
  if h : i.val + 1 < n then ε i * (ε ⟨i.val + 1, h⟩)⁻¹ else ε i * ε i

theorem character_simpleIdx_fst (ε : Fin n → Fˣ) (i : Fin n) :
    RootSubgroupIndex.character (simpleIdx i).1 ε = simpleChar ε i := by
  unfold simpleIdx simpleChar
  split_ifs with h <;> simp

theorem character_simpleIdx_snd (ε : Fin n → Fˣ) (i : Fin n) :
    RootSubgroupIndex.character (simpleIdx i).2 ε = (simpleChar ε i)⁻¹ := by
  unfold simpleIdx simpleChar
  split_ifs with h <;> simp [mul_comm]

def PlanesIn (i : Fin n) (P : Set (Fin n ⊕ Fin n)) : Prop :=
  (Sum.inl i ∈ P ∧ Sum.inr i ∈ P) ∧ ∀ h : i.val + 1 < n,
    (Sum.inl (⟨i.val + 1, h⟩ : Fin n) ∈ P ∧ Sum.inr (⟨i.val + 1, h⟩ : Fin n) ∈ P)

theorem isSupp_mat_elt {P : Set (Fin n ⊕ Fin n)} (r : RootSubgroupIndex n)
    (h1 : (pos1 r).1 ∈ P ∧ (pos1 r).2 ∈ P) (h2 : (pos2 r).1 ∈ P ∧ (pos2 r).2 ∈ P) (c : F) :
    IsSupp P (mat n F (elt r c)) := by
  intro a b hab
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply]
  have hE : E F r a b = 0 := by
    by_contra h
    rcases eq_pos_of_E_ne_zero r a b h with h' | h'
    · apply hab
      rw [show a = (pos1 r).1 from congrArg Prod.fst h',
        show b = (pos1 r).2 from congrArg Prod.snd h']
      exact h1
    · apply hab
      rw [show a = (pos2 r).1 from congrArg Prod.fst h',
        show b = (pos2 r).2 from congrArg Prod.snd h']
      exact h2
  rw [hE, smul_zero, add_zero]

theorem isSupp_simple_fst {i : Fin n} {P : Set (Fin n ⊕ Fin n)} (hP : PlanesIn i P) (c : F) :
    IsSupp P (mat n F (elt (simpleIdx i).1 c)) := by
  unfold simpleIdx
  split_ifs with h
  · exact isSupp_mat_elt _ ⟨hP.1.1, (hP.2 h).1⟩ ⟨(hP.2 h).2, hP.1.2⟩ c
  · exact isSupp_mat_elt _ ⟨hP.1.1, hP.1.2⟩ ⟨hP.1.1, hP.1.2⟩ c

theorem isSupp_simple_snd {i : Fin n} {P : Set (Fin n ⊕ Fin n)} (hP : PlanesIn i P) (c : F) :
    IsSupp P (mat n F (elt (simpleIdx i).2 c)) := by
  unfold simpleIdx
  split_ifs with h
  · exact isSupp_mat_elt _ ⟨(hP.2 h).1, hP.1.1⟩ ⟨hP.1.2, (hP.2 h).2⟩ c
  · exact isSupp_mat_elt _ ⟨hP.1.2, hP.1.1⟩ ⟨hP.1.2, hP.1.1⟩ c

theorem rankOne_le_suppGroup {i : Fin n} {P : Set (Fin n ⊕ Fin n)} (hP : PlanesIn i P) :
    rankOne (Symplectic.rootDatum n F).rootGroup i ≤ suppGroup P := by
  refine sup_le ?_ ?_
  · intro y hy
    have hy' : y ∈ rootGroup n F (Pi.single i 1 : Fin n → ℤ) := hy
    obtain ⟨c, rfl⟩ := (SpExtras.mem_rootGroup_iff (F := F) (stdVec_simpleIdx_fst i)).1 hy'
    exact isSupp_simple_fst hP c
  · intro y hy
    have hy' : y ∈ rootGroup n F (-(Pi.single i 1 : Fin n → ℤ)) := hy
    obtain ⟨c, rfl⟩ := (SpExtras.mem_rootGroup_iff (F := F) (stdVec_simpleIdx_snd i)).1 hy'
    exact isSupp_simple_snd hP c

end Simple

section Components

variable {p f n : ℕ} [Fact p.Prime]

theorem conj_mem_complGroup' {K : Type} [Field K] {i c x : StatedSp n K} (hc : c * i = i * c)
    (hx : x ∈ complGroup i) : c * x * c⁻¹ ∈ complGroup i := by
  have hc' : c⁻¹ * i = i * c⁻¹ := (Commute.inv_left (show Commute c i from hc)).eq
  intro v hv
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mem_complGroup.1 hx _ (mulVec_mem_minusSpace hc' hv), Matrix.mulVec_mulVec, ← map_mul,
    mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem isComponentOf_longRootGroup_stdInv (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (S : Finset (Fin n)) (hS : 1 ≤ S.card) :
    IsComponentOf (longRootGroup (stdInv (GaloisField p f) S))
      (Subgroup.centralizer ({stdInv (GaloisField p f) S} :
        Set (StatedSp n (GaloisField p f)))) := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  set z := stdInv (GaloisField p f) S with hz
  have hzz : z * z = 1 := stdInv_mul_self S
  have hle : longRootGroup z ≤ Subgroup.centralizer ({z} : Set (StatedSp n (GaloisField p f))) :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroup h2 hzz hx)
  have hnorm : ((longRootGroup z).subgroupOf
      (Subgroup.centralizer ({z} : Set (StatedSp n (GaloisField p f))))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro x c hx hc
    exact conj_mem_longRootGroup (Subgroup.mem_centralizer_singleton_iff.mp hc) hx
  refine ⟨hle, isSubnormal_of_normal_subgroupOf hle hnorm, ?_⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_longRootGroup_sp h2 (S := S) (g := 1) (z := z) (by simp [hz])
  exact Components.quasisimple_of_equiv e.symm (open_isQuasisimple_statedSp hq hS)

theorem isComponentOf_complGroup_stdInv (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (S : Finset (Fin n)) (hS : 1 ≤ Sᶜ.card) :
    IsComponentOf (complGroup (stdInv (GaloisField p f) S))
      (Subgroup.centralizer ({stdInv (GaloisField p f) S} :
        Set (StatedSp n (GaloisField p f)))) := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  set z := stdInv (GaloisField p f) S with hz
  have hzz : z * z = 1 := stdInv_mul_self S
  have hle : complGroup z ≤ Subgroup.centralizer ({z} : Set (StatedSp n (GaloisField p f))) :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_complGroup h2 hzz hx)
  have hnorm : ((complGroup z).subgroupOf
      (Subgroup.centralizer ({z} : Set (StatedSp n (GaloisField p f))))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro x c hx hc
    exact conj_mem_complGroup' (Subgroup.mem_centralizer_singleton_iff.mp hc) hx
  refine ⟨hle, isSubnormal_of_normal_subgroupOf hle hnorm, ?_⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_complGroup_sp h2 (S := S) (g := 1) (z := z) (by simp [hz])
  exact Components.quasisimple_of_equiv e.symm (open_isQuasisimple_statedSp hq hS)

end Components

section Main

variable {p f n : ℕ} [Fact p.Prime]

open Classical in
theorem equivStatedSp_diagonal_eq_stdInv {F : Type} [Field F] (ε : Fin n → Fˣ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) :
    equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal ε) =
      stdInv F (Finset.univ.filter fun j => ε j = -1) := by
  apply mat_injective
  rw [mat_equiv_diagonal, mat_stdInv]
  congr 1
  funext a
  rcases a with j | j
  · by_cases hj : ε j = -1
    · have hS : j ∈ Finset.univ.filter fun j => ε j = -1 := by simp [hj]
      simp only [stdSign, Sum.elim_inl, hS, ite_true, hj, Units.val_neg, Units.val_one]
    · have h1 : ε j = 1 := (hε j).resolve_right hj
      have hS : j ∉ Finset.univ.filter fun j => ε j = -1 := by simp [hj]
      simp only [stdSign, Sum.elim_inl, hS, ite_false, h1, Units.val_one]
  · by_cases hj : ε j = -1
    · have hS : j ∈ Finset.univ.filter fun j => ε j = -1 := by simp [hj]
      simp only [stdSign, Sum.elim_inr, hS, ite_true, hj, inv_neg, inv_one, Units.val_neg,
        Units.val_one]
    · have h1 : ε j = 1 := (hε j).resolve_right hj
      have hS : j ∉ Finset.univ.filter fun j => ε j = -1 := by simp [hj]
      simp only [stdSign, Sum.elim_inr, hS, ite_false, h1, inv_one, Units.val_one]

theorem actsDiagonallyOnSimple_signDiag {F : Type} [Field F] (ε : Fin n → Fˣ) (i : Fin n) :
    ActsDiagonallyOnSimple (D := Symplectic.rootDatum n F) (Sp.x n F)
      (MonoidHom.id (StatedSp n F)) 1 i
      (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal ε)) (simpleChar ε i) := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one]
    show _ * Sp.x n F (Pi.single i 1) c * _ = Sp.x n F (Pi.single i 1) _
    rw [x_simple_fst, x_simple_fst, diagonal_conj_elt, character_simpleIdx_fst]
  · simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one]
    show _ * Sp.x n F (-Pi.single i 1) c * _ = Sp.x n F (-Pi.single i 1) _
    rw [x_simple_snd, x_simple_snd, diagonal_conj_elt, character_simpleIdx_snd]

theorem eq_simpleChar_of_actsDiagonallyOnSimple {F : Type} [Field F] (ε : Fin n → Fˣ)
    {i : Fin n} {b : Fˣ}
    (hb : ActsDiagonallyOnSimple (D := Symplectic.rootDatum n F) (Sp.x n F)
      (MonoidHom.id (StatedSp n F)) 1 i
      (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal ε)) b) : b = simpleChar ε i := by
  have h1 := hb.1 1
  have h2 := (actsDiagonallyOnSimple_signDiag (F := F) ε i).1 1
  simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h1 h2
  rw [h1] at h2
  have h3 : Sp.x n F (Pi.single i 1) (b : F) = Sp.x n F (Pi.single i 1) (simpleChar ε i : F) := h2
  rw [x_simple_fst, x_simple_fst] at h3
  exact Units.ext (by simpa using elt_injective _ h3)

theorem toralShortRootFact_sp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ToralShortRootFact (Symplectic.rootDatum n (GaloisField p f)) (Sp.x n (GaloisField p f))
      (spSignDiag (GaloisField p f) n) := by
  rintro z ⟨ε, hε, rfl⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  refine ⟨fun i => ⟨_, actsDiagonallyOnSimple_signDiag ε i⟩, fun i b hb hb1 => ?_⟩
  have hbc : simpleChar ε i = 1 := (eq_simpleChar_of_actsDiagonallyOnSimple ε hb).symm.trans hb1
  classical
  set S : Finset (Fin n) := Finset.univ.filter fun j => ε j = -1 with hS
  rw [equivStatedSp_diagonal_eq_stdInv ε hε]
  have hmemS : ∀ j, j ∈ S ↔ ε j = -1 := fun j => by simp [hS]
  have hsame : ∀ h : i.val + 1 < n, ε i = ε ⟨i.val + 1, h⟩ := by
    intro h
    have := hbc
    simp only [simpleChar, h, dite_true] at this
    exact mul_inv_eq_one.mp this
  rcases hε i with hi | hi
  ·
    have hnot : ∀ j, ε j = 1 → j ∉ S := fun j hj hjS => by
      have h1 : (1 : (GaloisField p f)ˣ) = -1 := hj.symm.trans ((hmemS j).1 hjS)
      have h3 := congrArg Units.val h1
      simp only [Units.val_one, Units.val_neg] at h3
      exact h2 (by linear_combination h3)
    refine ⟨complGroup (stdInv (GaloisField p f) S), ?_, ?_⟩
    · rw [complGroup_stdInv h2]
      refine rankOne_le_suppGroup ⟨⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
      · exact hnot i hi
      · exact hnot i hi
      · exact hnot _ (hsame h ▸ hi)
      · exact hnot _ (hsame h ▸ hi)
    · exact isComponentOf_complGroup_stdInv hp2 hq S
        (Finset.card_pos.2 ⟨i, Finset.mem_compl.2 (hnot i hi)⟩)
  ·
    have hin : ∀ j, ε j = -1 → j ∈ S := fun j hj => (hmemS j).2 hj
    refine ⟨longRootGroup (stdInv (GaloisField p f) S), ?_, ?_⟩
    · rw [longRootGroup_stdInv h2]
      refine rankOne_le_suppGroup ⟨⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
      · exact hin i hi
      · exact hin i hi
      · exact hin _ (hsame h ▸ hi)
      · exact hin _ (hsame h ▸ hi)
    · exact isComponentOf_longRootGroup_stdInv hp2 hq S (Finset.card_pos.2 ⟨i, hin i hi⟩)

end Main

end CFSG.ClassicalInvolution.Balance
