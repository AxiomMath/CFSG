module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag4

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type*} [Field K]

theorem exists_linCut (n : ℕ) (I : Set ℕ) (a : Fin n) : ∃ c, (a : ℕ) < c ∧ (c = n ∨ c ∈ I) :=
  ⟨n, a.isLt, Or.inl rfl⟩

@[expose] noncomputable def linBlockLen (n : ℕ) (I : Set ℕ) (a : Fin n) : ℕ := by
  classical
  exact if (a : ℕ) = 0 ∨ (a : ℕ) ∈ I then Nat.find (exists_linCut n I a) - a else 0

variable {n : ℕ} {I : Set ℕ}

theorem linBlockLen_of_not_start {a : Fin n} (ha : ¬ ((a : ℕ) = 0 ∨ (a : ℕ) ∈ I)) :
    linBlockLen n I a = 0 := by
  classical
  simp only [linBlockLen, ha, ↓reduceIte]

theorem linBlockLen_spec {a : Fin n} (ha : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I) :
    (a : ℕ) + linBlockLen n I a ≤ n ∧ 1 ≤ linBlockLen n I a ∧
      ((a : ℕ) + linBlockLen n I a = n ∨ (a : ℕ) + linBlockLen n I a ∈ I) ∧
      ∀ c ∈ I, ¬ ((a : ℕ) < c ∧ c < (a : ℕ) + linBlockLen n I a) := by
  classical
  have hspec := Nat.find_spec (exists_linCut n I a)
  have hmin : ∀ c, (a : ℕ) < c → (c = n ∨ c ∈ I) → Nat.find (exists_linCut n I a) ≤ c :=
    fun c h1 h2 => Nat.find_min' _ ⟨h1, h2⟩
  have hn := hmin n a.isLt (Or.inl rfl)
  have hlen : linBlockLen n I a = Nat.find (exists_linCut n I a) - a := by
    simp only [linBlockLen, ha, ↓reduceIte]
  rw [hlen]
  refine ⟨by omega, by omega, ?_, fun c hc ⟨h1, h2⟩ => ?_⟩
  · rw [show (a : ℕ) + (Nat.find (exists_linCut n I a) - a) = Nat.find (exists_linCut n I a) by
      omega]
    exact hspec.2
  · have := hmin c h1 (Or.inr hc)
    omega

theorem linBlockLen_le (a : Fin n) : (a : ℕ) + linBlockLen n I a ≤ n := by
  by_cases ha : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I
  · exact (linBlockLen_spec ha).1
  · rw [linBlockLen_of_not_start ha]
    exact a.isLt.le

theorem linBlockLen_eq_of_maxBlock {a m : ℕ} (han : a < n) (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) (hm : 1 ≤ m) :
    m = linBlockLen n I ⟨a, han⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := linBlockLen_spec (I := I) (a := ⟨a, han⟩) ha
  simp only at h1 h2 h3 h4
  rcases maxBlock_eq_or_disjoint h h1 ha hb ha h3 hno h4 with ⟨-, e⟩ | e | e
  · exact e.symm
  · omega
  · omega

theorem linBlock_disjoint {a a' : Fin n} (hne : a ≠ a') {r : ℕ} (h1 : (a : ℕ) ≤ r)
    (h2 : r < a + linBlockLen n I a) (h3 : (a' : ℕ) ≤ r) (h4 : r < a' + linBlockLen n I a') :
    False := by
  by_cases ha : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I
  · by_cases ha' : (a' : ℕ) = 0 ∨ (a' : ℕ) ∈ I
    · obtain ⟨e1, -, e3, e4⟩ := linBlockLen_spec ha
      obtain ⟨f1, -, f3, f4⟩ := linBlockLen_spec ha'
      rcases maxBlock_eq_or_disjoint e1 f1 ha e3 ha' f3 e4 f4 with ⟨e, -⟩ | e | e
      · exact hne (Fin.ext e.symm)
      · omega
      · omega
    · rw [linBlockLen_of_not_start ha'] at h4
      omega
  · rw [linBlockLen_of_not_start ha] at h2
    omega

theorem blockLeft_linBlockLen (a : Fin n) :
    BlockLeft (flagStabilizer n K I) a (linBlockLen n I a) := by
  by_cases ha : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I
  · exact blockLeft_of_cut _ ha
  · intro g _ r l h1 h2 _
    rw [linBlockLen_of_not_start ha] at h2
    omega

theorem blockRight_linBlockLen (a : Fin n) :
    BlockRight (flagStabilizer n K I) a (linBlockLen n I a) := by
  by_cases ha : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I
  · exact blockRight_of_cut (linBlockLen_spec ha).2.2.1
  · intro g _ k c _ h2 h3
    rw [linBlockLen_of_not_start ha] at h3
    omega

variable (K n I) in
@[expose] noncomputable def linBlockHom (a : Fin n) :
    flagStabilizer n K I →* GL (Fin (linBlockLen n I a)) K :=
  (blkMon (flagStabilizer n K I) a (linBlockLen n I a) (linBlockLen_le a)
    (blockLeft_linBlockLen a) (blockRight_linBlockLen a)).toHomUnits

variable (K n I) in
@[expose] noncomputable def linLeviHom :
    flagStabilizer n K I →* ∀ a : Fin n, GL (Fin (linBlockLen n I a)) K :=
  MonoidHom.pi (linBlockHom K n I)

theorem coe_linLeviHom_apply (x : flagStabilizer n K I) (a : Fin n) :
    ((linLeviHom K n I x a : GL (Fin (linBlockLen n I a)) K) :
      Matrix (Fin (linBlockLen n I a)) (Fin (linBlockLen n I a)) K) =
      blkAt a (linBlockLen n I a) (linBlockLen_le a)
        ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem mem_unitriangular_of_linLeviHom {x : flagStabilizer n K I} (hx : linLeviHom K n I x = 1) :
    (x : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K := by
  refine mem_unitriangular_of_blocks x.2 fun a m h ha hb hno => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact blkAt_zero a h _
  · have han : a < n := by omega
    obtain rfl := linBlockLen_eq_of_maxBlock han h ha hb hno hm
    exact congrArg (fun y => Units.val (y ⟨a, han⟩)) hx

theorem isPGroup_ker_linLeviHom [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    IsPGroup 2 (linLeviHom K n I).ker := by
  let φ : (linLeviHom K n I).ker →* unitriangular n K :=
    ((flagStabilizer n K I).subtype.comp (linLeviHom K n I).ker.subtype).codRestrict _
      fun x => mem_unitriangular_of_linLeviHom x.2
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : unitriangular n K => (z : SpecialLinearGroup (Fin n) K)) hxy
  exact IsPGroup.of_injective (isPGroup_unitriangular_charTwo hn) φ hinj

variable (K n I) in
noncomputable abbrev linBlockSL (a : Fin n) : Subgroup (GL (Fin (linBlockLen n I a)) K) :=
  (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (linBlockLen n I a)) K →* _).range

theorem transvection_blk_mem_flagStabilizer {a m : ℕ} (h : a + m ≤ n)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {i j : Fin m} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection (blkIdxN_ne (h := h) hij) c ∈ flagStabilizer n K I := by
  refine mem_flagStabilizer_of_entries fun k l d hd hl hk => ?_
  rw [SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have hkl : k ≠ l := fun e => by subst e; omega
  have hne : ¬ (blkIdxN a m h i = k ∧ blkIdxN a m h j = l) := by
    rintro ⟨e1, e2⟩
    have h1 : (i : ℕ) < m := i.isLt
    have h2 := congrArg Fin.val e1
    have h3 := congrArg Fin.val e2
    simp only [blkIdxN] at h2 h3
    exact hno d hd ⟨by omega, by omega⟩
  simp [hkl, hne]

theorem blkAt_transvection_self {a m : ℕ} (h : a + m ≤ n) {i j : Fin m} (hij : i ≠ j) (c : K) :
    blkAt a m h ((SpecialLinearGroup.transvection (blkIdxN_ne (h := h) hij) c :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K) := by
  ext i' j'
  rw [blkAt_apply, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, blkIdxN,
    Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]

theorem blkAt_transvection_other {a m a' m' : ℕ} (h : a + m ≤ n) (h' : a' + m' ≤ n)
    (hd : ∀ r : ℕ, a ≤ r → r < a + m → a' ≤ r → r < a' + m' → False) {i j : Fin m}
    (hij : i ≠ j) (c : K) :
    blkAt a' m' h' ((SpecialLinearGroup.transvection (blkIdxN_ne (h := h) hij) c :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i' j'
  rw [blkAt_apply, SpecialLinearGroup.transvection_coe]
  have hne : ¬ (blkIdxN a m h i = ⟨a' + i', by omega⟩ ∧ blkIdxN a m h j = ⟨a' + j', by omega⟩) := by
    rintro ⟨e1, -⟩
    have h2 := congrArg Fin.val e1
    simp only [blkIdxN] at h2
    exact hd (a + i) (by omega) (by omega) (by omega) (by omega)
  simp only [Matrix.add_apply, Matrix.single_apply, hne, ↓reduceIte, add_zero, Matrix.one_apply,
    Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]

theorem pi_le_range_linLeviHom :
    Subgroup.pi Set.univ (linBlockSL K n I) ≤ (linLeviHom K n I).range := by
  classical
  rw [Subgroup.pi_le_iff]
  intro a
  rw [linBlockSL, MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
    Subgroup.map_map, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, hij, c, rfl⟩, rfl⟩
  have hstart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I := by
    by_contra ha
    have hi : (i : ℕ) < linBlockLen n I a := i.isLt
    have := linBlockLen_of_not_start ha
    omega
  have hno := (linBlockLen_spec hstart).2.2.2
  refine ⟨⟨_, transvection_blk_mem_flagStabilizer (linBlockLen_le a) hno hij c⟩, ?_⟩
  funext a'
  apply Units.ext
  rw [coe_linLeviHom_apply]
  by_cases ha' : a' = a
  · subst ha'
    simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact blkAt_transvection_self _ hij c
  · simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne ha',
      Units.val_one]
    exact blkAt_transvection_other _ _ (fun r h1 h2 h3 h4 =>
      linBlock_disjoint (Ne.symm ha') h1 h2 h3 h4) hij c

theorem commutator_range_linLeviHom_le :
    ⁅(linLeviHom K n I).range, (linLeviHom K n I).range⁆ ≤
      Subgroup.pi Set.univ (linBlockSL K n I) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rintro _ ⟨x, hx, rfl⟩
  refine (Subgroup.mem_pi _).mpr fun a _ => ?_
  rw [linBlockSL, SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  have hc : x ∈ commutator (flagStabilizer n K I) := by rwa [commutator_def]
  exact Abelianization.commutator_subset_ker
    (GeneralLinearGroup.det.comp (linBlockHom K n I a)) hc

end CFSG.AGLEmbedding.LeviBlock
