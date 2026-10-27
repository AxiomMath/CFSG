module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras

section Block

variable {F : Type*} [Field F] {σ : F ≃+* F} {r n : ℕ} {e : Fin r → Fin n}

@[expose] def IsBlkOn (e : Fin r → Fin n) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → M a b = (1 : Matrix (Fin n) (Fin n) F) a b

theorem IsBlkOn.of_isBlk {blk : Fin n → ℕ} (h : ∀ s, blk s ≠ 0 → s ∈ Set.range e)
    {M : Matrix (Fin n) (Fin n) F} (hM : IsBlk blk M) : IsBlkOn e M := by
  intro a b hab
  refine hM a b fun ⟨h1, h2⟩ => ?_
  rcases hab with ha | hb
  · exact ha (h a h2)
  · exact hb (h b (h1 ▸ h2))

theorem submatrix_mul_of_isBlkOn (he : Function.Injective e) {M N : Matrix (Fin n) (Fin n) F}
    (hM : IsBlkOn e M) : (M * N).submatrix e e = M.submatrix e e * N.submatrix e e := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  refine (Fintype.sum_of_injective e he _ _ (fun s hs => ?_) fun t => rfl).symm
  rw [hM _ _ (Or.inr hs), one_apply_ne (fun h => hs ⟨i, h⟩), zero_mul]

theorem det_submatrix_of_isBlkOn (he : Function.Injective e) {M : Matrix (Fin n) (Fin n) F}
    (hM : IsBlkOn e M) : (M.submatrix e e).det = M.det := by
  classical
  rw [M.twoBlockTriangular_det' (fun s => s ∈ Set.range e) fun a ha b hb => by
    rw [hM a b (Or.inr hb), one_apply_ne (show a ≠ b from fun h => hb (h ▸ ha))]]
  have h1 : M.toSquareBlockProp (fun s => s ∉ Set.range e) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    rw [toSquareBlockProp, Matrix.toBlock_apply, hM a b (Or.inl ha), one_apply, one_apply]
    simp only [Subtype.mk.injEq]
  rw [h1, det_one, mul_one]
  convert det_submatrix_equiv_self (Equiv.ofInjective e he)
    (M.toSquareBlockProp fun s => s ∈ Set.range e) using 2
  rfl

variable (σ) in
theorem conjTr_mul_antidiag_mul_apply (M : Matrix (Fin r) (Fin r) F) (a b : Fin r) :
    (conjTr σ M * (antidiag r : Matrix (Fin r) (Fin r) F) * M) a b =
      ∑ t, σ (M t a) * M (Fin.rev t) b := by
  simp only [mul_apply, conjTr, transpose_apply, map_apply, antidiag, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (Fin.rev t)]
  · simp
  · intro u _ hu
    simp [hu]
  · simp

theorem submatrix_isometry_of_isBlkOn (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) {M : Matrix (Fin n) (Fin n) F}
    (hM : IsBlkOn e M) (hiso : conjTr σ M * antidiag n * M = antidiag n) :
    conjTr σ (M.submatrix e e) * antidiag r * M.submatrix e e = antidiag r := by
  ext a b
  have h := congrFun (congrFun hiso (e a)) (e b)
  rw [conjTr_mul_antidiag_mul_apply] at h ⊢
  simp only [submatrix_apply, hrev]
  rw [Fintype.sum_of_injective e he _ (fun s => σ (M s (e a)) * M (Fin.rev s) (e b))
    (fun s hs => by rw [hM s (e a) (Or.inl hs), one_apply_ne (fun h => hs ⟨a, h.symm⟩),
      map_zero, zero_mul]) fun t => rfl, h]
  simp only [antidiag, of_apply, ← hrev, he.eq_iff]

theorem det_and_isometry_submatrix_of_isBlkOn (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) {g : SU σ n} (hg : IsBlkOn e (mat σ n g)) :
    ((mat σ n g).submatrix e e).det = 1 ∧
      conjTr σ ((mat σ n g).submatrix e e) * antidiag r * (mat σ n g).submatrix e e =
        antidiag r :=
  ⟨(det_submatrix_of_isBlkOn he hg).trans g.2.1, submatrix_isometry_of_isBlkOn he hrev hg g.2.2⟩

variable (σ) in
@[expose] noncomputable def unitaryBlockHom (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) (L : Subgroup (SU σ n))
    (hL : ∀ g ∈ L, IsBlkOn e (mat σ n g)) : L →* SU σ r where
  toFun g := ⟨⟨(mat σ n g).submatrix e e, (mat σ n (g : SU σ n)⁻¹).submatrix e e,
      by rw [← submatrix_mul_of_isBlkOn he (hL _ g.2), ← map_mul, mul_inv_cancel, map_one,
        submatrix_one _ he],
      by rw [← submatrix_mul_of_isBlkOn he (hL _ (L.inv_mem g.2)), ← map_mul, inv_mul_cancel,
        map_one, submatrix_one _ he]⟩,
    det_and_isometry_submatrix_of_isBlkOn he hrev (hL _ g.2)⟩
  map_one' := Subtype.ext (Units.ext (by
    change (mat σ n 1).submatrix e e = 1
    rw [map_one, submatrix_one _ he]))
  map_mul' g g' := Subtype.ext (Units.ext (by
    change (mat σ n (g * g' : SU σ n)).submatrix e e =
      (mat σ n g).submatrix e e * (mat σ n g').submatrix e e
    rw [map_mul, submatrix_mul_of_isBlkOn he (hL _ g.2)]))

section BlockHom

variable {he : Function.Injective e} {hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)}
  {L : Subgroup (SU σ n)} {hL : ∀ g ∈ L, IsBlkOn e (mat σ n g)}

theorem mat_unitaryBlockHom (g : L) :
    mat σ r (unitaryBlockHom σ he hrev L hL g) = (mat σ n g).submatrix e e :=
  rfl

theorem unitaryBlockHom_injective : Function.Injective (unitaryBlockHom σ he hrev L hL) := by
  intro g g' h
  have h' := congrArg (mat σ r) h
  rw [mat_unitaryBlockHom, mat_unitaryBlockHom] at h'
  refine Subtype.ext (mat_injective ?_)
  ext a b
  by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hab
    exact congrFun (congrFun h' i) j
  · rw [not_and_or] at hab
    rw [hL _ g.2 a b hab, hL _ g'.2 a b hab]

end BlockHom

theorem submatrix_single_of_injective (he : Function.Injective e) (i j : Fin r) (c : F) :
    (single (e i) (e j) c).submatrix e e = single i j c := by
  ext a b
  simp only [submatrix_apply, single_apply, he.eq_iff]

theorem submatrix_longRootMatrix (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) {i : Fin r} {j : Fin n} (hij : e i = j)
    (c : F) : (longRootMatrix j c).submatrix e e = longRootMatrix i c := by
  subst hij
  rw [longRootMatrix, longRootMatrix, ← hrev, submatrix_add, Pi.add_apply, Pi.add_apply,
    submatrix_one _ he, submatrix_single_of_injective he]

theorem submatrix_heisenbergMatrix (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) {i k : Fin r} {j l : Fin n} (hij : e i = j)
    (hkl : e k = l) (a b : F) :
    (heisenbergMatrix σ j l a b).submatrix e e = heisenbergMatrix σ i k a b := by
  subst hij hkl
  simp only [heisenbergMatrix, ← hrev, submatrix_add, submatrix_sub, Pi.add_apply,
    Pi.sub_apply, submatrix_one _ he, submatrix_single_of_injective he]

end Block

section Small

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem rootGroup_two_eq_range :
    rootGroup σ hσ 2 (Pi.single 0 1) = (longRootHom σ (i := (0 : Fin 2)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
      exfalso
      revert hij hi hj hji
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi0 : i = 0 := by
        revert hw
        fin_cases i <;> decide
      subst hi0
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

theorem rootGroup_two_neg_eq_range :
    rootGroup σ hσ 2 (-Pi.single 0 1) =
      (longRootHom σ (i := (1 : Fin 2)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
      exfalso
      revert hij hi hj hji
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi1 : i = 1 := by
        revert hw
        fin_cases i <;> decide
      subst hi1
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

theorem rootGroup_three_neg_eq_heisenbergSubgroup :
    rootGroup σ hσ 3 (-Pi.single 0 1) =
      heisenbergSubgroup σ hσ (i := 2) (k := 1) (by decide) (by decide) (by decide) := by
  refine le_antisymm ?_ (heisenberg_le hσ _ _ _ (by decide))
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    exfalso
    revert hij hi hj hji
    fin_cases i <;> fin_cases j <;> decide
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    exfalso
    revert hw
    fin_cases i <;> decide
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    have hi2 : i = 2 := by
      revert hw
      fin_cases i <;> decide
    have hk1 : k = 1 := by
      revert hk
      fin_cases k <;> decide
    subst hi2 hk1
    exact le_rfl

end Small

theorem rankOne_two_eq_top {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 2)
      (0 : Fin (2 / 2)) = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hD := isCTGroupDatum hF 2 le_rfl ζ hζ
  rw [eq_top_iff, ← hD.iSup_eq_top]
  refine iSup₂_le fun γ hγ => hD.le_rankOne 0 γ hγ fun k hk => absurd ?_ hk
  fin_cases k
  rfl

section Last

variable {F : Type*} {n : ℕ} {k : Fin (n / 2)}

@[expose] def toBlock3 (p q r : Fin n) (M : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin 3) (Fin 3) F :=
  !![M p p, M p q, M p r; M q p, M q q, M q r; M r p, M r q, M r r]

theorem toBlock_eq_submatrix (p q : Fin n) (M : Matrix (Fin n) (Fin n) F) :
    SUExtras.toBlock p q M = M.submatrix ![p, q] ![p, q] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toBlock3_eq_submatrix (p q r : Fin n) (M : Matrix (Fin n) (Fin n) F) :
    toBlock3 p q r M = M.submatrix ![p, q, r] ![p, q, r] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable (k) in
@[expose] def lastIdxEven : Fin 2 → Fin n := ![lowIdx k, Fin.rev (lowIdx k)]

theorem lastIdxEven_injective : Function.Injective (lastIdxEven (n := n) k) := by
  have hpp := lowIdx_ne_rev (n := n) k k
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h hpp
  · exact absurd h.symm hpp
  · rfl

theorem lastIdxEven_rev (i : Fin 2) :
    lastIdxEven (n := n) k (Fin.rev i) = Fin.rev (lastIdxEven k i) := by
  fin_cases i
  · rfl
  · exact (Fin.rev_rev _).symm

variable (k) in
@[expose] def lastIdxOdd (hn : ¬Even n) : Fin 3 → Fin n :=
  ![lowIdx k, midIdx n hn, Fin.rev (lowIdx k)]

theorem lastIdxOdd_injective (hk : ¬k.val + 1 < n / 2) (hn : ¬Even n) :
    Function.Injective (lastIdxOdd k hn) := by
  have hpp := lowIdx_ne_rev (n := n) k k
  obtain ⟨hpm, hp'm⟩ := last_odd_ne hk hn
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h hpm
  · exact absurd h hpp
  · exact absurd h.symm hpm
  · rfl
  · exact absurd h.symm hp'm
  · exact absurd h.symm hpp
  · exact absurd h hp'm
  · rfl

theorem lastIdxOdd_rev (hn : ¬Even n) (i : Fin 3) :
    lastIdxOdd k hn (Fin.rev i) = Fin.rev (lastIdxOdd k hn i) := by
  fin_cases i
  · rfl
  · exact (rev_midIdx hn).symm
  · exact (Fin.rev_rev _).symm

variable [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}

theorem isBlkOn_lastIdxEven (he : Even n) (hk : ¬k.val + 1 < n / 2) {g : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    IsBlkOn (lastIdxEven k) (mat σ n g) := by
  refine IsBlkOn.of_isBlk (fun s hs => ?_) (isBlk_last_of_mem hk hg)
  rcases (blkLast_eq_one_iff s).mp (blkLast_eq_one_of_ne_zero hs) with h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact absurd h (rev_ne_self_of_even he s)

theorem isBlkOn_lastIdxOdd (hn : ¬Even n) (hk : ¬k.val + 1 < n / 2) {g : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    IsBlkOn (lastIdxOdd k hn) (mat σ n g) := by
  refine IsBlkOn.of_isBlk (fun s hs => ?_) (isBlk_last_of_mem hk hg)
  rcases (blkLast_odd_iff hn s).mp (blkLast_eq_one_of_ne_zero hs) with h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

variable (σ hσ) in
@[expose] noncomputable def rankOneLastEvenHom (he : Even n) (hk : ¬k.val + 1 < n / 2) :
    CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k →* SU σ 2 :=
  unitaryBlockHom σ lastIdxEven_injective lastIdxEven_rev _ fun _ hg =>
    isBlkOn_lastIdxEven he hk hg

variable (σ hσ) in
@[expose] noncomputable def rankOneLastOddHom (hn : ¬Even n) (hk : ¬k.val + 1 < n / 2) :
    CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k →* SU σ 3 :=
  unitaryBlockHom σ (lastIdxOdd_injective hk hn) (lastIdxOdd_rev hn) _ fun _ hg =>
    isBlkOn_lastIdxOdd hn hk hg

variable {he : Even n} {hn : ¬Even n} {hk : ¬k.val + 1 < n / 2}

theorem mat_rankOneLastEvenHom (g : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    mat σ 2 (rankOneLastEvenHom σ hσ he hk g) =
      SUExtras.toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g) :=
  (toBlock_eq_submatrix _ _ _).symm

theorem mat_rankOneLastOddHom (g : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    mat σ 3 (rankOneLastOddHom σ hσ hn hk g) =
      toBlock3 (lowIdx k) (midIdx n hn) (Fin.rev (lowIdx k)) (mat σ n g) :=
  (toBlock3_eq_submatrix _ _ _ _).symm

theorem rankOneLastEvenHom_injective : Function.Injective (rankOneLastEvenHom σ hσ he hk) :=
  unitaryBlockHom_injective

theorem rankOneLastOddHom_injective : Function.Injective (rankOneLastOddHom σ hσ hn hk) :=
  unitaryBlockHom_injective

end Last

section Finite

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} {k : Fin (n / 2)}

theorem rankOneLastEvenHom_surjective (he : Even n) (hk : ¬k.val + 1 < n / 2) :
    Function.Surjective (rankOneLastEvenHom (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) he hk) := by
  have hσ := unitaryInvolution_involutive hF
  have hpp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hpp
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← rankOne_two_eq_top hF]
  refine sup_le ?_ ?_
  · rw [rootGroup_two_eq_range hσ]
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨longRootHom _ hpp c, Subgroup.mem_sup_left
      (longRootHom_mem hσ hpp (toStd_last_even hk he).symm c)⟩, mat_injective ?_⟩
    change (longRootMatrix (lowIdx k) (c.toAdd : F)).submatrix (lastIdxEven k) (lastIdxEven k) =
      longRootMatrix 0 (c.toAdd : F)
    exact submatrix_longRootMatrix (F := F) (i := 0) (j := lowIdx k) lastIdxEven_injective
      lastIdxEven_rev rfl _
  · rw [rootGroup_two_neg_eq_range hσ]
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨longRootHom _ hp' c, Subgroup.mem_sup_right
      (longRootHom_mem hσ hp' (toStd_neg_last_even hk he).symm c)⟩, mat_injective ?_⟩
    change (longRootMatrix (Fin.rev (lowIdx k)) (c.toAdd : F)).submatrix (lastIdxEven k)
      (lastIdxEven k) = longRootMatrix 1 (c.toAdd : F)
    exact submatrix_longRootMatrix (F := F) (i := 1) (j := Fin.rev (lowIdx k))
      lastIdxEven_injective lastIdxEven_rev rfl _

theorem rankOneLastOddHom_surjective (hn : ¬Even n) (hk : ¬k.val + 1 < n / 2) :
    Function.Surjective (rankOneLastOddHom (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) hn hk) := by
  have hσ := unitaryInvolution_involutive hF
  have hpp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hpp
  obtain ⟨hpm, hp'm⟩ := last_odd_ne hk hn
  have hmid := rev_midIdx hn
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← rankOne_three_eq_top hF]
  refine sup_le ?_ ?_
  · rw [rootGroup_three_eq_heisenbergSubgroup hσ]
    rintro x ⟨a, b, hab, hx⟩
    refine ⟨⟨heisRootElt hσ hpp hpm hmid a b hab, Subgroup.mem_sup_left
      (heisenberg_le hσ hpp hpm hmid (toStd_last_odd hk hn).symm
        (heisRootElt_mem hσ hpp hpm hmid a b hab))⟩, mat_injective ?_⟩
    change (heisenbergMatrix (unitaryInvolution F p f) (lowIdx k) (midIdx n hn) a b).submatrix
      (lastIdxOdd k hn) (lastIdxOdd k hn) = mat (unitaryInvolution F p f) 3 x
    rw [mat_apply, hx]
    exact submatrix_heisenbergMatrix (i := 0) (k := 1) (j := lowIdx k) (l := midIdx n hn)
      (lastIdxOdd_injective hk hn) (lastIdxOdd_rev hn) rfl rfl a b
  · rw [rootGroup_three_neg_eq_heisenbergSubgroup hσ]
    rintro x ⟨a, b, hab, hx⟩
    refine ⟨⟨heisRootElt hσ hp' hp'm hmid a b hab, Subgroup.mem_sup_right
      (heisenberg_le hσ hp' hp'm hmid (toStd_neg_last_odd hk hn).symm
        (heisRootElt_mem hσ hp' hp'm hmid a b hab))⟩, mat_injective ?_⟩
    change (heisenbergMatrix (unitaryInvolution F p f) (Fin.rev (lowIdx k)) (midIdx n hn) a
      b).submatrix (lastIdxOdd k hn) (lastIdxOdd k hn) = mat (unitaryInvolution F p f) 3 x
    rw [mat_apply, hx]
    exact submatrix_heisenbergMatrix (i := 2) (k := 1) (j := Fin.rev (lowIdx k))
      (l := midIdx n hn) (lastIdxOdd_injective hk hn) (lastIdxOdd_rev hn) rfl rfl a b

@[expose] noncomputable def rankOneLastEvenEquiv (he : Even n) (hk : ¬k.val + 1 < n / 2) :
    CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k ≃*
        SU (unitaryInvolution F p f) 2 :=
  MulEquiv.ofBijective (rankOneLastEvenHom _ _ he hk)
    ⟨rankOneLastEvenHom_injective, rankOneLastEvenHom_surjective hF he hk⟩

@[expose] noncomputable def rankOneLastOddEquiv (hn : ¬Even n) (hk : ¬k.val + 1 < n / 2) :
    CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k ≃*
        SU (unitaryInvolution F p f) 3 :=
  MulEquiv.ofBijective (rankOneLastOddHom _ _ hn hk)
    ⟨rankOneLastOddHom_injective, rankOneLastOddHom_surjective hF hn hk⟩

variable {hF}

theorem rankOneLastEvenEquiv_apply {he : Even n} {hk : ¬k.val + 1 < n / 2}
    (g : CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) :
    rankOneLastEvenEquiv hF he hk g = rankOneLastEvenHom _ _ he hk g :=
  rfl

theorem rankOneLastOddEquiv_apply {hn : ¬Even n} {hk : ¬k.val + 1 < n / 2}
    (g : CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) :
    rankOneLastOddEquiv hF hn hk g = rankOneLastOddHom _ _ hn hk g :=
  rfl

theorem mat_rankOneLastEvenEquiv {he : Even n} {hk : ¬k.val + 1 < n / 2}
    (g : CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) :
    mat (unitaryInvolution F p f) 2 (rankOneLastEvenEquiv hF he hk g) =
      SUExtras.toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat (unitaryInvolution F p f) n g) :=
  mat_rankOneLastEvenHom (he := he) (hk := hk) g

theorem mat_rankOneLastOddEquiv {hn : ¬Even n} {hk : ¬k.val + 1 < n / 2}
    (g : CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) :
    mat (unitaryInvolution F p f) 3 (rankOneLastOddEquiv hF hn hk g) =
      toBlock3 (lowIdx k) (midIdx n hn) (Fin.rev (lowIdx k)) (mat (unitaryInvolution F p f) n g) :=
  mat_rankOneLastOddHom (hk := hk) g

theorem coe_rankOneLastEvenEquiv {he : Even n} {hk : ¬k.val + 1 < n / 2}
    (g : CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) :
    ((rankOneLastEvenEquiv hF he hk g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      SUExtras.toBlock (lowIdx k) (Fin.rev (lowIdx k))
        (((g : SU (unitaryInvolution F p f) n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  mat_rankOneLastEvenHom (he := he) (hk := hk) g

theorem coe_rankOneLastOddEquiv {hn : ¬Even n} {hk : ¬k.val + 1 < n / 2}
    (g : CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) :
    ((rankOneLastOddEquiv hF hn hk g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      toBlock3 (lowIdx k) (midIdx n hn) (Fin.rev (lowIdx k))
        (((g : SU (unitaryInvolution F p f) n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  mat_rankOneLastOddHom (hk := hk) g

theorem toBlock_mat_rankOneLastEvenEquiv_symm {he : Even n} {hk : ¬k.val + 1 < n / 2}
    (A : SU (unitaryInvolution F p f) 2) :
    SUExtras.toBlock (lowIdx k) (Fin.rev (lowIdx k))
        (mat (unitaryInvolution F p f) n ((rankOneLastEvenEquiv hF he hk).symm A)) =
      mat (unitaryInvolution F p f) 2 A := by
  rw [← mat_rankOneLastEvenEquiv (hF := hF) (he := he) (hk := hk), MulEquiv.apply_symm_apply]

theorem toBlock3_mat_rankOneLastOddEquiv_symm {hn : ¬Even n} {hk : ¬k.val + 1 < n / 2}
    (A : SU (unitaryInvolution F p f) 3) :
    toBlock3 (lowIdx k) (midIdx n hn) (Fin.rev (lowIdx k))
        (mat (unitaryInvolution F p f) n ((rankOneLastOddEquiv hF hn hk).symm A)) =
      mat (unitaryInvolution F p f) 3 A := by
  rw [← mat_rankOneLastOddEquiv (hF := hF) (hn := hn) (hk := hk), MulEquiv.apply_symm_apply]

end Finite

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem nonempty_rankOne_last_even_mulEquiv (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}
    (he : Even n) (_hn : 2 ≤ n) {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) :
    Nonempty (↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) ≃*
        SU (unitaryInvolution F p f) 2) :=
  ⟨rankOneLastEvenEquiv hF he hk⟩

theorem nonempty_rankOne_last_odd_mulEquiv (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}
    (ho : ¬ Even n) (_hn : 3 ≤ n) {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) :
    Nonempty (↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) ≃*
        SU (unitaryInvolution F p f) 3) :=
  ⟨rankOneLastOddEquiv hF ho hk⟩

end Main

end CFSG.LieType.Steinberg
