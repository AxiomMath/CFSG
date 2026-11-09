module

public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.RawCard

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] noncomputable def stepTabP (kS M : Nat) : Nat :=
  foldUp kS (fun l s => strictN (Nat.land s (nat_lit 255)) (fun c =>
      nIf(hasBit M l, Nat.add (Nat.succ s) (Nat.shiftLeft l (Nat.add (nat_lit 8) (Nat.mul (nat_lit 8) c))), s)))
    (nat_lit 0)

@[expose] noncomputable def stepsPos (w : Nat) (PS : Nat → Nat) (kS kO BP i : Nat) : Nat :=
  stepTabP kS (nIf(Nat.beq i (nat_lit 0), Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1),
    fixMaskK w (mask w) PS kS BP i))

@[expose] noncomputable def schPK (n w : Nat) (S SI LR TR TRI : Nat → Nat) (kS kO BP nb i h₀ cnt : Nat) :
    Bool :=
  schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP nb i (stepsPos w S kS kO BP i) h₀ cnt

end CFSG.KS.Raw

end

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem stepTabP_fold {M : Nat} : ∀ k, k < 256 →
    (List.range k).foldl (fun s l => strictN (Nat.land s (nat_lit 255)) (fun c =>
      nIf(hasBit M l, Nat.add (Nat.succ s) (Nat.shiftLeft l (Nat.add (nat_lit 8) (Nat.mul (nat_lit 8) c))), s)))
      0 = ((List.range k).filter (hasBit M)).length +
        256 * enc ((List.range k).filter (hasBit M)) := by
  intro k
  induction k with
  | zero => intro _; simp [enc]
  | succ k ih =>
    intro hk1
    rw [List.range_succ, List.foldl_append, ih (by omega), List.filter_append]
    set L := (List.range k).filter (hasBit M) with hL
    have hlen : L.length ≤ k := by
      rw [hL]
      exact (List.length_filter_le _ _).trans (by simp)
    simp only [List.foldl_cons, List.foldl_nil, List.filter_cons, List.filter_nil]
    rw [strictN_eq]
    have e1 : Nat.land (L.length + 256 * enc L) 255 = L.length := by
      change (L.length + 256 * enc L) &&& (2 ^ 8 - 1) = L.length
      rw [Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [e1, nIf_eq]
    cases htk : hasBit M k
    · simp
    · simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil, enc_append]
      have e2 : Nat.shiftLeft k (Nat.add 8 (Nat.mul 8 L.length)) =
          256 * (k * 256 ^ L.length) := by
        rw [shl_eq', Nat.add_eq, Nat.mul_eq, Nat.pow_add, Nat.pow_mul]
        ring
      rw [e2, Nat.add_eq, Nat.succ_eq_add_one]
      ring

theorem stepTabP_cnt {kS M : Nat} (hk : kS < 256) :
    stCnt (stepTabP kS M) = ((List.range kS).filter (hasBit M)).length := by
  have hlen : ((List.range kS).filter (hasBit M)).length < 256 :=
    lt_of_le_of_lt ((List.length_filter_le _ _).trans (by simp)) hk
  unfold stCnt stepTabP
  rw [foldUp_eq, stepTabP_fold _ hk]
  change (_ + 256 * _) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem stepTabP_at {kS M j : Nat} (hk : kS < 256)
    (hj : j < ((List.range kS).filter (hasBit M)).length) :
    stAt (stepTabP kS M) j = ((List.range kS).filter (hasBit M))[j] := by
  have hlen : ((List.range kS).filter (hasBit M)).length < 256 :=
    lt_of_le_of_lt ((List.length_filter_le _ _).trans (by simp)) hk
  have hlt : ∀ x ∈ (List.range kS).filter (hasBit M), x < 256 := fun x hx => by
    rw [List.mem_filter, List.mem_range] at hx
    omega
  unfold stAt stepTabP
  rw [foldUp_eq, stepTabP_fold _ hk]
  exact digit_eq hlt hlen hj

theorem posList_facts {w kS kO BP : Nat} {PS : Nat → Nat} (hkO : kO ≤ kS) (i : Nat) :
    let PL := (List.range kS).filter (hasBit (nIf(Nat.beq i (nat_lit 0),
      Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1), fixMaskK w (mask w) PS kS BP i)))
    PL <+: (List.range kS).filter (fxK w PS BP i) ∧
      (i = 0 → PL = List.range kO) ∧ (i ≠ 0 → PL = (List.range kS).filter (fxK w PS BP i)) := by
  intro PL
  by_cases hi : i = 0
  · subst hi
    have hM : nIf(Nat.beq 0 (nat_lit 0), Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1),
        fixMaskK w (mask w) PS kS BP 0) = 2 ^ kO - 1 := by
      rw [nIf_eq]
      simp [Nat.one_shiftLeft]
    have hP : PL = List.range kO := by
      change (List.range kS).filter (hasBit _) = _
      rw [hM]
      obtain ⟨d, rfl⟩ : ∃ d, kS = kO + d := ⟨kS - kO, by omega⟩
      rw [List.range_add, List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2,
        List.append_nil]
      · intro x hx
        rw [List.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        simp [hasBit_eq, Nat.testBit_two_pow_sub_one]
      · intro x hx
        rw [List.mem_range] at hx
        simp [hasBit_eq, Nat.testBit_two_pow_sub_one, hx]
    have hF : (List.range kS).filter (fxK w PS BP 0) = List.range kS :=
      List.filter_eq_self.2 fun _ _ => rfl
    refine ⟨?_, fun _ => hP, fun h => absurd rfl h⟩
    rw [hP, hF]
    obtain ⟨d, rfl⟩ : ∃ d, kS = kO + d := ⟨kS - kO, by omega⟩
    rw [List.range_add]
    exact List.prefix_append _ _
  · have hM : nIf(Nat.beq i (nat_lit 0), Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1),
        fixMaskK w (mask w) PS kS BP i) = fixMaskK w (mask w) PS kS BP i := by
      rw [nIf_eq]
      simp [Nat.beq_eq, hi]
    have hP : PL = (List.range kS).filter (fxK w PS BP i) := by
      change (List.range kS).filter (hasBit _) = _
      rw [hM]
      apply List.filter_congr
      intro l hl
      rw [List.mem_range] at hl
      rw [hasBit_eq, fixMask_testBit]
      simp [hl]
    exact ⟨hP ▸ List.prefix_refl _, fun h => absurd h hi, fun _ => hP⟩

def SchP (n m : Nat) (pts pos : Nat → Nat) (t : Nat → Equiv.Perm (Fin n))
    (L : Subgroup (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ h < m, ∀ hh : pts h < n, pos (g ⟨pts h, hh⟩) < m ∧ pts (pos (g ⟨pts h, hh⟩)) = g ⟨pts h, hh⟩ ∧
    (t (pos (g ⟨pts h, hh⟩)))⁻¹ * (g * t h) ∈ L

section SchP

variable {n m : Nat} {pts pos : Nat → Nat} {t : Nat → Equiv.Perm (Fin n)}
  {L : Subgroup (Equiv.Perm (Fin n))}

theorem schP_one (hpp : ∀ k < m, pos (pts k) = k) : SchP n m pts pos t L 1 := by
  intro h hh hn
  simp only [Equiv.Perm.one_apply, one_mul]
  refine ⟨by rw [hpp h hh]; exact hh, by rw [hpp h hh], ?_⟩
  rw [hpp h hh, inv_mul_cancel]
  exact L.one_mem

theorem schP_mul (hpl : ∀ k < m, pts k < n) {g g' : Equiv.Perm (Fin n)}
    (hg : SchP n m pts pos t L g) (hg' : SchP n m pts pos t L g') :
    SchP n m pts pos t L (g * g') := by
  intro h hh hn
  obtain ⟨h1, h2, h3⟩ := hg' h hh hn
  set k := pos (g' ⟨pts h, hn⟩)
  have e : g' ⟨pts h, hn⟩ = ⟨pts k, hpl k h1⟩ := Fin.ext h2.symm
  obtain ⟨h4, h5, h6⟩ := hg k h1 (hpl k h1)
  rw [Equiv.Perm.mul_apply, e]
  refine ⟨h4, h5, ?_⟩
  have e3 : g * g' * t h = g * t k * ((t k)⁻¹ * (g' * t h)) := by group
  rw [e3, ← mul_assoc]
  exact L.mul_mem h6 h3

theorem schP_pow (hpp : ∀ k < m, pos (pts k) = k) (hpl : ∀ k < m, pts k < n)
    {g : Equiv.Perm (Fin n)} (hg : SchP n m pts pos t L g) : ∀ k, SchP n m pts pos t L (g ^ k)
  | 0 => by rw [pow_zero]; exact schP_one hpp
  | k + 1 => by rw [pow_succ]; exact schP_mul hpl (schP_pow hpp hpl hg k) hg

theorem schP_closure (hpp : ∀ k < m, pos (pts k) = k) (hpl : ∀ k < m, pts k < n)
    {A : Set (Equiv.Perm (Fin n))} (hA : ∀ s ∈ A, SchP n m pts pos t L s) :
    ∀ g ∈ Subgroup.closure A, SchP n m pts pos t L g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hA x hx
  | one => exact schP_one hpp
  | mul x y _ _ hx hy => exact schP_mul hpl hx hy
  | inv x _ hx =>
    have h1 : x * x ^ (orderOf x - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [inv_eq_of_mul_eq_one_right h1]
    exact schP_pow hpp hpl hx _

theorem card_le_schP (hm : 0 < m) (hpp : ∀ k < m, pos (pts k) = k) (hpl : ∀ k < m, pts k < n)
    {A : Set (Equiv.Perm (Fin n))} (hA : ∀ s ∈ A, SchP n m pts pos t L s) :
    Nat.card (Subgroup.closure A) ≤ m * Nat.card L := by
  have hP := schP_closure hpp hpl hA
  let f : Subgroup.closure A → Fin m × L := fun g =>
    (⟨_, (hP g g.2 0 hm (hpl 0 hm)).1⟩, ⟨_, (hP g g.2 0 hm (hpl 0 hm)).2.2⟩)
  have hf : Function.Injective f := by
    intro a b e
    have e1 := congrArg (fun p => (p.1 : Nat)) e
    have e2 := congrArg (fun p => (p.2 : Equiv.Perm (Fin n))) e
    simp only [f] at e1 e2
    rw [e1] at e2
    exact Subtype.ext (mul_right_cancel (mul_left_cancel e2))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this

end SchP

def Kl (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i : Nat) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ x ∈ levelIdx S base i, permOfArr n S[x]! = g}

theorem Kl_anti {n : Nat} {S : Array (Array Nat)} {base : Array Nat} {i l : Nat} (hil : i ≤ l) :
    Kl n S base l ≤ Kl n S base i := by
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  unfold levelIdx at hx ⊢
  rw [List.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  unfold fixesFirst at hx ⊢
  rw [allLt_iff] at hx ⊢
  exact fun k hk => hx.2 k (by omega)

theorem rawSteps_get {n : Nat} {S : Array (Array Nat)} {base : Array Nat} {i j : Nat}
    (hj : j < (levelIdx S base i).length) :
    (rawSteps n S base i)[j]! = S[(levelIdx S base i)[j]]! := by
  have hs : j < (rawSteps n S base i).size := by simp [rawSteps, levelSteps]; omega
  rw [getElem!_pos _ j hs]
  simp only [rawSteps, levelSteps]
  rw [Array.getElem_append_left (by simpa using hj)]
  simp

section Chain

variable {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}
variable (hd : Hd n S base kO W)
include hd

theorem step_memKl {i j : Nat} (hj : j < (rawSteps n S base i).size) :
    ∃ σ, Rep n (rawSteps n S base i)[j]! σ ∧ σ ∈ Kl n S base i := by
  have hmem : (rawSteps n S base i)[j]! ∈ levelSteps S (rawInvs n S) base i := by
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  unfold levelSteps at hmem
  rw [Array.mem_append, List.mem_toArray, List.mem_toArray, List.mem_map, List.mem_map] at hmem
  have hfix : ∀ idx ∈ levelIdx S base i, idx < S.size ∧
      permOfArr n S[idx]! ∈ Kl n S base i := by
    intro idx hidx
    refine ⟨?_, Subgroup.subset_closure ⟨idx, hidx, rfl⟩⟩
    unfold levelIdx at hidx
    rw [List.mem_filter, List.mem_range] at hidx
    exact hidx.1
  rcases hmem with ⟨idx, hidx, e⟩ | ⟨idx, hidx, e⟩
  · obtain ⟨h1, h2⟩ := hfix idx hidx
    exact ⟨_, e ▸ rep_S hd h1, h2⟩
  · obtain ⟨h1, h2⟩ := hfix idx hidx
    exact ⟨_, e ▸ rep_Si hd h1, Subgroup.inv_mem _ h2⟩

theorem tr_memKl {i : Nat} (hi : i < base.size) : ∀ k < (lev n S base i).pts.size,
    trP n S base i k ∈ Kl n S base i := by
  have F := lev_facts hd hi
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have e : trP n S base i 0 = 1 := (eqA_iff (rep_tr hd hi hk) rep_idA).1 F.tr_zero
      rw [e]
      exact Subgroup.one_mem _
    · have hp := F.par_lt k hk hk0
      have hl := F.lab_lt k hk hk0
      obtain ⟨σ, hσ, hσm⟩ := step_memKl hd hl
      have e : trP n S base i k = σ * trP n S base i (lev n S base i).par[k]! :=
        (eqA_iff (rep_tr hd hi hk) (rep_compA hσ (rep_tr hd hi (by omega)))).1 (F.tr_step k hk hk0)
      rw [e]
      exact Subgroup.mul_mem _ hσm (ih _ hp (by omega))

theorem sift_memKl : ∀ d l, base.size - l = d →
    ∀ (g : Array Nat) (G : Equiv.Perm (Fin n)), Rep n g G →
      siftA n (rawLevels n S base) base l g = true → G ∈ Kl n S base l := by
  intro d
  induction d with
  | zero =>
    intro l hl g G hg h
    have hls : ¬ l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    rw [siftA, dite_eq_right hls] at h
    rw [eq_of_eqA hg rep_idA h]
    exact Subgroup.one_mem _
  | succ d ih =>
    intro l hl g G hg h
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    have hT := tr_memKl hd hlb _ hk
    have hm := Kl_anti (Nat.le_succ l) (ih (l + 1) (by omega) _ _
      (rep_compA (rep_trInv hd hlb hk) hg) h)
    simpa using (Kl n S base l).mul_mem hT hm

end Chain

section Body

variable {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
include hb hp

omit hp in
theorem levelIdx_eq (hbl : ∀ t < nb, base[t]! < n) {i : Nat} (hi : i ≤ nb) :
    levelIdx S base i = (List.range kS).filter (fxK w PS BP i) := by
  obtain ⟨_, _, _, hS, hSj, _, hbt⟩ := hb
  unfold levelIdx
  rw [hS]
  apply List.filter_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [Bool.eq_iff_iff, fixesFirst, allLt_iff, fxK, allN_iff]
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  have htn : t < nb := by omega
  have hbn : pg w (mask w) BP t < n := hbt t htn ▸ hbl t htn
  rw [strictB_eq, beq_iff_eq, hbt t htn, hSj j hj, unpack_get hbn, beq_dec, decide_eq_true_iff]

theorem body_of_schK (hk : kS < 128) (hsz : n < 16777216) {LR TR TRI : Nat → Nat}
    (hbl : ∀ t < nb, base[t]! < n)
    (hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹)
    {i NS CH T : Nat} (hi : i < nb) (hNS : n ≤ NS * CH)
    (hs : ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i T
      (s * CH) CH = true)
    {j : Nat} (hjT : j < stCnt T) (hTj : stAt T j = stAt (stepsAt n w PS kS BP i) j)
    (hj : j < (rawSteps n S base i).size) {h : Nat} (hh : h < (lev n S base i).pts.size) :
    (lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]! <
        (lev n S base i).pts.size ∧
      siftA n (rawLevels n S base) base (i + 1)
        (compA n (lev n S base i).trInv[(lev n S base i).pos[((rawSteps n S base i)[j]!)[
          (lev n S base i).pts[h]!]!]!]! (compA n (rawSteps n S base i)[j]! (lev n S base i).tr[h]!))
        = true := by
  obtain ⟨TK, A, hT⟩ := hag i hi
  obtain ⟨_, hpr, hlet, _⟩ := kernel_steps hb hp hk hbl hi.le
  have F := native_facts hb hp hi (hbl i hi)
  have hhc : h < rcnt (LR i) := by rw [A.cnt]; exact hh
  obtain ⟨hCH, hsk, e⟩ := slice_cover hNS (by have := F.le; omega : h < n)
  have hk2 := schK_spec (hs _ hsk) (h := h) (by rw [Nat.add_eq] at e; omega)
    (by have := Nat.mod_lt h hCH; rw [Nat.add_eq] at e; omega) hhc j hjT
  rw [hTj] at hk2
  have hph : (lev n S base i).pts[h]! < n := F.pts_lt h hh
  have hzs : pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j))
      (rpt w (mask w) (LR i) h) = ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! := by
    rw [A.pt h hh]
    exact (hpr j hj ⟨_, hph⟩).trans ((rep_stp hb hp hj).apply hph).symm
  rw [hzs] at hk2
  obtain ⟨hk3, hk4⟩ := hk2
  have hzn : ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! < n :=
    (rep_stp hb hp hj).lt hph
  have hK := (A.pos _ hzn).1 hk3
  have hKe := A.posE _ hzn hK
  refine ⟨hK, ?_⟩
  rw [hKe] at hk4
  exact siftA_of_siftK hb hsz hbl hag (nb - (i + 1)) (i + 1) (by omega) _ _ _
    (prep_pcomp (by omega) (hT _ (by rw [A.cnt]; exact hK)).2
      (prep_pcomp (by omega) (hlet j hj) (hT h hhc).1))
    (rep_compA (A.tr _ hK).2 (rep_compA (rep_stp hb hp hj) (A.tr h hh).1)) hk4

end Body

end CFSG.KS.Raw.Orb

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw.Orb

theorem rawChainPK_sound {n w kS kO nb BP NS CH chunks : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schPK n w PS PSI LR TR TRI kS kO BP nb i (s * CH) CH = true) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true := by
  obtain ⟨hk, hH⟩ := rawHeadOK_of hb hh
  have hd := hd_of_head hk hH
  obtain ⟨hp, hsz, hkS⟩ := head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hS : S.size = kS := hb.2.2.2.1
  have hkO : kO ≤ kS := hS ▸ hk
  have hk2 : kS + kS < 256 := by omega
  have hbl : ∀ t < nb, base[t]! < n := fun t ht => hd.base_lt t (by omega)
  have hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹ :=
    fun l hl' => ⟨_, agree_levelK hb hp hbl hl' (hl l hl')⟩
  have hpos : ∀ i < nb, ∀ j, j < ((List.range kS).filter (hasBit (nIf(Nat.beq i (nat_lit 0),
      Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1), fixMaskK w (mask w) PS kS BP i)))).length →
      j < stCnt (stepsPos w PS kS kO BP i) ∧
      stAt (stepsPos w PS kS kO BP i) j = stAt (stepsAt n w PS kS BP i) j ∧
      j < (rawSteps n S base i).size ∧ j < (levelIdx S base i).length ∧
      (levelIdx S base i)[j]! = ((List.range kS).filter (hasBit (nIf(Nat.beq i (nat_lit 0),
        Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1), fixMaskK w (mask w) PS kS BP i))))[j]! := by
    intro i hi j hj
    obtain ⟨hpre, -, -⟩ := posList_facts (w := w) (BP := BP) (PS := PS) hkO i
    have hsplit := tab_split (M := fixMaskK w (mask w) PS kS BP i) (f := fxK w PS BP i)
      fixMask_testBit
    have hlen := hpre.length_le
    have hjI : j < ((List.range kS).filter (fxK w PS BP i)).length := by omega
    have hjL : j < ((List.range (kS + kS)).filter (tabP kS (fixMaskK w (mask w) PS kS BP i))).length := by
      rw [hsplit]
      simp
      omega
    have hcnt := (kernel_steps hb hp hkS hbl hi.le).1
    have hlI := levelIdx_eq hb hbl hi.le
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold stepsPos
      rw [stepTabP_cnt (by omega)]
      exact hj
    · unfold stepsPos stepsAt
      rw [stepTabP_at (by omega) hj, stAt_eq hk2 hjL]
      simp only [hsplit]
      rw [List.getElem_append_left hjI, hpre.getElem hj]
    · rw [← hcnt]
      unfold stepsAt
      rw [stCnt_eq hk2]
      exact hjL
    · rw [hlI]
      exact hjI
    · rw [hlI, getElem!_pos _ j hjI, getElem!_pos _ j hj, hpre.getElem hj]
  have hlev : ∀ i < nb, ∀ A : Set (Equiv.Perm (Fin n)), (∀ s ∈ A, ∃ j,
      j < ((List.range kS).filter (hasBit (nIf(Nat.beq i (nat_lit 0),
        Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1), fixMaskK w (mask w) PS kS BP i)))).length ∧
        s = stp n S base i j) →
      Nat.card (Subgroup.closure A) ≤ (lev n S base i).pts.size * Nat.card (Kl n S base (i + 1)) := by
    intro i hi A hA
    have hi' : i < base.size := by omega
    have F := lev_facts hd hi'
    refine card_le_schP (pts := fun k => (lev n S base i).pts[k]!)
      (pos := fun z => (lev n S base i).pos[z]!) (t := trP n S base i) F.pos F.pos_pts F.pts_lt ?_
    intro s hsA
    obtain ⟨j, hj, rfl⟩ := hA s hsA
    obtain ⟨hjT, hTj, hjs, -, -⟩ := hpos i hi j hj
    intro h hhm hn
    have B := body_of_schK hb hp hkS hsz hbl hag hi hNS (T := stepsPos w PS kS kO BP i) (hs i hi)
      hjT hTj hjs hhm
    have hz : ((stp n S base i j ⟨(lev n S base i).pts[h]!, hn⟩ : Fin n) : Nat) =
        ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! :=
      ((rep_stp hb hp hjs).apply hn).symm
    dsimp only
    rw [hz]
    refine ⟨B.1, F.pts_pos _ ((rep_stp hb hp hjs).lt hn) B.1, ?_⟩
    exact sift_memKl hd _ (i + 1) rfl _ _ (rep_compA (rep_trInv hd hi' B.1)
      (rep_compA (rep_stp hb hp hjs) (rep_tr hd hi' hhm))) B.2
  have hKl : ∀ i, 1 ≤ i → i < nb → Nat.card (Kl n S base i) ≤
      (lev n S base i).pts.size * Nat.card (Kl n S base (i + 1)) := by
    intro i h1 hi
    apply hlev i hi
    rintro _ ⟨x, hx, rfl⟩
    have hPL := (posList_facts (w := w) (BP := BP) (PS := PS) hkO i).2.2 (by omega)
    rw [levelIdx_eq hb hbl hi.le, ← hPL] at hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨-, -, -, h4, h5⟩ := hpos i hi j hj
    refine ⟨j, hj, ?_⟩
    unfold stp
    rw [rawSteps_get h4, ← getElem!_pos (levelIdx S base i) j h4, h5, getElem!_pos _ j hj]
  have hG : 0 < nb → Nat.card (Gen n S kO) ≤
      (lev n S base 0).pts.size * Nat.card (Kl n S base 1) := by
    intro h0
    apply hlev 0 h0
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    have hPL := (posList_facts (w := w) (BP := BP) (PS := PS) hkO 0).2.1 rfl
    have hjL : j < ((List.range kS).filter (hasBit (nIf(Nat.beq 0 (nat_lit 0),
        Nat.sub (Nat.shiftLeft (nat_lit 1) kO) (nat_lit 1), fixMaskK w (mask w) PS kS BP 0)))).length := by
      rw [hPL]
      simpa using hj
    obtain ⟨-, -, -, h4, h5⟩ := hpos 0 h0 j hjL
    refine ⟨j, hjL, ?_⟩
    rw [hPL, getElem!_pos (List.range kO) j (by simpa using hj), List.getElem_range] at h5
    unfold stp
    rw [rawSteps_get h4, ← getElem!_pos (levelIdx S base 0) j h4, h5]
  have hlast : Nat.card (Kl n S base nb) = 1 := by
    have hbot : Kl n S base nb = ⊥ := by
      have hH' := hH
      unfold rawHeadOK at hH'
      simp only [Bool.and_eq_true] at hH'
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h6⟩, _⟩ := hH'
      rw [eq_bot_iff]
      apply (Subgroup.closure_le _).2
      rintro _ ⟨x, hx, rfl⟩
      unfold levelIdx at hx
      rw [List.mem_filter, List.mem_range, ← hbs] at hx
      have h7 := allLt_spec h6 hx.1
      simp only [hx.2, Bool.not_true, Bool.false_or] at h7
      exact Subgroup.mem_bot.2 (eq_of_eqA (rep_S hd hx.1) rep_idA h7)
    rw [hbot, Subgroup.card_bot]
  have hchain : ∀ d i, i + d = nb → 1 ≤ i →
      Nat.card (Kl n S base i) ≤ ∏ l ∈ Finset.Ico i nb, (lev n S base l).pts.size := by
    intro d
    induction d with
    | zero =>
      intro i hi _
      rw [show i = nb by omega, Finset.Ico_self, Finset.prod_empty, hlast]
    | succ d ih =>
      intro i hi h1
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
      exact (hKl i h1 (by omega)).trans
        (Nat.mul_le_mul_left _ (ih (i + 1) (by omega) (by omega)))
  refine rawChainK_of_card chunks hb hh hl ?_
  change Nat.card (Gen n S kO) ≤ _
  rw [prod_sizes, hbs]
  rcases Nat.eq_zero_or_pos nb with h0 | h0
  · subst h0
    have hle : Gen n S kO ≤ Kl n S base 0 := by
      apply (Subgroup.closure_le _).2
      rintro _ ⟨⟨j, hj⟩, rfl⟩
      refine Subgroup.subset_closure ⟨j, ?_, rfl⟩
      unfold levelIdx
      rw [List.mem_filter, List.mem_range]
      exact ⟨by omega, allLt_iff.2 fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    rw [Finset.prod_range_zero, ← hlast]
    exact Subgroup.card_le_of_le hle
  · calc Nat.card (Gen n S kO)
        ≤ (lev n S base 0).pts.size * Nat.card (Kl n S base 1) := hG h0
      _ ≤ (lev n S base 0).pts.size * ∏ l ∈ Finset.Ico 1 nb, (lev n S base l).pts.size :=
        Nat.mul_le_mul_left _ (hchain (nb - 1) 1 (by omega) le_rfl)
      _ = ∏ l ∈ Finset.range nb, (lev n S base l).pts.size := by
        rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot h0]

@[expose, reducible] def SchTestsK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat)
    (kS kO BP nb NS CH : Nat) : Prop :=
  (∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) ∨
    ∀ i < nb, ∀ s < NS, schPK n w PS PSI LR TR TRI kS kO BP nb i (s * CH) CH = true

theorem rawChainSK_sound {n w kS kO nb BP NS CH chunks : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : SchTestsK n w PS PSI LR TR TRI kS kO BP nb NS CH) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true :=
  hs.elim (rawChainK_sound hb hh hl hNS) (rawChainPK_sound hb hh hl hNS)

end CFSG.KS.Raw

end
