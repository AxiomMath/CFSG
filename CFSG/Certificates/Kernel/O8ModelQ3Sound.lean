module

public import CFSG.Certificates.Kernel.O8ModelDefs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.F2WordSound

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.KC.Enum (pidn pg permOK pcomp)
open CFSG.Monster.B.Co2 PA

private theorem perm_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    CFSG.KC.Enum.allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

private theorem beq_one_rec (c : Bool) :
    Nat.beq 1 (Bool.rec (motive := fun _ => Nat) 0 1 c) = c := by
  cases c <;> rfl

private theorem size_foldl_set (t : Array ℕ) (l : List ℕ) (r : Array ℕ) :
    (List.foldl (fun b a => b.setIfInBounds t[a]! a) r l).size = r.size := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, ih, Array.size_setIfInBounds]

private theorem size_invCand (n : ℕ) (t : Array ℕ) : (invCand n t).size = n := by
  unfold invCand
  simp only [Array.set!_eq_setIfInBounds, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure, size_foldl_set,
    Array.size_replicate]

private theorem getD_ofFn {α : Type} {m : ℕ} (f : Fin m → α) (x : α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f).getD i x = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

private theorem rec_and (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem fget_orN {d m : ℕ} {f : ℕ → ℕ} (hf : ∀ i < m, f i < 2 ^ d) {j : ℕ}
    (hj : j < m) : fget (orN m fun i => Nat.shiftLeft (f i) (Nat.mul d i)) j d = f j := by
  have he : (orN m fun i => Nat.shiftLeft (f i) (Nat.mul d i)) = orN m fun i => f i <<< (d * i) :=
    rfl
  rw [he, fget_eq_pg, Orb.pg_eq, ← Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, F2W.testBit_orN_fields hf]
  by_cases ht : t < d
  · have hd : 0 < d := by omega
    have e1 : (d * j + t) / d = j := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt ht, Nat.add_zero]
    have e2 : (d * j + t) % d = t := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    have e3 : d * j + t < d * m := by
      have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at this
      omega
    simp [ht, e1, e2, e3]
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf j hj)
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private theorem bitN_testBit (x i : ℕ) : (bitN x i).testBit 0 = x.testBit i := by
  change (Nat.land (Nat.shiftRight x i) 1).testBit 0 = _
  change ((x >>> i) &&& 1).testBit 0 = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  simp

private theorem bitN_lt (x i : ℕ) : bitN x i < 2 ^ 1 := by
  change Nat.land (Nat.shiftRight x i) 1 < 2
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem imgMask_eq (n w O G : ℕ) :
    imgMask n w O G = orN n fun z => bitN O (pg w (mask w) G z) <<< (1 * z) := by
  unfold imgMask
  exact congrArg (orN n) (funext fun z => by rw [Nat.one_mul]; rfl)

private theorem imgMask_testBit {n w O G z : ℕ} :
    (imgMask n w O G).testBit z = (decide (z < n) && O.testBit (pg w (mask w) G z)) := by
  rw [imgMask_eq, F2W.testBit_orN_fields (fun i _ => bitN_lt _ _), Nat.one_mul, Nat.div_one,
    Nat.mod_one, bitN_testBit]

private theorem imgMask_lt (n w O G : ℕ) : imgMask n w O G < 2 ^ n := by
  rw [imgMask_eq]
  have := F2W.orN_fields_lt (d := 1) (n := n)
    (f := fun z => bitN O (pg w (mask w) G z)) (fun i _ => bitN_lt _ _)
  rwa [Nat.one_mul] at this

private theorem imgTab_get {n w O TI m j : ℕ} (hj : j < m) :
    fget (imgTab n w O TI m) j n = imgMask n w O (perAt n w TI j) :=
  fget_orN (f := fun i => imgMask n w O (perAt n w TI i)) (fun i _ => imgMask_lt _ _ _ _) hj

private theorem exists_bit_ne {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : a ≠ b) :
    ∃ z < n, a.testBit z ≠ b.testBit z := by
  by_contra hc
  push Not at hc
  apply h
  apply Nat.eq_of_testBit_eq
  intro z
  by_cases hz : z < n
  · exact hc z hz
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))]

private theorem stabB_eq {s : Array ℕ} {M : Array Bool} {S X : ℕ}
    (hs : ∀ z < 120, s[z]! = pg 9 (mask 9) S z) (hr : ∀ z < 120, pg 9 (mask 9) S z < 120)
    (hM : ∀ z < 120, M.getD z false = X.testBit z) : stabB s M = stabK 120 9 S X := by
  rw [Bool.eq_iff_iff, stabB, allLt_iff, stabK, ctAllN_iff]
  refine forall_congr' fun z => imp_congr_right fun hz => ?_
  rw [ctOrB_eq, ctNotB_eq, hs z hz, hM z hz, hM _ (hr z hz), F2W.bit_eq, F2W.bit_eq]

private theorem pg_land {P i : ℕ} (hi : i < 120) :
    pg 9 (mask 9) P i = pg 9 (mask 9) (Nat.land P (maskN 1080)) i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [PF.testBit_pgM, PF.testBit_pgM]
  by_cases hk : k < 9
  · have e : Nat.land P (maskN 1080) = P &&& (2 ^ 1080 - 1) := by
      rw [← F2W.maskN_eq]
      rfl
    have h1 : 9 * i + k < 1080 := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hk, h1]
  · simp [hk]

private theorem copy0_unpack (P : ℕ) :
    OmegaEight.copy0Arr (unpack 360 9 P) = unpack 120 9 (Nat.land P (maskN 1080)) := by
  apply arr_ext (by simp [OmegaEight.copy0Arr]) (unpack_size _ _ _)
  intro i hi
  rw [OmegaEight.copy0Arr, getElem!_ofFn_nat _ hi, Orb.unpack_get (by omega), Orb.unpack_get hi]
  exact pg_land hi

private theorem compA_unpack {n w P Q : ℕ} (h32 : n < 2 ^ 32) (hP : P >>> (n * w) = 0) :
    compA n (unpack n w P) (unpack n w Q) = unpack n w (pcomp n w (mask w) P Q) := by
  apply arr_ext (by simp [compA]) (unpack_size _ _ _)
  intro i hi
  rw [compA_get hi, Orb.unpack_get hi, unpack_get' hP, Orb.unpack_get hi, PF.pg_pcomp h32 hi]

private theorem compA_idA {n : ℕ} {x : Array ℕ} {g : Equiv.Perm (Fin n)} (hx : Rep n x g)
    (hs : x.size = n) : compA n (idA n) x = x :=
  arr_eq_of_rep (by simp [compA]) hs (by simpa using rep_compA rep_idA hx) hx

private theorem psiTArrG_pow {n : ℕ} {Q : ℕ → Array ℕ}
    (hQ : ∀ j < 6, ∃ g : Equiv.Perm (Fin n), Rep n (Q j) g ∧ (Q j).size = n) {j : ℕ}
    (hj : j < 6) : psiTArrG n Q (2 ^ j) = Q j := by
  obtain ⟨g, hg, hs⟩ := hQ j hj
  have hb : ∀ i, (2 ^ j).testBit i = decide (i = j) := fun i => by
    rw [Nat.testBit_two_pow]
    exact decide_eq_decide.2 eq_comm
  unfold psiTArrG
  simp only [hb]
  interval_cases j <;> simp [List.range_succ] <;> exact compA_idA hg hs

theorem q3_sound {uA T tg : ℕ → Array ℕ} {US PS OS U2 F : Array (Array ℕ)} {PB OB UB : Array ℕ}
    {fA fB : Array Bool} {g8 : Array ℕ} {uw qw : List (List ℤ)}
    {UA UP TG SP SIP LRP TRP TRIP SO SIO LRO TRO TRIO SU SIU LRU TRU TRIU : Nat → Nat}
    {kU kSP kOP nbP BPP kSO kOO nbO BPO kSU kOU nbU BPU FL FI m FA FB G8 G8I : Nat}
    {DP DO DU : List (List Int)}
    (huA : ∀ k < 6, uA k = unpack 120 9 (UA k))
    (hUS : US.size = kU ∧ ∀ s < kU, US[s]! = unpack 120 9 (UP s))
    (hP : LevelsK 120 9 SP SIP LRP TRP TRIP kSP kOP nbP BPP DP PS PB)
    (hO : LevelsK 360 9 SO SIO LRO TRO TRIO kSO kOO nbO BPO DO OS OB)
    (hU : LevelsK 120 9 SU SIU LRU TRU TRIU kSU kOU nbU BPU DU U2 UB)
    (hfA : ∀ z < 120, fA.getD z false = bit FA z) (hfB : ∀ z < 120, fB.getD z false = bit FB z)
    (hF : ListBind 120 9 F FL m) (h8 : g8 = unpack 360 9 G8) (h8c : Nat.shiftRight G8 3240 = 0)
    (hUP : allN kU (fun s => allN 120 fun z => Nat.blt (pg 9 (mask 9) (UP s) z) 120) = true)
    (hT : ∀ y < 64, T y = psiTArrG 360 (fun j => wordA 360 OS (rawInvs 360 OS) (qw.getD j [])) y)
    (hl : allN 6 (fun j => andB (lettersK kSO (uw.getD j [])) (lettersK kSO (qw.getD j []))) = true)
    (htg : ∀ j < 6, tg j = unpack 120 9 (TG j))
    (hsig : allN 6 (fun k => allN 120 fun z => Nat.blt (pg 9 (mask 9)
      (pc 360 9 (pc 360 9 (pc 360 9 G8 G8) (wordC 360 9 SO SIO (uw.getD k [])))
        (pc 360 9 G8I G8I)) z) 120) = true)
    (h : q3OK 120 9 UA UP kU ⟨LRP, TRIP, BPP, nbP⟩ FL FI m FA FB G8 G8I
      (fun k => wordC 360 9 SO SIO (uw.getD k [])) ⟨LRU, TRIU, BPU, nbU⟩
      (fun j => wordC 360 9 SO SIO (qw.getD j [])) TG = true) :
    q3CheckG uA US PS PB fA fB F g8 OS uw T U2 UB tg = true := by
  obtain ⟨hbP, hhP, hlP⟩ := hP
  obtain ⟨hbO, hhO, hlO⟩ := hO
  obtain ⟨hbU, hhU, hlU⟩ := hU
  have hpP := perm_head hhP
  have hpO := perm_head hhO
  have hpU := perm_head hhU
  have h32 : (120 : ℕ) < 2 ^ 32 := by decide
  have h32' : (360 : ℕ) < 2 ^ 32 := by decide
  have hn1 : (120 : ℕ) < 16777216 := by decide
  have hw1 : (120 : ℕ) + 1 < 2 ^ 9 := by decide
  obtain ⟨hFs, hFj⟩ := hF
  obtain ⟨hUSs, hUSj⟩ := hUS
  rw [ctAllN_iff] at hUP hl hsig
  have hbO' := hbO
  obtain ⟨-, hwO, -, hOS, hOSj, -, -⟩ := hbO'
  have hrep : ∀ h < kSO, Rep 360 (unpack 360 9 (SO h)) (permOfArr 360 (unpack 360 9 (SO h))) ∧
      Rep 360 (unpack 360 9 (SIO h)) (permOfArr 360 (unpack 360 9 (SO h)))⁻¹ := fun h hh =>
    rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 hpO h hh))
  have hS' : ∀ h < kSO, Rep 360 OS[h]! (permOfArr 360 (unpack 360 9 (SO h))) := fun h hh => by
    rw [hOSj h hh]
    exact (hrep h hh).1
  have hSi : ∀ h < kSO,
      Rep 360 (rawInvs 360 OS)[h]! (permOfArr 360 (unpack 360 9 (SO h)))⁻¹ := fun h hh => by
    rw [Orb.rawInvs_get (by omega)]
    exact rep_invCand (hS' h hh)
  have hW : ∀ wd : List ℤ, lettersK kSO wd = true → ∃ g : Equiv.Perm (Fin 360),
      Rep 360 (unpack 360 9 (wordC 360 9 SO SIO wd)) g ∧
      wordA 360 OS (rawInvs 360 OS) wd = unpack 360 9 (wordC 360 9 SO SIO wd) := by
    intro wd hwd
    obtain ⟨hPw, hlo⟩ := Orb.prep_wordK (gs := fun h => permOfArr 360 (unpack 360 9 (SO h)))
      (j := kSO) (by decide) hwO (fun h hh => Orb.prep_of_rep (hrep h hh).1)
      (fun h hh => Orb.prep_of_rep (hrep h hh).2) wd hwd
    exact ⟨_, Orb.rep_unpack hPw, arr_eq_of_rep (wordA_size' _ _ _ _) (unpack_size _ _ _)
      (rep_wordA (gs := fun h => permOfArr 360 (unpack 360 9 (SO h))) hS' hSi _ hlo)
      (Orb.rep_unpack hPw)⟩
  unfold q3OK at h
  simp only [ctAndB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩ := h
  rw [ctAllN_iff] at h1 h4 h6 h9 h10
  rw [F2W.strictN_eq, F2W.strictN_eq, beq_one_rec] at h5
  simp only [rec_and, ctAndB_eq, Bool.and_eq_true] at h5
  obtain ⟨h5a, h5b⟩ := h5
  rw [ctAllN_iff] at h5a h5b
  have hm : m = 315 := Nat.eq_of_beq_eq_true h2
  obtain ⟨hR2s, hR2Is, -⟩ := Orb.permOK_facts h7
  have hr2 := rep_permOfArr (Orb.isInvA_unpack h7)
  have hrho : compA 360 g8 g8 = unpack 360 9 (pc 360 9 G8 G8) := by
    rw [h8]
    exact compA_unpack h32' h8c
  have hrhoI : invCand 360 (compA 360 g8 g8) = unpack 360 9 (pc 360 9 G8I G8I) := by
    rw [hrho]
    exact arr_eq_of_rep (size_invCand _ _) (unpack_size _ _ _) (rep_invCand hr2.1) hr2.2
  have hsigE : ∀ X : ℕ, OmegaEight.copy0Arr (conjA 360 (compA 360 g8 g8) (unpack 360 9 X)) =
      unpack 120 9 (Nat.land (pc 360 9 (pc 360 9 (pc 360 9 G8 G8) X) (pc 360 9 G8I G8I))
        (maskN 1080)) := by
    intro X
    rw [conjA, hrhoI, hrho, compA_unpack h32' hR2s,
      compA_unpack h32' (PF.pcomp_shr _ _ h32' (by decide)), copy0_unpack]
    rfl
  have hFrep : ∀ j < m, ∃ g : Equiv.Perm (Fin 120), Rep 120 F[j]! g ∧
      Rep 120 (unpack 120 9 (perAt 120 9 FI j)) g⁻¹ := fun j hj => by
    have hr := rep_permOfArr (Orb.isInvA_unpack (Bool.and_eq_true _ _ ▸ h4 j hj).1)
    rw [hFj j hj]
    exact ⟨_, hr.1, hr.2⟩
  have hMA : ∀ (A : Array Bool) (X : ℕ), (∀ z < 120, A.getD z false = bit X z) → ∀ j < m,
      ∀ z < 120, ((F.map fun g => (Array.ofFn (n := 120) fun z =>
        A.getD (invCand 120 g)[z.val]! false : Array Bool))[j]!).getD z false =
        (fget (imgTab 120 9 X FI m) j 120).testBit z := by
    intro A X hA j hj z hz
    obtain ⟨g, hRg, hRi⟩ := hFrep j hj
    have hjF : j < F.size := by omega
    rw [getElem!_pos _ j (by simpa using hjF), Array.getElem_map, ← getElem!_pos F j hjF,
      getD_ofFn _ _ hz, imgTab_get hj, imgMask_testBit, decide_eq_true hz, Bool.true_and]
    have e : (invCand 120 F[j]!)[z]! = pg 9 (mask 9) (perAt 120 9 FI j) z := by
      rw [(rep_invCand hRg).apply hz, ← hRi.apply hz, Orb.unpack_get hz]
    have hlt : pg 9 (mask 9) (perAt 120 9 FI j) z < 120 := by
      rw [← e]
      exact (rep_invCand hRg).lt hz
    rw [e, hA _ hlt, F2W.bit_eq]
  have hUSrep : ∀ s < kU, ∀ z < 120, (US[s]!)[z]! = pg 9 (mask 9) (UP s) z := fun s hs z hz => by
    rw [hUSj s hs, Orb.unpack_get hz]
  have hUSr : ∀ s < kU, ∀ z < 120, pg 9 (mask 9) (UP s) z < 120 := fun s hs z hz =>
    Nat.blt_eq.mp (ctAllN_iff.1 (hUP s hs) z hz)
  have hfA' : ∀ z < 120, fA.getD z false = FA.testBit z := fun z hz => by rw [hfA z hz, F2W.bit_eq]
  have hfB' : ∀ z < 120, fB.getD z false = FB.testBit z := fun z hz => by rw [hfB z hz, F2W.bit_eq]
  unfold q3CheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [allLt_iff]
    intro k hk
    rw [huA k hk, Orb.unpack_get (by decide), Nat.eq_of_beq_eq_true (h1 k hk)]
    exact beq_self_eq_true _
  · rw [hFs, hm]
    exact beq_self_eq_true _
  · have hF0 := hFj 0 (by omega)
    rw [hF0, Nat.eq_of_beq_eq_true h3]
    exact (eqA_iff (Orb.rep_unpack (Orb.prep_pidn hn1 hw1)) rep_idA).2 rfl
  · rw [allLt_iff]
    intro j hj
    rw [hFs] at hj
    have h4j := h4 j hj
    rw [Bool.and_eq_true] at h4j
    obtain ⟨g, hRg, -⟩ := hFrep j hj
    rw [Bool.and_eq_true]
    refine ⟨isInvA_of_rep hRg (rep_invCand hRg), ?_⟩
    unfold memG
    rw [hFj j hj]
    exact siftK_sound hbP hpP hlP rfl (range_of_permOK h4j.1) h4j.2
  · rw [allLt_iff]
    intro j hj
    rw [hFs] at hj
    rw [allLt_iff]
    intro j' hj'
    rw [List.any_eq_true]
    have hd := h5a j hj
    rw [ctAllN_iff] at hd
    have hd' := hd j' hj'
    rw [ctOrB_eq, ctNotB_eq, ctNotB_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at hd'
    have key : ∀ X : ℕ, ∀ (A : Array Bool), (∀ z < 120, A.getD z false = bit X z) →
        Nat.beq (fget (imgTab 120 9 X FI m) j 120) (fget (imgTab 120 9 X FI m) j' 120) = false →
        ∃ z ∈ List.range 120, ((F.map fun g => (Array.ofFn (n := 120) fun z =>
          A.getD (invCand 120 g)[z.val]! false : Array Bool))[j]!).getD z false ≠
          ((F.map fun g => (Array.ofFn (n := 120) fun z =>
            A.getD (invCand 120 g)[z.val]! false : Array Bool))[j']!).getD z false := by
      intro X A hA hne
      rw [imgTab_get hj, imgTab_get (by omega)] at hne
      obtain ⟨z, hz, hzne⟩ := exists_bit_ne (imgMask_lt _ _ _ _) (imgMask_lt _ _ _ _)
        (Nat.ne_of_beq_eq_false hne)
      refine ⟨z, List.mem_range.2 hz, ?_⟩
      rw [hMA A X hA j hj z hz, hMA A X hA j' (by omega) z hz, imgTab_get hj,
        imgTab_get (by omega)]
      exact hzne
    rcases hd' with hd' | hd'
    · obtain ⟨z, hz, hne⟩ := key FA fA hfA hd'
      exact ⟨z, hz, by rw [Bool.or_eq_true, bne_iff_ne, bne_iff_ne]; exact Or.inl hne⟩
    · obtain ⟨z, hz, hne⟩ := key FB fB hfB hd'
      exact ⟨z, hz, by rw [Bool.or_eq_true, bne_iff_ne, bne_iff_ne]; exact Or.inr hne⟩
  · rw [Array.all_eq_true]
    intro s hs
    rw [hUSs] at hs
    have h6s := h6 s hs
    rw [Bool.and_eq_true] at h6s
    rw [Bool.and_eq_true, ← getElem!_pos US s (by omega),
      stabB_eq (hUSrep s hs) (hUSr s hs) hfA', stabB_eq (hUSrep s hs) (hUSr s hs) hfB']
    exact h6s
  · rw [allLt_iff]
    intro j hj
    rw [hFs] at hj
    have h5j := h5b j hj
    rw [ctOrB_eq, ctNotB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h5j
    rw [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
    rcases h5j with h5j | h5j
    · left
      rw [Bool.eq_false_iff]
      intro hall
      rw [Array.all_eq_true] at hall
      have : CFSG.KLie.CT.allN kU (fun s => stabK 120 9 (UP s) (fget (imgTab 120 9 FA FI m) j 120) &&
          stabK 120 9 (UP s) (fget (imgTab 120 9 FB FI m) j 120)) = true := by
        rw [ctAllN_iff]
        intro s hs
        have := hall s (by omega)
        rw [Bool.and_eq_true, ← getElem!_pos US s (by omega)] at this
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [← stabB_eq (hUSrep s hs) (hUSr s hs) (fun z hz => hMA fA FA hfA j hj z hz)]
          exact this.1
        · rw [← stabB_eq (hUSrep s hs) (hUSr s hs) (fun z hz => hMA fB FB hfB j hj z hz)]
          exact this.2
      rw [this] at h5j
      exact absurd h5j (by decide)
    · right
      exact Nat.eq_of_beq_eq_true h5j
  · rw [hrho]
    exact isInvA_of_rep hr2.1 (rep_invCand hr2.1)
  · rw [allLt_iff]
    intro k hk
    have hlk := hl k hk
    rw [ctAndB_eq, Bool.and_eq_true] at hlk
    obtain ⟨g, -, hwe⟩ := hW _ hlk.1
    have h9k := h9 k hk
    rw [Bool.and_eq_true] at h9k
    rw [Bool.and_eq_true, hwe, copy0_unpack, huA k hk, Nat.eq_of_beq_eq_true h9k.1, hsigE]
    refine ⟨eqA_self _, ?_⟩
    unfold memG
    have hsk := ctAllN_iff.1 (hsig k hk)
    refine siftK_sound hbU hpU hlU rfl (Orb.allN_iff.2 fun z hz => ?_) h9k.2
    rw [← pg_land hz]
    exact hsk z hz
  · rw [allLt_iff]
    intro j hj
    have hlj := hl j hj
    rw [ctAndB_eq, Bool.and_eq_true] at hlj
    have hQ : ∀ j' < 6, ∃ g : Equiv.Perm (Fin 360),
        Rep 360 (wordA 360 OS (rawInvs 360 OS) (qw.getD j' [])) g ∧
          (wordA 360 OS (rawInvs 360 OS) (qw.getD j' [])).size = 360 := by
      intro j' hj'
      have hl' := hl j' hj'
      rw [ctAndB_eq, Bool.and_eq_true] at hl'
      obtain ⟨g, hg, hwe⟩ := hW _ hl'.2
      rw [hwe]
      exact ⟨g, hg, unpack_size _ _ _⟩
    have h64 : 2 ^ j < 64 := Nat.pow_lt_pow_right (by decide) hj
    obtain ⟨g, -, hwe⟩ := hW _ hlj.2
    rw [hT _ h64, psiTArrG_pow hQ hj, hwe, hsigE, Nat.eq_of_beq_eq_true (h10 j hj), htg j hj]
    exact eqA_self _

end CFSG.KC.O8

end
