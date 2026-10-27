module

public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem siftK_zero (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP l G : Nat) :
    siftK n w m nw idn LR TRI BP 0 l G = bAnd(szOK n w, Nat.beq G idn) := rfl

theorem siftK_succ (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP d l G : Nat) :
    siftK n w m nw idn LR TRI BP (d + 1) l G =
      strictB (LR l) (fun R => strictB (rpos w m nw R (pg w m G (pg w m BP l))) (fun k =>
        bIf(Nat.blt k (rcnt R), strictB (pcomp n w m (TRI (Nat.add (roff n nw R) k)) G)
          (siftK n w m nw idn LR TRI BP d (Nat.succ l)), false))) := rfl

theorem head_facts {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true ∧
      n < 16777216 ∧ kS < 128 := by
  unfold headK at hh
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, hk, _, _, hperm, _⟩ := hh
  unfold szOK at hsz
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hsz
  exact ⟨hperm, hsz.1, Nat.blt_eq.mp hk⟩

theorem szOK_facts {n w : Nat} (h : szOK n w = true) : n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold szOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have h3 := Nat.blt_eq.mp h2
  rw [shl_eq', Nat.one_mul] at h3
  exact ⟨Nat.blt_eq.mp h1, h3⟩

section Sift

variable {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
include hb

theorem siftA_of_siftK_rng (hsz : n < 16777216) {LR TR TRI : Nat → Nat}
    (hbl : ∀ t < nb, base[t]! < n)
    (hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (g : Array Nat),
      (∀ i < n, g[i]! = pg w (mask w) G i ∧ pg w (mask w) G i < n) →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true →
      siftA n (rawLevels n S base) base l g = true := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro l hl G g hG h
    rw [siftK_zero] at h
    obtain ⟨hs, he⟩ := (bAnd_iff _ _).1 h
    have hGe : G = pidn n w := Nat.eq_of_beq_eq_true he
    obtain ⟨_, hw⟩ := szOK_facts hs
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)]
    unfold eqA
    rw [allLt_iff]
    intro i hi
    rw [(hG i hi).1, hGe, PF.pg_pidn hsz hw hi, idA_get hi]
    exact beq_self_eq_true i
  | succ d ih =>
    intro l hl G g hG h
    have hlb : l < nb := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    obtain ⟨TK, A, hT⟩ := hag l hlb
    have hbt : base[l]! = pg w (mask w) BP l := hb.2.2.2.2.2.2 l hlb
    have hbl' := hbl l hlb
    rw [siftK_succ, ← hbt] at h
    simp only [strictB_eq, bIf_eq] at h
    split at h
    · rename_i hk
      have hk' := Nat.blt_eq.mp hk
      have hz : g[base[l]!]! = pg w (mask w) G base[l]! := (hG _ hbl').1
      have hzn : pg w (mask w) G base[l]! < n := (hG _ hbl').2
      have hK := (A.pos _ hzn).1 hk'
      have hKe := A.posE _ hzn hK
      rw [siftA, dite_eq_left hls, chainLevels_getElem hls, hz]
      simp only [hK, decide_true, Bool.true_and]
      rw [← hKe]
      refine ih (l + 1) (by omega) _ _ (fun i hi => ?_) h
      have hgi := hG i hi
      have hR := (A.tr _ (hKe ▸ hK)).2
      have e := (hT _ hk').2 ⟨_, hgi.2⟩
      rw [compA_get hi, hgi.1, PF.pg_pcomp (by omega) hi]
      exact ⟨(hR.apply hgi.2).trans e.symm, lt_of_eq_of_lt e (Fin.is_lt _)⟩
    · exact absurd h Bool.false_ne_true

theorem siftA_of_siftK (hsz : n < 16777216) {LR TR TRI : Nat → Nat}
    (hbl : ∀ t < nb, base[t]! < n)
    (hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (g : Array Nat) (γ : Equiv.Perm (Fin n)),
      PRep n w G γ → Rep n g γ →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true →
      siftA n (rawLevels n S base) base l g = true := fun d l hl G g γ hG hg =>
  siftA_of_siftK_rng hb hsz hbl hag d l hl G g fun i hi =>
    ⟨by rw [hg.apply hi, hG ⟨i, hi⟩], by rw [hG ⟨i, hi⟩]; exact Fin.is_lt _⟩

omit hb in
theorem schK_spec {n w m nw idn kS BP nb i T h₀ cnt : Nat} {S SI LR TR TRI : Nat → Nat}
    (hs : schK n w m nw idn S SI LR TR TRI kS BP nb i T h₀ cnt = true) {h : Nat}
    (hh0 : h₀ ≤ h) (hh1 : h < h₀ + cnt) (hc : h < rcnt (LR i)) :
    ∀ j < stCnt T, rpos w m nw (LR i) (pg w m (letterK S SI kS (stAt T j))
        (rpt w m (LR i) h)) < rcnt (LR i) ∧
      siftK n w m nw idn LR TRI BP (Nat.sub nb (Nat.succ i)) (Nat.succ i)
        (pcomp n w m (TRI (Nat.add (roff n nw (LR i)) (rpos w m nw (LR i)
          (pg w m (letterK S SI kS (stAt T j)) (rpt w m (LR i) h)))))
          (pcomp n w m (letterK S SI kS (stAt T j)) (TR (Nat.add (roff n nw (LR i)) h)))) =
        true := by
  intro j hj
  unfold schK at hs
  simp only [strictB_eq] at hs
  have h1 := allN_spec hs (h - h₀) (by omega)
  have e : Nat.add h₀ (h - h₀) = h := by
    rw [Nat.add_eq]
    omega
  rw [e] at h1
  have h2 := allN_spec (bIf_of_true (blt_true hc) h1) j hj
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Nat.blt_eq.mp h3, h4⟩

variable (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
include hp

theorem schreierOK_of_schK (hk : kS < 128) (hsz : n < 16777216) {LR TR TRI : Nat → Nat}
    (hbl : ∀ t < nb, base[t]! < n)
    (hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹)
    {i NS CH : Nat} (hi : i < nb) (hNS : n ≤ NS * CH)
    (hs : ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) (chunks : Nat) :
    CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
      (rawLevels n S base)[i]! chunks = true := by
  change CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
    (lev n S base i) chunks = true
  unfold CFSG.Monster.B.Co2.Native.schreierOK
  apply parLt_of_forall
  intro h hh
  rw [allLt_iff]
  intro j hj
  dsimp only
  obtain ⟨TK, A, hT⟩ := hag i hi
  obtain ⟨hcnt, hpr, hlet, _⟩ := kernel_steps hb hp hk hbl hi.le
  have F := native_facts hb hp hi (hbl i hi)
  have hhc : h < rcnt (LR i) := by rw [A.cnt]; exact hh
  obtain ⟨hCH, hsk, e⟩ := slice_cover hNS (by have := F.le; omega : h < n)
  have hk2 := schK_spec (hs _ hsk) (h := h) (by rw [Nat.add_eq] at e; omega)
    (by have := Nat.mod_lt h hCH; rw [Nat.add_eq] at e; omega) hhc j (by rw [hcnt]; exact hj)
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
  simp only [hK, decide_true, Bool.true_and]
  rw [hKe] at hk4
  exact siftA_of_siftK hb hsz hbl hag (nb - (i + 1)) (i + 1) (by omega) _ _ _
    (prep_pcomp (by omega) (hT _ (by rw [A.cnt]; exact hK)).2
      (prep_pcomp (by omega) (hlet j hj) (hT h hhc).1))
    (rep_compA (A.tr _ hK).2 (rep_compA (rep_stp hb hp hj) (A.tr h hh).1)) hk4

end Sift

theorem rawChainOK_of_K {n w kS kO nb BP NS CH chunks : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true := by
  obtain ⟨hk, hH⟩ := rawHeadOK_of hb hh
  have hd := hd_of_head hk hH
  obtain ⟨hp, hsz, hkS⟩ := head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl : ∀ t < nb, base[t]! < n := fun t ht => hd.base_lt t (by omega)
  have hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹ :=
    fun l hl' => ⟨_, agree_levelK hb hp hbl hl' (hl l hl')⟩
  have hlv : ∀ i < base.size, levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]! = true := fun i hi => by
    rw [rawLevels_get hi]
    exact levelOK_of (levelOKT_bfs (hd.base_lt i hi) (steps_lt hd))
      (levelTrOK_bfs fun j hj => ⟨_, (step_rep hd hj).choose_spec.1⟩)
  have hsc : ∀ i < base.size, CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks = true := fun i hi =>
    schreierOK_of_schK hb hp hkS hsz hbl hag (by omega) hNS (hs i (by omega)) chunks
  change (rawHeadOK n (S.extract 0 kO) S base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]!) &&
    allLt base.size (fun i => CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks)) = true
  rw [hH, allLt_iff.2 hlv, allLt_iff.2 hsc]
  rfl

theorem base_lt_of_levels {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} (hb : Binds n w PS kS nb BP S base)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) : ∀ t < nb, base[t]! < n := fun t ht => by
  obtain ⟨_, _, hR, _⟩ := levelK_facts (hl t ht)
  rw [hb.2.2.2.2.2.2 t ht, ← hR.root]
  exact (hR.pt 0 hR.c_pos).1

theorem rawOrbitSizes_of_K {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    rawOrbitSizes n S base = (List.range nb).map fun i => rcnt (LR i) := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl := base_lt_of_levels hb hl
  rw [rawOrbitSizes]
  apply List.ext_getElem
  · simp [rawLevels, hbs]
  · intro k _ h2
    have hk : k < nb := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [chainLevels_getElem (by rw [chainLevels_size]; omega)]
    exact (agree_levelK hb hp hbl hk (hl k hk)).1.cnt.symm

theorem siftA_of_K {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hg : g = unpack n w G)
    (hr : allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true)
    (h : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true) :
    siftA n (rawLevels n S base) base 0 g = true := by
  have hbl := base_lt_of_levels hb hl
  have hsz : n < 16777216 := by have := hb.2.2.1; omega
  refine siftA_of_siftK_rng hb hsz hbl (fun l hl' => ⟨_, agree_levelK hb hp hbl hl' (hl l hl')⟩)
    nb 0 (Nat.zero_add nb) G g (fun i hi => ⟨by rw [hg, unpack_get hi], ?_⟩) h
  exact Nat.blt_eq.mp (allN_spec hr i hi)

end CFSG.KS.Raw.Orb

end
