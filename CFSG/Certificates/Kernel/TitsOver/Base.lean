module

public import Certificates.Data.Kernel.TitsOver.Check
public import CFSG.Certificates.Kernel.MaxD2.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
public import CFSG.Sporadic.Schreier.PairWords

public section

namespace CFSG.KS.TitsOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.KS.Mathieu
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.KS.MaxD2 CFSG.KS.BfsReplay
open CFSG.Monster.B.Co2.Native CFSG.AGLEmbedding.FusD2
open CFSG.Sporadic.Schreier (BaseFaithful)

variable {n w : Nat}

@[expose] def InH (H : Subgroup (Equiv.Perm (Fin n))) (w p : Nat) : Prop :=
  Cn n w p ∧ ∃ g ∈ H, TabRep (unpack n w p) g

@[expose] def BaseOK (n nb : Nat) (B : Nat → Nat) (bs : List Nat) : Prop :=
  (∀ s < nb, B s < n) ∧ ∀ x ∈ bs, ∃ s < nb, B s = x

theorem InH.mul {H : Subgroup (Equiv.Perm (Fin n))} {p q : Nat} (hp : InH H w p)
    (hq : InH H w q) : InH H w (pcomp n w (mask w) p q) := by
  obtain ⟨hp1, g, hg, hpg⟩ := hp
  obtain ⟨hq1, h, hh, hqh⟩ := hq
  refine ⟨cc hp1 hq1, g * h, H.mul_mem hg hh, ?_⟩
  rw [← comp_u hp1 hq1]
  exact hpg.comp hqh

theorem InH.one {H : Subgroup (Equiv.Perm (Fin n))} (hn : szOK n w = true) :
    InH H w (pidn n w) :=
  ⟨pidn_canon hn, 1, H.one_mem, by rw [← id_u hn]; exact TabRep.idTab⟩

theorem InH.eq_of_base {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat} {nb : Nat}
    {B : Nat → Nat} (hF : BaseFaithful H bs) (hB : BaseOK n nb B bs) {p q : Nat}
    (hp : InH H w p) (hq : InH H w q)
    (h : ∀ s < nb, pg w (mask w) p (B s) = pg w (mask w) q (B s)) : p = q := by
  obtain ⟨hp1, g, hg, hpg⟩ := hp
  obtain ⟨hq1, g', hg', hqg⟩ := hq
  have hfix : ∀ x : Fin n, (x : ℕ) ∈ bs → g x = g' x := by
    intro x hx
    obtain ⟨s, hs, e⟩ := hB.2 x hx
    have h1 := hpg.apply x
    have h2 := hqg.apply x
    rw [get_u x.isLt, ← e] at h1 h2
    apply Fin.ext
    rw [← h1, ← h2]
    exact h s hs
  have h1 := hF (g'⁻¹ * g) (H.mul_mem (H.inv_mem hg') hg) fun x hx => by
    rw [Equiv.Perm.mul_apply, hfix x hx]
    exact Equiv.Perm.inv_eq_iff_eq.2 rfl
  rw [inv_mul_eq_one] at h1
  subst h1
  exact u_inj hp1 hq1 (hpg.tab_eq hqg)

theorem lexLtK_iffB {a b c d : Nat} : lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold lexLtK LexLt
  simp only [PK.bIf_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  by_cases h : a < c
  · simp [h]
  · simp [h]

theorem inj_of_sortB {cnt : Nat} {T S SI : Nat → Nat}
    (hS : ∀ i < cnt, S i < cnt ∧ SI (S i) = i ∧ (i + 1 < cnt → T (S i) < T (S (i + 1)))) :
    ∀ a < cnt, ∀ b < cnt, T a = T b → a = b := by
  have hmono : ∀ i j, i < j → j < cnt → T (S i) < T (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hsurj : ∀ a < cnt, ∃ i < cnt, S i = a := by
    classical
    have himg : (Finset.range cnt).image S = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg SI e
    intro a ha
    have : a ∈ (Finset.range cnt).image S := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e (Nat.ne_of_lt (hmono i j h hj))
  · rw [h]
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h hi))

theorem penumPtB_spec {m nw k cnt nb i : Nat} {G B T PL POS SRT SRI : Nat → Nat}
    (h : penumPtBK n w m nw G k cnt nb B T PL POS SRT SRI i = true) :
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      T i = pcomp n w m (G (labOf PL i)) (T (parOf PL i)) ∧
      (i + 1 < cnt → LexLt (parOf PL i) (labOf PL i) (parOf PL (i + 1)) (labOf PL (i + 1)))) ∧
    (∀ j < k, r32 POS (i * k + j) < cnt ∧
      (∀ s < nb, pg w m (T (r32 POS (i * k + j))) (B s) = pg w m (G j) (pg w m (T i) (B s))) ∧
      (r32 POS (i * k + j) = 0 ∨
        ¬ LexLt i j (parOf PL (r32 POS (i * k + j))) (labOf PL (r32 POS (i * k + j))))) ∧
    (r32 SRT i < cnt ∧ r32 SRI (r32 SRT i) = i ∧
      (i + 1 < cnt → T (r32 SRT i) < T (r32 SRT (i + 1)))) := by
  unfold penumPtBK at h
  rw [PK.strictB_eq] at h
  simp only [PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨ht, hpos, hs⟩ := h
  refine ⟨fun hi => ?_, fun j hj => ?_, ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [PK.strictB_eq, PK.bIf_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    refine ⟨h1, h2, Nat.eq_of_beq_eq_true h3, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h4
    exact lexLtK_iffB.1 h4
  · have hq := (PK.allN_iff.1 hpos) j hj
    simp only [PK.strictB_eq, PK.bAnd_eq, Nat.mul_eq, Nat.add_eq, Bool.and_eq_true,
      Nat.blt_eq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, fun s hs => ?_, ?_⟩
    · have hb := (PK.allN_iff.1 h2) s hs
      rw [PK.strictB_eq] at hb
      exact Nat.eq_of_beq_eq_true hb
    · by_cases h0 : r32 POS (i * k + j) = 0
      · exact Or.inl h0
      · right
        have e : Nat.beq (r32 POS (i * k + j)) 0 = false :=
          Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
        rw [PK.bIf_eq, e] at h3
        intro hl
        rw [← lexLtK_iffB] at hl
        simp only [Bool.false_eq_true, ↓reduceIte, PK.bIf_eq, hl] at h3
  · rw [PK.strictB_eq] at hs
    simp only [PK.bIf_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h3
    exact Nat.blt_eq.mp h3

theorem penumSlB_spec {m nw k cnt nb lo len : Nat} {G B T PL POS SRT SRI : Nat → Nat}
    (h : penumSlBK n w m nw G k cnt nb B T PL POS SRT SRI lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt →
      penumPtBK n w m nw G k cnt nb B T PL POS SRT SRI i = true := by
  intro i h1 h2 h3
  have h' := (PK.allN_iff.1 h) (i - lo) (by omega)
  rw [PK.strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, PK.bIf_eq, if_pos (Nat.blt_eq.mpr h3)] at h'
  exact h'

theorem penumBK_left_sound {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}
    {k cnt cap nb : Nat} {G B T PL POS SRT SRI : Nat → Nat} {gens : Array Tab}
    (hn : szOK n w = true) (hg : GensOK n w k G gens) (hGH : ∀ j < k, InH H w (G j))
    (hF : BaseFaithful H bs) (hB : BaseOK n nb B bs)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtBK n w (mask w) (n * w) G k cnt nb B T PL POS SRT SRI i = true) :
    (enumBFS n gens cap = penumRec n w cnt T PL ∧
      enumOK n gens (penumRec n w cnt T PL) = true) ∧ ∀ i < cnt, InH H w (T i) := by
  obtain ⟨hk, hgj⟩ := hg
  have sp := fun i (hi : i < cnt) => penumPtB_spec (hp i hi)
  unfold penumHdK at hh
  simp only [PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hh
  obtain ⟨hc0, hcap, hT0, hPL0⟩ := hh
  have hT0' : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have hIn : ∀ i < cnt, InH H w (T i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h0 : i = 0
      · subst h0
        rw [hT0']
        exact InH.one hn
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).1 h0
        rw [h3]
        exact (hGH _ h2).mul (ih _ h1 (by omega))
  have hclose : ∀ h < cnt, ∀ j < k,
      T (r32 POS (h * k + j)) = pcomp n w (mask w) (G j) (T h) := by
    intro h hh j hj
    obtain ⟨h1, h2, -⟩ := (sp h hh).2.1 j hj
    exact InH.eq_of_base hF hB (hIn _ h1) ((hGH j hj).mul (hIn h hh)) fun s hs => by
      rw [h2 s hs, pg_pc hn (hB.1 s hs)]
  have hstep : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      leftStep n gens j (unpack n w t) = unpack n w (pcomp n w (mask w) (G j) t) := by
    intro j hj t ht
    unfold leftStep
    rw [(hgj j hj).1]
    exact comp_u (hgj j hj).2 ht
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortB (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2
  have R : Replay (leftStep n gens) k (idTab n) cnt (fun i => unpack n w (T i)) (parOf PL)
      (labOf PL) (fun h j => r32 POS (h * k + j)) := by
    refine ⟨hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change unpack n w (T 0) = idTab n
      rw [hT0', ← id_u hn]
    · unfold parOf
      rw [Nat.eq_of_beq_eq_true hPL0]
      rfl
    · unfold labOf
      rw [Nat.eq_of_beq_eq_true hPL0]
      rfl
    · intro a ha b hb e
      exact hinjT a ha b hb (u_inj (hIn a ha).1 (hIn b hb).1 e)
    · intro i hi0 hi
      obtain ⟨h1, h2, h3, -⟩ := (sp i hi).1 (by omega)
      refine ⟨h1, h2, ?_⟩
      change unpack n w (T i) = leftStep n gens (labOf PL i) (unpack n w (T (parOf PL i)))
      rw [hstep _ h2 _ (hIn _ (by omega)).1, ← h3]
    · intro i hi0 hi
      exact ((sp i (by omega)).1 (by omega)).2.2.2 hi
    · intro h hh j hj
      obtain ⟨h1, -, h3⟩ := (sp h hh).2.1 j hj
      refine ⟨h1, ?_, h3⟩
      change leftStep n gens j (unpack n w (T h)) = unpack n w (T (r32 POS (h * k + j)))
      rw [hstep _ hj _ (hIn h hh).1, hclose h hh j hj]
  rw [← hk] at R
  have := enumBFS_replay R hcap
  rw [penumRec_eq]
  exact ⟨this, hIn⟩

theorem icode_div (z : Int) : Nat.sub (Nat.shiftRight (icode z) 1) 1 = z.natAbs - 1 := by
  change icode z >>> 1 - 1 = _
  rw [Nat.shiftRight_eq_div_pow]
  cases z with
  | ofNat k =>
    change (k + k) / 2 ^ 1 - 1 = _
    simp only [Int.natAbs_ofNat']
    omega
  | negSucc k =>
    change (k + 1 + (k + 1) + 1) / 2 ^ 1 - 1 = _
    simp only [Int.natAbs_negSucc]
    omega

theorem icode_land (z : Int) : Nat.land (icode z) 1 = if 0 ≤ z then 0 else 1 := by
  change icode z &&& 1 = _
  rw [Nat.and_one_is_mod]
  cases z with
  | ofNat k =>
    change (k + k) % 2 = _
    have h0 : (0 : Int) ≤ Int.ofNat k := Int.ofNat_nonneg k
    rw [if_pos h0]
    omega
  | negSucc k =>
    change (k + 1 + (k + 1) + 1) % 2 = _
    rw [if_neg (Int.not_le.2 (Int.negSucc_lt_zero k))]
    omega

theorem wordPt_eq {S : List (Equiv.Perm (Fin n))} {gs gi : Array Tab} {kL : Nat}
    {Lf Li : Nat → Nat → Nat}
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹)
    (hLf : ∀ l < kL, ∀ y < n, Lf l y = (gs.getD l (idTab n))[y]!)
    (hLi : ∀ l < kL, ∀ y < n, Li l y = (gi.getD l (idTab n))[y]!) :
    ∀ wd : List Int, lettersOK kL wd = true → ∀ x < n,
      wordPtK (letF Lf Li) wd x = (Certificates.FusD2Perm.wordT n gs gi wd)[x]!
  | [], _, x, hx => by
    change x = (idTab n)[x]!
    unfold idTab
    rw [getElem!_pos _ x (by simpa using hx)]
    simp
  | z :: wd, hl, x, hx => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hw⟩ := hl
    have ih := wordPt_eq hgs hgi hLf hLi wd (by simpa only [lettersOK] using hw) x hx
    have hrep := wordT_rep S gs gi hgs hgi wd
    have hy : (Certificates.FusD2Perm.wordT n gs gi wd)[x]! < n := by
      rw [hrep.apply ⟨x, hx⟩]
      exact (wordVal S wd ⟨x, hx⟩).isLt
    change strictN (wordPtK (letF Lf Li) wd x) (fun y => letF Lf Li (icode z) y) =
      (comp n _ (Certificates.FusD2Perm.wordT n gs gi wd))[x]!
    rw [PK.strictN_eq, ih, comp_get hx]
    unfold letF
    rw [PK.nIf_eq, icode_div, icode_land]
    by_cases hz : 0 < z
    · have e1 : Nat.beq (if 0 ≤ z then 0 else 1) 0 = true := by
        rw [if_pos (by omega)]
        rfl
      rw [if_pos e1, if_pos hz, hLf _ (by omega) _ hy]
      have e2 : z.natAbs - 1 = z.toNat - 1 := by omega
      rw [e2]
    · have e1 : Nat.beq (if 0 ≤ z then 0 else 1) 0 = false := by
        rw [if_neg (by omega)]
        rfl
      rw [if_neg (by rw [e1]; decide), if_neg hz, hLi _ (by omega) _ hy]
      have e2 : z.natAbs - 1 = (-z).toNat - 1 := by omega
      rw [e2]

theorem wordBK_sound {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat} {nb kL : Nat}
    {B : Nat → Nat} (hF : BaseFaithful H bs) (hB : BaseOK n nb B bs)
    {S : List (Equiv.Perm (Fin n))} {gs gi : Array Tab} {Lf Li : Nat → Nat → Nat}
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹)
    (hLf : ∀ l < kL, ∀ y < n, Lf l y = (gs.getD l (idTab n))[y]!)
    (hLi : ∀ l < kL, ∀ y < n, Li l y = (gi.getD l (idTab n))[y]!)
    (hS : ∀ g ∈ S, g ∈ H) {wd : List Int} {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g)
    (hg : g ∈ H) {tgt : Nat → Nat} (htgt : ∀ s < nb, tgt (B s) = t[B s]!)
    (h : wordBK kL nb B Lf Li wd tgt = true) :
    Certificates.FusD2Perm.wordT n gs gi wd = t := by
  unfold wordBK at h
  obtain ⟨hl, hb⟩ := band_e h
  have hl' := lettersK_sound hl
  have hw := wordT_rep S gs gi hgs hgi wd
  have hval : wordVal S wd ∈ H := wordVal_mem S H hS wd
  have hfix : ∀ x : Fin n, (x : ℕ) ∈ bs → wordVal S wd x = g x := by
    intro x hx
    obtain ⟨s, hs, e⟩ := hB.2 x hx
    have h1 := (PK.allN_iff.1 hb) s hs
    rw [PK.strictB_eq] at h1
    have h2 := Nat.eq_of_beq_eq_true h1
    rw [wordPt_eq hgs hgi hLf hLi wd hl' _ (hB.1 s hs), htgt s hs, e, hw.apply x,
      ht.apply x] at h2
    exact Fin.ext h2
  have h1 := hF (g⁻¹ * wordVal S wd) (H.mul_mem (H.inv_mem hg) hval) fun x hx => by
    rw [Equiv.Perm.mul_apply, hfix x hx]
    exact Equiv.Perm.inv_eq_iff_eq.2 rfl
  rw [inv_mul_eq_one] at h1
  rw [h1] at ht
  exact hw.tab_eq ht

end CFSG.KS.TitsOver

end
