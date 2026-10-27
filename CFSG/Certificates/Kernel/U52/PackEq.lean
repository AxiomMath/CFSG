module

public import Certificates.Data.Kernel.Spor.WordF
public import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.StrongOfSound
import CFSG.Certificates.Kernel.U52.EvSound
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.HNOddCore.ChainUtil

public section

namespace CFSG.KS.WordF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

variable {n w : Nat}

@[expose] def Rng (n w P : Nat) : Prop := ∀ x < n, pg w (mask w) P x < n

@[expose] def Canon (n w P : Nat) : Prop := P >>> (n * w) = 0

theorem allBelowN_eq_allN (m : Nat) (p : Nat → Bool) :
    CFSG.ONSchreier.Native.allBelowN m p = allN m p := by
  rw [Bool.eq_iff_iff, CFSG.ONSchreier.allBelowN_iff]
  exact ⟨allN_of_forall, allN_spec⟩

theorem getElem!_unpack (P i : Nat) :
    (unpack n w P)[i]! = if i < n then pg w (mask w) P i else 0 := by
  split_ifs with h
  · exact unpack_get h
  · rw [getElem!_neg _ i (by simpa [unpack] using h)]
    rfl

theorem pcomp_unpackR (hn : n < 2 ^ 32) (P : Nat) {Q : Nat} (hQ : Rng n w Q) :
    CFSG.ONSchreier.Native.pcomp n (unpack n w P) (unpack n w Q) =
      unpack n w (pcomp n w (mask w) P Q) :=
  pcomp_unpack hn hQ

theorem rng_pcomp (hn : n < 2 ^ 32) {P Q : Nat} (hP : Rng n w P) (hQ : Rng n w Q) :
    Rng n w (pcomp n w (mask w) P Q) := fun x hx => by
  rw [CFSG.KS.PF.pg_pcomp hn hx]
  exact hP _ (hQ x hx)

theorem canon_pcomp (hn : n < 2 ^ 32) (hw : 0 < w) (P Q : Nat) :
    Canon n w (pcomp n w (mask w) P Q) :=
  CFSG.KS.PF.pcomp_shr P Q hn hw

theorem rng_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : Rng n w (pidn n w) := fun x hx => by
  rw [CFSG.KS.PF.pg_pidn hn hw hx]
  exact hx

theorem canon_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : Canon n w (pidn n w) :=
  CFSG.KS.PF.pidn_shr hn hw

theorem rng_of_permOK {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) : Rng n w P :=
  fun x hx => ((permOK_facts h).2.2 x hx).1

theorem canon_of_permOK {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    Canon n w P :=
  (permOK_facts h).1

theorem canon_evFK (hn : n < 2 ^ 32) (hn' : n < 16777216) (hw : n + 1 < 2 ^ w) {k : Nat}
    (LP LPI : Nat → Nat) (wd : List (Fin k × Bool)) :
    Canon n w (evFK n w (mask w) (pidn n w) LP LPI wd) := by
  cases wd with
  | nil => exact canon_pidn hn' hw
  | cons l wd => exact canon_pcomp hn (CFSG.KS.PF.w_pos hw) _ _

theorem rng_evFK (hn : n < 2 ^ 32) (hn' : n < 16777216) (hw : n + 1 < 2 ^ w) {k : Nat}
    {LP LPI : Nat → Nat} (hr : ∀ i < k, Rng n w (LP i) ∧ Rng n w (LPI i))
    (wd : List (Fin k × Bool)) : Rng n w (evFK n w (mask w) (pidn n w) LP LPI wd) := by
  induction wd with
  | nil => exact rng_pidn hn' hw
  | cons l wd ih =>
    obtain ⟨⟨i, hi⟩, b⟩ := l
    have e : evFK n w (mask w) (pidn n w) LP LPI ((⟨i, hi⟩, b) :: wd) =
        pcomp n w (mask w) (cond b (LP i) (LPI i)) (evFK n w (mask w) (pidn n w) LP LPI wd) := by
      cases b <;> rfl
    rw [e]
    refine rng_pcomp hn ?_ ih
    cases b
    · exact (hr i hi).2
    · exact (hr i hi).1

theorem pisInv_unpack {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    CFSG.ONSchreier.Native.pisInv n (unpack n w P) (unpack n w Q) = true := by
  obtain ⟨_, _, h3⟩ := permOK_facts h
  unfold CFSG.ONSchreier.Native.pisInv
  refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
  rw [unpack_get hi, unpack_get (h3 i hi).1, (h3 i hi).2]
  simp [(h3 i hi).1]

theorem unpack_inj (hw : 0 < w) {P Q : Nat} (hP : Canon n w P) (hQ : Canon n w Q)
    (h : unpack n w P = unpack n w Q) : P = Q :=
  CFSG.KS.PF.eq_of_fields hw hP hQ fun i hi => by rw [← unpack_get hi, h, unpack_get hi]

theorem peq_unpackC (hw : 0 < w) {P Q : Nat} (hP : Canon n w P) (hQ : Canon n w Q) :
    CFSG.ONSchreier.Native.peq n (unpack n w P) (unpack n w Q) = Nat.beq P Q := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]
  unfold CFSG.ONSchreier.Native.peq
  rw [CFSG.ONSchreier.allBelowN_iff]
  constructor
  · intro h
    refine CFSG.KS.PF.eq_of_fields hw hP hQ fun i hi => ?_
    have h1 := h i hi
    rw [unpack_get hi, unpack_get hi] at h1
    exact beq_iff_eq.1 h1
  · rintro rfl i _
    exact beq_self_eq_true _

theorem beq_unpackC (hw : 0 < w) {P Q : Nat} (hP : Canon n w P) (hQ : Canon n w Q) :
    (unpack n w P == unpack n w Q) = Nat.beq P Q := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨unpack_inj hw hP hQ, fun h => h ▸ rfl⟩

theorem contains_map_unpackC (hw : 0 < w) {α : Type} (f : α → Nat) (hf : ∀ x, Canon n w (f x))
    (l : List α) {Q : Nat} (hQ : Canon n w Q) :
    (l.map fun x => unpack n w (f x)).contains (unpack n w Q) = l.any fun x => Nat.beq Q (f x) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.contains_cons, List.any_cons, beq_unpackC hw hQ (hf a), ih]

theorem getD_map_unpack {α : Type} (f : α → Nat) (l : List α) (i : Nat) (d : Nat) :
    (l.map fun x => unpack n w (f x)).getD i (unpack n w d) = unpack n w ((l.map f).getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem canon_getD {α : Type} {f : α → Nat} (hf : ∀ x, Canon n w (f x)) (l : List α) (i : Nat)
    {d : Nat} (hd : Canon n w d) : Canon n w ((l.map f).getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact hd
  | some a => exact hf a

theorem rng_getD {α : Type} {f : α → Nat} (hf : ∀ x, Rng n w (f x)) (l : List α) (i : Nat)
    {d : Nat} (hd : Rng n w d) : Rng n w ((l.map f).getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact hd
  | some a => exact hf a

theorem sift_unpack {kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {G : Nat} (hG : Canon n w G)
    (hr : Rng n w G) :
    CFSG.Monster.B.Co2.Native.siftA n (CFSG.Certificates.Native.rawLevels n S base) base 0
        (unpack n w G) =
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G :=
  siftK_eq hb hp hl rfl hG (allN_of_forall fun i hi => Nat.blt_eq.mpr (hr i hi))

theorem binds_of {kS kO nb BP : Nat} {PS PSI : Nat → Nat} {O : Array (Array Nat)}
    {W : Array (List Int)} {D : List (List Int)} {base : List (Fin n)}
    (hO : O.size = kO ∧ ∀ j < kO, O[j]! = unpack n w (PS j))
    (hD : W.extract kO W.size = D.toArray) (hn : 0 < n ∧ n + 1 < 2 ^ w ∧ n < 65536)
    (hbase : (base.map Fin.val).toArray.size = nb ∧
      ∀ t < nb, (base.map Fin.val).toArray[t]! = pg w (mask w) BP t)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    Binds n w PS kS nb BP (CFSG.Sporadic.HNOddCore.strongArrs n O W) (base.map Fin.val).toArray := by
  have hSe : CFSG.Sporadic.HNOddCore.strongArrs n O W =
      (CFSG.YGroups.ModelNative.strongOf n O D.toArray).1 := by
    unfold CFSG.Sporadic.HNOddCore.strongArrs
    rw [hO.1, hD]
  obtain ⟨hS1, hS2⟩ := strongOf_bind hO hh
  rw [← hSe] at hS1 hS2
  exact ⟨hn.1, hn.2.1, hn.2.2, hS1, hS2, hbase.1, hbase.2⟩

end CFSG.KS.WordF

end
