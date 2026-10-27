module

public import Certificates.Data.Kernel.SporSch.MathieuOC
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.U6Chain
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu

@[expose] def ChainK (n w : Nat) (gens : List (Equiv.Perm (Fin n))) (words : List (List Int))
    {k : Nat} (bv : Vector (Fin n) k) (PS PSI LR TR TRI : Nat → Nat) (kS BP NS CH : Nat) : Prop :=
  0 < n ∧ n + 1 < 2 ^ w ∧ n < 65536 ∧
    (∀ j < gens.length, imageList (gens.getD j 1) = (unpack n w (PS j)).toList) ∧
    bv.toList.map Fin.val = (List.range k).map (pg w (mask w) BP) ∧
    headK n w (mask w) (n * w) (pidn n w) PS PSI kS gens.length words k BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS k BP ∧ n ≤ NS * CH ∧
    ∀ i < k, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP k i
      (stepsAt n w PS kS BP i) (s * CH) CH = true

@[expose] noncomputable def strongArr (n w kS : Nat) (PS : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := kS) fun j => unpack n w (PS j.val)

@[expose] noncomputable def baseArr (w k BP : Nat) : Array Nat :=
  Array.ofFn (n := k) fun i => pg w (mask w) BP i.val

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem binds_of (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) :
    Binds n w PS kS k BP (strongArr n w kS PS) (baseArr w k BP) :=
  ⟨hQ.1, hQ.2.1, hQ.2.2.1, by simp [strongArr], fun j hj => by
    rw [strongArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn], by simp [baseArr],
    fun t ht => by rw [baseArr, getElem!_pos _ t (by simpa using ht), Array.getElem_ofFn]⟩

theorem lenW_eq : ∀ D : List (List Int), CFSG.KS.Mathieu.lenW D = D.length
  | [] => rfl
  | _ :: D => congrArg Nat.succ (lenW_eq D)

theorem kS_eq (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) :
    kS = gens.length + words.length := by
  have hh := hQ.2.2.2.2.2.1
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  have := Nat.eq_of_beq_eq_true hh.2.2.2.1
  rw [Nat.add_eq, lenW_eq] at this
  omega

theorem rep_of_imageList {t : Array Nat} {g : Equiv.Perm (Fin n)} (h : imageList g = t.toList) :
    Rep n t g := by
  rw [← Array.toArray_toList (xs := t), ← h]
  exact rep_imageList g

theorem chainK_arrays (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) :
    ChainArrays (certificate hn gens words bv hbs)
        ((strongArr n w kS PS).extract 0 gens.length) (strongArr n w kS PS) (baseArr w k BP)
        (CFSG.Sporadic.Schreier.Co3.Native.wordsArr gens.length kS words) ∧
      rawChainOK n ((strongArr n w kS PS).extract 0 gens.length) (strongArr n w kS PS)
        (baseArr w k BP) (CFSG.Sporadic.Schreier.Co3.Native.wordsArr gens.length kS words) 1 =
        true := by
  have hb := binds_of hQ
  have hk := kS_eq hQ
  obtain ⟨-, -, -, hgen, hbv, hh, hl, hNS, hs⟩ := hQ
  have hraw := rawChainK_sound (chunks := 1) hb hh hl hNS hs
  refine ⟨?_, hraw⟩
  subst hk
  refine certificate_chainArrays hn gens words bv hbs hraw (by simp [strongArr])
    (by simp [strongArr]) (fun j hj => ?_) (by simp [baseArr]) (fun i => ?_)
  · rw [getElem!_pos _ j (by simp [strongArr]; omega), Array.getElem_extract]
    simp only [strongArr, Nat.zero_add, Array.getElem_ofFn]
    exact rep_of_imageList (hgen j hj)
  · have e := List.getElem_of_eq hbv (i := i.val) (by simp)
    simp only [List.getElem_map, Vector.getElem_toList, List.getElem_range] at e
    rw [baseArr, getElem!_pos _ i.val (by simp), Array.getElem_ofFn, ← e]
    rfl

theorem ordK_eq (LR : Nat → Nat) : ∀ k, ordK LR k = ((List.range k).map fun i => rcnt (LR i)).prod
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, ← ordK_eq LR k]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_comm _ _

theorem chainK_check (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) :
    (certificate hn gens words bv hbs).check = true ∧
      (certificate hn gens words bv hbs).orderCertificate = ordK LR k := by
  obtain ⟨hA, hraw⟩ := chainK_arrays hn hbs hQ
  obtain ⟨hV, hsz⟩ := validSchreier_of_chainOK hA Nat.one_pos hraw
  refine ⟨hV, ?_⟩
  have hb := binds_of hQ
  have hp := (Orb.head_facts hQ.2.2.2.2.2.1).1
  have hos := rawOrbitSizesK_sound hb hp hQ.2.2.2.2.2.2.1
  rw [ordK_eq, ← hos, RawSchreierDatum.orderCertificate, rawOrbitSizes]
  congr 1
  apply List.ext_getElem (by simp [rawLevels, baseArr]; rfl)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
  rw [hsz]
  change (rawLevels n _ _)[i]!.pts.size = _
  rw [getElem!_pos _ i (by simpa using h2)]

theorem chainK_sift (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {g : Equiv.Perm (Fin n)} {G : Nat}
    (hg : imageList g = (unpack n w G).toList)
    (hG : CFSG.KS.Prim.canonK n w (mask w) (n * w) G = true)
    (h : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 G = true) :
    (certificate hn gens words bv hbs).sift g 0 = true := by
  obtain ⟨hA, hraw⟩ := chainK_arrays hn hbs hQ
  have hb := binds_of hQ
  have hp := (Orb.head_facts hQ.2.2.2.2.2.1).1
  have hs := siftK_sound hb hp hQ.2.2.2.2.2.2.1 rfl (range_of_canonK hG) h
  have hF := chainCheckFacts hraw
  rw [hA.siftA_eq hF k 0 (by simp [certificate]) _ g (rep_of_imageList hg)] at hs
  exact hs

end CFSG.KS.SporSch.MOC

end
