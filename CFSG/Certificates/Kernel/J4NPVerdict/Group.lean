module

public import CFSG.Certificates.Kernel.J4NPVerdict.Rep
public import CFSG.Sporadic.J4.QT2AData

public section

namespace CFSG.KC.J4NPV

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KC.Loop

theorem vj_char_le (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

theorem w5K_eq : ∀ cs : List Char, w5K cs = cs.filterMap fun ch =>
    if 'a' ≤ ch ∧ ch ≤ 'e' then some ((ch.toNat - 'a'.toNat + 1 : Nat) : Int)
    else if 'A' ≤ ch ∧ ch ≤ 'E' then some (-((ch.toNat - 'A'.toNat + 1 : Nat) : Int))
    else none
  | [] => rfl
  | ch :: cs => by
    rw [List.filterMap_cons, ← w5K_eq cs]
    have key : w5K (ch :: cs) = Bool.rec (motive := fun _ => List Int)
        (Bool.rec (motive := fun _ => List Int) (w5K cs)
          (List.cons (Int.negSucc (Nat.sub ch.toNat 65)) (w5K cs))
          (andB (Nat.ble 65 ch.toNat) (Nat.ble ch.toNat 69)))
        (List.cons (Int.ofNat (Nat.sub ch.toNat 96)) (w5K cs))
        (andB (Nat.ble 97 ch.toNat) (Nat.ble ch.toNat 101)) := rfl
    rw [key]
    have e97 : ('a' : Char).toNat = 97 := rfl
    have e101 : ('e' : Char).toNat = 101 := rfl
    have e65 : ('A' : Char).toNat = 65 := rfl
    have e69 : ('E' : Char).toNat = 69 := rfl
    simp only [vj_char_le, e97, e101, e65, e69]
    cases hA : andB (Nat.ble 97 ch.toNat) (Nat.ble ch.toNat 101) with
    | true =>
      obtain ⟨a1, a2⟩ := vj_andB_iff.1 hA
      rw [Nat.ble_eq] at a1 a2
      rw [if_pos ⟨a1, a2⟩]
      change Int.ofNat (ch.toNat - 96) :: w5K cs = ((ch.toNat - 97 + 1 : Nat) : Int) :: w5K cs
      congr 1
      have : ch.toNat - 96 = ch.toNat - 97 + 1 := by omega
      rw [this]
      rfl
    | false =>
      have h1 : ¬ (97 ≤ ch.toNat ∧ ch.toNat ≤ 101) := by
        rintro ⟨a1, a2⟩
        rw [← Nat.ble_eq] at a1 a2
        rw [a1, a2] at hA
        exact absurd hA (by decide)
      rw [if_neg h1]
      cases hB : andB (Nat.ble 65 ch.toNat) (Nat.ble ch.toNat 69) with
      | true =>
        obtain ⟨b1, b2⟩ := vj_andB_iff.1 hB
        rw [Nat.ble_eq] at b1 b2
        rw [if_pos ⟨b1, b2⟩]
        change Int.negSucc (ch.toNat - 65) :: w5K cs =
          (-((ch.toNat - 65 + 1 : Nat) : Int)) :: w5K cs
        rfl
      | false =>
        have h2 : ¬ (65 ≤ ch.toNat ∧ ch.toNat ≤ 69) := by
          rintro ⟨b1, b2⟩
          rw [← Nat.ble_eq] at b1 b2
          rw [b1, b2] at hB
          exact absurd hB (by decide)
        rw [if_neg h2]

theorem w5K_toList (s : String) : w5K s.toList = CFSG.Sporadic.J4.QT2A.w5 s := by
  rw [w5K_eq]
  rfl

@[expose] noncomputable def vjElt (u k : Nat → J) (p : Nat × Nat) : J :=
  eta u 11 p.1 * ((CFSG.J4Tree.Native.pcSeqT p.2).map k).prod

@[expose] noncomputable def facProd (g5 gE : Nat → J) (fs : List (String × List Int)) : J :=
  (fs.map fun f => wordProd g5 (CFSG.Sporadic.J4.QT2A.w5 f.1) * wordProd gE f.2).prod

structure TabsOK (T : Tabs) (g5 gE u k f : Nat → J) : Prop where
  consts : ∃ pad t0 t1 t2 t3 t4 t5 t6 : Nat, Consts T.c T.rm T.one pad t0 t1 t2 t3 t4 t5 t6
  l5 : ∀ i, VjRep (getN T.one T.l5 i) (g5 i)
  l5i : ∀ i, VjRep (getN T.one T.l5i i) (g5 i)⁻¹
  ge : ∀ i, VjRep (getN T.one T.ge i) (gE i)
  gei : ∀ i, VjRep (getN T.one T.gei i) (gE i)⁻¹
  us_len : T.us.length = 11
  us : ∀ i < 11, VjRep (T.us.getD i 0) (u i)
  km_len : T.km.length = 4
  km : ∀ i, VjRep (getN T.one T.km i) (k i)
  km' : ∀ i < 4, VjRep (T.km.getD i 0) (k i)
  fm_len : T.fm.length = 10
  fm : ∀ j < 10, VjRep (T.fm.getD j 0) (f j)

variable {T : Tabs} {g5 gE u k f : Nat → J}

theorem getD_map_lt {β : Type} {F : β → Nat} {L : List β} {d : β} {i : Nat} (hi : i < L.length) :
    (L.map F).getD i 0 = F (L.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem vjRep_coords (hT : TabsOK T g5 gE u k f) (L : List (Nat × Nat)) :
    ∀ i < (L.map (coordK T)).length,
      VjRep ((L.map (coordK T)).getD i 0) (vjElt u k (L.getD i (0, 0))) := by
  intro i hi
  obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
  rw [List.length_map] at hi
  rw [getD_map_lt hi]
  exact vjRep_coordK hK hT.us_len hT.us hT.km _

theorem vjRep_eltFrom (hT : TabsOK T g5 gE u k f) : ∀ (fs : List (String × List Int)) {a : Nat}
    {x : J}, VjRep a x → VjRep (eltFrom T fs a) (x * facProd g5 gE fs)
  | [], a, x, h => by
    change VjRep a (x * facProd g5 gE [])
    simpa [facProd] using h
  | fc :: fs, a, x, h => by
    obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
    change VjRep (eltFrom T fs (wordFrom T.c T.rm T.one T.ge T.gei fc.2
      (wordFrom T.c T.rm T.one T.l5 T.l5i (w5K fc.1.toList) a))) _
    have h1 := vjRep_wordFrom hK hT.l5 hT.l5i (w5K fc.1.toList) h
    rw [w5K_toList] at h1
    rw [w5K_toList]
    have h2 := vjRep_wordFrom hK hT.ge hT.gei fc.2 h1
    have h3 := vjRep_eltFrom hT fs h2
    have e : facProd g5 gE (fc :: fs) = wordProd g5 (CFSG.Sporadic.J4.QT2A.w5 fc.1) *
        wordProd gE fc.2 * facProd g5 gE fs := by
      simp only [facProd, List.map_cons, List.prod_cons]
    rw [e, ← mul_assoc, ← mul_assoc]
    exact h3

theorem vjRep_eltK (hT : TabsOK T g5 gE u k f) (fs : List (String × List Int)) :
    VjRep (eltK T fs) (facProd g5 gE fs) := by
  obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
  have := vjRep_eltFrom hT fs (vjRep_one hK)
  rwa [one_mul] at this

theorem normEq_group (hT : TabsOK T g5 gE u k f) {Vs : List Nat} {v : Nat → J}
    (hV : ∀ i < Vs.length, VjRep (Vs.getD i 0) (v i)) {X x m : Nat} {sx vx : J}
    (hX : VjRep X sx) (hx : VjRep x vx) (h : normEq T Vs X x m = true) :
    sx * vx = eta v Vs.length m * sx := by
  obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
  exact vjRep_eq_of_eq (vjRep_mul hK hX hx) (vjRep_mul hK (vjRep_maskK hK hV m) hX)
    (Nat.eq_of_beq_eq_true h)

theorem npB_group (hT : TabsOK T g5 gE u k f) {d : CFSG.J4Tree.VerdictJ.NPData}
    (h : npB T d = true) :
    (∀ p ∈ CFSG.J4Tree.Native.treeWv d.node, p.2 < 1024) ∧ (∀ p ∈ d.V, p.2 < 1024) ∧
      (CFSG.J4Tree.Native.treeWv d.node).length = d.V.length ∧
      (∀ i < d.V.length, vjElt u k ((CFSG.J4Tree.Native.treeWv d.node).getD i (0, 0)) *
        facProd g5 gE d.g = facProd g5 gE d.g * vjElt u k (d.V.getD i (0, 0))) ∧
      (∀ s < 11, ∀ i < d.V.length, (∀ p ∈ d.V, p.2 = 0) ∨
        u s * vjElt u k (d.V.getD i (0, 0)) = eta (fun l => vjElt u k (d.V.getD l (0, 0)))
          d.V.length (d.masks.getD (s * d.V.length + i) 0) * u s) ∧
      ∀ s < 4, ∀ i < d.V.length,
        k s * vjElt u k (d.V.getD i (0, 0)) = eta (fun l => vjElt u k (d.V.getD l (0, 0)))
          d.V.length ((d.masks.drop (11 * d.V.length)).getD (s * d.V.length + i) 0) * k s := by
  obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
  obtain ⟨hW, hV, hlen, hc, hu, hk⟩ := npB_spec h
  have hG := vjRep_eltK hT d.g
  have hWs := vjRep_coords hT (CFSG.J4Tree.Native.treeWv d.node)
  have hVs := vjRep_coords hT d.V
  have hVl : (d.V.map (coordK T)).length = d.V.length := List.length_map _
  refine ⟨hW, hV, hlen, fun i hi => ?_, fun s hs i hi => ?_, fun s hs i hi => ?_⟩
  · exact vjRep_eq_of_eq (vjRep_mul hK (hWs i (by rw [List.length_map]; omega)) hG)
      (vjRep_mul hK hG (hVs i (by rw [hVl]; exact hi))) (hc i hi)
  · rcases hu s (by rw [hT.us_len]; exact hs) i hi with he | he
    · exact Or.inl he
    · right
      have := normEq_group hT hVs (hT.us s hs) (hVs i (by rw [hVl]; exact hi)) he
      rwa [hVl] at this
  · have he := hk s (by rw [hT.km_len]; exact hs) i hi
    rw [hT.us_len] at he
    have := normEq_group hT hVs (hT.km' s hs) (hVs i (by rw [hVl]; exact hi)) he
    rwa [hVl] at this

theorem fB_group (hT : TabsOK T g5 gE u k f) {d : CFSG.J4Tree.VerdictJ.FData}
    (h : fB T d = true) :
    (∀ p ∈ CFSG.J4Tree.Native.treeWv d.node, p.2 < 1024) ∧ ∀ j < 10,
      facProd g5 gE d.d * f j = eta (fun l => vjElt u k ((CFSG.J4Tree.Native.treeWv d.node).getD l
        (0, 0))) (CFSG.J4Tree.Native.treeWv d.node).length (d.masks.getD j 0) *
          facProd g5 gE d.d := by
  obtain ⟨hW, _, hf⟩ := fB_spec h
  have hWs := vjRep_coords hT (CFSG.J4Tree.Native.treeWv d.node)
  refine ⟨hW, fun j hj => ?_⟩
  have := normEq_group hT hWs (vjRep_eltK hT d.d) (hT.fm j hj) (hf j (by rw [hT.fm_len]; exact hj))
  rwa [List.length_map] at this

theorem conjB_group (hT : TabsOK T g5 gE u k f) {src : List (Nat × Nat)}
    {d : CFSG.J4Tree.M4.ConjD} (h : conjB T src d = true) :
    (∀ p ∈ src, p.2 < 1024) ∧ (∀ p ∈ d.tgt, p.2 < 1024) ∧
      (∀ i < src.length, wordProd gE d.word * vjElt u k (src.getD i (0, 0)) =
        eta (fun l => vjElt u k (d.tgt.getD l (0, 0))) d.tgt.length (d.fwd.getD i 0) *
          wordProd gE d.word) ∧
      ∀ j < d.tgt.length, vjElt u k (d.tgt.getD j (0, 0)) * wordProd gE d.word =
        wordProd gE d.word * eta (fun l => vjElt u k (src.getD l (0, 0))) src.length
          (d.bwd.getD j 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, hK⟩ := hT.consts
  obtain ⟨hs, ht, _, _, hfw, hbw⟩ := conjB_spec h
  have hG := vjRep_wordJ hK hT.ge hT.gei d.word
  have hSs := vjRep_coords hT src
  have hTs := vjRep_coords hT d.tgt
  refine ⟨hs, ht, fun i hi => ?_, fun j hj => ?_⟩
  · have := normEq_group hT hTs hG (hSs i (by rw [List.length_map]; exact hi)) (hfw i hi)
    rwa [List.length_map] at this
  · have hm := vjRep_maskK hK hSs (d.bwd.getD j 0)
    rw [List.length_map] at hm
    exact vjRep_eq_of_eq (vjRep_mul hK (hTs j (by rw [List.length_map]; exact hj)) hG)
      (vjRep_mul hK hG hm) (hbw j hj)

end CFSG.KC.J4NPV

end
