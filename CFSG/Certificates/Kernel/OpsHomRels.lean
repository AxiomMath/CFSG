module

public import CFSG.Certificates.Kernel.OpsHom
public import CFSG.RankThree.PartOne.KS.HNFiveInputs
public import CFSG.RankThree.PartOne.KS.ScalFiveDefs

public section

namespace CFSG.KC.OpsHom.Hom

open CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.KC.OpsHom

variable {M V M' V' : Type} {O : Ops M V} {O' : Ops M' V'} (H : Hom O O')

theorem UU_fst (x : M' × M') : (H.UU x).1 = H.U x.1 := rfl

theorem eqPow_U {a b : M'} (ha : H.P a) (hb : H.P b) (e : ℕ) :
    O.eq (H.U a) (O.pow (H.U b) e) = O'.eq a (O'.pow b e) := by
  rw [(H.pow_U e hb).1, H.eq ha (H.pow_U e hb).2]

section HN

open CFSG.RankThree.PartOne.KS.HNFive

theorem hnPowOK_U {a : M'} (ha : H.P a) (e : ℕ) : powOK O (H.U a) e = powOK O' a e := by
  unfold powOK
  rw [(H.pow_U e ha).1, H.one.1, H.eq (H.pow_U e ha).2 H.one.2]

theorem hnCommOK_U {a b : M'} (ha : H.P a) (hb : H.P b) :
    commOK O (H.U a) (H.U b) = commOK O' a b := by
  unfold commOK
  rw [(H.mul ha hb).1, (H.mul hb ha).1, H.eq (H.mul ha hb).2 (H.mul hb ha).2]

theorem hnNeOne_U {a : M'} (ha : H.P a) (t : ℕ) : neOne O (H.U a) t = neOne O' a t := by
  unfold neOne
  obtain ⟨u1, uq⟩ := H.unit t
  obtain ⟨v1, vq⟩ := H.vmul uq ha
  rw [u1, v1, H.vne vq uq]

theorem hnPBcomm_U {a b : M' × M'} (ha : H.PP a) (hb : H.PP b) :
    pBcomm O (H.UU a) (H.UU b) = H.U (pBcomm O' a b) ∧ H.P (pBcomm O' a b) := by
  obtain ⟨m1, p1⟩ := H.mul ha.2 hb.2
  obtain ⟨m2, p2⟩ := H.mul ha.1 hb.1
  obtain ⟨m3, p3⟩ := H.mul p1 p2
  change O.mul (O.mul (H.U a.2) (H.U b.2)) (O.mul (H.U a.1) (H.U b.1)) = _ ∧ _
  rw [m1, m2, m3]
  exact ⟨rfl, p3⟩

theorem hnPConj_U {g a : M' × M'} (hg : H.PP g) (ha : H.PP a) :
    pConj O (H.UU g) (H.UU a) = H.U (pConj O' g a) ∧ H.P (pConj O' g a) := by
  obtain ⟨m1, p1⟩ := H.mul hg.2 ha.1
  obtain ⟨m2, p2⟩ := H.mul p1 hg.1
  change O.mul (O.mul (H.U g.2) (H.U a.1)) (H.U g.1) = _ ∧ _
  rw [m1, m2]
  exact ⟨rfl, p2⟩

theorem hnProdPow_U {qs : Fin 4 → M'} {z : M'} (hq : ∀ j, H.P (qs j)) (hz : H.P z)
    (a : Fin 4 → ℕ) (c : ℕ) :
    prodPow O (fun j => H.U (qs j)) (H.U z) a c = H.U (prodPow O' qs z a c) ∧
      H.P (prodPow O' qs z a c) := by
  obtain ⟨e0, p0⟩ := H.pow_U (a 0) (hq 0)
  obtain ⟨e1, p1⟩ := H.pow_U (a 1) (hq 1)
  obtain ⟨e2, p2⟩ := H.pow_U (a 2) (hq 2)
  obtain ⟨e3, p3⟩ := H.pow_U (a 3) (hq 3)
  obtain ⟨ez, pz⟩ := H.pow_U c hz
  obtain ⟨o1, po⟩ := H.one
  obtain ⟨m3, q3⟩ := H.mul p3 po
  obtain ⟨m2, q2⟩ := H.mul p2 q3
  obtain ⟨m1, q1⟩ := H.mul p1 q2
  obtain ⟨m0, q0⟩ := H.mul p0 q1
  obtain ⟨mz, qz⟩ := H.mul q0 pz
  unfold prodPow
  beta_reduce
  rw [e0, e1, e2, e3, ez, o1, m3, m2, m1, m0, mz]
  exact ⟨rfl, qz⟩

theorem hnRelsOK_U [Inhabited M] [Inhabited M'] {R : Array (M' × M')}
    (hR : ∀ r < R.size, H.PP R[r]!) (hZ : iZ < R.size) (hX : iX < R.size)
    (hQ : ∀ j, iQ j < R.size) (hRr : ∀ j, iR j < R.size) :
    relsOK O (R.map H.UU) = relsOK O' R := by
  have gQ : ∀ j, (R.map H.UU)[iQ j]! = H.UU R[iQ j]! := fun j => get_map R H.UU (hQ j)
  have gR : ∀ j, (R.map H.UU)[iR j]! = H.UU R[iR j]! := fun j => get_map R H.UU (hRr j)
  have pZ := (hR _ hZ).1
  have pX := hR _ hX
  have pQ : ∀ j, H.PP R[iQ j]! := fun j => hR _ (hQ j)
  have pR : ∀ j, H.PP R[iR j]! := fun j => hR _ (hRr j)
  have pq : ∀ j, H.P (R[iQ j]!).1 := fun j => (pQ j).1
  have powZ := H.hnPowOK_U pZ
  have neZ := H.hnNeOne_U pZ
  have powX := H.hnPowOK_U pX.1
  have commXZ := H.hnCommOK_U pX.1 pZ
  have powQ : ∀ j e, powOK O (H.U R[iQ j]!.1) e = powOK O' R[iQ j]!.1 e :=
    fun j => H.hnPowOK_U (pQ j).1
  have commQZ : ∀ j, commOK O (H.U R[iQ j]!.1) (H.U R[iZ]!.1) = commOK O' R[iQ j]!.1 R[iZ]!.1 :=
    fun j => H.hnCommOK_U (pQ j).1 pZ
  have commRZ : ∀ j, commOK O (H.U R[iR j]!.1) (H.U R[iZ]!.1) = commOK O' R[iR j]!.1 R[iZ]!.1 :=
    fun j => H.hnCommOK_U (pR j).1 pZ
  have bcQ : ∀ i j, O.eq (pBcomm O (H.UU R[iQ i]!) (H.UU R[iQ j]!)) (O.pow (H.U R[iZ]!.1) (exM i j)) =
      O'.eq (pBcomm O' R[iQ i]! R[iQ j]!) (O'.pow R[iZ]!.1 (exM i j)) := fun i j => by
    obtain ⟨e1, p1⟩ := H.hnPBcomm_U (pQ i) (pQ j)
    rw [e1, H.eqPow_U p1 pZ]
  have conjX : ∀ i, O.eq (pConj O (H.UU R[iX]!) (H.UU R[iQ i]!))
      (prodPow O (fun j => H.U R[iQ j]!.1) (H.U R[iZ]!.1) (exX i) (cx i)) =
      O'.eq (pConj O' R[iX]! R[iQ i]!) (prodPow O' (fun j => R[iQ j]!.1) R[iZ]!.1 (exX i) (cx i)) :=
    fun i => by
      obtain ⟨e1, p1⟩ := H.hnPConj_U pX (pQ i)
      obtain ⟨e2, p2⟩ := H.hnProdPow_U pq pZ (exX i) (cx i)
      rw [e1, e2, H.eq p1 p2]
  have conjR : ∀ j i, O.eq (pConj O (H.UU R[iR j]!) (H.UU R[iQ i]!))
      (prodPow O (fun l => H.U R[iQ l]!.1) (H.U R[iZ]!.1) (exR j i) (cr j i)) =
      O'.eq (pConj O' R[iR j]! R[iQ i]!)
        (prodPow O' (fun l => R[iQ l]!.1) R[iZ]!.1 (exR j i) (cr j i)) :=
    fun j i => by
      obtain ⟨e1, p1⟩ := H.hnPConj_U (pR j) (pQ i)
      obtain ⟨e2, p2⟩ := H.hnProdPow_U pq pZ (exR j i) (cr j i)
      rw [e1, e2, H.eq p1 p2]
  unfold relsOK
  simp only [get_map R H.UU hZ, get_map R H.UU hX, gQ, gR]
  simp only [UU_fst, powZ, neZ, powX, commXZ, powQ, commQZ, commRZ, bcQ, conjX, conjR]

end HN

section Scal

open CFSG.RankThree.PartOne.KS.ScalFive

theorem scPowOK_U {a : M'} (ha : H.P a) (e : ℕ) : powOK O (H.U a) e = powOK O' a e := by
  unfold powOK
  rw [(H.pow_U e ha).1, H.one.1, H.eq (H.pow_U e ha).2 H.one.2]

theorem scCommOK_U {a b : M'} (ha : H.P a) (hb : H.P b) :
    commOK O (H.U a) (H.U b) = commOK O' a b := by
  unfold commOK
  rw [(H.mul ha hb).1, (H.mul hb ha).1, H.eq (H.mul ha hb).2 (H.mul hb ha).2]

theorem scNeOne_U {a : M'} (ha : H.P a) (t : ℕ) : neOne O (H.U a) t = neOne O' a t := by
  unfold neOne
  obtain ⟨u1, uq⟩ := H.unit t
  obtain ⟨v1, vq⟩ := H.vmul uq ha
  rw [u1, v1, H.vne vq uq]

theorem scPBcomm_U {a b : M' × M'} (ha : H.PP a) (hb : H.PP b) :
    pBcomm O (H.UU a) (H.UU b) = H.U (pBcomm O' a b) ∧ H.P (pBcomm O' a b) := by
  obtain ⟨m1, p1⟩ := H.mul ha.2 hb.2
  obtain ⟨m2, p2⟩ := H.mul ha.1 hb.1
  obtain ⟨m3, p3⟩ := H.mul p1 p2
  change O.mul (O.mul (H.U a.2) (H.U b.2)) (O.mul (H.U a.1) (H.U b.1)) = _ ∧ _
  rw [m1, m2, m3]
  exact ⟨rfl, p3⟩

theorem scPConj_U {g a : M' × M'} (hg : H.PP g) (ha : H.PP a) :
    pConj O (H.UU g) (H.UU a) = H.U (pConj O' g a) ∧ H.P (pConj O' g a) := by
  obtain ⟨m1, p1⟩ := H.mul hg.2 ha.1
  obtain ⟨m2, p2⟩ := H.mul p1 hg.1
  change O.mul (O.mul (H.U g.2) (H.U a.1)) (H.U g.1) = _ ∧ _
  rw [m1, m2]
  exact ⟨rfl, p2⟩

theorem scFoldr_U {n : ℕ} {qs : Fin n → M'} (hq : ∀ j, H.P (qs j)) (a : Fin n → ℕ) :
    ∀ l : List (Fin n), l.foldr (fun j acc => O.mul (O.pow (H.U (qs j)) (a j)) acc) O.one =
      H.U (l.foldr (fun j acc => O'.mul (O'.pow (qs j) (a j)) acc) O'.one) ∧
      H.P (l.foldr (fun j acc => O'.mul (O'.pow (qs j) (a j)) acc) O'.one)
  | [] => H.one
  | j :: l => by
    obtain ⟨e1, p1⟩ := scFoldr_U hq a l
    obtain ⟨e2, p2⟩ := H.pow_U (a j) (hq j)
    rw [List.foldr_cons, List.foldr_cons, e1, e2]
    exact H.mul p2 p1

theorem scProdPow_U {n : ℕ} {qs : Fin n → M'} {z : M'} (hq : ∀ j, H.P (qs j)) (hz : H.P z)
    (a : Fin n → ℕ) (c : ℕ) :
    prodPow O (fun j => H.U (qs j)) (H.U z) a c = H.U (prodPow O' qs z a c) ∧
      H.P (prodPow O' qs z a c) := by
  obtain ⟨e1, p1⟩ := H.scFoldr_U hq a (List.finRange n)
  obtain ⟨ez, pz⟩ := H.pow_U c hz
  unfold prodPow
  beta_reduce
  rw [e1, ez]
  exact H.mul p1 pz

theorem scRelsOK_U [Inhabited M] [Inhabited M'] {n : ℕ} (D : Data n) {R : Array (M' × M')}
    (hR : ∀ r < R.size, H.PP R[r]!) (hZ : D.iZ < R.size) (hS : D.iS < R.size)
    (hT : D.iT < R.size) (hQ : ∀ j, D.iQ j < R.size) :
    relsOK O D (R.map H.UU) = relsOK O' D R := by
  have gQ : ∀ j, (R.map H.UU)[D.iQ j]! = H.UU R[D.iQ j]! := fun j => get_map R H.UU (hQ j)
  have pZ := (hR _ hZ).1
  have pS := hR _ hS
  have pT := hR _ hT
  have pQ : ∀ j, H.PP R[D.iQ j]! := fun j => hR _ (hQ j)
  have pq : ∀ j, H.P (R[D.iQ j]!).1 := fun j => (pQ j).1
  have powZ := H.scPowOK_U pZ
  have neZ := H.scNeOne_U pZ
  have powT := H.scPowOK_U pT.1
  have powQ : ∀ j e, powOK O (H.U R[D.iQ j]!.1) e = powOK O' R[D.iQ j]!.1 e :=
    fun j => H.scPowOK_U (pQ j).1
  have commQZ : ∀ j, commOK O (H.U R[D.iQ j]!.1) (H.U R[D.iZ]!.1) =
      commOK O' R[D.iQ j]!.1 R[D.iZ]!.1 :=
    fun j => H.scCommOK_U (pQ j).1 pZ
  have bcQ : ∀ i j, O.eq (pBcomm O (H.UU R[D.iQ i]!) (H.UU R[D.iQ j]!))
      (O.pow (H.U R[D.iZ]!.1) (D.exM i j)) =
      O'.eq (pBcomm O' R[D.iQ i]! R[D.iQ j]!) (O'.pow R[D.iZ]!.1 (D.exM i j)) := fun i j => by
    obtain ⟨e1, p1⟩ := H.scPBcomm_U (pQ i) (pQ j)
    rw [e1, H.eqPow_U p1 pZ]
  have conjS : ∀ i, O.eq (pConj O (H.UU R[D.iS]!) (H.UU R[D.iQ i]!))
      (prodPow O (fun j => H.U R[D.iQ j]!.1) (H.U R[D.iZ]!.1) (D.exS i) (D.cs i)) =
      O'.eq (pConj O' R[D.iS]! R[D.iQ i]!)
        (prodPow O' (fun j => R[D.iQ j]!.1) R[D.iZ]!.1 (D.exS i) (D.cs i)) :=
    fun i => by
      obtain ⟨e1, p1⟩ := H.scPConj_U pS (pQ i)
      obtain ⟨e2, p2⟩ := H.scProdPow_U pq pZ (D.exS i) (D.cs i)
      rw [e1, e2, H.eq p1 p2]
  have conjT : ∀ i, O.eq (pConj O (H.UU R[D.iT]!) (H.UU R[D.iQ i]!))
      (O.mul (O.pow (H.U R[D.iQ i]!.1) D.rT) (O.pow (H.U R[D.iZ]!.1) (D.ct i))) =
      O'.eq (pConj O' R[D.iT]! R[D.iQ i]!)
        (O'.mul (O'.pow R[D.iQ i]!.1 D.rT) (O'.pow R[D.iZ]!.1 (D.ct i))) :=
    fun i => by
      obtain ⟨e1, p1⟩ := H.scPConj_U pT (pQ i)
      obtain ⟨e2, p2⟩ := H.pow_U D.rT (pq i)
      obtain ⟨e3, p3⟩ := H.pow_U (D.ct i) pZ
      obtain ⟨e4, p4⟩ := H.mul p2 p3
      rw [e1, e2, e3, e4, H.eq p1 p4]
  have pow5 : O.eq (O.pow (H.U R[D.iS]!.1) 5)
      (prodPow O (fun j => H.U R[D.iQ j]!.1) (H.U R[D.iZ]!.1) D.e5 D.c5) =
      O'.eq (O'.pow R[D.iS]!.1 5) (prodPow O' (fun j => R[D.iQ j]!.1) R[D.iZ]!.1 D.e5 D.c5) := by
    obtain ⟨e1, p1⟩ := H.pow_U 5 pS.1
    obtain ⟨e2, p2⟩ := H.scProdPow_U pq pZ D.e5 D.c5
    rw [e1, e2, H.eq p1 p2]
  have bcTS : O.eq (pBcomm O (H.UU R[D.iT]!) (H.UU R[D.iS]!))
      (prodPow O (fun j => H.U R[D.iQ j]!.1) (H.U R[D.iZ]!.1) D.eTS D.cTS) =
      O'.eq (pBcomm O' R[D.iT]! R[D.iS]!)
        (prodPow O' (fun j => R[D.iQ j]!.1) R[D.iZ]!.1 D.eTS D.cTS) := by
    obtain ⟨e1, p1⟩ := H.scPBcomm_U pT pS
    obtain ⟨e2, p2⟩ := H.scProdPow_U pq pZ D.eTS D.cTS
    rw [e1, e2, H.eq p1 p2]
  unfold relsOK
  simp only [get_map R H.UU hZ, get_map R H.UU hS, get_map R H.UU hT, gQ]
  simp only [UU_fst, powZ, neZ, powT, powQ, commQZ, bcQ, conjS, conjT, pow5, bcTS]

end Scal

end CFSG.KC.OpsHom.Hom

end
