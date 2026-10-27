module

public import Certificates.Data.Kernel.LocalQT.CovT
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCheck

import CFSG.Certificates.Kernel.LocalQTCovTTri

namespace CFSG.KC.LQT.Cov.PfT

open CFSG.KC.LQT.Cov CFSG.KC.LQT.Cov.T CFSG.KC.LQT.Cov.Parse CFSG.KC.LQT.Cov.Eqns
open CFSG.KC.LQT.Cov.Perm CFSG.KC.LQT.Cov.TEqns CFSG.KC.LQT.Syl CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Sporadic.Schreier.Tits

private theorem flags_spec : ∀ Q : List (Bool × Nat),
    (List.rec (motive := fun _ => Bool) true (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q : Bool) =
      true → ∀ q ∈ Q, q.1 = true
  | [], _, q, hq => absurd hq List.not_mem_nil
  | q :: Q, h, q', hq' => by
    change CFSG.KC.Ord.andB q.1 (List.rec (motive := fun _ => Bool) true
      (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q) = true at h
    rw [CFSG.KC.LQT.Cov.Parse.andB_eq', Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact h.1
    · exact flags_spec Q h.2 q' hq'

private noncomputable def xT (S SI : Nat → Nat) (D : CT) : List Nat :=
  List.map (CFSG.KS.Raw.wordK 1755 11 (CFSG.KS.mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI) D.xw

private theorem xT_get (D : CT) (S SI : Nat → Nat) {i : Fin 2}
    (hi : (i : Nat) < D.xw.length) :
    CFSG.KC.LQT.Syl.getK (xT S SI D) i 0 =
      CFSG.KS.Raw.wordK 1755 11 (CFSG.KS.mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI
        (D.xw[(i : Nat)]) := by
  rw [xT, CFSG.KC.LQT.Cov.Parse.getK_getD, List.getD_eq_getElem?_getD]
  simp [List.getElem?_map, List.getElem?_eq_getElem hi]

private theorem xT_unpack (D : CT) (S SI : Nat → Nat)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (CFSG.KS.mask 11) (1755 * 11) (S j) (SI j) = true)
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true)
    (hlettersAll : CFSG.KC.LQT.T2.allT D.xw (CFSG.KS.Raw.lettersK 13) = true)
    (hxw2 : D.xw.length = 2) :
    ∀ i : Fin 2,
      CFSG.KS.Raw.unpack 1755 11 (CFSG.KC.LQT.Syl.getK (xT S SI D) i 0) = (ofCT D).xa i := by
  intro i
  rw [xT_get D S SI (by rw [hxw2]; exact i.2)]
  rw [← wordArr_eq_unpack hS hperm hsz
    ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hlettersAll _
      (List.getElem_mem (by rw [hxw2]; exact i.2)))]
  fin_cases i <;> simp [CovData.xa, CovData.xwOf, ofCT, hxw2]

private theorem xT_range (D : CT) (S SI : Nat → Nat)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (CFSG.KS.mask 11) (1755 * 11) (S j) (SI j) = true)
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true)
    (hlettersAll : CFSG.KC.LQT.T2.allT D.xw (CFSG.KS.Raw.lettersK 13) = true)
    (hxw2 : D.xw.length = 2) :
    ∀ i : Fin 2, ∀ j < 1755,
      CFSG.KC.Enum.pg 11 (CFSG.KS.mask 11) (CFSG.KC.LQT.Syl.getK (xT S SI D) i 0) j < 1755 := by
  intro i j hj
  rw [xT_get D S SI (by rw [hxw2]; exact i.2)]
  exact wordK_range hS hperm hsz
    ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hlettersAll _
      (List.getElem_mem (by rw [hxw2]; exact i.2))) j hj

private theorem words_zero_nil {D : CT}
    (h0 : CFSG.KC.LQT.Syl.lenK (CFSG.KC.LQT.Syl.getK D.words 0 [1]) = 0) :
    D.words.getD 0 [] = [] := by
  have hlen : (D.words.getD 0 [1]).length = 0 := by
    rw [← CFSG.KC.LQT.Cov.Parse.getK_getD]
    exact CFSG.KC.LQT.Cov.Parse.lenK_length .. ▸ h0
  rw [List.getD_eq_getElem?_getD] at hlen ⊢
  cases h : D.words[0]? with
  | none => simp [h] at hlen
  | some w => simpa [h] using hlen

private theorem E_props {D : CT} {X P : List Nat} {E' : Nat → Nat}
    (hwords : D.words.length = D.nV)
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 2)
    (hpar : parOK (rowsG D.words) D.nV P = true)
    (hE0 : E' 0 = pidn 1755 11)
    (hrec : ∀ v, 0 < v → v < D.nV →
      E' v = pcomp 1755 11 (mask 11) (E' (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG D.words) v [])) 2) 0))
    (hX : ∀ i : Fin 2, CFSG.KS.Raw.unpack 1755 11 (getK X i 0) = (ofCT D).xa i)
    (hXlt : ∀ i : Fin 2, ∀ j < 1755,
      CFSG.KC.Enum.pg 11 (mask 11) (getK X i 0) j < 1755)
    (hz : D.words.getD 0 [] = []) :
    (∀ v < D.nV,
        CFSG.KS.Raw.unpack 1755 11 (E' v) = elaOf (ofCT D).xa (D.words.getD v [])) ∧
      (∀ v < D.nV, E' v >>> (1755 * 11) = 0) ∧
      (∀ v < D.nV, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E' v) j < 1755) := by
  have hparSpec : ∀ v, 0 < v → v < D.nV → getK P (v - 1) 0 < v :=
    fun v hv hlt => (parOK_spec hpar).2 v hv hlt |>.1
  refine ⟨buildE_unpack D X (ofCT D).xa P E' hwords hletters hpar hE0 hrec hX hXlt hz,
    buildE_canon hE0 hrec, ?_⟩
  exact buildE_range hE0 hrec hXlt hparSpec

private noncomputable def kT (D : CT) (P : List Nat) (S SI : Nat → Nat) : List Nat → Bool :=
  fun E =>
    goodT D (rowsG D.words) (rowsG D.tgt) (rowsG D.back) (rowsG P) 1755 11 (xT S SI D)
        (rowsG E) &&
      (CFSG.KC.LQT.T2.distinctS E &&
        CFSG.KC.LQT.T2.allT D.blocks (blkT 1755 11 13 S SI D (rowsG E)))

private theorem build_data (D : CT) (P : List Nat) (S SI : Nat → Nat)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true)
    (hxw2 : D.xw.length = 2)
    (hwords : D.words.length = D.nV)
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 2)
    (hlettersAll : CFSG.KC.LQT.T2.allT D.xw (CFSG.KS.Raw.lettersK 13) = true)
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (CFSG.KS.mask 11) (1755 * 11) (S j) (SI j) = true)
    (hpar : parOK (rowsG D.words) D.nV P = true)
    (hbuild : buildE 1755 11 (xT S SI D) (rowsG D.words) P (kT D P S SI) = true) :
    ∃ E : Nat → Nat, 0 < D.nV ∧
      (∀ v, 0 < v → v < D.nV →
        E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
          (getK (xT S SI D) (Nat.mod (lastK (getRG (rowsG D.words) v [])) 2) 0)) ∧
      (∀ v < D.nV, CFSG.KS.Raw.unpack 1755 11 (E v) = elaOf (ofCT D).xa (D.words.getD v [])) ∧
      (∀ v < D.nV, E v >>> (1755 * 11) = 0) ∧
      (∀ v < D.nV, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E v) j < 1755) ∧
      (∀ i : Fin 2, CFSG.KS.Raw.unpack 1755 11 (getK (xT S SI D) i 0) = (ofCT D).xa i) ∧
      (∀ i : Fin 2, ∀ j < 1755,
        CFSG.KC.Enum.pg 11 (mask 11) (getK (xT S SI D) i 0) j < 1755) ∧
      goodT D (rowsG D.words) (rowsG D.tgt) (rowsG D.back) (rowsG P) 1755 11 (xT S SI D)
        (rowsG ((List.range D.nV).map E)) = true ∧
      CFSG.KC.LQT.T2.distinctS ((List.range D.nV).map E) = true ∧
      CFSG.KC.LQT.T2.allT D.blocks
        (blkT 1755 11 13 S SI D (rowsG ((List.range D.nV).map E))) = true := by
  obtain ⟨E, hk, hE0, hrec⟩ :=
    buildE_exists D (xT S SI D) P (kT D P S SI) hpar hbuild
  simp only [kT, Bool.and_eq_true] at hk
  obtain ⟨hgoodT, hdist, hblkAll⟩ := hk
  have hgoodT' := hgoodT
  rw [goodT] at hgoodT'
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hgoodT'
  have hnV : 0 < D.nV := Nat.blt_eq.mp hgoodT'.1
  have hz : D.words.getD 0 [] = [] := words_zero_nil (Nat.beq_eq.mp hgoodT'.2.1)
  have hX := xT_unpack D S SI hS hperm hsz hlettersAll hxw2
  have hXlt := xT_range D S SI hS hperm hsz hlettersAll hxw2
  obtain ⟨hEunpack, hEcanon, hElt⟩ := E_props hwords hletters hpar hE0 hrec hX hXlt hz
  exact ⟨E, hnV, hrec, hEunpack, hEcanon, hElt, hX, hXlt, hgoodT, hdist, hblkAll⟩

private theorem good_checks (D : CT) {X : List Nat} (P : List Nat) (S SI : Nat → Nat) (E : Nat → Nat)
    (hwords : D.words.length = D.nV)
    (hxw : D.xw.length = 2)
    (hll : CFSG.KC.LQT.T2.allT D.xw (CFSG.KS.Raw.lettersK 13) = true)
    (hEunpack : ∀ v < D.nV, CFSG.KS.Raw.unpack 1755 11 (E v) = elaOf (ofCT D).xa (D.words.getD v []))
    (hEcanon : ∀ v < D.nV, E v >>> (1755 * 11) = 0)
    (hElt : ∀ v < D.nV, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E v) j < 1755)
    (hX : ∀ i : Fin 2, CFSG.KS.Raw.unpack 1755 11 (getK X i 0) = (ofCT D).xa i)
    (hXlt : ∀ i : Fin 2, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (getK X i 0) j < 1755)
    (hrec : ∀ v, 0 < v → v < D.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG D.words) v [])) 2) 0))
    (hdist : CFSG.KC.LQT.T2.distinctS ((List.range D.nV).map E) = true)
    (hgoodT : goodT D (rowsG D.words) (rowsG D.tgt) (rowsG D.back) (rowsG P) 1755 11 X
      (rowsG ((List.range D.nV).map E)) = true)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (CFSG.KS.mask 11) (1755 * 11) (S j) (SI j) = true)
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true)
    (hblkAll : CFSG.KC.LQT.T2.allT D.blocks
      (blkT 1755 11 13 S SI D (rowsG ((List.range D.nV).map E))) = true) :
    goodCheck (ofCT D) (ofCT D).elaTab = true ∧
      (ofCT D).blocks.all (blkCheck (ofCT D) (ofCT D).elaTab) = true := by
  refine ⟨goodT_sound D E P X hwords hxw hll hEunpack hEcanon hElt hX hXlt hrec hdist hgoodT, ?_⟩
  rw [show (ofCT D).blocks = D.blocks.map (fun b =>
    ({ gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 } : Blk)) from rfl,
    List.all_map]
  apply List.all_eq_true.2
  intro b hb
  exact blkT_sound D E P S SI b hwords hEunpack hElt hS hperm hsz
    ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hblkAll b hb)

private noncomputable def qT (D : CT) : List (Bool × Nat) :=
  eqnsT D (rowsG D.words) (rowsG D.tgt) (rowsG D.back)

private theorem eqns_checks (D : CT) (H : List (List Nat))
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 2)
    (hnV : 0 < D.nV)
    (hlenH : CFSG.KC.LQT.Syl.lenK H = 2 * D.nV)
    (htri : triT (rowsG (List.map Prod.snd (qT D))) H = true)
    (hflagsH : (List.rec (motive := fun _ => Bool) true
      (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) (qT D) : Bool) = true)
    (hformsBound : CFSG.KC.LQT.P.allL (List.map Prod.snd (qT D))
      (fun f => Nat.blt f (Nat.pow 2 (Nat.add (Nat.mul 2 D.nV)
        (Nat.mul 32 (CFSG.KC.LQT.Syl.lenK D.blocks))))) = true) :
    (ofCT D).eqns.all (Eqn.valid (ofCT D)) = true ∧ geFinal (ofCT D) = true := by
  have hflags : ∀ q ∈ qT D, q.1 = true := flags_spec _ hflagsH
  have hvalid : (ofCT D).eqns.all (Eqn.valid (ofCT D)) = true := eqnsT_valid hletters hnV hflags
  have hforms : (qT D).map Prod.snd = (ofCT D).forms := eqnsT_forms hletters
  have hfs : ∀ f ∈ (ofCT D).forms, f < 2 ^ (2 * D.nV + 32 * (ofCT D).blocks.length) := by
    intro f hf
    have hf' : f ∈ (qT D).map Prod.snd := by rwa [hforms]
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf'
    have := (CFSG.KC.LQT.P.allL_iff _ _).1 hformsBound q.2 (List.mem_map_of_mem hq)
    simpa [Nat.blt_eq, CFSG.KC.LQT.Cov.Parse.lenK_length, List.length_map, ofCT] using this
  exact ⟨hvalid, tri_geFinal H hletters hlenH htri hfs⟩

end CFSG.KC.LQT.Cov.PfT

public section

namespace CFSG.KC.LQT.Cov

open CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Sporadic.Schreier.Tits CFSG.KC.LQT.Syl CFSG.KC.LQT.Cov.Parse
open CFSG.KC.LQT.Cov.T CFSG.KC.LQT.Cov.Eqns

theorem covT_sound (cs : List Char) (P : List ℕ) (H : List (List ℕ)) (nV0 : ℕ) (S SI : ℕ → ℕ)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hA : covTA 1755 11 13 S SI cs P nV0 = true) (hB : covTB cs H = true) :
    covCheck (parseData (String.ofList cs)) = true ∧ (parseData (String.ofList cs)).nV = nV0 := by
  rw [covTA] at hA
  cases hp : parseT cs with
  | none =>
    rw [hp] at hA
    exact absurd hA Bool.false_ne_true
  | some D =>
    rw [covTB] at hB
    rw [hp] at hA hB
    simp only [allBs_cons, allBs_nil,
      Bool.and_true, Bool.and_eq_true] at hA
    obtain ⟨hsz, hxwlen, hnv0, hpermAll, hlettersAll, hpar, hbuild⟩ := hA
    have hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (CFSG.KS.mask 11) (1755 * 11) (S j) (SI j) = true :=
      fun j hj => (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 hpermAll j hj
    obtain ⟨hxw2, hwords, hletters, hpd⟩ := parseT_sound hp
    simp only [allBs_cons, allBs_nil,
      Bool.and_true, Bool.and_eq_true] at hB
    obtain ⟨hlenH, htri, hflagsH, hformsBound⟩ := hB
    obtain ⟨E, hnV, hrec, hEunpack, hEcanon, hElt, hX, hXlt, hgoodT, hdist, hblkAll⟩ :=
      CFSG.KC.LQT.Cov.PfT.build_data D P S SI hS hsz hxw2 hwords hletters hlettersAll hperm hpar hbuild
    obtain ⟨hgoodCheck, hblocks⟩ := CFSG.KC.LQT.Cov.PfT.good_checks D P S SI E
      hwords hxw2 hlettersAll hEunpack hEcanon hElt hX hXlt hrec hdist hgoodT hS hperm hsz hblkAll
    obtain ⟨hvalid, hge⟩ :=
      CFSG.KC.LQT.Cov.PfT.eqns_checks D H hletters hnV (Nat.beq_eq.mp hlenH) htri hflagsH hformsBound
    rw [hpd, covCheck]
    refine ⟨?_, Nat.beq_eq.mp hnv0⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨hgoodCheck, hblocks⟩, hvalid⟩, hge⟩

end CFSG.KC.LQT.Cov

end
