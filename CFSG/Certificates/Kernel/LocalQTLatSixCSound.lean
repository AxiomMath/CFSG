module

public import CFSG.Certificates.Kernel.LocalQTContainsCSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheckDefs

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.A5.G3

variable {n : ℕ}

theorem commK_code (hn : n ≤ 32) (G : List (Perm (Fin n))) : ∀ l : List CommWord,
    commK n (G.map P.code) l = P.code (commProd G l)
  | [] => P.code_one
  | q :: l => by
    change P.mul n (P.mul n (P.mul n (P.mul n (CFSG.KC.LQT.W.evalWK n (G.map P.code) q.1)
      (CFSG.KC.LQT.W.evalWK n (G.map P.code) q.2.1)) (CFSG.KC.LQT.W.evalWK n (G.map P.code) q.2.2.1))
      (CFSG.KC.LQT.W.evalWK n (G.map P.code) q.2.2.2)) (commK n (G.map P.code) l) = _
    rw [commK_code hn G l, LK.evalWK_code hn, LK.evalWK_code hn, LK.evalWK_code hn,
      LK.evalWK_code hn, P.code_mul hn, P.code_mul hn, P.code_mul hn, P.code_mul hn]
    rfl

theorem enc_commProd (G : List (Perm (Fin n))) : ∀ l : List CommWord,
    RN.enc (commProd G l) = commProd (G.map RN.enc) l
  | [] => RN.enc_one
  | q :: l => by
    simp only [commProd, RN.enc_mul, enc_evalW (rawIsEnc n), enc_commProd G l]

@[expose] noncomputable def perfGo (n : ℕ) (G0 : List ℕ) : List ℕ → List (List CommWord) → Bool :=
  fun G => List.rec (motive := fun _ => List (List CommWord) → Bool) (fun _ => true)
    (fun g _ ih P => List.rec (motive := fun _ => Bool) true
      (fun p P' _ => CFSG.KC.Ord.andB (Nat.beq (commK n G0 p) g) (ih P')) P) G

theorem perfGo_sound (G0 : List ℕ) : ∀ (G : List ℕ) (Q : List (List CommWord)),
    perfGo n G0 G Q = true → ∀ q ∈ G.zip Q, commK n G0 q.2 = q.1
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | g :: G, p :: Q, h => by
    change CFSG.KC.Ord.andB (Nat.beq (commK n G0 p) g) (perfGo n G0 G Q) = true at h
    rw [P.andB_iff, P.beq_iff] at h
    intro q hq
    rw [List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact h.1
    · exact perfGo_sound G0 G Q h.2 q hq

theorem enc_mul_eq_one (hn : n ≤ 32) (G : List (Perm (Fin n))) (u v : List ℕ)
    (h : Nat.beq (P.mul n (CFSG.KC.LQT.W.evalWK n (G.map P.code) u)
      (CFSG.KC.LQT.W.evalWK n (G.map P.code) v)) (P.one n) = true) :
    evalW (G.map RN.enc) u * evalW (G.map RN.enc) v = 1 := by
  rw [P.beq_iff, LK.evalWK_code hn, LK.evalWK_code hn, P.code_mul hn, P.code_one,
    P.code_eq_iff hn] at h
  rw [← enc_evalW (rawIsEnc n), ← enc_evalW (rawIsEnc n), ← RN.enc_mul, h, RN.enc_one]

theorem perf_sound (hn : n ≤ 32) (G : List (Perm (Fin n))) (Q : List (List CommWord))
    (h : perfK n (G.map P.code) Q = true) : perfOK (RN.enc : Perm (Fin n) → RN n) G Q = true := by
  change CFSG.KC.Ord.andB _ (CFSG.KC.Ord.andB (perfGo n (G.map P.code) (G.map P.code) Q) _) =
    true at h
  rw [P.andB_iff, P.andB_iff, P.beq_iff, LK.lenA_eq, LK.lenA_eq, List.length_map,
    allA_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold perfOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨h1, fun p hp => ?_⟩, fun l hl q hq => ?_⟩
  · have hz : (P.code p.1, p.2) ∈ (G.map P.code).zip Q := by
      rw [List.zip_map_left, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have := perfGo_sound _ _ _ h2 _ hz
    dsimp only at this
    rw [commK_code hn, P.code_eq_iff hn] at this
    rw [← enc_commProd, this]
  · have := h3 l hl
    rw [allA_eq_true] at this
    have hq' := P.andB_iff.1 (this q hq)
    exact ⟨enc_mul_eq_one hn G _ _ hq'.1, enc_mul_eq_one hn G _ _ hq'.2⟩

theorem noSix_of (hn : n ≤ 32) {C : List Lvl} {F : ℕ} {S : SetM} (G : List (Perm (Fin n))) (d : ℕ)
    (hR : RepM rnc n C F S (bfsSet (G.map RN.enc) d)) (h : noSixK n S = true) :
    noSixCheck (bfsSet (G.map RN.enc) d) = true := by
  unfold noSixK at h
  rw [repM_allL hR] at h
  unfold noSixCheck
  rw [toList_all_iff]
  intro x hx
  obtain ⟨σ, -, rfl⟩ := bfsSet_sound (rawIsEnc n) G d x hx
  have hσ := h _ hx
  simp only [P.letB_eq, rnc_enc, P.code_mul hn, P.notB_iff, P.andB_iff, P.beq_iff, P.code_one,
    P.code_eq_iff hn] at hσ
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hh
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← RN.enc_mul, ← RN.enc_one,
    RN.enc_inj.eq_iff] at hh
  have e6 : σ * σ * σ * σ * σ * σ = σ * σ * σ * (σ * σ * σ) := by simp only [mul_assoc]
  apply hσ
  refine ⟨?_, hh.1.2, hh.2⟩
  rw [← e6]
  exact hh.1.1

theorem adataC_sound (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (A : AData n) (d : ℕ)
    (h : adataC n C (chainF C) d (A.gens.map P.code, A.perf) = true) : A.check d = true := by
  unfold adataC at h
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.beq_iff] at h
  obtain ⟨hc, hs, hp, hx⟩ := h
  have hb : (bfsM n C (chainF C) (A.gens.map P.code) d).ok = true := (P.andB_iff.1 hc).1
  have hR := repN hn hok hI A.gens d hb
  have hcl : closedH (A.gens.map RN.enc) (bfsSet (A.gens.map RN.enc) d) = true := by
    have := closedM_iff (idxInjN hn hok hI (chainF C)) (rnc_mul hn) rnc_one (A.gens.map RN.enc)
      hR hb
    rw [map_rnc_enc] at this
    exact this.1 hc
  unfold AData.check
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hcl, (repM_size hR).symm.trans hs⟩, perf_sound hn A.gens A.perf hp⟩,
    noSix_of hn A.gens d hR hx⟩

theorem latSix_sound (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (ms : List Mem)
    (c : LatCert (Perm (Fin n))) (ds : List (AData n))
    (h : latSixC n C c.depth (c.tGens.map P.code) (c.lat.map (List.map P.code)) ms c.sizes
      (ds.map fun A => (A.gens.map P.code, A.perf)) = true) : latSixCheck c ds = true := by
  unfold latSixC at h
  rw [P.andB_iff, P.andB_iff, P.andB_iff, allA_eq_true, P.allN_iff, LK.lenA_eq] at h
  obtain ⟨h0, hok, hds, hall⟩ := h
  have hms := memsOK_iff h0
  have hlen : ms.length = (c.tGens :: c.lat).length := by
    have := congrArg List.length hms
    simpa using this
  unfold latSixCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun A hA => adataC_sound hn hok hI A c.depth (hds _ (List.mem_map_of_mem hA)),
    fun j hj => ?_⟩
  rw [List.mem_range] at hj
  have hj' := hall j (by omega)
  rw [P.orB_iff, P.notB_iff, P.beq_iff, LK.getO_eq, getK_getD'] at hj'
  rw [Bool.or_eq_true]
  rcases hj' with e | e
  · left
    rw [bne_iff_ne]
    exact e
  · right
    cases hp : (membersX n C (chainF C) c.depth ms)[j]? with
    | none =>
      rw [hp] at e
      exact absurd e Bool.false_ne_true
    | some p =>
      rw [hp] at e
      obtain ⟨L, hL, hp2, hp1⟩ := memAt hms j hp
      obtain ⟨hc, hA⟩ := P.andB_iff.1 e
      rw [hp2] at hc hA
      have hR := mem_rel hn hok hI hp1 hc
      rw [LK.anyA_iff] at hA
      obtain ⟨A', hA', hAm⟩ := hA
      obtain ⟨A, hAd, rfl⟩ := List.mem_map.1 hA'
      rw [List.any_eq_true]
      refine ⟨A, hAd, ?_⟩
      dsimp only at hAm
      rw [P.allL_map] at hAm
      have hgd : (c.tGens :: c.lat).getD j [] = L := by
        rw [List.getD_eq_getElem?_getD, hL]
        rfl
      rw [List.all_eq_true, hgd]
      exact fun g hg => Std.HashSet.contains_iff_mem.2 ((hR.2.1 g).1 (hAm g hg))

theorem tleCC_sound (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true)
    (MW : List (List (List ℕ))) (c : LatCert (Perm (Fin n)))
    (h : tleCC n C c.depth (c.mGens.map P.code) MW (c.tGens.map P.code) = true) :
    c.tleOK RN.enc = true := by
  unfold tleCC at h
  rw [P.andB_iff, P.andB_iff] at h
  obtain ⟨hok, hM, h6⟩ := h
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  obtain ⟨hMin, -, -⟩ := grpM_spec hn hok hI c.mGens MW c.depth hM
  unfold tleC at h6
  rw [P.allL_map] at h6
  unfold LatCert.tleOK
  rw [List.all_eq_true]
  exact fun g hg => Std.HashSet.contains_iff_mem.2 ((hMin g).1 ((inC_iff hn hC g).1 (h6 g hg)))

end CFSG.KC.LQT.CM

end
