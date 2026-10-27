module

public import Certificates.Data.Kernel.LocalQT.CoreR
public import Certificates.Data.Kernel.LocalQT.M24L
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
import CFSG.Certificates.Kernel.LocalQTM24Snd.Core
import CFSG.Certificates.Kernel.LocalQTM24Snd.X0
import CFSG.Certificates.Kernel.LocalQTM24Snd.Img
import CFSG.Certificates.Kernel.LocalQTM24Snd.Iset
import CFSG.Certificates.Kernel.LocalQTM24Snd.Sub
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.KC.LQT.W CFSG.KC.LQT.L

theorem coreR_sound {n : ℕ} (gs : List (Perm (Fin n))) {G : List ℕ} (hG : gs.map codeP = G)
    (c : ECert) (kOrd : ℕ) (C : List Lvl) (W : List (List (List ℕ)))
    (hE : eK n (c.eW.map (evalWK n G)) = true) (hC : chainOK n C = true)
    (hI : CFSG.KC.LQT.L.chainInj n C = true)
    (hgc : grpC n C (chainF C) (c.nW.map (evalWK n G)) W c.depth = true)
    (hL : chainF C = c.nOrd)
    (hN : normK n (c.eW.map (evalWK n G)) (c.nW.map (evalWK n G)) = true)
    (hO : orbN n G (c.eW.map (evalWK n G)) c.rT c.nOrd kOrd = true) :
    c.coreCheckT (gs.map RN.enc) kOrd = true := by
  exact CFSG.KC.LQT.M24Snd.coreR_snd gs hG c kOrd C W hE hC hI hgc hL hN hO

end CFSG.KC.LQT.Syl

namespace CFSG.KC.LQT.M24

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.KC.LQT.W

theorem evalWK_codeP {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) (w : List ℕ) :
    evalWK n (gs.map codeP) w = codeP (evalW gs w) := by
  induction w with
  | nil => exact CFSG.KC.LQT.P.code_one
  | cons i w ih =>
    change CFSG.KC.LQT.P.mul n (genAt n (gs.map codeP) i) (evalWK n (gs.map codeP) w) = _
    rw [genAt_map, ih]
    exact CFSG.KC.LQT.P.code_mul hn _ _

theorem codeP_inj {n : ℕ} (hn : n ≤ 32) : Function.Injective (codeP : Perm (Fin n) → ℕ) :=
  fun _ _ h => CFSG.KC.LQT.P.code_inj hn h

theorem x0_sound {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) (xW : List ℕ)
    (h : x0K n (gs.map codeP) xW = true) :
    (xPow (evalW (gs.map RN.enc) xW) 5 == 1 && evalW (gs.map RN.enc) xW != 1) = true := by
  exact CFSG.KC.LQT.M24Snd.x0_snd hn gs xW h

theorem sub_sound {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) (pW : List (List ℕ))
    (d size : ℕ) (h : subK n (gs.map codeP) pW d size = true)
    (hb : size * pW.length ≤ 131072) :
    subgroupCheck (gs.map RN.enc) pW d size = true := by
  exact CFSG.KC.LQT.M24Snd.sub_snd hn gs pW d size h hb

theorem iset_sound {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) (g0 g1 g2 g3 : Perm (Fin n))
    (pW : List (List ℕ)) (d r : ℕ) (xW : List ℕ) (c1 c2 c3 c4 c5 : ECert) (Els : List (List ℕ))
    (S : List ℕ) (chs hss : List (List ℕ))
    (hes : allZ [c1.eW, c2.eW, c3.eW, c4.eW, c5.eW] Els (esK n (gs.map codeP)) = true)
    (hpre : isetPre n (gs.map codeP) pW d S = true) (hin : isetIn S chs.flatten = true)
    (hlen : chs.length = hss.length)
    (hch : ∀ j < chs.length, isetChunk n (codeP g0) (codeP g1) (codeP g2) (codeP g3) S r
      (evalWK n (gs.map codeP) xW) Els chs.flatten (chs.getD j []) (hss.getD j []) = true) :
    conjClosed (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3) (conjBfs (RN.enc g0) (RN.enc g1)
        (RN.enc g2) (RN.enc g3) (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r) = true ∧
      (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)).all (fun x => (conjBfs (RN.enc g0)
        (RN.enc g1) (RN.enc g2) (RN.enc g3)
        (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r).contains x) = true ∧
      (conjBfs (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3)
        (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r).toList.all
        (yCheck (evalW (gs.map RN.enc) xW) (c1.Es (gs.map RN.enc)) (c2.Es (gs.map RN.enc))
          (c3.Es (gs.map RN.enc)) (c4.Es (gs.map RN.enc)) (c5.Es (gs.map RN.enc))) = true := by
  exact CFSG.KC.LQT.M24Snd.iset_snd hn gs g0 g1 g2 g3 pW d r xW c1 c2 c3 c4 c5 Els S chs hss hes hpre
    hin hlen hch

section Conj

variable {G : Type*} [Group G]

@[expose] def conjHom (E N : Subgroup G) (h : N ≤ Subgroup.normalizer (E : Set G)) :
    N →* Perm E where
  toFun x :=
    { toFun := fun e => ⟨x * e * x⁻¹, (Subgroup.mem_normalizer_iff.1 (h x.2) e).1 e.2⟩
      invFun := fun e => ⟨x⁻¹ * e * x, by
        have := (Subgroup.mem_normalizer_iff.1 (h (N.inv_mem x.2)) e).1 e.2
        simpa using this⟩
      left_inv := fun e => Subtype.ext (by simp [mul_assoc])
      right_inv := fun e => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun e => Subtype.ext (by simp)
  map_mul' x y := Equiv.ext fun e => Subtype.ext (by simp [Perm.mul_apply, mul_assoc])

theorem conjHom_apply (E N : Subgroup G) (h : N ≤ Subgroup.normalizer (E : Set G)) (x : N)
    (e : E) : ((conjHom E N h x e : E) : G) = x * e * x⁻¹ := rfl

theorem mem_of_card_range [Finite G] (E N : Subgroup G) (h : N ≤ Subgroup.normalizer (E : Set G))
    (hEN : E ≤ N) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : Nat.card (conjHom E N h).range * Nat.card E = Nat.card N) (x : G) (hx : x ∈ N)
    (hc : ∀ e ∈ E, x * e = e * x) : x ∈ E := by
  set K := (conjHom E N h).ker with hK
  have h1 : Nat.card N = Nat.card (N ⧸ K) * Nat.card K :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have h2 : Nat.card (N ⧸ K) = Nat.card (conjHom E N h).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (conjHom E N h)).toEquiv
  have hpos : 0 < Nat.card (conjHom E N h).range := Nat.card_pos
  have hKE : Nat.card K = Nat.card E := by
    rw [h2, ← hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hle : E.subgroupOf N ≤ K := by
    intro y hy
    rw [hK, MonoidHom.mem_ker]
    refine Equiv.ext fun e => Subtype.ext ?_
    rw [conjHom_apply]
    have := hcomm y (Subgroup.mem_subgroupOf.1 hy) e e.2
    change (y : G) * e * (y : G)⁻¹ = e
    rw [this]
    group
  have hEq : E.subgroupOf N = K := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hKE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]
  have hxK : (⟨x, hx⟩ : N) ∈ K := by
    rw [hK, MonoidHom.mem_ker]
    refine Equiv.ext fun e => Subtype.ext ?_
    rw [conjHom_apply]
    change x * e * x⁻¹ = e
    rw [hc e e.2]
    group
  rw [← hEq] at hxK
  exact Subgroup.mem_subgroupOf.1 hxK

end Conj

theorem imgD_sound {n : ℕ} (hn : n ≤ 32) (eG nG : List (Perm (Fin n)))
    (hle : Subgroup.closure {g | g ∈ nG} ≤
      Subgroup.normalizer ((Subgroup.closure {g | g ∈ eG} : Subgroup (Perm (Fin n))) : Set _))
    (C : List CFSG.KC.LQT.L.Lvl) (W : List (List (List ℕ))) (d m : ℕ)
    (hE : CFSG.KC.LQT.Syl.eK n (eG.map codeP) = true)
    (h : imgCK n (eG.map codeP) (nG.map codeP) C W d m = true) :
    Nat.card (conjHom _ _ hle).range = m := by
  exact CFSG.KC.LQT.M24Snd.imgD_snd hn eG nG hle (conjHom _ _ hle)
    (fun x e => conjHom_apply _ _ hle x e) C W d m hE h

theorem imgV_sound {n : ℕ} (hn : n ≤ 32) (eG nG : List (Perm (Fin n)))
    (hle : Subgroup.closure {g | g ∈ nG} ≤
      Subgroup.normalizer ((Subgroup.closure {g | g ∈ eG} : Subgroup (Perm (Fin n))) : Set _))
    (r : ℕ) (ω : Perm (Fin n)) (hω : ω ∈ Subgroup.closure {g | g ∈ nG})
    (hE : CFSG.KC.LQT.Syl.eK n (eG.map codeP) = true)
    (h : imgVK n (eG.map codeP) (nG.map codeP) (codeP ω) r = true) :
    conjHom _ _ hle ⟨ω, hω⟩ ≠ 1 ∧ conjHom _ _ hle ⟨ω, hω⟩ ^ 3 = 1 ∧
      ∀ x, conjHom _ _ hle x * conjHom _ _ hle ⟨ω, hω⟩ = conjHom _ _ hle ⟨ω, hω⟩ * conjHom _ _ hle x ∨
        conjHom _ _ hle x * conjHom _ _ hle ⟨ω, hω⟩ =
          conjHom _ _ hle ⟨ω, hω⟩ ^ 2 * conjHom _ _ hle x := by
  exact CFSG.KC.LQT.M24Snd.imgV_snd hn eG nG hle (conjHom _ _ hle)
    (fun x e => conjHom_apply _ _ hle x e) r ω hω hE h

section SoundP

variable {n : ℕ}

structure SoundP (c : ECert) (gl : List (Perm (Fin n))) : Prop where
  comm : ∀ x ∈ Subgroup.closure {g | g ∈ c.eW.map (evalW gl)},
    ∀ y ∈ Subgroup.closure {g | g ∈ c.eW.map (evalW gl)}, x * y = y * x
  cardE : Nat.card (Subgroup.closure {g | g ∈ c.eW.map (evalW gl)}) = 16
  memE : ∀ x, x ∈ Subgroup.closure {g | g ∈ c.eW.map (evalW gl)} ↔
    RN.enc x ∈ c.Es (gl.map RN.enc)
  surjE : ∀ ε ∈ c.Es (gl.map RN.enc), ∃ x ∈ Subgroup.closure {g | g ∈ c.eW.map (evalW gl)},
    RN.enc x = ε
  memN : ∀ x, x ∈ Subgroup.closure {g | g ∈ c.nW.map (evalW gl)} ↔
    RN.enc x ∈ c.Ns (gl.map RN.enc)
  surjN : ∀ ε ∈ c.Ns (gl.map RN.enc), ∃ x ∈ Subgroup.closure {g | g ∈ c.nW.map (evalW gl)},
    RN.enc x = ε
  cardN : Nat.card (Subgroup.closure {g | g ∈ c.nW.map (evalW gl)}) = c.nOrd
  le : Subgroup.closure {g | g ∈ c.nW.map (evalW gl)} ≤
    Subgroup.normalizer ((Subgroup.closure {g | g ∈ c.eW.map (evalW gl)} :
      Subgroup (Perm (Fin n))) : Set (Perm (Fin n)))

theorem soundP (c : ECert) (gl : List (Perm (Fin n)))
    (hc : (c.eCheck (gl.map RN.enc) && c.nCheck (gl.map RN.enc)) = true) : SoundP c gl := by
  classical
  have h := rawIsEnc n
  set gR : List (RN n) := gl.map RN.enc with hgR
  set eG : List (Perm (Fin n)) := c.eW.map (evalW gl) with heG
  set nG : List (Perm (Fin n)) := c.nW.map (evalW gl) with hnG
  have heR : c.eR gR = eG.map RN.enc := by
    simp only [ECert.eR, heG, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [Function.comp, enc_evalW h, hgR]
  have hnR : c.nR gR = nG.map RN.enc := by
    simp only [ECert.nR, hnG, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [Function.comp, enc_evalW h, hgR]
  have hEs : c.Es gR = bfsSet (eG.map RN.enc) 16 := by simp only [ECert.Es, heR]
  have hNs : c.Ns gR = bfsSet (nG.map RN.enc) c.depth := by simp only [ECert.Ns, hnR]
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hE, hN⟩ := hc
  simp only [ECert.eCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hE
  obtain ⟨⟨⟨hEcl, hEsize⟩, -⟩, hEcomm⟩ := hE
  have hcl1 : closedH (eG.map RN.enc) (bfsSet (eG.map RN.enc) 16) = true := by
    rw [← hEs, ← heR]; exact hEcl
  have hmemE := mem_closure_iff_H h eG 16 hcl1
  have hcardE := card_closure_of_closedH h eG 16 hcl1
  have hEcommG : ∀ g ∈ eG, ∀ g' ∈ eG, g * g' = g' * g := by
    intro g hg g' hg'
    have := hEcomm (RN.enc g) (by rw [heR]; exact List.mem_map_of_mem hg) (RN.enc g')
      (by rw [heR]; exact List.mem_map_of_mem hg')
    apply h.inj
    rw [h.map_mul, h.map_mul]
    exact this
  simp only [ECert.nCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true] at hN
  obtain ⟨⟨hNcl, hNsize⟩, hNnorm⟩ := hN
  have hclN : closedH (nG.map RN.enc) (bfsSet (nG.map RN.enc) c.depth) = true := by
    rw [← hNs, ← hnR]; exact hNcl
  have hmemN := mem_closure_iff_H h nG c.depth hclN
  have hcardN := card_closure_of_closedH h nG c.depth hclN
  have hnormgen : ∀ g ∈ nG, g ∈ Subgroup.normalizer
      ((Subgroup.closure {g | g ∈ eG} : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
    intro g hg
    have hconj : ∀ e ∈ eG, g * e * g⁻¹ ∈ Subgroup.closure {g | g ∈ eG} := by
      intro e he
      obtain ⟨e', he', hee'⟩ := hNnorm (RN.enc g) (by rw [hnR]; exact List.mem_map_of_mem hg)
        (RN.enc e) (by rw [heR]; exact List.mem_map_of_mem he)
      rw [hEs] at he'
      obtain ⟨x, hxE, hx⟩ := bfsSet_sound h eG 16 e' (Std.HashSet.mem_toList.1 he')
      have h1 : g * e = x * g := by
        apply h.inj
        rw [h.map_mul, h.map_mul, hx]
        exact hee'
      have h2 : g * e * g⁻¹ = x := by rw [h1]; group
      rw [h2]
      exact hxE
    apply mem_normalizer_of_conj_le
    have hle : Subgroup.closure {g | g ∈ eG} ≤
        (Subgroup.closure {g | g ∈ eG}).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro e he
      exact hconj e he
    intro x hx
    exact hle hx
  exact
    { comm := closure_comm (S := {g | g ∈ eG}) hEcommG
      cardE := by rw [hcardE, ← hEs]; exact hEsize
      memE := fun x => by rw [hmemE x, hEs]
      surjE := fun ε hε => by
        rw [hEs] at hε
        exact bfsSet_sound h eG 16 ε hε
      memN := fun x => by rw [hmemN x, hNs]
      surjN := fun ε hε => by
        rw [hNs] at hε
        exact bfsSet_sound h nG c.depth ε hε
      cardN := by rw [hcardN, ← hNs]; exact hNsize
      le := by
        rw [Subgroup.closure_le]
        exact fun g hg => hnormgen g hg }

theorem evalW_mem {G : Type*} [Group G] (gs : List G) (w : List ℕ) :
    evalW gs w ∈ Subgroup.closure {g | g ∈ gs} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    rcases Nat.lt_or_ge i gs.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact Subgroup.subset_closure (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]
      exact Subgroup.one_mem _

theorem map_codeP_evalW (hn : n ≤ 32) (gl : List (Perm (Fin n))) (ws : List (List ℕ)) :
    (ws.map (evalW gl)).map codeP = ws.map (evalWK n (gl.map codeP)) := by
  rw [List.map_map]
  exact List.map_congr_left fun u _ => (evalWK_codeP hn gl u).symm

theorem mem_of_wordEq (hn : n ≤ 32) (gl : List (Perm (Fin n))) (nW : List (List ℕ))
    (w v : List ℕ) (h : wordEqK n (gl.map codeP) nW w v = true) :
    evalW gl v ∈ Subgroup.closure {g | g ∈ nW.map (evalW gl)} := by
  have e1 : nW.map (evalWK n (gl.map codeP)) = (nW.map (evalW gl)).map codeP :=
    (map_codeP_evalW hn gl nW).symm
  have h' : evalWK n (nW.map (evalWK n (gl.map codeP))) w = evalWK n (gl.map codeP) v :=
    Nat.eq_of_beq_eq_true h
  rw [e1, evalWK_codeP hn, evalWK_codeP hn] at h'
  rw [← codeP_inj hn h']
  exact evalW_mem _ w

theorem allZ_spec {α : Type} {f : α → List ℕ → Bool} :
    ∀ {l : List α} {m : List (List ℕ)}, allZ l m f = true → ∀ x ∈ l, ∃ y ∈ m, f x y = true
  | [], _, _ => fun _ hx => absurd hx List.not_mem_nil
  | _ :: _, [], h => absurd h (by simp [allZ])
  | x :: l, y :: m, h => by
    have e : allZ (x :: l) (y :: m) f = CFSG.KC.Ord.andB (f x y) (allZ l m f) := rfl
    rw [e, CFSG.KC.LQT.L.andB_eq, Bool.and_eq_true] at h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨y, List.mem_cons_self, h.1⟩
    · obtain ⟨y', hy', hf⟩ := allZ_spec h.2 z hz
      exact ⟨y', List.mem_cons_of_mem _ hy', hf⟩

theorem hypD_of_card (c : ECert) (gl : List (Perm (Fin n))) (hs : SoundP c gl)
    (hEN : Subgroup.closure {g | g ∈ c.eW.map (evalW gl)} ≤
      Subgroup.closure {g | g ∈ c.nW.map (evalW gl)})
    (hcard : Nat.card (conjHom _ _ hs.le).range * 16 = c.nOrd)
    (h3840 : c.nOrd % 3840 = 0) : c.hypDCheck (gl.map RN.enc) = true := by
  have h := rawIsEnc n
  simp only [ECert.hypDCheck, ECert.selfCentCheck, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true]
  refine ⟨fun x hx => ?_, h3840⟩
  obtain ⟨σ, hσ, rfl⟩ := hs.surjN x (Std.HashSet.mem_toList.1 hx)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Std.HashSet.contains_iff_mem]
  by_cases hc : ∀ e ∈ Subgroup.closure {g | g ∈ c.eW.map (evalW gl)}, σ * e = e * σ
  · right
    refine (hs.memE σ).1 (mem_of_card_range _ _ hs.le hEN hs.comm ?_ σ hσ hc)
    rw [hs.cardE, hcard, hs.cardN]
  · left
    push Not at hc
    obtain ⟨e, he, hne⟩ := hc
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have := hall (RN.enc e) (Std.HashSet.mem_toList.2 ((hs.memE e).1 he))
    rw [beq_iff_eq, ← h.map_mul, ← h.map_mul] at this
    exact hne (h.inj this)

theorem hypV_of_img (c : ECert) (gl : List (Perm (Fin n))) (hs : SoundP c gl) (omW : List ℕ)
    (hω : evalW gl omW ∈ Subgroup.closure {g | g ∈ c.nW.map (evalW gl)})
    (hv : conjHom _ _ hs.le ⟨_, hω⟩ ≠ 1 ∧ conjHom _ _ hs.le ⟨_, hω⟩ ^ 3 = 1 ∧
      ∀ x, conjHom _ _ hs.le x * conjHom _ _ hs.le ⟨_, hω⟩ =
          conjHom _ _ hs.le ⟨_, hω⟩ * conjHom _ _ hs.le x ∨
        conjHom _ _ hs.le x * conjHom _ _ hs.le ⟨_, hω⟩ =
          conjHom _ _ hs.le ⟨_, hω⟩ ^ 2 * conjHom _ _ hs.le x) :
    c.hypVCheck (gl.map RN.enc) omW = true := by
  have h := rawIsEnc n
  set E := Subgroup.closure {g | g ∈ c.eW.map (evalW gl)} with hEdef
  set N := Subgroup.closure {g | g ∈ c.nW.map (evalW gl)} with hNdef
  set ψ := conjHom E N hs.le with hψ
  set ω := evalW gl omW with hωdef
  have hencω : evalW (gl.map RN.enc) omW = RN.enc ω := (enc_evalW h gl omW).symm
  obtain ⟨hne, h3, hall⟩ := hv
  have act : ∀ (x : N) (e : E), ((ψ x e : E) : Perm (Fin n)) = x * e * x⁻¹ := fun x e => rfl
  have actE : ∀ (x : N) (e : Perm (Fin n)) (he : e ∈ E), x * e * (x : Perm (Fin n))⁻¹ ∈ E :=
    fun x e he => (ψ x ⟨e, he⟩).2
  simp only [ECert.hypVCheck, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Std.HashSet.contains_iff_mem, hencω]
  refine ⟨⟨⟨(hs.memN ω).1 hω, ?_⟩, ?_⟩, ?_⟩
  ·
    obtain ⟨e, he⟩ : ∃ e : E, ψ ⟨ω, hω⟩ e ≠ e := by
      by_contra hc
      push Not at hc
      exact hne (Equiv.ext hc)
    refine ⟨RN.enc e, Std.HashSet.mem_toList.2 ((hs.memE e).1 e.2), fun heq => he ?_⟩
    refine Subtype.ext ?_
    rw [act]
    have : ω * e = e * ω := h.inj (by rw [h.map_mul, h.map_mul]; exact heq)
    change ω * e * ω⁻¹ = e
    rw [this]
    group
  ·
    intro v hv
    obtain ⟨e, he, rfl⟩ := hs.surjE v (Std.HashSet.mem_toList.1 hv)
    have h3e := congrArg (fun p : Perm E => ((p ⟨e, he⟩ : E) : Perm (Fin n))) h3
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.coe_one, id] at h3e
    change ω * (ω * (ω * e * ω⁻¹) * ω⁻¹) * ω⁻¹ = e at h3e
    simp only [← h.map_mul]
    congr 1
    calc ω * ω * ω * e = (ω * (ω * (ω * e * ω⁻¹) * ω⁻¹) * ω⁻¹) * (ω * ω * ω) := by group
      _ = e * (ω * ω * ω) := by rw [h3e]
  ·
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := hs.surjN x (Std.HashSet.mem_toList.1 hx)
    have key : ∀ y : N, ψ (⟨σ, hσ⟩ * ⟨ω, hω⟩) = ψ y →
        ∀ v ∈ (c.Es (gl.map RN.enc)).toList, ∃ p ∈ (c.Es (gl.map RN.enc)).toList.map
          (fun e => (e * (RN.enc σ * RN.enc ω), e * RN.enc (y : Perm (Fin n)))),
          RN.enc σ * RN.enc ω * v = p.1 ∧ RN.enc (y : Perm (Fin n)) * v = p.2 := by
      intro y hy v hv
      obtain ⟨e, he, rfl⟩ := hs.surjE v (Std.HashSet.mem_toList.1 hv)
      set e' := σ * ω * e * (σ * ω)⁻¹ with he'
      have he'E : e' ∈ E := actE (⟨σ, hσ⟩ * ⟨ω, hω⟩) e he
      have hy' : (y : Perm (Fin n)) * e * (y : Perm (Fin n))⁻¹ = e' := by
        have := congrArg (fun p : Perm E => ((p ⟨e, he⟩ : E) : Perm (Fin n))) hy
        simp only [act] at this
        rw [he']
        exact this.symm
      refine ⟨(RN.enc e' * (RN.enc σ * RN.enc ω), RN.enc e' * RN.enc (y : Perm (Fin n))),
        List.mem_map.2 ⟨RN.enc e', Std.HashSet.mem_toList.2 ((hs.memE e').1 he'E), rfl⟩, ?_, ?_⟩
      · simp only [← h.map_mul]
        congr 1
        rw [he']
        group
      · simp only [← h.map_mul]
        congr 1
        rw [← hy']
        group
    rcases hall ⟨σ, hσ⟩ with h1 | h2
    · left
      have hy : ψ (⟨σ, hσ⟩ * ⟨ω, hω⟩) = ψ (⟨ω, hω⟩ * ⟨σ, hσ⟩) := by
        rw [map_mul, map_mul, h1]
      have := key _ hy
      simpa only [Subgroup.coe_mul, h.map_mul] using this
    · right
      have hy : ψ (⟨σ, hσ⟩ * ⟨ω, hω⟩) = ψ (⟨ω, hω⟩ * ⟨ω, hω⟩ * ⟨σ, hσ⟩) := by
        rw [map_mul, map_mul, map_mul, h2, pow_two]
      have := key _ hy
      simpa only [Subgroup.coe_mul, h.map_mul] using this

end SoundP

end CFSG.KC.LQT.M24

end
