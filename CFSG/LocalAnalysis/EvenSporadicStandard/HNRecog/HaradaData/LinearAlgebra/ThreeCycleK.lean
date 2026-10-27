module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs
public import CFSG.Permutation.FinPack
public import CFSG.Permutation.FinPack64
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA.ThreeCycleK

open Equiv
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack (memK allK anyK memK_iff allK_iff anyK_iff)
open CFSG.Permutation.FinPack64

@[expose] def toN (x : V6) : ℕ :=
  (x 0).val + 2 * (x 1).val + 4 * (x 2).val + 8 * (x 3).val + 16 * (x 4).val + 32 * (x 5).val

@[expose] def ofN (n : ℕ) : V6 := fun i => (((n >>> i.val) % 2 : ℕ) : ZMod 2)

set_option maxRecDepth 100000 in
theorem toN_lt : ∀ x : V6, toN x < 64 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ofN_toN : ∀ x : V6, ofN (toN x) = x := by decide +kernel

set_option maxRecDepth 100000 in
theorem toN_ofN : ∀ i : Fin 64, toN (ofN i) = i := by decide +kernel

@[expose] def eV : V6 ≃ Fin 64 where
  toFun x := ⟨toN x, toN_lt x⟩
  invFun i := ofN i
  left_inv := ofN_toN
  right_inv i := Fin.ext (toN_ofN i)

@[expose] def phi (g : Perm V6) : Perm (Fin 64) := (eV.symm.trans g).trans eV

@[expose] def cd (g : Perm V6) : ℕ := pkw 6 (phi g)

theorem phi_mul (g h : Perm V6) : phi (g * h) = phi g * phi h := by
  ext x
  simp [phi, Perm.mul_apply]

theorem cd_mul (g h : Perm V6) : cd (g * h) = mulW 64 (cd g) (cd h) := by
  rw [cd, phi_mul]
  exact pk_mul (le_refl 64) rfl rfl

theorem cd_inj {g h : Perm V6} (e : cd g = cd h) : g = h := by
  have e1 : phi g = phi h := eq_of_pk (le_refl 64) rfl rfl e
  refine Equiv.ext fun v => ?_
  have e2 := congrArg (fun p : Perm (Fin 64) => eV.symm (p (eV v))) e1
  simpa [phi] using e2

@[expose] def cOne : ℕ :=
  39392078757191557952714343944915560488424390381760365930566598193007564623154681709773698286566728461254900444831808
@[expose] def cT1 : ℕ :=
  39392078608077760949174737636133760920570162877966941784564213129907278278669792792884777407432264372898242673516608
@[expose] def cT2 : ℕ :=
  35082482017615286586722996139180489888017973256318439874814141129324063984685717654312563819818376994911148189700480
@[expose] def cT4 : ℕ :=
  39382609432933398148468889077127087905170132657296650309054614975351599747567006594852346779684346851442799191789696
@[expose] def cT5 : ℕ :=
  31282730313894256687466830392733010495230338851538028161297863326767542025054657346193001793227431720080008810131520
@[expose] def cT6 : ℕ :=
  17844037226440065646528493661177180761031248632726268827312409158618775519155788822595788130720433198630643711219840
@[expose] def cT7 : ℕ :=
  29385220040646928311500619475290425927850379972578224426652711507095133854731481464451400897991566809895909899116608
@[expose] def cGA : ℕ :=
  30667224273227655770982844338929853344780017842679018714477442480907762677498984880557850248068722512536354352853120
@[expose] def cGB : ℕ :=
  17738190650644314232269394697467443032621669428474062696586977038975022323475724345792735460190818736742979182664640
@[expose] def cGC : ℕ :=
  29063112709135238462325861035805108307885604766447056482311442577164019820965757474684955521078041131621715536648320

theorem pk_one : pkw 6 (1 : Perm (Fin 64)) = cOne := by decide +kernel

theorem cd_one : cd 1 = cOne := pk_one

theorem cd_t1 : cd (transv (ofN 12)) = cT1 := by decide +kernel
theorem cd_t2 : cd (transv (ofN 7)) = cT2 := by decide +kernel
theorem cd_t4 : cd (transv (ofN 3)) = cT4 := by decide +kernel
theorem cd_t5 : cd (transv (ofN 13)) = cT5 := by decide +kernel
theorem cd_t6 : cd (transv (ofN 35)) = cT6 := by decide +kernel
theorem cd_t7 : cd (transv tv) = cT7 := by decide +kernel

theorem cd_gA : cd (transv (ofN 3) * transv (ofN 13)) = cGA := by
  rw [cd_mul, cd_t4, cd_t5]
  decide +kernel

theorem cd_gB : cd (transv (ofN 13) * transv (ofN 35)) = cGB := by
  rw [cd_mul, cd_t5, cd_t6]
  decide +kernel

theorem cd_gC : cd (transv (ofN 35) * transv tv) = cGC := by
  rw [cd_mul, cd_t6, cd_t7]
  decide +kernel

@[expose] noncomputable def gK (k : Fin 3) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) cGA
    (fun j _ => Nat.rec (motive := fun _ => ℕ) cGB (fun _ _ => cGC) j) k.val

@[expose] noncomputable def evK (w : List (Fin 3)) : ℕ :=
  List.rec (motive := fun _ => ℕ) cOne (fun k _ r => mulW 64 (gK k) r) w

@[expose] def wordsK : List (List (Fin 3)) :=
  [[], [0], [1], [2], [0,0], [0,1], [0,2], [1,0], [1,1], [1,2], [2,0], [2,1], [2,2],
   [0,0,1], [0,0,2], [0,1,1], [0,1,2], [0,2,0], [0,2,1], [0,2,2], [1,0,0], [1,1,0], [1,1,2],
   [1,2,0], [1,2,2], [2,0,0], [2,0,1], [2,1,0], [2,1,1], [2,2,0], [2,2,1],
   [0,0,2,1], [0,0,2,2], [0,1,1,0], [0,2,0,0], [0,2,0,1], [0,2,1,0], [0,2,1,1], [0,2,2,0],
   [1,1,2,0], [1,2,2,0], [1,2,2,1], [2,0,0,1], [2,0,0,2], [2,0,1,1], [2,1,0,0], [2,1,1,0],
   [2,2,0,0], [2,2,1,0],
   [0,0,2,1,0], [0,2,0,0,1], [0,2,0,1,1], [0,2,1,0,0], [0,2,1,1,0], [0,2,2,0,0],
   [1,2,2,0,0], [1,2,2,1,0], [2,0,1,1,0],
   [0,0,2,1,0,0], [0,2,0,1,1,0]]

#kc_repo #kc_decls CFSG.EvenSporadicStandard.HNRecog.HaradaLA.ThreeCycleK "CFSG/LocalAnalysis/EvenSporadicStandard/HNRecog/HaradaData/LinearAlgebra/data/threecyclek_l5.txt" 5875 613260266604100191

theorem wordsK_evK : wordsK.map evK = L5 := by
  have h : (wordsK.map evK == L5) = true := by decide +kernel
  exact beq_iff_eq.mp h

@[expose] noncomputable def chkMul : Bool :=
  allK (fun c => memK (mulW 64 c cGA) L5 && memK (mulW 64 c cGB) L5 && memK (mulW 64 c cGC) L5) L5

@[expose] noncomputable def chkInv : Bool :=
  allK (fun c => anyK (fun d => Nat.beq (mulW 64 c d) cOne) L5) L5

@[expose] noncomputable def nodupK (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t r => Bool.rec (motive := fun _ => Bool) r false (memK a t)) L

@[expose] noncomputable def chkCen : Bool :=
  allK (fun c => Bool.rec (motive := fun _ => Bool) true (Nat.beq c cOne)
    (Nat.beq (mulW 64 c cGA) (mulW 64 cGA c) && Nat.beq (mulW 64 c cGB) (mulW 64 cGB c) &&
      Nat.beq (mulW 64 c cGC) (mulW 64 cGC c))) L5

theorem chkMul_true : chkMul = true := by decide +kernel

theorem chkInv_true : chkInv = true := by decide +kernel

theorem nodupK_L5 : nodupK L5 = true := by decide +kernel

theorem chkCen_true : chkCen = true := by decide +kernel

theorem nodup_of_nodupK {L : List ℕ} (h : nodupK L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a L ih =>
    change Bool.rec (motive := fun _ => Bool) (nodupK L) false (memK a L) = true at h
    cases ha : memK a L
    · rw [ha] at h
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih h⟩
      rw [memK_iff.mpr hm] at ha
      exact Bool.noConfusion ha
    · rw [ha] at h
      exact absurd (h : false = true) Bool.false_ne_true

theorem mul_closed {c : ℕ} (hc : c ∈ L5) (k : Fin 3) : mulW 64 c (gK k) ∈ L5 := by
  have h := allK_iff.mp chkMul_true c hc
  simp only [Bool.and_eq_true, memK_iff] at h
  fin_cases k
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem inv_closed {c : ℕ} (hc : c ∈ L5) : ∃ d ∈ L5, mulW 64 c d = cOne := by
  obtain ⟨d, hd, e⟩ := anyK_iff.mp (allK_iff.mp chkInv_true c hc)
  exact ⟨d, hd, Nat.eq_of_beq_eq_true e⟩

theorem evK_nil : evK [] = cOne := rfl

theorem evK_cons (k : Fin 3) (ks : List (Fin 3)) : evK (k :: ks) = mulW 64 (gK k) (evK ks) :=
  rfl

theorem gen_codes {gen : Fin 3 → Perm V6} (h0 : cd (gen 0) = cGA) (h1 : cd (gen 1) = cGB)
    (h2 : cd (gen 2) = cGC) : ∀ k, cd (gen k) = gK k := by
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem map_cd_of {ev : List (Fin 3) → Perm V6} {gen : Fin 3 → Perm V6} (h0 : ev [] = 1)
    (hs : ∀ k ks, ev (k :: ks) = gen k * ev ks) (hgen : ∀ k, cd (gen k) = gK k)
    {A : List (Perm V6)} (hA : A = wordsK.map ev) : A.map cd = L5 := by
  have h : ∀ w, cd (ev w) = evK w := by
    intro w
    induction w with
    | nil => rw [h0, cd_one, evK_nil]
    | cons k ks ih => rw [hs, cd_mul, hgen, ih, evK_cons]
  have hf : (fun w => cd (ev w)) = evK := funext h
  rw [hA, List.map_map]
  change wordsK.map (fun w => cd (ev w)) = L5
  rw [hf]
  exact wordsK_evK

variable {A : List (Perm V6)}

theorem cd_mem (hA : A.map cd = L5) {g : Perm V6} (hg : g ∈ A) : cd g ∈ L5 := by
  rw [← hA]
  exact List.mem_map.mpr ⟨g, hg, rfl⟩

theorem mem_of_cd (hA : A.map cd = L5) {g : Perm V6} (hg : cd g ∈ L5) : g ∈ A := by
  rw [← hA] at hg
  obtain ⟨h, hh, e⟩ := List.mem_map.mp hg
  rw [← cd_inj e]
  exact hh

theorem mul_mem_of {gen : Fin 3 → Perm V6} (hA : A.map cd = L5) (hgen : ∀ k, cd (gen k) = gK k)
    {g : Perm V6} (hg : g ∈ A) (k : Fin 3) : g * gen k ∈ A := by
  apply mem_of_cd hA
  rw [cd_mul, hgen k]
  exact mul_closed (cd_mem hA hg) k

theorem inv_mem_of (hA : A.map cd = L5) {g : Perm V6} (hg : g ∈ A) : g⁻¹ ∈ A := by
  obtain ⟨d, hd, e⟩ := inv_closed (cd_mem hA hg)
  rw [← hA] at hd
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hd
  have e1 : g * h = 1 := cd_inj (by rw [cd_mul, e, cd_one])
  rw [inv_eq_of_mul_eq_one_right e1]
  exact hh

theorem nodup_of (hA : A.map cd = L5) : A.Nodup := by
  have h : (A.map cd).Nodup := by
    rw [hA]
    exact nodup_of_nodupK nodupK_L5
  exact h.of_map cd

private theorem beq_of_comm {g a : Perm V6} {C : ℕ} (ha : cd a = C) (h : g * a = a * g) :
    Nat.beq (mulW 64 (cd g) C) (mulW 64 C (cd g)) = true := by
  rw [← ha, ← cd_mul, ← cd_mul, h]
  exact Nat.beq_refl _

theorem center_of (hA : A.map cd = L5) {a b c : Perm V6} (ha : cd a = cGA) (hb : cd b = cGB)
    (hc : cd c = cGC) {g : Perm V6} (hg : g ∈ A)
    (h : g * a = a * g ∧ g * b = b * g ∧ g * c = c * g) : g = 1 := by
  have hx := allK_iff.mp chkCen_true (cd g) (cd_mem hA hg)
  beta_reduce at hx
  rw [beq_of_comm ha h.1, beq_of_comm hb h.2.1, beq_of_comm hc h.2.2] at hx
  apply cd_inj
  rw [cd_one]
  exact Nat.eq_of_beq_eq_true hx

@[expose] def cW3 : ℕ :=
  32619847233840974757794010400930919644081142881266567418007168911067533886920688440505336704679703197125061215294080
@[expose] def cUV : ℕ :=
  17834567902181905842283038793388947217127586851598937760832295374876971958196694806515187713562036737951889277986880
@[expose] def cWV : ℕ :=
  30328783798220542047320566442574333607713083610130154170926863853110212657304618319682284640962782855915106281990208

theorem cd_w3 : cd (transv (ofN 12) * transv (ofN 7)) = cW3 := by
  rw [cd_mul, cd_t1, cd_t2]
  decide +kernel

theorem cd_uV : cd (transv (ofN 3) * transv (ofN 13) * (transv (ofN 13) * transv (ofN 35))) =
    cUV := by
  rw [cd_mul, cd_gA, cd_gB]
  decide +kernel

theorem cd_wV : cd (transv (ofN 13) * transv (ofN 35) * (transv (ofN 3) * transv (ofN 13))) =
    cWV := by
  rw [cd_mul, cd_gA, cd_gB]
  decide +kernel

theorem eq_of_cd {g h : Perm V6} {a b : ℕ} (hg : cd g = a) (hh : cd h = b) (e : a = b) : g = h :=
  cd_inj (by rw [hg, hh, e])

theorem ne_of_cd {g h : Perm V6} {a b : ℕ} (hg : cd g = a) (hh : cd h = b)
    (e : Nat.beq a b = false) : g ≠ h := by
  intro gh
  subst gh
  rw [hg] at hh
  rw [hh, Nat.beq_refl] at e
  exact Bool.noConfusion e

theorem comm_of {g h : Perm V6} {a b : ℕ} (hg : cd g = a) (hh : cd h = b)
    (e : mulW 64 a b = mulW 64 b a) : g * h = h * g :=
  cd_inj (by rw [cd_mul, cd_mul, hg, hh, e])

theorem cube_of {g : Perm V6} {a : ℕ} (hg : cd g = a) (e : mulW 64 (mulW 64 a a) a = cOne) :
    g * g * g = 1 :=
  cd_inj (by rw [cd_mul, cd_mul, hg, e, cd_one])

theorem w3_cube_K : mulW 64 (mulW 64 cW3 cW3) cW3 = cOne := by decide +kernel
theorem comm_gA_w3_K : mulW 64 cGA cW3 = mulW 64 cW3 cGA := by decide +kernel
theorem comm_gB_w3_K : mulW 64 cGB cW3 = mulW 64 cW3 cGB := by decide +kernel
theorem comm_gC_w3_K : mulW 64 cGC cW3 = mulW 64 cW3 cGC := by decide +kernel

theorem commid_of {a x y : Perm V6} {A X Y : ℕ} (ha : cd a = A) (hx : cd x = X) (hy : cd y = Y)
    (h : mulW 64 A X = mulW 64 (mulW 64 Y X) A) : a * x * a⁻¹ * x⁻¹ = y := by
  have e : a * x = y * x * a := cd_inj (by rw [cd_mul, cd_mul, cd_mul, ha, hx, hy, h])
  rw [e, mul_inv_cancel_right, mul_inv_cancel_right]

theorem commA_of {a b c : Perm V6} (ha : cd a = cGA) (hb : cd b = cGB) (hc : cd c = cGC) :
    b * (b * c * c * a * a) * b⁻¹ * (b * c * c * a * a)⁻¹ = a :=
  commid_of hb (by rw [cd_mul, cd_mul, cd_mul, cd_mul, ha, hb, hc]) ha (by decide +kernel)

theorem commB_of {a c : Perm V6} {b : Perm V6} (ha : cd a = cGA) (hb : cd b = cGB)
    (hc : cd c = cGC) : a * (a * a * c) * a⁻¹ * (a * a * c)⁻¹ = b :=
  commid_of ha (by rw [cd_mul, cd_mul, ha, hc]) hb (by decide +kernel)

theorem commC_of {a b c : Perm V6} (ha : cd a = cGA) (hb : cd b = cGB) (hc : cd c = cGC) :
    b * (a * c * a) * b⁻¹ * (a * c * a)⁻¹ = c :=
  commid_of hb (by rw [cd_mul, cd_mul, ha, hc]) hc (by decide +kernel)

theorem uV_wV_of {u w : Perm V6} (hu : cd u = cUV) (hw : cd w = cWV) :
    u * u = 1 ∧ w * w = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w := by
  refine ⟨eq_of_cd (by rw [cd_mul, hu]) cd_one ?_, eq_of_cd (by rw [cd_mul, hw]) cd_one ?_,
    comm_of hu hw ?_, ne_of_cd hu cd_one ?_, ne_of_cd hw cd_one ?_, ne_of_cd hu hw ?_⟩ <;>
    decide +kernel

section Klein

variable {G : Type*} [Group G] {u w x y : G}

private theorem klein_rules (hu : u * u = 1) (hw : w * w = 1) (huw : u * w = w * u) :
    (∀ z : G, u * (u * z) = z) ∧ (∀ z : G, w * (w * z) = z) ∧ w * u = u * w ∧
      (∀ z : G, w * (u * z) = u * (w * z)) := by
  refine ⟨fun z => ?_, fun z => ?_, huw.symm, fun z => ?_⟩
  · rw [← mul_assoc, hu, one_mul]
  · rw [← mul_assoc, hw, one_mul]
  · rw [← mul_assoc, ← huw, mul_assoc]

set_option linter.unusedSimpArgs false in
theorem klein_mul (hu : u * u = 1) (hw : w * w = 1) (huw : u * w = w * u)
    (hx : x = 1 ∨ x = u ∨ x = w ∨ x = u * w) (hy : y = 1 ∨ y = u ∨ y = w ∨ y = u * w) :
    x * y = 1 ∨ x * y = u ∨ x * y = w ∨ x * y = u * w := by
  obtain ⟨r1, r2, r3, r4⟩ := klein_rules hu hw huw
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, one_mul, mul_one, hu, hw, r1, r2, r3, r4, eq_self_iff_true, true_or,
      or_true]

theorem klein_inv (hu : u * u = 1) (hw : w * w = 1) (huw : u * w = w * u)
    (hx : x = 1 ∨ x = u ∨ x = w ∨ x = u * w) :
    x⁻¹ = 1 ∨ x⁻¹ = u ∨ x⁻¹ = w ∨ x⁻¹ = u * w := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [inv_one, mul_inv_rev, hui, hwi, huw.symm, true_or, or_true]

end Klein

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA.ThreeCycleK
