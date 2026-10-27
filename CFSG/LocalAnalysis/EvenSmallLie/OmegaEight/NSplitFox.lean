module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitAct
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitModel

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem toVec7_eq (x : ℕ) : toVec 7 x = mk7 (toVec 6 (x % 64)) (bz (x.testBit 6)) := by
  ext j
  by_cases h : (j : ℕ) < 6
  · simp only [mk7, h, dite_true, toVec]
    rw [show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_mod_two_pow]
    simp [h]
  · have : j = 6 := by ext; simp; omega
    subst this
    simp [mk7, toVec]

theorem genCode_lt (ε : Eps) {i v : ℕ} (hi : i < 7) (hv : v < 64) : genCode ε i v < 64 :=
  (genCode_invol ε hi hv).2

theorem actEForm_lt (ε : Eps) {i x : ℕ} (hi : i < 7) : actEForm ε i x < 128 := by
  have h1 := genCode_lt ε hi (Nat.mod_lt x (by norm_num : 0 < 64))
  have h2 := genCode_lt ε hi (by norm_num : 0 < 64)
  rw [actEForm]
  split
  · omega
  · have := Nat.xor_lt_two_pow (n := 6) h1 h2
    omega

theorem toVec_actEForm (ε : Eps) {i x : ℕ} (hi : i < 7) :
    toVec 7 (actEForm ε i x) = actV7 (sPerm ε ⟨i, hi⟩) (toVec 7 x) := by
  have hm : x % 64 < 64 := Nat.mod_lt x (by norm_num)
  have h1 := genCode_lt ε hi hm
  have h2 := genCode_lt ε hi (by norm_num : 0 < 64)
  have hs : ∀ y, y < 64 → sPerm ε ⟨i, hi⟩ (toVec 6 y) = toVec 6 (genCode ε i y) := fun y hy => by
    rw [sPerm_apply, sFun, vecBits_toVec hy]
  rw [toVec7_eq x, actV7_mk7, hs _ hm, actEForm]
  by_cases hb : x.testBit 6
  · simp only [hb, ite_true]
    rw [toVec7_eq]
    have e1 : (genCode ε i (x % 64) + 64) % 64 = genCode ε i (x % 64) := by omega
    have e2 : (genCode ε i (x % 64) + 64).testBit 6 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]
      omega
    rw [e1, e2]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp [bz, h11]
  · simp only [hb, Bool.false_eq_true, ite_false]
    have hlt := Nat.xor_lt_two_pow (n := 6) h1 h2
    rw [toVec7_eq]
    have e1 : (genCode ε i (x % 64) ^^^ genCode ε i 0) % 64 = genCode ε i (x % 64) ^^^
        genCode ε i 0 := Nat.mod_eq_of_lt hlt
    have e2 : (genCode ε i (x % 64) ^^^ genCode ε i 0).testBit 6 = false :=
      Nat.testBit_lt_two_pow hlt
    rw [e1, e2, toVec_xor, ← hs 0 (by norm_num)]
    simp [bz, show toVec 6 0 = 0 from toVec_zero 6]


theorem actECode_eq (ε : Eps) {i x : ℕ} (hi : i < 7) (hx : x < 128) :
    actECode ε i x = actEForm ε i x :=
  (gamFacts ε).1.1 i hi x hx

theorem toVec_actECode (ε : Eps) {i x : ℕ} (hi : i < 7) (hx : x < 128) :
    toVec 7 (actECode ε i x) = rhoE ε (sGen ε ⟨i, hi⟩) (toVec 7 x) := by
  rw [actECode_eq ε hi hx, toVec_actEForm ε hi]
  rfl

theorem actECode_lt (ε : Eps) {i x : ℕ} (hi : i < 7) (hx : x < 128) : actECode ε i x < 128 := by
  rw [actECode_eq ε hi hx]; exact actEForm_lt ε hi

theorem sGen_inv (ε : Eps) (i : Fin 7) : (sGen ε i)⁻¹ = sGen ε i :=
  Subtype.ext (sPerm_inv ε i)

theorem permIdx_eq (ε : Eps) {i g : ℕ} (hi : i < 7) (hg : g < mOf ε) :
    permIdx ε i g = (alphaZ ε (sGen ε ⟨i, hi⟩) ⟨g, hg⟩ : ℕ) := by
  rw [alphaZ_val]
  obtain ⟨h1, -, -, h4⟩ := (gamFacts ε).2 g hg
  obtain ⟨hlt, heq⟩ := h4 i hi
  have hv : vecBits ((sGen ε ⟨i, hi⟩ : Equiv.Perm V6) (gam ε g)) =
      genCode ε i ((gamArr ε).getD g 0) := by
    change vecBits (sFun ε i (toVec 6 ((gamArr ε).getD g 0))) = _
    rw [vecBits_sFun ε hi, vecBits_toVec h1]
  rw [hv, ← heq, (gamFacts ε).2 _ hlt |>.2.2.1]

theorem actMCode_eq (ε : Eps) (i y : ℕ) :
    actMCode ε i y = foldOr (mOf ε) 7 fun g => actECode ε i (blkN 7 y (permIdx ε i g)) := rfl

theorem unpack_actMCode (ε : Eps) {i : ℕ} (hi : i < 7) (y : ℕ) :
    unpackV (mOf ε) 7 (toVec (mOf ε * 7) (actMCode ε i y)) =
      indAct (rhoE ε) (alphaZ ε) (sGen ε ⟨i, hi⟩) (unpackV (mOf ε) 7 (toVec (mOf ε * 7) y)) := by
  rw [actMCode_eq, toVec_foldOr (by norm_num) _ (fun g _ => actECode_lt ε hi (blkN_lt 7 _ _))]
  ext g : 1
  show _ = rhoE ε (sGen ε ⟨i, hi⟩) (unpackV (mOf ε) 7 (toVec (mOf ε * 7) y)
    (alphaZ ε (sGen ε ⟨i, hi⟩)⁻¹ g))
  rw [sGen_inv]
  have hg := g.2
  have hp : permIdx ε i g < mOf ε := (((gamFacts ε).2 g hg).2.2.2 i hi).1
  rw [toVec_actECode ε hi (blkN_lt 7 _ _)]
  congr 1
  have hidx : (⟨permIdx ε i g, hp⟩ : Fin (mOf ε)) = alphaZ ε (sGen ε ⟨i, hi⟩) g :=
    Fin.ext (permIdx_eq ε hi hg)
  rw [← hidx]
  exact toVec_blkN (k := mOf ε) y ⟨permIdx ε i g, hp⟩

theorem foxECode_lt (ε : Eps) {d : ℕ → ℕ} (hd : ∀ i, d i < 128) :
    ∀ {w : List ℕ}, (∀ i ∈ w, i < 7) → foxECode ε d w < 128
  | [], _ => by simp [foxECode]
  | i :: w, hw => by
    have hi := hw i List.mem_cons_self
    have h1 := foxECode_lt ε hd (w := w) fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have h2 := actECode_lt ε hi h1
    have := Nat.xor_lt_two_pow (n := 7) (hd i) h2
    simpa [foxECode] using this

theorem finOfNat_eq {i : ℕ} (hi : i < 7) : (Fin.ofNat 7 i : Fin 7) = ⟨i, hi⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hi)

theorem toVec_foxECode (ε : Eps) {d : ℕ → ℕ} (hd : ∀ i, d i < 128) :
    ∀ {w : List ℕ}, (∀ i ∈ w, i < 7) → toVec 7 (foxECode ε d w) =
      foxSum (fun i => rhoE ε (sGen ε i)) (fun i => toVec 7 (d i))
        (w.map (Fin.ofNat 7))
  | [], _ => toVec_zero 7
  | i :: w, hw => by
    have hi := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 7 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [foxECode, toVec_xorN, toVec_actECode ε hi (foxECode_lt ε hd hw'),
      toVec_foxECode ε hd hw', List.map_cons, finOfNat_eq hi]
    rfl

theorem unpackV_add (k n : ℕ) (y z : Fin (k * n) → ZMod 2) :
    unpackV k n (y + z) = unpackV k n y + unpackV k n z := rfl

theorem unpack_foxMCode (ε : Eps) (d : ℕ → ℕ) :
    ∀ {w : List ℕ}, (∀ i ∈ w, i < 7) →
      unpackV (mOf ε) 7 (toVec (mOf ε * 7) (foxMCode ε d w)) =
        foxSum (fun i => indAct (rhoE ε) (alphaZ ε) (sGen ε i))
          (fun i => unpackV (mOf ε) 7 (toVec (mOf ε * 7) (d i))) (w.map (Fin.ofNat 7))
  | [], _ => by
    rw [foxMCode, toVec_zero]
    rfl
  | i :: w, hw => by
    have hi := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 7 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [foxMCode, toVec_xorN, unpackV_add, unpack_actMCode ε hi, unpack_foxMCode ε d hw',
      List.map_cons, finOfNat_eq hi]
    rfl

end CFSG.EvenSmallLie.OmegaEight.NSplit
