module

public import Certificates.Data.Kernel.D4K
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.D4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum

theorem siftOK_parts {n w nb BP G : Nat} {LR TRI : Nat → Nat}
    (h : siftOK n w LR TRI BP nb G = true) :
    Nat.beq (Nat.shiftRight G (n * w)) 0 = true ∧
      allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true := by
  unfold siftOK at h
  cases h1 : Nat.beq (Nat.shiftRight G (n * w)) 0 <;> rw [h1] at h
  · exact absurd (h : false = true) Bool.false_ne_true
  cases h2 : allN n (fun i => Nat.blt (pg w (mask w) G i) n) <;> rw [h2] at h
  · exact absurd (h : false = true) Bool.false_ne_true
  exact ⟨rfl, rfl, h⟩

theorem allBlk_true {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
      at h
    cases h1 : f (Nat.add b len) <;> rw [h1] at h
    · exact absurd (h : false = true) Bool.false_ne_true
    rcases Nat.lt_or_ge l len with h2 | h2
    · exact allBlk_true h l h2
    · have e : l = len := by omega
      subst e
      exact h1

theorem forall_of_slices {L K : Nat} {f : Nat → Bool} (hL : 0 < L)
    (h : ∀ s < K, allBlk (Nat.mul L s) f L = true) : ∀ i < L * K, f i = true := by
  intro i hi
  have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at hi)
  have := allBlk_true (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  have e : Nat.mul L (i / L) + i % L = i := Nat.div_add_mod i L
  rwa [e] at this

theorem allN_of_slices {L K : Nat} {f : Nat → Bool} (hL : 0 < L)
    (h : ∀ s < K, allBlk (Nat.mul L s) f L = true) : allN (L * K) f = true :=
  Orb.allN_iff.2 (forall_of_slices hL h)

theorem permB_pts {n w ng N : Nat} {G T E S : Nat → Nat}
    (hk : CFSG.KC.BfsPin.bfsK n w ng G N T E S = true)
    (hp : ∀ k < ng, CFSG.KC.Misc.ArrEnum.permB n w (G k) = true) :
    ∀ i < N, CFSG.KC.Misc.ArrEnum.permB n w (T i) = true := fun i hi =>
  CFSG.KC.Misc.ArrEnum.permB_of_pp (CFSG.KC.BfsPin.PP_pts hk (fun k hk' => hp k hk') i hi)

theorem linesK_of {n w p N r : Nat} {T LX : Nat → Nat}
    (h1 : ∀ k < N, lineAt n w p r T LX k = true)
    (h2 : allN r (fun j => permB n w (LX j) && Nat.beq (pw n w (LX j) p) (pidn n w)) = true) :
    linesK n w p N r T LX = true := by
  unfold linesK
  rw [Bool.and_eq_true]
  exact ⟨Orb.allN_iff.2 h1, h2⟩

theorem testBit_imgBitsK {w p x : Nat} :
    ∀ k, (imgBitsK k w p).testBit x = true ↔ ∃ i < k, pg w (mask w) p i = x
  | 0 => by
    change Nat.testBit 0 x = true ↔ _
    simp
  | k + 1 => by
    change (imgBitsK k w p ||| 2 ^ pg w (mask w) p k).testBit x = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true, testBit_imgBitsK k, Nat.testBit_two_pow]
    constructor
    · rintro (⟨i, hi, e⟩ | e)
      · exact ⟨i, by omega, e⟩
      · exact ⟨k, by omega, of_decide_eq_true e⟩
    · rintro ⟨i, hi, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, e⟩
      · exact Or.inr (decide_eq_true e)

theorem PP_of_permImgK {n w p : Nat} (hw : szOK n w = true) (h : permImgK n w p = true) :
    CFSG.KC.BfsPin.PP n w p := by
  unfold permImgK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hlt : ∀ i < n, pg w (mask w) p i < n := fun i hi => Nat.blt_eq.mp (Orb.allN_iff.1 h2 i hi)
  let f : Fin n → Fin n := fun y => ⟨pg w (mask w) p y, hlt y y.2⟩
  have hf : Function.Surjective f := fun x => by
    have hx : (2 ^ n - 1).testBit x.1 = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true x.2
    rw [← Nat.eq_of_beq_eq_true h3, testBit_imgBitsK] at hx
    obtain ⟨i, hi, e⟩ := hx
    exact ⟨⟨i, hi⟩, Fin.ext e⟩
  have hi := Finite.injective_iff_surjective.2 hf
  refine ⟨?_, ⟨hlt, fun a ha b hb e => ?_⟩⟩
  · unfold CFSG.KS.Prim.canonK
    simp only [CFSG.KS.bAnd_iff]
    exact ⟨hw, h1, Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hlt i hi)⟩
  · have := @hi ⟨a, ha⟩ ⟨b, hb⟩ (Fin.ext e)
    exact congrArg Fin.val this

theorem permB_of_permImgK {n w p : Nat} (hw : szOK n w = true) (h : permImgK n w p = true) :
    permB n w p = true :=
  permB_of_pp (PP_of_permImgK hw h)

theorem pw3_of_cubeIdK {n w p : Nat} (hw : szOK n w = true) (hp : permB n w p = true)
    (h : cubeIdK n w p = true) : Nat.beq (pw n w p 3) (pidn n w) = true := by
  have hP := pp_of_permB hw hp
  have hn := hP.lt32
  obtain ⟨hn', hw'⟩ := CFSG.KC.BfsPin.szOK_facts' hw
  have e1 : ∀ e, ppow n w (mask w) (pidn n w) p (e + 1) =
      pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p e) := fun e =>
    PF.strictN_eqP (ppow n w (mask w) (pidn n w) p e) (fun q => pcomp n w (mask w) p q)
  have e3 : ppow n w (mask w) (pidn n w) p 3 = pcomp n w (mask w) p (pcomp n w (mask w) p
      (pcomp n w (mask w) p (pidn n w))) := by
    rw [(e1 2 : ppow n w (mask w) (pidn n w) p 3 = _),
      (e1 1 : ppow n w (mask w) (pidn n w) p 2 = _),
      (e1 0 : ppow n w (mask w) (pidn n w) p 1 = _)]
    rfl
  unfold cubeIdK at h
  have hc := Orb.allN_iff.1 h
  unfold pw
  rw [← CFSG.KC.BfsPin.eqA_PP (pp_ppow hw hP 3) (CFSG.KC.BfsPin.PP.id hw)]
  unfold CFSG.Monster.B.Co2.Native.eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  rw [CFSG.KC.BfsPin.unpack_getElem!, CFSG.KC.BfsPin.unpack_getElem!]
  simp only [hx, ↓reduceIte]
  rw [e3, PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pidn hn' hw' hx, beq_iff_eq]
  exact Nat.eq_of_beq_eq_true (hc x hx)

theorem beq_of_pg {n w P Q : Nat} (hP : CFSG.KC.BfsPin.PP n w P) (hQ : CFSG.KC.BfsPin.PP n w Q)
    (h : ∀ x < n, pg w (mask w) P x = pg w (mask w) Q x) : Nat.beq P Q = true := by
  rw [← CFSG.KC.BfsPin.eqA_PP hP hQ]
  unfold CFSG.Monster.B.Co2.Native.eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  rw [CFSG.KC.BfsPin.unpack_getElem!, CFSG.KC.BfsPin.unpack_getElem!]
  simp only [hx, ↓reduceIte]
  rw [h x hx]
  exact beq_self_eq_true _

theorem pg_ppow_succ {n w p x : Nat} (hn : n < 2 ^ 32) (hx : x < n) (e : Nat) :
    pg w (mask w) (ppow n w (mask w) (pidn n w) p (e + 1)) x =
      pg w (mask w) p (pg w (mask w) (ppow n w (mask w) (pidn n w) p e) x) := by
  have e1 : ppow n w (mask w) (pidn n w) p (e + 1) =
      pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p e) :=
    PF.strictN_eqP (ppow n w (mask w) (pidn n w) p e) (fun q => pcomp n w (mask w) p q)
  rw [e1, PF.pg_pcomp hn hx]

theorem cubeIdK_of_pw3 {n w p : Nat} (hw : szOK n w = true) (hp : permB n w p = true)
    (h : Nat.beq (pw n w p 3) (pidn n w) = true) : cubeIdK n w p = true := by
  have hn := (pp_of_permB hw hp).lt32
  obtain ⟨hn', hw'⟩ := CFSG.KC.BfsPin.szOK_facts' hw
  unfold cubeIdK
  rw [Orb.allN_iff]
  intro x hx
  have e := congrArg (fun q => pg w (mask w) q x) (Nat.eq_of_beq_eq_true h)
  unfold pw at e
  rw [pg_ppow_succ hn hx 2, pg_ppow_succ hn hx 1, pg_ppow_succ hn hx 0] at e
  change pg w (mask w) p (pg w (mask w) p (pg w (mask w) p (pg w (mask w) (pidn n w) x))) = _
    at e
  rw [PF.pg_pidn hn' hw' hx] at e
  rw [e]
  exact Nat.beq_refl x

theorem lineAt_of_lineCubeK {n w r k : Nat} {T LX : Nat → Nat} (hw : szOK n w = true)
    (hT : permB n w (T k) = true) (hL : ∀ j < r, permB n w (LX j) = true)
    (h : lineCubeK n w r T LX k = true) : lineAt n w 3 r T LX k = true := by
  have hTP := pp_of_permB hw hT
  have hn := hTP.lt32
  obtain ⟨hn', hw'⟩ := CFSG.KC.BfsPin.szOK_facts' hw
  unfold lineCubeK at h
  unfold lineAt
  cases hc : cubeIdK n w (T k)
  · have h3 : Nat.beq (pw n w (T k) 3) (pidn n w) = false := by
      cases h' : Nat.beq (pw n w (T k) 3) (pidn n w)
      · rfl
      · rw [cubeIdK_of_pw3 hw hT h'] at hc
        exact Bool.noConfusion hc
    rw [h3]
    rfl
  rw [hc] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inr h)
  right
  rw [anyNP_eq, List.any_eq_true] at h ⊢
  obtain ⟨j, hj, hj'⟩ := h
  have hjr : j < r := List.mem_range.1 hj
  have hLP := pp_of_permB hw (hL j hjr)
  refine ⟨j, hj, ?_⟩
  rw [anyNP_eq, List.any_eq_true]
  rw [Bool.or_eq_true] at hj'
  rcases hj' with e | e
  · refine ⟨1, List.mem_range.2 (by omega), beq_of_pg hTP (pp_ppow hw hLP 1) fun x hx => ?_⟩
    rw [Nat.eq_of_beq_eq_true e]
    unfold pw
    rw [pg_ppow_succ hn hx 0]
    change _ = pg w (mask w) (LX j) (pg w (mask w) (pidn n w) x)
    rw [PF.pg_pidn hn' hw' hx]
  · refine ⟨2, List.mem_range.2 (by omega), beq_of_pg hTP (pp_ppow hw hLP 2) fun x hx => ?_⟩
    unfold eq2 at e
    unfold pw
    rw [pg_ppow_succ hn hx 1, pg_ppow_succ hn hx 0]
    change _ = pg w (mask w) (LX j) (pg w (mask w) (LX j) (pg w (mask w) (pidn n w) x))
    rw [PF.pg_pidn hn' hw' hx]
    exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 e x hx)

theorem pw3_all {n w r : Nat} {LX : Nat → Nat} (hw : szOK n w = true)
    (h : allN r (fun j => permImgK n w (LX j) && cubeIdK n w (LX j)) = true) :
    allN r (fun j => permB n w (LX j) && Nat.beq (pw n w (LX j) 3) (pidn n w)) = true := by
  rw [Orb.allN_iff] at h ⊢
  intro j hj
  have hj' := h j hj
  rw [Bool.and_eq_true] at hj' ⊢
  have hb := permB_of_permImgK hw hj'.1
  exact ⟨hb, pw3_of_cubeIdK hw hb hj'.2⟩

theorem transK_of_transE {n w r nc : Nat} {H X L : Nat → Nat} {rec : List Nat}
    (hw : szOK n w = true) (hX : ∀ c < nc, permB n w (X c) = true)
    (hL : ∀ j < r, permB n w (L j) = true) (hrec : ∀ j < r, rec.getD j 0 < nc)
    (h : transE n w r H X L rec = true) : transK n w r H X L rec = true := by
  unfold transE at h
  unfold transK
  rw [Orb.allN_iff] at h ⊢
  intro j hj
  have hj' := h j hj
  rw [Bool.and_eq_true] at hj' ⊢
  refine ⟨permB_of_permImgK hw hj'.1, ?_⟩
  have hH := PP_of_permImgK hw hj'.1
  have hXp := pp_of_permB hw (hX _ (hrec j hj))
  have hLp := pp_of_permB hw (hL j hj)
  have hn := hH.lt32
  have hw2 : n < 2 ^ w := by
    have := (CFSG.KC.BfsPin.szOK_facts' hw).2
    omega
  have he0 : eq22 n w (mask w) (H j) (X (rec.getD j 0)) (L j) (H j) = true := hj'.2
  unfold eq22 at he0
  have he := Orb.allN_iff.1 he0
  have hs : ∀ x < n, ∃ y < n, pg w (mask w) (H j) y = x := by
    let f : Fin n → Fin n := fun y => ⟨pg w (mask w) (H j) y, hH.2.1 y y.2⟩
    have hf : Function.Injective f := fun a b e =>
      Fin.ext (hH.2.2 a a.2 b b.2 (congrArg Fin.val e))
    intro x hx
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨x, hx⟩
    exact ⟨y, y.2, congrArg Fin.val hy⟩
  unfold cj cm
  rw [← CFSG.KC.BfsPin.eqA_PP (hH.mul (hXp.mul hH.inv)) hLp]
  unfold CFSG.Monster.B.Co2.Native.eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  rw [CFSG.KC.BfsPin.unpack_getElem!, CFSG.KC.BfsPin.unpack_getElem!]
  simp only [hx, ↓reduceIte]
  obtain ⟨y, hy, rfl⟩ := hs x hx
  rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, CFSG.KS.PinvS.pg_pinvS hw2 hH.2 hy,
    Nat.eq_of_beq_eq_true (he y hy)]
  exact beq_self_eq_true _

end CFSG.KC.D4K

end
