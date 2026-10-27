module

public import CFSG.Certificates.Kernel.Q47KSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Q47KOSound
import CFSG.Certificates.Kernel.Q47KRunSound
import CFSG.Certificates.Kernel.FusYKSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Q47
open CFSG.KLie.CT (anyN andB orB notB)

theorem hsz64 : szOK 64 7 = true := by decide

theorem all_bound {n w : Nat} {gs : List (Array Nat)} {G : Nat → Nat} (h : Bound n w gs G)
    {f : Array Nat → Bool} (hf : ∀ k < gs.length, f (unpack n w (G k)) = true) : gs.all f = true := by
  rw [list_of_bound h, List.all_map, List.all_eq_true]
  intro k hk
  exact hf k (List.mem_range.1 hk)

theorem bnd_pin {n w : Nat} {gs : List (Array Nat)} {g : Nat} {G : Nat → Nat} {N : Nat}
    {T E S : Nat → Nat} (p : Pin n w gs g G N T E S) : Bound n w gs G := by
  have hl : gs.length = g := by simpa using p.size
  intro k hk
  exact ⟨by rw [← FusYK.toArray_get]; exact p.bind k (hl ▸ hk), p.perm k (hl ▸ hk)⟩

theorem len_pin {n w : Nat} {gs : List (Array Nat)} {g : Nat} {G : Nat → Nat} {N : Nat}
    {T E S : Nat → Nat} (p : Pin n w gs g G N T E S) : gs.length = g := by simpa using p.size

theorem PP_bound {n w : Nat} {gs : List (Array Nat)} {G : Nat → Nat} (hsz : szOK n w = true)
    (h : Bound n w gs G) {k : Nat} (hk : k < gs.length) : PP n w (G k) :=
  PP_of_permOK hsz (h k hk).2

theorem permOK_PP {n w p : Nat} (hp : PP n w p) :
    permOK n w (mask w) (n * w) p (pinvS n w (mask w) p) = true :=
  CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2

theorem testBit_foldr (x : Nat) : ∀ L : List Nat,
    (L.foldr (fun b acc => Nat.lor acc (Nat.shiftLeft 1 b)) 0).testBit x = decide (x ∈ L)
  | [] => by simp
  | b :: L => by
    have hs : Nat.shiftLeft 1 b = 2 ^ b := (Nat.shiftLeft_eq 1 b).trans (Nat.one_mul _)
    have e : (List.foldr (fun b acc => Nat.lor acc (Nat.shiftLeft 1 b)) 0 (b :: L)) =
        (L.foldr (fun b acc => Nat.lor acc (Nat.shiftLeft 1 b)) 0) ||| 2 ^ b := by
      rw [List.foldr_cons, hs]
      rfl
    rw [e, Nat.testBit_lor, testBit_foldr x L, Nat.testBit_two_pow, Bool.eq_iff_iff,
      Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr fun h => Or.inl h.symm, fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

theorem bit_maskOf (B : Array Nat) (x : Nat) : HeAutK.bitK (maskOf B) x = decide (x ∈ B.toList) := by
  rw [FusYK.bitK_eq_testBit]
  exact testBit_foldr x B.toList

theorem contains_eq (B : Array Nat) (x : Nat) : B.contains x = decide (x ∈ B.toList) := by
  rw [Bool.eq_iff_iff, Array.contains_iff_mem, decide_eq_true_iff, Array.mem_toList_iff]

theorem memTab_get (B : Array Nat) {x : Nat} (hx : x < 64) : (memTab B)[x]! = B.contains x := by
  unfold memTab
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem unpack_lt {t x : Nat} (ht : PP 64 7 t) (hx : x < 64) : (unpack 64 7 t)[x]! < 64 := by
  rw [unpack_getElem!, ite_eq_left hx]
  exact ht.2.1 x hx

theorem unpack_get64 {t x : Nat} (hx : x < 64) : (unpack 64 7 t)[x]! = pg 7 (mask 7) t x := by
  rw [unpack_getElem!, ite_eq_left hx]

abbrev Lt64 (A : Array Nat) : Prop := ∀ a ∈ A.toList, a < 64

theorem mapsInto_eq {t : Nat} {A : Array Nat} (B : Array Nat) (hA : Lt64 A) :
    mapsInto (unpack 64 7 t) A B = mapsK t A (maskOf B) := by
  unfold mapsInto mapsK
  refine HexaK.all_congr_mem fun a ha => ?_
  rw [unpack_get64 (hA a ha), bit_maskOf, contains_eq]

theorem mapsIntoM_eq {t : Nat} (ht : PP 64 7 t) {A : Array Nat} (B : Array Nat) (hA : Lt64 A) :
    mapsIntoM (unpack 64 7 t) A (memTab B) = mapsK t A (maskOf B) := by
  unfold mapsIntoM mapsK
  refine HexaK.all_congr_mem fun a ha => ?_
  rw [memTab_get B (unpack_lt ht (hA a ha)), unpack_get64 (hA a ha), bit_maskOf, contains_eq]

theorem swapCheck_eq {t : Nat} (ht : PP 64 7 t) {W1 W2 : Array Nat} (h1 : Lt64 W1) (h2 : Lt64 W2) :
    swapCheckG W1 W2 (unpack 64 7 t) = swapK W1 W2 t := by
  unfold swapCheckG swapK
  rw [mapsIntoM_eq ht _ h1, mapsIntoM_eq ht _ h2, mapsIntoM_eq ht _ h1, mapsIntoM_eq ht _ h2, orB_eq,
    andB_eq, andB_eq]

theorem eight_lt {W : Array Nat} (h : eightCheck W = true) : Lt64 W := by
  unfold eightCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem eight_size {W : Array Nat} (h : eightCheck W = true) : W.size = 8 := by
  unfold eightCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem ts_eight {form W : Array Nat} (h : tsCheckG form W = true) : eightCheck W = true := by
  unfold tsCheckG at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem get_lt64 {W : Array Nat} (h : eightCheck W = true) {i : Nat} (hi : i < 8) : W[i]! < 64 := by
  have hs := eight_size h
  rw [getElem!_pos W i (by omega)]
  exact eight_lt h _ (Array.getElem_mem_toList _)

theorem addCheck_eq {t : Nat} : addCheck (unpack 64 7 t) = addK t := by
  unfold addCheck addK
  rw [allN_eq']
  refine HexaK.all_congr_mem fun u hu => ?_
  rw [allN_eq']
  refine HexaK.all_congr_mem fun v hv => ?_
  have hu' := List.mem_range.1 hu
  have hv' := List.mem_range.1 hv
  have huv : u ^^^ v < 64 := Nat.xor_lt_two_pow (n := 6) hu' hv'
  rw [unpack_get64 huv, unpack_get64 hu', unpack_get64 hv', beq_nat]
  rfl

theorem isom_of {form : Array Nat} {t : Nat}
    (hp : permOK 64 7 (mask 7) (64 * 7) t (pinvS 64 7 (mask 7) t) = true) (ha : addK t = true)
    (hf : formCheckG form (unpack 64 7 t) = true) : isomCheckG form (unpack 64 7 t) = true := by
  unfold isomCheckG
  rw [Bool.and_eq_true, Bool.and_eq_true, addCheck_eq]
  exact ⟨⟨validA_unpack hp, ha⟩, hf⟩

theorem isom_all {form : Array Nat} {gs : List (Array Nat)} {G : Nat → Nat} (b : Bound 64 7 gs G)
    (ha : ∀ k < gs.length, addK (G k) = true)
    (hf : ∀ k < gs.length, formCheckG form (unpack 64 7 (G k)) = true) :
    gs.all (isomCheckG form) = true :=
  all_bound b fun k hk => isom_of (b k hk).2 (ha k hk) (hf k hk)

theorem form_of_trans {form : Array Nat} {gs : List (Array Nat)} {G : Nat → Nat} {j : Nat}
    (b : Bound 64 7 gs G) (h : gs.all (transElG form j) = true) :
    ∀ k < gs.length, formCheckG form (unpack 64 7 (G k)) = true := by
  intro k hk
  rw [List.all_eq_true] at h
  have := h _ (List.getElem_mem hk)
  rw [← getElem!_pos gs k hk, (b k hk).1] at this
  unfold transElG at this
  rw [Bool.and_eq_true] at this
  exact this.1

theorem transCheck_eq {LY : List Nat} {W : Array Nat} (hW : eightCheck W = true) :
    transCheck (LY.map (unpack 64 7)) W = transYK LY W := by
  unfold transCheck transYK
  refine HexaK.all_congr_mem fun x _ => ?_
  have e : ∀ y ∈ LY, ((fun y : Array Nat => y[W[1]!]! == x) ∘ unpack 64 7) y =
      Nat.beq (pg 7 (mask 7) y W[1]!) x := fun y _ => by
    simp only [Function.comp_apply]
    rw [unpack_get64 (get_lt64 hW (by decide)), beq_nat]
  rw [orB_eq, beq_nat, List.any_map, HexaK.any_congr_mem e]

theorem evalWord_eq {GY : Nat → Nat} {yg : List (Array Nat)} {h : Nat} (bY : Bound 64 7 yg GY)
    (hyl : yg.length = 2) (pY : ∀ k < 2, PP 64 7 (GY k)) (ph : PP 64 7 h) :
    ∀ ws : List Nat, ws.all (fun l => decide (1 ≤ l) && decide (l ≤ 3)) = true →
      evalWordG (yg ++ [unpack 64 7 h]) ws = unpack 64 7 (evalK (witL GY h) ws) ∧
        PP 64 7 (evalK (witL GY h) ws)
  | [], _ => ⟨idA_eq hsz64, PP.id hsz64⟩
  | l :: ws, hw => by
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      at hw
    obtain ⟨⟨h1, h3⟩, hw⟩ := hw
    obtain ⟨e, p⟩ := evalWord_eq bY hyl pY ph ws hw
    have hL : (yg ++ [unpack 64 7 h])[l - 1]! = unpack 64 7 (witL GY h (Nat.sub l 1)) ∧
        PP 64 7 (witL GY h (Nat.sub l 1)) := by
      unfold witL
      rw [nIf_ite]
      by_cases hl : l - 1 < 2
      · have hl' : Nat.blt (Nat.sub l 1) 2 = true := Nat.blt_eq.mpr hl
        rw [ite_eq_left hl', getElem!_pos _ _ (by simp; omega),
          List.getElem_append_left (by omega), ← getElem!_pos yg _ (by omega)]
        exact ⟨(bY _ (by omega)).1, pY _ hl⟩
      · have hf : Nat.blt (Nat.sub l 1) 2 ≠ true := fun e => hl (Nat.blt_eq.mp e)
        rw [ite_eq_right hf, getElem!_pos _ _ (by simp; omega), List.getElem_append_right (by omega)]
        have e2 : l - 1 - yg.length = 0 := by omega
        refine ⟨?_, ph⟩
        simp only [e2, List.getElem_singleton]
    have e1 : evalWordG (yg ++ [unpack 64 7 h]) (l :: ws) =
        compA 64 (yg ++ [unpack 64 7 h])[l - 1]! (evalWordG (yg ++ [unpack 64 7 h]) ws) := rfl
    have e2 : evalK (witL GY h) (l :: ws) =
        HexaK.mul 64 7 (witL GY h (Nat.sub l 1)) (evalK (witL GY h) ws) := by
      change strictN (evalK (witL GY h) ws) (fun acc => HexaK.mul 64 7 (witL GY h (Nat.sub l 1)) acc) = _
      rw [strictN_eq']
    rw [e1, e2, hL.1, e, compA_PP hL.2 p]
    exact ⟨rfl, hL.2.mul p⟩

theorem witCheck_of {GY : Nat → Nat} {yg : List (Array Nat)} {g u : Nat} {ws : List (List Nat)}
    (bY : Bound 64 7 yg GY) (hyl : yg.length = 2) (pg' : PP 64 7 g) (pu : PP 64 7 u)
    (hl : ws.all (·.all fun l => decide (1 ≤ l) && decide (l ≤ 3)) = true)
    (h : witK GY g u ws = true) :
    witCheckG yg (compA 64 (unpack 64 7 g) (unpack 64 7 u)) ws = true := by
  have pY : ∀ k < 2, PP 64 7 (GY k) := fun k hk => PP_bound hsz64 bY (by omega)
  have ph : PP 64 7 (HexaK.mul 64 7 g u) := pg'.mul pu
  unfold witK at h
  rw [strictB_eq'] at h
  rw [compA_PP pg' pu]
  change witCheckG yg (unpack 64 7 (HexaK.mul 64 7 g u)) ws = true
  generalize HexaK.mul 64 7 g u = h' at h ph
  have hw : ∀ k < ws.length, (ws.getD k []).all (fun l => decide (1 ≤ l) && decide (l ≤ 3)) = true := by
    intro k hk
    rw [List.all_eq_true] at hl
    rw [List.getD_eq_getElem _ _ hk]
    exact hl _ (List.getElem_mem hk)
  have hlen := Nat.eq_of_beq_eq_true h
  obtain ⟨-, eE, cE⟩ := runK_sound (n := 64) (w := 7) (gs := ws.map (evalWordG (yg ++ [unpack 64 7 h'])))
    (G := fun k => evalK (witL GY h') (ws.getD k [])) (fuel := 100) hsz64 (List.length_map ..)
    (fun k hk => by
      have e := evalWord_eq bY hyl pY ph _ (hw k hk)
      refine ⟨?_, permOK_PP e.2⟩
      rw [getElem!_pos _ k (by simpa using hk), List.getElem_map, ← e.1, List.getD_eq_getElem _ _ hk])
    (by rw [hlen]; decide) (by decide)
  rw [hlen] at cE
  unfold witCheckG
  rw [Bool.and_eq_true]
  exact ⟨hl, cE⟩

end CFSG.KC.Q47K

end
