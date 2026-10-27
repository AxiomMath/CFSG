module

public import Certificates.Data.Kernel.Co3K
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3CheckInputs

public section

namespace CFSG.KC.Co3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
open CFSG.Sporadic.Schreier.Co3.Native CFSG.Certificates.Native
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

abbrev Cn (X : Nat) : Prop := canonK 276 9 (mask 9) (276 * 9) X = true

theorem cnPk {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pk p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem compU {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 276 (unpack 276 9 p) (unpack 276 9 q) = unpack 276 9 (pk p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem eqU {p q : Nat} (hp : Cn p) (hq : Cn q) :
    eqA 276 (unpack 276 9 p) (unpack 276 9 q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · refine neK_sound ?_
    unfold neK
    rw [hp, hq, h]
  · exact eqK_sound h

theorem idU (h : idK 276 9 (mask 9) = true) : idA 276 = unpack 276 9 idk := (idK_sound h).symm

theorem anyNK_spec {n : Nat} {f : Nat → Bool} (h : anyNK n f = true) : ∃ i < n, f i = true := by
  induction n with
  | zero =>
    have e : anyNK 0 f = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | succ n ih =>
    have e : anyNK (n + 1) f = Bool.rec (motive := fun _ => Bool) (anyNK n f) true (f n) := rfl
    rw [e] at h
    cases hf : f n
    · rw [hf] at h
      obtain ⟨i, hi, hfi⟩ := ih h
      exact ⟨i, by omega, hfi⟩
    · exact ⟨n, by omega, hf⟩

private theorem bif_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem nat_all_iff {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun H i h => H ⟨i, h⟩ (List.mem_finRange _), fun H x _ => H x.1 x.2⟩

theorem nat_any_iff {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.any n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  exact ⟨fun ⟨x, _, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨i, h, hf⟩ => ⟨⟨i, h⟩, List.mem_finRange _, hf⟩⟩

private theorem ofFn_ext {n : Nat} {f h : Fin n → Nat} {g : Equiv.Perm (Fin n)}
    (hf : Rep n (Array.ofFn f) g) (hh : Rep n (Array.ofFn h) g) : Array.ofFn f = Array.ofFn h := by
  congr 1
  funext x
  have a := hf x
  have b := hh x
  rw [getElem!_ofFn_nat _ x.2] at a b
  rw [a, b]

theorem prod3_of {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds 276 9 PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK 276 9 (mask 9) (276 * 9) (PS j) (PSI j)) = true)
    (hl : LevelsOK 276 9 PS PSI LR TR TRI kS 3 BP)
    (hc : ∀ i < 3, ∀ k < rcnt (LR i), Cn (TR (roff 276 (276 * 9) (LR i) + k)))
    {P : Nat → Bool} {Q : Array Nat → Bool}
    (hPQ : ∀ G, Cn G → P G = true → Q (unpack 276 9 G) = true)
    (h : ∀ a < rcnt (LR 0), prod3K LR TR P a = true) :
    co3KAllProd3 (rawLevels 276 S base) Q = true := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hlev : ∀ i < 3, (rawLevels 276 S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), ∃ g : Equiv.Perm (Fin 276), Rep 276 (rawLevels 276 S base)[i]!.tr[k]! g ∧
        Raw.Orb.PRep 276 9 (TR (roff 276 (276 * 9) (LR i) + k)) g := by
    intro i hi
    obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    refine ⟨A.cnt.symm, fun k hk => ⟨_, (A.tr k (by rw [← A.cnt]; exact hk)).1, (P k hk).1⟩⟩
  obtain ⟨c0, T0⟩ := hlev 0 (by omega)
  obtain ⟨c1, T1⟩ := hlev 1 (by omega)
  obtain ⟨c2, T2⟩ := hlev 2 (by omega)
  unfold co3KAllProd3 allLt
  rw [nat_all_iff]
  intro a ha
  rw [nat_all_iff]
  intro b hb'
  rw [nat_all_iff]
  intro c hc'
  rw [c0] at ha
  rw [c1] at hb'
  rw [c2] at hc'
  obtain ⟨g0, r0, p0⟩ := T0 a ha
  obtain ⟨g1, r1, p1⟩ := T1 b hb'
  obtain ⟨g2, r2, p2⟩ := T2 c hc'
  have hk := h a ha
  unfold prod3K at hk
  simp only [Raw.Orb.strictB_eq] at hk
  have hk' := Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 hk b hb') c hc'
  have h32 : (276 : Nat) < 2 ^ 32 := by norm_num
  have hq := Raw.Orb.prep_pcomp h32 (Raw.Orb.prep_pcomp h32 p0 p1) p2
  have hG : Cn (pk (pk (TR (roff 276 (276 * 9) (LR 0) + a)) (TR (roff 276 (276 * 9) (LR 1) + b)))
      (TR (roff 276 (276 * 9) (LR 2) + c))) :=
    cnPk (cnPk (hc 0 (by omega) a ha) (hc 1 (by omega) b hb')) (hc 2 (by omega) c hc')
  have e : compA 276 (compA 276 (rawLevels 276 S base)[0]!.tr[a]! (rawLevels 276 S base)[1]!.tr[b]!)
      (rawLevels 276 S base)[2]!.tr[c]! = unpack 276 9 (pk (pk (TR (roff 276 (276 * 9) (LR 0) + a))
        (TR (roff 276 (276 * 9) (LR 1) + b))) (TR (roff 276 (276 * 9) (LR 2) + c))) := by
    have ra := rep_compA (rep_compA r0 r1) r2
    have rb := Raw.Orb.rep_unpack hq
    unfold compA at ra ⊢
    unfold unpack at rb ⊢
    exact ofFn_ext ra rb
  beta_reduce
  rw [e]
  exact hPQ _ hG hk'

theorem eK_of {E Z G : Nat} (hE : Cn E) (hZ : Cn Z) (hG : Cn G) (h : eK E (pk E Z) G = true) :
    (eqA 276 (compA 276 (unpack 276 9 G) (unpack 276 9 E)) (compA 276 (unpack 276 9 E) (unpack 276 9 G)) ||
      eqA 276 (compA 276 (unpack 276 9 G) (unpack 276 9 E))
        (compA 276 (compA 276 (unpack 276 9 E) (unpack 276 9 Z)) (unpack 276 9 G))) = true := by
  rw [compU hG hE, compU hE hG, compU hE hZ, compU (cnPk hE hZ) hG, eqU (cnPk hG hE) (cnPk hE hG),
    eqU (cnPk hG hE) (cnPk (cnPk hE hZ) hG)]
  unfold eK at h
  rw [Raw.Orb.strictB_eq] at h
  rcases bif_true h with ⟨h1, _⟩ | ⟨_, h2⟩
  · rw [h1, Bool.true_or]
  · rw [h2, Bool.or_true]

theorem k3K_of {S SI D : Nat → Nat} {G : Nat} {Gs Ginv Ds : Array (Array Nat)}
    (hS : ∀ k < 8, Cn (S k)) (hSI : ∀ k < 8, Cn (SI k)) (hD : ∀ i < 23, Cn (D i))
    (hId : idA 276 = unpack 276 9 idk) (hcid : Cn idk) (hG : Cn G)
    (hGs : Gs.size = 8) (hGk : ∀ k < 8, Gs[k]! = unpack 276 9 (S k))
    (hGi : ∀ k < 8, Ginv[k]! = unpack 276 9 (SI k))
    (hDs : Ds.size = 23) (hDk : ∀ i < 23, Ds[i]! = unpack 276 9 (D i))
    (h : k3K S SI D G = true) :
    (!(eqA 276 (compA 276 (unpack 276 9 G) (unpack 276 9 G)) (idA 276)) ||
      eqA 276 (unpack 276 9 G) (idA 276) ||
      !(allLt Gs.size fun k => commutesA 276 (unpack 276 9 G)
        (compA 276 (compA 276 Gs[k]! (unpack 276 9 G)) Ginv[k]!)) ||
      anyLt Ds.size fun i => eqA 276 (unpack 276 9 G) Ds[i]!) = true := by
  rw [hId, compU hG hG, eqU (cnPk hG hG) hcid, eqU hG hcid]
  unfold k3K at h
  cases e1 : Nat.beq (pk G G) idk
  · rw [Bool.not_false, Bool.true_or, Bool.true_or, Bool.true_or]
  rw [e1] at h
  cases e2 : Nat.beq G idk
  · rw [e2] at h
    cases e3 : (allLt Gs.size fun k => commutesA 276 (unpack 276 9 G)
        (compA 276 (compA 276 Gs[k]! (unpack 276 9 G)) Ginv[k]!))
    · rw [Bool.not_false, Bool.or_true, Bool.true_or]
    have hall : allN 8 (fun k => strictB (pk (pk (S k) G) (SI k)) (fun C =>
        Nat.beq (pk G C) (pk C G))) = true := by
      refine Raw.Orb.allN_iff.2 fun k hk => ?_
      rw [Raw.Orb.strictB_eq]
      have := allLt_spec e3 (i := k) (by rw [hGs]; exact hk)
      unfold commutesA at this
      have cC : Cn (pk (pk (S k) G) (SI k)) := cnPk (cnPk (hS k hk) hG) (hSI k hk)
      rw [hGk k hk, hGi k hk, compU (hS k hk) hG, compU (cnPk (hS k hk) hG) (hSI k hk),
        compU hG cC, compU cC hG, eqU (cnPk hG cC) (cnPk cC hG)] at this
      exact this
    rw [hall] at h
    obtain ⟨i, hi, hgi⟩ := anyNK_spec h
    have hany : (anyLt Ds.size fun i => eqA 276 (unpack 276 9 G) Ds[i]!) = true := by
      unfold anyLt
      rw [nat_any_iff]
      refine ⟨i, by rw [hDs]; exact hi, ?_⟩
      beta_reduce
      rw [hDk i hi, eqU hG (hD i hi)]
      exact hgi
    rw [hany, Bool.or_true]
  · rw [Bool.or_true, Bool.true_or, Bool.true_or]

theorem pairK_of {T Z X Y : Nat} {Ws : Array (Array Nat)} (hX : Cn X) (hY : Cn Y) (hZ : Cn Z)
    (hW : ∀ k < 72, Cn (lane T k)) (hWs : Ws.size = 72)
    (hWk : ∀ k < 72, Ws[k]! = unpack 276 9 (lane T k)) (h : pairK T Z X Y = true) :
    (!(commutesA 276 (unpack 276 9 X) (unpack 276 9 Y)) || eqA 276 (unpack 276 9 X) (unpack 276 9 Z) ||
      eqA 276 (unpack 276 9 Y) (unpack 276 9 Z) || eqA 276 (unpack 276 9 Y) (unpack 276 9 X) ||
      eqA 276 (unpack 276 9 Y) (compA 276 (unpack 276 9 X) (unpack 276 9 Z)) ||
      anyLt Ws.size fun k => !(commutesA 276 Ws[k]! (unpack 276 9 X) &&
        commutesA 276 Ws[k]! (unpack 276 9 Y))) = true := by
  unfold commutesA
  rw [compU hX hY, compU hY hX, eqU (cnPk hX hY) (cnPk hY hX), eqU hX hZ, eqU hY hZ, eqU hY hX,
    compU hX hZ, eqU hY (cnPk hX hZ)]
  unfold pairK at h
  cases e1 : Nat.beq (pk X Y) (pk Y X)
  · rw [Bool.not_false, Bool.true_or, Bool.true_or, Bool.true_or, Bool.true_or, Bool.true_or]
  rw [e1] at h
  cases e2 : Nat.beq X Z
  · rw [e2] at h
    cases e3 : Nat.beq Y Z
    · rw [e3] at h
      cases e4 : Nat.beq Y X
      · rw [e4] at h
        cases e5 : Nat.beq Y (pk X Z)
        · rw [e5] at h
          obtain ⟨k, hk, hs⟩ := anyNK_spec h
          rw [Raw.Orb.strictB_eq] at hs
          have hany : (anyLt Ws.size fun k => !(eqA 276 (compA 276 Ws[k]! (unpack 276 9 X))
              (compA 276 (unpack 276 9 X) Ws[k]!) && eqA 276 (compA 276 Ws[k]! (unpack 276 9 Y))
              (compA 276 (unpack 276 9 Y) Ws[k]!))) = true := by
            unfold anyLt
            rw [nat_any_iff]
            refine ⟨k, by rw [hWs]; exact hk, ?_⟩
            beta_reduce
            have cW := hW k hk
            rw [hWk k hk, compU cW hX, compU hX cW, compU cW hY, compU hY cW,
              eqU (cnPk cW hX) (cnPk hX cW), eqU (cnPk cW hY) (cnPk hY cW)]
            unfold sepK at hs
            cases f1 : Nat.beq (pk (lane T k) X) (pk X (lane T k))
            · rfl
            rw [f1] at hs
            cases f2 : Nat.beq (pk (lane T k) Y) (pk Y (lane T k))
            · rfl
            rw [f2] at hs
            exact absurd hs (by decide)
          rw [hany, Bool.or_true]
        · rw [Bool.or_true, Bool.true_or]
      · rw [Bool.or_true, Bool.true_or, Bool.true_or]
    · rw [Bool.or_true, Bool.true_or, Bool.true_or, Bool.true_or]
  · rw [Bool.or_true, Bool.true_or, Bool.true_or, Bool.true_or, Bool.true_or]

theorem k5RowK_spec {D : Nat → Nat} {T Z i : Nat} (h : k5RowK D T Z i = true) :
    ∀ j < 23, pairK T Z (D i) (D j) = true := by
  intro j hj
  unfold k5RowK at h
  rw [Raw.Orb.strictB_eq] at h
  have := Raw.Orb.allN_iff.1 h j hj
  rwa [Raw.Orb.strictB_eq] at this

private theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · have hne : a ≠ b := fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
    simpa using hne
  · rw [Nat.eq_of_beq_eq_true h]
    simp

theorem fix1K_of {K : Nat} (h : fix1K K = true) : co3KFix1 (unpack 36 6 K) = true := by
  unfold fix1K at h
  obtain ⟨p, hp, hpa⟩ := anyNK_spec h
  unfold co3KFix1 anyLt allLt
  rw [nat_any_iff]
  refine ⟨p, hp, ?_⟩
  rw [nat_all_iff]
  intro i hi
  have hk := Raw.Orb.allN_iff.1 hpa i hi
  beta_reduce
  rw [Raw.Orb.unpack_get hi, beq_nat, beq_nat i p]
  cases e1 : Nat.beq (pg 6 (mask 6) K i) i <;> cases e2 : Nat.beq i p <;> rw [e1, e2] at hk <;>
    first | rfl | exact absurd hk (by decide)

end CFSG.KC.Co3K

end
