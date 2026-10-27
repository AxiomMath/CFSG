module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.PresentationLetters
public import CFSG.Certificates.WordPresentation
import CFSG.Certificates.Kernel.Misc.Coset.ActSound

public section

namespace CFSG.KC.MiscCoset.Act

open CFSG.Certificates.CosetEnumeration

@[expose] def Rep (A : ℕ → ℕ) (m N : ℕ) (σ : Fin m → Equiv.Perm (Fin N)) : Prop :=
  ∀ g : Fin m, ∀ x : Fin N, A (x.val * (m + m) + 2 * g.val) = (σ g x).val ∧
    A (x.val * (m + m) + (2 * g.val + 1)) = ((σ g)⁻¹ x).val

@[expose] def revCodes {m : ℕ} (w : List (Fin m × Bool)) : List ℕ := (w.map letterCode).reverse

theorem walk_revCodes {m N : ℕ} {σ : Fin m → Equiv.Perm (Fin N)} {A : ℕ → ℕ}
    (hA : Rep A m N σ) (v : List (Fin m × Bool)) (x : Fin N) :
    walk A (Nat.add m m) (revCodes v) x.val = (CFSG.Certificates.signedProd σ v x).val := by
  have hwalk : ∀ (v : List ℕ) (c : ℕ) (x : ℕ), walk A (Nat.add m m) (v ++ [c]) x =
      step A (Nat.add m m) (walk A (Nat.add m m) v x) c := by
    intro v
    induction v with
    | nil => intro c x; rfl
    | cons d v ih => intro c x; exact ih c _
  induction v generalizing x with
  | nil => rfl
  | cons l v ih =>
    rw [revCodes, List.map_cons, List.reverse_cons, ← revCodes, hwalk, ih,
      CFSG.Certificates.signedProd_cons, Equiv.Perm.mul_apply]
    obtain ⟨g, b⟩ := l
    cases b
    · exact (hA g _).2
    · have := (hA g (CFSG.Certificates.signedProd σ v x)).1
      simpa [step, letterCode] using this

theorem relsAt_sound {m N : ℕ} {σ : Fin m → Equiv.Perm (Fin N)} {A : ℕ → ℕ} (hA : Rep A m N σ)
    (ws : List (List (Fin m × Bool))) {rels : List (List ℕ)} (hrels : ws.map revCodes = rels)
    (h : ∀ x < N, relsAt A (Nat.add m m) rels x = true) :
    ∀ w ∈ ws, CFSG.Certificates.signedProd σ w = 1 := by
  intro w hw
  ext x
  rw [← walk_revCodes hA w x]
  exact relsAt_spec (h x.val x.isLt) _ (hrels ▸ List.mem_map_of_mem hw)

theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

theorem nthW_eq : ∀ (ws : List (List ℕ)) (i : ℕ), nthW ws i = ws.getD i []
  | [], _ => by rw [List.getD_nil]; rfl
  | _ :: _, 0 => by rw [List.getD_cons_zero]; rfl
  | _ :: ws, i + 1 => by rw [List.getD_cons_succ]; exact nthW_eq ws i

theorem keyRec_eq (A : ℕ → ℕ) (L N : ℕ) (w : List ℕ) : ∀ (base : List ℕ) (acc : ℕ),
    List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun b _ ih acc => ih (Nat.add (Nat.mul acc N) (walk A L w b))) base acc =
      (base.map (walk A L w)).foldl (fun acc x => acc * N + x) acc
  | [], _ => rfl
  | b :: base, acc => keyRec_eq A L N w base (acc * N + walk A L w b)

theorem keyOf_eq (A : ℕ → ℕ) (L N : ℕ) (w base : List ℕ) :
    keyOf A L N w base = (base.map (walk A L w)).foldl (fun acc x => acc * N + x) 0 :=
  keyRec_eq A L N w base 0

theorem base_lt {N : ℕ} : ∀ base : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun b _ ih => andB (Nat.blt b N) ih) base = true →
    ∀ b ∈ base, b < N
  | [], _ => fun b hb => absurd hb List.not_mem_nil
  | b :: base, h => by
    have h' : andB (Nat.blt b N) (List.rec (motive := fun _ => Bool) true
        (fun b _ ih => andB (Nat.blt b N) ih) base) = true := h
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h'.1
    · exact base_lt base h'.2 c hc

theorem keysInc_spec {A : ℕ → ℕ} {L N : ℕ} {ws : List (List ℕ)} {base : List ℕ} :
    ∀ (ord : List ℕ) (p : ℕ), keysInc A L N ws base ord p = true →
      (∀ i ∈ ord, i < lenL ws ∧ p ≤ keyOf A L N (nthW ws i) base) ∧
        ord.Pairwise (fun a b => keyOf A L N (nthW ws a) base < keyOf A L N (nthW ws b) base)
  | [], _, _ => ⟨fun i hi => absurd hi List.not_mem_nil, List.Pairwise.nil⟩
  | i :: ord, p, h => by
    have h' : andB (Nat.blt i (lenL ws))
        (andB (Nat.blt p (Nat.succ (keyOf A L N (nthW ws i) base)))
          (keysInc A L N ws base ord (Nat.succ (keyOf A L N (nthW ws i) base)))) = true := h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := keysInc_spec ord _ h3
    refine ⟨fun j hj => ?_, List.Pairwise.cons (fun j hj => ?_) ih2⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact ⟨h1, by omega⟩
      · have := (ih1 j hj).2
        exact ⟨(ih1 j hj).1, by omega⟩
    · have := (ih1 j hj).2
      omega

theorem distinctOK_sound {m N : ℕ} {σ : Fin m → Equiv.Perm (Fin N)} {A : ℕ → ℕ}
    (hA : Rep A m N σ) (ws : List (List (Fin m × Bool))) {rels : List (List ℕ)}
    (hrels : ws.map revCodes = rels) {base ord : List ℕ}
    (h : distinctOK A (Nat.add m m) N rels base ord = true) :
    ∀ i j : ℕ, ∀ (hi : i < ws.length) (hj : j < ws.length),
      CFSG.Certificates.signedProd σ ws[i] = CFSG.Certificates.signedProd σ ws[j] → i = j := by
  unfold distinctOK at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hb, hl, hk⟩ := h
  have hbase := base_lt base hb
  have hlr : lenL rels = ws.length := by rw [lenL_eq, ← hrels, List.length_map]
  have hlen : ord.length = ws.length := by
    have := Nat.eq_of_beq_eq_true hl
    rwa [lenL_eq, hlr] at this
  obtain ⟨hmem, hpw⟩ := keysInc_spec ord 0 hk
  have hmap : (ord.map fun a => keyOf A (Nat.add m m) N (nthW rels a) base).Nodup :=
    (List.pairwise_map.2 hpw).imp (fun h => Nat.ne_of_lt h)
  have hnd : ord.Nodup := List.Nodup.of_map _ hmap
  have hall : ∀ i < ws.length, i ∈ ord := by
    intro i hi
    have hsub : ord.toFinset ⊆ Finset.range ws.length := fun x hx => by
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_range, ← hlr]
      exact (hmem x hx).1
    have hcard : (Finset.range ws.length).card ≤ ord.toFinset.card := by
      rw [Finset.card_range, List.toFinset_card_of_nodup hnd, hlen]
    rw [← List.mem_toFinset, Finset.eq_of_subset_of_card_le hsub hcard, Finset.mem_range]
    exact hi
  intro i j hi hj he
  refine List.inj_on_of_nodup_map hmap (hall i hi) (hall j hj) ?_
  have hri : nthW rels i = revCodes ws[i] := by
    rw [nthW_eq, ← hrels, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
      Option.getD_some, List.getElem_map]
  have hrj : nthW rels j = revCodes ws[j] := by
    rw [nthW_eq, ← hrels, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj),
      Option.getD_some, List.getElem_map]
  change keyOf A (Nat.add m m) N (nthW rels i) base = keyOf A (Nat.add m m) N (nthW rels j) base
  rw [hri, hrj, keyOf_eq, keyOf_eq]
  congr 1
  apply List.map_congr_left
  intro b hbm
  have e1 := walk_revCodes hA ws[i] ⟨b, hbase b hbm⟩
  have e2 := walk_revCodes hA ws[j] ⟨b, hbase b hbm⟩
  rw [he] at e1
  exact e1.trans e2.symm

end CFSG.KC.MiscCoset.Act

end
