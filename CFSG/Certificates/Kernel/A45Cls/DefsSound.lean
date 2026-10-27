module

public import Certificates.Data.Kernel.A45Cls.Defs
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

theorem wordK_prep (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {G : Nat → Nat}
    {g : Nat → Equiv.Perm (Fin n)} : ∀ l : List Nat, (∀ k ∈ l, PRep n w (G k) (g k)) →
      PRep n w (wordK n w G l) (l.map g).prod
  | [], _ => prep_pidn hn hw
  | k :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact prep_pcomp (by omega) (h k List.mem_cons_self)
      (wordK_prep hn hw l fun j hj => h j (List.mem_cons_of_mem k hj))

theorem lettersK_spec {ng : Nat} : ∀ {l : List Nat}, lettersK ng l = true → ∀ k ∈ l, k < ng
  | [], _, k, hk => absurd hk List.not_mem_nil
  | j :: l, h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (lettersK ng l) (Nat.blt j ng) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Nat.blt_eq.mp h1
    · exact lettersK_spec h2 k hk

theorem bindWs_spec {ng : Nat} {G0 G : Nat → Nat} : ∀ {ws : List (List Nat)} {k : Nat},
    bindWs n w ng G0 G ws k = true → ∀ j (h : j < ws.length),
      (∀ q ∈ ws[j], q < ng) ∧ G (k + j) = wordK n w G0 ws[j]
  | [], _, _, j, h => absurd h (Nat.not_lt_zero j)
  | l :: ws, k, hb, j, h => by
    have hb' : Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (bindWs n w ng G0 G ws (Nat.succ k))
          (Nat.beq (G k) (wordK n w G0 l))) (lettersK ng l) = true := hb
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hb'
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    rcases j with _ | j
    · exact ⟨lettersK_spec h1, Nat.eq_of_beq_eq_true h2⟩
    · have := bindWs_spec h3 j (by simpa using h)
      rw [List.getElem_cons_succ, Nat.add_succ, ← Nat.succ_add]
      exact this

theorem cntN_eq (f : Nat → Bool) :
    ∀ m, cntN m f = ((Finset.range m).filter fun i => f i = true).card
  | 0 => rfl
  | m + 1 => by
    have e : cntN (m + 1) f =
        Bool.rec (motive := fun _ => Nat) (cntN m f) (Nat.succ (cntN m f)) (f m) := rfl
    rw [e, Finset.range_add_one, Finset.filter_insert, cntN_eq f m]
    cases hf : f m
    · rw [if_neg (by simp)]
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]

@[expose] def fixC (g : Equiv.Perm (Fin n)) : Nat := (Finset.univ.filter fun i => g i = i).card

theorem fixK_eq {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) : fixK n w P = fixC g := by
  rw [fixK, cntN_eq, fixC, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Nat.beq_eq]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨⟨a, ha⟩, Fin.ext ((hP ⟨a, ha⟩).symm.trans h), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.2, (hP i).trans ?_⟩
    rw [hi]

theorem fixC_conj (g h : Equiv.Perm (Fin n)) : fixC (h * g * h⁻¹) = fixC g := by
  unfold fixC
  refine Finset.card_bij (fun i _ => (h⁻¹ : Equiv.Perm (Fin n)) i) ?_ ?_ ?_
  · intro i hi
    have hi' : (h * g * h⁻¹) i = i := (Finset.mem_filter.1 hi).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hi'
    have := congrArg (h⁻¹ : Equiv.Perm (Fin n)) hi'
    simpa using this
  · intro a _ b _ e
    exact (h⁻¹ : Equiv.Perm (Fin n)).injective e
  · intro b hb
    have hb' : g b = b := (Finset.mem_filter.1 hb).2
    refine ⟨h b, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    simp [hb']

end CFSG.KC.A45Cls

end
