module

public import CFSG.Certificates.Kernel.Misc.O62SoundE8

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.Misc
open CFSG.KC.LQT.P (letB impB allN anyN allL anyL)
open CFSG.LargeExtraspecial.O62

theorem certK_cons_cons (p : ℕ × List ℕ) (ps : List (ℕ × List ℕ)) (F : ℕ) (t : List ℕ) :
    certK (p :: ps) (F :: t) = andB (nodup8 F) (andB (certOK8 F p.2) (certK ps t)) := rfl

theorem certK_cons_nil (p : ℕ × List ℕ) (ps : List (ℕ × List ℕ)) : certK (p :: ps) [] = false :=
  rfl

theorem certK_spec : ∀ (certs : List (ℕ × List ℕ)) (EP : List ℕ), certK certs EP = true →
    ∀ pF ∈ certs.zip EP, nodup8 pF.2 = true ∧ certOK8 pF.2 pF.1.2 = true
  | [], _, _, pF, hpF => by simp at hpF
  | p :: ps, [], h, _, _ => by rw [certK_cons_nil] at h; exact absurd h (by decide)
  | p :: ps, F :: t, h, pF, hpF => by
    rw [certK_cons_cons, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    rw [List.zip_cons_cons, List.mem_cons] at hpF
    rcases hpF with rfl | hpF
    · exact ⟨h.1, h.2.1⟩
    · exact certK_spec ps t h.2.2 pF hpF

@[expose] noncomputable def fitChk (m ev E kE : ℕ) (p : ℕ × List ℕ) (F : ℕ) : Bool :=
  andB (Nat.beq p.1 kE) (andB (allL p.2 (qBK m))
    (andB (impB (Nat.beq ev 1) (Nat.beq (parW p.2) 0)) (allN 8 fun i => mem8 F (e8 E i))))

@[expose] noncomputable def fitAux (m ev E kE : ℕ) (certs : List (ℕ × List ℕ)) (EP : List ℕ) :
    Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => false)
    (fun p _ ih EP => List.rec (motive := fun _ => Bool) false
      (fun F t _ => orB (fitChk m ev E kE p F) (ih t)) EP) certs EP

theorem fitK_eq (m ev E : ℕ) (certs : List (ℕ × List ℕ)) (EP : List ℕ) :
    fitK m ev E certs EP = fitAux m ev E (key8 E) certs EP := by
  unfold fitK
  rw [letB_eq]
  rfl

theorem fitAux_cons_cons (m ev E kE : ℕ) (p : ℕ × List ℕ) (ps : List (ℕ × List ℕ)) (F : ℕ)
    (t : List ℕ) : fitAux m ev E kE (p :: ps) (F :: t) =
      orB (fitChk m ev E kE p F) (fitAux m ev E kE ps t) := rfl

theorem fitAux_cons_nil (m ev E kE : ℕ) (p : ℕ × List ℕ) (ps : List (ℕ × List ℕ)) :
    fitAux m ev E kE (p :: ps) [] = false := rfl

theorem fitAux_spec (m ev E kE : ℕ) : ∀ (certs : List (ℕ × List ℕ)) (EP : List ℕ),
    fitAux m ev E kE certs EP = true →
    ∃ pF ∈ certs.zip EP, pF.1.1 = kE ∧ (∀ c ∈ pF.1.2, qBK m c = true) ∧
      (ev = 1 → parW pF.1.2 = 0) ∧ ∀ i < 8, mem8 pF.2 (e8 E i) = true
  | [], _, h => absurd h (by simp [fitAux])
  | p :: ps, [], h => by rw [fitAux_cons_nil] at h; exact absurd h (by decide)
  | p :: ps, F :: t, h => by
    rw [fitAux_cons_cons, orB_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · unfold fitChk at h
      simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, allL_eq, List.all_eq_true, impB_eq,
        Bool.or_eq_true, Bool.not_eq_true', allN_iff] at h
      refine ⟨(p, F), by simp [List.zip_cons_cons], h.1, h.2.1, ?_, h.2.2.2⟩
      intro hev
      rcases h.2.2.1 with h1 | h1
      · rw [hev] at h1; exact absurd h1 (by decide)
      · simpa using h1
    · obtain ⟨pF, hpF, rest⟩ := fitAux_spec m ev E kE ps t h
      exact ⟨pF, by simp [List.zip_cons_cons, hpF], rest⟩

theorem length_e8List (E : ℕ) : (e8List E).length = 8 := by simp [e8List]

theorem fit_cert {m ev x y z : ℕ} {certs : List (ℕ × List ℕ)} {EP : List ℕ}
    (hc : certK certs EP = true) (hnd : nodup8 (spanE x y z) = true)
    (hfit : fitK m ev (spanE x y z) certs EP = true) :
    ∃ p ∈ certs, p.1 = Check.keyOf (Check.spanC [z, y, x]) ∧ (∀ c ∈ p.2, qBK m c = true) ∧
      (ev = 1 → parW p.2 = 0) ∧ Check.certOK (Check.spanC [z, y, x]) p.2 = true := by
  rw [fitK_eq] at hfit
  obtain ⟨⟨p, F⟩, hpF, hkey, hq, hpar, hmem⟩ := fitAux_spec _ _ _ _ _ _ hfit
  obtain ⟨hFn, hFc⟩ := certK_spec certs EP hc (p, F) hpF
  have hpc : p ∈ certs := (List.of_mem_zip hpF).1
  refine ⟨p, hpc, ?_, hq, hpar, ?_⟩
  · have hkey' : p.1 = key8 (spanE x y z) := hkey
    rw [hkey', key8_eq, e8List_spanE, List.map_reverse, List.sum_reverse]
    rfl
  · have hE8 : (e8List (spanE x y z)).Nodup := (nodup8_iff _).1 hnd
    have hF8 : (e8List F).Nodup := (nodup8_iff _).1 hFn
    have hsub : e8List (spanE x y z) ⊆ e8List F := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      exact (mem8_iff _ _).1 (hmem i (List.mem_range.1 hi))
    have hperm := (hE8.subperm hsub).perm_of_length_le (by simp [length_e8List])
    have hset : ∀ a, a ∈ Check.spanC [z, y, x] ↔ a ∈ e8List F := by
      intro a
      rw [← hperm.mem_iff, e8List_spanE, List.mem_reverse]
    rw [certOK_congr hset]
    exact (certOK8_iff F p.2).1 hFc

end CFSG.KC.Misc.O62

end
