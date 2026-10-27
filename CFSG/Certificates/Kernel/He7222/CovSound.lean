module

public import Certificates.Data.Kernel.He7222.Cover
public import Batteries.Data.List.Basic
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.He7222.ChainSound
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KS.PF

@[expose] def CovLeaf (w m nf kt k1 ncl : ℕ) (CK : List (List ℕ)) (t0 c : ℕ) (S0 : List ℕ)
    (stack : List ℕ) (q : ℕ) : Prop :=
  q = c → invP w m (t0 :: stack) nf = true → keyN w m (t0 :: stack) nf ≠ kt →
    keyN w m (t0 :: stack) nf ≠ k1 → ∃ r ∈ S0, Nat.land r 255 < ncl ∧
      keyN w m (t0 :: stack) nf = getS (getLs CK (Nat.land r 255)) (Nat.shiftRight r 8)

theorem leafK_sound {w m nf kt k1 ncl : ℕ} {CK : List (List ℕ)} {ys st : List ℕ}
    {k : List ℕ → Bool} (h : leafK w m nf kt k1 ncl CK ys st k = true) :
    (∃ st', (∀ r ∈ st', r ∈ st) ∧ k st' = true) ∧
    (invP w m ys nf = true → keyN w m ys nf ≠ kt → keyN w m ys nf ≠ k1 → ∃ r ∈ st,
      Nat.land r 255 < ncl ∧
        keyN w m ys nf = getS (getLs CK (Nat.land r 255)) (Nat.shiftRight r 8)) := by
  unfold leafK at h
  rw [bIf_iff] at h
  rcases h with ⟨hi, h⟩ | ⟨hi, h⟩
  · rw [strictB_eqP] at h
    rw [bIf_iff] at h
    rcases h with ⟨hk, h⟩ | ⟨hk, h⟩
    · exact ⟨⟨st, fun r hr => hr, h⟩, fun _ hne => absurd (Nat.eq_of_beq_eq_true hk) hne⟩
    rw [bIf_iff] at h
    rcases h with ⟨hk1, h⟩ | ⟨hk1, h⟩
    · exact ⟨⟨st, fun r hr => hr, h⟩, fun _ _ hne => absurd (Nat.eq_of_beq_eq_true hk1) hne⟩
    cases st with
    | nil => exact absurd h (by simp)
    | cons r rest =>
      have h' : bAnd(Nat.blt (Nat.land r (nat_lit 255)) ncl,
          bAnd(Nat.beq (keyN w m ys nf) (getS (getLs CK (Nat.land r (nat_lit 255)))
            (Nat.shiftRight r (nat_lit 8))), k rest)) = true := h
      rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h'
      exact ⟨⟨rest, fun x hx => List.mem_cons_of_mem _ hx, h'.2.2⟩,
        fun _ _ _ => ⟨r, List.mem_cons_self, h'.1, Nat.eq_of_beq_eq_true h'.2.1⟩⟩
  · exact ⟨⟨st, fun r hr => hr, h⟩, fun h' => by rw [hi] at h'; exact absurd h' (by simp)⟩

@[expose] noncomputable def walkL (w m nf kt k1 ncl : ℕ) (CK : List (List ℕ)) (t0 c : ℕ)
    (Ls : List (List ℕ)) (q : ℕ) (stack : List ℕ) (lvl : List ℕ) :
    List ℕ → (List ℕ → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool)
    (fun st k => k st)
    (fun t _ ihT st k => strictB (pg w m t q) (fun q' =>
      walkK w m nf kt k1 ncl CK t0 c Ls q' (List.cons t stack) st (fun st' => ihT st' k)))
    lvl

theorem walkK_sound {w m nf kt k1 ncl : ℕ} {CK : List (List ℕ)} {t0 c : ℕ} {S0 : List ℕ} :
    ∀ (Ls : List (List ℕ)) (q : ℕ) (stack st : List ℕ) (k : List ℕ → Bool),
    (∀ r ∈ st, r ∈ S0) → walkK w m nf kt k1 ncl CK t0 c Ls q stack st k = true →
    (∃ st', (∀ r ∈ st', r ∈ S0) ∧ k st' = true) ∧ ∀ ts : List ℕ, List.Forall₂ (· ∈ ·) ts Ls →
      CovLeaf w m nf kt k1 ncl CK t0 c S0 (ts.reverse ++ stack)
        (ts.foldl (fun q t => pg w m t q) q) := by
  intro Ls
  induction Ls with
  | nil =>
    intro q stack st k hst h
    have h' : bIf(Nat.beq q c, leafK w m nf kt k1 ncl CK (List.cons t0 stack) st k, k st) =
      true := h
    rw [bIf_iff] at h'
    rcases h' with ⟨hq, hl⟩ | ⟨hq, hk⟩
    · obtain ⟨⟨st', hst', hk⟩, hleaf⟩ := leafK_sound hl
      refine ⟨⟨st', fun r hr => hst r (hst' r hr), hk⟩, fun ts hts => ?_⟩
      cases hts
      intro _ hi hkt hk1
      obtain ⟨r, hr, hcl, hkey⟩ := hleaf hi hkt hk1
      exact ⟨r, hst r hr, hcl, hkey⟩
    · refine ⟨⟨st, hst, hk⟩, fun ts hts => ?_⟩
      cases hts
      intro hqc
      have hqc' : q = c := hqc
      rw [hqc', Nat.beq_refl] at hq
      exact absurd hq (by simp)
  | cons lvl Ls ih =>
    intro q stack
    have inner : ∀ (lv : List ℕ) (st : List ℕ) (k : List ℕ → Bool), (∀ r ∈ st, r ∈ S0) →
        walkL w m nf kt k1 ncl CK t0 c Ls q stack lv st k = true →
        (∃ st', (∀ r ∈ st', r ∈ S0) ∧ k st' = true) ∧ ∀ t ∈ lv, ∀ ts : List ℕ,
          List.Forall₂ (· ∈ ·) ts Ls → CovLeaf w m nf kt k1 ncl CK t0 c S0
            (ts.reverse ++ t :: stack) (ts.foldl (fun q t => pg w m t q) (pg w m t q)) := by
      intro lv
      induction lv with
      | nil => exact fun st k hst h => ⟨⟨st, hst, h⟩, fun t ht => absurd ht List.not_mem_nil⟩
      | cons t lv ihl =>
        intro st k hst h
        have h' : strictB (pg w m t q) (fun q' => walkK w m nf kt k1 ncl CK t0 c Ls q'
            (List.cons t stack) st (fun st' => walkL w m nf kt k1 ncl CK t0 c Ls q stack lv st' k))
            = true := h
        rw [strictB_eqP (pg w m t q)] at h'
        obtain ⟨⟨st1, hst1, hk1⟩, hleaf1⟩ := ih (pg w m t q) (t :: stack) st _ hst h'
        obtain ⟨⟨st2, hst2, hk2⟩, hleaf2⟩ := ihl st1 k hst1 hk1
        refine ⟨⟨st2, hst2, hk2⟩, fun t' ht' => ?_⟩
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact hleaf1
        · exact hleaf2 t' ht'
    intro st k hst h
    obtain ⟨hk, hleaf⟩ := inner lvl st k hst h
    refine ⟨hk, fun ts hts => ?_⟩
    cases hts with
    | cons ht hts' =>
      rename_i t ts
      have := hleaf t ht ts hts'
      rw [List.reverse_cons, List.append_assoc, List.foldl_cons]
      exact this

theorem covK_sound {w m nf ncl tau : ℕ} {CK : List (List ℕ)} {b0 : ℕ} {T0 : List ℕ}
    {Ls : List (List ℕ)} {Cc : List ℕ} {Cov : List (List ℕ)} {i : ℕ}
    (h : covK w m nf ncl tau CK b0 T0 Ls Cc Cov i = true) :
    pg w m (getS T0 i) (getS Cc i) = b0 ∧ ∀ ts : List ℕ, List.Forall₂ (· ∈ ·) ts Ls →
      CovLeaf w m nf (keyN w m [tau] nf) (keyN w m [] nf) ncl CK (getS T0 i) (getS Cc i)
        (getLs Cov i) ts.reverse (ts.foldl (fun q t => pg w m t q) (pg w m (getS T0 i) b0)) := by
  unfold covK at h
  simp only [strictB_eqP] at h
  rw [bAnd_iff] at h
  obtain ⟨hb, hw⟩ := h
  obtain ⟨-, hleaf⟩ := walkK_sound Ls _ [] _ _ (fun r hr => hr) hw
  refine ⟨Nat.eq_of_beq_eq_true hb, fun ts hts => ?_⟩
  have := hleaf ts hts
  rw [List.append_nil] at this
  exact this

end CFSG.KC.HeChain

end
