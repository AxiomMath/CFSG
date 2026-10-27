module

public import CFSG.Certificates.Kernel.TwistDce3.Walk

public section

namespace CFSG.Certificates.TwDce3.Fold

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
open CFSG.KC.TwDce3 CFSG.KC.YModel CFSG.Certificates.CosetEnumeration
open CFSG.Certificates.TwDce.Words hiding evP_eq isOne_spec wsMk_spec wsFail_lt dN1_lt dN2_lt
open CFSG.Certificates.TwDce.Core hiding wsBad_fail
open CFSG.Certificates.TwDce2.Words hiding evP_eq isOne_spec
open CFSG.Certificates.TwDce2.Walk hiding val_one2 val_eq_of_isOne2 step_core2 tStep_spec
  posStep_mk posStep_fail foldl_fail posStep_spec walk_list wR2 walkRun_eq walk_core walkOK_spec
open CFSG.Certificates.TwDce3.Walk

section Loop

variable {PB : ℕ} {F RD RW RA WD RJ : ℕ → ℕ} {INVM BS NB NT PSF PSB : ℕ}

theorem foldStep_eq (r S : ℕ) : foldStep PB F INVM BS NB NT PSF PSB RD RW RA WD RJ r S =
    if andB (Nat.blt 0 S) (andB (nodesOK S (RD r))
      (recOK PB F INVM BS NB NT PSF PSB RD RW RA WD r (RJ r))) = true
    then (if isTree (dKind (RD r)) = true then S + 1 else S) else 0 := by
  unfold foldStep
  rw [sN_eq, brec_eq, brec_eq]

theorem foldRange_succ (a n S : ℕ) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a (n + 1) S =
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ (a + 1) n
      (foldStep PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a S) := by
  unfold foldRange
  exact sN_eq _ _

theorem foldRange_snoc (n : ℕ) : ∀ a S,
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a (n + 1) S =
    foldStep PB F INVM BS NB NT PSF PSB RD RW RA WD RJ (a + n)
      (foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S) := by
  induction n with
  | zero => intro a S; rw [foldRange_succ]; rfl
  | succ n ih =>
    intro a S
    rw [foldRange_succ, ih, foldRange_succ, show a + 1 + n = a + (n + 1) by omega]

theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem nodesOK_parts {S d : ℕ} (h : nodesOK S d = true) :
    (dKind d = 0 → dN1 d < S ∧ dN2 d = S) ∧ (dKind d = 1 → dN1 d = S ∧ dN2 d < S) ∧
      (dKind d ≠ 0 → dKind d ≠ 1 → dN1 d < S ∧ dN2 d < S) := by
  simp only [nodesOK, sB_eq, brec_eq, kandB_iff] at h
  obtain ⟨-, h⟩ := h
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk0 hk1 => ?_⟩
  · rw [hk] at h
    simp only [show Nat.beq 0 0 = true from rfl, ↓reduceIte, kandB_iff] at h
    exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩
  · rw [hk] at h
    simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl, ↓reduceIte,
      Bool.false_eq_true, kandB_iff] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.blt_eq.mp h.2⟩
  · simp only [beq_f hk0, beq_f hk1, ↓reduceIte, Bool.false_eq_true, kandB_iff] at h
    exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2⟩

theorem recOK_parts {r J : ℕ} (h : recOK PB F INVM BS NB NT PSF PSB RD RW RA WD r J = true) :
    wBelow 12 (RW r) = true ∧ wBelow 12 (RA r) = true ∧
      (dKind (RD r) < 2 ∨
        (2 ≤ dKind (RD r) ∧ dKind (RD r) < 4 ∧
          walkOK PB F INVM BS NB NT PSF PSB RD RW RA WD r (RD r) J = true) ∨
        (dKind (RD r) = 4 ∧ dN1 (RD r) = 0 ∧ dN2 (RD r) = 0)) := by
  simp only [recOK, sB_eq, brec_eq, kandB_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split_ifs at h3 with hk2 hk4
  · exact Or.inl (Nat.blt_eq.mp hk2)
  · have : ¬ dKind (RD r) < 2 := fun h => hk2 (Nat.blt_eq.mpr h)
    exact Or.inr (Or.inl ⟨by omega, Nat.blt_eq.mp hk4, h3⟩)
  · simp only [kandB_iff] at h3
    exact Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true h3.1, Nat.eq_of_beq_eq_true h3.2.1,
      Nat.eq_of_beq_eq_true h3.2.2⟩)

end Loop

variable {G : Type*} [Group G]

theorem rh_congr {RD RW RA : ℕ → ℕ} {H : Subgroup G} {x : ℕ → G} {t : G}
    {X X' : ℕ → G} {f : ℕ} (h : RH RD RW RA H x t X f)
    (h1 : X' (dN1 (RD f)) = X (dN1 (RD f))) (h2 : X' (dN2 (RD f)) = X (dN2 (RD f))) :
    RH RD RW RA H x t X' f :=
  ⟨h.rw, h.ra, fun hk => by rw [h1, h2]; exact h.fact hk,
    fun hk3 hk5 => by rw [h1, h2]; exact h.eq hk3 hk5⟩

def Bnd (RD : ℕ → ℕ) (j S : ℕ) : Prop :=
  ∀ r < j, dKind (RD r) < 5 ∧ dN1 (RD r) < S ∧ dN2 (RD r) < S

theorem dce_fold {PB : ℕ} {F RD RW RA WD RJ : ℕ → ℕ} {INVM BS NB NT PSF PSB N C : ℕ}
    (hfold : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 N 1 = C) (hC : 0 < C)
    (H : Subgroup G) (x : ℕ → G) (t : G)
    (hxH : ∀ c < 12, x c ∈ H)
    (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12)
    (hTf : ∀ c < NT, thL PSF c < 12 ∧ x c * t = t * x (thL PSF c))
    (hTb : ∀ c < NT, thL PSB c < 12 ∧ x c * t⁻¹ = t⁻¹ * x (thL PSB c))
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    (hWD : ∀ i < 4096, wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ lst (WD i), c < 15) ∧
      evalWord v (lst (WD i)) = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (hlen : ∀ r < N, wLen (RW r) < 2 ^ 16 ∧ wLen (RA r) < 2 ^ 16) :
    ∃ X : ℕ → G, X 0 = 1 ∧ ∀ r < N, dKind (RD r) < 5 ∧ dN1 (RD r) < C ∧ dN2 (RD r) < C ∧
      (dKind (RD r) < 3 →
        CE H (X (dN1 (RD r)) * val x (RW r) * t) (X (dN2 (RD r)) * val x (RA r))) ∧
      (3 ≤ dKind (RD r) → CE H (X (dN1 (RD r))) (X (dN2 (RD r)) * val x (RW r))) := by
  have inv : ∀ j ≤ N, 0 < foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 j 1 →
      ∃ X : ℕ → G, X 0 = 1 ∧ Hist2 RD RW RA H x t X j ∧
        Bnd RD j (foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 j 1) := by
    intro j
    induction j with
    | zero =>
      intro _ _
      exact ⟨fun _ => 1, rfl, fun f hf => absurd hf (Nat.not_lt_zero _),
        fun r hr => absurd hr (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj hS'
      rw [foldRange_snoc, zero_add] at hS' ⊢
      set S := foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 j 1 with hSdef
      rw [foldStep_eq] at hS' ⊢
      split_ifs at hS' ⊢ with hc hk
      · simp only [kandB_iff] at hc
        obtain ⟨hS0, hn, hrec⟩ := hc
        obtain ⟨X, hX0, hH, hB⟩ := ih (by omega) (Nat.blt_eq.mp hS0)
        have hk' : dKind (RD j) < 2 := Nat.blt_eq.mp hk
        obtain ⟨hn0, hn1, -⟩ := nodesOK_parts hn
        obtain ⟨hiw, hia, -⟩ := recOK_parts hrec
        have hRW : GD (2 ^ 16) (RW j) := ⟨(wBelow_spec hiw).1, (wBelow_spec hiw).2, (hlen j hj).1⟩
        have hRA : GD (2 ^ 16) (RA j) := ⟨(wBelow_spec hia).1, (wBelow_spec hia).2, (hlen j hj).2⟩
        have hS0' : 0 < S := Nat.blt_eq.mp hS0
        have hbnd : ∀ r < j + 1, dKind (RD r) < 5 ∧ dN1 (RD r) < S + 1 ∧ dN2 (RD r) < S + 1 := by
          intro r hr
          rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
          · exact ⟨(hB r hr).1, by have := (hB r hr).2.1; omega, by have := (hB r hr).2.2; omega⟩
          · obtain hk0 | hk1 : dKind (RD r) = 0 ∨ dKind (RD r) = 1 := by omega
            · have := hn0 hk0; exact ⟨by omega, by omega, by omega⟩
            · have := hn1 hk1; exact ⟨by omega, by omega, by omega⟩
        obtain hk0 | hk1 : dKind (RD j) = 0 ∨ dKind (RD j) = 1 := by omega
        · obtain ⟨hn1', hn2'⟩ := hn0 hk0
          let X' := Function.update X S (X (dN1 (RD j)) * val x (RW j) * t * (val x (RA j))⁻¹)
          have hX'lt : ∀ n < S, X' n = X n := fun n hn => Function.update_of_ne (by omega) _ _
          refine ⟨X', by rw [hX'lt 0 hS0', hX0], fun f hf => ?_, hbnd⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hf | rfl
          · exact rh_congr (hH f hf) (hX'lt _ (hB f hf).2.1) (hX'lt _ (hB f hf).2.2)
          · refine ⟨hRW, hRA, fun _ => ?_, fun hk3 => absurd hk3 (by omega)⟩
            rw [hX'lt _ hn1', hn2']
            change CE H _ (Function.update X S _ S * _)
            rw [Function.update_self]
            exact CE.of_eq (by group)
        · obtain ⟨hn1', hn2'⟩ := hn1 hk1
          let X' := Function.update X S (X (dN2 (RD j)) * val x (RA j) * t⁻¹ * (val x (RW j))⁻¹)
          have hX'lt : ∀ n < S, X' n = X n := fun n hn => Function.update_of_ne (by omega) _ _
          refine ⟨X', by rw [hX'lt 0 hS0', hX0], fun f hf => ?_, hbnd⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hf | rfl
          · exact rh_congr (hH f hf) (hX'lt _ (hB f hf).2.1) (hX'lt _ (hB f hf).2.2)
          · refine ⟨hRW, hRA, fun _ => ?_, fun hk3 => absurd hk3 (by omega)⟩
            rw [hX'lt _ hn2', hn1']
            change CE H (Function.update X S _ S * _ * t) _
            rw [Function.update_self]
            exact CE.of_eq (by group)
      · simp only [kandB_iff] at hc
        obtain ⟨hS0, hn, hrec⟩ := hc
        obtain ⟨X, hX0, hH, hB⟩ := ih (by omega) (Nat.blt_eq.mp hS0)
        have hk' : ¬ dKind (RD j) < 2 := fun h => hk (Nat.blt_eq.mpr h)
        obtain ⟨-, -, hnn⟩ := nodesOK_parts hn
        obtain ⟨hn1, hn2⟩ := hnn (by omega) (by omega)
        obtain ⟨hiw, hia, hcase⟩ := recOK_parts hrec
        have hRW : GD (2 ^ 16) (RW j) := ⟨(wBelow_spec hiw).1, (wBelow_spec hiw).2, (hlen j hj).1⟩
        have hRA : GD (2 ^ 16) (RA j) := ⟨(wBelow_spec hia).1, (wBelow_spec hia).2, (hlen j hj).2⟩
        have hW := fun (hw : walkOK PB F INVM BS NB NT PSF PSB RD RW RA WD j (RD j) (RJ j) = true) =>
          walkOK_spec PB F RD RW RA WD INVM BS NB NT PSF PSB H x t hinv hNT hTf hTb hone v hv hv12
            hv13 hv14 hWD hH hRW hRA hw
        have hR : RH RD RW RA H x t X j := by
          refine ⟨hRW, hRA, fun hk3 => ?_, fun hk3 hk5 => ?_⟩
          · rcases hcase with h | ⟨-, -, hw⟩ | ⟨h4, -, -⟩
            · omega
            · rcases hW hw with ⟨-, hf⟩ | ⟨h3, -⟩
              · exact hf
              · omega
            · omega
          · rcases hcase with h | ⟨-, -, hw⟩ | ⟨-, h01, h02⟩
            · omega
            · rcases hW hw with ⟨h2, -⟩ | ⟨-, he⟩
              · omega
              · exact he
            · unfold CE
              rw [h01, h02, hX0, one_mul, one_mul]
              exact H.inv_mem (evalWord_mem12 hxH hRW.lt)
        refine ⟨X, hX0, fun f hf => ?_, fun r hr => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hf | rfl
          · exact hH f hf
          · exact hR
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
          · exact hB r hr
          · refine ⟨?_, hn1, hn2⟩
            rcases hcase with h | ⟨-, h, -⟩ | ⟨h, -, -⟩ <;> omega
      · exact absurd hS' (lt_irrefl 0)
  obtain ⟨X, hX0, hH, hB⟩ := inv N le_rfl (hfold ▸ hC)
  rw [hfold] at hB
  exact ⟨X, hX0, fun r hr => ⟨(hB r hr).1, (hB r hr).2.1, (hB r hr).2.2,
    fun hk => (hH r hr).fact hk, fun hk3 => (hH r hr).eq hk3 (hB r hr).1⟩⟩

end CFSG.Certificates.TwDce3.Fold

end
