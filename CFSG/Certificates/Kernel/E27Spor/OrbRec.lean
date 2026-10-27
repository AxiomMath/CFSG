module

public import Certificates.Data.Kernel.E27Spor.OrbRec
public import CFSG.HardMathSupport.Foote.E27.OrbitF3
public import CFSG.Certificates.Kernel.E27Lie.Sound

public section

namespace CFSG.KS.E27Spor

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.E27Spor CFSG.KS.E27Lie
open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27.OrbitF3
open scoped Matrix

theorem lcode_decD : ∀ (d c : ℕ), lcode (decD d c) = c % 3 ^ d
  | 0, c => by simp [decD, lcode, Nat.mod_one]
  | d + 1, c => by
    have ih := lcode_decD d (c / 3)
    unfold lcode at ih ⊢
    rw [decD, List.foldr_cons, ih, pow_succ', Nat.mod_mul]

theorem validD_decD : ∀ (d c : ℕ), ValidD d (decD d c)
  | 0, c => ⟨rfl, by simp [decD]⟩
  | d + 1, c => by
    obtain ⟨h1, h2⟩ := validD_decD d (c / 3)
    refine ⟨by rw [decD, List.length_cons, h1], fun x hx => ?_⟩
    rw [decD, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by norm_num)
    · exact h2 x hx

theorem lcode_lt : ∀ {d : ℕ} {w : List ℕ}, ValidD d w → lcode w < 3 ^ d
  | 0, [], _ => by simp [lcode]
  | 0, _ :: _, h => absurd h.1 (by simp)
  | _ + 1, [], h => absurd h.1 (by simp)
  | d + 1, a :: w, h => by
    have hw : ValidD d w := ⟨by simpa using h.1, fun x hx => h.2 x (List.mem_cons_of_mem _ hx)⟩
    have ha := h.2 a (List.mem_cons_self ..)
    have ih := lcode_lt hw
    have e : lcode (a :: w) = a + 3 * lcode w := rfl
    rw [e, pow_succ']
    omega

theorem decD_lcode {d : ℕ} {w : List ℕ} (hw : ValidD d w) : decD d (lcode w) = w :=
  lcode_inj (validD_decD d _).2 hw.2 ((validD_decD d _).1.trans hw.1.symm)
    (by rw [lcode_decD, Nat.mod_eq_of_lt (lcode_lt hw)])

theorem inj_of_sortC {key s : ℕ → ℕ} {n : ℕ} (hs : ∀ q < n, sortC key s n q = true) :
    ∀ i < n, ∀ k < n, key i = key k → i = k := by
  have hs' : ∀ q < n, s q < n ∧ (q + 1 < n → key (s q) < key (s (q + 1))) := by
    intro q hq
    have h := hs q hq
    unfold sortC at h
    rw [sB_eq, bRec_eq] at h
    split_ifs at h with h1
    · rw [bRec_eq] at h
      refine ⟨blt_of h1, fun hq1 => ?_⟩
      rw [if_pos (Eq.mpr Nat.blt_eq hq1), sB_eq] at h
      exact blt_of h
  have mono : ∀ q q', q < q' → q' < n → key (s q) < key (s q') := by
    intro q q' hqq hq'
    induction q' with
    | zero => omega
    | succ q' ih =>
      rcases Nat.lt_or_ge q q' with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hs' q' (by omega)).2 hq')
      · have : q = q' := by omega
        subst this
        exact (hs' q (by omega)).2 hq'
  have sinj : ∀ q < n, ∀ q' < n, s q = s q' → q = q' := by
    intro q hq q' hq' e
    rcases Nat.lt_trichotomy q q' with h | h | h
    · have := mono q q' h hq'
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
    · exact h
    · have := mono q' q h hq
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
  have ssurj : ∀ i < n, ∃ q < n, s q = i := by
    let F : Fin n → Fin n := fun q => ⟨s q.val, (hs' q.val q.isLt).1⟩
    have hF : Function.Injective F := fun a b e =>
      Fin.ext (sinj a.val a.isLt b.val b.isLt (congrArg Fin.val e))
    intro i hi
    obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hF) ⟨i, hi⟩
    exact ⟨q.val, q.isLt, congrArg Fin.val hq⟩
  intro i hi k hk e
  obtain ⟨q, hq, rfl⟩ := ssurj i hi
  obtain ⟨q', hq', rfl⟩ := ssurj k hk
  have hqq : q = q' := by
    rcases Nat.lt_trichotomy q q' with h | h | h
    · exact absurd e (Nat.ne_of_lt (mono q q' h hq'))
    · exact h
    · exact absurd e.symm (Nat.ne_of_lt (mono q' q h hq))
  rw [hqq]

variable {d : ℕ} {gens : List (GL (Fin d) (ZMod 3))} {rows : List (List (List ℕ))}

theorem ncard_orbit_of_checks (hlen : gens.length = rows.length)
    (hrows : ∀ (i : ℕ) (h₁ : i < gens.length) (h₂ : i < rows.length),
      ((gens[i] : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) =
        rowsMat 3 d rows[i])
    {b : List ℕ} (hb : ValidD d b) {N : ℕ} (hN : 0 < N) {C pp pj s : ℕ → ℕ}
    {im : ℕ → ℕ → ℕ} (ht : ∀ i < N, orbTreeC d rows C pp pj (lcode b) i = true)
    (hi : ∀ i < N, orbImgC d rows C im N i = true) (hs : ∀ q < N, sortC C s N q = true) :
    (MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨rowsVec 3 d b⟩ : RowVD d)).ncard =
      N := by
  set K : Subgroup (GL (Fin d) (ZMod 3)) := Subgroup.closure {g | g ∈ gens} with hK
  set v : Fin d → ZMod 3 := rowsVec 3 d b with hv
  set V : ℕ → List ℕ := fun i => decD d (C i) with hV
  have hgen : ∀ t < rows.length, ∃ g ∈ K,
      (g : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d (rows.getD t []) := by
    intro t ht'
    have ht'' : t < gens.length := hlen ▸ ht'
    refine ⟨gens[t], Subgroup.subset_closure (List.getElem_mem ht''), ?_⟩
    rw [hrows t ht'' ht', List.getD_eq_getElem _ _ ht']
  have htree : ∀ i < N, C i < 3 ^ d ∧ (i = 0 → C 0 = lcode b) ∧
      (i ≠ 0 → pp i < i ∧ pj i < rows.length ∧
        C i = lcode (lvecMul 3 d (V (pp i)) (rows.getD (pj i) []))) := by
    intro i hiN
    have h := ht i hiN
    unfold orbTreeC at h
    rw [bRec_eq] at h
    split_ifs at h with h1
    rw [bRec_eq] at h
    have hC : C i < 3 ^ d := by rw [← Nat.pow_eq]; exact blt_of h1
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos (Nat.beq_refl 0)] at h
      exact ⟨hC, fun _ => beq_of h, fun h => absurd rfl h⟩
    · have hb0 : (Nat.beq i 0 = true) = False := by simp only [Nat.beq_eq, h0]
      rw [if_neg (by rw [hb0]; exact id), bRec_eq] at h
      split_ifs at h with h2
      rw [bRec_eq] at h
      split_ifs at h with h3
      exact ⟨hC, fun e => absurd e h0, fun _ => ⟨blt_of h2, blt_of h3, beq_of h⟩⟩
  have hVval : ∀ i, ValidD d (V i) := fun i => validD_decD d (C i)
  have hV0 : V 0 = b := by
    have := (htree 0 hN).2.1 rfl
    simp only [hV, this]
    exact decD_lcode hb
  have hVstep : ∀ i < N, i ≠ 0 → V i = lvecMul 3 d (V (pp i)) (rows.getD (pj i) []) := by
    intro i hiN h0
    obtain ⟨-, -, e⟩ := (htree i hiN).2.2 h0
    simp only [hV]
    rw [e]
    exact decD_lcode (validD_lvecMul _ _)
  have hreach : ∀ i < N, ∃ g ∈ K, rowsVec 3 d (V i) = v ᵥ* (g : Matrix (Fin d) (Fin d) (ZMod 3)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hiN
      by_cases h0 : i = 0
      · subst h0
        exact ⟨1, one_mem _, by rw [hV0, Units.val_one, Matrix.vecMul_one]⟩
      · obtain ⟨hpi, hpj, -⟩ := (htree i hiN).2.2 h0
        obtain ⟨g, hg, hgu⟩ := ih (pp i) hpi (by omega)
        obtain ⟨t, htK, htG⟩ := hgen (pj i) hpj
        refine ⟨g * t, mul_mem hg htK, ?_⟩
        rw [hVstep i hiN h0, rowsVec_lvecMul, hgu, Units.val_mul, ← Matrix.vecMul_vecMul, htG]
  have himg : ∀ i < N, ∀ t < rows.length, im t i < N ∧
      V (im t i) = lvecMul 3 d (V i) (rows.getD t []) := by
    intro i hiN t ht'
    have h := allN_spec (hi i hiN) t ht'
    rw [bRec_eq] at h
    split_ifs at h with h1
    refine ⟨blt_of h1, ?_⟩
    simp only [hV]
    rw [beq_of h]
    exact decD_lcode (validD_lvecMul _ _)
  have hCinj := inj_of_sortC hs
  have hinj : ∀ i < N, ∀ k < N, rowsVec 3 d (V i) = rowsVec 3 d (V k) → i = k := by
    intro i hiN k hkN e
    have e1 := rowsVec_injD (hVval i) (hVval k) e
    have e2 := congrArg lcode e1
    simp only [hV, lcode_decD, Nat.mod_eq_of_lt (htree i hiN).1,
      Nat.mod_eq_of_lt (htree k hkN).1] at e2
    exact hCinj i hiN k hkN e2
  let S : Set (Fin d → ZMod 3) := {u | ∃ i < N, u = rowsVec 3 d (V i)}
  have hclosed : ∀ u ∈ S, ∀ t < rows.length, u ᵥ* rowsMat 3 d (rows.getD t []) ∈ S := by
    rintro u ⟨i, hiN, rfl⟩ t ht'
    obtain ⟨hl, e⟩ := himg i hiN t ht'
    exact ⟨im t i, hl, by rw [e, rowsVec_lvecMul]⟩
  have hinv : ∀ g ∈ K, ∀ u ∈ S, u ᵥ* (g : Matrix (Fin d) (Fin d) (ZMod 3)) ∈ S := by
    intro g hg
    have hg' : g ∈ Submonoid.closure ({g | g ∈ gens} : Set (GL (Fin d) (ZMod 3))) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hg
    clear hg
    induction hg' using Submonoid.closure_induction with
    | mem t ht =>
      intro u hu
      obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ht
      have hi'' : i < rows.length := hlen ▸ hi'
      have := hclosed u hu i hi''
      rwa [List.getD_eq_getElem _ _ hi'', ← hrows i hi' hi''] at this
    | one => intro u hu; rwa [Units.val_one, Matrix.vecMul_one]
    | mul a c _ _ iha ihc =>
      intro u hu
      rw [Units.val_mul, ← Matrix.vecMul_vecMul]
      exact ihc _ (iha u hu)
  have hbS : v ∈ S := ⟨0, hN, by rw [hV0]⟩
  have horbit : {w : Fin d → ZMod 3 | ∃ g ∈ K, w = v ᵥ* (g : Matrix (Fin d) (Fin d) (ZMod 3))} =
      S := by
    ext u
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hinv g hg _ hbS
    · rintro ⟨i, hiN, rfl⟩
      obtain ⟨g, hg, e⟩ := hreach i hiN
      exact ⟨g, hg, e⟩
  have hncard : S.ncard = N := by
    have e : S = ↑((Finset.range N).image fun i => rowsVec 3 d (V i)) := by
      ext u
      simp only [S, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
        Set.mem_Iio]
      constructor
      · rintro ⟨i, hiN, rfl⟩; exact ⟨i, hiN, rfl⟩
      · rintro ⟨i, hiN, rfl⟩; exact ⟨i, hiN, rfl⟩
    rw [e, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
    intro i hiN k hkN h
    exact hinj i (Finset.mem_range.1 hiN) k (Finset.mem_range.1 hkN) h
  have himage : RowVD.vec '' MulAction.orbit K (⟨v⟩ : RowVD d) = S := by
    rw [← horbit]
    ext u
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨(g : GL (Fin d) (ZMod 3))⁻¹, inv_mem g.2, vec_smulD g _⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨(⟨g, hg⟩⁻¹ : K) • (⟨v⟩ : RowVD d), ⟨_, rfl⟩, ?_⟩
      rw [vec_smulD, Subgroup.coe_inv, inv_inv]
  rw [← Set.ncard_image_of_injective _ (fun a c h => RowVD.ext h), himage, hncard]

end CFSG.KS.E27Spor

end
