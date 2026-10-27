module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE32Lift

public section

namespace CFSG.ComponentClassification.SolMax.NineE32

open Equiv Subgroup

variable {X : Type} [Group X] {H : Subgroup X} {φ : ↥H →* A9 × Multiplicative (ZMod 2)}
  {t : X}

namespace Frame

variable (F : Frame H φ t)
include F

@[expose] def Acts (y : X) (f : W → W) : Prop :=
  ∀ v : W, y * F.κ (Multiplicative.ofAdd v) * y⁻¹ = F.κ (Multiplicative.ofAdd (f v))

variable {F}

theorem Acts.mul {y y' : X} {f f' : W → W} (h : F.Acts y f) (h' : F.Acts y' f') :
    F.Acts (y * y') (f ∘ f') := by
  intro v
  rw [show y * y' * F.κ (Multiplicative.ofAdd v) * (y * y')⁻¹ =
    y * (y' * F.κ (Multiplicative.ofAdd v) * y'⁻¹) * y⁻¹ by group, h' v, h]
  rfl

theorem Acts.one : F.Acts 1 id := by
  intro v
  simp

theorem Acts.add {y : X} {f : W → W} (h : F.Acts y f) (v w : W) : f (v + w) = f v + f w := by
  apply Multiplicative.ofAdd.injective
  apply F.inj
  rw [← h, ofAdd_add, map_mul, ofAdd_add, map_mul, ← h, ← h]
  group

theorem Acts.injective {y : X} {f : W → W} (h : F.Acts y f) : Function.Injective f := by
  intro v w hvw
  have h1 := h v
  rw [hvw, ← h w] at h1
  have h2 : F.κ (Multiplicative.ofAdd v) = F.κ (Multiplicative.ofAdd w) := by
    have := congrArg (fun x => y⁻¹ * x * y) h1
    simpa [mul_assoc] using this
  exact Multiplicative.ofAdd.injective (F.inj h2)

theorem Acts.bijective {y : X} {f : W → W} (h : F.Acts y f) : Function.Bijective f :=
  Finite.injective_iff_bijective.mp h.injective

theorem Acts.inv {y : X} {f : W → W} (h : F.Acts y f) :
    F.Acts y⁻¹ ((Equiv.ofBijective f h.bijective).symm) := by
  intro v
  set g := (Equiv.ofBijective f h.bijective).symm
  have hg : f (g v) = v := (Equiv.ofBijective f h.bijective).apply_symm_apply v
  have h1 := h (g v)
  rw [hg] at h1
  rw [← h1]
  group

theorem Acts.conj_t {y : X} {f : W → W} (h : F.Acts y f) :
    y * t * y⁻¹ = F.κ (Multiplicative.ofAdd (f tW)) := by
  rw [← h tW, F.ht]

variable (F)

theorem exists_acts_gW [Finite X] (hφ : Function.Surjective φ) (i : Fin 4) :
    ∃ n ∈ H, F.Acts n (gW i) := by
  obtain ⟨n, hnH, hn⟩ := F.exists_normalizing hφ
    (y := ((⟨xPerm i, xPerm_mem i⟩ : A9), (1 : Multiplicative (ZMod 2))))
    (f := fun v => Multiplicative.ofAdd (gW i (Multiplicative.toAdd v))) (fun v => by
      refine Prod.ext (Subtype.ext ?_) ?_
      · simp only [Prod.fst_mul, Prod.fst_inv, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [enc_apply_fst, enc_apply_fst, xPerm_conj]
        rfl
      · simp only [Prod.snd_mul, Prod.snd_inv, one_mul, inv_one, mul_one]
        rw [enc_apply_snd, enc_apply_snd]
        simp only [toAdd_ofAdd]
        rw [gW_snd])
  exact ⟨n, hnH, fun v => hn (Multiplicative.ofAdd v)⟩

theorem acts_gWord [Finite X] (hφ : Function.Surjective φ) (w : List ℕ)
    (hw : ∀ i ∈ w, i < 4) : ∃ n : X, F.Acts n (gWord w) := by
  induction w with
  | nil => exact ⟨1, Acts.one⟩
  | cons i w ih =>
    obtain ⟨n₀, hn₀⟩ := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    obtain ⟨n₁, -, hn₁⟩ := F.exists_acts_gW hφ ⟨i, hw i (List.mem_cons_self ..)⟩
    exact ⟨n₁ * n₀, hn₁.mul hn₀⟩

@[expose] def orbitT : Set W := {v | ∃ (y : X) (f : W → W), F.Acts y f ∧ f tW = v}

theorem tW_mem_orbitT : tW ∈ F.orbitT := ⟨1, id, Acts.one, rfl⟩

variable {F}

theorem Acts.mem_orbitT {y : X} {f : W → W} (h : F.Acts y f) {v : W} (hv : v ∈ F.orbitT) :
    f v ∈ F.orbitT := by
  obtain ⟨y', f', h', rfl⟩ := hv
  exact ⟨y * y', f ∘ f', h.mul h', rfl⟩

theorem Acts.mem_orbitT_iff {y : X} {f : W → W} (h : F.Acts y f) (v : W) :
    f v ∈ F.orbitT ↔ v ∈ F.orbitT := by
  refine ⟨fun hv => ?_, h.mem_orbitT⟩
  have := h.inv.mem_orbitT hv
  rwa [Equiv.ofBijective_symm_apply_apply] at this

variable (F)

theorem orbitT_cases
    (hφt : ∀ htH : t ∈ H, φ ⟨t, htH⟩ = (1, Multiplicative.ofAdd 1))
    (hfour : ∀ (x : X) (hx : x ∈ H), x * t = t * x →
      ((φ ⟨x, hx⟩).1 : Perm (Fin 9)).support.card = 4 → ∀ g : X, g⁻¹ * t * g ≠ x)
    {v : W} (hv : v ∈ F.orbitT) : v = tW ∨ isM v ∨ isTM v := by
  obtain ⟨y, f, hf, rfl⟩ := hv
  have hconj := hf.conj_t
  rcases type_cases (f tW) with h0 | ht | h4 | hm | htm
  · exfalso
    rw [h0] at hconj
    have ht1 : t = 1 := by
      have : y * t * y⁻¹ = 1 := by rw [hconj]; exact map_one F.κ
      have := congrArg (fun x => y⁻¹ * x * y) this
      simpa [mul_assoc] using this
    have htH : t ∈ H := by rw [← F.ht]; exact F.mem _
    have h1 := hφt htH
    rw [show (⟨t, htH⟩ : ↥H) = 1 from Subtype.ext ht1, map_one] at h1
    exact absurd (congrArg Prod.snd h1) (by decide)
  · exact Or.inl ht
  · exfalso
    have hxH := F.mem (Multiplicative.ofAdd (f tW))
    refine hfour _ hxH ?_ ?_ y⁻¹ (by rw [inv_inv, hconj])
    · have h1 : F.κ (Multiplicative.ofAdd (f tW)) * F.κ (Multiplicative.ofAdd tW) =
          F.κ (Multiplicative.ofAdd tW) * F.κ (Multiplicative.ofAdd (f tW)) := by
        rw [← map_mul F.κ, ← map_mul F.κ, mul_comm (Multiplicative.ofAdd (f tW))]
      rwa [F.ht] at h1
    · rw [F.phi, enc_apply_fst]
      exact h4
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr htm)

theorem isM_mem_orbitT [Finite X] (hφ : Function.Surjective φ) {v : W} (hv : v ∈ F.orbitT)
    (hvM : isM v) {w : W} (hwM : isM w) : w ∈ F.orbitT := by
  obtain ⟨n, hn⟩ := F.acts_gWord hφ (wordAt wordsM v) (wordAt_lt _ wordsM_lt v)
  obtain ⟨n', hn'⟩ := F.acts_gWord hφ (wordAt wordsM w) (wordAt_lt _ wordsM_lt w)
  have hm : mW ∈ F.orbitT := by
    rw [← hn.mem_orbitT_iff, gWord_wordsM v hvM]
    exact hv
  have := hn'.mem_orbitT hm
  rwa [gWord_wordsM w hwM] at this

theorem isTM_mem_orbitT [Finite X] (hφ : Function.Surjective φ) {v : W} (hv : v ∈ F.orbitT)
    (hvM : isTM v) {w : W} (hwM : isTM w) : w ∈ F.orbitT := by
  obtain ⟨n, hn⟩ := F.acts_gWord hφ (wordAt wordsTM v) (wordAt_lt _ wordsTM_lt v)
  obtain ⟨n', hn'⟩ := F.acts_gWord hφ (wordAt wordsTM w) (wordAt_lt _ wordsTM_lt w)
  have hm : sW ∈ F.orbitT := by
    rw [← hn.mem_orbitT_iff, gWord_wordsTM v hvM]
    exact hv
  have := hn'.mem_orbitT hm
  rwa [gWord_wordsTM w hwM] at this

end Frame

theorem mask_ofMask : ∀ n : Fin 32, mask (ofMask n) = n := by decide

theorem mask_ofMask_lt {n : ℕ} (hn : n < 32) : mask (ofMask n) = n :=
  mask_ofMask ⟨n, hn⟩

theorem mask_lt : ∀ v : W, mask v < 32 := by decide

theorem xor_lt_32 {a b : ℕ} (ha : a < 32) (hb : b < 32) : a ^^^ b < 32 := by
  have := Nat.xor_lt_two_pow (n := 5) ha hb
  simpa using this

theorem foldl_lt (cols : List ℕ) (m : ℕ) :
    ∀ (l : List ℕ), (∀ k ∈ l, cols.getD k 0 < 32) → ∀ acc : ℕ, acc < 32 →
      l.foldl (fun acc k => if m.testBit k then acc ^^^ cols.getD k 0 else acc) acc < 32 := by
  intro l
  induction l with
  | nil => exact fun _ acc h => h
  | cons k l ih =>
    intro hl acc hacc
    simp only [List.foldl_cons]
    refine ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ ?_
    by_cases hk : m.testBit k = true
    · simp only [hk, ite_true]
      exact xor_lt_32 hacc (hl k (List.mem_cons_self ..))
    · simp only [hk]
      exact hacc

theorem applyCols_lt {cols : List ℕ} (hc : ∀ k < 5, cols.getD k 0 < 32) (m : ℕ) :
    applyCols cols m < 32 :=
  foldl_lt cols m _ (fun k hk => hc k (List.mem_range.mp hk)) 0 (by decide)

@[expose] def linW (cols : List ℕ) (v : W) : W := ofMask (applyCols cols (mask v))

@[expose] def evalWordW (cols : List ℕ) (w : List ℕ) (v : W) : W :=
  w.foldr (fun l acc => linW (letter cols l) acc) v

theorem gColsN_lt : ∀ l < 4, ∀ k < 5, (gColsN.getD l []).getD k 0 < 32 := by decide

theorem getD_letter_lt {cols : List ℕ} (hc : ∀ k < 5, cols.getD k 0 < 32) (l : ℕ) :
    ∀ k < 5, (letter cols l).getD k 0 < 32 := by
  unfold letter
  split_ifs with hl
  · exact gColsN_lt l hl
  · exact hc

theorem mask_evalWordW {cols : List ℕ} (hc : ∀ k < 5, cols.getD k 0 < 32) (w : List ℕ) (v : W) :
    mask (evalWordW cols w v) = evalWord cols w (mask v) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [evalWordW, evalWord, List.foldr_cons] at ih ⊢
    rw [linW, mask_ofMask_lt (applyCols_lt (getD_letter_lt hc l) _), ih]

namespace Frame

variable {F : Frame H φ t}

theorem Acts.eq_linW {y : X} {f : W → W} (h : F.Acts y f) :
    f = linW [mask (f (eW 0)), mask (f (eW 1)), mask (f (eW 2)), mask (f (eW 3)),
      mask (f (eW 4))] := by
  funext v
  rw [linW, ← mask_eq_applyCols f h.add, ofMask_mask]

theorem acts_evalWordW [Finite X] (hφ : Function.Surjective φ) {n : X} {cols : List ℕ}
    (hn : F.Acts n (linW cols)) (w : List ℕ) (hw : ∀ l ∈ w, l < 5) :
    ∃ y : X, F.Acts y (evalWordW cols w) := by
  induction w with
  | nil => exact ⟨1, Acts.one⟩
  | cons l w ih =>
    obtain ⟨y₀, hy₀⟩ := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    by_cases hl : l < 4
    · obtain ⟨n₁, -, hn₁⟩ := F.exists_acts_gW hφ ⟨l, hl⟩
      refine ⟨n₁ * y₀, ?_⟩
      have h := hn₁.mul hy₀
      have hlet : linW (letter cols l) = gW l := by
        funext v
        simp [linW, letter, hl, gW]
      have : evalWordW cols (l :: w) = gW l ∘ evalWordW cols w := by
        funext v
        simp only [evalWordW, List.foldr_cons, Function.comp_apply]
        rw [hlet]
      rw [this]
      exact h
    · refine ⟨n * y₀, ?_⟩
      have hlet : letter cols l = cols := by simp [letter, hl]
      have : evalWordW cols (l :: w) = linW cols ∘ evalWordW cols w := by
        funext v
        simp only [evalWordW, List.foldr_cons, Function.comp_apply, hlet]
      rw [this]
      exact hn.mul hy₀

end Frame

@[expose] def Otm (y : W) : Prop := y = tW ∨ isTM y

instance : DecidablePred Otm := fun y => by unfold Otm; infer_instance

theorem Otm_iff_mem : ∀ y : W, Otm y ↔ mask y ∈ oListN := by decide

theorem oListN_lt : ∀ o ∈ oListN, o < 32 := by decide

theorem oListN_nodup : oListN.Nodup := by decide

@[expose] def betaW (j : ℕ) : W := ofMask (betaN.getD j 0)

theorem betaW_zero : betaW 0 = sW := by decide

theorem Otm_betaW : ∀ j < 5, Otm (betaW j) := by decide

theorem eW_eq_sum : ∀ k < 5, eW k = (if (bInvN.getD k 0).testBit 0 then betaW 0 else 0) +
    (if (bInvN.getD k 0).testBit 1 then betaW 1 else 0) +
    (if (bInvN.getD k 0).testBit 2 then betaW 2 else 0) +
    (if (bInvN.getD k 0).testBit 3 then betaW 3 else 0) +
    (if (bInvN.getD k 0).testBit 4 then betaW 4 else 0) := by
  decide

theorem table_lt : ∀ e ∈ table, (∀ l ∈ e.2.1, l < 5) ∧ e.2.2 < 36 := by decide

theorem lookup_lt (u : List ℕ) : (∀ l ∈ (lookup u).1, l < 5) ∧ (lookup u).2 < 36 := by
  unfold lookup
  cases h : table.find? (fun e => e.1 == u) with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    exact table_lt e (List.mem_of_find?_eq_some h)

theorem digits_code (a b c d : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) :
    digits (a + 10 * b + 100 * c + 1000 * d) = [a, b, c, d] := by
  simp only [digits, List.cons.injEq, and_true]
  omega

theorem encPerm_eW : ∀ i : Fin 4, encPerm (eW i) = aPerm i := by decide

theorem mask_eW : ∀ i : Fin 4, mask (eW i) = 2 ^ (i : ℕ) := by decide

theorem mask_tW : mask tW = t₀N := by decide

end CFSG.ComponentClassification.SolMax.NineE32
