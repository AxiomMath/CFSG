module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9E1
public import Certificates.Certificate26752

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def E1L : Subgroup HSCover := closure {bet 0, bet 1, bet 2, tL}

@[expose] def fsOf (l : List ℕ) : Finset (Fin 3850) := Finset.univ.filter fun i => i.val ∈ l

section Orbit

theorem harX_rep_pi (i : Fin 6) :
    Rep 3850 (harX i) ((harPiHom (PresentedGroup.of i) : ↥hsP) : Equiv.Perm (Fin 3850)) := by
  rw [harPiHom_of]
  exact (rep_harX i).1

theorem harPiHom_hsGens : hsGens.map harPiHom0 = harXs.map (tp 3850) := by
  simp [hsGens, harXs, List.map_map, Function.comp_def, harPiHom0_of, tp_harX]

theorem rep_pi_wordVal (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) :
    Rep 3850 (wordTbl 3850 harXs w)
      ((harPiHom (wordVal hsGens w) : ↥hsP) : Equiv.Perm (Fin 3850)) := by
  have hr := rep_wordTbl'' (n := 3850) (by norm_num) harXs_perm w (by
    have : harXs.length = 6 := rfl
    rw [this]
    exact hw)
  rw [harPiHom_coe, map_wordVal, harPiHom_hsGens]
  exact hr

theorem card_stabilizer_le {P : Subgroup (Equiv.Perm (Fin 3850))} [Finite P]
    (S : Finset (Fin 3850)) (l : List (Finset (Fin 3850))) (hl : l.Nodup)
    (hmem : ∀ s ∈ l, ∃ g : P, g • S = s) :
    l.length * Nat.card (MulAction.stabilizer P S) ≤ Nat.card P := by
  have h1 := MulAction.index_stabilizer P S
  have h2 := (MulAction.stabilizer P S).card_mul_index
  have hsub : (l.toFinset : Set (Finset (Fin 3850))) ⊆ MulAction.orbit P S := by
    intro s hs
    obtain ⟨g, hg⟩ := hmem s (List.mem_toFinset.1 hs)
    exact ⟨g, hg⟩
  have hle : l.length ≤ (MulAction.orbit P S).ncard := by
    calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hl).symm
      _ = (l.toFinset : Set (Finset (Fin 3850))).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit P S).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h1] at h2
  calc l.length * Nat.card (MulAction.stabilizer P S)
      ≤ (MulAction.orbit P S).ncard * Nat.card (MulAction.stabilizer P S) :=
        Nat.mul_le_mul_right _ hle
    _ = Nat.card P := by rw [mul_comm]; exact h2

theorem mem_smul_fsOf {P : Subgroup (Equiv.Perm (Fin 3850))} (g : P) (l : List ℕ)
    (i : Fin 3850) : i ∈ g • fsOf l ↔ ((g⁻¹ : P) • i).val ∈ l := by
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [fsOf] using hy
  · intro h
    refine ⟨(g⁻¹ : P) • i, by simpa [fsOf] using h, ?_⟩
    simp

theorem fsOf_imgList {P : Subgroup (Equiv.Perm (Fin 3850))} (g : P) {T : Table}
    (hT : Rep 3850 T (g : Equiv.Perm (Fin 3850))) {l : List ℕ} (hl : ∀ x ∈ l, x < 3850) :
    fsOf (imgList T l) = g • fsOf l := by
  ext i
  rw [mem_smul_fsOf]
  simp only [fsOf, imgList, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map]
  constructor
  · rintro ⟨x, hx, hxi⟩
    have hx3 := hl x hx
    have h1 : ap T x = ((g : Equiv.Perm (Fin 3850)) ⟨x, hx3⟩).val := by
      rw [hT x hx3, idx_of_lt _ hx3]
      rfl
    rw [h1] at hxi
    have h2 : (g : Equiv.Perm (Fin 3850)) ⟨x, hx3⟩ = i := Fin.ext hxi
    have h3 : ((g⁻¹ : P) • i) = ⟨x, hx3⟩ := by
      rw [← h2]
      simp [Subgroup.smul_def]
    rw [h3]
    exact hx
  · intro hmem
    refine ⟨((g⁻¹ : P) • i).val, hmem, ?_⟩
    have hx3 : ((g⁻¹ : P) • i).val < 3850 := ((g⁻¹ : P) • i).isLt
    rw [hT _ hx3, idx_of_lt _ hx3]
    simp [Subgroup.smul_def]

end Orbit

section BFS

@[expose] def OrbInv (S : List ℕ) (a : Array (List ℕ)) : Prop :=
  ∀ i, (h : i < a.size) →
    (∀ x ∈ a[i], x < 3850) ∧ ∃ g : ↥hsP, fsOf a[i] = g • fsOf S

theorem foldl_orbitStep_none (l : List (ℕ × ℕ)) : l.foldl orbitStep none = none := by
  induction l with
  | nil => rfl
  | cons st rest ih => exact ih

theorem harXs_getD (k : ℕ) (hk : k < 6) : harXs.getD k (idT 3850) = harX ⟨k, hk⟩ := by
  have hlen : harXs.length = 6 := rfl
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp [harXs]

theorem orbInv_step {S : List ℕ} {a a' : Array (List ℕ)} (ha : OrbInv S a) {st : ℕ × ℕ}
    (h : orbitStep (some a) st = some a') : OrbInv S a' := by
  unfold orbitStep at h
  simp only at h
  split at h
  · rename_i hc
    cases h
    intro i hi
    rw [Array.size_push] at hi
    by_cases hia : i < a.size
    · rw [Array.getElem_push_lt hia]
      exact ha i hia
    · have hi' : i = a.size := by omega
      subst hi'
      rw [Array.getElem_push_eq]
      obtain ⟨hlt, g₀, hg₀⟩ := ha st.1 hc.1
      rw [harXs_getD _ hc.2]
      have hgen := harX_rep_pi (⟨st.2, hc.2⟩ : Fin 6)
      set g : ↥hsP := harPiHom (PresentedGroup.of (⟨st.2, hc.2⟩ : Fin 6)) with hg
      refine ⟨?_, g * g₀, ?_⟩
      · intro x hx
        simp only [imgList, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hy3 := hlt y hy
        rw [hgen y hy3]
        exact idx_lt _ hy3
      · rw [fsOf_imgList g hgen hlt, hg₀, smul_smul]
  · cases h

theorem orbInv_foldl (S : List ℕ) (steps : List (ℕ × ℕ)) :
    ∀ (a a' : Array (List ℕ)), OrbInv S a → steps.foldl orbitStep (some a) = some a' →
      OrbInv S a' := by
  induction steps with
  | nil =>
    intro a a' ha h
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ha
  | cons st rest ih =>
    intro a a' ha h
    simp only [List.foldl_cons] at h
    cases hs : orbitStep (some a) st with
    | none =>
      rw [hs, foldl_orbitStep_none] at h
      cases h
    | some a₁ =>
      rw [hs] at h
      exact ih a₁ a' (orbInv_step ha hs) h

theorem lt_of_mem_sigmaPts {x : ℕ} (hx : x ∈ sigmaPts) : x < 3850 := by
  unfold sigmaPts at hx
  exact List.mem_range.1 (List.mem_of_mem_filter hx)

theorem orbInv_init (S : List ℕ) (hS : ∀ x ∈ S, x < 3850) : OrbInv S #[S] := by
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  exact ⟨fun x hx => hS x hx, 1, (one_smul ↥hsP _).symm⟩

end BFS

theorem mem_fsOf_iff {l : List ℕ} {i : Fin 3850} : i ∈ fsOf l ↔ i.val ∈ l := by
  simp [fsOf]

theorem setKey_eq_of_fsOf_eq {x y : List ℕ} (h : fsOf x = fsOf y) : setKey x = setKey y := by
  have hc : canonList x = canonList y := by
    unfold canonList
    apply List.filter_congr
    intro p hp
    have hp3 : p < 3850 := List.mem_range.1 hp
    have h1 : (⟨p, hp3⟩ : Fin 3850) ∈ fsOf x ↔ (⟨p, hp3⟩ : Fin 3850) ∈ fsOf y := by rw [h]
    rw [mem_fsOf_iff, mem_fsOf_iff] at h1
    rw [Bool.eq_iff_iff]
    simpa using h1
  unfold setKey
  rw [hc]

section Final

theorem exists_orbit_list : ∃ l : List (Finset (Fin 3850)), l.length = 4125 ∧ l.Nodup ∧
    ∀ s ∈ l, ∃ g : ↥hsP, g • fsOf sigmaPts = s := by
  have hok := Certificates.certificate26752
  unfold orbitOK at hok
  cases hsets : orbitSets with
  | none =>
    rw [hsets] at hok
    exact absurd hok (by simp)
  | some a =>
    rw [hsets] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hsize, -⟩, hsort⟩ := hok
    have hinv : OrbInv sigmaPts a := by
      unfold orbitSets at hsets
      exact orbInv_foldl sigmaPts orbitSteps #[sigmaPts] a
        (orbInv_init _ (fun x hx => lt_of_mem_sigmaPts hx)) hsets
    refine ⟨a.toList.map fsOf, ?_, ?_, ?_⟩
    · simp [hsize]
    · have hsorted := (pairwise_of_strictlyIncreasing hsort).imp (fun hab => Nat.ne_of_lt hab)
      have hkeys : (a.toList.map setKey).Nodup :=
        (List.mergeSort_perm _ _).nodup_iff.1 hsorted
      rw [List.Nodup, List.pairwise_map] at hkeys ⊢
      refine hkeys.imp_of_mem fun {x y} hx hy hne h => hne ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      have hi' : i < a.size := by simpa using hi
      have hj' : j < a.size := by simpa using hj
      exact setKey_eq_of_fsOf_eq h
    · intro s hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi' : i < a.size := by simpa using hi
      obtain ⟨g, hg⟩ := (hinv i hi').2
      exact ⟨g, by simpa [Array.getElem_toList] using hg.symm⟩

theorem card_stabilizer_sigma_le :
    Nat.card (MulAction.stabilizer ↥hsP (fsOf sigmaPts)) ≤ 10752 := by
  obtain ⟨l, hlen, hnd, hmem⟩ := exists_orbit_list
  have h := card_stabilizer_le (P := hsP) (fsOf sigmaPts) l hnd hmem
  rw [hlen, card_hsP] at h
  omega

end Final

theorem sq_mem_closure_sq {M : Type*} [Group M] {s : Set M}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) {x : M} (hx : x ∈ Subgroup.closure s) :
    x * x ∈ Subgroup.closure ((fun a => a * a) '' s) := by
  have hpw : s.Pairwise Commute := fun a ha b hb _ => hs a ha b hb
  have := Subgroup.isMulCommutative_closure hpw
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure ⟨y, hy, rfl⟩
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hcomm : y * z = z * y := setLike_mul_comm hy hz
    have e : y * z * (y * z) = (y * y) * (z * z) := by
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [← hcomm]
        _ = y * y * (z * z) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y hy ihy =>
    have e : y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihy

section Final2

theorem E1_gens_comm (hΛ : HSCtx) :
    ∀ x ∈ ({bet 0, bet 1, bet 2, tL} : Set HSCover),
      ∀ y ∈ ({bet 0, bet 1, bet 2, tL} : Set HSCover), x * y = y * x := by
  have hb : ∀ i j : ℕ, i < 3 → j < 3 → bet i * bet j = bet j * bet i := fun i j hi hj =>
    hΛ.bet_comm hi hj
  rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl)
  all_goals first
    | rfl
    | exact hb _ _ (by norm_num) (by norm_num)
    | exact (hΛ.tL_central _).symm
    | exact hΛ.tL_central _

theorem rep_piBetaT (j : ℕ) :
    Rep 3850 (piBetaT j) ((harPiHom (bet j) : ↥hsP) : Equiv.Perm (Fin 3850)) :=
  rep_pi_wordVal _ (betaWords_getD_letters j)

theorem piBetaSqT_apply (j : ℕ) (i : Fin 3850) :
    ap (piBetaSqT j) i.val = ((harPiHom (bet j) * harPiHom (bet j)) • i).val := by
  have h := Rep.compT (rep_piBetaT j) (rep_piBetaT j)
  rw [piBetaSqT, h i.val i.2, idx_of_lt _ i.2]
  rfl

theorem mem_sigma_iff_gens (i : Fin 3850) :
    i ∈ fsOf sigmaPts ↔ ∀ j < 3, (harPiHom (bet j) * harPiHom (bet j)) • i = i := by
  rw [mem_fsOf_iff]
  unfold sigmaPts
  simp only [List.mem_filter, List.mem_range, List.all_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨-, h⟩ j hj
    apply Fin.ext
    rw [← piBetaSqT_apply, h j (by simpa using hj)]
  · intro h
    refine ⟨i.2, fun j hj => ?_⟩
    rw [piBetaSqT_apply, h j (by simpa using hj)]

theorem mem_sigma_iff (hΛ : HSCtx) (i : Fin 3850) :
    i ∈ fsOf sigmaPts ↔ ∀ x ∈ E1L, (harPiHom x * harPiHom x) • i = i := by
  rw [mem_sigma_iff_gens]
  constructor
  · intro h x hx
    let Fx : Subgroup HSCover := (MulAction.stabilizer ↥hsP i).comap harPiHom
    have hmem : ∀ a : HSCover, a ∈ Fx ↔ harPiHom a • i = i := fun a => Iff.rfl
    have hgens :
        (fun a => a * a) '' ({bet 0, bet 1, bet 2, tL} : Set HSCover) ⊆ (Fx : Set HSCover) := by
      rintro _ ⟨a, (rfl | rfl | rfl | rfl), rfl⟩
      · show bet 0 * bet 0 ∈ Fx
        rw [hmem, map_mul]
        exact h 0 (by norm_num)
      · show bet 1 * bet 1 ∈ Fx
        rw [hmem, map_mul]
        exact h 1 (by norm_num)
      · show bet 2 * bet 2 ∈ Fx
        rw [hmem, map_mul]
        exact h 2 (by norm_num)
      · show tL * tL ∈ Fx
        rw [hmem, (tL_involution hΛ).1, map_one, one_smul]
    have hxsq := sq_mem_closure_sq (E1_gens_comm hΛ) hx
    have h1 : x * x ∈ Fx := (Subgroup.closure_le Fx).2 hgens hxsq
    rw [hmem, map_mul] at h1
    exact h1
  · intro h j hj
    refine h (bet j) (Subgroup.subset_closure ?_)
    interval_cases j <;> simp

theorem sigma_invariant (hΛ : HSCtx) {k : HSCover} (hk : k ∈ normalizer (E1L : Set HSCover)) :
    harPiHom k • fsOf sigmaPts = fsOf sigmaPts := by
  ext i
  rw [mem_smul_fsOf, ← mem_fsOf_iff, mem_sigma_iff hΛ, mem_sigma_iff hΛ]
  have hkn := mem_normalizer_iff.1 hk
  have hkn' := mem_normalizer_iff.1 (inv_mem hk)
  have key : ∀ x : HSCover,
      ((harPiHom x * harPiHom x) • ((harPiHom k)⁻¹ • i) = (harPiHom k)⁻¹ • i) ↔
        (harPiHom (k * x * k⁻¹) * harPiHom (k * x * k⁻¹)) • i = i := by
    intro x
    have e : harPiHom (k * x * k⁻¹) = harPiHom k * harPiHom x * (harPiHom k)⁻¹ := by
      simp [map_mul, map_inv]
    rw [e]
    constructor
    · intro h
      calc (harPiHom k * harPiHom x * (harPiHom k)⁻¹ *
            (harPiHom k * harPiHom x * (harPiHom k)⁻¹)) • i
          = harPiHom k • ((harPiHom x * harPiHom x) • ((harPiHom k)⁻¹ • i)) := by
            simp [mul_smul, mul_assoc]
        _ = i := by rw [h]; simp
    · intro h
      calc (harPiHom x * harPiHom x) • ((harPiHom k)⁻¹ • i)
          = (harPiHom k)⁻¹ • ((harPiHom k * harPiHom x * (harPiHom k)⁻¹ *
              (harPiHom k * harPiHom x * (harPiHom k)⁻¹)) • i) := by
            simp [mul_smul, mul_assoc]
        _ = (harPiHom k)⁻¹ • i := by rw [h]
  constructor
  · intro h y hy
    have hy' := (hkn' y).1 hy
    have := (key (k⁻¹ * y * k⁻¹⁻¹)).1 (h _ hy')
    simpa [mul_assoc] using this
  · intro h x hx
    exact (key x).2 (h _ ((hkn x).1 hx))

theorem card_normalizer_E1L_le (hΛ : HSCtx) :
    Nat.card (normalizer (E1L : Set HSCover)) ≤ 21504 := by
  set K := normalizer (E1L : Set HSCover) with hK
  let φ : K →* ↥hsP := harPiHom.comp K.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range ≤ MulAction.stabilizer ↥hsP (fsOf sigmaPts) := by
    rintro _ ⟨k, rfl⟩
    exact sigma_invariant hΛ k.2
  have hr : Nat.card φ.range ≤ 10752 :=
    (Subgroup.card_le_of_le hrange).trans card_stabilizer_sigma_le
  have hker : Nat.card φ.ker ≤ 2 := by
    have : Finite (center HSCover) :=
      Nat.finite_of_card_ne_zero (by rw [hΛ.card_center]; norm_num)
    rw [← hΛ.card_center]
    refine Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨((x : K) : HSCover), ?_⟩ : center HSCover)) ?_
    · have hx : harPiHom ((x : K) : HSCover) = 1 := x.2
      exact (hΛ.coverMaps.π_ker _).1 hx
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
  calc Nat.card K = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ 2 * 10752 := Nat.mul_le_mul hker hr

end Final2

end CFSG.EvenSporadicStandard.TwoHS
