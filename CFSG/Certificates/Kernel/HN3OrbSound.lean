module

public import CFSG.Certificates.Kernel.HN3Sound

public section

namespace CFSG.KS.HN3

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HN3 CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KS.HNF26720
  CFSG.KS.HNF26729 CFSG.KS.HNLocal CFSG.KC.LQT.SecS Matrix

private theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem rowK_spec (vec : Nat → Nat → Nat) (S : List Nat) (x : Nat) :
    ∀ (gens js : List Nat), rowK vec S x gens js = true →
      ∀ j < gens.length, vec x (gens.getD j 0) = S.getD (js.getD j 0) (headN S)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | g :: gens, js, h, j, hj => by
    have h' : andB (Nat.beq (vec x g) (getN (headN S) S (headN js)))
        (rowK vec S x gens (tailN js)) = true := h
    obtain ⟨h1, h2⟩ := andB_true' h'
    cases j with
    | zero =>
      rw [List.getD_cons_zero, Nat.eq_of_beq_eq_true h1, getN_eq, headN_eq js]
    | succ j =>
      rw [List.getD_cons_succ, rowK_spec vec S x gens (tailN js) h2 j (by simpa using hj),
        tailN_getD]

theorem closeK_spec (vec : Nat → Nat → Nat) (S gens : List Nat) :
    ∀ (xs : List Nat) (I : List (List Nat)), closeK vec S gens xs I = true →
      ∀ p < xs.length, ∀ j < gens.length,
        vec (xs.getD p 0) (gens.getD j 0) = S.getD ((I.getD p []).getD j 0) (headN S)
  | [], _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | x :: xs, I, h, p, hp => by
    have h' : andB (rowK vec S x gens (List.rec (motive := fun _ => List Nat) List.nil
        (fun r _ _ => r) I)) (closeK vec S gens xs (List.rec (motive := fun _ => List (List Nat))
        List.nil (fun _ t _ => t) I)) = true := h
    obtain ⟨h1, h2⟩ := andB_true' h'
    intro j hj
    cases p with
    | zero =>
      rw [List.getD_cons_zero, rowK_spec vec S x gens _ h1 j hj]
      cases I <;> rfl
    | succ p =>
      rw [List.getD_cons_succ, closeK_spec vec S gens xs _ h2 p (by simpa using hp) j hj]
      cases I <;> simp

theorem treeK_spec (I : List (List Nat)) (ng : Nat) :
    ∀ (T : List (Nat × Nat)) (k : Nat), treeK I ng T k = true →
      ∀ m < T.length, (T.getD m (0, 0)).1 < k + m ∧ (T.getD m (0, 0)).2 < ng ∧
        (I.getD (T.getD m (0, 0)).1 []).getD (T.getD m (0, 0)).2 0 = k + m
  | [], _, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | e :: T, k, h, m, hm => by
    have h' : andB (Nat.blt e.1 k) (andB (Nat.blt e.2 ng)
        (andB (Nat.beq (getN 0 (getL I e.1) e.2) k) (treeK I ng T (Nat.succ k)))) = true := h
    obtain ⟨h1, h'⟩ := andB_true' h'
    obtain ⟨h2, h'⟩ := andB_true' h'
    obtain ⟨h3, h4⟩ := andB_true' h'
    cases m with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero]
      refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, ?_⟩
      have e3 := Nat.eq_of_beq_eq_true h3
      rwa [getN_eq, getL_eq] at e3
    | succ m =>
      obtain ⟨a1, a2, a3⟩ := treeK_spec I ng T (k + 1) h4 m (by simpa using hm)
      rw [List.getD_cons_succ]
      exact ⟨by omega, a2, by rw [a3]; omega⟩

theorem orbK_facts {mul vec : Nat → Nat → Nat} {vldV : Nat → Bool} {G : List Nat} {ONE : Nat}
    {gw : List (List Nat)} {S : List Nat} {I : List (List Nat)} {T : List (Nat × Nat)}
    {O : List Nat} {n : Nat} (h : orbK mul vec vldV G ONE gw S I T O n = true) :
    vldV (headN S) = true ∧ S.length = n ∧ T.length + 1 = n ∧ O.length = n ∧
      closeK vec S (gw.map fun w => wordG mul G w ONE) S I = true ∧
      treeK I (gw.map fun w => wordG mul G w ONE).length T 1 = true ∧
      incrK (headN S) S O 0 = true := by
  unfold orbK at h
  rw [forceLB_eq] at h
  obtain ⟨a1, h⟩ := andB_true' h
  obtain ⟨a2, h⟩ := andB_true' h
  obtain ⟨a3, h⟩ := andB_true' h
  obtain ⟨a4, h⟩ := andB_true' h
  obtain ⟨a5, h⟩ := andB_true' h
  obtain ⟨a6, a7⟩ := andB_true' h
  exact ⟨a1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3, Nat.eq_of_beq_eq_true a4, a5,
    a6, a7⟩

@[reducible] noncomputable def vecAct {K : Type*} [Group K]
    (ρ : K →* Matrix (Fin 133) (Fin 133) (ZMod 5)) : MulAction K (Fin 133 → ZMod 5) where
  smul h x := x ᵥ* ρ h⁻¹
  one_smul x := by
    change x ᵥ* ρ 1⁻¹ = x
    rw [inv_one, map_one, vecMul_one]
  mul_smul h k x := by
    change x ᵥ* ρ (h * k)⁻¹ = (x ᵥ* ρ k⁻¹) ᵥ* ρ h⁻¹
    rw [_root_.mul_inv_rev, map_mul, vecMul_vecMul]

theorem getD_irrel {l : List Nat} {i : Nat} (hi : i < l.length) (d d' : Nat) :
    l.getD i d = l.getD i d' := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem orbK_dvd {G : List Nat} {gw : List (List Nat)}
    (hG : ∀ w ∈ gw, ∀ c ∈ w, Canon 5 133 13 (getN 0 G c)) {S : List Nat}
    {I : List (List Nat)} {T : List (Nat × Nat)} {O : List Nat} {n : Nat}
    (h : orbK (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) G ONE gw S I T O n = true)
    {Γ : Type*} [Group Γ] (ρ : Γ →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (K : Subgroup Γ)
    (k : ℕ → Γ)
    (hk : ∀ j < gw.length, k j ∈ K ∧ ρ (k j) = ((gw.getD j []).map fun c => OM (getN 0 G c)).prod) :
    n ∣ Nat.card K := by
  classical
  obtain ⟨hv, hS, hT, hO, hcl, htr, hinc⟩ := orbK_facts h
  set gens := gw.map fun w => wordG (mulR 5 13 1729 133 9 L H CM RM) G w ONE with hgens
  have hglen : gens.length = gw.length := List.length_map _
  have hgen : ∀ j < gw.length, Canon 5 133 13 (gens.getD j 0) ∧
      ordMat 5 133 13 1729 (gens.getD j 0) = ρ (k j) := by
    intro j hj
    have e : gens.getD j 0 = wordG (mulR 5 13 1729 133 9 L H CM RM) G (gw.getD j []) ONE := by
      simp only [hgens, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some]
    rw [e]
    have hw : ∀ c ∈ gw.getD j [], Canon 5 133 13 (getN 0 G c) :=
      hG _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
    obtain ⟨c1, e1⟩ := wordG_one hc hw
    exact ⟨c1, e1.trans (hk j hj).2.symm⟩
  have hn : 0 < n := by omega
  set v0 := headN S with hv0def
  let sv : ℕ → Nat := fun i => S.getD i v0
  have sv0 : sv 0 = v0 := by
    change S.getD 0 v0 = v0
    rw [hv0def, headN_eq, getD_irrel (by omega) _ 0]
  have svd : ∀ i < n, sv i = S.getD i 0 := fun i hi => getD_irrel (by omega) _ _
  have hcv : VCanon 5 133 13 v0 := CFSG.KS.J4Hub.validV_canon hc hv
  let Hs : Subgroup Γ := Subgroup.closure {x | ∃ j < gw.length, k j = x}
  have hHK : Hs ≤ K := (Subgroup.closure_le K).2 (by rintro _ ⟨j, hj, rfl⟩; exact (hk j hj).1)
  have reach : ∀ i < n, VCanon 5 133 13 (sv i) ∧
      ∃ g ∈ Hs, toVec 5 133 13 (sv i) = toVec 5 133 13 v0 ᵥ* ρ g := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨by rw [sv0]; exact hcv, 1, Hs.one_mem, by rw [sv0, map_one, vecMul_one]⟩
      · obtain ⟨a1, a2, a3⟩ := treeK_spec I _ T 1 htr (i - 1) (by omega)
        have hj : (T.getD (i - 1) (0, 0)).2 < gw.length := by rwa [hglen] at a2
        have hp : (T.getD (i - 1) (0, 0)).1 < i := by omega
        have hcl' := closeK_spec _ S gens S I hcl (T.getD (i - 1) (0, 0)).1 (by omega)
          (T.getD (i - 1) (0, 0)).2 (by rw [hglen]; exact hj)
        have e1 : 1 + (i - 1) = i := by omega
        rw [a3, e1, ← hv0def, ← svd _ (by omega)] at hcl'
        obtain ⟨cp, g, hg, ep⟩ := ih _ hp (by omega)
        obtain ⟨cg, eg⟩ := hgen _ hj
        obtain ⟨c2, e2⟩ := vecR_sound hc cp cg
        refine ⟨?_, g * k (T.getD (i - 1) (0, 0)).2,
          Hs.mul_mem hg (Subgroup.subset_closure ⟨_, hj, rfl⟩), ?_⟩
        · change VCanon 5 133 13 (S.getD i v0)
          rw [← hcl']
          exact c2
        · change toVec 5 133 13 (S.getD i v0) = _
          rw [← hcl', e2, ep, eg, map_mul, vecMul_vecMul]
  let V : Finset (Fin 133 → ZMod 5) := (Finset.range n).image fun i => toVec 5 133 13 (sv i)
  have memV : ∀ x, x ∈ (V : Set (Fin 133 → ZMod 5)) ↔ ∃ i < n, toVec 5 133 13 (sv i) = x := by
    intro x
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, V]
  have closed_gen : ∀ j < gw.length, ∀ x ∈ (V : Set (Fin 133 → ZMod 5)),
      x ᵥ* ρ (k j) ∈ (V : Set (Fin 133 → ZMod 5)) := by
    intro j hj x hx
    obtain ⟨i, hi, rfl⟩ := (memV x).1 hx
    have hcl' := closeK_spec _ S gens S I hcl i (by omega) j (by rw [hglen]; exact hj)
    rw [← hv0def, ← svd i hi] at hcl'
    obtain ⟨ci, -⟩ := reach i hi
    obtain ⟨cg, eg⟩ := hgen j hj
    obtain ⟨-, e2⟩ := vecR_sound hc ci cg
    rw [hcl', eg] at e2
    rw [memV]
    by_cases hq : (I.getD i []).getD j 0 < n
    · exact ⟨_, hq, e2⟩
    · refine ⟨0, hn, ?_⟩
      rw [sv0, ← e2, List.getD_eq_default _ _ (by omega)]
  have closed : ∀ y ∈ Hs, ∀ x ∈ (V : Set (Fin 133 → ZMod 5)),
      x ᵥ* ρ y ∈ (V : Set (Fin 133 → ZMod 5)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact closed_gen j hj
    | one =>
      intro x hx
      rwa [map_one, vecMul_one]
    | mul y z _ _ hy hz =>
      intro x hx
      rw [map_mul, ← vecMul_vecMul]
      exact hz _ (hy x hx)
    | inv y _ hy =>
      intro x hx
      have hinj : Set.InjOn (fun u => u ᵥ* ρ y) (V : Set (Fin 133 → ZMod 5)) := by
        intro u _ u' _ e
        have e' := congrArg (fun t => t ᵥ* ρ y⁻¹) e
        simp only [vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, vecMul_one] at e'
        exact e'
      have hbij := ((V.finite_toSet).injOn_iff_bijOn_of_mapsTo (fun u hu => hy u hu)).1 hinj
      obtain ⟨u, hu, rfl⟩ := hbij.surjOn hx
      change u ᵥ* ρ y ᵥ* ρ y⁻¹ ∈ _
      rw [vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, vecMul_one]
      exact hu
  letI := vecAct (ρ.comp Hs.subtype)
  have horb : MulAction.orbit Hs (toVec 5 133 13 v0) = (V : Set (Fin 133 → ZMod 5)) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change toVec 5 133 13 v0 ᵥ* ρ ((g⁻¹ : Hs) : Γ) ∈ _
      exact closed _ (g⁻¹).2 _ ((memV _).2 ⟨0, hn, by rw [sv0]⟩)
    · intro hx
      obtain ⟨i, hi, rfl⟩ := (memV x).1 hx
      obtain ⟨-, g, hg, e⟩ := reach i hi
      refine ⟨(⟨g, hg⟩ : Hs)⁻¹, ?_⟩
      change toVec 5 133 13 v0 ᵥ* ρ (((⟨g, hg⟩ : Hs)⁻¹)⁻¹ : Hs) = _
      rw [inv_inv, e]
  obtain ⟨-, hpw⟩ := incrK_sound v0 S O 0 hinc
  have hnd : (O.map (getN v0 S)).Nodup := hpw.imp fun hab => Nat.ne_of_lt hab
  have hA : (O.map (getN v0 S)).toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hO]
  have hsub : (O.map (getN v0 S)).toFinset ⊆ (Finset.range n).image sv := by
    intro y hy
    rw [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨o, -, rfl⟩ := hy
    rw [Finset.mem_image]
    by_cases ho : o < n
    · exact ⟨o, Finset.mem_range.2 ho, by rw [getN_eq]⟩
    · refine ⟨0, Finset.mem_range.2 hn, ?_⟩
      rw [sv0, getN_eq, List.getD_eq_default _ _ (by omega)]
  have hB : ((Finset.range n).image sv).card = n := by
    refine le_antisymm (Finset.card_image_le.trans (by rw [Finset.card_range])) ?_
    have h2 := Finset.card_le_card hsub
    rw [hA] at h2
    exact h2
  have hV : V.card = n := by
    have e : V = ((Finset.range n).image sv).image (toVec 5 133 13) := by
      rw [Finset.image_image]
      rfl
    rw [e, Finset.card_image_of_injOn, hB]
    intro a ha b hb hab
    rw [Finset.coe_image] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨i', hi', rfl⟩ := hb
    have hi2 : i < n := Finset.mem_range.1 hi
    have hi2' : i' < n := Finset.mem_range.1 hi'
    exact vec_inj (by norm_num) (reach i hi2).1 (reach i' hi2').1 hab
  have hcard : (MulAction.orbit Hs (toVec 5 133 13 v0)).ncard = n := by
    rw [horb, Set.ncard_coe_finset, hV]
  have hidx := MulAction.index_stabilizer Hs (toVec 5 133 13 v0)
  rw [hcard] at hidx
  rw [← hidx]
  exact (Subgroup.index_dvd_card _).trans (Subgroup.card_dvd_of_le hHK)

end CFSG.KS.HN3

end
