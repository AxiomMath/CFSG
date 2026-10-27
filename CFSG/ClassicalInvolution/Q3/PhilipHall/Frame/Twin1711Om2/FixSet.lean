module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.ClassPkg
public import Certificates.Certificate197003

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)
open CFSG.ClassicalInvolution.Generic
open CFSG.RankThree.PerfectCover (HopfCover hopfLift comp_hopfLift hopfLift_surjective hopfCoverMap)
open scoped Pointwise

set_option linter.unusedSectionVars false


private noncomputable def fx2_quotEquiv : HY ⧸ Subgroup.center HY ≃* omegaT :=
  (QuotientGroup.quotientMulEquivOfEq center_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective qY qY_surjective)

private noncomputable def fx2_autHom : MulAut HY →* MulAut omegaT :=
  (MulAut.congr fx2_quotEquiv).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom HY)

private theorem fx2_autHom_injective : Function.Injective fx2_autHom := by
  haveI := isPerfect_HY
  exact (MulAut.congr fx2_quotEquiv).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective HY)

private theorem fx2_card_mulAut_le : Nat.card (MulAut HY) ≤ 1045094400 := by
  haveI := finite_mulAut_omegaT
  rw [← card_mulAut_omegaT]
  exact Nat.card_le_card_of_injective _ fx2_autHom_injective

private theorem fx2_card_mulAut_top_le : Nat.card (MulAut ↥(⊤ : Subgroup HY)) ≤ 1045094400 := by
  rw [Nat.card_congr (MulAut.congr Subgroup.topEquiv).toEquiv]
  exact fx2_card_mulAut_le

private instance fx2_finite_aut : Finite (MulAut ↥(⊤ : Subgroup HY)) :=
  Finite.of_injective
    (fun α : MulAut ↥(⊤ : Subgroup HY) => (α : ↥(⊤ : Subgroup HY) → ↥(⊤ : Subgroup HY)))
    DFunLike.coe_injective

private theorem fx2_card_HY : Nat.card HY = 696729600 := card_YP

private theorem fx2_card_mul_le {H G : Type} [Group H] [Group G] [Finite H] [Finite G]
    (c : H →* G) (A F : Subgroup G) (hcA : c.range ≤ A) (hFA : F ≤ A) :
    Nat.card F * Nat.card H ≤ Nat.card (F.comap c) * Nat.card A := by
  set R := c.range with hR
  have hne : R.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : R.relIndex F ≤ R.relIndex A := Subgroup.relIndex_le_of_le_right hFA hne
  have h1 : Nat.card F ≤ R.relIndex A * Nat.card (R ⊓ F : Subgroup _) :=
    calc Nat.card F = R.relIndex F * Nat.card (R ⊓ F : Subgroup _) :=
          (Subgroup.relIndex_mul_card R F).symm
      _ ≤ R.relIndex A * Nat.card (R ⊓ F : Subgroup _) := Nat.mul_le_mul_right _ hidx
  have h3 : Nat.card H * Nat.card (F ⊓ R : Subgroup _) = Nat.card (F.comap c) * Nat.card R := by
    have e1 := Subgroup.relIndex_mul_card F R
    have e2 := Subgroup.index_mul_card (F.comap c)
    rw [Subgroup.index_comap] at e2
    calc Nat.card H * Nat.card (F ⊓ R : Subgroup _)
        = F.relIndex R * Nat.card (F.comap c) * Nat.card (F ⊓ R : Subgroup _) := by rw [e2]
      _ = Nat.card (F.comap c) * (F.relIndex R * Nat.card (F ⊓ R : Subgroup _)) := by ring
      _ = Nat.card (F.comap c) * Nat.card R := by rw [e1]
  have h2 : R.relIndex A * Nat.card R = Nat.card A := by
    have := Subgroup.relIndex_mul_card R A
    rwa [inf_of_le_left hcA] at this
  calc Nat.card F * Nat.card H
      ≤ R.relIndex A * Nat.card (R ⊓ F : Subgroup _) * Nat.card H := Nat.mul_le_mul_right _ h1
    _ = R.relIndex A * (Nat.card H * Nat.card (F ⊓ R : Subgroup _)) := by rw [inf_comm]; ring
    _ = Nat.card (F.comap c) * (R.relIndex A * Nat.card R) := by rw [h3]; ring
    _ = Nat.card (F.comap c) * Nat.card A := by rw [h2]

private def fx2_conjTop (H : Type) [Group H] : H →* MulAut ↥(⊤ : Subgroup H) :=
  (MulAut.congr Subgroup.topEquiv.symm).toMonoidHom.comp MulAut.conj

private theorem fx2_conjTop_apply {H : Type} [Group H] (x : H) (y : ↥(⊤ : Subgroup H)) :
    ((fx2_conjTop H x y : ↥(⊤ : Subgroup H)) : H) = x * y * x⁻¹ := by
  simp [fx2_conjTop, MulAut.congr_apply]

private theorem fx2_conjTop_mem_fixSet_iff {H : Type} [Group H] (B : Set (Subgroup H)) (x : H) :
    fx2_conjTop H x ∈ fixSet (⊤ : Subgroup H) B ↔
      x ∈ Subgroup.centralizer {y : H | ∃ J ∈ B, y ∈ J} := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · rintro hx y ⟨J, hJ, hy⟩
    have h := congrArg (fun z : ↥(⊤ : Subgroup H) => (z : H)) (hx J hJ ⟨y, trivial⟩ hy)
    simp only [fx2_conjTop_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h b hb y hy
    apply Subtype.ext
    rw [fx2_conjTop_apply]
    have := h y ⟨b, hb, hy⟩
    calc x * (y : H) * x⁻¹ = (y * x) * x⁻¹ := by rw [this]
      _ = y := by group

private theorem fx2_card_fixSet_mul_le {H : Type} [Group H] [Finite H] (B : Set (Subgroup H))
    (A : Subgroup (MulAut ↥(⊤ : Subgroup H)))
    (hF : fixSet (⊤ : Subgroup H) B ≤ A) (hR : ∀ x : H, fx2_conjTop H x ∈ A) :
    Nat.card (fixSet (⊤ : Subgroup H) B) * Nat.card H ≤
      Nat.card (Subgroup.centralizer {y : H | ∃ J ∈ B, y ∈ J}) * Nat.card A := by
  haveI : Finite (MulAut ↥(⊤ : Subgroup H)) :=
    Finite.of_injective
      (fun α : MulAut ↥(⊤ : Subgroup H) => (α : ↥(⊤ : Subgroup H) → ↥(⊤ : Subgroup H)))
      DFunLike.coe_injective
  have hC : Subgroup.centralizer {y : H | ∃ J ∈ B, y ∈ J} =
      (fixSet (⊤ : Subgroup H) B).comap (fx2_conjTop H) := by
    ext x
    rw [Subgroup.mem_comap]
    exact (fx2_conjTop_mem_fixSet_iff B x).symm
  rw [hC]
  exact fx2_card_mul_le (fx2_conjTop H) A _ (by rintro _ ⟨x, rfl⟩; exact hR x) hF

@[ext] private structure Fx2Tup (m : ℕ) where
  p : Fin m → Equiv.Perm (Fin 480)

private noncomputable instance fx2_smulInst (m : ℕ) : SMul HY (Fx2Tup m) where
  smul g t := ⟨fun b => phi g * t.p b * (phi g)⁻¹⟩

private theorem fx2_smul_p {m : ℕ} (g : HY) (t : Fx2Tup m) (b : Fin m) :
    (g • t).p b = phi g * t.p b * (phi g)⁻¹ := rfl

private noncomputable instance fx2_actionInst (m : ℕ) : MulAction HY (Fx2Tup m) where
  one_smul t := Fx2Tup.ext (funext fun b => by simp [fx2_smul_p])
  mul_smul g h t := Fx2Tup.ext (funext fun b => by simp [fx2_smul_p, mul_assoc])

private theorem fx2_size_conjA (g y : Array ℕ) :
    (CFSG.RankThree.Native.conjA 480 g y).size = 480 := by
  simp [CFSG.RankThree.Native.conjA, compA]

private theorem fx2_size_wY (LY : Array (Array ℕ)) (w : List ℕ) : (wY LY w).size = 480 := by
  cases w with
  | nil => simp [wY, idA]
  | cons l w => simp [wY, compA]

private theorem fx2_get_append_left {X Y : Array ℕ} {i : ℕ} (h : i < X.size) :
    (X ++ Y)[i]! = X[i]! := by
  rw [getElem!_pos (X ++ Y) i (by rw [Array.size_append]; omega), getElem!_pos X i h,
    Array.getElem_append_left h]

private theorem fx2_get_append_right {X Y : Array ℕ} {i : ℕ} (h : X.size ≤ i)
    (h2 : i - X.size < Y.size) : (X ++ Y)[i]! = Y[i - X.size]! := by
  rw [getElem!_pos (X ++ Y) i (by rw [Array.size_append]; omega), getElem!_pos Y (i - X.size) h2,
    Array.getElem_append_right h]

private def Fx2Blocks (P : Array ℕ) (Bs : List (Array ℕ)) : Prop :=
  P.size = 480 * Bs.length ∧
    ∀ (b : ℕ) (hb : b < Bs.length), ∀ i < 480, P[b * 480 + i]! = (Bs[b])[i]!

private theorem fx2_blocks_nil : Fx2Blocks #[] [] :=
  ⟨by simp, fun b hb => absurd hb (by simp)⟩

private theorem fx2_blocks_append {P X : Array ℕ} {Bs : List (Array ℕ)} (hP : Fx2Blocks P Bs)
    (hX : X.size = 480) : Fx2Blocks (P ++ X) (Bs ++ [X]) := by
  obtain ⟨hs, hb⟩ := hP
  refine ⟨by rw [Array.size_append, hs, hX, List.length_append, List.length_singleton]; ring, ?_⟩
  intro b hb' i hi
  rw [List.length_append, List.length_singleton] at hb'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hb' with hlt | heq
  · rw [fx2_get_append_left (by rw [hs]; omega), hb b hlt i hi, List.getElem_append_left hlt]
  · subst heq
    rw [fx2_get_append_right (by rw [hs]; omega) (by rw [hX]; omega)]
    have e : Bs.length * 480 + i - P.size = i := by rw [hs]; omega
    rw [e]
    simp

private theorem fx2_blocks_foldl1 {α : Type} (f : α → Array ℕ) (hf : ∀ a, (f a).size = 480) :
    ∀ (L : List α) (P : Array ℕ) (Bs : List (Array ℕ)), Fx2Blocks P Bs →
      Fx2Blocks (L.foldl (fun acc a => acc ++ f a) P) (Bs ++ L.map f)
  | [], P, Bs, h => by simpa using h
  | a :: L, P, Bs, h => by
    have := fx2_blocks_foldl1 f hf L (P ++ f a) (Bs ++ [f a]) (fx2_blocks_append h (hf a))
    simpa [List.foldl_cons, List.map_cons, List.append_assoc] using this

private theorem fx2_blocks_foldl2 {α : Type} (f g : α → Array ℕ) (hf : ∀ a, (f a).size = 480)
    (hg : ∀ a, (g a).size = 480) :
    ∀ (L : List α) (P : Array ℕ) (Bs : List (Array ℕ)), Fx2Blocks P Bs →
      Fx2Blocks (L.foldl (fun acc a => acc ++ f a ++ g a) P)
        (Bs ++ L.flatMap fun a => [f a, g a])
  | [], P, Bs, h => by simpa using h
  | a :: L, P, Bs, h => by
    have := fx2_blocks_foldl2 f g hf hg L (P ++ f a ++ g a) (Bs ++ [f a] ++ [g a])
      (fx2_blocks_append (fx2_blocks_append h (hf a)) (hg a))
    simpa [List.foldl_cons, List.flatMap_cons, List.append_assoc] using this

private theorem fx2_blkY_get {u : Array ℕ} {b i : ℕ} (hi : i < 480) :
    (blkY u b)[i]! = u[b * 480 + i]! :=
  getElem!_ofFn_nat (fun i : Fin 480 => u[b * 480 + (i : ℕ)]!) hi

private theorem fx2_rep_blk {u Y : Array ℕ} {b : ℕ} {G : Equiv.Perm (Fin 480)}
    (h : ∀ i < 480, u[b * 480 + i]! = Y[i]!) (hY : Rep 480 Y G) : Rep 480 (blkY u b) G := by
  intro x
  rw [fx2_blkY_get x.2, h x x.2]
  exact hY x

private theorem fx2_validTupY {m : ℕ} {u : Array ℕ} (h : validTupY m u = true) :
    u.size = m * 480 ∧ ∀ k < m, validA 480 (blkY u k) = true := by
  simp only [validTupY, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h

private theorem fx2_blocks_actTupY (m : ℕ) (g u : Array ℕ) :
    Fx2Blocks (actTupY m g u)
      ((List.range m).map fun b => CFSG.RankThree.Native.conjA 480 g (blkY u b)) := by
  have := fx2_blocks_foldl1 (fun b => CFSG.RankThree.Native.conjA 480 g (blkY u b))
    (fun b => fx2_size_conjA g _) (List.range m) #[] [] fx2_blocks_nil
  simpa [actTupY] using this

private noncomputable def fx2_dec (m : ℕ) (u : Array ℕ) : Fx2Tup m :=
  ⟨fun b => permOfArr 480 (blkY u b)⟩

private theorem fx2_gens_valid {ws : List (List ℕ)} (hws : ∀ w ∈ ws, w ∈ allWordsY) {k : ℕ}
    (hk : k < (ws.map (wY (lettersY (reflTab ())))).toArray.size) :
    validA 480 (ws.map (wY (lettersY (reflTab ())))).toArray[k]! = true := by
  have hk' : k < ws.length := by simpa using hk
  have e : (ws.map (wY (lettersY (reflTab ())))).toArray[k]! =
      wY (lettersY (reflTab ())) ws[k] := by
    rw [getElem!_pos _ k hk, List.getElem_toArray, List.getElem_map]
  rw [e]
  exact (wordsCheckY_spec (hws _ (List.getElem_mem hk'))).2

private theorem fx2_hact_aux (m : ℕ) {g : Array ℕ} {G : Equiv.Perm (Fin 480)}
    (hgv : validA 480 g = true) (hp : permOfArr 480 g = G) {a : Array ℕ}
    (ha : validTupY m a = true) :
    fx2_dec m (actTupY m g a) = (⟨fun b => G * (fx2_dec m a).p b * G⁻¹⟩ : Fx2Tup m) := by
  have hv := (fx2_validTupY ha).2
  refine Fx2Tup.ext (funext fun b => ?_)
  obtain ⟨-, hent⟩ := fx2_blocks_actTupY m g a
  have hbm : (b : ℕ) < ((List.range m).map fun b =>
      CFSG.RankThree.Native.conjA 480 g (blkY a b)).length := by simp
  have hr := fx2_rep_blk (b := b) (u := actTupY m g a)
    (fun i hi => by rw [hent b hbm i hi]; simp)
    (CFSG.RankThree.Native.rep_conjA hgv
      (CFSG.RankThree.Native.rep_of_validA (hv b b.2)))
  rw [hp] at hr
  exact CFSG.RankThree.Native.permOfArr_eq_of_rep hr

private theorem fx2_hact {ws : List (List ℕ)} (hws : ∀ w ∈ ws, w ∈ allWordsY) (m : ℕ) {k : ℕ}
    (hk : k < (ws.map (wY (lettersY (reflTab ())))).toArray.size) {a : Array ℕ}
    (ha : validTupY m a = true) :
    fx2_dec m (actTupY m (ws.map (wY (lettersY (reflTab ())))).toArray[k]! a) =
      gensOfY ws k • fx2_dec m a :=
  fx2_hact_aux m (fx2_gens_valid hws hk)
    (CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_gensOfY (wordYOK_of_sub hws) hk)) ha

private theorem fx2_keyPtsY_lt : ∀ p ∈ keyPtsY, p < 480 := by
  intro p hp
  simp only [keyPtsY, CFSG.EvenSmallLie.OmegaEight.Weyl.keyPts, List.mem_append, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | ⟨a, ha, rfl⟩ <;> omega

private theorem fx2_hkey {m : ℕ} {a b : Array ℕ} (ha : validTupY m a = true)
    (hb : validTupY m b = true) (h : fx2_dec m a = fx2_dec m b) : keyTupY m a = keyTupY m b := by
  have hva := (fx2_validTupY ha).2
  have hvb := (fx2_validTupY hb).2
  have hblk : ∀ k < m, ∀ p < 480, a[k * 480 + p]! = b[k * 480 + p]! := by
    intro k hk p hp
    have e : permOfArr 480 (blkY a k) = permOfArr 480 (blkY b k) :=
      congrArg (fun t => t.p ⟨k, hk⟩) h
    have h1 := (CFSG.RankThree.Native.rep_of_validA (hva k hk)).apply hp
    have h2 := (CFSG.RankThree.Native.rep_of_validA (hvb k hk)).apply hp
    rw [e] at h1
    have h3 : (blkY a k)[p]! = a[k * 480 + p]! := fx2_blkY_get hp
    have h4 : (blkY b k)[p]! = b[k * 480 + p]! := fx2_blkY_get hp
    rw [← h3, ← h4, h1, h2]
  unfold keyTupY
  congr 1
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  refine List.map_congr_left fun p hp => ?_
  exact hblk k (List.mem_range.1 hk) p (fx2_keyPtsY_lt p hp)

private theorem fx2_orbit {ws : List (List ℕ)} (hws : ∀ w ∈ ws, w ∈ allWordsY) {m : ℕ}
    {u0 : Array ℕ} {sz : ℕ}
    (h : tupSize m (ws.map (wY (lettersY (reflTab ())))).toArray u0 sz = true) :
    validTupY m u0 = true ∧ (MulAction.orbit (closureY ws) (fx2_dec m u0)).ncard = sz := by
  simp only [tupSize, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hv, hc⟩, hsz⟩ := h
  have := ncard_orbit_of_arrCertOK (gens := gensOfY ws) (dec := fx2_dec m) hc
    (fun k hk a ha => fx2_hact hws m hk ha) (fun a b ha hb h => fx2_hkey ha hb h)
  rw [closure_gensOfY] at this
  exact ⟨hv, this.trans hsz⟩

private theorem fx2_card_stab_eq {K : Subgroup HY} {m : ℕ} {u : Array ℕ} {o : ℕ}
    (ho : (MulAction.orbit ↥K (fx2_dec m u)).ncard = o) :
    Nat.card (MulAction.stabilizer ↥K (fx2_dec m u)) * o = Nat.card ↥K := by
  rw [← ho, ← MulAction.index_stabilizer, Subgroup.card_mul_index]

private theorem fx2_fix_of_blocks {m : ℕ} {u0 : Array ℕ} {Bs : List (Array ℕ)} {E : Set HY}
    (hB : Fx2Blocks u0 Bs) (hm : Bs.length = m)
    (hE : ∀ B ∈ Bs, ∃ e ∈ E, Rep 480 B (phi e)) {x : HY}
    (hx : x ∈ Subgroup.centralizer E) : x • fx2_dec m u0 = fx2_dec m u0 := by
  refine Fx2Tup.ext (funext fun b => ?_)
  have hb : (b : ℕ) < Bs.length := by rw [hm]; exact b.2
  obtain ⟨e, he, hrep⟩ := hE Bs[(b : ℕ)] (List.getElem_mem hb)
  have hr : Rep 480 (blkY u0 b) (phi e) := fx2_rep_blk (fun i hi => hB.2 b hb i hi) hrep
  show phi x * permOfArr 480 (blkY u0 b) * (phi x)⁻¹ = permOfArr 480 (blkY u0 b)
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hr]
  have hc : e * x = x * e := Subgroup.mem_centralizer_iff.1 hx e he
  rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, hc]

private theorem fx2_i0Y_mem : i0Y ∈ R0Y := Subgroup.subset_closure (Set.mem_insert _ _)

private theorem fx2_j0Y_mem : j0Y ∈ R0Y :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

private theorem fx2_wordYOK_I : wordYOK wI0 = true :=
  (wordsCheckY_spec (w := wI0) (by simp [allWordsY])).1

private theorem fx2_wordYOK_J : wordYOK wJ0 = true :=
  (wordsCheckY_spec (w := wJ0) (by simp [allWordsY])).1

private theorem fx2_nil_mem : ([] : List ℕ) ∈ allWordsY := by
  have h : ([] : List ℕ) ∈ wDT := by
    unfold wDT
    exact List.mem_cons.2 (Or.inl rfl)
  simp only [allWordsY, List.mem_append]
  exact Or.inl (Or.inr h)

private theorem fx2_wFuse0_length : wFuse0.length = 3 := by
  have h := om2A_parts.2.1
  simp only [wordsCheckY, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

private theorem fx2_closure_wT : closureY wT = T0Y := classPkg0Y.1

private theorem fx2_card_T0Y : Nat.card T0Y = 110592 := classPkg0Y.2.2.1

private noncomputable def fx2_pair : Fx2Tup 2 := ⟨![phi i0Y, phi j0Y]⟩

private theorem fx2_orbit_pair : 24 ≤ (MulAction.orbit ↥T0Y fx2_pair).ncard := by
  refine Certificates.certificate197003.2.2.1.trans ?_
  have hsub : {p : Equiv.Perm (Fin 480) × Equiv.Perm (Fin 480) | ∃ s ∈ Om2Facts.G wT,
      p = (s * Om2Facts.E wI0 * s⁻¹, s * Om2Facts.E wJ0 * s⁻¹)} ⊆
      (fun u : Fx2Tup 2 => (u.p 0, u.p 1)) '' MulAction.orbit ↥T0Y fx2_pair := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨s', hs', rfl⟩ := exists_of_mem_G (wordYOK_of_sub wT_sub) hs
    rw [fx2_closure_wT] at hs'
    refine ⟨(⟨s', hs'⟩ : T0Y) • fx2_pair, MulAction.mem_orbit _ _, ?_⟩
    rw [← phi_wordE fx2_wordYOK_I, ← phi_wordE fx2_wordYOK_J]
    rfl
  exact (Set.ncard_le_ncard hsub ((Set.finite_range _).image _)).trans
    (Set.ncard_image_le (Set.finite_range _))

private theorem fx2_cent_mem_2 {x : HY} (hx : x ∈ Subgroup.centralizer ({i0Y, j0Y} : Set HY)) :
    x ∈ T0Y ∧ x • fx2_pair = fx2_pair := by
  have c1 : i0Y * x = x * i0Y := Subgroup.mem_centralizer_iff.1 hx i0Y (by simp)
  have c2 : j0Y * x = x * j0Y := Subgroup.mem_centralizer_iff.1 hx j0Y (by simp)
  refine ⟨?_, Fx2Tup.ext (funext fun b => ?_)⟩
  · rw [Subgroup.mem_centralizer_singleton_iff, ← i0Y_mul_self]
    calc x * (i0Y * i0Y) = (x * i0Y) * i0Y := (mul_assoc _ _ _).symm
      _ = (i0Y * x) * i0Y := by rw [c1]
      _ = i0Y * (x * i0Y) := mul_assoc _ _ _
      _ = i0Y * (i0Y * x) := by rw [c1]
      _ = (i0Y * i0Y) * x := (mul_assoc _ _ _).symm
  · fin_cases b
    · change phi x * phi i0Y * (phi x)⁻¹ = phi i0Y
      rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, c1]
    · change phi x * phi j0Y * (phi x)⁻¹ = phi j0Y
      rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, c2]

private theorem fx2_card_Z_le :
    Nat.card (Subgroup.centralizer ({i0Y, j0Y} : Set HY)) ≤ 4608 := by
  have hst : Nat.card (MulAction.stabilizer ↥T0Y fx2_pair) *
      (MulAction.orbit ↥T0Y fx2_pair).ncard = 110592 := by
    rw [← fx2_card_T0Y, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
  have hle : Nat.card (Subgroup.centralizer ({i0Y, j0Y} : Set HY)) ≤
      Nat.card (MulAction.stabilizer ↥T0Y fx2_pair) :=
    Nat.card_le_card_of_injective
      (fun x => ⟨⟨x.1, (fx2_cent_mem_2 x.2).1⟩,
        (MulAction.mem_stabilizer_iff).2 (fx2_cent_mem_2 x.2).2⟩)
      fun x y h => Subtype.ext (congrArg (fun z => z.1.1) h)
  have h24 : Nat.card (MulAction.stabilizer ↥T0Y fx2_pair) * 24 ≤ 4608 * 24 :=
    calc _ ≤ Nat.card (MulAction.stabilizer ↥T0Y fx2_pair) *
          (MulAction.orbit ↥T0Y fx2_pair).ncard := Nat.mul_le_mul_left _ fx2_orbit_pair
      _ = 4608 * 24 := hst
  omega

private theorem fx2_card_closure_wCR : Nat.card (closureY wCR) = 4608 := by
  have h := om2A_parts.2.2.2.1
  simp only [enumCheckY, Bool.and_eq_true] at h
  exact (enumSizeY_spec (wordYOK_of_sub wCR_sub) h.2).1

private theorem fx2_closure_wCR_eq :
    closureY wCR = Subgroup.centralizer ({i0Y, j0Y} : Set HY) := by
  have hle : closureY wCR ≤ Subgroup.centralizer ({i0Y, j0Y} : Set HY) := by
    rw [closureY, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c1, c2⟩ := comm_R0Y_of_mem hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · exact c1.symm
    · rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact c2.symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [fx2_card_closure_wCR]; exact fx2_card_Z_le)

private theorem fx2_S8_mem {B : Set (Subgroup HY)} (h0 : R0Y ∈ B)
    (h1 : ∀ k < 3, conjSub (fuse0 k) R0Y ∈ B) :
    ∀ u ∈ Om2Facts.S8, ∃ y ∈ {y : HY | ∃ J ∈ B, y ∈ J}, phi y = u := by
  rintro _ ⟨w, hw, v, hv, rfl⟩
  have hwA : w ∈ allWordsY := by
    rcases List.mem_cons.1 hw with rfl | hw
    · exact fx2_nil_mem
    · exact wFuse0_sub w hw
  have hwOK := (wordsCheckY_spec hwA).1
  have hmem : ∀ y ∈ R0Y, wordE w * y * (wordE w)⁻¹ ∈ {y : HY | ∃ J ∈ B, y ∈ J} := by
    intro y hy
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨R0Y, h0, by simpa [wordE] using hy⟩
    · obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.1 hw
      have hk3 : k < 3 := by
        have := fx2_wFuse0_length
        omega
      refine ⟨conjSub (fuse0 k) R0Y, h1 k hk3, ?_⟩
      have e : wordE w = fuse0 k := by
        rw [← hkw]
        change wordE wFuse0[k] = wordE (wFuse0.getD k [])
        rw [List.getD_eq_getElem _ _ hk]
        rfl
      rw [e]
      exact conj_mem_conjSub hy
  have hv' : ∃ y ∈ R0Y, phi y = Om2Facts.E v := by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨i0Y, fx2_i0Y_mem, phi_wordE fx2_wordYOK_I⟩
    · rw [List.mem_singleton.1 hv]
      exact ⟨j0Y, fx2_j0Y_mem, phi_wordE fx2_wordYOK_J⟩
  obtain ⟨y, hy, hyv⟩ := hv'
  refine ⟨wordE w * y * (wordE w)⁻¹, hmem y hy, ?_⟩
  rw [map_mul, map_mul, map_inv, hyv, phi_wordE hwOK]

private theorem fx2_card_cent_le_8 {B : Set (Subgroup HY)} (h0 : R0Y ∈ B)
    (h1 : ∀ k < 3, conjSub (fuse0 k) R0Y ∈ B) :
    Nat.card (Subgroup.centralizer {y : HY | ∃ J ∈ B, y ∈ J}) ≤ 8 := by
  refine le_trans ?_ Certificates.certificate197003.2.2.2.1
  have hle : Subgroup.centralizer {y : HY | ∃ J ∈ B, y ∈ J} ≤ closureY wCR := by
    rw [fx2_closure_wCR_eq]
    refine Subgroup.centralizer_le ?_
    rintro y (rfl | hy)
    · exact ⟨R0Y, h0, fx2_i0Y_mem⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨R0Y, h0, fx2_j0Y_mem⟩
  have hS := fx2_S8_mem h0 h1
  have hx : ∀ x ∈ Subgroup.centralizer {y : HY | ∃ J ∈ B, y ∈ J},
      phi x ∈ Om2Facts.G wCR ⊓ Subgroup.centralizer Om2Facts.S8 := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨(mem_closureY_iff (wordYOK_of_sub wCR_sub)).1 (hle hx),
      Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hS u hu
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx y hy]
  exact Nat.card_le_card_of_injective (fun x => ⟨phi x.1, hx x.1 x.2⟩)
    fun a b h => Subtype.ext (phi_injective (congrArg Subtype.val h))

private def fx2_AK : Subgroup (MulAut ↥(⊤ : Subgroup HY)) where
  carrier := {α | ∀ k < 3, α ⟨cK k, Subgroup.mem_top _⟩ = ⟨cK k, Subgroup.mem_top _⟩}
  mul_mem' := by
    intro α β hα hβ k hk
    rw [MulAut.mul_apply, hβ k hk, hα k hk]
  one_mem' := fun k hk => rfl
  inv_mem' := by
    intro α hα k hk
    calc α⁻¹ ⟨cK k, Subgroup.mem_top _⟩ = α⁻¹ (α ⟨cK k, Subgroup.mem_top _⟩) := by rw [hα k hk]
      _ = ⟨cK k, Subgroup.mem_top _⟩ := α.symm_apply_apply _

private theorem fx2_conjTop_mem_AK (x : HY) : fx2_conjTop HY x ∈ fx2_AK := by
  intro k hk
  apply Subtype.ext
  rw [fx2_conjTop_apply]
  change x * cK k * x⁻¹ = cK k
  rw [cK_comm k x, mul_inv_cancel_right]

private theorem fx2_fixSet_le_AK {B : Set (Subgroup HY)} (h0 : R0Y ∈ B)
    (h1 : ∀ k < 3, conjSub (fuse0 k) R0Y ∈ B) : fixSet (⊤ : Subgroup HY) B ≤ fx2_AK := by
  intro α hα k hk
  have ht0 : t0Y ∈ R0Y := by
    rw [← i0Y_mul_self]
    exact mul_mem fx2_i0Y_mem fx2_i0Y_mem
  have h2 : t0Y * cK k ∈ conjSub (fuse0 k) R0Y := by
    rw [← fuse0_conj hk]
    exact conj_mem_conjSub ht0
  have e1 := hα R0Y h0 ⟨t0Y, Subgroup.mem_top _⟩ ht0
  have e2 := hα _ (h1 k hk) ⟨t0Y * cK k, Subgroup.mem_top _⟩ h2
  have e : (⟨cK k, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup HY)) =
      (⟨t0Y, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup HY))⁻¹ * ⟨t0Y * cK k, Subgroup.mem_top _⟩ :=
    Subtype.ext (by simp)
  rw [e, map_mul, map_inv, e1, e2]

private theorem fx2_cK1 : ((cK 1 : HY) : WP × WP) = (1, zPlus) := by
  simp [cK]

private theorem fx2_psi_cK1_ne (ψ : MulAut HY) (hψ : ∀ u, qY (ψ u) = sigmaO (qY u)) :
    ψ (cK 1) ≠ cK 1 := by
  intro hc
  have hm : (uPlus, yPlus) ∈ YP := mem_YP.2 autEquiv_rhoA_uPlus
  set v : HY := ⟨(uPlus, yPlus), hm⟩ with hv
  have hvv : v * v = cK 1 := Subtype.ext (by
    rw [fx2_cK1]
    exact Prod.ext uPlus_mul_self yPlus_mul_self)
  have hq : pHat ((ψ v : WP × WP).1) = pHat yPlus := by
    have := hψ v
    rw [qY_apply] at this
    rw [← autEquiv_rhoA_uPlus]
    exact this
  have hzc := Subgroup.mem_center_iff.1 zPlus_mem_center (ψ v : WP × WP).1
  have hzz : zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self
  have hsq : (ψ v : WP × WP).1 * (ψ v : WP × WP).1 = zPlus := by
    rcases pHat_eq_iff.1 hq with h | h
    · rw [← h]
      exact yPlus_mul_self
    · calc (ψ v : WP × WP).1 * (ψ v : WP × WP).1
          = (ψ v : WP × WP).1 * (ψ v : WP × WP).1 * (zPlus * zPlus) := by rw [hzz, mul_one]
        _ = ((ψ v : WP × WP).1 * zPlus) * ((ψ v : WP × WP).1 * zPlus) := by
          calc (ψ v : WP × WP).1 * (ψ v : WP × WP).1 * (zPlus * zPlus)
              = (ψ v : WP × WP).1 * ((ψ v : WP × WP).1 * zPlus) * zPlus := by group
            _ = (ψ v : WP × WP).1 * (zPlus * (ψ v : WP × WP).1) * zPlus := by rw [hzc]
            _ = _ := by group
        _ = yPlus * yPlus := by rw [h]
        _ = zPlus := yPlus_mul_self
  have h2 : ψ v * ψ v = cK 1 := by rw [← map_mul, hvv, hc]
  have h3 : ((ψ v * ψ v : HY) : WP × WP).1 = ((cK 1 : HY) : WP × WP).1 :=
    congrArg (fun z : HY => ((z : WP × WP)).1) h2
  rw [fx2_cK1] at h3
  exact zPlus_ne_one (hsq.symm.trans h3)

private theorem fx2_exists_psi : ∃ ψ : MulAut HY, ∀ u, qY (ψ u) = sigmaO (qY u) := by
  haveI := isPerfect_HY
  let f' : HY →* omegaT := sigmaO.symm.toMonoidHom.comp qY
  have hfs : Function.Surjective f' := sigmaO.symm.surjective.comp qY_surjective
  have hk : f'.ker ≤ Subgroup.center HY := by
    intro u hu
    apply ker_qY_le_center
    rw [MonoidHom.mem_ker] at hu ⊢
    exact (MulEquiv.map_eq_one_iff sigmaO.symm).1 hu
  let L : HopfCover omegaT →* HY := hopfLift f' hfs hk
  have hL : f'.comp L = hopfCoverMap omegaT := comp_hopfLift f' hfs hk
  have hLs : Function.Surjective L := hopfLift_surjective f' hfs hk
  let ψ0 : HY →* HY := L.comp hopfEquivY.symm.toMonoidHom
  have hψs : Function.Surjective ψ0 := hLs.comp hopfEquivY.symm.surjective
  have hψi : Function.Injective ψ0 := Finite.injective_iff_surjective.2 hψs
  refine ⟨MulEquiv.ofBijective ψ0 ⟨hψi, hψs⟩, fun u => ?_⟩
  have e1 : f' (L (hopfEquivY.symm u)) = hopfCoverMap omegaT (hopfEquivY.symm u) :=
    DFunLike.congr_fun hL _
  have e2 : hopfCoverMap omegaT (hopfEquivY.symm u) = qY u := by
    rw [← qY_hopfEquivY, MulEquiv.apply_symm_apply]
  rw [e2] at e1
  exact (MulEquiv.symm_apply_eq sigmaO).1 e1

private theorem fx2_AK_ne_top : fx2_AK ≠ ⊤ := by
  intro h
  obtain ⟨ψ, hψ⟩ := fx2_exists_psi
  have hmem : (MulAut.congr Subgroup.topEquiv.symm) ψ ∈ fx2_AK := by
    rw [h]
    exact Subgroup.mem_top _
  have := hmem 1 (by norm_num)
  apply fx2_psi_cK1_ne ψ hψ
  exact congrArg Subtype.val this

private theorem fx2_card_AK :
    Nat.card fx2_AK * 2 ≤ Nat.card (MulAut ↥(⊤ : Subgroup HY)) := by
  have h1 : fx2_AK.index ≠ 1 := fun h => fx2_AK_ne_top (Subgroup.index_eq_one.1 h)
  have h2 : fx2_AK.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.card_mul_index fx2_AK
  calc Nat.card fx2_AK * 2 ≤ Nat.card fx2_AK * fx2_AK.index := Nat.mul_le_mul_left _ (by omega)
    _ = _ := h3

theorem card_fixSet_le1 {B : Set (Subgroup HY)} (h0 : R0Y ∈ B) :
    Nat.card (fixSet (⊤ : Subgroup HY) B) ≤ 6912 := by
  have hsub : ({R0Y} : Set (Subgroup HY)) ⊆ B := by
    intro J hJ
    rw [Set.mem_singleton_iff] at hJ
    rw [hJ]
    exact h0
  have h2 : Nat.card (fixSet (⊤ : Subgroup HY) B) ≤
      Nat.card (fixSet (⊤ : Subgroup HY) ({R0Y} : Set (Subgroup HY))) :=
    Subgroup.card_le_of_le (OmGen.fixSet_anti hsub)
  have h3 := OmGen.card_fixSet_mul_le (H := HY) ({R0Y} : Set (Subgroup HY))
  have h5 : Nat.card (Subgroup.centralizer
      {y : HY | ∃ J ∈ ({R0Y} : Set (Subgroup HY)), y ∈ J}) ≤ 4608 := by
    refine (Subgroup.card_le_of_le (Subgroup.centralizer_le ?_)).trans fx2_card_Z_le
    rintro y (rfl | hy)
    · exact ⟨R0Y, rfl, fx2_i0Y_mem⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨R0Y, rfl, fx2_j0Y_mem⟩
  have h6 := Nat.mul_le_mul h5 fx2_card_mulAut_top_le
  rw [fx2_card_HY] at h3
  omega

theorem card_fixSet_le4 {B : Set (Subgroup HY)} (h0 : R0Y ∈ B)
    (h1 : ∀ k < 3, conjSub (fuse0 k) R0Y ∈ B) : Nat.card (fixSet (⊤ : Subgroup HY) B) ≤ 6 := by
  have h3 := fx2_card_fixSet_mul_le B fx2_AK (fx2_fixSet_le_AK h0 h1) fx2_conjTop_mem_AK
  have hC := fx2_card_cent_le_8 h0 h1
  have hA := fx2_card_AK
  have hAut := fx2_card_mulAut_top_le
  rw [fx2_card_HY] at h3
  have h7 := Nat.mul_le_mul_right (Nat.card fx2_AK) hC
  omega

theorem mem_closureY_wCR_of_comm {u : HY} (hi : u * i0Y = i0Y * u) (hj : u * j0Y = j0Y * u) :
    u ∈ closureY wCR := by
  rw [fx2_closure_wCR_eq, Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | hh
  · exact hi.symm
  · rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hj.symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
