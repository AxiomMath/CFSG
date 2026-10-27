module

public import CFSG.CGT.Timmesfeld75.Lemma210
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412d

public section

namespace CFSG.GroupTheory

open CFSG.CGT.Timmesfeld75
open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

private abbrev W2 (F : Type*) := (Fin 2 → F) × (Fin 2 → F)

private theorem w2_add_self (w : W2 F) : w + w = 0 := by
  obtain ⟨a, b⟩ := w
  apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _

private theorem slAct_sub (g : SL(2, F)) (u v : W2 F) :
    slAct g (u - v) = slAct g u - slAct g v := by
  ext <;> simp [slAct, Matrix.mulVec_sub]

private theorem scalar_eq_one (μ : F) (hμ : μ ^ (Fintype.card F + 1) = 1) (hμ0 : μ ≠ 0) :
    μ = 1 := by
  have hq : Even (Fintype.card F) :=
    Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hodd : Odd (Fintype.card F - 1) := by
    obtain ⟨k, hk⟩ := hq
    have hpos := Fintype.card_pos (α := F)
    exact ⟨k - 1, by omega⟩
  have hcop : Nat.Coprime (Fintype.card F + 1) (Fintype.card F - 1) := by
    have h2 : Nat.Coprime (Fintype.card F - 1) ((Fintype.card F - 1) + 2) :=
      Nat.coprime_self_add_right.mpr (Odd.coprime_two_right hodd)
    have h3 : (Fintype.card F - 1) + 2 = Fintype.card F + 1 := by
      have := Fintype.card_pos (α := F)
      omega
    rw [h3] at h2
    exact h2.symm
  have h1 : μ ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ0
  have hsq : μ ^ 2 = 1 := by
    have h3 : μ ^ (Fintype.card F - 1) * μ ^ 2 = μ ^ (Fintype.card F + 1) := by
      rw [← pow_add]
      congr 1
      have := Fintype.card_pos (α := F)
      omega
    rw [h1, hμ] at h3
    simpa using h3
  exact CharTwo.sq_inj.mp (by simpa using hsq)

private theorem fix_graph (T : W2 F →+ W2 F)
    (hT : ∀ (g : SL(2, F)) u, T (slAct g u) = slAct g (T u))
    (hpow : ∀ u, (⇑T)^[Fintype.card F + 1] u = u)
    {c : F} (hTU : ∀ u ∈ graphSub (n := 2) c, T u ∈ graphSub (n := 2) c) :
    ∀ u ∈ graphSub (n := 2) c, T u = u := by
  let S : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => (T (v, c • v)).1
      map_zero' := by
        rw [smul_zero, show ((0 : Fin 2 → F), (0 : Fin 2 → F)) = (0 : W2 F) from rfl,
          map_zero]
        rfl
      map_add' := fun v w => by
        have h : T (v + w, c • (v + w)) = T (v, c • v) + T (w, c • w) := by
          rw [show (v + w, c • (v + w)) = (v, c • v) + (w, c • w) by
            ext <;> simp [smul_add, mul_add]]
          exact map_add T _ _
        exact congrArg Prod.fst h }
  have hScomm : ∀ (g : SL(2, F)) (v : Fin 2 → F),
      S ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ S v := by
    intro g v
    have h1 : slAct g (v, c • v) =
        ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v, c • ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) := by
      unfold slAct
      rw [Matrix.mulVec_smul]
    calc S ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
        = (T (slAct g (v, c • v))).1 := by rw [h1]; rfl
      _ = (slAct g (T (v, c • v))).1 := by rw [hT]
      _ = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (T (v, c • v)).1 := rfl
      _ = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ S v := rfl
  obtain ⟨μ, hμ⟩ := CFSG.QuasithinUnique.Lin2.schur_sl2 S hScomm
  have hTapply : ∀ v : Fin 2 → F, T (v, c • v) = (μ • v, c • (μ • v)) := by
    intro v
    have hmem : T (v, c • v) ∈ graphSub (n := 2) c := hTU _ (mem_graphSub.mpr rfl)
    have h2 : (T (v, c • v)).1 = μ • v := hμ v
    exact Prod.ext h2 ((mem_graphSub.mp hmem).trans (by rw [h2]))
  have hiter : ∀ (k : ℕ) (v : Fin 2 → F),
      (⇑T)^[k] (v, c • v) = ((μ ^ k) • v, c • ((μ ^ k) • v)) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [Function.iterate_succ_apply', ih v, hTapply]
        apply Prod.ext <;> funext i <;>
          simp only [Pi.smul_apply, smul_eq_mul, pow_succ] <;> ring
  have hμpow : μ ^ (Fintype.card F + 1) = 1 := by
    have h := hpow (Pi.single (0 : Fin 2) (1 : F), c • Pi.single (0 : Fin 2) (1 : F))
    rw [hiter (Fintype.card F + 1)] at h
    have h1 : (μ ^ (Fintype.card F + 1)) • (Pi.single (0 : Fin 2) (1 : F)) =
        Pi.single (0 : Fin 2) (1 : F) := by
      simpa using congrArg Prod.fst h
    have h2 := congrFun h1 (0 : Fin 2)
    simpa using h2
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : Fintype.card F + 1 ≠ 0)] at hμpow
    exact zero_ne_one hμpow
  have hμ1 : μ = 1 := scalar_eq_one μ hμpow hμ0
  intro u hu
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → F, u = (v, c • v) :=
    ⟨u.1, Prod.ext rfl (mem_graphSub.mp hu)⟩
  rw [hv, hTapply, hμ1, one_smul]

private theorem fix_prod (T : W2 F →+ W2 F)
    (hT : ∀ (g : SL(2, F)) u, T (slAct g u) = slAct g (T u))
    (hpow : ∀ u, (⇑T)^[Fintype.card F + 1] u = u)
    (hTU : ∀ u ∈ AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤,
      T u ∈ AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤) :
    ∀ u ∈ AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤, T u = u := by
  let S : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => (T (0, v)).2
      map_zero' := by
        rw [show ((0 : Fin 2 → F), (0 : Fin 2 → F)) = (0 : W2 F) from rfl, map_zero]
        rfl
      map_add' := fun v w => by
        have h : T ((0 : Fin 2 → F), v + w) = T (0, v) + T (0, w) := by
          rw [show ((0 : Fin 2 → F), v + w) = ((0 : Fin 2 → F), v) + ((0 : Fin 2 → F), w) by
            ext <;> simp]
          exact map_add T _ _
        exact congrArg Prod.snd h }
  have hTapply : ∀ v : Fin 2 → F, T ((0 : Fin 2 → F), v) = (0, S v) := by
    intro v
    have hmem : T ((0 : Fin 2 → F), v) ∈
        AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤ :=
      hTU _ (AddSubgroup.mem_prod.mpr
        ⟨AddSubgroup.mem_bot.mpr rfl, AddSubgroup.mem_top _⟩)
    exact Prod.ext (AddSubgroup.mem_bot.mp (AddSubgroup.mem_prod.mp hmem).1) rfl
  have hScomm : ∀ (g : SL(2, F)) (v : Fin 2 → F),
      S ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ S v := by
    intro g v
    have h1 : slAct g ((0 : Fin 2 → F), v) =
        ((0 : Fin 2 → F), (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
      unfold slAct
      simp
    calc S ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
        = (T (slAct g ((0 : Fin 2 → F), v))).2 := by rw [h1]; rfl
      _ = (slAct g (T ((0 : Fin 2 → F), v))).2 := by rw [hT]
      _ = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (T ((0 : Fin 2 → F), v)).2 := rfl
      _ = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ S v := by rw [hTapply]
  obtain ⟨μ, hμ⟩ := CFSG.QuasithinUnique.Lin2.schur_sl2 S hScomm
  have hTapply' : ∀ v : Fin 2 → F, T ((0 : Fin 2 → F), v) = (0, μ • v) := by
    intro v
    rw [hTapply, hμ v]
    rfl
  have hiter : ∀ (k : ℕ) (v : Fin 2 → F),
      (⇑T)^[k] ((0 : Fin 2 → F), v) = ((0 : Fin 2 → F), (μ ^ k) • v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [Function.iterate_succ_apply', ih v, hTapply']
        apply Prod.ext <;> funext i <;>
          simp only [Pi.smul_apply, smul_eq_mul, pow_succ] <;> ring
  have hμpow : μ ^ (Fintype.card F + 1) = 1 := by
    have h := hpow ((0 : Fin 2 → F), Pi.single (0 : Fin 2) (1 : F))
    rw [hiter (Fintype.card F + 1)] at h
    have h1 : (μ ^ (Fintype.card F + 1)) • (Pi.single (0 : Fin 2) (1 : F)) =
        Pi.single (0 : Fin 2) (1 : F) := by
      simpa using congrArg Prod.snd h
    have h2 := congrFun h1 (0 : Fin 2)
    simpa using h2
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : Fintype.card F + 1 ≠ 0)] at hμpow
    exact zero_ne_one hμpow
  have hμ1 : μ = 1 := scalar_eq_one μ hμpow hμ0
  intro u hu
  obtain ⟨h1, -⟩ := AddSubgroup.mem_prod.mp hu
  have h1' : u.1 = 0 := AddSubgroup.mem_bot.mp h1
  rw [show u = (0, u.2) from Prod.ext h1' rfl, hTapply', hμ1, one_smul]

private theorem fix_of_line (T : W2 F →+ W2 F)
    (hT : ∀ (g : SL(2, F)) u, T (slAct g u) = slAct g (T u))
    (hpow : ∀ u, (⇑T)^[Fintype.card F + 1] u = u)
    {U : AddSubgroup (W2 F)} (hTU : ∀ u ∈ U, T u ∈ U)
    (hline : U = AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤ ∨
      ∃ c : F, U = graphSub (n := 2) c) :
    ∀ u ∈ U, T u = u := by
  rcases hline with h | ⟨c, hc⟩
  · rw [h] at hTU ⊢
    exact fix_prod T hT hpow hTU
  · rw [hc] at hTU ⊢
    exact fix_graph T hT hpow hTU

private theorem line_ne_bot {U : AddSubgroup (W2 F)}
    (hline : U = AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤ ∨
      ∃ c : F, U = graphSub (n := 2) c) : U ≠ ⊥ := by
  intro hbot
  have hsingle : (Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  rcases hline with h | ⟨c, hc⟩
  · have hmem : ((0 : Fin 2 → F), Pi.single (0 : Fin 2) (1 : F)) ∈ U := by
      rw [h, AddSubgroup.mem_prod]
      exact ⟨AddSubgroup.mem_bot.mpr rfl, AddSubgroup.mem_top _⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    exact hsingle (congrArg Prod.snd hmem)
  · have hmem : (Pi.single (0 : Fin 2) (1 : F), c • Pi.single (0 : Fin 2) (1 : F)) ∈ U := by
      rw [hc]
      exact mem_graphSub.mpr rfl
    rw [hbot, AddSubgroup.mem_bot] at hmem
    exact hsingle (congrArg Prod.fst hmem)

private theorem eq_of_sq_eq_one_of_iterate (T : W2 F →+ W2 F)
    (hT2 : ∀ u, T (T u) = u) (hpow : ∀ u, (⇑T)^[Fintype.card F + 1] u = u) :
    ∀ u, T u = u := by
  have hodd : Odd (Fintype.card F + 1) :=
    (Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))).add_one
  obtain ⟨m, hm⟩ := hodd
  have hpow2 : (⇑T)^[2] = id := funext fun w => hT2 w
  have hIterOdd : ∀ (k : ℕ) (v : W2 F), (⇑T)^[2 * k + 1] v = T v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring]
        rw [Function.iterate_add_apply, hpow2]
        simpa using ih v
  intro u
  have h1 : (⇑T)^[Fintype.card F + 1] u = u := hpow u
  rw [hm, hIterOdd m u] at h1
  exact h1

private theorem false_of_line (T : W2 F →+ W2 F)
    (hT : ∀ (g : SL(2, F)) u, T (slAct g u) = slAct g (T u))
    (hpow : ∀ u, (⇑T)^[Fintype.card F + 1] u = u) (hne : ∃ u, T u ≠ u)
    {U : AddSubgroup (W2 F)} (hTU : ∀ u ∈ U, T u ∈ U)
    (hline : U = AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤ ∨
      ∃ c : F, U = graphSub (n := 2) c) : False := by
  have hUne : U ≠ ⊥ := line_ne_bot hline
  have hid : ∀ u ∈ U, T u = u := fix_of_line T hT hpow hTU hline
  let S : W2 F →+ W2 F :=
    { toFun := fun u => T u - u
      map_zero' := by simp
      map_add' := fun u v => by
        rw [map_add]
        abel }
  have hSval : ∀ u, S u = T u - u := fun u => rfl
  have hST : ∀ u, S (T u) = T (S u) := by
    intro u
    simp only [hSval, map_sub]
  have hScomm : ∀ (g : SL(2, F)) u, S (slAct g u) = slAct g (S u) := by
    intro g u
    have h1 : slAct g (T u - u) = slAct g (T u) - slAct g u := slAct_sub g (T u) u
    rw [hSval, hT, hSval, h1]
  have hSInv : IsSLInv S.range := by
    intro g u hu
    obtain ⟨v, rfl⟩ := hu
    exact ⟨slAct g v, hScomm g v⟩
  have hSstab : ∀ u ∈ S.range, T u ∈ S.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨T v, hST v⟩
  have hSne : S.range ≠ ⊥ := by
    intro hbot
    obtain ⟨u, hu⟩ := hne
    apply hu
    have hmem : S u ∈ S.range := ⟨u, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hStop : S.range ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective S := fun y => by
      have : y ∈ S.range := by rw [htop]; exact AddSubgroup.mem_top y
      exact this
    have hinj : Function.Injective S := Finite.injective_iff_surjective.mpr hsurj
    obtain ⟨⟨u, huU⟩, hune⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hUne
    have hune' : u ≠ 0 := fun h => hune (Subtype.ext h)
    have hzero : S u = 0 := by
      rw [hSval, sub_eq_zero]
      exact hid u huU
    exact hune' (hinj (by simpa using hzero))
  have hline' : S.range = AddSubgroup.prod (⊥ : AddSubgroup (Fin 2 → F)) ⊤ ∨
      ∃ c : F, S.range = graphSub (n := 2) c := by
    rcases isSLInv_classify (n := 2) (by norm_num) hSInv with h | h | h | ⟨c, hc⟩
    · exact absurd h hSne
    · exact absurd h hStop
    · exact Or.inl h
    · exact Or.inr ⟨c, hc⟩
  have hid2 : ∀ u ∈ S.range, T u = u := fix_of_line T hT hpow hSstab hline'
  have hS2 : ∀ u, S (S u) = 0 := by
    intro u
    have h4 : S u = T u - u := hSval u
    calc S (S u) = S (T u - u) := by rw [h4]
      _ = S (T u) - S u := map_sub S (T u) u
      _ = T (S u) - S u := by rw [hST u]
      _ = S u - S u := by rw [hid2 (S u) ⟨u, rfl⟩]
      _ = 0 := sub_self _
  have hT2 : ∀ u, T (T u) = u := by
    intro u
    have htu : T u = u + S u := by
      rw [hSval]
      abel
    calc T (T u) = T (u + S u) := by rw [htu]
      _ = T u + T (S u) := map_add T u (S u)
      _ = T u + S u := by rw [hid2 (S u) ⟨u, rfl⟩]
      _ = (u + S u) + S u := by rw [htu]
      _ = u + (S u + S u) := add_assoc u (S u) (S u)
      _ = u := by rw [w2_add_self (S u), add_zero]
  obtain ⟨u, hu⟩ := hne
  exact hu (eq_of_sq_eq_one_of_iterate T hT2 hpow u)


theorem eq_bot_or_top_of_isSLInv_of_commute {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (T : ((Fin 2 → F) × (Fin 2 → F)) →+ ((Fin 2 → F) × (Fin 2 → F)))
    (hT : ∀ (g : SL(2, F)) u, T (CFSG.CGT.Timmesfeld75.slAct g u) =
      CFSG.CGT.Timmesfeld75.slAct g (T u))
    (hpow : ∀ u, (⇑T)^[Fintype.card F + 1] u = u) (hne : ∃ u, T u ≠ u)
    {U : AddSubgroup ((Fin 2 → F) × (Fin 2 → F))}
    (hU : CFSG.CGT.Timmesfeld75.IsSLInv U)
    (hTU : ∀ u ∈ U, T u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases isSLInv_classify (n := 2) (by norm_num) hU with h | h | h | ⟨c, hc⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (false_of_line T hT hpow hne hTU (Or.inl h)).elim
  · exact (false_of_line T hT hpow hne hTU (Or.inr ⟨c, hc⟩)).elim

end CFSG.GroupTheory
