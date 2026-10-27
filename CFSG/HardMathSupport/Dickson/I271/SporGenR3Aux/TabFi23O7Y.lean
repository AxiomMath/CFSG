module

public import CFSG.LieType.Multipliers.O73Data
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Om
import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23O7

open CFSG.YGroups CFSG.YGroups.ModelNative CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.CosetEnumeration CFSG.LieType.Multipliers.O73 Matrix
open CFSG.RankThree.PartOne.N143.O7 (Om Iso)

private theorem map_evalWord' {G H : Type*} [Group G] [Group H] (φ : G →* H) (g : ℕ → G)
    (w : List ℕ) : φ (evalWord g w) = evalWord (fun c => φ (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

private theorem evalWord_const {G : Type*} [Group G] (a : G) (w : List ℕ) :
    evalWord (fun _ => a) w = a ^ w.length := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, ih, List.length_cons, pow_succ']

private theorem f1_mem : y322WordF1 ∈ eWords := by
  unfold eWords
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))

private theorem card_range_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

private instance :
    Finite (YGroup 3 2 2) :=
  Nat.finite_of_card_ne_zero (by rw [card_y322]; norm_num)

private theorem tMat_mul_self
    (i : Fin 8) : tMat (vecs i) * tMat (vecs i) = 1 :=
  (vecs_check.2.2.2.1 i).1

private theorem rMat_mul_self
    (i : Fin 8) : rMat (vecs i) * rMat (vecs i) = 1 :=
  (vecs_check.2.2.2.1 i).2

private noncomputable def tG (c : ℕ) : GL Idx (ZMod 3) :=
  if h : c < 8 then ⟨tMat (vecs c), tMat (vecs c), tMat_mul_self ⟨c, h⟩, tMat_mul_self ⟨c, h⟩⟩
  else 1

private noncomputable def rG (c : ℕ) : GL Idx (ZMod 3) :=
  if h : c < 8 then ⟨rMat (vecs c), rMat (vecs c), rMat_mul_self ⟨c, h⟩, rMat_mul_self ⟨c, h⟩⟩
  else 1

private def mOne : GL Idx (ZMod 3) := -1

private theorem rG_eq
    (c : ℕ) (hc : c < 8) : rG c = mOne * tG c := by
  ext i j
  simp only [rG, tG, hc, dite_true, mOne, Units.val_neg, tMat,
    neg_one_mul]
  exact (neg_neg _).symm

private theorem mOne_comm (A : GL Idx (ZMod 3)) : mOne * A = A * mOne := by
  simp [mOne]

private theorem mOne_mul_self : mOne * mOne = 1 := by
  simp [mOne]

private theorem code_lt (v : Idx → ZMod 3) : code v < 2187 := by
  have h : ∀ i, (v i).val < 3 := fun i => ZMod.val_lt (v i)
  have := h (.inl 0); have := h (.inl 1); have := h (.inl 2)
  have := h (.inr (.inl 0)); have := h (.inr (.inl 1)); have := h (.inr (.inl 2))
  have := h (.inr (.inr ()))
  unfold code
  omega

private theorem dec_injective
    : Function.Injective fun x : Fin 2187 => dec x := by
  intro x y h
  have hx := code_dec_check x
  have hy := code_dec_check y
  simp only at h
  rw [h] at hx
  exact Fin.ext (hx.symm.trans hy)

private theorem dec_surjective
    : Function.Surjective fun x : Fin 2187 => dec x := by
  have hcard : Nat.card (Idx → ZMod 3) ≤ Nat.card (Fin 2187) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  exact (dec_injective.bijective_of_nat_card_le hcard).2

private theorem dec_code (v : Idx → ZMod 3) :
    dec (code v) = v := by
  obtain ⟨x, rfl⟩ := dec_surjective v
  simp only
  rw [code_dec_check x]

private noncomputable def cE : (Idx → ZMod 3) ≃ Fin 2187 where
  toFun v := ⟨code v, code_lt v⟩
  invFun x := dec x
  left_inv v := dec_code v
  right_inv x := Fin.ext (code_dec_check x)

private noncomputable def ψ
    : GL Idx (ZMod 3) →* Equiv.Perm (Fin 2187) :=
  (Equiv.permCongrHom cE).toMonoidHom.comp
    ((MulAction.toPermHom ((Idx → ZMod 3) ≃ₗ[ZMod 3] (Idx → ZMod 3)) (Idx → ZMod 3)).comp
      (ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 3)).toMonoidHom)

private theorem ψ_apply (A : GL Idx (ZMod 3)) (x : Fin 2187) :
    ((ψ A x : Fin 2187) : ℕ) = code ((A : Matrix Idx Idx (ZMod 3)) *ᵥ dec x) := rfl

private theorem ψ_injective : Function.Injective ψ := by
  intro A B h
  apply (ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 3)).injective
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, rfl⟩ := dec_surjective v
  have := congrArg (fun g : Equiv.Perm (Fin 2187) => ((g x : Fin 2187) : ℕ)) h
  simp only [ψ_apply] at this
  rw [ClassicalGroups.Orthogonal.toLinEquiv_apply, ClassicalGroups.Orthogonal.toLinEquiv_apply,
    ← dec_code ((A : Matrix Idx Idx (ZMod 3)) *ᵥ dec x),
    ← dec_code ((B : Matrix Idx Idx (ZMod 3)) *ᵥ dec x), this]

private theorem getElem!_ofFn' {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem rep_tabOf
    {A : GL Idx (ZMod 3)} {M : Matrix Idx Idx (ZMod 3)}
    (hA : (A : Matrix Idx Idx (ZMod 3)) = M) : Rep 2187 (tabOf M) (ψ A) := fun x => by
  rw [tabOf, getElem!_ofFn_nat _ x.2, ψ_apply, hA]

private theorem ψ_tG (c : ℕ) : ψ (tG c) = arrGen 2187 tTabs c := by
  by_cases hc : c < 8
  · have h1 : Rep 2187 tTabs[c]! (ψ (tG c)) := by
      rw [tTabs, getElem!_ofFn' _ hc]
      exact rep_tabOf (by simp [tG, hc])
    have h2 := rep_letterOf vecs_check.2.2.2.2.1 c
    rw [letterOf, ite_eq_left (by rw [vecs_check.2.1]; exact hc)] at h2
    exact Rep.unique h1 h2
  · rw [tG, dite_eq_right hc, map_one, arrGen_of_le (by rw [vecs_check.2.1]; omega)]

private theorem ψ_rG (c : ℕ) : ψ (rG c) = arrGen 2187 rTabs c := by
  by_cases hc : c < 8
  · have h1 : Rep 2187 rTabs[c]! (ψ (rG c)) := by
      rw [rTabs, getElem!_ofFn' _ hc]
      exact rep_tabOf (by simp [rG, hc])
    have h2 := rep_letterOf vecs_check.2.2.2.2.2.1 c
    rw [letterOf, ite_eq_left (by rw [vecs_check.2.2.1]; exact hc)] at h2
    exact Rep.unique h1 h2
  · rw [rG, dite_eq_right hc, map_one, arrGen_of_le (by rw [vecs_check.2.2.1]; omega)]

private theorem evalWord_tG_eq_one
    {w : List ℕ} (hw : w ∈ yRels 3 2 2 ++ eWords) :
    evalWord tG w = 1 := by
  apply ψ_injective
  rw [map_evalWord', map_one]
  simp only [ψ_tG]
  exact evalWord_arrGen_eq_one vecs_check.2.2.2.2.1 relators_check.1 w hw

private theorem evalWord_rG_eq_one
    {w : List ℕ} (hw : w ∈ yRels 3 2 2) :
    evalWord rG w = 1 := by
  apply ψ_injective
  rw [map_evalWord', map_one]
  simp only [ψ_rG]
  exact evalWord_arrGen_eq_one vecs_check.2.2.2.2.2.1 relators_check.2.1 w hw

private noncomputable def τ : YGroup 3 2 2 →* GL Idx (ZMod 3) :=
  yModelHom tG fun _ hw => evalWord_tG_eq_one (List.mem_append_left _ hw)

private noncomputable def ρ : YGroup 3 2 2 →* GL Idx (ZMod 3) :=
  yModelHom rG fun _ hw => evalWord_rG_eq_one hw

private noncomputable def βf (x : Fin 728) : Fin 2187 :=
  ⟨betaArr[x.val]!, beta_check.2.1 x⟩

private theorem βf_injective : Function.Injective βf :=
  fun x y h => beta_check.2.2.1 x y (congrArg Fin.val h)

private theorem ρ_beta
    (g : YGroup 3 2 2) (x : Fin 728) : ψ (ρ g) (βf x) = βf (y322Model g x) := by
  let S : Subgroup (YGroup 3 2 2) :=
    { carrier := {g | ∀ x, ψ (ρ g) (βf x) = βf (y322Model g x)}
      one_mem' := fun x => by simp
      mul_mem' := fun {g h} hg hh x => by
        simp only [Set.mem_ofPred_eq] at hg hh ⊢
        rw [map_mul, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hh x, hg]
      inv_mem' := fun {g} hg x => by
        simp only [Set.mem_ofPred_eq, map_inv] at hg ⊢
        have := hg ((y322Model g)⁻¹ x)
        rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
        rw [Equiv.Perm.inv_eq_iff_eq, this] }
  have hS : Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩ x
    have hc' : c < 8 := by simpa [ngen] using hc
    have hρ : ρ (yGen 3 2 2 c) = rG c := yModelHom_yGen hc
    rw [hρ, ψ_rG]
    apply Fin.ext
    have h1 := (rep_letterOf vecs_check.2.2.2.2.2.1 c) (βf x)
    rw [letterOf, ite_eq_left (by rw [vecs_check.2.2.1]; exact hc')] at h1
    rw [← h1, βf]
    simp only
    rw [beta_check.2.2.2 ⟨c, hc'⟩ x, (y322Model_rep hc') x]
    rfl
  exact (hS (by rw [closure_yGen]; trivial)) x

private theorem ρ_injective :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply y322Model_injective
  rw [map_one]
  ext x
  have := ρ_beta g x
  rw [hg, map_one, Equiv.Perm.one_apply] at this
  rw [βf_injective this.symm]
  rfl

private theorem ρ_eq_or
    (g : YGroup 3 2 2) : ρ g = τ g ∨ ρ g = mOne * τ g := by
  let S : Subgroup (YGroup 3 2 2) :=
    { carrier := {g | ρ g = τ g ∨ ρ g = mOne * τ g}
      one_mem' := Or.inl (by simp)
      mul_mem' := fun {g h} hg hh => by
        simp only [Set.mem_ofPred_eq, map_mul] at hg hh ⊢
        rcases hg with hg | hg <;> rcases hh with hh | hh <;> rw [hg, hh]
        · exact Or.inl rfl
        · right; rw [← mul_assoc, ← mOne_comm, mul_assoc]
        · right; rw [mul_assoc]
        · left; rw [mul_assoc, ← mul_assoc (τ g), ← mOne_comm, ← mul_assoc, ← mul_assoc,
            mOne_mul_self, one_mul]
      inv_mem' := fun {g} hg => by
        simp only [Set.mem_ofPred_eq, map_inv] at hg ⊢
        rcases hg with hg | hg <;> rw [hg]
        · exact Or.inl rfl
        · right
          rw [_root_.mul_inv_rev, mOne_comm, inv_eq_of_mul_eq_one_left mOne_mul_self] }
  have hS : Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c < 8 := by simpa [ngen] using hc
    right
    show ρ (yGen 3 2 2 c) = mOne * τ (yGen 3 2 2 c)
    rw [ρ, τ, yModelHom_yGen hc, yModelHom_yGen hc, rG_eq c hc']
  exact hS (by rw [closure_yGen]; trivial)

private theorem card_ker_τ_le :
    Nat.card τ.ker ≤ 2 := by
  let f : τ.ker → ({1, mOne} : Set (GL Idx (ZMod 3))) := fun g =>
    ⟨ρ g, by
      rcases ρ_eq_or g with h | h <;> rw [h, MonoidHom.mem_ker.1 g.2]
      · exact Or.inl rfl
      · exact Or.inr (mul_one _)⟩
  have hf : Function.Injective f := fun g h hgh =>
    Subtype.ext (ρ_injective (congrArg Subtype.val hgh))
  calc Nat.card τ.ker ≤ Nat.card ({1, mOne} : Set (GL Idx (ZMod 3))) :=
        Nat.card_le_card_of_injective f hf
    _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

private theorem τ_yGen {c : ℕ} (hc : c < 8) :
    τ (yGen 3 2 2 c) = tG c :=
  yModelHom_yGen hc

private theorem τ_f1 : τ y322F1 = 1 := by
  have hlt : ∀ c ∈ y322WordF1, c < 8 := by decide
  rw [y322F1, map_evalWord', evalWord_congr (g' := tG) (fun c hc => τ_yGen (hlt c hc))]
  exact evalWord_tG_eq_one (List.mem_append_right _ f1_mem)

private theorem tG_isometry (c : ℕ) (v : Idx → ZMod 3) :
    q3 ((tG c : Matrix Idx Idx (ZMod 3)) *ᵥ v) = q3 v := by
  by_cases hc : c < 8
  · obtain ⟨x, rfl⟩ := dec_surjective v
    have h := vecs_check.2.2.2.2.2.2 ⟨c, hc⟩ x
    simp only [tG, dite_eq_left hc]
    exact h
  · simp [tG, hc]

private theorem top_eq_commutator_sup :
    (⊤ : Subgroup (YGroup 3 2 2)) = commutator (YGroup 3 2 2) ⊔ Subgroup.zpowers y322F1 := by
  set a : ℕ → Abelianization (YGroup 3 2 2) :=
    fun c => Abelianization.of (yGen 3 2 2 c) with ha
  have hsq : ∀ c, a c * a c = 1 := fun c => by
    simp only [ha, ← map_mul, yGen_mul_self, map_one]
  have hinv : ∀ c, (a c)⁻¹ = a c := fun c => inv_eq_of_mul_eq_one_left (hsq c)
  have hval : ∀ w ∈ yRels 3 2 2, evalWord a w = 1 := fun w hw => by
    rw [ha, ← map_evalWord' Abelianization.of (yGen 3 2 2) w, evalWord_yGen_of_mem hw, map_one]
  have hedge : ∀ e ∈ [(0, 1), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (6, 7)],
      [e.1, e.2, e.1, e.2, e.1, e.2] ∈ yRels 3 2 2 := by decide +kernel
  have hadj : ∀ e ∈ [(0, 1), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (6, 7)],
      a e.2 = a e.1 := fun e he => by
    have h := hval _ (hedge e he)
    simp only [evalWord_cons, evalWord_nil, mul_one] at h
    have h' : a e.1 * a e.2 = 1 := by
      calc a e.1 * a e.2 = (a e.1 * a e.1) * (a e.1 * a e.2) * (a e.2 * a e.2) := by
            rw [hsq, hsq, one_mul, mul_one]
        _ = a e.1 * (a e.2 * (a e.1 * (a e.2 * (a e.1 * a e.2)))) := by
            simp only [mul_comm, mul_left_comm]
        _ = 1 := h
    rw [← hinv (e.1), eq_inv_iff_mul_eq_one, mul_comm]
    exact h'
  have hall : ∀ c < 8, a c = a 0 := by
    have h01 := hadj (0, 1) (by simp)
    have h04 := hadj (0, 4) (by simp)
    have h06 := hadj (0, 6) (by simp)
    have h12 := hadj (1, 2) (by simp)
    have h23 := hadj (2, 3) (by simp)
    have h45 := hadj (4, 5) (by simp)
    have h67 := hadj (6, 7) (by simp)
    simp only at h01 h04 h06 h12 h23 h45 h67
    intro c hc
    interval_cases c
    · rfl
    · exact h01
    · exact h12.trans h01
    · exact h23.trans (h12.trans h01)
    · exact h04
    · exact h45.trans h04
    · exact h06
    · exact h67.trans h06
  have hlen : y322WordF1.length = 63 := by decide
  have hf1 : Abelianization.of y322F1 = a 0 := by
    have hlt : ∀ c ∈ y322WordF1, c < 8 := by decide
    rw [y322F1, map_evalWord' Abelianization.of (yGen 3 2 2) y322WordF1]
    change evalWord a y322WordF1 = a 0
    rw [evalWord_congr (g' := fun _ => a 0) (fun c hc => hall c (hlt c hc)), evalWord_const, hlen,
      show 63 = 2 * 31 + 1 by norm_num, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
  have h1 : (Subgroup.zpowers y322F1).map (Abelianization.of (G := YGroup 3 2 2)) = ⊤ := by
    rw [MonoidHom.map_zpowers, hf1, eq_top_iff]
    have : (⊤ : Subgroup (Abelianization (YGroup 3 2 2))) =
        (Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2))).map Abelianization.of := by
      rw [closure_yGen, ← MonoidHom.range_eq_map]
      exact (MonoidHom.range_eq_top.2
        (fun x => QuotientGroup.induction_on x fun g => ⟨g, rfl⟩)).symm
    rw [this, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have hc' : c < 8 := by simpa [ngen] using hc
    change a c ∈ _
    rw [hall c hc']
    exact Subgroup.mem_zpowers _
  have h2 := congrArg (Subgroup.comap (Abelianization.of (G := YGroup 3 2 2))) h1
  rw [Subgroup.comap_map_eq, Subgroup.comap_top, Abelianization.ker_of] at h2
  rw [sup_comm]
  exact h2.symm

private theorem range_τ_le_om : τ.range ≤ Om := by
  have hiso : τ.range ≤ Iso := by
    rw [τ, range_yModelHom, Subgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact Subgroup.subset_closure (tG_isometry c)
  have hrange : τ.range = ⁅τ.range, τ.range⁆ := by
    have h := congrArg (Subgroup.map τ) top_eq_commutator_sup
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, τ_f1, Subgroup.zpowers_one_eq_bot, sup_bot_eq,
      commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h
    exact h
  rw [hrange]
  exact Subgroup.commutator_mono hiso hiso

private theorem range_τ_eq_om :
    τ.range = Om := by
  have hfin : Finite ↥Om := Nat.finite_of_card_ne_zero (by rw [tabFi23_card_om]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge range_τ_le_om ?_
  rw [tabFi23_card_om]
  have h := card_range_mul_card_ker τ
  rw [card_y322] at h
  by_contra hlt
  have := Nat.mul_le_mul (Nat.le_sub_one_of_lt (Nat.lt_of_not_le hlt)) card_ker_τ_le
  omega

end CFSG.HardMathSupport.Dickson.I271.TabFi23O7

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.YGroups
open CFSG.LieType.Multipliers.O73 (Idx)
open CFSG.RankThree.PartOne.N143.O7 (Om)

theorem tabFi23_y322_to_om :
    ∃ π : YGroup 3 2 2 →* ↥Om, Function.Surjective π ∧ π.ker = Subgroup.zpowers y322F1 ∧
      Nat.card π.ker = 2 := by
  have hf1 : Subgroup.zpowers y322F1 ≤ TabFi23O7.τ.ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact TabFi23O7.τ_f1
  have hne : Subgroup.zpowers y322F1 ≠ ⊥ := fun h => y322F1_ne_one (Subgroup.zpowers_eq_bot.1 h)
  have h2 : 1 < Nat.card (Subgroup.zpowers y322F1) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hle := TabFi23O7.card_ker_τ_le
  have hker : Subgroup.zpowers y322F1 = TabFi23O7.τ.ker :=
    Subgroup.eq_of_le_of_card_ge hf1 (by omega)
  refine ⟨TabFi23O7.τ.codRestrict Om fun y => TabFi23O7.range_τ_le_om ⟨y, rfl⟩, ?_, ?_, ?_⟩
  · intro o
    have ho : (o : GL Idx (ZMod 3)) ∈ TabFi23O7.τ.range := by
      rw [TabFi23O7.range_τ_eq_om]
      exact o.2
    obtain ⟨y, hy⟩ := ho
    exact ⟨y, Subtype.ext hy⟩
  · rw [MonoidHom.ker_codRestrict, hker]
  · rw [MonoidHom.ker_codRestrict, ← hker]
    have hle' : Nat.card (Subgroup.zpowers y322F1) ≤ 2 := by
      rw [hker]
      exact hle
    omega

end CFSG.HardMathSupport.Dickson.I271
