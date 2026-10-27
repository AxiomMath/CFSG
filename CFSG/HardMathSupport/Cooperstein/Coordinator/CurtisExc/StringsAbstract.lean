module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.Quasithin.Background.SmithCurtisBasic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Abstract

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [Algebra K k] [CharP k 2]
  {V : Type} [AddCommGroup V] [Module k V]

@[expose] def upperHom (K : Type) [Field K] : Multiplicative K →* SL(2, K) where
  toFun c := uElt (Multiplicative.toAdd c)
  map_one' := uElt_zero
  map_mul' a b := uElt_add _ _

theorem isPGroup_range_upperHom : IsPGroup 2 (upperHom K).range := by
  rintro ⟨_, c, rfl⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (upperHom K c) ^ (2 ^ 1) = 1
  rw [pow_one, pow_two, ← map_mul]
  have : c * c = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero _
  rw [this, map_one]

theorem mem_fixSub_upper {σ : Representation k SL(2, K) V} {f : V} :
    f ∈ fixSub σ (upperHom K).range ↔ ∀ c : K, σ (uElt c) f = f := by
  constructor
  · intro h c
    exact h _ ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro h _ ⟨c, rfl⟩
    exact h (Multiplicative.toAdd c)

theorem orbitSpan_isSimple (σ : Representation k SL(2, K) V) {v : V} (Fix : Submodule k V)
    (hvF : v ∈ Fix) (hFst : ∀ g : SL(2, K), ∀ w ∈ Fix, σ g w ∈ Fix)
    (hfix : ∀ f ∈ Fix, (∀ c : K, σ (uElt c) f = f) → ∃ c : k, f = c • v)
    (W' : Submodule k V) (hW' : W' ≤ orbitSpan σ v) (hst : ∀ g : SL(2, K), ∀ w ∈ W', σ g w ∈ W') :
    W' = ⊥ ∨ W' = orbitSpan σ v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (upperHom K).range := Set.finite_range _ |>.to_subtype
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  have hN : orbitSpan σ v ≤ Fix := by
    rw [orbitSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hFst g v hvF
  obtain ⟨f, hfW, hf0, hffix⟩ := exists_fixed_mem σ isPGroup_range_upperHom hst hbot
  obtain ⟨c, hc⟩ := hfix f (hN (hW' hfW)) (mem_fixSub_upper.1 hffix)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hc, zero_smul])
  have hvW : v ∈ W' := by
    have : c⁻¹ • f ∈ W' := W'.smul_mem _ hfW
    rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine le_antisymm hW' ?_
  rw [orbitSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact hst g v hvW

theorem prod_zpow_eq_zpow_sum {k' : Type*} [Field k'] {ι : Type*} (s : Finset ι) (w : k') (hw : w ≠ 0)
    (f : ι → ℤ) : ∏ i ∈ s, w ^ f i = w ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih => rw [Finset.prod_insert has, Finset.sum_insert has, zpow_add₀ hw, ih]

theorem tensorRep_dElt_single {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (z : Kˣ)
    (y0 : ι → Fin 2) :
    tensorRep K k e (dElt z) (Pi.single y0 1) =
      (algebraMap K k (z : K)) ^ (((∑ i, 2 ^ e i : ℕ) : ℤ) - 2 * (aexp e y0 : ℤ)) •
        (Pi.single y0 1 : (ι → Fin 2) → k) := by
  have hz : (algebraMap K k (z : K)) ≠ 0 := by simpa using z.ne_zero
  funext x'
  rw [tensorRep_apply, Finset.sum_eq_single y0]
  · rw [Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x' = y0
    · subst hx
      rw [Pi.single_eq_same, mul_one]
      unfold tmatE
      have hf : ∀ i, twistMat k (e i) (dElt z) (x' i) (x' i) =
          (algebraMap K k (z : K)) ^ (((2 ^ e i : ℕ) : ℤ) - 2 * (((x' i : ℕ) * 2 ^ e i : ℕ) : ℤ)) := by
        intro i
        rw [twistMat_dElt]
        rcases fin2_cases (x' i) with h | h
        · simp only [h, Fin.val_zero, zero_mul, Nat.cast_zero, mul_zero, sub_zero, Fin.isValue,
            Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
          rw [zpow_natCast]
        · simp only [h, Fin.val_one, one_mul, Nat.cast_pow, Nat.cast_ofNat, Fin.isValue,
            Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [show ((2 : ℤ) ^ e i - 2 * 2 ^ e i) = -((2 ^ e i : ℕ) : ℤ) by push_cast; ring,
            zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, map_inv₀, inv_pow]
      rw [Finset.prod_congr rfl fun i _ => hf i, prod_zpow_eq_zpow_sum _ _ hz]
      congr 1
      unfold aexp
      push_cast
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    · rw [Pi.single_eq_of_ne hx, mul_zero]
      have hx' : ∃ i, x' i ≠ y0 i := by
        by_contra hc
        push Not at hc
        exact hx (funext hc)
      obtain ⟨i, hi⟩ := hx'
      have : tmatE k e (dElt z) x' y0 = 0 := by
        unfold tmatE
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [twistMat_dElt]
        rcases fin2_cases (x' i) with h | h <;> rcases fin2_cases (y0 i) with h' | h' <;>
          simp_all
      rw [this]
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, mul_zero]
  · simp

theorem string_data {n : ℕ} (hK : Nat.card K = 2 ^ n) (σ : Representation k SL(2, K) V) {v : V}
    (hv0 : v ≠ 0) (Fix : Submodule k V) (hvF : v ∈ Fix)
    (hFst : ∀ g : SL(2, K), ∀ w ∈ Fix, σ g w ∈ Fix)
    (hfix : ∀ f ∈ Fix, (∀ c : K, σ (uElt c) f = f) → ∃ c : k, f = c • v)
    (hvu : ∀ c : K, σ (uElt c) v = v) (ε : Kˣ → k)
    (hε : ∀ z : Kˣ, σ (dElt z) v = ε z • v) :
    ∃ J : Finset ℕ, (∀ i ∈ J, i < n) ∧
      (∀ z : Kˣ, ε z = (algebraMap K k (z : K)) ^ (∑ i ∈ J, 2 ^ i)) ∧
      Module.finrank k (orbitSpan σ v) = 2 ^ J.card ∧ (J = ∅ → ∀ g, σ g v = v) ∧
      (∀ b ∈ J, ∃ e ∈ orbitSpan σ v, e ≠ 0 ∧ ∀ z : Kˣ, σ (dElt z) e =
        (algebraMap K k (z : K)) ^ (((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) - 2 ^ (b + 1)) • e) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  set N := orbitSpan σ v with hNdef
  have hNst : ∀ g : SL(2, K), ∀ w ∈ N, σ g w ∈ N := fun g w hw => orbitSpan_stable σ v g hw
  have hvN : v ∈ N := mem_orbitSpan_self σ v
  let τσ : Representation k SL(2, K) N := restrictRep σ N hNst
  have hτσ : ∀ g (w : N), ((τσ g w : N) : V) = σ g w := fun g w => rfl
  have hirr : τσ.IsIrreducible := by
    rw [isIrreducible_iff]
    refine ⟨⟨⟨⟨v, hvN⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩, fun U hU => ?_⟩
    have hst : ∀ g : SL(2, K), ∀ w ∈ U.map N.subtype, σ g w ∈ U.map N.subtype := by
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨τσ g u, hU g u hu, rfl⟩
    rcases orbitSpan_isSimple σ Fix hvF hFst hfix (U.map N.subtype)
      (by rintro _ ⟨u, -, rfl⟩; exact u.2) hst with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have : (u : V) ∈ U.map N.subtype := ⟨u, hu, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro x _
      have : (x : V) ∈ U.map N.subtype := by rw [h]; exact x.2
      obtain ⟨u, hu, hux⟩ := this
      have : u = x := Subtype.ext hux
      rwa [← this]
  obtain ⟨J, ⟨hJ, ⟨Φ⟩⟩, -⟩ := frobTensor_classification hF τσ hirr
  let v' : N := ⟨v, hvN⟩
  have hv'0 : v' ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hΦ0 : Φ v' ≠ 0 := fun h => hv'0 (Φ.toLinearEquiv.injective (by rw [map_zero]; exact h))
  have hΦu : ∀ t : K, frobTensor K k J (uElt t) (Φ v') = Φ v' := by
    intro t
    rw [← equiv_apply Φ]
    congr 1
    exact Subtype.ext (hvu t)
  obtain ⟨c, hc⟩ := (tensorRep_fixed_iff hF (fun i : J => (i : ℕ)) Subtype.val_injective
    (fun i => hJ i i.2) (Φ v')).1 hΦu
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΦ0 (by rw [hc, zero_smul])
  have hb0 : (baseVec : (J → Fin 2) → k) ≠ 0 := by
    intro h
    exact hΦ0 (by rw [hc, h, smul_zero])
  refine ⟨J, hJ, fun z => ?_, ?_, ?_, ?_⟩
  · have h1 : Φ (τσ (dElt z) v') = ε z • Φ v' := by
      have : τσ (dElt z) v' = ε z • v' := Subtype.ext (hε z)
      rw [this, map_smul]
    rw [equiv_apply Φ, hc, map_smul, frobTensor_dElt_baseVec, smul_smul, smul_smul] at h1
    have h3 := smul_left_injective k hb0 h1
    have : (algebraMap K k (z : K)) ^ (∑ i ∈ J, 2 ^ i) = ε z := by
      refine mul_right_cancel₀ hc0 ?_
      rw [mul_comm] at h3
      exact h3
    exact this.symm
  · have := Φ.toLinearEquiv.finrank_eq
    rw [finrank_frobTensor] at this
    exact this
  · intro hJ0 g
    subst hJ0
    have h1 : frobTensor K k ∅ g (Φ v') = Φ v' := frobTensor_empty_apply g _
    rw [← equiv_apply Φ] at h1
    have := Φ.toLinearEquiv.injective h1
    exact congrArg Subtype.val this
  · intro b hb
    let y0 : J → Fin 2 := fun i => if (i : ℕ) = b then 1 else 0
    obtain ⟨e, he⟩ : ∃ e : N, Φ e = Pi.single y0 1 :=
      ⟨Φ.toLinearEquiv.symm (Pi.single y0 1), Φ.toLinearEquiv.apply_symm_apply _⟩
    have haexp : aexp (fun i : J => (i : ℕ)) y0 = 2 ^ b := by
      unfold aexp
      rw [Finset.sum_eq_single (⟨b, hb⟩ : J)]
      · simp [y0]
      · intro i _ hi
        have : (i : ℕ) ≠ b := fun h => hi (Subtype.ext h)
        simp [y0, this]
      · simp
    have hsum : (∑ i : J, 2 ^ (fun i : J => (i : ℕ)) i) = ∑ i ∈ J, 2 ^ i := by
      rw [Finset.univ_eq_attach, Finset.sum_attach J (fun i => 2 ^ i)]
    refine ⟨(e : V), e.2, ?_, fun z => ?_⟩
    · intro h0
      have : e = 0 := Subtype.ext h0
      rw [this, map_zero] at he
      have := congrFun he y0
      simp at this
    · have h1 : Φ (τσ (dElt z) e) = tensorRep K k (fun i : J => (i : ℕ)) (dElt z) (Φ e) :=
        equiv_apply Φ _ _
      rw [he, tensorRep_dElt_single, hsum, haexp] at h1
      have h2 : Φ (τσ (dElt z) e) = Φ (((algebraMap K k (z : K)) ^ (((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) -
          2 ^ (b + 1))) • e) := by
        rw [h1, map_smul, he]
        congr 2
        push_cast
        ring
      exact congrArg Subtype.val (Φ.toLinearEquiv.injective h2)

set_option maxHeartbeats 1600000 in
theorem finrank_iSup_orbitSpan [Module.Finite k V] {ι : Type*} [DecidableEq ι]
    (σ : Representation k SL(2, K) V) (v : ι → V) (Fix : ι → Submodule k V)
    (hvF : ∀ i, v i ∈ Fix i) (hFst : ∀ i, ∀ g : SL(2, K), ∀ w ∈ Fix i, σ g w ∈ Fix i)
    (hfix : ∀ i, ∀ f ∈ Fix i, (∀ c : K, σ (uElt c) f = f) → ∃ c : k, f = c • v i)
    (hvu : ∀ i, ∀ c : K, σ (uElt c) (v i) = v i) (s : Finset ι)
    (hli : LinearIndepOn k v (↑s : Set ι)) :
    Module.finrank k (⨆ i ∈ s, orbitSpan σ (v i) : Submodule k V) =
        ∑ i ∈ s, Module.finrank k (orbitSpan σ (v i)) ∧
      (∀ f ∈ (⨆ i ∈ s, orbitSpan σ (v i) : Submodule k V),
        (∀ c : K, σ (uElt c) f = f) → f ∈ Submodule.span k (v '' (↑s : Set ι))) ∧
      s.SupIndep (fun i => orbitSpan σ (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun f hf _ => ?_, Finset.supIndep_empty _⟩
    simp at hf
    simp [hf]
  | insert a s has ih =>
    have hli' : LinearIndepOn k v (↑s : Set ι) := hli.mono (by simp)
    have hins : LinearIndepOn k v (insert a (↑s : Set ι)) := by simpa using hli
    obtain ⟨hli1, hli2⟩ := (linearIndepOn_insert (by simpa using has)).1 hins
    obtain ⟨ihd, ihf, ihs⟩ := ih hli'
    set T : Submodule k V := ⨆ i ∈ s, orbitSpan σ (v i) with hT
    set Na := orbitSpan σ (v a) with hNa
    have hTst : ∀ g : SL(2, K), ∀ w ∈ T, σ g w ∈ T := by
      intro g w hw
      have : T ≤ (T.comap (σ g)) := by
        rw [hT]
        refine iSup₂_le fun i hi => ?_
        rw [orbitSpan, Submodule.span_le]
        rintro _ ⟨h, rfl⟩
        show σ g (σ h (v i)) ∈ T
        rw [act_mul]
        exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi
          (Submodule.subset_span ⟨g * h, rfl⟩))
      exact this hw
    have hv_notin : v a ∉ T := by
      intro hvT
      exact hli2 (ihf _ hvT (hvu a))
    have hinf : T ⊓ Na = ⊥ := by
      rcases orbitSpan_isSimple σ (Fix a) (hvF a) (hFst a) (hfix a) (T ⊓ Na) inf_le_right
        (fun g w hw => ⟨hTst g w hw.1, orbitSpan_stable σ (v a) g hw.2⟩) with h | h
      · exact h
      · exfalso
        apply hv_notin
        have : v a ∈ T ⊓ Na := by rw [h]; exact mem_orbitSpan_self σ _
        exact this.1
    have hsup : (⨆ i ∈ insert a s, orbitSpan σ (v i) : Submodule k V) = Na ⊔ T := by
      rw [Finset.iSup_insert]
    have hsup' : (⨆ i ∈ insert a s, orbitSpan σ (v i) : Submodule k V) = T ⊔ Na := by
      rw [hsup, sup_comm]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsup', Finset.sum_insert has]
      have h := Submodule.finrank_sup_add_finrank_inf_eq T Na
      rw [hinf, finrank_bot] at h
      change Module.finrank k ↥(T ⊔ Na) = Module.finrank k ↥Na + ∑ i ∈ s, Module.finrank k (orbitSpan σ (v i))
      rw [← ihd]
      omega
    · intro f hf hfu
      rw [hsup', Submodule.mem_sup] at hf
      obtain ⟨x, hx, y, hy, rfl⟩ := hf
      have hx0 : ∀ c : K, σ (uElt c) x = x := by
        intro c
        have hsum : (σ (uElt c) x - x) + (σ (uElt c) y - y) = 0 := by
          have := hfu c
          rw [map_add] at this
          calc (σ (uElt c) x - x) + (σ (uElt c) y - y)
              = (σ (uElt c) x + σ (uElt c) y) - (x + y) := by abel
            _ = 0 := sub_eq_zero.2 this
        have h1 : σ (uElt c) x - x ∈ T := T.sub_mem (hTst _ x hx) hx
        have h2 : σ (uElt c) x - x ∈ Na := by
          rw [eq_neg_of_add_eq_zero_left hsum]
          exact Na.neg_mem (Na.sub_mem (orbitSpan_stable σ (v a) _ hy) hy)
        have : σ (uElt c) x - x ∈ T ⊓ Na := ⟨h1, h2⟩
        rw [hinf, Submodule.mem_bot, sub_eq_zero] at this
        exact this
      have hy0 : ∀ c : K, σ (uElt c) y = y := by
        intro c
        have := hfu c
        rw [map_add, hx0 c] at this
        exact add_left_cancel this
      have hNaFix : Na ≤ Fix a := by
        rw [hNa, orbitSpan, Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact hFst a g _ (hvF a)
      obtain ⟨c, hc⟩ := hfix a y (hNaFix hy) hy0
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 (Finset.subset_insert a s)))
          (ihf x hx hx0)
      · rw [hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, by simp, rfl⟩)
    · refine ihs.insert ?_
      rw [Finset.sup_eq_iSup]
      exact disjoint_comm.1 (disjoint_iff.2 hinf)

end Abstract

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
