module

public import CFSG.LieType.BorelTits.Flag
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Parab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

open CFSG.LieType.BorelTits CFSG.Open Subgroup Module
open scoped MatrixGroups

variable {F : Type*} [Field F] {K : Type*} [Group K]

@[expose] noncomputable def rep (σ : K ≃* SL(3, F)) : K →* Module.End F (Fin 3 → F) where
  toFun x := Matrix.toLin' ((σ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
  map_one' := by rw [map_one, coe_SL_one, Matrix.toLin'_one]; rfl
  map_mul' x y := by rw [map_mul, coe_SL_mul, Matrix.toLin'_mul]; rfl

theorem rep_apply (σ : K ≃* SL(3, F)) (x : K) :
    rep σ x = Matrix.toLin' ((σ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := rfl

theorem rep_injective (σ : K ≃* SL(3, F)) : Function.Injective (rep σ) := by
  intro x y h
  apply σ.injective
  apply Subtype.ext
  exact Matrix.toLin'.injective h

theorem det_rep (σ : K ≃* SL(3, F)) (x : K) : LinearMap.det (rep σ x) = 1 := by
  rw [rep_apply, LinearMap.det_toLin']
  exact (σ x).2

theorem sub_mem_of_pow_two_eq_one [CharP F 2] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) {a : ℕ} (hT : T ^ 2 ^ a = 1)
    {W W' : Submodule F V} (hW : ∀ v ∈ W, T v ∈ W) (hW' : ∀ v ∈ W', T v ∈ W') (hlt : W < W')
    (hrank : finrank F W' = finrank F W + 1) : ∀ v ∈ W', T v - v ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, huW', huW⟩ := SetLike.exists_of_lt hlt
  have hle : W ⊔ Submodule.span F {u} ≤ W' :=
    sup_le hlt.le (Submodule.span_le.2 (Set.singleton_subset_iff.2 huW'))
  have hlt' : W < W ⊔ Submodule.span F {u} :=
    lt_of_le_of_ne le_sup_left fun h =>
      huW (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
  have hr1 := Submodule.finrank_lt_finrank_of_lt hlt'
  have hr2 := Submodule.finrank_mono hle
  have hW'eq : W ⊔ Submodule.span F {u} = W' :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  obtain ⟨w₀, hw₀, y, hy, hsum⟩ := Submodule.mem_sup.1 (hW'eq ▸ hW' u huW')
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hpow : ∀ m : ℕ, (T ^ m) u - c ^ m • u ∈ W := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have key : (T ^ (m + 1)) u - c ^ (m + 1) • u = T ((T ^ m) u - c ^ m • u) + c ^ m • w₀ := by
        rw [pow_succ', Module.End.mul_apply, map_sub, map_smul, ← hsum, smul_add, smul_smul,
          pow_succ]
        abel
      rw [key]
      exact W.add_mem (hW _ ih) (W.smul_mem _ hw₀)
  have h1 := hpow (2 ^ a)
  rw [hT, Module.End.one_apply, ← one_smul F u, smul_smul, mul_one, ← sub_smul] at h1
  have hc : c ^ 2 ^ a = 1 := by
    by_contra hne
    apply huW
    have := W.smul_mem (1 - c ^ 2 ^ a)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hne)), one_smul] at this
  have hc1 : c = 1 := by
    have h0 : (c - 1) ^ 2 ^ a = 0 := by rw [sub_pow_char_pow, hc, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero a two_ne_zero) |>.1 h0)
  subst hc1
  have hTu : T u - u = w₀ := by rw [← hsum, one_smul, add_sub_cancel_right]
  intro v hv
  rw [← hW'eq] at hv
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have : T (w + d • u) - (w + d • u) = (T w - w) + d • (T u - u) := by
    rw [map_add, map_smul, smul_sub]
    abel
  rw [this, hTu]
  exact W.add_mem (W.sub_mem (hW w hw) hw) (W.smul_mem d hw₀)

section Flag

variable [Finite F] [CharP F 2] (σ : K ≃* SL(3, F))

theorem fixFlag_lt_succ {R : Subgroup K} (hR : IsPGroup 2 R) {k : ℕ}
    (hk : fixFlag (rep σ) R k ≠ ⊤) : fixFlag (rep σ) R k < fixFlag (rep σ) R (k + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := fixFlag (rep σ) R k with hWdef
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F, w ∉ W := by
    by_contra h
    push Not at h
    exact hk (eq_top_iff.2 fun v _ => h v)
  have hW : ∀ g ∈ R, ∀ v ∈ W, rep σ g v ∈ W := fun g hg v hv =>
    flagStab_apply_mem _ ((normalizer_le_flagStab_fixFlag _ R) (Subgroup.le_normalizer hg)) hv
  haveI hnt : Nontrivial ((Fin 3 → F) ⧸ W) := by
    refine ⟨⟨Submodule.Quotient.mk w, 0, ?_⟩⟩
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  haveI : Finite ((Fin 3 → F) ⧸ W) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective W)
  have hRp : IsPGroup 2 (⊤ : Subgroup R) := hR.of_equiv Subgroup.topEquiv.symm
  obtain ⟨x, hx0, hx⟩ := exists_fixed_ne_zero (quotRep (rep σ) R W hW) 2 ⊤ hRp
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
  refine lt_of_le_of_ne (fixFlag_le_succ _ R k) fun heq => hx0 ?_
  rw [Submodule.Quotient.mk_eq_zero, heq, mem_fixFlag_succ]
  intro g hg
  have := hx ⟨g, hg⟩ (Subgroup.mem_top _)
  rw [quotRep_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_eq_zero] at this
  exact this

theorem flagKernel_inf_normalizer_le [Finite K] {R : Subgroup K} (hR : IsPGroup 2 R)
    (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) :
    flagKernel (rep σ) (fixFlag (rep σ) R) ⊓ normalizer (R : Set K) ≤ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := exists_fixFlag_eq_top (rep σ) 2 R hR
  have hQp : IsPGroup 2 (flagKernel (rep σ) (fixFlag (rep σ) R)) :=
    isPGroup_flagKernel (rep σ) 2 (rep_injective σ) (fixFlag_zero _ R) hm
  refine le_trans ?_ hRc.le
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQp.to_le inf_le_left)
  intro g hg
  have hgS : g ∈ flagStab (rep σ) (fixFlag (rep σ) R) := normalizer_le_flagStab_fixFlag _ R hg
  have hgK := flagStab_le_normalizer_flagKernel (rep σ) (fixFlag (rep σ) R) hgS
  rw [mem_normalizer_iff] at hgK ⊢
  intro h
  rw [mem_inf, mem_inf, ← hgK h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, mul_mem (mul_mem hg h2) (inv_mem hg)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := mul_mem (mul_mem (inv_mem hg) h2) hg
    simpa [mul_assoc] using this

theorem eq_flagKernel_of_radical [Finite K] {R : Subgroup K} (hR : IsPGroup 2 R)
    (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) :
    R = flagKernel (rep σ) (fixFlag (rep σ) R) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := exists_fixFlag_eq_top (rep σ) 2 R hR
  exact eq_of_inf_normalizer_le (le_flagKernel_fixFlag _ R)
    (isPGroup_flagKernel (rep σ) 2 (rep_injective σ) (fixFlag_zero _ R) hm)
    (flagKernel_inf_normalizer_le σ hR hRc)

theorem normalizer_eq_flagStab [Finite K] {R : Subgroup K} (hR : IsPGroup 2 R)
    (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) :
    normalizer (R : Set K) = flagStab (rep σ) (fixFlag (rep σ) R) := by
  refine le_antisymm (normalizer_le_flagStab_fixFlag _ R) ?_
  have := flagStab_le_normalizer_flagKernel (rep σ) (fixFlag (rep σ) R)
  rwa [← eq_flagKernel_of_radical σ hR hRc] at this

theorem fixFlag_zero_ne_top (R : Subgroup K) : fixFlag (rep σ) R 0 ≠ ⊤ := by
  rw [fixFlag_zero]
  intro h
  have : (Pi.single 0 1 : Fin 3 → F) ∈ (⊥ : Submodule F (Fin 3 → F)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at this
  have h0 := congrFun this 0
  simp at h0

theorem false_of_complete_flag [Finite K] {R : Subgroup K} (hR : IsPGroup 2 R)
    (hRi : 2 ∣ R.index) (hRc : pCoreOf 2 (normalizer (R : Set K)) = R)
    (h2 : fixFlag (rep σ) R 2 ≠ ⊤) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Fl := fixFlag (rep σ) R with hFl
  have hl0 : Fl 0 < Fl 1 := fixFlag_lt_succ σ hR (fixFlag_zero_ne_top σ R)
  have hl1 : Fl 1 < Fl 2 :=
    fixFlag_lt_succ σ hR fun h => h2 (eq_top_iff.2 (h ▸ fixFlag_le_succ _ R 1))
  have hl2 : Fl 2 < Fl 3 := fixFlag_lt_succ σ hR h2
  have r0 : finrank F (Fl 0) = 0 := by rw [hFl, fixFlag_zero]; exact finrank_bot F _
  have r01 := Submodule.finrank_lt_finrank_of_lt hl0
  have r12 := Submodule.finrank_lt_finrank_of_lt hl1
  have r23 := Submodule.finrank_lt_finrank_of_lt hl2
  have r3 : finrank F (Fl 3) ≤ 3 := (Submodule.finrank_le _).trans (by simp)
  have h3top : Fl 3 = ⊤ := Submodule.eq_top_of_finrank_eq (by simp; omega)
  have htop : ∀ k, 3 ≤ k → Fl k = ⊤ := fun k hk =>
    eq_top_iff.2 (h3top ▸ fixFlag_mono _ R hk)
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hSN : (S : Subgroup K) ⊓ normalizer (R : Set K) ≤ R := by
    intro x ⟨hxS, hxN⟩
    refine flagKernel_inf_normalizer_le σ hR hRc ⟨?_, hxN⟩
    have hxF : x ∈ flagStab (rep σ) Fl := normalizer_le_flagStab_fixFlag _ R hxN
    obtain ⟨a, ha⟩ := S.isPGroup' ⟨x, hxS⟩
    have hxa : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hT : rep σ x ^ 2 ^ a = 1 := by rw [← map_pow, hxa, map_one]
    refine ⟨hxF, fun k v hv => ?_⟩
    rcases lt_or_ge k 3 with hk | hk
    · have hinv : ∀ j, ∀ w ∈ Fl j, rep σ x w ∈ Fl j := fun j w hw => flagStab_apply_mem _ hxF hw
      interval_cases k
      · exact sub_mem_of_pow_two_eq_one _ hT (hinv 0) (hinv 1) hl0 (by omega) v hv
      · exact sub_mem_of_pow_two_eq_one _ hT (hinv 1) (hinv 2) hl1 (by omega) v hv
      · exact sub_mem_of_pow_two_eq_one _ hT (hinv 2) (hinv 3) hl2 (by omega) v hv
    · have hk' : fixFlag (rep σ) R k = ⊤ := htop k hk
      rw [hk']
      exact Submodule.mem_top
  have hRSeq : R = S := eq_of_inf_normalizer_le hRS S.isPGroup' hSN
  exact S.not_dvd_index (hRSeq ▸ hRi)

theorem exists_stab [Finite K] {R : Subgroup K} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hRi : 2 ∣ R.index) (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) :
    ∃ C : Submodule F (Fin 3 → F), (finrank F C = 1 ∨ finrank F C = 2) ∧
      ∀ x, x ∈ normalizer (R : Set K) ↔ ∀ v ∈ C, rep σ x v ∈ C ∧ rep σ x⁻¹ v ∈ C := by
  set Fl := fixFlag (rep σ) R with hFl
  by_cases h2 : Fl 2 = ⊤
  swap
  · exact (false_of_complete_flag σ hR hRi hRc h2).elim
  have htop : ∀ k, 2 ≤ k → Fl k = ⊤ := fun k hk => eq_top_iff.2 (h2 ▸ fixFlag_mono _ R hk)
  have hl0 : Fl 0 < Fl 1 := fixFlag_lt_succ σ hR (fixFlag_zero_ne_top σ R)
  have h1top : Fl 1 ≠ ⊤ := by
    intro h
    apply hR1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    apply rep_injective σ
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Fl 1 := h ▸ Submodule.mem_top
    have := hv g hg
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have r01 := Submodule.finrank_lt_finrank_of_lt hl0
  have r0 : finrank F (Fl 0) = 0 := by rw [hFl, fixFlag_zero]; exact finrank_bot F _
  have r1 : finrank F (Fl 1) < 3 := by
    have := Submodule.finrank_lt h1top
    simpa using this
  refine ⟨Fl 1, by omega, fun x => ?_⟩
  rw [normalizer_eq_flagStab σ hR hRc, mem_flagStab]
  constructor
  · intro h v hv
    exact h 1 v hv
  · intro h k v hv
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · rw [fixFlag_zero, Submodule.mem_bot] at hv
        subst hv
        simp
      · exact h v hv
    · have hk' : fixFlag (rep σ) R k = ⊤ := htop k hk
      rw [hk']
      exact ⟨Submodule.mem_top, Submodule.mem_top⟩

end Flag

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136
