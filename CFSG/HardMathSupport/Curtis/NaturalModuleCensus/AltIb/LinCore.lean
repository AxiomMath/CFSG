module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinBlocks
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.G2
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Blocks

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.CALinearPlane CFSG.QuasithinUnique
  CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

section Orders

variable [Finite K]

theorem card_GL_eq_mul_card_SL (m : ℕ) [NeZero m] :
    Nat.card (GL (Fin m) K) =
      (Nat.card K - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin m) K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Matrix.card_GL_field, ← Nat.card_eq_fintype_card]
  have hdvd : Nat.card K - 1 ∣ ∏ i : Fin m, (Nat.card K ^ m - Nat.card K ^ (i : ℕ)) := by
    have h0 : (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) :=
      Finset.mem_univ _
    refine (?_ : Nat.card K - 1 ∣ Nat.card K ^ m - Nat.card K ^ ((⟨0, _⟩ : Fin m) : ℕ)).trans
      (Finset.dvd_prod_of_mem (fun i : Fin m => Nat.card K ^ m - Nat.card K ^ (i : ℕ)) h0)
    have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 m
    simpa using this
  rw [Nat.mul_div_cancel' hdvd]

theorem sub_one_dvd_pow_sub_pow_self {q : ℕ} (hq : 0 < q) (i k : ℕ) (hi : i ≤ k) :
    q - 1 ∣ q ^ k - q ^ i := by
  have h1 := Nat.sub_dvd_pow_sub_pow q 1 k
  have h2 := Nat.sub_dvd_pow_sub_pow q 1 i
  simp only [one_pow] at h1 h2
  have h3 := Nat.dvd_sub h1 h2
  have hle : q ^ i ≤ q ^ k := Nat.pow_le_pow_right hq hi
  have hpos : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have : q ^ k - 1 - (q ^ i - 1) = q ^ k - q ^ i := by omega
  rwa [this] at h3

theorem pow_dvd_card_SL (k : ℕ) (hk : 1 ≤ k) :
    (Nat.card K - 1) ^ (k - 1) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : NeZero k := ⟨by omega⟩
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have h := Matrix.card_SL_field (𝔽 := K) k
  rw [← Nat.card_eq_fintype_card] at h
  rw [h]
  have hdvd : (Nat.card K - 1) ^ k ∣ ∏ i : Fin k, (Nat.card K ^ k - Nat.card K ^ (i : ℕ)) := by
    have := Finset.prod_dvd_prod_of_dvd (s := (Finset.univ : Finset (Fin k)))
      (fun _ => Nat.card K - 1) (fun i : Fin k => Nat.card K ^ k - Nat.card K ^ (i : ℕ))
      (fun i _ => sub_one_dvd_pow_sub_pow_self (by omega) _ _ (by omega))
    simpa [Finset.prod_const] using this
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  have hk' : k = (k - 1) + 1 := by omega
  have hpos : 0 < Nat.card K - 1 := by omega
  rw [hk', pow_succ, mul_assoc]
  rw [show (Nat.card K - 1) ^ (k - 1) * ((Nat.card K - 1) * c) =
      (Nat.card K - 1) * ((Nat.card K - 1) ^ (k - 1) * c) by ring, Nat.mul_div_cancel_left _ hpos]
  simp only [Nat.add_sub_cancel]
  exact Dvd.intro _ rfl

theorem card_SL2_eq : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
    Nat.card K * (Nat.card K ^ 2 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  have h := Matrix.card_SL_field (𝔽 := K) 2
  rw [← Nat.card_eq_fintype_card] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h]
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [ha]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have h1 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    have : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    omega
  have h2 : (a + 1) ^ 2 - (a + 1) = (a + 1) * a := by
    have : (a + 1) ^ 2 = (a + 1) * a + (a + 1) := by ring
    omega
  rw [h1, h2]
  have : a + 1 - 1 = a := by omega
  rw [this]
  ring

theorem noAp_sl2 [CharP K 2] {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1) :
    NoAp p (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hz : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 := by
      rw [CFSG.AGLEmbedding.ParabPrime.sl2_center_eq_bot (k := K), Subgroup.card_bot]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    rw [hz, mul_one, card_SL2_eq] at h
    exact h.symm
  have hf' : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card (K := K) 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
  obtain ⟨f, hf⟩ := hf'
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  rw [hf] at hq2 hpq
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0] at hq2; norm_num at hq2
    · exact h0
  rcases Nat.lt_or_ge f 4 with hf4 | hf4
  · interval_cases f
    · rcases hp57 with rfl | rfl <;> norm_num at hpq
    · rcases hp57 with rfl | rfl <;> norm_num at hpq
    · rcases hp57 with rfl | rfl
      · norm_num at hpq
      · exact noAp_seven_of_card_eq (by rw [hcard, hf]; norm_num)
  · have h16 : 16 ≤ 2 ^ f := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    refine NoAp.of_card_lt ?_
    rw [hcard, hf]
    have hbig : 4080 ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      have h1 : 16 * (16 ^ 2 - 1) ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
        Nat.mul_le_mul h16 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 2) 1)
      simpa using h1
    rcases hp57 with rfl | rfl
    · rw [nat_card_alt_five]; omega
    · rw [nat_card_alt_seven]; omega

end Orders

section Cyclic

@[expose] noncomputable def reindexGL {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ ≃ κ') : GL κ K ≃* GL κ' K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv

omit [Field K] in
theorem gl_comm_of_card_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] [Field K]
    (hk : Fintype.card κ = 1) (a b : GL κ K) : a * b = b * a := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hk
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  exact mul_comm _ _

theorem le_ker_det_of_perfect {κ : Type} [Fintype κ] [DecidableEq κ] {P : Subgroup (GL κ K)}
    (hP : ⁅P, P⁆ = P) : P ≤ (Matrix.GeneralLinearGroup.det (n := κ) (R := K)).ker := by
  rw [← hP, Subgroup.commutator_le]
  intro g _ h _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
  simp

theorem isCyclic_of_perfect_gl [Finite K] [CharP K 2] {κ : Type} [Fintype κ] [DecidableEq κ]
    (hk : Fintype.card κ ≤ 2) (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (GL κ K)} (hP : ⁅P, P⁆ = P) {Q : Subgroup (GL κ K)} (hQP : Q ≤ P)
    (hQ : IsPGroup p Q) : IsCyclic Q := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.lt_or_ge (Fintype.card κ) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Fintype.card κ) 1 with h0 | h1
    · have h0' : Fintype.card κ = 0 := by omega
      have : IsEmpty κ := Fintype.card_eq_zero_iff.1 h0'
      have : Subsingleton (GL κ K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      have : Subsingleton Q := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      infer_instance
    · have h1' : Fintype.card κ = 1 := by omega
      have hPbot : P = ⊥ := by
        rw [← hP, eq_bot_iff, Subgroup.commutator_le]
        intro g _ h _
        rw [Subgroup.mem_bot, commutatorElement_def]
        simp [gl_comm_of_card_eq_one h1' g h]
      have : Q = ⊥ := eq_bot_iff.2 (hPbot ▸ hQP)
      rw [this]
      infer_instance
  · have h2 : Fintype.card κ = 2 := by omega
    set e : Fin 2 ≃ κ := (Fintype.equivFinOfCardEq h2).symm with he
    let ψ : Matrix.SpecialLinearGroup (Fin 2) K →* GL κ K :=
      (reindexGL e).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
    have hker : P ≤ ψ.range := by
      intro g hg
      have hdet : (g : Matrix κ κ K).det = 1 := by
        have := le_ker_det_of_perfect hP hg
        rw [MonoidHom.mem_ker] at this
        have h' := congrArg Units.val this
        simpa [Matrix.GeneralLinearGroup.det] using h'
      refine ⟨⟨(g : Matrix κ κ K).submatrix e e, ?_⟩, ?_⟩
      · rw [← hdet]
        exact Matrix.det_submatrix_equiv_self e _
      · apply Units.ext
        ext i j
        show ((g : Matrix κ κ K).submatrix e e) (e.symm i) (e.symm j) = (g : Matrix κ κ K) i j
        simp
    exact AltIb.isCyclic_of_le_range ψ (sylow_isCyclic_sl2 hK hp hp2) (hQP.trans hker) hQ

omit [Field K] in
theorem perfect_eq_bot_of_card_le_one [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (hk : Fintype.card κ ≤ 1) {P : Subgroup (GL κ K)} (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  rcases Nat.lt_or_ge (Fintype.card κ) 1 with h0 | h1
  · have h0' : Fintype.card κ = 0 := by omega
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 h0'
    have : Subsingleton (GL κ K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  · have h1' : Fintype.card κ = 1 := by omega
    rw [← hP, eq_bot_iff, Subgroup.commutator_le]
    intro g _ h _
    rw [Subgroup.mem_bot, commutatorElement_def]
    simp [gl_comm_of_card_eq_one h1' g h]

end Cyclic

section Levi

variable [Finite K]

theorem levi_data_sl2 [CharP K 2] {G : Type} [Group G] {J : Subgroup G} {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K - 1)
    {k : ℕ} (hk : k = 2) (φ : Matrix.SpecialLinearGroup (Fin k) K →* G)
    (hφ : Function.Injective φ) (hφJ : ∀ A, φ A ∈ J) :
    φ.range ≤ J ∧ CFSG.Open.IsQuasisimple ↥φ.range ∧ p ∣ Nat.card φ.range ∧
      NoAp p (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  subst hk
  have hK4 : 4 ≤ Nat.card K := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have e := (MonoidHom.ofInjective hφ)
  refine ⟨by rintro _ ⟨A, rfl⟩; exact hφJ A, ?_, ?_, ?_⟩
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
      (isQuasisimple_SL2_of_four_le hK4)
  · rw [← Nat.card_congr e.toEquiv, card_SL2_eq]
    refine Dvd.dvd.mul_left ?_ _
    have hq1 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
      simpa using this
    exact hpq.trans hq1
  · exact noAp_center_quotient_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)
      (noAp_sl2 hp57 hpq)

end Levi

@[expose] noncomputable def linFlagBlocks [CharP K 2] (I : Set ℕ) {p : ℕ} (hp : (p : K) ≠ 0) :
    FlagBlocks p ↥(flagStabilizer n K I) where
  ι := {ab : ℕ × ℕ // IsConsecutiveCut n I ab.1 ab.2}
  H := fun i => GL (Fin (i.1.2 - i.1.1)) K
  ρ := fun i => blockHomGL i.2
  inj_of_pow := fun e he hall =>
    Subtype.ext (eq_one_of_blocks_trivial_pow e.2 hp (by
      have := congrArg Subtype.val he
      simpa using this) fun a b h => (blockHomGL_eq_one_iff h e).1 (hall ⟨(a, b), h⟩))

instance [CharP K 2] [Finite K] (I : Set ℕ) {p : ℕ} (hp : (p : K) ≠ 0) (i : (linFlagBlocks (n := n) I hp).ι) :
    Finite ((linFlagBlocks (n := n) I hp).H i) :=
  inferInstanceAs (Finite (GL (Fin (i.1.2 - i.1.1)) K))

section TF

variable [Finite K] [CharP K 2]

theorem not_sq_dvd_card_GL_block {I : Set ℕ} {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hpq : ¬ p ∣ Nat.card K - 1) (hA1 : CoverA1 n K I p) {a b : ℕ}
    (h : IsConsecutiveCut n I a b) (hlt : b - a < n) : ¬ p ^ 2 ∣ Nat.card (GL (Fin (b - a)) K) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have : NeZero (b - a) := ⟨by have := h.1; omega⟩
  rw [card_GL_eq_mul_card_SL]
  intro hd
  have hcop : Nat.Coprime (p ^ 2) (Nat.card K - 1) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
  exact a1_blocks hp57 hA1 h hlt (hcop.dvd_of_dvd_mul_left hd)

theorem coreTF {I : Set ℕ} (hne : I.Nonempty) (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hpq : ¬ p ∣ Nat.card K - 1) (hA1 : CoverA1 n K I p)
    {x : SpecialLinearGroup (Fin n) K} (hxp : x ^ p = 1)
    (hfix : Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    {V E : Subgroup (SpecialLinearGroup (Fin n) K)} (hVQ : V ≤ flagStabilizer n K I)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)))
    (hV : ⁅V, V⁆ = V) (hEV : E ≤ V) (hE : ∀ e ∈ E, e ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E) :
    False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hpodd : Odd p := hp.odd_of_ne_two (by rcases hp57 with rfl | rfl <;> norm_num)
  have hp0 : (p : K) ≠ 0 := natCast_ne_zero_of_odd_charTwo hpodd
  set Q := flagStabilizer n K I with hQ
  have hxQ : x ∈ Q := hfix (Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    rw [hh])
  let B : FlagBlocks p ↥Q := linFlagBlocks I hp0
  have hH : ∀ i, ¬ p ^ 2 ∣ Nat.card (B.H i) := fun i =>
    not_sq_dvd_card_GL_block hp57 hpq hA1 i.2 (sub_lt_of_isConsecutiveCut hI hne i.2)
  have hV' : ⁅V.subgroupOf Q, V.subgroupOf Q⁆ = V.subgroupOf Q := commutator_subgroupOf_eq hVQ hV
  have hEV' : E.subgroupOf Q ≤ V.subgroupOf Q := fun e he =>
    Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  have hE' : ∀ e ∈ E.subgroupOf Q, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hE _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf Q) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVQ)).toEquiv]
    exact hEc
  have hcyc : ∀ i, IsCyclic ↥((E.subgroupOf Q).map (B.ρ i)) := fun i =>
    isCyclic_of_isPGroup_of_not_sq_dvd hp (hH i) (isPGroup_of_pow_eq_one (by
      rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hE' e he, map_one]))
  obtain ⟨i, j, hij, hi, hj⟩ := B.exists_two_ne_bot_map hp hE' hEc' hcyc
  have hxV' : ∀ v ∈ V.subgroupOf Q, v * (⟨x, hxQ⟩ : ↥Q) = ⟨x, hxQ⟩ * v := by
    intro v hv
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hVx (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x)
    exact this.symm
  have hxp' : (⟨x, hxQ⟩ : ↥Q) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hx1 : ∀ i, (E.subgroupOf Q).map (B.ρ i) ≠ ⊥ → B.ρ i ⟨x, hxQ⟩ = 1 := by
    intro i hi
    by_contra hne'
    exact hi (map_eq_bot_of_transfer (B.ρ i) hp (hH i) hV' hEV' hE' hxp' hxV'
      (fun h _ => hne' h))
  have hbi := (blockHomGL_eq_one_iff i.2 ⟨x, hxQ⟩).1 (hx1 i hi)
  have hbj := (blockHomGL_eq_one_iff j.2 ⟨x, hxQ⟩).1 (hx1 j hj)
  have hne2 : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  rcases cut_disjoint i.2 j.2 hne2 with hd | hd
  · exact false_of_trivialBlocks hpodd hxQ hxp hfix i.2 j.2 hd hbi hbj
  · exact false_of_trivialBlocks hpodd hxQ hxp hfix j.2 i.2 hd hbj hbi

end TF

section Split

variable [Finite K] [CharP K 2]

theorem block_size_le_two {I : Set ℕ} {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1)
    (hA1 : CoverA1 n K I p) {a b : ℕ} (h : IsConsecutiveCut n I a b) (hlt : b - a < n) :
    b - a ≤ 2 := by
  by_contra hk
  push Not at hk
  refine a1_blocks hp57 hA1 h hlt ?_
  have := pow_dvd_card_SL (K := K) (b - a) (by omega)
  exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans this

theorem levi_block {I : Set ℕ} {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1)
    (hK4 : 4 ≤ Nat.card K) {a b : ℕ} (h : IsConsecutiveCut n I a b) (hk : b - a = 2)
    (hlt : b - a < n) :
    (blockSLOn K (intervalCoords n a b h.2.1)).range ≤ flagStabilizer n K I ∧
      (blockSLOn K (intervalCoords n a b h.2.1)).range ⊓
        Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ ∧
      CFSG.Open.IsQuasisimple ↥(blockSLOn K (intervalCoords n a b h.2.1)).range ∧
      p ∣ Nat.card (blockSLOn K (intervalCoords n a b h.2.1)).range ∧
      NoAp p (↥(blockSLOn K (intervalCoords n a b h.2.1)).range ⧸
        Subgroup.center ↥(blockSLOn K (intervalCoords n a b h.2.1)).range) := by
  have hJ : (intervalCoords n a b h.2.1).card = 2 := by rw [card_intervalCoords]; exact hk
  obtain ⟨hle, hq, hpd, hn⟩ := levi_data_sl2 (J := flagStabilizer n K I) hp57 (Or.inr hK4) hpq hJ
    (blockSLOn K (intervalCoords n a b h.2.1)) (blockSLOn_injective _) (fun A => by
      have : blockSLOn K (intervalCoords n a b h.2.1) A ∈
          (blockSLOn K (intervalCoords n a b h.2.1)).range := ⟨A, rfl⟩
      rw [range_blockSLOn] at this
      exact coordBlockSL_le_flagStabilizer h this)
  refine ⟨hle, ?_, hq, hpd, hn⟩
  rw [range_blockSLOn]
  exact coordBlockSL_inf_center (by omega)

theorem two_blocks_eq {I : Set ℕ} (hne : I.Nonempty) (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1) (hK4 : 4 ≤ Nat.card K)
    (hA2 : CoverA2 n K I p) {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b)
    (h' : IsConsecutiveCut n I a' b') (hk : b - a = 2) (hk' : b' - a' = 2) :
    (a, b) = (a', b') := by
  by_contra hne2
  obtain ⟨hl₁, hz₁, hq₁, hp₁, hn₁⟩ := levi_block hp57 hpq hK4 h hk
    (sub_lt_of_isConsecutiveCut hI hne h)
  obtain ⟨hl₂, hz₂, hq₂, hp₂, hn₂⟩ := levi_block hp57 hpq hK4 h' hk'
    (sub_lt_of_isConsecutiveCut hI hne h')
  have hdisj : Disjoint (intervalCoords n a b h.2.1) (intervalCoords n a' b' h'.2.1) ∨
      Disjoint (intervalCoords n a' b' h'.2.1) (intervalCoords n a b h.2.1) := by
    rcases cut_disjoint h h' hne2 with hd | hd
    · left
      exact Finset.disjoint_left.2 fun i hi1 hi2 => by
        rw [mem_intervalCoords] at hi1 hi2
        omega
    · right
      exact Finset.disjoint_left.2 fun i hi1 hi2 => by
        rw [mem_intervalCoords] at hi1 hi2
        omega
  refine hA2 _ _ hl₁ hl₂ hz₁ hz₂ hq₁ hq₂ ?_ hp₁ hp₂ hn₁ hn₂
  rintro _ ⟨B', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨A, rfl⟩
  rcases hdisj with hd | hd
  · exact blockSLOn_mul_comm_of_disjoint hd A B'
  · exact (blockSLOn_mul_comm_of_disjoint hd B' A).symm

theorem coreSplit {I : Set ℕ} (hne : I.Nonempty) (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1) (hA1 : CoverA1 n K I p)
    (hA2 : CoverA2 n K I p) {V P : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hVQ : V ≤ flagStabilizer n K I) (hV : ⁅V, V⁆ = V) (hPV : P ≤ V) (hP : IsPGroup p P) :
    IsCyclic P := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hK4 : 4 ≤ Nat.card K := by
    rcases card_eq_two_or_four_le (K := K) with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  set Q := flagStabilizer n K I with hQ
  have hPQ : P ≤ Q := hPV.trans hVQ
  have hV' : ⁅V.subgroupOf Q, V.subgroupOf Q⁆ = V.subgroupOf Q := commutator_subgroupOf_eq hVQ hV
  have hPV' : P.subgroupOf Q ≤ V.subgroupOf Q := fun g hg =>
    Subgroup.mem_subgroupOf.2 (hPV (Subgroup.mem_subgroupOf.1 hg))
  have hP' : IsPGroup p (P.subgroupOf Q) := hP.comap_subtype
  have hsz : ∀ a b (h : IsConsecutiveCut n I a b), b - a ≤ 2 := fun a b h =>
    block_size_le_two hp57 hpq hA1 h (sub_lt_of_isConsecutiveCut hI hne h)
  have hperf : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : ↥Q →* GL κ K),
      ⁅(V.subgroupOf Q).map ρ, (V.subgroupOf Q).map ρ⁆ = (V.subgroupOf Q).map ρ := by
    intro κ _ _ ρ
    rw [← Subgroup.map_commutator, hV']
  have key : ∀ g ∈ P.subgroupOf Q,
      (∀ a b (h : IsConsecutiveCut n I a b), b - a = 2 → blockHomGL h g = 1) → g = 1 := by
    intro g hg hall
    obtain ⟨k, hk⟩ := hP' ⟨g, hg⟩
    have hgk : g ^ p ^ k = 1 := congrArg Subtype.val hk
    have hm : ((p ^ k : ℕ) : K) ≠ 0 := natCast_ne_zero_of_odd_charTwo (hpodd.pow)
    refine Subtype.ext (eq_one_of_blocks_trivial_pow g.2 hm (by
      have := congrArg Subtype.val hgk
      simpa using this) fun a b h => ?_)
    by_cases hk2 : b - a = 2
    · exact (blockHomGL_eq_one_iff h g).1 (hall a b h hk2)
    · have hle : Fintype.card (Fin (b - a)) ≤ 1 := by
        have := hsz a b h
        simp only [Fintype.card_fin]
        omega
      have hbot := perfect_eq_bot_of_card_le_one (K := K) hle (hperf (blockHomGL h))
      have hmem : blockHomGL h g ∈ (V.subgroupOf Q).map (blockHomGL h) :=
        Subgroup.mem_map_of_mem _ (hPV' hg)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (blockHomGL_eq_one_iff h g).1 hmem
  have hcycP' : IsCyclic ↥(P.subgroupOf Q) := by
    by_cases h2 : ∃ a b, ∃ h : IsConsecutiveCut n I a b, b - a = 2
    · obtain ⟨a₀, b₀, h₀, hk₀⟩ := h2
      have hinj : ∀ g ∈ P.subgroupOf Q, blockHomGL h₀ g = 1 → g = 1 := by
        intro g hg hρ
        refine key g hg fun a b h hk => ?_
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (two_blocks_eq hne hI hp57 hpq hK4 hA2 h h₀ hk hk₀)
        exact hρ
      have hcycim : IsCyclic ↥((P.subgroupOf Q).map (blockHomGL h₀)) :=
        isCyclic_of_perfect_gl (κ := Fin (b₀ - a₀)) (by simp [hk₀]) hK4 hp hp2
          (hperf (blockHomGL h₀)) (Subgroup.map_mono hPV') (hP'.map _)
      have hbij : Function.Bijective ((blockHomGL h₀).subgroupMap (P.subgroupOf Q)) := by
        refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_,
          MonoidHom.subgroupMap_surjective _ _⟩
        exact Subtype.ext (hinj x.1 x.2 (congrArg Subtype.val hx))
      exact isCyclic_of_surjective (MulEquiv.ofBijective _ hbij).symm.toMonoidHom
        (MulEquiv.surjective _)
    · push Not at h2
      have hbot : P.subgroupOf Q = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun g hg =>
        key g hg fun a b h hk => absurd hk (h2 a b h)
      rw [hbot]
      infer_instance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPQ).toMonoidHom
    (MulEquiv.surjective _)

end Split

section Cover

variable {G : Type} [Group G]

theorem exists_mulEquiv_map (σ : SpecialLinearGroup (Fin n) K →* G)
    {X : Subgroup (SpecialLinearGroup (Fin n) K)} (h : X ⊓ σ.ker = ⊥) :
    ∃ e : ↥X ≃* ↥(X.map σ), ∀ x : ↥X, ((e x : ↥(X.map σ)) : G) = σ x := by
  have hbij : Function.Bijective (σ.subgroupMap X) := by
    refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_, MonoidHom.subgroupMap_surjective _ _⟩
    have h1 : σ (x : SpecialLinearGroup (Fin n) K) = 1 := congrArg Subtype.val hx
    have : (x : SpecialLinearGroup (Fin n) K) ∈ X ⊓ σ.ker := ⟨x.2, h1⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  exact ⟨MulEquiv.ofBijective _ hbij, fun _ => rfl⟩

theorem coverA1_of_hom {I : Set ℕ} {p : ℕ} {J : Subgroup G}
    (σ : SpecialLinearGroup (Fin n) K →* G)
    (hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hQ : flagStabilizer n K I ≤ J.comap σ)
    (hA1 : ∀ X : Subgroup G, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) :
    CoverA1 n K I p := by
  intro X hXQ hXZ hXq hd
  obtain ⟨e, -⟩ := exists_mulEquiv_map σ (X := X)
    (eq_bot_iff.2 (fun x hx => by
      have := (inf_le_inf_left X hker) hx
      rw [hXZ] at this
      exact this))
  refine hA1 (X.map σ) (Subgroup.map_le_iff_le_comap.2 fun x hx => hQ (hXQ hx))
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hXq) ?_
  rwa [← Nat.card_congr e.toEquiv]

theorem coverA2_of_hom {I : Set ℕ} {p : ℕ} {J : Subgroup G}
    (σ : SpecialLinearGroup (Fin n) K →* G)
    (hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hQ : flagStabilizer n K I ≤ J.comap σ)
    (hA2 : ∀ X₁ X₂ : Subgroup G, X₁ ≤ J → X₂ ≤ J → CFSG.Open.IsQuasisimple ↥X₁ →
      CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set G) →
      p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) :
    CoverA2 n K I p := by
  intro X₁ X₂ h₁ h₂ hz₁ hz₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂
  have hker' : ∀ {X : Subgroup (SpecialLinearGroup (Fin n) K)},
      X ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → X ⊓ σ.ker = ⊥ := fun {X} hXZ =>
    eq_bot_iff.2 (fun x hx => by
      have := (inf_le_inf_left X hker) hx
      rw [hXZ] at this
      exact this)
  obtain ⟨e₁, -⟩ := exists_mulEquiv_map σ (hker' hz₁)
  obtain ⟨e₂, -⟩ := exists_mulEquiv_map σ (hker' hz₂)
  refine hA2 (X₁.map σ) (X₂.map σ) (Subgroup.map_le_iff_le_comap.2 fun x hx => hQ (h₁ hx))
    (Subgroup.map_le_iff_le_comap.2 fun x hx => hQ (h₂ hx))
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e₁.symm hq₁)
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e₂.symm hq₂) ?_
    (by rwa [← Nat.card_congr e₁.toEquiv]) (by rwa [← Nat.card_congr e₂.toEquiv])
    (noAp_center_quotient_of_surjective e₁.symm.toMonoidHom (MulEquiv.surjective _) hn₁)
    (noAp_center_quotient_of_surjective e₂.symm.toMonoidHom (MulEquiv.surjective _) hn₂)
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hc hy) z hz]

end Cover

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell
