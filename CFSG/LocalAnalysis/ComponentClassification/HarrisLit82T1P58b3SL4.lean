module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Sp4Key
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57N
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LSL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.Foote5.OddLieCore (blockTwo blockTwo_injective range_blockTwo
  blockPt blockPt_mem blockPt_injective eq_blockPt_of_mem blockTwo_apply_pt blockTwo_apply_not_mem
  blockTwo_mul_apply_pt blockTwo_mul_apply_not_mem)
open scoped MatrixGroups

namespace P58b3

theorem oddAutInner_of_card_outer_dvd {X : Type} [Group X] (hX : Group.IsPerfect X) {m : ℕ}
    (h : Nat.card (Outer (X ⧸ center X)) ∣ 2 ^ m) : OddAutInner X := by
  intro α k hk hα
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  have hidx : (inner (X ⧸ center X)).index = 2 ^ j := hj
  set Φ := PerfectAutomorphisms.centerQuotientHom X with hΦdef
  have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (QuotientGroup.mk' (center X) x) :=
    fun x => by
      change PerfectAutomorphisms.onCenterQuotient (MulAut.conj x) = _
      exact onCenterQuotient_conj x
  have hΦ : Function.Injective Φ := PerfectAutomorphisms.centerQuotientHom_injective X
  have hI : (inner (X ⧸ center X)).comap Φ = (MulAut.conj : X →* MulAut X).range := by
    ext β
    rw [mem_comap]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) y
      exact ⟨x, hΦ ((hΦconj x).trans hy)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hΦconj x).symm⟩
  rw [← hI] at hα ⊢
  rw [mem_comap, map_pow] at hα
  exact mem_of_pow_mem_of_index_eq_two_pow hidx hk hα

theorem oddAutInner_of_PSL_four {X : Type} [Group X] (hX : IsQuasisimple X)
    (hm : Blueprint.LieModel (X ⧸ center X) .PSL 4 3 1) : OddAutInner X := by
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have h := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound _ 4 3 1
    hcl).2.2.2.2 (by norm_num)
  norm_num at h
  exact oddAutInner_of_card_outer_dvd hX.1 (m := 2) (by simpa using h)

variable {F : Type} [Field F]

theorem blockTwo_neg_one {n : ℕ} (J : Finset (Fin n)) (hJ : J.card = 2) :
    ((blockTwo J hJ (-1 : SL(2, F)) : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      diagonal (fun x => if x ∈ J then (-1 : F) else 1) := by
  ext i j
  by_cases hij : i ∈ J ∧ j ∈ J
  · obtain ⟨hi, hj⟩ := hij
    rcases eq_blockPt_of_mem J hJ hi with rfl | rfl <;>
    rcases eq_blockPt_of_mem J hJ hj with rfl | rfl <;>
    simp [blockTwo_apply_pt, (blockPt_injective J hJ).eq_iff, blockPt_mem]
  · have hor : i ∉ J ∨ j ∉ J := by
      by_contra h
      push Not at h
      exact hij h
    rw [blockTwo_apply_not_mem J hJ _ hor, diagonal_apply]
    by_cases h : i = j
    · subst h
      have hi : i ∉ J := hor.elim id id
      simp [hi]
    · simp [h]

theorem isSupp_blockTwo {n : ℕ} (J : Finset (Fin n)) (hJ : J.card = 2) (X : SL(2, F)) :
    LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp (J : Set (Fin n))
      ((blockTwo J hJ X : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
  intro x y hxy
  rw [blockTwo_apply_not_mem J hJ X (by simpa only [Finset.mem_coe] using hxy), one_apply]

theorem exists_blockTwo_mul_of_pow_three [Finite F] (hF : Nat.card F = 3) {σ : Fin 4 → Bool}
    (hJ₁ : (coordSet σ true).card = 2) (hJ₂ : (coordSet σ false).card = 2) {y : SL(4, F)}
    (hy : slConjugation 4 F (signGL F σ) y = y) (hy3 : y ^ 3 = 1) :
    ∃ A B : SL(2, F),
      y = blockTwo (coordSet σ true) hJ₁ A * blockTwo (coordSet σ false) hJ₂ B := by
  have h2 : (2 : F) ≠ 0 := Foote5.OddLieCore.two_ne_zero_of_card hF
  obtain ⟨p, hpdef⟩ : ∃ p : Fin 2 → Fin 4, p = blockPt (coordSet σ true) hJ₁ := ⟨_, rfl⟩
  have hp : p 0 ≠ p 1 := fun h => absurd (blockPt_injective _ hJ₁
    (show blockPt (coordSet σ true) hJ₁ 0 = blockPt (coordSet σ true) hJ₁ 1 by
      rw [← hpdef]; exact h)) (by decide)
  have hpinj : ∀ α β, p α = p β ↔ α = β := fun α β => by
    rw [hpdef]
    exact (blockPt_injective _ hJ₁).eq_iff
  have hpt : ∀ α, σ (p α) = true := fun α => by
    rw [hpdef]
    exact mem_coordSet.mp (blockPt_mem _ hJ₁ α)
  have hpJ : ∀ i, σ i = true → i = p 0 ∨ i = p 1 := fun i hi => by
    rw [hpdef]
    exact eq_blockPt_of_mem _ hJ₁ (mem_coordSet.mpr hi)
  have hcross : ∀ i j, σ i ≠ σ j → (y : Matrix (Fin 4) (Fin 4) F) i j = 0 := fun i j hij =>
    entry_eq_zero_of_fixed_signGL h2 hy hij
  have hpair : ∀ i, i ∈ ({p 0, p 1} : Finset (Fin 4)) ↔ σ i = true := by
    intro i
    rw [Burgoyne.Proj.mem_pair]
    constructor
    · rintro (rfl | rfl)
      · exact hpt 0
      · exact hpt 1
    · exact hpJ i
  have hBD : Burgoyne.Proj.BlockDiag {p 0, p 1} (y : Matrix (Fin 4) (Fin 4) F) := by
    rw [Burgoyne.Proj.blockDiag_iff]
    intro i j hij
    apply hcross
    rw [hpair, hpair] at hij
    cases hi : σ i <;> cases hj : σ j <;> simp_all
  have hM3 : (y : Matrix (Fin 4) (Fin 4) F) * y * y = 1 := by
    have h := congrArg (fun z : SL(4, F) => (z : Matrix (Fin 4) (Fin 4) F)) hy3
    simpa only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one] using h
  have hA3 : Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F) *
      Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F) *
      Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Burgoyne.Proj.pairBlock_mul hp hBD,
      ← Burgoyne.Proj.pairBlock_mul hp (Burgoyne.Proj.blockDiag_mul hBD hBD), hM3]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Burgoyne.Proj.pairBlock, one_apply, hp, Ne.symm hp]
  have hdet : (Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F)).det = 1 := by
    have h3 := congrArg Matrix.det hA3
    rw [det_mul, det_mul, det_one] at h3
    rcases Foote5.OddLieCore.eq_zero_or_one_or_neg_one hF
      (Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F)).det with h | h | h
    · rw [h] at h3
      simp at h3
    · exact h
    · rw [h] at h3
      exfalso
      apply h2
      linear_combination -h3
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) =
      Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F) := ⟨⟨_, hdet⟩, rfl⟩
  have hz : (blockTwo (coordSet σ true) hJ₁ A)⁻¹ * y ∈ coordBlockSL F (coordSet σ false) := by
    rw [mem_coordBlockSL_iff]
    intro i j hij
    rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul]
    by_cases hi : σ i = true
    · obtain ⟨α, rfl⟩ : ∃ α, i = p α := (hpJ i hi).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
      rw [hpdef, blockTwo_mul_apply_pt hJ₁, ← hpdef]
      by_cases hj : σ j = true
      · obtain ⟨β, rfl⟩ : ∃ β, j = p β := (hpJ j hj).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
        have hAA : ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * A = 1 := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one]
        have e := congrFun (congrFun hAA α) β
        rw [Matrix.mul_apply, Fin.sum_univ_two, hA] at e
        have hcol : ∀ γ : Fin 2, (y : Matrix (Fin 4) (Fin 4) F) (p γ) (p β) =
            Burgoyne.Proj.pairBlock (p 0) (p 1) (y : Matrix (Fin 4) (Fin 4) F) γ β := by
          intro γ
          fin_cases γ <;> fin_cases β <;> rfl
        rw [hcol 0, hcol 1, e, one_apply]
        simp only [hpinj]
      · have hσj : σ j = false := by simpa using hj
        rw [hcross (p 0) j (by rw [hpt, hσj]; decide),
          hcross (p 1) j (by rw [hpt, hσj]; decide)]
        have hne : p α ≠ j := fun h => hj (h ▸ hpt α)
        simp [hne]
    · have hσi : σ i = false := by simpa using hi
      have hj : σ j = true := by
        rcases hij with h | h
        · exact absurd (mem_coordSet.mpr hσi) h
        · simpa [mem_coordSet] using h
      have hiJ : i ∉ coordSet σ true := fun h => hi (mem_coordSet.mp h)
      rw [blockTwo_mul_apply_not_mem hJ₁ _ _ hiJ, hcross i j (by rw [hσi, hj]; decide)]
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      simp [hne]
  rw [← range_blockTwo _ hJ₂] at hz
  obtain ⟨B, hB⟩ := hz
  exact ⟨A, B, by rw [hB, mul_inv_cancel_left]⟩

theorem false_of_sl4 [Finite F] (hF : Nat.card F = 3) {X : Type} [Group X] [Finite X]
    (Ψ : SL(4, F) →* X) (hΨi : Function.Injective Ψ) (hΨs : Function.Surjective Ψ) {t : X}
    {σ : Fin 4 → Bool} (hf : ∀ y, t * Ψ y * t⁻¹ = Ψ (slConjugation 4 F (signGL F σ) y))
    (hJ₁ : (coordSet σ true).card = 2) (hJ₂ : (coordSet σ false).card = 2) {c : X}
    (hc : ∀ y, Ψ y = c → (y : Matrix (Fin 4) (Fin 4) F) = -1) {Q : Subgroup X}
    (hQ : IsSolvableTwoComponentIn Q (centralizer {t})) (hcQ : c ∈ Q) : False := by
  have h2 : (2 : F) ≠ 0 := Foote5.OddLieCore.two_ne_zero_of_card hF
  have hmemC : ∀ y, Ψ y ∈ centralizer ({t} : Set X) ↔
      slConjugation 4 F (signGL F σ) y = y := by
    intro y
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply hΨi
      rw [← hf y, ← h, mul_inv_cancel_right]
    · intro h
      have h' := hf y
      rw [h] at h'
      calc Ψ y * t = t * Ψ y * t⁻¹ * t := by rw [h']
        _ = t * Ψ y := by group
  have hC : ∀ x ∈ centralizer ({t} : Set X),
      ∃ y, Ψ y = x ∧ slConjugation 4 F (signGL F σ) y = y := by
    intro x hx
    obtain ⟨y, rfl⟩ := hΨs x
    exact ⟨y, rfl, (hmemC y).mp hx⟩
  have hblk : ∀ (b : Bool) (hJ : (coordSet σ b).card = 2) (M : SL(2, F)),
      blockTwo (coordSet σ b) hJ M ∈ coordBlockSL F (coordSet σ b) := fun b hJ M => by
    rw [← range_blockTwo _ hJ]
    exact ⟨M, rfl⟩
  have hfix : ∀ (b : Bool) (y : SL(4, F)), y ∈ coordBlockSL F (coordSet σ b) →
      slConjugation 4 F (signGL F σ) y = y := by
    intro b y hy
    refine slConjugation_diagGL_fixes_coordBlockSL _ ?_ hy
    intro i hi j hj
    rw [mem_coordSet] at hi hj
    rw [hi, hj]
  set ρ : ∀ b : Bool, (coordSet σ b).card = 2 → SL(2, F) →* X :=
    fun b hJ => Ψ.comp (blockTwo (coordSet σ b) hJ) with hρ
  have hρi : ∀ b hJ, Function.Injective (ρ b hJ) := fun b hJ =>
    hΨi.comp (blockTwo_injective _ hJ)
  have hR : ∀ b hJ, (ρ b hJ).range ≤ centralizer ({t} : Set X) := by
    rintro b hJ _ ⟨M, rfl⟩
    exact (hmemC _).mpr (hfix b _ (hblk b hJ M))
  have hN : ∀ b hJ, ((ρ b hJ).range.subgroupOf (centralizer ({t} : Set X))).Normal := by
    intro b hJ
    rw [normal_subgroupOf_iff (hR b hJ)]
    rintro _ x ⟨M, rfl⟩ hx
    obtain ⟨y, rfl, hy⟩ := hC x hx
    have hmem : y * blockTwo _ hJ M * y⁻¹ ∈ coordBlockSL F (coordSet σ b) :=
      conj_mem_coordBlockSL (compIndicator_comm_of_fixed_signGL h2 hy b) (hblk b hJ M)
    rw [← range_blockTwo _ hJ] at hmem
    obtain ⟨M', hM'⟩ := hmem
    exact ⟨M', by
      change Ψ (blockTwo _ hJ M') = Ψ y * Ψ (blockTwo _ hJ M) * (Ψ y)⁻¹
      rw [hM', map_mul, map_mul, map_inv]⟩
  have hdisj : Disjoint ((coordSet σ true : Finset (Fin 4)) : Set (Fin 4))
      ((coordSet σ false : Finset (Fin 4)) : Set (Fin 4)) := by
    rw [Set.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_coe, mem_coordSet] at hi hi'
    rw [hi] at hi'
    exact Bool.noConfusion hi'
  have hcomm : ∀ A B, ρ true hJ₁ A * ρ false hJ₂ B = ρ false hJ₂ B * ρ true hJ₁ A := by
    intro A B
    change Ψ _ * Ψ _ = Ψ _ * Ψ _
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact (LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp.commute
      (isSupp_blockTwo _ hJ₁ A) (isSupp_blockTwo _ hJ₂ B) hdisj).eq
  have hinf : ∀ A B, ρ true hJ₁ A = ρ false hJ₂ B → A = 1 := by
    intro A B h
    change Ψ (blockTwo (coordSet σ true) hJ₁ A) = Ψ (blockTwo (coordSet σ false) hJ₂ B) at h
    have h' : blockTwo (coordSet σ true) hJ₁ A = blockTwo (coordSet σ false) hJ₂ B := hΨi h
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    have e := congrArg (fun z : SL(4, F) => (z : Matrix (Fin 4) (Fin 4) F)
      (blockPt _ hJ₁ a) (blockPt _ hJ₁ b)) h'
    have hpt : ∀ a, blockPt (coordSet σ true) hJ₁ a ∉ coordSet σ false := fun a h => by
      have h1 := mem_coordSet.mp (blockPt_mem _ hJ₁ a)
      rw [mem_coordSet, h1] at h
      exact Bool.noConfusion h
    rw [blockTwo_apply_pt, blockTwo_apply_not_mem _ hJ₂ B (Or.inl (hpt a))] at e
    rw [e, Matrix.SpecialLinearGroup.coe_one, one_apply]
    simp [(blockPt_injective _ hJ₁).eq_iff]
  have hdec : ∀ x ∈ centralizer ({t} : Set X), x ^ 3 = 1 →
      ∃ A B, x = ρ true hJ₁ A * ρ false hJ₂ B := by
    intro x hx hx3
    obtain ⟨y, rfl, hy⟩ := hC x hx
    have hy3 : y ^ 3 = 1 := hΨi (by rw [map_pow, hx3, map_one])
    obtain ⟨A, B, hAB⟩ := exists_blockTwo_mul_of_pow_three hF hJ₁ hJ₂ hy hy3
    exact ⟨A, B, by rw [hAB, map_mul]; rfl⟩
  have hZ : ∀ b hJ, ∀ x ∈ centralizer ({t} : Set X), ρ b hJ (-1) * x = x * ρ b hJ (-1) := by
    intro b hJ x hx
    obtain ⟨y, rfl, hy⟩ := hC x hx
    change Ψ _ * Ψ y = Ψ y * Ψ _
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [blockTwo_neg_one]
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : σ i = σ j
    · have : (i ∈ coordSet σ b ↔ j ∈ coordSet σ b) := by rw [mem_coordSet, mem_coordSet, hij]
      by_cases hi : i ∈ coordSet σ b
      · simp [hi, this.mp hi]
      · simp [hi, mt this.mpr hi]
    · rw [entry_eq_zero_of_fixed_signGL h2 hy hij]
      simp
  have hcρ : ρ true hJ₁ (-1) * ρ false hJ₂ (-1) = c := by
    obtain ⟨y₀, hy₀⟩ := hΨs c
    rw [← hy₀]
    change Ψ _ * Ψ _ = Ψ y₀
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hc y₀ hy₀, blockTwo_neg_one, blockTwo_neg_one,
      diagonal_mul_diagonal]
    ext i j
    rw [diagonal_apply, Matrix.neg_apply, one_apply]
    by_cases hij : i = j
    · subst hij
      cases h : σ i <;> simp [mem_coordSet, h]
    · simp [hij]
  exact false_of_two_sl hF (ρ true hJ₁) (ρ false hJ₂) (hρi _ _) (hρi _ _) (hR _ _) (hR _ _)
    (hN _ _) (hN _ _) hcomm hinf hdec (hZ _ _) (hZ _ _) hQ (hcρ ▸ hcQ)

theorem harris82Lemma58bThreeRowAt_PSL_four : Harris82Lemma58bThreeRowAt .PSL 4 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ _ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  obtain ⟨F, _, _, Ψ, hF, hΨi, hΨs, hΨc⟩ := P58b3L.exists_sl_iso hX hO (by norm_num) hmX
    (P58b3L.mk_ne_one hz₁ hz₁K) (P58b3L.mk_mem_center hKc.1 hz₁K)
  have h2 : (2 : F) ≠ 0 := Foote5.OddLieCore.two_ne_zero_of_card hF
  obtain ⟨P, σ, hf⟩ := P58b3L.exists_sign_chart h2 (by norm_num) Ψ hΨi hΨs
    (P58b3L.mk_mul_self hz₂ hz₂K)
  have hΨ'i : Function.Injective (Ψ.comp (MulAut.conj P).toMonoidHom) :=
    hΨi.comp (MulAut.conj P).injective
  have hΨ's : Function.Surjective (Ψ.comp (MulAut.conj P).toMonoidHom) :=
    hΨs.comp (MulAut.conj P).surjective
  have hc' := P58b3L.conj_preimage Ψ hΨc P
  by_cases hbig : ∃ b₀, 3 ≤ (coordSet σ b₀).card
  · obtain ⟨b₀, hb₀⟩ := hbig
    obtain ⟨Q, hQt, hQsub, -, hQsolv, a, ha, b, hb, haa, hbb, hab⟩ :=
      P58b3L.exists_quat_config hz₁ hz₂ hL₁ hz₁L he₁ hKc.1 hO₁ hz₁K hz₂K
    exact P58b3L.false_of_block hF _ hΨ'i hΨ's hf hb₀ hQt hQsub hQsolv ha hb hc' haa hbb hab
  · push Not at hbig
    have hsum := Foote5.OddLieCore.card_coordSet_add σ
    have h1 := hbig true
    have h0 := hbig false
    have hJ₁ : (coordSet σ true).card = 2 := by omega
    have hJ₂ : (coordSet σ false).card = 2 := by omega
    have hQ := lemma57_fourGroup_map_of_aut hz₂ hL₁ hKc.1 hO₁ hN hz₂K hz₁K
      (oddAutInner_of_PSL_four hX hmX)
    have hcQ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
        ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
      ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
    exact false_of_sl4 hF _ hΨ'i hΨ's hf hJ₁ hJ₂ hc' hQ hcQ

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
