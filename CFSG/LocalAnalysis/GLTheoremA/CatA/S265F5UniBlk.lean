module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5LinBlk
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open Matrix
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (compIndicator)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  (coordBlockSU blockSUOn_injective mem_coordBlockSU_iff mem_coordBlockSU_iff_indicator)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedSU_eq_gramSU)

section Quasi

variable {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]

theorem isQuasisimple_coordBlockSU_of_two_pow {e n : ℕ} (hK : Nat.card K₀ = (2 ^ e) ^ 2)
    (he : 2 ≤ e) {J : Finset (Fin n)} (hJ : 2 ≤ J.card) :
    CFSG.Open.IsQuasisimple (coordBlockSU K₀ 2 e J) :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (blockSUOn_injective (K := K₀) (p := 2) (f := e) J))
      (CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
        (MulEquiv.subgroupCongr (SUid_eq_statedSU hK J.card)).symm
        (CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_statedSU_of_two_le hK he hJ)))

end Quasi

section Entries

variable {F : Type} [Field F]

theorem diagonal_mul_comm_of_eq_one_off {n : ℕ} {d : Fin n → F} {J : Finset (Fin n)}
    (hJ : ∀ i ∈ J, ∀ j ∈ J, d i = d j) {N : Matrix (Fin n) (Fin n) F}
    (hN : ∀ i j, (i ∉ J ∨ j ∉ J) → N i j = if i = j then 1 else 0) :
    diagonal d * N = N * diagonal d := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hi : i ∈ J
  · by_cases hj : j ∈ J
    · rw [hJ i hi j hj, mul_comm]
    · rw [hN i j (Or.inr hj)]
      split_ifs with hij
      · subst hij
        ring
      · ring
  · rw [hN i j (Or.inl hi)]
    split_ifs with hij
    · subst hij
      ring
    · ring

end Entries

section Subfield

variable {f e : ℕ} {K : Type} [Field K]

private theorem mem_gramSU_of_subfieldGL (h : UnitaryFieldData 2 f K) {k : Subfield K}
    (h₀ : UnitaryFieldData 2 e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {n : ℕ}
    {g : GL (Fin n) k} (hg : subfieldGL k n g ∈ gramSU h (idGram K n)) :
    g ∈ gramSU h₀ (idGram k n) := by
  obtain ⟨h1, h2⟩ := mem_gramSU.1 hg
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · simp only [idGram, Units.val_one, Matrix.mul_one] at h1 ⊢
    rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul] at h1
    refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
    change (((g : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g).map k.subtype =
      (1 : Matrix (Fin n) (Fin n) k).map k.subtype
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [coe_subfieldGL] at h2
    apply Subtype.val_injective
    change k.subtype ((g : Matrix (Fin n) (Fin n) k).det) = k.subtype 1
    rw [RingHom.map_det, map_one]
    exact h2

end Subfield

section Block

variable {K : Type} [Field K] [CharP K 2]

theorem glaPLayer_ne_bot_of_unitary_diagonal_block {f : ℕ} (h : UnitaryFieldData 2 f K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} {e : ℕ}
    (h₀ : UnitaryFieldData 2 e (fixSubfield σ))
    (hbar₀ : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) (he2 : 2 ≤ e) (hpe : p ∣ 2 ^ e + 1)
    {X : primeFormUnitary h (idGram K p)} {d : Fin p → K}
    (hX : ((X : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = diagonal d)
    {a a' c : Fin p} (haa' : a ≠ a') (hda : d a = d a') (hdc : d c ≠ d a) :
    GLAPLayer p (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K p) X)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := h.finite
  set K₀ := fixSubfield σ with hK₀def
  haveI : Finite K₀ := h₀.finite
  haveI : CharP K₀ 2 := h₀.charP
  have hσK₀ : ∀ x ∈ K₀, σ x = x := fun x hx => RingHom.mem_eqLocusField.mp hx
  have hK₀card : Nat.card K₀ = (2 ^ e) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  have hcard : Fintype.card (Fin p) < 2 * p := by
    rw [Fintype.card_fin]
    have := hp.pos
    omega
  set hC := isPrimeFormGram_idGram (K := K) (n := p) with hCdef
  have hd0 : ∀ l, d l ≠ 0 := by
    intro l h0
    have hdet : ((X : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    apply hdet
    rw [hX, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ l) h0
  set J : Finset (Fin p) := Finset.univ.filter fun l => d l = d a with hJ
  have hmemJ : ∀ l, l ∈ J ↔ d l = d a := fun l => by simp [hJ]
  have haJ : a ∈ J := (hmemJ a).2 rfl
  have ha'J : a' ∈ J := (hmemJ a').2 hda.symm
  have hcJ : c ∉ J := fun h => hdc ((hmemJ c).1 h)
  have hJ2 : 2 ≤ J.card := by
    calc 2 = ({a, a'} : Finset (Fin p)).card := (Finset.card_pair haa').symm
      _ ≤ J.card := Finset.card_le_card (by
          intro l hl
          rcases Finset.mem_insert.1 hl with rfl | hl
          · exact haJ
          · rw [Finset.mem_singleton.1 hl]
            exact ha'J)
  have hdJ : ∀ i ∈ J, ∀ j ∈ J, d i = d j := fun i hi j hj =>
    ((hmemJ i).1 hi).trans ((hmemJ j).1 hj).symm
  have heq₀ : SUid (unitaryInvolution K₀ 2 e) p = gramSU h₀ (idGram K₀ p) :=
    (SUid_eq_statedSU hK₀card p).trans (statedSU_eq_gramSU h₀ p)
  set Bk := coordBlockSU K₀ 2 e J with hBk
  set ι : Su K₀ 2 e p →* gramSU h (idGram K p) :=
    (subfieldSU h h₀ hbar₀ p).comp (MulEquiv.subgroupCongr heq₀).toMonoidHom with hιdef
  have hιcoe : ∀ g : Su K₀ 2 e p, ((ι g : gramSU h (idGram K p)) : GL (Fin p) K) =
      subfieldGL K₀ p (g : GL (Fin p) K₀) := fun g => rfl
  set ψ : ↥Bk →* primeFormP h (idGram K p) :=
    (QuotientGroup.mk' _).comp (ι.comp Bk.subtype) with hψdef
  have hψ : ∀ g : ↥Bk, ψ g = ((ι g : gramSU h (idGram K p)) : primeFormP h (idGram K p)) :=
    fun g => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hψ, QuotientGroup.eq_one_iff] at hg
    obtain ⟨ν, -, -, hν⟩ := hg
    have hgc := mem_coordBlockSU_iff.1 g.2 c c (Or.inl hcJ)
    have hν1 : ν = 1 := by
      apply Units.ext
      have h1 := congrArg (fun x : GL (Fin p) K => (x : Matrix (Fin p) (Fin p) K) c c) hν
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
      rw [hιcoe, coe_subfieldGL, Matrix.map_apply, hgc, if_pos rfl] at h1
      simpa using h1.symm
    have hg1 : ((g : Su K₀ 2 e p) : GL (Fin p) K₀) = 1 := by
      apply subfieldGL_injective K₀ p
      rw [map_one, ← hιcoe, hν, hν1, map_one]
    exact Subtype.ext (Subtype.ext hg1)
  have hσB : ∀ g : GL (Fin p) K₀, glAut σ (subfieldGL K₀ p g) = subfieldGL K₀ p g := by
    intro g
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hσK₀ _ ((g : Matrix (Fin p) (Fin p) K₀) i j).2
  have hXB : ∀ g : Su K₀ 2 e p, g ∈ Bk →
      (X : GL (Fin p) K) * subfieldGL K₀ p (g : GL (Fin p) K₀) =
        subfieldGL K₀ p (g : GL (Fin p) K₀) * X := by
    intro g hg
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_subfieldGL, hX]
    refine diagonal_mul_comm_of_eq_one_off hdJ fun i j hij => ?_
    rw [Matrix.map_apply, mem_coordBlockSU_iff.1 hg i j hij]
    split_ifs <;> simp
  have hLH : ψ.range ≤ fixSubgroup (primeFormFieldHom h hC σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K p) X) := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixSubgroup, hψ]
      show primeFormFieldAut h hC σ _ = _
      rw [primeFormFieldAut_mk]
      congr 1
      exact Subtype.ext (hσB _)
    · rw [mem_fixSubgroup, hψ, primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      show (X : GL (Fin p) K) * subfieldGL K₀ p ((g : Su K₀ 2 e p) : GL (Fin p) K₀) *
        (X : GL (Fin p) K)⁻¹ = subfieldGL K₀ p ((g : Su K₀ 2 e p) : GL (Fin p) K₀)
      rw [hXB _ g.2, mul_inv_cancel_right]
  have hPmap : (compIndicator K₀ J).map K₀.subtype = compIndicator K J := by
    rw [compIndicator, compIndicator, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  have hN : (ψ.range.subgroupOf (fixSubgroup (primeFormFieldHom h hC σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K p) X))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLH]
    rintro _ y ⟨g, rfl⟩ hy
    obtain ⟨Y₁, rfl⟩ := QuotientGroup.mk_surjective y
    have hyσ := (Subgroup.mem_inf.1 hy).1
    have hyX := (Subgroup.mem_inf.1 hy).2
    rw [mem_fixSubgroup] at hyσ hyX
    rw [primeFormConjHom_mk, QuotientGroup.eq] at hyX
    obtain ⟨ν, -, hνp, hν⟩ := hyX
    have hν' : ((X : GL (Fin p) K) * Y₁ * (X : GL (Fin p) K)⁻¹)⁻¹ * (Y₁ : GL (Fin p) K) =
        GeneralLinearGroup.scalar (Fin p) ν := hν
    set s := GeneralLinearGroup.scalar (Fin p) ν with hs
    have hsc : ∀ g : GL (Fin p) K, s * g = g * s := fun g => GeneralLinearGroup.scalar_commute ν g
    have hYX : (Y₁ : GL (Fin p) K) * X = s * ((X : GL (Fin p) K) * Y₁) := by
      have h1 : (Y₁ : GL (Fin p) K) = (X : GL (Fin p) K) * Y₁ * (X : GL (Fin p) K)⁻¹ * s := by
        rw [← hν', mul_inv_cancel_left]
      calc (Y₁ : GL (Fin p) K) * X = (X : GL (Fin p) K) * Y₁ * (X : GL (Fin p) K)⁻¹ * s * X := by
            rw [← h1]
        _ = (X : GL (Fin p) K) * Y₁ * (X : GL (Fin p) K)⁻¹ * (s * X) := by group
        _ = (X : GL (Fin p) K) * Y₁ * (X : GL (Fin p) K)⁻¹ * (X * s) := by rw [hsc]
        _ = s * ((X : GL (Fin p) K) * Y₁) := by
            rw [hsc ((X : GL (Fin p) K) * Y₁)]
            group
    have hYXm : ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * diagonal d =
        (ν : K) • (diagonal d * ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) := by
      have h2 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K)) hYX
      simp only [Units.val_mul, hs, GeneralLinearGroup.coe_scalar, hX] at h2
      rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    have hν1 : (ν : K) = 1 := by
      by_contra hne
      have hνp' : (ν : K) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val, hνp, Units.val_one]
      have hdet : IsUnit ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).det := by
        rw [(mem_gramSU.1 Y₁.2).2]
        exact isUnit_one
      exact haa' (injective_of_mul_diagonal_eq_smul hp hcard hd0 hνp' hne hdet hYXm hda)
    have hYd : diagonal d * ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * diagonal d := by
      rw [hYXm, hν1, one_smul]
    have hYP : compIndicator K J * ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        ((Y₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * compIndicator K J := by
      rw [compIndicator]
      refine diagonal_mul_comm_of_fiber (fun i j hij => ?_) hYd
      simp only [hmemJ, hij]
    have hyσ' : primeFormFieldAut h hC σ (Y₁ : primeFormP h (idGram K p)) = Y₁ := hyσ
    rw [primeFormFieldAut_mk, QuotientGroup.eq] at hyσ'
    obtain ⟨w, -, -, hw⟩ := hyσ'
    have hw' : (glAut σ (Y₁ : GL (Fin p) K))⁻¹ * (Y₁ : GL (Fin p) K) =
        GeneralLinearGroup.scalar (Fin p) w := hw
    have hσY : glAut σ (Y₁ : GL (Fin p) K) =
        (Y₁ : GL (Fin p) K) * (GeneralLinearGroup.scalar (Fin p) w)⁻¹ := by
      rw [← hw', _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    obtain ⟨B₀, hB₀⟩ : ∃ B₀ : GL (Fin p) K₀, B₀ = ((g : Su K₀ 2 e p) : GL (Fin p) K₀) :=
      ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : GL (Fin p) K, u = (Y₁ : GL (Fin p) K) := ⟨_, rfl⟩
    rw [← hu] at hσY hYP
    have humem : u ∈ gramSU h (idGram K p) := hu ▸ Y₁.2
    have hBmem : subfieldGL K₀ p B₀ ∈ gramSU h (idGram K p) := by
      rw [hB₀, ← hιcoe]
      exact (ι g).2
    have hsB : (GeneralLinearGroup.scalar (Fin p) w)⁻¹ * subfieldGL K₀ p B₀ =
        subfieldGL K₀ p B₀ * (GeneralLinearGroup.scalar (Fin p) w)⁻¹ :=
      (show Commute (GeneralLinearGroup.scalar (Fin p) w) (subfieldGL K₀ p B₀) from
        GeneralLinearGroup.scalar_commute w _).inv_left.eq
    obtain ⟨Z, hZ⟩ : ∃ Z : GL (Fin p) K, Z = u * subfieldGL K₀ p B₀ * u⁻¹ := ⟨_, rfl⟩
    have hZσ : glAut σ Z = Z := by
      rw [hZ, map_mul, map_mul, map_inv, hσY, hσB]
      calc u * (GeneralLinearGroup.scalar (Fin p) w)⁻¹ * subfieldGL K₀ p B₀ *
            (u * (GeneralLinearGroup.scalar (Fin p) w)⁻¹)⁻¹
          = u * ((GeneralLinearGroup.scalar (Fin p) w)⁻¹ * subfieldGL K₀ p B₀) *
              GeneralLinearGroup.scalar (Fin p) w * u⁻¹ := by group
        _ = u * (subfieldGL K₀ p B₀ * (GeneralLinearGroup.scalar (Fin p) w)⁻¹) *
              GeneralLinearGroup.scalar (Fin p) w * u⁻¹ := by rw [hsB]
        _ = u * subfieldGL K₀ p B₀ * u⁻¹ := by group
    have hZmem : Z ∈ gramSU h (idGram K p) := by
      rw [hZ]
      exact mul_mem (mul_mem humem hBmem) (inv_mem humem)
    obtain ⟨Z₀, hZ₀⟩ := exists_subfieldGL_eq_of_fixed p hZσ
    have hZ₀g : Z₀ ∈ gramSU h₀ (idGram K₀ p) :=
      mem_gramSU_of_subfieldGL h h₀ hbar₀ (by rw [hZ₀]; exact hZmem)
    obtain ⟨hg1, hg2⟩ := mem_coordBlockSU_iff_indicator.1 g.2
    rw [← hB₀] at hg1 hg2
    set P := compIndicator K J with hP
    set Um : Matrix (Fin p) (Fin p) K := (u : Matrix (Fin p) (Fin p) K) with hUm
    set Ui : Matrix (Fin p) (Fin p) K := ((u⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)
      with hUi
    set Bm : Matrix (Fin p) (Fin p) K := (B₀ : Matrix (Fin p) (Fin p) K₀).map K₀.subtype with hBm
    have hUU : Um * Ui = 1 := by rw [hUm, hUi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hUU' : Ui * Um = 1 := by rw [hUm, hUi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hPB : P * Bm = P := by
      have := congrArg (fun M : Matrix (Fin p) (Fin p) K₀ => M.map K₀.subtype) hg1
      simp only [Matrix.map_mul, hPmap] at this
      exact this
    have hBP : Bm * P = P := by
      have := congrArg (fun M : Matrix (Fin p) (Fin p) K₀ => M.map K₀.subtype) hg2
      simp only [Matrix.map_mul, hPmap] at this
      exact this
    have hPUi : P * Ui = Ui * P := by
      calc P * Ui = Ui * Um * P * Ui := by rw [hUU', Matrix.one_mul]
        _ = Ui * (Um * P) * Ui := by simp only [Matrix.mul_assoc]
        _ = Ui * (P * Um) * Ui := by rw [hYP]
        _ = Ui * P * (Um * Ui) := by simp only [Matrix.mul_assoc]
        _ = Ui * P := by rw [hUU, Matrix.mul_one]
    have hZm : (Z : Matrix (Fin p) (Fin p) K) = Um * Bm * Ui := by
      rw [hZ, Units.val_mul, Units.val_mul, coe_subfieldGL]
    have hPZ : P * (Z : Matrix (Fin p) (Fin p) K) = P := by
      rw [hZm]
      calc P * (Um * Bm * Ui) = Um * (P * Bm) * Ui := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hYP, Matrix.mul_assoc Um P Bm]
        _ = P := by rw [hPB, Matrix.mul_assoc, hPUi, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    have hZP : (Z : Matrix (Fin p) (Fin p) K) * P = P := by
      rw [hZm]
      calc Um * Bm * Ui * P = Um * (Bm * P) * Ui := by
            rw [Matrix.mul_assoc, hPUi.symm, ← Matrix.mul_assoc, Matrix.mul_assoc Um Bm P]
        _ = P := by rw [hBP, ← hYP, Matrix.mul_assoc, hUU, Matrix.mul_one]
    have hZ₀m : (Z₀ : Matrix (Fin p) (Fin p) K₀).map K₀.subtype = (Z : Matrix (Fin p) (Fin p) K) := by
      rw [← hZ₀, coe_subfieldGL]
    have hinj := Matrix.map_injective (m := Fin p) (n := Fin p)
      (f := (K₀.subtype : K₀ → K)) Subtype.val_injective
    set Z₀s : Su K₀ 2 e p := ⟨Z₀, (SetLike.ext_iff.1 heq₀ Z₀).2 hZ₀g⟩ with hZ₀s
    have hZ₀J : Z₀s ∈ Bk := by
      rw [hBk, mem_coordBlockSU_iff_indicator]
      refine ⟨hinj ?_, hinj ?_⟩
      · change (compIndicator K₀ J * (Z₀ : Matrix (Fin p) (Fin p) K₀)).map K₀.subtype =
          (compIndicator K₀ J).map K₀.subtype
        rw [Matrix.map_mul, hPmap, hZ₀m, hPZ]
      · change ((Z₀ : Matrix (Fin p) (Fin p) K₀) * compIndicator K₀ J).map K₀.subtype =
          (compIndicator K₀ J).map K₀.subtype
        rw [Matrix.map_mul, hPmap, hZ₀m, hZP]
    refine ⟨⟨Z₀s, hZ₀J⟩, ?_⟩
    rw [hψ, hψ g, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show subfieldGL K₀ p Z₀ = (Y₁ : GL (Fin p) K) *
      subfieldGL K₀ p ((g : Su K₀ 2 e p) : GL (Fin p) K₀) * (Y₁ : GL (Fin p) K)⁻¹
    rw [hZ₀, hZ, hu, hB₀]
  have hLq : CFSG.Open.IsQuasisimple ↥ψ.range :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (MonoidHom.ofInjective hψinj).symm (isQuasisimple_coordBlockSU_of_two_pow hK₀card he2 hJ2)
  have hpK₀ : p ∣ Nat.card K₀ - 1 := by
    obtain ⟨y, hy⟩ : ∃ y, 2 ^ e = y + 1 := ⟨2 ^ e - 1, by have := @Nat.one_le_two_pow e; omega⟩
    have hsq : (y + 1) ^ 2 = y * (y + 1 + 1) + 1 := by ring
    rw [hK₀card, hy, hsq, Nat.add_sub_cancel]
    rw [hy] at hpe
    exact Dvd.dvd.mul_left hpe y
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.CTP.exists_primitiveRoot_of_dvd (F := K₀) hp hpK₀
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζn : h₀.bar ζ * ζ = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    exact (hζ.pow_eq_one_iff_dvd _).2 hpe
  set fd : Fin p → K₀ := fun l => if l = a then ζ else if l = a' then ζ⁻¹ else 1 with hfd
  have hfa : fd a = ζ := if_pos rfl
  have hfa' : fd a' = ζ⁻¹ := by
    show (if a' = a then ζ else if a' = a' then ζ⁻¹ else 1) = ζ⁻¹
    rw [if_neg haa'.symm, if_pos rfl]
  have hfo : ∀ l, l ≠ a → l ≠ a' → fd l = 1 := fun l h1 h2 => by
    show (if l = a then ζ else if l = a' then ζ⁻¹ else 1) = 1
    rw [if_neg h1, if_neg h2]
  have hfdet : ∏ l, fd l = 1 := by
    have hsub : ∀ l ∈ (Finset.univ : Finset (Fin p)), l ∉ ({a, a'} : Finset (Fin p)) →
        fd l = 1 := by
      intro l _ hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact hfo l hl.1 hl.2
    rw [← Finset.prod_subset (Finset.subset_univ _) hsub, Finset.prod_pair haa', hfa, hfa',
      mul_inv_cancel₀ hζ0]
  have hfp : ∀ l, fd l ^ p = 1 := by
    intro l
    by_cases h1 : l = a
    · rw [h1, hfa, hζ.pow_eq_one]
    · by_cases h2 : l = a'
      · rw [h2, hfa', inv_pow, hζ.pow_eq_one, inv_one]
      · rw [hfo l h1 h2, one_pow]
  have hfn : ∀ l, h₀.bar (fd l) * fd l = 1 := by
    intro l
    by_cases h1 : l = a
    · rw [h1, hfa, hζn]
    · by_cases h2 : l = a'
      · rw [h2, hfa', map_inv₀, ← mul_inv, hζn, inv_one]
      · rw [hfo l h1 h2, map_one, one_mul]
  have hf0 : ∀ l, fd l ≠ 0 := fun l h0 => by
    have := hfp l
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : GL (Fin p) K₀, (x₀ : Matrix (Fin p) (Fin p) K₀) = diagonal fd :=
    ⟨⟨diagonal fd, diagonal fun l => (fd l)⁻¹,
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext l; exact mul_inv_cancel₀ (hf0 l),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext l; exact inv_mul_cancel₀ (hf0 l)⟩,
      rfl⟩
  have hx₀g : x₀ ∈ gramSU h₀ (idGram K₀ p) := by
    refine mem_gramSU.2 ⟨?_, ?_⟩
    · simp only [idGram, Units.val_one, Matrix.mul_one]
      rw [hx₀, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext l
      exact hfn l
    · rw [hx₀, det_diagonal, hfdet]
  have hx₀p : x₀ ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hx₀, diagonal_pow, Units.val_one, ← diagonal_one]
    congr 1
    funext l
    exact hfp l
  obtain ⟨sw, hsw⟩ : ∃ sw : Matrix (Fin p) (Fin p) K₀,
      sw = (Equiv.swap a a').permMatrix K₀ := ⟨_, rfl⟩
  have hswapp : ∀ i j, sw i j = if Equiv.swap a a' i = j then 1 else 0 := by
    intro i j
    rw [hsw, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_def, Option.some.injEq]
  have hsw2 : sw * sw = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hswapp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Equiv.swap_apply_self]
  have hswT : swᵀ = sw := by
    rw [hsw, Matrix.transpose_permMatrix, Equiv.swap_inv]
  have hswmap : sw.map h₀.bar = sw := by
    ext i j
    rw [Matrix.map_apply, hswapp]
    split_ifs <;> simp
  have hswdet : sw.det = 1 := by
    rw [hsw, Matrix.det_permutation, Equiv.Perm.sign_swap haa']
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    exact CharTwo.neg_eq 1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : GL (Fin p) K₀, (s₀ : Matrix (Fin p) (Fin p) K₀) = sw :=
    ⟨⟨sw, sw, hsw2, hsw2⟩, rfl⟩
  have hs₀g : s₀ ∈ gramSU h₀ (idGram K₀ p) := by
    refine mem_gramSU.2 ⟨?_, ?_⟩
    · simp only [idGram, Units.val_one, Matrix.mul_one]
      rw [hs₀, hswmap, hswT, hsw2]
    · rw [hs₀, hswdet]
  have hswaa' : sw a a' = 1 := by rw [hswapp, Equiv.swap_apply_left, if_pos rfl]
  have hnc : x₀ * s₀ ≠ s₀ * x₀ := by
    intro hxs
    have h' := congrArg (fun A : GL (Fin p) K₀ => (A : Matrix (Fin p) (Fin p) K₀) a a') hxs
    simp only [Units.val_mul, hx₀, hs₀, diagonal_mul, mul_diagonal, hswaa', hfa, hfa', mul_one,
      one_mul] at h'
    have hζ2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h']
      exact mul_inv_cancel₀ hζ0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((hζ.pow_eq_one_iff_dvd 2).1 hζ2))
  have hblk : ∀ (g : GL (Fin p) K₀) (hg : g ∈ gramSU h₀ (idGram K₀ p)),
      (∀ i j, (i ∉ J ∨ j ∉ J) → (g : Matrix (Fin p) (Fin p) K₀) i j = if i = j then 1 else 0) →
      (⟨g, (SetLike.ext_iff.1 heq₀ g).2 hg⟩ : Su K₀ 2 e p) ∈ Bk := by
    intro g hg hent
    rw [hBk, mem_coordBlockSU_iff]
    exact hent
  have hx₀J := hblk x₀ hx₀g (by
    intro i j hij
    rw [hx₀]
    by_cases hij' : i = j
    · subst hij'
      rw [diagonal_apply_eq, if_pos rfl]
      have hi : i ∉ J := by tauto
      exact hfo i (fun h' => hi (h' ▸ haJ)) (fun h' => hi (h' ▸ ha'J))
    · rw [diagonal_apply_ne _ hij', if_neg hij'])
  have hs₀J := hblk s₀ hs₀g (by
    intro i j hij
    rw [hs₀, hswapp]
    rcases hij with hi | hj
    · have hia : i ≠ a := fun h' => hi (by rw [h']; exact haJ)
      have hia' : i ≠ a' := fun h' => hi (by rw [h']; exact ha'J)
      have hsi : Equiv.swap a a' i = i := Equiv.swap_apply_of_ne_of_ne hia hia'
      by_cases hij : i = j
      · subst hij
        rw [if_pos hsi, if_pos rfl]
      · have hne : Equiv.swap a a' i ≠ j := by
          rw [hsi]
          exact hij
        rw [if_neg hne, if_neg hij]
    · have hja : j ≠ a := fun h' => hj (by rw [h']; exact haJ)
      have hja' : j ≠ a' := fun h' => hj (by rw [h']; exact ha'J)
      have hsj : Equiv.swap a a' j = j := Equiv.swap_apply_of_ne_of_ne hja hja'
      by_cases hij : i = j
      · subst hij
        rw [if_pos hsj, if_pos rfl]
      · have hne : Equiv.swap a a' i ≠ j := by
          intro h'
          apply hij
          rw [← hsj] at h'
          exact (Equiv.swap a a').injective h'
        rw [if_neg hne, if_neg hij])
  set eJ := MonoidHom.ofInjective hψinj with heJ
  set x : ↥ψ.range := eJ ⟨_, hx₀J⟩ with hx
  set y : ↥ψ.range := eJ ⟨_, hs₀J⟩ with hy
  have hxy : x * y ≠ y * x := by
    intro hxy
    rw [hx, hy, ← map_mul, ← map_mul] at hxy
    exact hnc (congrArg (fun z : ↥Bk => ((z : Su K₀ 2 e p) : GL (Fin p) K₀)) (eJ.injective hxy))
  have hxp : x ^ p = 1 := by
    rw [hx, ← map_pow]
    have h1 : (⟨_, hx₀J⟩ : ↥Bk) ^ p = 1 := Subtype.ext (Subtype.ext hx₀p)
    rw [h1, map_one]
  have hxc : x ∉ Subgroup.center ↥ψ.range := fun hxc =>
    hxy (Subgroup.mem_center_iff.1 hxc y).symm
  have hdvd : p ∣ Nat.card (↥ψ.range ⧸ Subgroup.center ↥ψ.range) := by
    have hord : orderOf (x : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = p := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]
      · intro h
        exact hxc ((QuotientGroup.eq_one_iff x).1 h)
    have h := orderOf_dvd_natCard (x : ↥ψ.range ⧸ Subgroup.center ↥ψ.range)
    rwa [hord] at h
  exact Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp hLH hN hLq hdvd

end Block

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
