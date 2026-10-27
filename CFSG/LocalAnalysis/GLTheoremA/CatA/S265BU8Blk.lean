module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8BlkConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5UniBlk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open Matrix
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedSU_eq_gramSU)
open CFSG.LocalAnalysis.GLTheoremA.S265F5 (diagonal_mul_comm_of_eq_one_off)

variable {K : Type} [Field K]

theorem glaPLayer_ne_bot_of_diagonal_four (h : UnitaryFieldData 2 3 K) {n : ℕ}
    (hn : n = 5 ∨ n = 6) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {X₀ : primeFormUnitary h (idGram K n)} {e : Fin n → K}
    (hX₀ : ((X₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal e)
    (h4 : Nat.card {l // e l = 1} = 4) :
    GLAPLayer 3 (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K n) X₀)) ≠ ⊥ := by
  classical
  haveI := h.finite
  have h₀ : UnitaryFieldData 2 1 (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ
  have hbar₀ : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h Nat.prime_three (by decide) hσ
  set K₀ := fixSubfield σ
  haveI : Finite K₀ := h₀.finite
  haveI : CharP K₀ 2 := h₀.charP
  set hC := isPrimeFormGram_idGram (K := K) (n := n)
  set J : Finset (Fin n) := Finset.univ.filter fun l => e l = 1 with hJ
  have hJe : ∀ l, l ∈ J ↔ e l = 1 := fun l => by simp [hJ]
  have hJ4 : J.card = 4 := by
    rw [← Nat.card_eq_finsetCard, ← h4]
    exact Nat.card_congr (Equiv.subtypeEquivRight hJe)
  obtain ⟨c, hcJ⟩ : ∃ c, c ∉ J := by
    by_contra hall
    push Not at hall
    have := Finset.card_le_card (fun l _ => hall l : (Finset.univ : Finset (Fin n)) ⊆ J)
    rw [Finset.card_univ, Fintype.card_fin, hJ4] at this
    omega
  have hJc : Jᶜ.card < J.card := by
    rw [Finset.card_compl, Fintype.card_fin, hJ4]
    omega
  have hdJ : ∀ i ∈ J, ∀ j ∈ J, e i = e j := fun i hi j hj =>
    ((hJe i).1 hi).trans ((hJe j).1 hj).symm
  have heq₀ : SUid (unitaryInvolution K₀ 2 1) n = gramSU h₀ (idGram K₀ n) :=
    (SUid_eq_statedSU (h₀.card.trans (by norm_num)) n).trans (statedSU_eq_gramSU h₀ n)
  set Bk := coordBlockSU K₀ 2 1 J
  set ι : Su K₀ 2 1 n →* gramSU h (idGram K n) :=
    (subfieldSU h h₀ hbar₀ n).comp (MulEquiv.subgroupCongr heq₀).toMonoidHom
  have hιcoe : ∀ g : Su K₀ 2 1 n, ((ι g : gramSU h (idGram K n)) : GL (Fin n) K) =
      subfieldGL K₀ n (g : GL (Fin n) K₀) := fun g => rfl
  set ψ : ↥Bk →* primeFormP h (idGram K n) :=
    (QuotientGroup.mk' _).comp (ι.comp Bk.subtype)
  have hψ : ∀ g : ↥Bk, ψ g = ((ι g : gramSU h (idGram K n)) : primeFormP h (idGram K n)) :=
    fun g => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hψ, QuotientGroup.eq_one_iff] at hg
    obtain ⟨ν, -, -, hν⟩ := hg
    have hgc := mem_coordBlockSU_iff.1 g.2 c c (Or.inl hcJ)
    have hν1 : ν = 1 := by
      apply Units.ext
      have h1 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) c c) hν
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at h1
      rw [hιcoe, coe_subfieldGL, Matrix.map_apply, hgc, if_pos rfl] at h1
      simpa using h1.symm
    have hg1 : ((g : Su K₀ 2 1 n) : GL (Fin n) K₀) = 1 := by
      apply subfieldGL_injective K₀ n
      rw [map_one, ← hιcoe, hν, hν1, map_one]
    exact Subtype.ext (Subtype.ext hg1)
  have hσB : ∀ g : GL (Fin n) K₀, glAut σ (subfieldGL K₀ n g) = subfieldGL K₀ n g := by
    intro g
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact (mem_fixSubfield σ).1 ((g : Matrix (Fin n) (Fin n) K₀) i j).2
  have hXB : ∀ g : Su K₀ 2 1 n, g ∈ Bk →
      (X₀ : GL (Fin n) K) * subfieldGL K₀ n (g : GL (Fin n) K₀) =
        subfieldGL K₀ n (g : GL (Fin n) K₀) * X₀ := by
    intro g hg
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_subfieldGL, hX₀]
    refine diagonal_mul_comm_of_eq_one_off hdJ fun i j hij => ?_
    rw [Matrix.map_apply, mem_coordBlockSU_iff.1 hg i j hij]
    split_ifs <;> simp
  have hLH : ψ.range ≤ fixSubgroup (primeFormFieldHom h hC σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K n) X₀) := by
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
      show (X₀ : GL (Fin n) K) * subfieldGL K₀ n ((g : Su K₀ 2 1 n) : GL (Fin n) K₀) *
        (X₀ : GL (Fin n) K)⁻¹ = subfieldGL K₀ n ((g : Su K₀ 2 1 n) : GL (Fin n) K₀)
      rw [hXB _ g.2, mul_inv_cancel_right]
  have hN : (ψ.range.subgroupOf (fixSubgroup (primeFormFieldHom h hC σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K n) X₀))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLH]
    rintro _ y ⟨g, rfl⟩ hy
    obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
    haveI : Finite (fixSubfield σ) := h₀.finite
    haveI : CharP (fixSubfield σ) 2 := h₀.charP
    obtain ⟨Z, hZJ, hZ⟩ := exists_coordBlockSU_eq_conj h (σ := σ) h₀ hbar₀ hX₀ hJe hJc
      (Subgroup.mem_inf.1 hy).1 (Subgroup.mem_inf.1 hy).2 g.2
    refine ⟨⟨Z, hZJ⟩, ?_⟩
    rw [hψ, hψ g, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hZ
  obtain ⟨hsimp, ⟨a, b, hab⟩, h3⟩ := simple_coordBlockSU_of_card_four h₀ hJ4
  haveI : IsSimpleGroup ↥Bk := hsimp
  set eJ := MonoidHom.ofInjective hψinj
  haveI : IsSimpleGroup ψ.range := eJ.symm.isSimpleGroup
  have hnc : ∃ a b : ψ.range, a * b ≠ b * a :=
    ⟨eJ a, eJ b, fun h' => hab (eJ.injective (by rw [map_mul, map_mul]; exact h'))⟩
  have h3L : 3 ∣ Nat.card ψ.range := by
    rw [← Nat.card_congr eJ.toEquiv]
    exact h3
  have hle := le_glaPLayer_of_normal_simple Nat.prime_three hLH hN hnc h3L
  intro hbot
  rw [hbot] at hle
  obtain ⟨a', b', hab'⟩ := hnc
  have ha : a' = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle a'.2))
  have hb : b' = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle b'.2))
  exact hab' (by rw [ha, hb])

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
