module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

section UniModel

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem glaPLayer_ne_bot_of_field_unitary {f : ℕ} (h : UnitaryFieldData 2 f K) (hf : Odd f)
    (hf1 : f ≠ 1) (hf3 : f ≠ 3) {x c : MulAut (primeFormP h (idGram K 3))} (hx3 : x ^ 3 = 1)
    (hxD : x ∉ primeFormD h (idGram K 3)) (hcD : c ∈ primeFormD h (idGram K 3)) (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) (hcomm : x * c = c * x) {t : primeFormP h (idGram K 3)} (ht : orderOf t = 2)
    (hct : c t = t) : GLAPLayer 3 (fixSubgroup x ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  have hne : ¬ (3 = 3 ∧ 2 ^ f = 2) := fun h' =>
    hf1 (Nat.pow_right_injective le_rfl (h'.2.trans (pow_one 2).symm))
  obtain ⟨σ, hσdef⟩ : ∃ σ : K ≃+* K, primeFormFieldFactor h
      (isPrimeFormGram_idGram (K := K) (n := 3)) (le_refl 3) hne x = σ := ⟨_, rfl⟩
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 3)) (le_refl 3) hne
  have hσ3 : σ ^ 3 = 1 := by rw [← hσdef, ← map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hxD
    rw [← hker, MonoidHom.mem_ker, hσdef, h1]
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h0 => hxD (h0 ▸ Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, N, hN⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h (le_refl 3) hne
      Nat.prime_three (by norm_num) x hxo σ hσdef hσo
  obtain ⟨M, rfl⟩ := hcD
  obtain ⟨g, hg⟩ : ∃ g : MulAut (primeFormP h (idGram K 3)),
      g = primeFormConjHom h (idGram K 3) N := ⟨_, rfl⟩
  have hcM' : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) =
      g⁻¹ * primeFormConjHom h (idGram K 3) M * g := by
    rw [hg, map_mul, map_mul, map_inv]
  have hfσ : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ = g⁻¹ * x * g := by
    rw [hg]
    exact hN.symm
  have hM1 : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) ≠ 1 := by
    rw [hcM']
    intro h1
    apply hc1
    calc primeFormConjHom h (idGram K 3) M =
          g * (g⁻¹ * primeFormConjHom h (idGram K 3) M * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hM3 : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) ^ 3 = 1 := by
    rw [hcM']
    have := conj_pow (a := g⁻¹) (b := primeFormConjHom h (idGram K 3) M) (i := 3)
    rw [inv_inv] at this
    rw [this, hc3]
    group
  have hcomm' : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
      primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) =
      primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ := by
    rw [hfσ, hcM']
    calc g⁻¹ * x * g * (g⁻¹ * primeFormConjHom h (idGram K 3) M * g)
        = g⁻¹ * (x * primeFormConjHom h (idGram K 3) M) * g := by group
      _ = g⁻¹ * (primeFormConjHom h (idGram K 3) M * x) * g := by rw [hcomm]
      _ = g⁻¹ * primeFormConjHom h (idGram K 3) M * g * (g⁻¹ * x * g) := by group
  have ht' : orderOf (g⁻¹ t) = 2 :=
    (orderOf_injective (g⁻¹ : MulAut (primeFormP h (idGram K 3))).toMonoidHom
      (MulEquiv.injective _) t).trans ht
  have hfix' : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) (g⁻¹ t) = g⁻¹ t := by
    rw [hcM']
    simp only [MulAut.mul_apply, MulAut.apply_inv_self, hct]
  have hred := glaPLayer_ne_bot_of_fieldHom_conjHom h hf hf3 hσo hM1 hM3 hcomm' ht' hfix'
  apply HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three g⁻¹
  rw [show g⁻¹ * x * g⁻¹⁻¹ = primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ by
      rw [hfσ, inv_inv],
    show g⁻¹ * primeFormConjHom h (idGram K 3) M * g⁻¹⁻¹ =
      primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) by rw [hcM', inv_inv]]
  exact hred

theorem exists_layer_of_unitary_model {T : Type} [Group T] [Finite T] {f : ℕ}
    (h : UnitaryFieldData 2 f K) (hf : Odd f) (hf1 : f ≠ 1) (hf3 : f ≠ 3)
    (e : T ≃* primeFormP h (idGram K 3)) {β : MulAut T} (hβ3 : β ^ 3 = 1)
    (hβD : MulAut.congr e β ∉ primeFormD h (idGram K 3))
    (Eb : Subgroup (MulAut T)) (hE3 : ∀ c ∈ Eb, c ^ 3 = 1)
    (hEcomm : ∀ c ∈ Eb, β * c = c * β) (h9 : 9 ≤ Nat.card Eb) {t : T} (ht : orderOf t = 2)
    (hEt : ∀ c ∈ Eb, c t = t) :
    ∃ c ∈ Eb, c ∉ Subgroup.zpowers β ∧ GLAPLayer 3 (fixSubgroup β ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI : Finite (MulAut (primeFormP h (idGram K 3))) :=
    Finite.of_injective
      (fun (g : MulAut (primeFormP h (idGram K 3))) (w : primeFormP h (idGram K 3)) => g w)
      (fun g g' hgg' => MulEquiv.ext (congrFun hgg'))
  have hne : ¬ (3 = 3 ∧ 2 ^ f = 2) := fun h' =>
    hf1 (Nat.pow_right_injective le_rfl (h'.2.trans (pow_one 2).symm))
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hcard' : Nat.card (Eb.map (MulAut.congr e).toMonoidHom) = Nat.card Eb :=
    Subgroup.card_map_of_injective hφinj
  have hE3' : ∀ c ∈ Eb.map (MulAut.congr e).toMonoidHom, c ^ 3 = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE3 c hc, map_one]
  have hbound := card_le_three_mul_card_inf_primeFormD h hne
    (B := Eb.map (MulAut.congr e).toMonoidHom) hE3'
  have hne' : (Eb.map (MulAut.congr e).toMonoidHom ⊓ primeFormD h (idGram K 3) :
      Subgroup (MulAut (primeFormP h (idGram K 3)))) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hbound
    omega
  obtain ⟨⟨c', hc'⟩, hc'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne'
  obtain ⟨hc'E, hc'D⟩ := Subgroup.mem_inf.1 hc'
  obtain ⟨c, hcE, rfl⟩ := hc'E
  have hcD : MulAut.congr e c ∈ primeFormD h (idGram K 3) := hc'D
  have hc1 : MulAut.congr e c ≠ 1 := fun h0 => hc'1 (Subtype.ext h0)
  have hx3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hc3 : MulAut.congr e c ^ 3 = 1 := by rw [← map_pow, hE3 c hcE, map_one]
  have hxc : MulAut.congr e β * MulAut.congr e c = MulAut.congr e c * MulAut.congr e β := by
    rw [← map_mul, ← map_mul, hEcomm c hcE]
  have hxo : Nat.card (Subgroup.zpowers (MulAut.congr e β)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 (fun h0 => hβD (h0 ▸ Subgroup.one_mem _))
  have hxD := CFSG.LocalAnalysis.GLTheoremA.S265.s265_inf_zpowers_bot Nat.prime_three hxo hβD
  refine ⟨c, hcE, ?_, ?_⟩
  · intro hcβ
    apply hc1
    have hmem : MulAut.congr e c ∈
        (primeFormD h (idGram K 3) ⊓ Subgroup.zpowers (MulAut.congr e β) : Subgroup _) := by
      refine Subgroup.mem_inf.2 ⟨hcD, ?_⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcβ
      exact Subgroup.mem_zpowers_iff.2 ⟨i, (map_zpow (MulAut.congr e) β i).symm⟩
    rw [hxD] at hmem
    exact Subgroup.mem_bot.1 hmem
  · apply glaPLayer_ne_bot_of_congr Nat.prime_three e
    have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
    have hct : MulAut.congr e c (e t) = e t := by
      show e (c (e.symm (e t))) = e t
      rw [MulEquiv.symm_apply_apply, hEt c hcE]
    exact glaPLayer_ne_bot_of_field_unitary h hf hf1 hf3 hx3 hβD hcD hc1 hc3 hxc ht' hct

end UniModel

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
