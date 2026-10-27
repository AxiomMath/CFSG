module

public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits Module
open scoped MatrixGroups

section Involution

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem nondeg_eigSpace_neg_one (h2 : (2 : K) ≠ 0) (x : SUid σ n)
    (hI : suMat x * suMat x = 1) : Nondeg σ (eigSpace (suMat x) (-1)) := by
  intro v hv hv'
  refine eq_zero_of_herm σ fun u => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Submodule.mem_sup.mp ((isCompl_eigSpace h2 hI).sup_eq_top ▸ Submodule.mem_top : u ∈ _ ⊔ _)
  rw [herm_add_right, hv' a ha, orth_eigSpace_neg_one_one h2 x v hv b hb, add_zero]

theorem nondeg_eigSpace_one (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (x : SUid σ n)
    (hI : suMat x * suMat x = 1) : Nondeg σ (eigSpace (suMat x) 1) := by
  intro v hv hv'
  refine eq_zero_of_herm σ fun u => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Submodule.mem_sup.mp ((isCompl_eigSpace h2 hI).sup_eq_top ▸ Submodule.mem_top : u ∈ _ ⊔ _)
  rw [herm_add_right, hv' b hb,
    herm_eq_zero_comm σ hσ.invol (orth_eigSpace_neg_one_one h2 x a ha v hv), zero_add]

theorem perp_eigSpace_neg_one (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (x : SUid σ n)
    (hI : suMat x * suMat x = 1) :
    perp σ (eigSpace (suMat x) (-1)) = eigSpace (suMat x) 1 := by
  apply le_antisymm
  · intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.mp ((isCompl_eigSpace h2 hI).sup_eq_top ▸ Submodule.mem_top : w ∈ _ ⊔ _)
    have ha0 : a = 0 := nondeg_eigSpace_neg_one h2 x hI a ha fun t ht => by
      have h1 : herm σ (a + b) t = 0 := hw t ht
      have h2' : herm σ b t = 0 :=
        herm_eq_zero_comm σ hσ.invol (orth_eigSpace_neg_one_one h2 x t ht b hb)
      rwa [herm_add_left, h2', add_zero] at h1
    rw [ha0, zero_add]
    exact hb
  · intro w hw t ht
    exact herm_eq_zero_comm σ hσ.invol (orth_eigSpace_neg_one_one h2 x t ht w hw)

theorem perp_eigSpace_one (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (x : SUid σ n)
    (hI : suMat x * suMat x = 1) :
    perp σ (eigSpace (suMat x) 1) = eigSpace (suMat x) (-1) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.mp ((isCompl_eigSpace h2 hI).sup_eq_top ▸ Submodule.mem_top : w ∈ _ ⊔ _)
    have hb0 : b = 0 := nondeg_eigSpace_one hσ h2 x hI b hb fun t ht => by
      have h1 : herm σ (a + b) t = 0 := hw t ht
      have h2' : herm σ a t = 0 := orth_eigSpace_neg_one_one h2 x a ha t ht
      rwa [herm_add_left, h2', zero_add] at h1
    rw [hb0, add_zero]
    exact ha
  · intro w hw t ht
    exact orth_eigSpace_neg_one_one h2 x w hw t ht

theorem smul_mem_eigSpace_neg_one_of_fix (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)
    {i : SUid σ n} (hI : suMat i * suMat i = 1) {x : SUid σ n}
    (hx : ∀ w ∈ eigSpace (suMat i) 1, x • w = w) {v : Fin n → K}
    (hv : v ∈ eigSpace (suMat i) (-1)) : x • v ∈ eigSpace (suMat i) (-1) := by
  rw [← perp_eigSpace_one hσ h2 i hI]
  intro w hw
  rw [← hx w hw, herm_smul_smul]
  exact orth_eigSpace_neg_one_one h2 i v hv w hw

theorem commute_and_fix_iff_fix (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) {i : SUid σ n}
    (hI : suMat i * suMat i = 1) {x : SUid σ n} :
    (suMat x * suMat i = suMat i * suMat x ∧ suMat x * (1 + suMat i) = 1 + suMat i) ↔
      ∀ w ∈ eigSpace (suMat i) 1, x • w = w := by
  rw [commute_and_fix_iff_vec h2 hI]
  constructor
  · rintro ⟨hw, -⟩ w hw'
    exact hw w hw'
  · intro hw
    exact ⟨fun w hw' => hw w hw', fun v hv => smul_mem_eigSpace_neg_one_of_fix hσ h2 hI hw hv⟩

theorem nondeg_herm_top : Nondeg σ (⊤ : Submodule K (Fin n → K)) := fun _ _ hs =>
  eq_zero_of_herm σ fun y => hs y trivial

theorem finrank_add_finrank_herm_perp (hσ : IsUnitaryInvolution σ) {V : Submodule K (Fin n → K)}
    (hV : Nondeg σ V) : finrank K V + finrank K (perp σ V) = n := by
  have h := finrank_eq_add_finrank_inf_perp hσ hV (le_top : V ≤ ⊤)
  rw [top_inf_eq, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem nondeg_herm_perp (hσ : IsUnitaryInvolution σ) {V : Submodule K (Fin n → K)}
    (hV : Nondeg σ V) : Nondeg σ (perp σ V) := by
  have := Nondeg.inf_perp hσ nondeg_herm_top hV (le_top : V ≤ ⊤)
  rwa [top_inf_eq] at this

end Involution

section LongRoot

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem mem_longRootGroupSU_iff_fix (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {i : Su K p f n} (hI : suMat i * suMat i = 1) {x : Su K p f n} :
    x ∈ longRootGroupSU K p f (suMat i) ↔ ∀ w ∈ eigSpace (suMat i) 1, x • w = w :=
  commute_and_fix_iff_fix (isUnitaryInvolution_unitaryInvolution hK)
    (two_ne_zero_of_charP_ne_two hp) hI

theorem IsLongRootSU2.mem_iff_fix (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i)
    {x : Su K p f n} : x ∈ L ↔ ∀ w ∈ fixSpaceSU i, x • w = w := by
  rw [h.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp)]
  exact mem_longRootGroupSU_iff_fix hK hp h.coe_mul_self

theorem IsLongRootSU2.isCompl (hp : p ≠ 2) {hn : 2 ≤ n} {L : Subgroup (Su K p f n)}
    {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) : IsCompl (minusSpaceSU i) (fixSpaceSU i) :=
  isCompl_eigSpace (two_ne_zero_of_charP_ne_two hp) h.coe_mul_self

theorem IsLongRootSU2.perp_minusSpaceSU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    perp (unitaryInvolution K p f) (minusSpaceSU i) = fixSpaceSU i :=
  perp_eigSpace_neg_one (isUnitaryInvolution_unitaryInvolution hK)
    (two_ne_zero_of_charP_ne_two hp) i h.coe_mul_self

theorem IsLongRootSU2.nondeg_minusSpaceSU (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    Nondeg (unitaryInvolution K p f) (minusSpaceSU i) :=
  nondeg_eigSpace_neg_one (two_ne_zero_of_charP_ne_two hp) i h.coe_mul_self

theorem orth_minusSpaceSU_of_le_fixSpaceSU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} {L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₂ : IsLongRootSU2 K p f hn L₂ i₂) (hle : minusSpaceSU i₁ ≤ fixSpaceSU i₂) :
    Orth (unitaryInvolution K p f) (minusSpaceSU i₁) (minusSpaceSU i₂) := by
  intro u hu v hv
  have : u ∈ perp (unitaryInvolution K p f) (minusSpaceSU i₂) := by
    rw [h₂.perp_minusSpaceSU hK hp]
    exact hle hu
  exact this v hv

theorem IsLongRootSU2.exists_nondeg (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    ∃ V : Submodule K (Fin n → K), Nondeg (unitaryInvolution K p f) V ∧ finrank K V = 2 ∧
      ∀ x : Su K p f n, x ∈ L ↔ ∀ w ∈ perp (unitaryInvolution K p f) V, x • w = w :=
  ⟨minusSpaceSU i, h.nondeg_minusSpaceSU hp,
    h.finrank_minusSpaceSU (two_ne_zero_of_charP_ne_two hp),
    fun _ => by rw [h.perp_minusSpaceSU hK hp]; exact h.mem_iff_fix hK hp⟩

theorem IsLongRootSU2.exists_isCompl (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    ∃ V W : Submodule K (Fin n → K), IsCompl V W ∧ Orth (unitaryInvolution K p f) V W ∧
      Nondeg (unitaryInvolution K p f) V ∧ Nondeg (unitaryInvolution K p f) W ∧
      finrank K V = 2 ∧ ∀ x : Su K p f n,
        x ∈ L ↔ (∀ w ∈ W, x • w = w) ∧ ∀ v ∈ V, x • v ∈ V := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  refine ⟨minusSpaceSU i, fixSpaceSU i, h.isCompl hp, orth_eigSpace_neg_one_one h2 i,
    h.nondeg_minusSpaceSU hp, nondeg_eigSpace_one hσ h2 i h.coe_mul_self,
    h.finrank_minusSpaceSU h2, fun x => ?_⟩
  rw [h.eq_longRootGroupSU h2, mem_longRootGroupSU, commute_and_fix_iff_vec h2 h.coe_mul_self]
  rfl

theorem exists_isLongRootSU2_of_nondeg (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hn : 2 ≤ n) {V : Submodule K (Fin n → K)} (hV : Nondeg (unitaryInvolution K p f) V)
    (hV2 : finrank K V = 2) {L : Subgroup (Su K p f n)}
    (hL : ∀ x : Su K p f n, x ∈ L ↔ ∀ w ∈ perp (unitaryInvolution K p f) V, x • w = w) :
    ∃ i : Su K p f n, IsLongRootSU2 K p f hn L i := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hVp : Nondeg (unitaryInvolution K p f) (perp (unitaryInvolution K p f) V) :=
    nondeg_herm_perp hσ hV
  have hdim : finrank K (perp (unitaryInvolution K p f) V) = n - 2 := by
    have := finrank_add_finrank_herm_perp hσ hV
    omega
  let E : Bool → Submodule K (Fin n → K) := fun b => cond b (perp (unitaryInvolution K p f) V) V
  let ε : Fin n → Bool := fun j => decide (2 ≤ j.val)
  have hnd : ∀ b, Nondeg (unitaryInvolution K p f) (E b) := fun b => by
    cases b
    · exact hV
    · exact hVp
  have horth : ∀ s t, s ≠ t → Orth (unitaryInvolution K p f) (E s) (E t) := by
    intro s t hst u hu v hv
    cases s <;> cases t
    · exact absurd rfl hst
    · exact herm_eq_zero_comm _ hσ.invol (hv u hu)
    · exact hu v hv
    · exact absurd rfl hst
  have hε : ∀ b, Nat.card {j // ε j = b} = finrank K (E b) := by
    intro b
    cases b
    · change _ = finrank K V
      rw [hV2, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => j.val < 2)
        (fun j => by simp only [ε, decide_eq_false_iff_not, not_le]))]
      exact card_fin_val_lt hn
    · change _ = finrank K (perp (unitaryInvolution K p f) V)
      rw [hdim, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => 2 ≤ j.val)
        (fun j => by simp only [ε, decide_eq_true_eq]))]
      exact card_fin_val_ge hn
  obtain ⟨g, hg⟩ := exists_su_adapted hσ (by omega) E hnd horth ε hε
  set i : Su K p f n := g * rootInvSU K p f hn * g⁻¹ with hidef
  have hi : IsLongRootSU2 K p f hn ((rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom) i :=
    ⟨g, rfl, rfl⟩
  have hle : minusSpaceSU i ≤ V := by
    have e : suMat i = suMat g * negBlock K n 0 * suMat g⁻¹ := by
      simp only [hidef, suMat_mul, suMat_rootInvSU]
    rw [minusSpaceSU, e, eigSpace_conj_aux (suMat_mul_suMat_inv g) (suMat_inv_mul_suMat g)]
    rintro _ ⟨u, hu, rfl⟩
    rw [Matrix.toLin'_apply]
    refine mulVec_mem_of_columns fun a ha => ?_
    have hlt : a.val < 2 := by
      by_contra hcon
      exact ha ((mem_eigSpace_negBlock_neg_one_iff h2 0).mp hu a (by omega))
    have hcol : (fun b => suMat g b a) ∈ E (ε a) := by
      have := hg a
      rwa [suMat_smul, Matrix.mulVec_single_one] at this
    have hεa : ε a = false := by simp [ε, show ¬ 2 ≤ a.val by omega]
    rw [hεa] at hcol
    exact hcol
  have hmin : minusSpaceSU i = V :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hi.finrank_minusSpaceSU h2, hV2])
  refine ⟨i, ?_⟩
  have hLeq : L = (rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [hL, hi.mem_iff_fix hK hp, ← hmin, hi.perp_minusSpaceSU hK hp]
  rw [hLeq]
  exact ⟨g, rfl, rfl⟩

theorem exists_isLongRootSU2_iff (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    (L : Subgroup (Su K p f n)) :
    (∃ i : Su K p f n, IsLongRootSU2 K p f hn L i) ↔
      ∃ V : Submodule K (Fin n → K), Nondeg (unitaryInvolution K p f) V ∧ finrank K V = 2 ∧
        ∀ x : Su K p f n, x ∈ L ↔ ∀ w ∈ perp (unitaryInvolution K p f) V, x • w = w := by
  constructor
  · rintro ⟨i, h⟩
    exact h.exists_nondeg hK hp
  · rintro ⟨V, hV, hV2, hL⟩
    exact exists_isLongRootSU2_of_nondeg hK hp hn hV hV2 hL

theorem exists_isLongRootSU2_iff_fixingSubgroup (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hn : 2 ≤ n) (L : Subgroup (Su K p f n)) :
    (∃ i : Su K p f n, IsLongRootSU2 K p f hn L i) ↔
      ∃ V : Submodule K (Fin n → K), Nondeg (unitaryInvolution K p f) V ∧ finrank K V = 2 ∧
        L = fixingSubgroup (Su K p f n) (perp (unitaryInvolution K p f) V : Set (Fin n → K)) := by
  rw [exists_isLongRootSU2_iff hK hp hn L]
  refine exists_congr fun V => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [Subgroup.ext_iff]
  refine forall_congr' fun x => ?_
  rw [mem_fixingSubgroup_iff]
  rfl

theorem isLongRootSU2_range_blockEmb (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {j : ℕ}
    (hj : j + 2 ≤ n) :
    IsLongRootSU2 K p f (by omega : 2 ≤ n) (blockEmb K p f n 2 j hj).range
      (blockEmb K p f n 2 j hj (negOneSU K p f)) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  set i₀ : Su K p f n := blockEmb K p f n 2 j hj (negOneSU K p f) with hi₀
  have hI : suMat i₀ * suMat i₀ = 1 := by
    rw [← suMat_mul, hi₀, ← map_mul, negOneSU_mul_self, map_one, suMat_one]
  have hmat : suMat i₀ = negBlock K n j := by
    rw [hi₀, suMat_blockEmb, suMat_negOneSU]
    rfl
  obtain ⟨i, hi⟩ := exists_isLongRootSU2_of_nondeg hK hp (by omega : 2 ≤ n)
    (V := eigSpace (suMat i₀) (-1)) (nondeg_eigSpace_neg_one h2 i₀ hI)
    (by rw [hmat]; exact finrank_eigSpace_negBlock h2 hj)
    (L := (blockEmb K p f n 2 j hj).range) fun x => by
      rw [perp_eigSpace_neg_one hσ h2 i₀ hI, range_blockEmb_eq_longRootGroupSU h2 hj, ← hmat]
      exact mem_longRootGroupSU_iff_fix hK hp hI
  have hmem : i₀ ∈ (blockEmb K p f n 2 j hj).range := ⟨negOneSU K p f, rfl⟩
  have hord : orderOf i₀ = 2 := by
    rw [hi₀, orderOf_injective (blockEmb K p f n 2 j hj) (blockEmb_injective _)]
    exact orderOf_negOneSU h2
  rw [hi.eq_of_orderOf_eq_two hK hp hmem hord]
  exact hi

theorem isLongRootSU2_standardU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {n : ℕ}
    (hn : 1 ≤ n) (i : Fin n) :
    IsLongRootSU2 K p f (by omega : 2 ≤ n + 1) (standardU K p f n i)
      (blockEmb2 K p f n i (negOneSU K p f)) :=
  isLongRootSU2_range_blockEmb hK hp (j := i) (by have := i.isLt; omega)

end LongRoot

end CFSG.ClassicalInvolution.Models
