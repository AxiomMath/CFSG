module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4SecG
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSpGen
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSLGen
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSp
public import CFSG.ClassicalInvolution.ModelFacts.TG3F3
public import CFSG.GH74.GLS.LU.StdPairLin
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (minusSpace fixSpace mem_minusSpace
  mem_fixSpace mat_transpose_mul_gram_mul)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.RankThree.Classical (spForm spEnd spForm_mulVec spForm_nondegenerate)
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1

section Transfer

variable {G₀ X : Type} [Group G₀] [Group X]

theorem centralizer_sup_eq_top_of_cover
    (hcen : ∀ c ∈ Subgroup.center G₀, ∀ c' ∈ Subgroup.center G₀, c ≠ 1 → c' ≠ 1 → c = c')
    (hgen : ∀ i J : G₀, i * i = 1 → i ∉ Subgroup.center G₀ → J * J ∈ Subgroup.center G₀ →
      J * J ≠ 1 → i * J = J * i →
        Subgroup.centralizer ({i} : Set G₀) ⊔ Subgroup.centralizer ({J} : Set G₀) = ⊤)
    (ψ : G₀ →* X) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G₀)
    (hlift : ∀ c ∈ Subgroup.center X, ∃ f ∈ Subgroup.center G₀, ψ f = c) {u w : X}
    (hu : u * u = 1) (hwZ : w * w ∈ Subgroup.center X) (hw1 : w * w ≠ 1) (huw : u * w = w * u) :
    Subgroup.centralizer ({u} : Set X) ⊔ Subgroup.centralizer ({w} : Set X) ⊔
      Subgroup.centralizer ({u * w} : Set X) = ⊤ := by
  obtain ⟨f, hfZ, hfw⟩ := hlift _ hwZ
  have hf1 : f ≠ 1 := fun h => hw1 (by rw [← hfw, h, map_one])
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    by_contra hk1
    apply hw1
    rw [← hfw, ← hcen k (hker hk) f hfZ hk1 hf1]
    exact MonoidHom.mem_ker.mp hk
  obtain ⟨i, rfl⟩ := hψ u
  obtain ⟨J, rfl⟩ := hψ w
  have hi : i * i = 1 := hinj (by rw [map_mul, hu, map_one])
  have hJ : J * J = f := hinj (by rw [map_mul, hfw])
  have hiJ : i * J = J * i := hinj (by rw [map_mul, map_mul, huw])
  have hmap : ∀ g : G₀, (Subgroup.centralizer ({g} : Set G₀)).map ψ ≤
      Subgroup.centralizer ({ψ g} : Set X) := by
    intro g
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [← map_mul, hx, map_mul]
  by_cases hiZ : i ∈ Subgroup.center G₀
  · have htop : Subgroup.centralizer ({ψ i} : Set X) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨g, rfl⟩ := hψ x
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp hiZ g]
    rw [htop, top_sup_eq, top_sup_eq]
  · have h := hgen i J hi hiZ (by rw [hJ]; exact hfZ) (by rw [hJ]; exact hf1) hiJ
    have h2 : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({ψ i} : Set X) ⊔
        Subgroup.centralizer ({ψ J} : Set X) := by
      rw [← MonoidHom.range_eq_top.mpr hψ, MonoidHom.range_eq_map, ← h, Subgroup.map_sup]
      exact sup_le_sup (hmap i) (hmap J)
    exact eq_top_iff.mpr (h2.trans le_sup_left)

end Transfer

section Sp

variable {K : Type} [Field K] {n : ℕ}

theorem spForm_minusSpace_fixSpace_eq_zero (h2 : (2 : K) ≠ 0) {i : StatedSp n K}
    {a b : Fin n ⊕ Fin n → K} (ha : a ∈ minusSpace i) (hb : b ∈ fixSpace i) :
    spForm n K a b = 0 := by
  have h := spForm_mulVec (mat n K i) a b
  rw [mat_transpose_mul_gram_mul, mem_minusSpace.mp ha, mem_fixSpace.mp hb] at h
  have h' : spForm n K (-a) b = spForm n K a b := h
  rw [map_neg, LinearMap.neg_apply] at h'
  have h3 : (2 : K) * spForm n K a b = 0 := by linear_combination -h'
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem eq_zero_of_mem_minusSpace_of_orth (h2 : (2 : K) ≠ 0) {i : StatedSp n K}
    (hi : i * i = 1) {a : Fin n ⊕ Fin n → K} (ha : a ∈ minusSpace i)
    (h0 : ∀ u ∈ minusSpace i, spForm n K a u = 0) : a = 0 := by
  refine (spForm_nondegenerate (r := n) (K := K)).1 a fun v => ?_
  have hv : v ∈ minusSpace i ⊔ fixSpace i := by
    rw [(ModelFacts.TG3.isCompl_minusSpace_fixSpace h2 hi).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, h0 v₁ hv₁, spForm_minusSpace_fixSpace_eq_zero h2 ha hv₂, add_zero]

theorem eq_zero_of_mem_fixSpace_of_orth (h2 : (2 : K) ≠ 0) {i : StatedSp n K}
    (hi : i * i = 1) {b : Fin n ⊕ Fin n → K} (hb : b ∈ fixSpace i)
    (h0 : ∀ u ∈ fixSpace i, spForm n K b u = 0) : b = 0 := by
  refine (spForm_nondegenerate (r := n) (K := K)).1 b fun v => ?_
  have hv : v ∈ minusSpace i ⊔ fixSpace i := by
    rw [(ModelFacts.TG3.isCompl_minusSpace_fixSpace h2 hi).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, ModelFacts.TG3.form_comm_zero (spForm_minusSpace_fixSpace_eq_zero h2 hv₁ hb),
    h0 v₂ hv₂, add_zero]

theorem finrank_ne_one_of_orth {P : Submodule K (Fin n ⊕ Fin n → K)}
    (hnd : ∀ a ∈ P, (∀ u ∈ P, spForm n K a u = 0) → a = 0) : Module.finrank K P ≠ 1 := by
  intro h
  obtain ⟨⟨a, ha⟩, ha0, hspan⟩ := finrank_eq_one_iff'.mp h
  apply ha0
  refine (Submodule.mk_eq_zero P ha).mpr (hnd a ha fun u hu => ?_)
  obtain ⟨c, hc⟩ := hspan ⟨u, hu⟩
  have hu' : u = c • a := (congrArg Subtype.val hc).symm
  rw [hu', map_smul, smul_eq_mul, ModelFacts.TG3.form_self_zero, mul_zero]

theorem finrank_minusSpace_fixSpace_eq_two (h2 : (2 : K) ≠ 0) {i : StatedSp 2 K}
    (hi : i * i = 1) (hiZ : i ∉ Subgroup.center (StatedSp 2 K)) :
    Module.finrank K (minusSpace i) = 2 ∧ Module.finrank K (fixSpace i) = 2 := by
  have hc := ModelFacts.TG3.isCompl_minusSpace_fixSpace h2 hi
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hsum
  have h1 := finrank_ne_one_of_orth fun a ha h0 => eq_zero_of_mem_minusSpace_of_orth h2 hi ha h0
  have h1' := finrank_ne_one_of_orth fun b hb h0 => eq_zero_of_mem_fixSpace_of_orth h2 hi hb h0
  have h0 : Module.finrank K (minusSpace i) ≠ 0 := by
    intro h
    apply hiZ
    have hsup := hc.sup_eq_top
    rw [Submodule.finrank_eq_zero.mp h, bot_sup_eq] at hsup
    have hi1 : i = 1 := mat_injective (Matrix.ext_iff_mulVec.mpr fun v => by
      rw [map_one, Matrix.one_mulVec]
      exact mem_fixSpace.mp (by rw [hsup]; exact Submodule.mem_top))
    rw [hi1]
    exact Subgroup.one_mem _
  have h0' : Module.finrank K (fixSpace i) ≠ 0 := by
    intro h
    apply hiZ
    have hsup := hc.sup_eq_top
    rw [Submodule.finrank_eq_zero.mp h, sup_bot_eq] at hsup
    have hneg : mat 2 K i = -1 := Matrix.ext_iff_mulVec.mpr fun v => by
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
      exact mem_minusSpace.mp (by rw [hsup]; exact Submodule.mem_top)
    rw [Subgroup.mem_center_iff]
    intro g
    apply mat_injective
    rw [map_mul, map_mul, hneg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]
  omega

theorem sp4_eq_of_mem_center {c c' : StatedSp 2 K} (hc : c ∈ Subgroup.center (StatedSp 2 K))
    (hc' : c' ∈ Subgroup.center (StatedSp 2 K)) (h1 : c ≠ 1) (h1' : c' ≠ 1) : c = c' := by
  apply mat_injective
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [Asc77.mulVec_eq_neg_of_mem_center (by norm_num) hc h1
      (Models.SymplecticPairs.mul_self_eq_one_of_mem_center (by norm_num) hc) v,
    Asc77.mulVec_eq_neg_of_mem_center (by norm_num) hc' h1'
      (Models.SymplecticPairs.mul_self_eq_one_of_mem_center (by norm_num) hc') v]

theorem sp4_centralizer_sup_eq_top {i J : StatedSp 2 𝔽₃} (hi : i * i = 1)
    (hiZ : i ∉ Subgroup.center (StatedSp 2 𝔽₃)) (hJZ : J * J ∈ Subgroup.center (StatedSp 2 𝔽₃))
    (hJ1 : J * J ≠ 1) (hiJ : i * J = J * i) :
    Subgroup.centralizer ({i} : Set (StatedSp 2 𝔽₃)) ⊔
      Subgroup.centralizer ({J} : Set (StatedSp 2 𝔽₃)) = ⊤ := by
  have h2 := ModelFacts.TG3.two_ne_zero_three
  obtain ⟨hd₁, hd₂⟩ := finrank_minusSpace_fixSpace_eq_two h2 hi hiZ
  have hJ : ∀ v, spEnd J (spEnd J v) = -v := fun v => by
    show mat 2 𝔽₃ J *ᵥ (mat 2 𝔽₃ J *ᵥ v) = -v
    rw [Matrix.mulVec_mulVec, ← map_mul]
    exact Asc77.mulVec_eq_neg_of_mem_center (by norm_num) hJZ hJ1
      (Models.SymplecticPairs.mul_self_eq_one_of_mem_center (by norm_num) hJZ) v
  exact ModelFacts.TG3.sp_gen h2 ModelFacts.TG3.mul_self_ne_neg_one_three
    ModelFacts.TG3.exists_sq_add_sq_three i J hi hiJ hJ (minusSpace i) (fixSpace i)
    (fun v => by rw [mem_minusSpace]; rfl) (fun v => by rw [mem_fixSpace]; rfl) hd₁ hd₂
    (fun a ha h0 => eq_zero_of_mem_minusSpace_of_orth h2 hi ha h0)
    (fun b hb h0 => eq_zero_of_mem_fixSpace_of_orth h2 hi hb h0)

end Sp

section SL

theorem eq_one_or_coe_eq_neg_one_sl4 {c : SL(4, 𝔽₃)} (hc : c ∈ Subgroup.center SL(4, 𝔽₃)) :
    c = 1 ∨ (c : Matrix (Fin 4) (Fin 4) 𝔽₃) = -1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rcases ModelFacts.TG3.eq_zero_or_one_or_neg_one_three r with h | h | h
  · rw [h] at hr
    simp at hr
  · left
    apply Subtype.ext
    rw [← hrc, h, map_one, Matrix.SpecialLinearGroup.coe_one]
  · right
    rw [← hrc, h, map_neg, map_one]

theorem sl4_eq_of_mem_center {c c' : SL(4, 𝔽₃)} (hc : c ∈ Subgroup.center SL(4, 𝔽₃))
    (hc' : c' ∈ Subgroup.center SL(4, 𝔽₃)) (h1 : c ≠ 1) (h1' : c' ≠ 1) : c = c' :=
  Subtype.ext (((eq_one_or_coe_eq_neg_one_sl4 hc).resolve_left h1).trans
    ((eq_one_or_coe_eq_neg_one_sl4 hc').resolve_left h1').symm)

variable {K : Type} [Field K]

theorem finrank_eigSpace_neg_one_sl4 (h2 : (2 : K) ≠ 0) {i : SL(4, K)} (hi : i * i = 1)
    (hiZ : i ∉ Subgroup.center SL(4, K)) :
    Module.finrank K (Models.eigSpace (i : Matrix (Fin 4) (Fin 4) K) (-1)) = 2 := by
  have hI : (i : Matrix (Fin 4) (Fin 4) K) * i = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hi, Matrix.SpecialLinearGroup.coe_one]
  have hdet := CFSG.GH74.GLS.LU.det_eq_neg_one_pow_finrank_eigSpace h2 hI
  rw [i.2] at hdet
  have hc := Models.isCompl_eigSpace h2 hI
  have hle : Module.finrank K (Models.eigSpace (i : Matrix (Fin 4) (Fin 4) K) (-1)) ≤ 4 :=
    (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  generalize hd : Module.finrank K (Models.eigSpace (i : Matrix (Fin 4) (Fin 4) K) (-1)) = d
    at hdet hle
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [pow_one] at hdet
    exact hneg hdet.symm
  have hd3 : d ≠ 3 := by
    rintro rfl
    rw [show (-1 : K) ^ 3 = -1 by ring] at hdet
    exact hneg hdet.symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hiZ
    have hsup := hc.sup_eq_top
    rw [Submodule.finrank_eq_zero.mp hd, bot_sup_eq] at hsup
    have hi1 : i = 1 := Subtype.ext (Matrix.ext_iff_mulVec.mpr fun v => by
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      exact Models.mem_eigSpace_one.mp (by rw [hsup]; exact Submodule.mem_top))
    rw [hi1]
    exact Subgroup.one_mem _
  have hd4 : d ≠ 4 := by
    rintro rfl
    apply hiZ
    have htop : Models.eigSpace (i : Matrix (Fin 4) (Fin 4) K) (-1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hd, Module.finrank_fin_fun])
    have hneg1 : (i : Matrix (Fin 4) (Fin 4) K) = -1 := Matrix.ext_iff_mulVec.mpr fun v => by
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
      exact Models.mem_eigSpace_neg_one.mp (by rw [htop]; exact Submodule.mem_top)
    exact Matrix.SpecialLinearGroup.mem_center_iff.mpr
      ⟨-1, by norm_num, by rw [map_neg, map_one, hneg1]⟩
  omega

theorem sl4_centralizer_sup_eq_top {i J : SL(4, 𝔽₃)} (hi : i * i = 1)
    (hiZ : i ∉ Subgroup.center SL(4, 𝔽₃)) (hJZ : J * J ∈ Subgroup.center SL(4, 𝔽₃))
    (hJ1 : J * J ≠ 1) (hiJ : i * J = J * i) :
    Subgroup.centralizer ({i} : Set SL(4, 𝔽₃)) ⊔ Subgroup.centralizer ({J} : Set SL(4, 𝔽₃)) =
      ⊤ := by
  have h2 := ModelFacts.TG3.two_ne_zero_three
  have hJ : (J : Matrix (Fin 4) (Fin 4) 𝔽₃) * J = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    exact (eq_one_or_coe_eq_neg_one_sl4 hJZ).resolve_left hJ1
  exact ModelFacts.TG3.sl4_gen ModelFacts.TG3.eq_zero_or_one_or_neg_one_three
    ModelFacts.TG3.mul_self_ne_neg_one_three h2 i J hi hiJ hJ
    (finrank_eigSpace_neg_one_sl4 h2 hi hiZ)

end SL

section Cit3


theorem e4CoverGen_proved : E4CoverGen := by
  intro X _ _ hX u w hu hwZ hw1 huw
  rcases hX with ⟨ψ, hψ, hker, hlift⟩ | ⟨ψ, hψ, hker, hlift⟩
  · exact centralizer_sup_eq_top_of_cover (G₀ := StatedSp 2 𝔽₃)
      (fun _ hc _ hc' h1 h1' => sp4_eq_of_mem_center hc hc' h1 h1')
      (fun _ _ hi hiZ hJZ hJ1 hiJ => sp4_centralizer_sup_eq_top hi hiZ hJZ hJ1 hiJ)
      ψ hψ hker hlift hu hwZ hw1 huw
  · exact centralizer_sup_eq_top_of_cover (G₀ := SL(4, 𝔽₃))
      (fun _ hc _ hc' h1 h1' => sl4_eq_of_mem_center hc hc' h1 h1')
      (fun _ _ hi hiZ hJZ hJ1 hiJ => sl4_centralizer_sup_eq_top hi hiZ hJZ hJ1 hiJ)
      ψ hψ hker hlift hu hwZ hw1 huw

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
