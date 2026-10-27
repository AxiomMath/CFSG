module

public import CFSG.ClassicalInvolution.Asc77.AscT7MV
public import CFSG.ClassicalInvolution.Asc77.AscT7MR
public import CFSG.ClassicalInvolution.Asc77.AscT7MT
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuSlayer

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4 CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.Dichotomy
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suMat_zneg_mul_zA :
    suMat (InnerSu.zneg K p f * zA K p f) =
      !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] := by
  rw [suMat_mul, InnerSu.suMat_zneg, suMat_zA]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem mk_zneg_mul (g : Su K p f 4) :
    (QuotientGroup.mk (InnerSu.zneg K p f * g) : PU K p f) = QuotientGroup.mk g := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr InnerSu.zneg_mem_center, one_mul]

theorem mk_zA_mem_layU_zero :
    (QuotientGroup.mk (zA K p f) : PU K p f) ∈ layU K p f 0 (by norm_num) := by
  obtain ⟨A, hA⟩ := exists_blockEmb_of_entries (j := 3) (i := 0) (by norm_num) hj_zero
    (InnerSu.zneg K p f * zA K p f) (by
      intro a b hab
      rw [suMat_zneg_mul_zA]
      fin_cases a <;> fin_cases b <;> simp_all)
  refine ⟨_, ⟨A, rfl⟩, ?_⟩
  show (QuotientGroup.mk (blockEmb K p f 4 3 0 (by norm_num) A) : PU K p f) = _
  rw [hA, mk_zneg_mul]

theorem mk_zA_mem_layU_one :
    (QuotientGroup.mk (zA K p f) : PU K p f) ∈ layU K p f 1 (by norm_num) := by
  obtain ⟨A, hA⟩ := exists_blockEmb_of_entries (j := 0) (i := 1) (by norm_num) hj_one
    (InnerSu.zneg K p f * zA K p f) (by
      intro a b hab
      rw [suMat_zneg_mul_zA]
      fin_cases a <;> fin_cases b <;> simp_all)
  refine ⟨_, ⟨A, rfl⟩, ?_⟩
  show (QuotientGroup.mk (blockEmb K p f 4 3 1 (by norm_num) A) : PU K p f) = _
  rw [hA, mk_zneg_mul]

theorem actsAsM_one : ActsAsM (1 : MulAut (PU K p f)) 1 1 :=
  ⟨Matrix.mul_one _, Matrix.mul_one _, fun h => ⟨h, rfl, by simp⟩⟩

theorem ActsAsM.eq_of_eq {φ ψ : MulAut (PU K p f)} {M Mi : Matrix (Fin 4) (Fin 4) K}
    (hφ : ActsAsM φ M Mi) (hψ : ActsAsM ψ M Mi) : φ = ψ := by
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨h₁, hh₁, hm₁⟩ := hφ.2.2 h
  obtain ⟨h₂, hh₂, hm₂⟩ := hψ.2.2 h
  have : h₁ = h₂ := suMat_injective (by rw [hm₁, hm₂])
  rw [hh₁, hh₂, this]

theorem actsAsD_mul_self {φ : MulAut (PU K p f)} {j : Fin 4} (h : ActsAsD K p f φ j) :
    φ * φ = 1 := by
  rw [actsAsD_iff] at h
  have h1 := h.mul h
  rw [dMat_mul_self] at h1
  exact h1.eq_of_eq actsAsM_one

section Diag

variable {X : Type} [Group X] [Finite X] {θ : X →* MulAut (PU K p f)} {ι : PU K p f →* X}

theorem layerData_zU (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) (hq : 5 ≤ p ^ f)
    (hι : ∀ x, θ (ι x) = MulAut.conj x) :
    LayerData ι.range ⊥ (ι (QuotientGroup.mk (zA K p f)))
      ((((InnerSu.R0 K p f ⊔ InnerSu.R0' K p f).map (MulAut.conj (sU K p f)).toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center (Su K p f 4)))).map ι) := by
  set e : Su K p f 4 →* X := ι.comp (QuotientGroup.mk' (Subgroup.center (Su K p f 4))) with he
  have hι' := ι_injective hι (centre_trivial_PU hK hq)
  have hker : e.ker ≤ Subgroup.center (Su K p f 4) := by
    intro s hs
    have h1 : ι (QuotientGroup.mk s) = 1 := hs
    have h2' : (QuotientGroup.mk s : PU K p f) = 1 := hι' (h1.trans (map_one ι).symm)
    exact (QuotientGroup.eq_one_iff s).mp h2'
  have hSL : SLayer (zA K p f) ((InnerSu.R0 K p f ⊔ InnerSu.R0' K p f).map
      (MulAut.conj (sU K p f)).toMonoidHom) :=
    (InnerSu.slayer_x0 hK h2 hq).map (MulAut.conj (sU K p f))
  have h := SLayer.layerData hSL e hker ⊥ bot_le
  have hrange : e.range = ι.range := by
    rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  have hmap : ((InnerSu.R0 K p f ⊔ InnerSu.R0' K p f).map
      (MulAut.conj (sU K p f)).toMonoidHom).map e = ((((InnerSu.R0 K p f ⊔
        InnerSu.R0' K p f).map (MulAut.conj (sU K p f)).toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center (Su K p f 4)))).map ι) := by
    simp only [he, Subgroup.map_map]
    rfl
  rw [hrange, hmap] at h
  exact h

theorem sU_conj_diag (a b : K) :
    suMat (sU K p f) *
      (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K) *
      suMat (sU K p f)⁻¹ = !![a, 0, 0, 0; 0, b, 0, 0; 0, 0, b, 0; 0, 0, 0, a] := by
  rw [suMat_sU, suMat_sU_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem actsAsM_sU : ActsAsM (MulAut.conj (QuotientGroup.mk (sU K p f) : PU K p f))
    (suMat (sU K p f)) (suMat (sU K p f)⁻¹) := actsAsM_conj _

theorem actsAsM_sU_inv : ActsAsM (MulAut.conj (QuotientGroup.mk (sU K p f) : PU K p f))⁻¹
    (suMat (sU K p f)⁻¹) (suMat (sU K p f)) := by
  have h := actsAsM_conj (sU K p f)⁻¹
  rwa [inv_inv, QuotientGroup.mk_inv, map_inv] at h

theorem hN_U (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hθ : Function.Injective θ) (hι : ∀ x, θ (ι x) = MulAut.conj x) {y : X}
    (hy : ActsAsD K p f (θ y) 3) :
    ∀ n ∈ involutionOddCore (ι (QuotientGroup.mk (zA K p f))), n * y = y * n := by
  intro n hn
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have : ι.range.Normal := range_normal hθ hι
  have hLz := layerData_zU hK h2 hq hι
  have hι' := ι_injective hι (centre_trivial_PU hK hq)
  set c : MulAut (PU K p f) := MulAut.conj (QuotientGroup.mk (sU K p f)) with hc
  have hcp : ∀ s' : Su K p f 4, c (QuotientGroup.mk s') =
      QuotientGroup.mk (sU K p f * s' * (sU K p f)⁻¹) := fun s' => by
    rw [hc, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hfixQ : ∀ r ∈ InnerSu.R0 K p f ⊔ InnerSu.R0' K p f,
      θ n (QuotientGroup.mk (sU K p f * r * (sU K p f)⁻¹)) =
        QuotientGroup.mk (sU K p f * r * (sU K p f)⁻¹) := by
    intro r hr
    have hmem : ι (QuotientGroup.mk (sU K p f * r * (sU K p f)⁻¹)) ∈ (((InnerSu.R0 K p f ⊔
        InnerSu.R0' K p f).map (MulAut.conj (sU K p f)).toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center (Su K p f 4)))).map ι :=
      Subgroup.mem_map_of_mem ι (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hr))
    have := hLz.commutes_of_oddCore hn hmem
    exact (ι_commute_iff hθ hι hι' n _).mp this
  have hfixb : ∀ b : Su K p f 4, b ∈ InnerSu.R0 K p f ⊔ InnerSu.R0' K p f →
      (c⁻¹ * θ n * c) (QuotientGroup.mk b) = QuotientGroup.mk b := by
    intro b hb
    show c⁻¹ (θ n (c (QuotientGroup.mk b))) = _
    rw [hcp, hfixQ b hb, ← hcp]
    simp
  have hfix0 : ∀ A : Su K p f 2,
      (c⁻¹ * θ n * c) (QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) A)) =
        QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) A) := fun A =>
    hfixb _ (Subgroup.mem_sup_left ⟨A, rfl⟩)
  have hfix2 : ∀ A : Su K p f 2,
      (c⁻¹ * θ n * c) (QuotientGroup.mk (blockEmb K p f 4 2 2 (by norm_num) A)) =
        QuotientGroup.mk (blockEmb K p f 4 2 2 (by norm_num) A) := fun A =>
    hfixb _ (Subgroup.mem_sup_right ⟨A, rfl⟩)
  have hodd : Odd (orderOf n) :=
    Odd.of_dvd_nat (odd_natCard_involutionOddCore _) (Subgroup.orderOf_dvd_natCard _ hn)
  have hodd' : Odd (orderOf (c⁻¹ * θ n * c)) := by
    refine Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one ?_)
    have h1 := conj_pow (a := c⁻¹) (b := θ n) (i := orderOf n)
    rw [inv_inv] at h1
    rw [h1, ← map_pow, pow_orderOf_eq_one, map_one]
    group
  obtain ⟨a, b, ha, hb, -, -, hform⟩ := su4_odd_blocks hK hp hq (c⁻¹ * θ n * c) hfix0 hfix2 hodd'
  have hD : ActsAsM (c⁻¹ * θ n * c)
      (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K)
      !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] := by
    refine ⟨?_, ?_, hform⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, ha, hb]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, ha, hb]
  have hθn : θ n = c * (c⁻¹ * θ n * c) * c⁻¹ := by group
  have hM := (actsAsM_sU.mul hD).mul actsAsM_sU_inv
  rw [← hθn, sU_conj_diag] at hM
  have hyM : ActsAsM (θ y) (dMat 3) (dMat 3) := actsAsD_iff.mp hy
  have hcomm : (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, b, 0; 0, 0, 0, a] : Matrix (Fin 4) (Fin 4) K) *
      dMat 3 = dMat 3 * !![a, 0, 0, 0; 0, b, 0, 0; 0, 0, b, 0; 0, 0, 0, a] := by
    rw [dMat_three_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have := hM.comm hyM hcomm
  apply hθ
  rw [map_mul, map_mul]
  exact this

theorem d3_not_comm (h2 : (2 : K) ≠ 0) :
    ¬ ((dMat 3 : Matrix (Fin 4) (Fin 4) K) * suMat (sU K p f) = suMat (sU K p f) * dMat 3) := by
  intro h
  have := entry_zero_of_comm h (i := 1) (k := 3)
    (sgn_ne_of_eq_ne h2 (j := 3) (i := 3) (k := 1) rfl (by decide)).symm
  rw [suMat_sU] at this
  simp at this

theorem d0_not_comm (h2 : (2 : K) ≠ 0) :
    ¬ ((dMat 0 : Matrix (Fin 4) (Fin 4) K) * suMat (OuterU4.mixSU K p f) =
      suMat (OuterU4.mixSU K p f) * dMat 0) := by
  intro h
  have := entry_zero_of_comm h (i := 0) (k := 2)
    (sgn_ne_of_eq_ne h2 (j := 0) (i := 0) (k := 2) rfl (by decide))
  rw [OuterU4.suMat_mixSU] at this
  simp at this

theorem z_ne_one_U (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hι : ∀ x, θ (ι x) = MulAut.conj x) : ι (QuotientGroup.mk (zA K p f)) ≠ 1 := by
  intro h
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hι' := ι_injective hι (centre_trivial_PU hK hq)
  have h1 : (QuotientGroup.mk (zA K p f) : PU K p f) = 1 := hι' (h.trans (map_one ι).symm)
  have hz : zA K p f ∈ Subgroup.center (Su K p f 4) := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.Models.Transfer.exists_scalar_of_mem_center_su hK hq
    (by norm_num) hz
  have e1 := congrFun (congrFun hc 0) 0
  have e2 := congrFun (congrFun hc 1) 1
  rw [suMat_zA] at e1 e2
  simp at e1 e2
  apply h2
  linear_combination e2 - e1

theorem y_ne_one_U (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {y : X}
    (hy : ActsAsD K p f (θ y) 3) : y ≠ 1 := by
  intro h1
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hθ1 : θ y = 1 := by rw [h1, map_one]
  apply d3_not_comm h2
  refine comm_of_fix_U hK hq h2 (j := 3) (g := sU K p f) ?_
  have := hy (sU K p f)
  rw [hθ1] at this
  simpa using this.symm

theorem zy_ne_one_U (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hι : ∀ x, θ (ι x) = MulAut.conj x) {y : X} (hy : ActsAsD K p f (θ y) 3) :
    ι (QuotientGroup.mk (zA K p f)) * y ≠ 1 := by
  intro h1
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hzy : θ (ι (QuotientGroup.mk (zA K p f)) * y) =
      MulAut.conj (QuotientGroup.mk (zA K p f) : PU K p f) * θ y := by rw [map_mul, hι]
  have hD0 := actsAsD_zy hy
  have hθ1 : MulAut.conj (QuotientGroup.mk (zA K p f) : PU K p f) * θ y = 1 := by
    rw [← hzy, h1, map_one]
  apply d0_not_comm h2
  refine comm_of_fix_U hK hq h2 (j := 0) (g := OuterU4.mixSU K p f) ?_
  have := hD0 (OuterU4.mixSU K p f)
  rw [hθ1] at this
  simpa using this.symm

theorem alphaOf_klein_diagU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hθ : Function.Injective θ) (hι : ∀ x, θ (ι x) = MulAut.conj x) {y : X}
    (hy : ActsAsD K p f (θ y) 3) :
    alphaOf (Subgroup.closure ({ι (QuotientGroup.mk (zA K p f)), y} : Set X)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hzy : θ (ι (QuotientGroup.mk (zA K p f)) * y) =
      MulAut.conj (QuotientGroup.mk (zA K p f) : PU K p f) * θ y := by rw [map_mul, hι]
  have hD0 : ActsAsD K p f (θ (ι (QuotientGroup.mk (zA K p f)) * y)) 0 := by
    rw [hzy]
    exact actsAsD_zy hy
  refine alphaOf_klein_of_layers hθ hι (centre_trivial_PU hK hq) (y := y)
    (z := ι (QuotientGroup.mk (zA K p f))) (Q₁ := layU K p f 0 (by norm_num))
    (Q₂ := layU K p f 1 (by norm_num)) ?_ ?_ ?_ (z_ne_one_U hK hp hq hι) (y_ne_one_U hK hp hq hy)
    (zy_ne_one_U hK hp hq hι hy) (layU_fix (by norm_num) hj_zero hy)
    (fun g hg q hq' => layU_norm (by norm_num) hj_zero hK hq h2 hy g hg q hq')
    (layU_perf hK hq _) (layU_gen hK hq _) (layU_fix (by norm_num) hj_one hD0)
    (fun g hg q hq' => layU_norm (by norm_num) hj_one hK hq h2 hD0 g hg q hq')
    (layU_perf hK hq _) (layU_gen hK hq _)
    (Subgroup.mem_map_of_mem ι mk_zA_mem_layU_zero) (Subgroup.mem_map_of_mem ι mk_zA_mem_layU_one)
    (hN_U hK hp hq hθ hι hy) (layU_sup hK hq)
  · rw [← map_mul, ← QuotientGroup.mk_mul, zA_mul_self, QuotientGroup.mk_one, map_one]
  · apply hθ
    rw [map_mul, actsAsD_mul_self hy, map_one]
  · apply hθ
    rw [map_mul, map_mul, hι]
    refine ActsAsM.comm actsAsM_zA (actsAsD_iff.mp hy) ?_
    rw [suMat_zA, dMat_three_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

end Diag

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
