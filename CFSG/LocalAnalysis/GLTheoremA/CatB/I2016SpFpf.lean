module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfA6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfFix
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfFive
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open Module CFSG.Open CFSG.RankThree.Classical CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
  CFSG.LocalAnalysis.GLTheoremA.I2016

@[expose] noncomputable def spEquivHom : StatedSp 4 (ZMod 2) →* (V8 ≃ₗ[ZMod 2] V8) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V8).toMonoidHom.comp (spLin 4 (ZMod 2))

@[expose] noncomputable def spEndHom : StatedSp 4 (ZMod 2) →* Module.End (ZMod 2) V8 :=
  (Units.coeHom (Module.End (ZMod 2) V8)).comp (spLin 4 (ZMod 2))

theorem spEquivHom_apply (a : StatedSp 4 (ZMod 2)) (v : V8) : spEquivHom a v = spEnd a v := rfl

theorem spEndHom_apply (a : StatedSp 4 (ZMod 2)) : spEndHom a = spEnd a := rfl

theorem spEquivHom_eq_one_iff {a : StatedSp 4 (ZMod 2)} : spEquivHom a = 1 ↔ a = 1 := by
  rw [← spEnd_eq_one_iff]
  constructor
  · intro h
    refine LinearMap.ext fun v => ?_
    rw [← spEquivHom_apply, h]
    rfl
  · intro h
    refine LinearEquiv.ext fun v => ?_
    rw [spEquivHom_apply, h]
    rfl

theorem spForm_spEnd (a : StatedSp 4 (ZMod 2)) (u v : V8) :
    spForm 4 (ZMod 2) (spEnd a u) (spEnd a v) = spForm 4 (ZMod 2) u v :=
  CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup.mp (spLin_mem a) u v

theorem finrank_V8 : finrank (ZMod 2) V8 = 8 := by
  simp [V8, Module.finrank_fintype_fun_eq_card]

theorem spEnd_sq_add_eq_zero {g : StatedSp 4 (ZMod 2)} (hg3 : g ^ 3 = 1)
    (hfpf : ∀ v : V8, spEnd g v = v → v = 0) : spEnd g ^ 2 + spEnd g + 1 = 0 := by
  have h3 : ∀ v, spEnd g (spEnd g (spEnd g v)) = v := fun v => by
    have h : spEnd (g * (g * g)) v = v := by
      rw [show g * (g * g) = g ^ 3 by rw [pow_succ, pow_two, mul_assoc], hg3, spEnd_one]
      rfl
    simpa [spEnd_mul_apply] using h
  refine LinearMap.ext fun v => ?_
  apply hfpf
  simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, map_add,
    LinearMap.zero_apply, h3]
  abel

theorem fpfIrrGap_holds : FpfIrrGap := by
  intro g A₀ A₁ hg3 hg1 hC M hMA₁ hM6 U hUM hUg
  by_contra hU
  obtain ⟨hU0, hUtop⟩ : U ≠ ⊥ ∧ U ≠ ⊤ := not_or.mp hU
  have hA0 : A₀ = ⊥ := by
    rcases hC.fixed with h | h
    · exact h.2
    · exact absurd h.1 (by norm_num)
  have hCA : Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) = A₁ := by
    rw [hC.centralizer_eq, hA0, bot_sup_eq]
  have hfpf : ∀ v : V8, spEnd g v = v → v = 0 := fixedPointFree_of_class hg3 hg1 hC
  have hγ : spEnd g ^ 2 + spEnd g + 1 = 0 := spEnd_sq_add_eq_zero hg3 hfpf
  obtain ⟨A', S, _, f, hA'M, hcat, hf⟩ := hM6
  obtain ⟨hSsimple, h5S, y, hy⟩ := a6_data hcat
  haveI := hSsimple
  have hcomm : ∀ a : ↥A', (a : StatedSp 4 (ZMod 2)) * g = g * a := fun a =>
    Subgroup.mem_centralizer_singleton_iff.mp (hCA ▸ hMA₁ (hA'M a.2))
  have hpres : ∀ a : ↥A', ∀ u ∈ U, spEnd (a : StatedSp 4 (ZMod 2)) u ∈ U := fun a u hu =>
    hUM a (hA'M a.2) u hu
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card ↥A' := h5S.trans (Subgroup.card_dvd_of_surjective hf)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hxa5 : orderOf (x : StatedSp 4 (ZMod 2)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx5 : (x : StatedSp 4 (ZMod 2)) ^ 5 = 1 := by rw [← hxa5]; exact pow_orderOf_eq_one _
  have hx1 : (x : StatedSp 4 (ZMod 2)) ≠ 1 := fun h => by rw [h, orderOf_one] at hxa5; omega
  have hxfpf : ∀ v : V8, spEquivHom (x : StatedSp 4 (ZMod 2)) v = v → v = 0 := by
    refine fixed_eq_zero_of_order_five (V := V8) finrank_V8 (spForm 4 (ZMod 2))
      spForm_nondegenerate.2 (spEquivHom (x : StatedSp 4 (ZMod 2))) (spEquivHom g)
      (by rw [← map_pow, hx5, map_one]) (fun h => hx1 (spEquivHom_eq_one_iff.mp h))
      (by rw [← map_pow, hg3, map_one]) hfpf ?_ ?_ ?_
    · refine LinearEquiv.ext fun v => ?_
      show spEnd (x : StatedSp 4 (ZMod 2)) (spEnd g v) = spEnd g (spEnd (x : StatedSp 4 (ZMod 2)) v)
      rw [← spEnd_mul_apply, ← spEnd_mul_apply, hcomm x]
    · exact fun v w => spForm_spEnd _ v w
    · exact fun v w => spForm_spEnd _ v w
  have hU4 : finrank (ZMod 2) U = 4 := by
    have h4 : 4 ∣ finrank (ZMod 2) U :=
      CFSG.Quasithin.Kleidman.F204.O2Alg.four_dvd_finrank_of_invariant
        (spEquivHom (x : StatedSp 4 (ZMod 2))) (by rw [← map_pow, hx5, map_one]) hxfpf U
        (fun w hw => hpres x w hw)
    have hlt : finrank (ZMod 2) U < 8 := finrank_V8 ▸ Submodule.finrank_lt hUtop
    have hpos : 1 ≤ finrank (ZMod 2) U := Submodule.one_le_finrank_iff.mpr hU0
    omega
  have hQ4 : finrank (ZMod 2) (V8 ⧸ U) = 4 := by
    have := Submodule.finrank_quotient_add_finrank U
    rw [finrank_V8] at this
    omega
  obtain ⟨m, k, hmk, hfm⟩ := exists_two_element_lift f hf hy
  have hT : spEnd (m : StatedSp 4 (ZMod 2)) ^ (2 ^ k) = 1 := by
    rw [← spEndHom_apply, ← map_pow, ← Subgroup.coe_pow, hmk, Subgroup.coe_one, map_one]
  have hTγ : Commute (spEnd (m : StatedSp 4 (ZMod 2))) (spEnd g) := by
    refine LinearMap.ext fun v => ?_
    show spEnd (m : StatedSp 4 (ZMod 2)) (spEnd g v) = spEnd g (spEnd (m : StatedSp 4 (ZMod 2)) v)
    rw [← spEnd_mul_apply, ← spEnd_mul_apply, hcomm m]
  obtain ⟨hflU, hflQ⟩ := sq_trivial_on_flag U hU4.le hQ4.le (spEnd g) (spEnd (m : StatedSp 4 (ZMod 2)))
    hγ hTγ hUg (fun u hu => hpres m u hu) k hT
  let ρ : ↥A' →* Module.End (ZMod 2) V8 := spEndHom.comp A'.subtype
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (spEnd_eq_one_iff.mp ha)
  obtain ⟨K, hKn, hK2, hKm⟩ := exists_normal_exp_two ρ hρ U (fun a u hu => hpres a u hu)
  have := sq_eq_one_of_normal_exp_two f hf K hK2 (hKm m hflU hflQ)
  exact hfm this

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
