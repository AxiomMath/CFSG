module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911G2
import CFSG.Walter.FinalNative
import CFSG.GH74.Generic.BProg.B1.PilotS4Facts
import CFSG.GH74.Generic.BProg.B2.FixFourS45

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace GenLocG2Basic

theorem centralizer_sup_eq_top_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {z z' : A}
    (h : centralizer ({e z} : Set B) ⊔ centralizer ({e z'} : Set B) = ⊤) :
    centralizer ({z} : Set A) ⊔ centralizer ({z'} : Set A) = ⊤ := by
  have hc : ∀ w : A, centralizer ({e w} : Set B) ≤ (centralizer ({w} : Set A)).map e.toMonoidHom := by
    intro w y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    show e.symm y ∈ centralizer ({w} : Set A)
    rw [mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    simpa using hy
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ centralizer ({e z} : Set B) ⊔ centralizer ({e z'} : Set B) := by rw [h]; trivial
  have h1 : centralizer ({e z} : Set B) ⊔ centralizer ({e z'} : Set B) ≤
      (centralizer ({z} : Set A) ⊔ centralizer ({z'} : Set A)).map e.toMonoidHom := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (hc z) (hc z')
  obtain ⟨y, hy, hyx⟩ := h1 hx
  have : y = x := e.injective hyx
  rwa [this] at hy

theorem eq_of_sq_eq_one_of_isCyclic {Q : Type*} [Group Q] [IsCyclic Q] {x y : Q}
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.1 (hg x)
  obtain ⟨b, rfl⟩ := mem_zpowers_iff.1 (hg y)
  have key : ∀ c : ℤ, g ^ c * g ^ c = 1 → g ^ c ≠ 1 →
      ∃ m : ℤ, c + c = (orderOf g : ℤ) * (2 * m + 1) := by
    intro c hc hc1
    rw [← zpow_add, zpow_eq_one_iff_modEq] at hc
    rw [Ne, zpow_eq_one_iff_modEq] at hc1
    obtain ⟨k, hk⟩ := (Int.modEq_zero_iff_dvd.1 hc)
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exact absurd (Int.modEq_zero_iff_dvd.2 ⟨m, by linarith⟩) hc1
    · exact ⟨m, hk⟩
  obtain ⟨m, hm⟩ := key a hx hx1
  obtain ⟨l, hl⟩ := key b hy hy1
  rw [zpow_eq_zpow_iff_modEq]
  exact Int.modEq_iff_dvd.2 ⟨l - m, by linarith⟩

theorem congr_mem_range_conj_iff {A B : Type} [Group A] [Group B] (e : A ≃* B) (α : MulAut A) :
    MulAut.congr e α ∈ (MulAut.conj : B →* MulAut B).range ↔
      α ∈ (MulAut.conj : A →* MulAut A).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
    have := congrArg (fun φ : MulAut B => e.symm (φ (e x))) hy
    simpa [MulAut.congr_apply, MulAut.conj_apply] using this
  · rintro ⟨g, rfl⟩
    refine ⟨e g, MulEquiv.ext fun x => ?_⟩
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem mem_fixedIn_zpowers {J : Type} [Group J] (σ : MulAut J) (x : J) :
    x ∈ fixedIn J (zpowers σ) ↔ σ x = x := by
  constructor
  · intro h
    exact h σ (mem_zpowers σ)
  · intro h φ hφ
    have hle : zpowers σ ≤ MulAction.stabilizer (MulAut J) x :=
      zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact h)
    simpa using MulAction.mem_stabilizer_iff.1 (hle hφ)

theorem nonempty_fixedIn_zpowers_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (σ : MulAut A) :
    Nonempty (↥(fixedIn A (zpowers σ)) ≃*
      ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub (MulAut.congr e σ))) := by
  have hmap : (fixedIn A (zpowers σ)).map e.toMonoidHom =
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub (MulAut.congr e σ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_fixedIn_zpowers σ x).1 hx
      show (MulAut.congr e σ) (e x) = e x
      simp [MulAut.congr_apply, hx']
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hy' : (MulAut.congr e σ) y = y := hy
      refine (mem_fixedIn_zpowers σ _).2 ?_
      apply e.injective
      simpa [MulAut.congr_apply] using hy'
  exact ⟨((fixedIn A (zpowers σ)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

end GenLocG2Basic

section G2


variable {J : Type} [Group J] [Finite J] {f : ℕ}

omit [Finite J] in
theorem g2_sup_centralizer_eq_top (hf : 2 ≤ f) (hJ : LieModel J .G2 0 3 f) {z z' : J}
    (hz : z * z = 1) (hz' : z' * z' = 1) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) (hne : z ≠ z')
    (hc : z * z' = z' * z) :
    centralizer ({z} : Set J) ⊔ centralizer ({z'} : Set J) = ⊤ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hq : 5 ≤ 3 ^ f := by
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨ψ⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.equiv_modelUniv_g2 hp (by norm_num) (by omega)
    (by omega) hJ
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .G2 0 3 f := ⟨hp, by omega, rfl, by omega⟩
  refine GenLocG2Basic.centralizer_sup_eq_top_of_equiv ψ ?_
  refine CFSG.ClassicalInvolution.G2D4Models.g2CentralizersGenerate_of_nonToral
    (CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all) (by norm_num) hq hadm (ψ z) (ψ z')
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hz, map_one]
  · rw [← map_mul, hz', map_one]
  · exact fun h => hz1 (ψ.injective (by rw [h, map_one]))
  · exact fun h => hz1' (ψ.injective (by rw [h, map_one]))
  · exact fun h => hne (ψ.injective h)
  · rw [← map_mul, ← map_mul, hc]

omit
  [Finite J] in
theorem g2_mul_mem_inn (hf : 1 ≤ f) (hJ : LieModel J .G2 0 3 f) {σ σ' : MulAut J}
    (hσ : σ * σ = 1) (hσ' : σ' * σ' = 1) (hc : σ * σ' = σ' * σ)
    (h₁ : σ ∉ (MulAut.conj : J →* MulAut J).range) (h₂ : σ' ∉ (MulAut.conj : J →* MulAut J).range) :
    σ * σ' ∈ (MulAut.conj : J →* MulAut J).range := by
  have _ := hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hJ
  obtain ⟨-, H, _, hcyc, Θ, hΘ⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_aut_facts Nat.prime_three (by norm_num) hf F hcard
  let Θ' : MulAut J →* H := Θ.comp (MulAut.congr e).toMonoidHom
  have hker : ∀ α : MulAut J, Θ' α = 1 ↔ α ∈ (MulAut.conj : J →* MulAut J).range := by
    intro α
    rw [← GenLocG2Basic.congr_mem_range_conj_iff e α, ← hΘ]
    rfl
  have h1 : Θ' σ ≠ 1 := fun h => h₁ ((hker σ).1 h)
  have h2 : Θ' σ' ≠ 1 := fun h => h₂ ((hker σ').1 h)
  have hs1 : Θ' σ * Θ' σ = 1 := by rw [← map_mul, hσ, map_one]
  have hs2 : Θ' σ' * Θ' σ' = 1 := by rw [← map_mul, hσ', map_one]
  have heq : Θ' σ = Θ' σ' := GenLocG2Basic.eq_of_sq_eq_one_of_isCyclic hs1 hs2 h1 h2
  rw [← hker, map_mul, ← heq]
  exact hs1

omit
  [Finite J] in
theorem g2_outer_fixed_qShape4 (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f)
    {σ : MulAut J} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : J →* MulAut J).range) :
    QShape4 ↥(fixedIn J (Subgroup.zpowers σ)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hJ
  have : CharP F CFSG.LieType.Ree.ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hcard
  have : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.LieType.Ree.ReeTag.G2.tag F) :=
    CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨Ψ⟩ := GenLocG2Basic.nonempty_fixedIn_zpowers_equiv e σ
  have hα2 : (MulAut.congr e σ) ^ 2 = 1 := by rw [sq, ← map_mul, hσ, map_one]
  have hnot : MulAut.congr e σ ∉ (MulAut.conj : CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.G2g F →*
      MulAut (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.G2g F)).range :=
    fun h => hout ((GenLocG2Basic.congr_mem_range_conj_iff e σ).1 h)
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
      (by omega) hcard hα2 with
    ⟨g, a, hαg⟩ | ⟨e', he', hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαb⟩
  · exact absurd (CFSG.GH74.GLS.IVK.Proofs2.ivk93res_inner_of_diag hαg) hnot
  · exfalso
    have h3 : 3 ^ f = 3 ^ (2 * e') := by rw [← hcard, hKe, ← pow_mul, mul_comm]
    have h4 : f = 2 * e' := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    obtain ⟨k, hk⟩ := hodd
    omega
  · have hb : 1 ≤ b := by omega
    have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
    have hα' : (MulAut.conj g * CFSG.LieType.Ree.ReeTag.G2.finiteReeAut F b) ^ 2 = 1 := hαb ▸ hα2
    obtain ⟨Ψ'⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.g2_ree_fixed_equiv hK' hα'
    have hfix := congrArg CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub hαb
    exact ⟨2 * b + 1, CFSG.Walter.blueprintLieModel_twistedG2_of_mulEquiv b hb F hK'
      (Ψ.trans ((MulEquiv.subgroupCongr hfix).trans Ψ'))⟩

theorem g2_sup_centralizer_fixed_eq_top (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f)
    {σ : MulAut J} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : J →* MulAut J).range) {d : J}
    (hd : orderOf d = 2) (hσd : σ d = d) :
    centralizer ({d} : Set J) ⊔ fixedIn J (Subgroup.zpowers σ) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := g2_outer_fixed_qShape4 hf hodd hJ hσ hout
  have hdJ₀ : d ∈ fixedIn J (Subgroup.zpowers σ) := (GenLocG2Basic.mem_fixedIn_zpowers σ d).2 hσd
  have hd₀ : orderOf (⟨d, hdJ₀⟩ : ↥(fixedIn J (Subgroup.zpowers σ))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hd
  obtain ⟨n, hsplit⟩ := CFSG.GH74.Generic.BProg.B1.PilotS4.splitGrp_of_qShape4 hQ
  obtain ⟨L, hL⟩ := hsplit.split _ hd₀
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (by rw [hL.card]; exact hL.even)
  have hl2 : orderOf (l : ↥(fixedIn J (Subgroup.zpowers σ))) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hl
  obtain ⟨g, hg⟩ := (FixFourS45.shape4_data hQ).2 _ _ hd₀ hl2
  have hcomm : (⟨d, hdJ₀⟩ : ↥(fixedIn J (Subgroup.zpowers σ))) * (l : ↥(fixedIn J (Subgroup.zpowers σ))) =
      (l : ↥(fixedIn J (Subgroup.zpowers σ))) * ⟨d, hdJ₀⟩ :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hL.le_cent l.2)).symm
  have hne : (l : ↥(fixedIn J (Subgroup.zpowers σ))) ≠ ⟨d, hdJ₀⟩ := fun hh => hL.not_mem (hh ▸ l.2)
  set u : J := ((l : ↥(fixedIn J (Subgroup.zpowers σ))) : J) with hu
  have hu2 : orderOf u = 2 := by rw [hu, Subgroup.orderOf_coe]; exact hl2
  have hsq : ∀ x : J, orderOf x = 2 → x * x = 1 := fun x hx => by
    rw [← sq]; exact hx ▸ pow_orderOf_eq_one x
  have hgu : (g : J) * d * (g : J)⁻¹ = u := congrArg Subtype.val hg
  have hgen := g2_sup_centralizer_eq_top (by omega) hJ (hsq d hd) (hsq u hu2)
    (fun h => by rw [h, orderOf_one] at hd; omega) (fun h => by rw [h, orderOf_one] at hu2; omega)
    (fun h => hne (Subtype.ext h.symm)) (congrArg Subtype.val hcomm)
  rw [eq_top_iff, ← hgen]
  refine sup_le le_sup_left ?_
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hcd : (g : J)⁻¹ * y * (g : J) ∈ centralizer ({d} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : y * ((g : J) * d * (g : J)⁻¹) = ((g : J) * d * (g : J)⁻¹) * y := by rw [hgu]; exact hy
    calc (g : J)⁻¹ * y * (g : J) * d = (g : J)⁻¹ * (y * ((g : J) * d * (g : J)⁻¹)) * (g : J) := by group
      _ = (g : J)⁻¹ * (((g : J) * d * (g : J)⁻¹) * y) * (g : J) := by rw [h1]
      _ = d * ((g : J)⁻¹ * y * (g : J)) := by group
  have hy' : y = (g : J) * ((g : J)⁻¹ * y * (g : J)) * (g : J)⁻¹ := by group
  rw [hy']
  exact mul_mem (mul_mem (mem_sup_right g.2) (mem_sup_left hcd)) (mem_sup_right (inv_mem g.2))

end G2

end CFSG.GH74.Generic.BProg.B2
