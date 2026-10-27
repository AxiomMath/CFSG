module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassCore
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassKer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4_hker_of_data {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz3 : z ^ 3 = 1)
    (e : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (L U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hLF : L ≤ fixSub (MulAut.conj z))
    (hCL : ∀ c ∈ fixSub (MulAut.conj z), (∀ x ∈ L, c * x = x * c) → e c = c →
      c ∈ Subgroup.zpowers z)
    (hU : U₀ ≤ fixSub (MulAut.conj z)) (hUp : IsPGroup p U₀)
    (hcard : (p ^ f) ^ 3 ≤ Nat.card U₀) :
    ∀ ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), Odd (orderOf ζ) →
      Nat.Coprime (orderOf ζ) 3 → ζ * MulAut.conj z = MulAut.conj z * ζ → ζ * e = e * ζ →
      (∀ c ∈ fixSub (MulAut.conj z), ζ c = c) → ζ = 1 := by
  classical
  intro ζ hodd hcop hcomm hcomme hfix
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_bot hcen
  refine d4PtKer_of_inner_trivial hp hp2 hf K hK σ hσ (MulAut.conj z) e ?_ U₀ hU hUp hcard ζ
    hodd hcop hcomm hcomme hfix
  rintro _ ⟨c₀, rfl⟩ hodd' hcop' hcomm' hcomme' hfix'
  have hc₀z : c₀ * z = z * c₀ := by
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm'
  have hc₀F : c₀ ∈ fixSub (MulAut.conj z) := by
    rw [mem_fixSub, MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact hc₀z.symm
  have hec₀ : e c₀ = c₀ := by
    apply hinj
    rw [← mulAut_conj_conj e c₀]
    calc e * MulAut.conj c₀ * e⁻¹ = MulAut.conj c₀ * e * e⁻¹ := by rw [hcomme']
      _ = MulAut.conj c₀ := mul_inv_cancel_right _ _
  have hcL : ∀ x ∈ L, c₀ * x = x * c₀ := by
    intro x hx
    have := hfix' x (hLF hx)
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hmem := hCL c₀ hc₀F hcL hec₀
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hz3' : (MulAut.conj z : MulAut _) ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  have hcube : (MulAut.conj (z ^ k) : MulAut _) ^ 3 = 1 := by
    rw [map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3', one_zpow]
  have hdvd : orderOf (MulAut.conj (z ^ k) : MulAut _) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  have h1 : orderOf (MulAut.conj (z ^ k) : MulAut _) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop' hdvd
  exact orderOf_eq_one_iff.1 h1


theorem d4_weyl_cube_of_pow_three {p f : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K) (hδ : δ = σ ∨ δ = σ⁻¹)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1) :
    (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩) ^ 3 = 1 := by
  classical
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hΦ3 : (fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 := by
    have h := d4_fieldActor_pow_three K hK σ hσ
    rcases hδ with h' | h'
    · rw [h']
      exact h
    · have h2 : fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
        map_inv (fieldActorHom (t := TwistTag.D4) σ) σ
      rw [h', h2, inv_pow, h, inv_one]
  have hN := normSeq_eq_one_of_pow_eq_one hcen hΦ3 he3
  rw [normSeq_three] at hN
  have hn' : ((fieldActor (t := TwistTag.D4) σ δ n : graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom :=
    fieldActor_mem_monoY σ δ hnmono
  have hn'' : ((fieldActor (t := TwistTag.D4) σ δ (fieldActor (t := TwistTag.D4) σ δ n) :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
      graphFixedMonomial TwistTag.D4 K σ.toRingHom :=
    fieldActor_mem_monoY σ δ hn'
  have h1 := graphFixedRootWeylHom_fieldActor σ δ n hnmono
  have h2 := graphFixedRootWeylHom_fieldActor σ δ _ hn'
  have hprod : (⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩ :
        graphFixedRootMonomial TwistTag.D4 K σ.toRingHom) *
      ⟨((fieldActor (t := TwistTag.D4) σ δ n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hn', (fieldActor σ δ n).2⟩⟩ *
      ⟨((fieldActor (t := TwistTag.D4) σ δ (fieldActor (t := TwistTag.D4) σ δ n) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K),
        Subgroup.mem_inf.2 ⟨hn'', (fieldActor σ δ (fieldActor σ δ n)).2⟩⟩ = 1 := by
    exact Subtype.ext (congrArg (fun x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (x : ModGL TwistTag.D4.tag K)) hN)
  have := congrArg (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom) hprod
  rw [map_mul, map_mul, map_one, h2, h1] at this
  rwa [pow_three, ← mul_assoc]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
