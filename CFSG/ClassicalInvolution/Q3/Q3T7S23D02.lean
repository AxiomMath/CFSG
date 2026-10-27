module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23E01
public import CFSG.ClassicalInvolution.Q3.Q3T7S23D01
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1A
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1B
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1C

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel
  four_le_card_shortField')
open CFSG.ClassicalInvolution.Models (rootSU2 longRootSetU)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open CFSG.ClassicalInvolution.Phan (Su)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}


namespace D4C

section Model

variable {X : Type} [Group X]

theorem exists_chart_psu3 {Φ : Set (Subgroup X)} (P : C22G.PSULayer 3 1 Φ)
    {J J' : Subgroup X} {t : X} (hJΦ : J ∈ Φ) (hJ'Φ : J' ∈ Φ)
    (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t) (hJJ' : J ≠ J')
    (hcommJ : Commutes J J') :
    ∃ ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X,
      ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) ∧
      (∀ n ∈ ψ.ker, ¬ 3 ∣ orderOf n) ∧ ψ.range = omegaGen Φ ∧
      (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ = J ∧
      Q3.Q3P21.rootSU2Two.map ψ = J' ∧
      Q3.Q3W.Pow3 (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)) ∧
      Q3.Q3W.Pow3 Q3.Q3P21.rootSU2Two := by
  classical
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have hker : P.ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 3 1 Fact.out).K := P.ker_le
  have hcop : ∀ x ∈ P.ψ.ker, ¬ 3 ∣ orderOf x :=
    Q3.Q3W.ker_not_dvd_three_model (show IsFundTag .PSU from trivial)
      Q3T8.Asc77.C22G.PsuPair.admissible P.ψ hker
  obtain ⟨eJ⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num)
    (t := .PSU) (n := 4) (by trivial) Q3T8.Asc77.C22G.PsuPair.admissible (by decide)
    (by decide) hRJ
  obtain ⟨eJ'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num)
    (t := .PSU) (n := 4) (by trivial) Q3T8.Asc77.C22G.PsuPair.admissible (by decide)
    (by decide) hRJ'
  obtain ⟨-, -, -, -, -, -, hP3⟩ :=
    Q3.Q3W.exists_lift_central_involution3 P.ψ hker hcop eJ (hJR ▸ htJ)
  obtain ⟨-, -, -, -, -, -, hP3'⟩ :=
    Q3.Q3W.exists_lift_central_involution3 P.ψ hker hcop eJ' (hJ'R ▸ htJ')
  have hcRR : Commutes RJ RJ' := by
    have h := Q3.Q3W.commutes_of_map_commute_exponent3 P.ψ hker hcop (A := RJ') (L := RJ) hP3
      (fun a' ha' l hl => (hcommJ _ (hJR ▸ ⟨l, hl, rfl⟩) _ (hJ'R ▸ ⟨a', ha', rfl⟩)).symm)
    exact fun x hx y hy => (h y hy x hx).symm
  have hRne : RJ ≠ RJ' := by
    intro h
    apply hJJ'
    rw [hJR, hJ'R, h]
  obtain ⟨φ₀, hφ₀⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
    Q3T8.Asc77.C22G.PsuPair.admissible
  obtain ⟨g₁, hg₂, hg₃⟩ := Q3.Q3P21.y1c (RJ.map φ₀.toMonoidHom) ((hφ₀ RJ).mp hRJ)
    (RJ'.map φ₀.toMonoidHom) ((hφ₀ RJ').mp hRJ')
    (fun h => hRne (Subgroup.map_injective φ₀.injective h))
    ((RouteD.Gaps.commutes_map_equiv φ₀).mpr hcRR)
  let φ : (modelUniv .PSU 4 3 1 Nat.prime_three).K ≃* Su (GaloisField 3 (2 * 1)) 3 1 4 :=
    φ₀.trans (MulAut.conj g₁⁻¹)
  have hmapφ : ∀ R : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K,
      R.map φ.toMonoidHom = conjSub g₁⁻¹ (R.map φ₀.toMonoidHom) := fun R => by
    unfold conjSub
    rw [Subgroup.map_map]
    rfl
  have hR₂φ : RJ.map φ.toMonoidHom =
      rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4) := by
    rw [hmapφ, hg₂]
    exact conjSub_inv_conjSub g₁ _
  have hR₃φ : RJ'.map φ.toMonoidHom = Q3.Q3P21.rootSU2Two := by
    rw [hmapφ, hg₃]
    exact conjSub_inv_conjSub g₁ _
  have hcomp : (P.ψ.comp φ.symm.toMonoidHom).comp φ.toMonoidHom = P.ψ := by
    ext r
    simp
  refine ⟨P.ψ.comp φ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have h1 : φ.symm y ∈ P.ψ.ker := hy
    have h2 := hker h1
    have : y = φ (φ.symm y) := by simp
    rw [this]
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro w'
    apply φ.symm.injective
    rw [map_mul, map_mul]
    simpa using h2 (φ.symm w')
  · intro n hn
    have h1 : φ.symm n ∈ P.ψ.ker := hn
    have := hcop _ h1
    rwa [MulEquiv.orderOf_eq] at this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.symm.surjective,
      ← MonoidHom.range_eq_map, P.range_eq]
  · rw [← hR₂φ, Subgroup.map_map, hcomp, ← hJR]
  · rw [← hR₃φ, Subgroup.map_map, hcomp, ← hJ'R]
  · rw [← hR₂φ]
    exact Q3.Q3W.Pow3.map φ.toMonoidHom hP3
  · rw [← hR₃φ]
    exact Q3.Q3W.Pow3.map φ.toMonoidHom hP3'

theorem exists_short_block3 (ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))
    (hcop : ∀ n ∈ ψ.ker, ¬ 3 ∣ orderOf n)
    (h0 : Q3.Q3W.Pow3 (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)))
    (h2 : Q3.Q3W.Pow3 Q3.Q3P21.rootSU2Two) {z₁ u : X} (hz₁2 : z₁ * z₁ = 1)
    (hz₁u : z₁ * u = u * z₁) (hu : u ∈ ψ.range)
    (hstab : ∀ x, z₁ * ψ x * z₁⁻¹ ∈ ψ.range)
    (hu0 : ∀ x ∈ (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ,
      u * x = x * u)
    (hu2 : ∀ x ∈ Q3.Q3P21.rootSU2Two.map ψ, u * x = x * u)
    (θ θ' : SL(2, GaloisField 3 1) →* X)
    (hθ : θ.range = (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ)
    (hθ' : θ'.range = Q3.Q3P21.rootSU2Two.map ψ)
    (hθτ : ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s))
    (hθ'τ : ∀ s, z₁ * θ' s * z₁⁻¹ = θ' (diagConj2 (-1) 1 s))
    (hclaim : ∀ a : X, a * u = u * a →
      (∀ x ∈ (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ,
        a * x = x * a) →
      (∀ x ∈ Q3.Q3P21.rootSU2Two.map ψ, a * x = x * a) → a * z₁ = z₁ * a) :
    ∃ (S : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)) (W : Subgroup X),
      TwistedB2BlockPair (minusCoeffs_irr 3 1) W
        ((rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ) (S.map ψ) ∧
      rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4) ⊔ S = ⊤ ∧
      S.map ψ ≤ ⁅S.map ψ, S.map ψ⁆ ∧ ∀ y ∈ S, z₁ * ψ y * z₁⁻¹ = ψ y := by
  classical
  have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁2
  let τ : X ≃* X := MulAut.conj z₁
  have hτ : ∀ x : X, τ (τ x) = x := by
    intro x
    show z₁ * (z₁ * x * z₁⁻¹) * z₁⁻¹ = x
    rw [hz₁inv]
    calc z₁ * (z₁ * x * z₁) * z₁ = (z₁ * z₁) * x * (z₁ * z₁) := by group
      _ = x := by rw [hz₁2]; simp
  have hstab' : ∀ x, τ (ψ x) ∈ ψ.range := hstab
  have hθτ₀ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s) := hθτ
  have hθ'τ₀ : ∀ s, τ (θ' s) = θ' (diagConj2 (-1) 1 s) := hθ'τ
  obtain ⟨H₁, H₂, y, hy, -, hyR₀, hyR₂, hd1, hd2⟩ :=
    Q3.Q3P21.y1a ψ hker τ hτ θ θ' hθ hθ' hθτ₀ hθ'τ₀
  obtain ⟨xu, hxu⟩ := hu
  have hxu0 : ∀ b ∈ rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4),
      ψ xu * ψ b = ψ b * ψ xu := by
    intro b hb
    rw [hxu]
    exact hu0 _ ⟨b, hb, rfl⟩
  have hxu2 : ∀ b ∈ Q3.Q3P21.rootSU2Two, ψ xu * ψ b = ψ b * ψ xu := by
    intro b hb
    rw [hxu]
    exact hu2 _ ⟨b, hb, rfl⟩
  have hyu : u * ψ y = ψ y * u := by
    have := Q3.Q3P21.comm_blockDiag_of_map_centralizes ψ hker hcop h0 h2 xu hxu0 hxu2 y H₁ H₂ hy
    rwa [hxu] at this
  have hact : ∀ {R : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)},
      (∀ b ∈ R, τ (ψ b) = ψ (y * b * y⁻¹)) →
        ∀ x ∈ R.map ψ, (ψ y)⁻¹ * z₁ * x = x * ((ψ y)⁻¹ * z₁) := by
    intro R hyR x hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hτb : z₁ * ψ b * z₁⁻¹ = ψ (y * b * y⁻¹) := hyR b hb
    calc (ψ y)⁻¹ * z₁ * ψ b = (ψ y)⁻¹ * (z₁ * ψ b * z₁⁻¹) * z₁ := by group
      _ = (ψ y)⁻¹ * ψ (y * b * y⁻¹) * z₁ := by rw [hτb]
      _ = ψ b * ((ψ y)⁻¹ * z₁) := by
        simp only [map_mul, map_inv]
        group
  have hau : (ψ y)⁻¹ * z₁ * u = u * ((ψ y)⁻¹ * z₁) := by
    have hyu' : (ψ y)⁻¹ * u = u * (ψ y)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hyu]
      group
    calc (ψ y)⁻¹ * z₁ * u = (ψ y)⁻¹ * (z₁ * u) := by group
      _ = (ψ y)⁻¹ * (u * z₁) := by rw [hz₁u]
      _ = ((ψ y)⁻¹ * u) * z₁ := by group
      _ = (u * (ψ y)⁻¹) * z₁ := by rw [hyu']
      _ = u * ((ψ y)⁻¹ * z₁) := by group
  have hcomm := hclaim ((ψ y)⁻¹ * z₁) hau (fun x hx => hact hyR₀ x hx) (fun x hx => hact hyR₂ x hx)
  have hfixy : τ (ψ y) = ψ y := by
    have h1 : (ψ y)⁻¹ * z₁ = z₁ * (ψ y)⁻¹ := by
      have h3 : (ψ y)⁻¹ * z₁ * z₁ = z₁ * ((ψ y)⁻¹ * z₁) := by
        rw [← hcomm]
      calc (ψ y)⁻¹ * z₁ = (ψ y)⁻¹ * z₁ * z₁ * z₁⁻¹ := by group
        _ = z₁ * ((ψ y)⁻¹ * z₁) * z₁⁻¹ := by rw [h3]
        _ = z₁ * (ψ y)⁻¹ := by group
    have hc : z₁ * ψ y = ψ y * z₁ := by
      calc z₁ * ψ y = ψ y * ((ψ y)⁻¹ * z₁) * ψ y := by group
        _ = ψ y * (z₁ * (ψ y)⁻¹) * ψ y := by rw [h1]
        _ = ψ y * z₁ := by group
    show z₁ * ψ y * z₁⁻¹ = ψ y
    rw [hc]
    group
  have hlin := Q3.Q3P21.y1b ψ hker τ hτ hstab' H₁ H₂ y hy hyR₀ hyR₂ hd1 hd2 hfixy
  have hirr := minusCoeffs_irr 3 1
  have := fact_shortField hirr
  have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
  have hg6 : SpinMinus6Generated (minusCoeffs_irr 3 1) :=
    spinMinus6Generated_galois (p := 3) (f := 1) (by norm_num)
  obtain ⟨S, W₃, hpair, hRS, hfix⟩ := Q3.Q3P21.exists_fixed_shortPair_linear_three hg6 ψ hker τ
    hτ (R := rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4))
    ⟨_, Models.isLongRootSU2_standard (by norm_num : 2 ≤ 4)⟩ θ hθ hθτ₀ hlin
  have hSperf : S.map ψ ≤ ⁅S.map ψ, S.map ψ⁆ := by
    obtain ⟨θ₀, -, -, -, -, hV⟩ := hpair
    have := range_perfect_of_sl2 (four_le_card_shortField' (b := (minusCoeffs 3 1).1)
      (c := (minusCoeffs 3 1).2)) (θ₀.comp (spinMinusModel hirr).sb)
    rwa [MonoidHom.range_comp, hV] at this
  exact ⟨S, W₃, hpair, hRS, hSperf, hfix⟩

end Model

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem eSideD4_3
    [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hex : ExactMembers Ω)
    (hOE : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥)
    (hE : LayerOrthType Ω e 6 false) {z₁ : G} (hz₁2 : z₁ * z₁ = 1) (hz₁e : z₁ * e = e * z₁)
    (hz₁u : z₁ * u = u * z₁)
    (θ θ' : SL(2, GaloisField 3 1) →* G) (hθ : θ.range = conjSub g K)
    (hθ' : θ'.range = conjSub g K')
    (hθτ : ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s))
    (hθ'τ : ∀ s, z₁ * θ' s * z₁⁻¹ = θ' (diagConj2 (-1) 1 s))
    (hclaim : ∀ a : G, a * u = u * a → (∀ x ∈ conjSub g K, a * x = x * a) →
      (∀ x ∈ conjSub g K', a * x = x * a) → a * z₁ = z₁ * a) :
    ∃ K₃ : Subgroup G, (∃ V, TwistedB2BlockPair (minusCoeffs_irr 3 1) V (conjSub g K) K₃) ∧
      K₃ ≤ Subgroup.centralizer ({z₁} : Set G) ∧ K₃ ≤ ⁅K₃, K₃⁆ ∧
      K₃ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e ∧
      Q3T8.Asc77.ExactLayer.exactLayer Ω e ≤ conjSub g K ⊔ K₃ ∧
      conjSub g K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e ∧
      conjSub g K' ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e := by
  classical
  have hst := hs.stand
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hKΩ hs.hz hR hRN
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hK'Ω hzK' hR' hR'N
  have hJΩ : conjSub g K ∈ Ω := hst.hyp.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hst.hyp.conjInvariant g K' hK'Ω
  have hJe := Q3T8.Asc77.T7Z.conjSub_le_centralizer_e' hd hKe
  have hJ'e := Q3T8.Asc77.T7Z.conjSub_le_centralizer_e' hd hK'e
  have hKΦ : K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hKΩ hKe
  have hK'Φ : K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hK'Ω hK'e
  have hJΦ : conjSub g K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hJΩ hJe
  have hJ'Φ : conjSub g K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hJ'Ω hJ'e
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne ((conjSub_inj g).mp h).symm
  have hcommJ : Commutes (conjSub g K) (conjSub g K') :=
    (Q3T8.Asc77.T7Z.twin_commutes hs hex).conjSub g
  obtain ⟨R₂, R₂', a₂, b₂, v', hJt, hJ't, -⟩ := Q3T8.Asc77.T7L.exists_uFrame hs hd
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJt).2
  have hJ'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJ't).2
  obtain ⟨P⟩ := Q3T8.Asc77.C22N.nonempty_psuLayer_of_layerOrth hOE hE
  have hLayer := Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω e
  have hKle : K ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := le_omegaGen hKΦ
  have hK'le : K' ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := le_omegaGen hK'Φ
  have hJle : conjSub g K ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := le_omegaGen hJΦ
  have hJ'le : conjSub g K' ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) :=
    le_omegaGen hJ'Φ
  have hue : u ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := sup_le hKle hK'le hd.hu
  obtain ⟨ψ, hker, hcop, hrange, hJ0, hJ'0, h0, h2⟩ :=
    exists_chart_psu3 P hJΦ hJ'Φ htJ htJ' hJJ' hcommJ
  have hz₁c : z₁ ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hz₁e
  have hstab : ∀ x, z₁ * ψ x * z₁⁻¹ ∈ ψ.range := by
    intro x
    have h1 := Q3T8.Asc77.ExactLayer.conjSub_exactLayer hst.hyp.conjInvariant hz₁c
    have hx : ψ x ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω e := by
      have hx' : ψ x ∈ ψ.range := ⟨x, rfl⟩
      rw [hrange, ← hLayer] at hx'
      exact hx'
    have h2' : z₁ * ψ x * z₁⁻¹ ∈ conjSub z₁ (Q3T8.Asc77.ExactLayer.exactLayer Ω e) :=
      conj_mem_conjSub hx
    rw [h1, hLayer, ← hrange] at h2'
    exact h2'
  have hu0 : ∀ x ∈ (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ,
      u * x = x * u := by
    intro x hx
    rw [hJ0] at hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJu hx)).symm
  have hu2 : ∀ x ∈ Q3.Q3P21.rootSU2Two.map ψ, u * x = x * u := by
    intro x hx
    rw [hJ'0] at hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJ'u hx)).symm
  have huψ : u ∈ ψ.range := by
    rw [hrange]
    exact hue
  obtain ⟨S, W₃, hpair, hRS, hSperf, hfix⟩ := exists_short_block3 ψ hker hcop h0 h2 hz₁2 hz₁u huψ
    hstab hu0 hu2 θ θ' (hθ.trans hJ0.symm) (hθ'.trans hJ'0.symm) hθτ hθ'τ
    (by
      intro a ha hJa hJ'a
      refine hclaim a ha (fun x hx => hJa x ?_) (fun x hx => hJ'a x ?_)
      · rw [hJ0]; exact hx
      · rw [hJ'0]; exact hx)
  refine ⟨S.map ψ, ⟨_, hJ0 ▸ hpair⟩, ?_, hSperf, ?_, ?_, hJle.trans hLayer.ge,
    hJ'le.trans hLayer.ge⟩
  · rintro _ ⟨y₀, hy₀, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix y₀ hy₀
    calc ψ y₀ * z₁ = (z₁ * ψ y₀ * z₁⁻¹) * z₁ := by rw [h]
      _ = z₁ * ψ y₀ := by group
  · rw [hLayer, ← hrange]
    exact Subgroup.map_le_range ψ S
  · rw [hLayer, ← hrange, MonoidHom.range_eq_map, ← hRS, Subgroup.map_sup, hJ0]

end D4C

end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
