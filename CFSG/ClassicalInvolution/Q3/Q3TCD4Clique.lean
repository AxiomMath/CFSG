module

public import CFSG.ClassicalInvolution.Q3.Q3TCBridge
public import CFSG.ClassicalInvolution.Q3.Q3WASTSign
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourModel
public import CFSG.ClassicalInvolution.RouteD.ExoticD4LinearClique
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
public import CFSG.ClassicalInvolution.Q3.Q3TCNodes
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement



section Spin

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}

theorem exists_central_involution3 {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx3 p e Q 𝔉)
    {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉) :
    ∃ c ∈ R, orderOf c = 2 ∧ ∀ r ∈ R, c * r = r * c := by
  obtain ⟨i, hI⟩ := S.map R hR
  obtain ⟨c, hcR, hci⟩ : i ∈ R.map (spinAction Q) := hI.mem
  have hc2 : c * c = 1 := by
    refine S.inj R hR (c * c) (R.mul_mem hcR hcR) ?_
    rw [map_mul, hci]
    exact hI.mul_self
  have hc1 : c ≠ 1 := fun h => hI.ne_one S.odd_card (by rw [← hci, h, map_one])
  refine ⟨c, hcR, orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1, fun r hr => ?_⟩
  have hcomm : c * r * c⁻¹ * r⁻¹ = 1 := by
    refine S.inj R hR _ (R.mul_mem (R.mul_mem (R.mul_mem hcR hr) (R.inv_mem hcR))
      (R.inv_mem hr)) ?_
    have hcen := Subgroup.mem_centralizer_singleton_iff.mp
      (hI.le_centralizer ⟨r, hr, rfl⟩)
    simp only [map_mul, map_inv, hci]
    rw [← hcen]
    group
  calc c * r = (c * r * c⁻¹ * r⁻¹) * (r * c) := by group
    _ = r * c := by rw [hcomm, one_mul]

end Spin

section Spin4

variable {K : Type} [Field K] [Finite K]

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

theorem mem_centralizer_of_map_genSq {X G : Type} [Group X] [Group G] (ψ : G →* X)
    (hker : ψ.ker ≤ Subgroup.center G) (hk2 : ∀ x ∈ ψ.ker, x * x = 1) {R : Subgroup G}
    (hR : GenSq R) {g : G}
    (hg : ψ g ∈ Subgroup.centralizer ((R.map ψ : Subgroup X) : Set X)) :
    g ∈ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (commute_of_map_commute_of_genSq ψ hker hk2 hR (b := g)
    (fun a ha => Subgroup.mem_centralizer_iff.mp hg (ψ a) ⟨a, ha, rfl⟩) x hx)

theorem fund_pair_mul_central_plus3 (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ 4)
    (hker2 : ∀ x ∈ (spinAction (quadPlus 4 K)).ker, x * x = 1)
    (hsingle : Generic.FundamentalSingleClass .POmegaPlus (plusDatum 4 K hn3))
    (hGS : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3), GenSq R)
    (hinj : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3),
      ∀ c ∈ R, spinAction (quadPlus 4 K) c = 1 → c = 1)
    (hlong : ∀ k : Fin 4, Generic.IsLongestRoot (plusDatum 4 K hn3) (Pi.single k 1))
    (hgen : ∀ x : spinGroup (quadPlus 4 K),
      ⨆ k : Fin 4, rankOneRoot (plusDatum 4 K hn3) x (Pi.single k 1) = ⊤)
    {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 K))}
    (hR₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3))
    (hR₂ : R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3))
    (hc : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a)
    {c₁ c₂ : spinGroup (quadPlus 4 K)} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hz₁ : ∀ r ∈ R₁, c₁ * r = r * c₁) (hz₂ : ∀ r ∈ R₂, c₂ * r = r * c₂)
    (h₁ : c₁ ≠ 1) (h₂ : c₂ ≠ 1) :
    c₁ * c₂ ∈ Subgroup.center (spinGroup (quadPlus 4 K)) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hker := ker_spinAction_le_center (quadPlus 4 K)
  have hdim : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hmemF : ∀ (x : spinGroup (quadPlus 4 K)) (k : Fin 4),
      rankOneRoot (plusDatum 4 K hn3) x (Pi.single k 1) ∈
        Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3) := fun x k =>
    ⟨x, Pi.single k 1, Or.inl (hlong k), rfl⟩
  have hθ₁ : spinAction (quadPlus 4 K) c₁ ≠ 1 := fun h => h₁ (hinj R₁ hR₁ c₁ hc₁ h)
  have hθ₂ : spinAction (quadPlus 4 K) c₂ ≠ 1 := fun h => h₂ (hinj R₂ hR₂ c₂ hc₂ h)
  obtain ⟨fr₁, hfr₁⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR₁
  obtain ⟨fr₂, hfr₂⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR₂
  have hi₁ : spinAction (quadPlus 4 K) c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction (quadPlus 4 K) c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  by_cases hEq : fr₂.La (-1) = fr₁.La (-1)
  · apply hker
    rw [MonoidHom.mem_ker, map_mul, hi₁, hi₂, hEq]
    exact fr₁.La_neg_one_mul_self
  · have hc' : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
      rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hc c₁ hc₁ c₂ hc₂]
    have hcent : ∀ A : SL(2, K), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
      intro A
      obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction (quadPlus 4 K)) := hfr₁ ▸ ⟨A, rfl⟩
      rw [← hi₂, ← hrA, ← map_mul, ← map_mul, (hc r hr c₂ hc₂).symm]
    have horth := (Frame.orth_or_eq h2 hc' hcent).resolve_right hEq
    have hneg := La_neg_one_mul_of_orth h2 hdim horth
    have hθ12 : spinAction (quadPlus 4 K) (c₁ * c₂) = LinearEquiv.neg K := by
      rw [map_mul, hi₁, hi₂, hneg]
    have hcent' : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3),
        R ≤ Subgroup.centralizer ({c₁ * c₂} : Set (spinGroup (quadPlus 4 K))) := by
      intro R hR y hy
      have := mem_centralizer_of_map_genSq (spinAction (quadPlus 4 K)) hker hker2 (hGS R hR)
        (g := c₁ * c₂) (by
        rw [hθ12, Subgroup.mem_centralizer_iff]
        intro h _
        ext v
        simp)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp this y hy)
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ (⨆ k : Fin 4, rankOneRoot (plusDatum 4 K hn3) 1 (Pi.single k 1)) := by
      rw [hgen 1]
      trivial
    have : (⨆ k : Fin 4, rankOneRoot (plusDatum 4 K hn3) 1 (Pi.single k 1)) ≤
        Subgroup.centralizer ({c₁ * c₂} : Set (spinGroup (quadPlus 4 K))) :=
      iSup_le fun k => hcent' _ (hmemF 1 k)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hg)

end Spin4

section Model4

theorem plus4_data3 : ∃ hn3 : 3 ≤ 4,
    Generic.FundamentalSingleClass .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3) ∧
    (∀ k : Fin 4, Generic.IsLongestRoot (plusDatum 4 (GaloisField 3 1) hn3) (Pi.single k 1)) ∧
    (∀ x : spinGroup (quadPlus 4 (GaloisField 3 1)),
      ⨆ k : Fin 4, rankOneRoot (plusDatum 4 (GaloisField 3 1) hn3) x (Pi.single k 1) = ⊤) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨hp, Nat.one_pos, le_rfl⟩
  have hM : Generic.modelUniv .POmegaPlus 4 3 1 hp =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 3 1 hp =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 hp).trans (modelUniv_POmegaPlus hn3)
  refine ⟨hn3, ?_, ?_, ?_⟩
  · have key : ∀ M : LieUniversal,
        M = ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
        Generic.FundamentalSingleClass .POmegaPlus M.D →
        Generic.FundamentalSingleClass .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3) := by
      rintro M rfl h
      exact h
    exact key _ hM (fundamentalSingleClass .POmegaPlus 4 3 1 hp trivial hadm (by decide)
      (by decide))
  · have key : ∀ M : LieUniversal,
        M = ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
        (∀ k : Fin M.D.rank, Generic.IsLongestRoot M.D (Pi.single k 1)) →
        ∀ k : Fin 4, Generic.IsLongestRoot (plusDatum 4 (GaloisField 3 1) hn3) (Pi.single k 1) := by
      rintro M rfl h
      exact h
    exact key _ hM fun k => isLongestRoot_single .POmegaPlus 4 3 1 hp trivial hadm k trivial
  · have key : ∀ M : LieUniversal,
        M = ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
        (∀ g : M.K, ⨆ i : Fin M.D.rank, rankOneRoot M.D g (Pi.single i 1) = ⊤) →
        ∀ x : spinGroup (quadPlus 4 (GaloisField 3 1)),
          ⨆ k : Fin 4, rankOneRoot (plusDatum 4 (GaloisField 3 1) hn3) x (Pi.single k 1) = ⊤ := by
      rintro M rfl h
      exact h
    exact key _ hM (iSup_rankOneRoot_simple_eq_top .POmegaPlus 4 3 1 hp trivial hadm)

end Model4

section Clique

theorem d4Clique3_model :
    ∀ (hn3 : 3 ≤ 4)
      {R₁ R₂ R₃ : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))},
      R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3) →
      R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3) →
      R₃ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3) →
      Commutes R₁ R₂ →
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₃) →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃ := by
  obtain ⟨hn3', hsingle, hlong, hgen⟩ := plus4_data3
  intro hn3 R₁ R₂ R₃ h₁ h₂ h₃ hcomm hlin
  have S := spinCtx3_pOmegaPlus (p := 3) (n := 4) (e := 1) (by norm_num) (by norm_num)
  have hsub := fundamentalSubgroups_subset_longest (t := .POmegaPlus) (by decide) (by decide)
    (plusDatum 4 (GaloisField 3 1) hn3)
  have h₁' := hsub h₁
  have h₂' := hsub h₂
  have h₃' := hsub h₃
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd S.odd_card
  have hGS : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3),
      GenSq R := fun R hR => S.genSq (hsub hR)
  have hinj : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3),
      ∀ c ∈ R, spinAction (quadPlus 4 (GaloisField 3 1)) c = 1 → c = 1 :=
    fun R hR c hc h => S.inj R (hsub hR) c hc h
  obtain ⟨W, hW⟩ := hlin
  obtain ⟨c₁, hc₁, ho₁, hz₁⟩ := exists_central_involution3 S h₁'
  obtain ⟨c₂, hc₂, ho₂, hz₂⟩ := exists_central_involution3 S h₂'
  obtain ⟨c₃, hc₃, ho₃, hz₃⟩ := exists_central_involution3 S h₃'
  have hne1 : ∀ {c : spinGroup (quadPlus 4 (GaloisField 3 1))}, orderOf c = 2 → c ≠ 1 :=
    fun ho h => by
      rw [h, orderOf_one] at ho
      omega
  have hsq : ∀ {c : spinGroup (quadPlus 4 (GaloisField 3 1))}, orderOf c = 2 → c * c = 1 :=
    fun {c} ho => by
      rw [← pow_two]
      exact ho ▸ pow_orderOf_eq_one c
  have hζ : c₁ * c₂ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) :=
    fund_pair_mul_central_plus3 S.odd_card hn3 S.hker2 hsingle hGS hinj hlong hgen h₁ h₂ hcomm
      hc₁ hc₂ hz₁ hz₂ (hne1 ho₁) (hne1 ho₂)
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := RouteD.Gaps.standardPair_involutions_commute h2 hW hc₁ hc₃ ho₁ ho₃
  have h₁₂ : c₁ * c₂ = c₂ * c₁ := hcomm c₁ hc₁ c₂ hc₂
  have hc₂eq : c₂ = c₁ * (c₁ * c₂) := by
    rw [← mul_assoc, hsq ho₁, one_mul]
  have hc₁eq : c₁ = (c₁ * c₂) * c₂ := by
    rw [mul_assoc, hsq ho₂, mul_one]
  have h₂₃ : c₂ * c₃ = c₃ * c₂ := by
    have hz := Subgroup.mem_center_iff.mp hζ c₃
    calc c₂ * c₃ = (c₁ * (c₁ * c₂)) * c₃ := by rw [← hc₂eq]
      _ = c₁ * (c₃ * (c₁ * c₂)) := by rw [hz]; group
      _ = (c₁ * c₃) * (c₁ * c₂) := by group
      _ = (c₃ * c₁) * (c₁ * c₂) := by rw [h₁₃]
      _ = c₃ * (c₁ * (c₁ * c₂)) := by group
      _ = c₃ * c₂ := by rw [← hc₂eq]
  have hne₁₃ : R₁ ≠ R₃ := RouteD.ne_of_linearBlockStandardPair hW
  have hnc₁₃ : ¬ Commutes R₁ R₃ := RouteD.not_commutes_of_linearBlockStandardPair hW
  have hne₂₃ : R₂ ≠ R₃ := by
    rintro rfl
    exact hnc₁₃ hcomm
  have hnc₂₃ : ¬ Commutes R₂ R₃ := by
    intro hc23
    obtain ⟨v, hv, hvne⟩ := exists_not_commute_of_linearBlockStandardPair h2 hW hc₁ ho₁
    apply hvne
    have hz := Subgroup.mem_center_iff.mp hζ v
    calc c₁ * v = ((c₁ * c₂) * c₂) * v := by rw [← hc₁eq]
      _ = (c₁ * c₂) * (c₂ * v) := by group
      _ = (c₁ * c₂) * (v * c₂) := by rw [hc23 c₂ hc₂ v hv]
      _ = ((c₁ * c₂) * v) * c₂ := by group
      _ = (v * (c₁ * c₂)) * c₂ := by rw [← hz]
      _ = v * c₁ := by rw [mul_assoc, ← hc₁eq]
  rcases Q3W.spinCtx3_sign S h₁' h₃' h₂' hc₁ hc₃ hc₂ ho₁ ho₃ ho₂ h₁₃ h₂₃ h₁₂ hcomm hne₁₃ hne₂₃
    hnc₁₃ hnc₂₃ with ⟨-, ⟨W', hW'⟩⟩ | ⟨⟨W', hu⟩, -⟩
  · exact ⟨_, linearBlockStandardPair_symm hW'⟩
  · exact (Q3W.false_of_linear_of_unitary3 ⟨_, hW⟩ ⟨_, hu⟩).elim

end Clique


theorem d4LinearClique3 : D4LinearClique3 := by
  obtain ⟨hn3, -, -, -⟩ := plus4_data3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hM : Generic.modelUniv .POmegaPlus 4 3 1 hp =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 3 1 hp =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 hp).trans (modelUniv_POmegaPlus hn3)
  have key : ∀ M : LieUniversal,
      M = ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
      ∀ R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
        ∀ R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
          ∀ R₃ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
            Commutes R₁ R₂ → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₃) →
              ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃ := by
    rintro M rfl R₁ h₁ R₂ h₂ R₃ h₃ hcomm hlin
    exact d4Clique3_model hn3 h₁ h₂ h₃ hcomm hlin
  exact key _ hM

end CFSG.ClassicalInvolution.Q3.Q3TC
