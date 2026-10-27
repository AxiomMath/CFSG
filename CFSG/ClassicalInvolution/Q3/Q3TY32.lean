module

public import CFSG.ClassicalInvolution.Q3.Q3TPCtx
public import CFSG.ClassicalInvolution.Q3.Q3TPChain
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3TY3
public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.Q3.Q3TSRowSU4
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Pairs
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSU
public import CFSG.ClassicalInvolution.Q3.Q3TWRowTD
public import CFSG.ClassicalInvolution.Q3.Q3TY1
public import CFSG.ClassicalInvolution.Q3.Q3TY5
public import CFSG.ClassicalInvolution.Q3.Q3WATwinDRow
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TP
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open scoped MatrixGroups


section Model

theorem yData3S_psu4 : YData3S .PSU 4 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadmU : StatedLieAdmissible .PSU 4 3 1 := ⟨hp, le_rfl, by norm_num, by decide⟩
  have hpc := powCop3_model (t := .PSU) (n := 4) trivial hadmU (by decide) (by decide)
  refine ⟨ModelFacts.fundamentalSingleClass .PSU 4 3 1 hp trivial hadmU (by decide) (by decide),
    perfectK_of_admissible hp trivial hadmU, hpc.pow3, ?_, fun w hw => hpc.cop w hw⟩
  intro R hR r hr hc
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e, he⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadmU
  obtain ⟨ε⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSU)
    (n := 4) (by norm_num) trivial hadmU (by decide) (by decide) hR
  obtain ⟨i, hi⟩ := (he R).mp hR
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hcR : (⟨r, hr⟩ : R) ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc s)
  rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 ε _).mp hcR) with h | h
  · have : (⟨r, hr⟩ : R) = 1 := ε.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · exfalso
    have hr2 : orderOf r = 2 := by
      have : orderOf (⟨r, hr⟩ : R) = 2 := by
        rw [orderOf_eq_two_iff_of_equiv_sl2 hodd ε]
        exact ε.injective (by rw [h]; simp)
      rwa [Subgroup.orderOf_mk] at this
    have hrL : e r ∈ R.map e.toMonoidHom := ⟨r, hr, rfl⟩
    have hord : orderOf (e r) = 2 := by rw [MulEquiv.orderOf_eq]; exact hr2
    have hei := hi.eq_of_orderOf_eq_two hK hp2 hrL hord
    have hz : e r ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 4) := Q3TS.equiv_mem_center e hc
    rw [hei] at hz
    exact ModelFacts.TG3.not_mem_center_of_isLongRootSU2 hK hp2 le_rfl (by norm_num) hi hz

theorem exists_noncommuting_fund_psu4 :
    ∃ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
      ∃ R' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
        R ≠ R' ∧ ¬ Commutes R R' := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadmU : StatedLieAdmissible .PSU 4 3 1 := ⟨hp, le_rfl, by norm_num, by decide⟩
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  have h2 : (2 : GaloisField 3 2) ≠ 0 := two_ne_zero_of_charP_ne_two (p := 3) hp2
  obtain ⟨e, he⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadmU
  let T₁ : Pair 4 := ⟨{(0 : Fin 4), 1}, Finset.card_pair (by decide)⟩
  let T₂ : Pair 4 := ⟨{(1 : Fin 4), 2}, Finset.card_pair (by decide)⟩
  have hmap : ∀ T : Pair 4,
      ((LcU (GaloisField 3 2) 3 1 T).map e.symm.toMonoidHom).map e.toMonoidHom =
        LcU (GaloisField 3 2) 3 1 T := fun T => by
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := MonoidHom.ext fun x => by simp
    rw [this, Subgroup.map_id]
  refine ⟨(LcU (GaloisField 3 2) 3 1 T₁).map e.symm.toMonoidHom,
    (he _).mpr (by rw [hmap]; exact LcU_mem_longRootSetU h2 _ T₁),
    (LcU (GaloisField 3 2) 3 1 T₂).map e.symm.toMonoidHom,
    (he _).mpr (by rw [hmap]; exact LcU_mem_longRootSetU h2 _ T₂), ?_, ?_⟩
  · intro h
    have h' := congrArg (fun S => S.map e.toMonoidHom) h
    simp only [hmap] at h'
    have hT := LcU_injective hK hp2 (by norm_num : 2 ≤ 4) h'
    have : (0 : Fin 4) ∈ T₂.1 := by rw [← hT]; simp [T₁]
    simp [T₂] at this
  · intro hc
    have := commutes_map_hom e.toMonoidHom hc
    rw [hmap, hmap] at this
    exact not_commutes_LcU_overlap hK hp2 (by norm_num : 3 ≤ 4) (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide) this

end Model

section Chain

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem commutes_partner_of_perfect3S (c : TCtxS3 tY nY Ω K z) (hMFZ : Gaps.FundNoncentral 3)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hD : Nat.card ι ≤ 4)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t) {S : Subgroup G}
    (hS : ⁅S, S⁆ = S) (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) : Commutes β S := by
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 ht (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj c.hΩ.conjInvariant h z c.hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]
    exact localOddThreeFree3_conj c.hΩ.conjInvariant h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 c.hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  have hnorm := perfect_le_normalizer_of_involution3 hMFZ c.hΩ c.hex hP1t hO3t Dt hD hSt hS hβ ht
  obtain ⟨e⟩ := ht.nonempty_equiv_sl2 (c.hex β hβ)
  have hcent := perfect_le_centralizer_of_normalizes_sl2 e hS hnorm
  intro b hb s hs
  exact Subgroup.mem_centralizer_iff.mp (hcent hs) b hb

@[expose] def TwinSU4ShortNode3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSU 4) (conjClass3 K) z →
      ∀ (N K₂ : Subgroup G) (t : G), N ∈ conjClass3 K → IsClassicalMember3 N t →
        K₂ ∈ centralizingMembers (conjClass3 K) {z} → K₂ ≠ K →
        (∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T) →
        Commutes K K₂ → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N) →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₂) →
        ∃ Us : Subgroup G, Us ≤ ⁅Us, Us⁆ ∧ Commutes K Us ∧
          Us ≤ Subgroup.centralizer ({t} : Set G) ∧
          ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W K₂ Us

theorem chainPiece3TwinSU4_of_inputs (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3)
    (hL : TwinLinked3) (hS : TwinSU4ShortNode3) : Q3TS.ChainPiece3TwinSU4 := by
  intro G _ _ _ hnab K z hR hshape
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hadmU : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨c⟩ := nonempty_tctxS3 yData3S_psu4 h3 hR hshape
  obtain ⟨T₁, hT₁, hT₁img⟩ := c.exists_twin
  have hT₁K : T₁ ≠ K := c.twin_ne hT₁ hT₁img.le
  have hT₁comm : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T₁ → Commutes T₁ N :=
    fun N hN hNT => c.commutes_T_of_ne hT₁ hT₁img.le hN hNT
  obtain ⟨R₀, hR₀, R₁, hR₁, hR₀₁, hnc⟩ := exists_noncommuting_fund_psu4
  obtain ⟨K₂, hK₂, hK₂K, hK₂Q, hK₂img⟩ := c.exists_member_of_fund hR₀
  obtain ⟨K₂', hK₂', -, -, hK₂'img⟩ := c.exists_member_of_fund hR₁
  have hK₂T : K₂ ≠ T₁ := by
    rintro rfl
    exact hK₂Q hT₁img.le
  have hne : K₂' ≠ K₂ := by
    rintro rfl
    exact hR₀₁ (Q3W.eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 R₀ hR₀)
      (c.hY.pow3 R₁ hR₁) (hK₂img.symm.trans hK₂'img))
  have hnotcomm : ¬ Commutes K₂ K₂' := fun h =>
    hnc ((c.commutes_iff_fund hK₂ hK₂' hR₀ hK₂img hK₂'img).mp h)
  have hnotTwin : ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T := by
    rintro T hT rfl
    exact hnotcomm (hT.comm_T K₂' hK₂' hne)
  obtain ⟨w, hw⟩ := hR.inClass.classical K₂ hK₂.1
  have hzw : z ≠ w := by
    rintro rfl
    exact not_locImg_eq_map_fund3S c.hY hK₂ hw c.d.ψ c.d.ker_le hR₀ hK₂img
  have hKK₂ : Commutes K K₂ := c.commutes_K_of_ne hK₂ hK₂K
  obtain ⟨hP1x, hO3x⟩ := hP G K z hR K₂ hK₂.1 w hw hKK₂ hzw
  have hlink := hL G hnab K z hR .PSU 4 (Or.inr ⟨rfl, rfl⟩) hshape K₂ hK₂ hK₂K hnotTwin w hw
  obtain ⟨-, N, hN, p1, p2⟩ := exists_chain_of_twin_product3 h3 hnab hR hT₁ hT₁K hT₁comm hK₂ hK₂K
    hK₂T hw hzw hP1x hO3x hlink
  obtain ⟨t, ht⟩ := hR.inClass.classical N hN.1
  obtain ⟨Us, hUsp, hKUs, hUst, hsp⟩ := hS G hnab K z hR hshape N K₂ t hN.1 ht hK₂ hK₂K hnotTwin
    hKK₂ p1 p2
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  have : Finite ι := hι
  have hD : Nat.card ι ≤ 4 := by omega
  have hNUs : Commutes N Us := commutes_partner_of_perfect3S c (Gaps.fundNoncentral 3) hsingle D hD
    hN.1 ht (le_antisymm (commutator_self_le _) hUsp) hUst
  refine ⟨![K, N, K₂, Us], ?_, ?_, ?_, ?_⟩
  · exact hKΩ
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact hKK₂
      | exact hKUs
      | exact hNUs
  · intro i j hij hj
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact absurd hj (by decide)
      | exact p1
      | exact p2
  · intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hi (by decide)
      | exact absurd hj (by decide)
      | exact hsp

theorem piece3TwinSU4_of_inputs (h3 : OddThreeFreeInput) (hW : Q3TW.WeakCT3MinusMap 5)
    (hP : Q3TC.ProductP1Input3) (hL : TwinLinked3) (hS : TwinSU4ShortNode3) : Piece3TwinSU4 :=
  Q3TS.piece3TwinSU4_of_chain h3 hW (chainPiece3TwinSU4_of_inputs h3 hP hL hS)

end Chain

end CFSG.ClassicalInvolution.Q3.Q3TY
