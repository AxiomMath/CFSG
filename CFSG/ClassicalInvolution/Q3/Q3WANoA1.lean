module

public import CFSG.ClassicalInvolution.Q3.Q3WARoot
public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

theorem center_m11_eq_bot : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := by
  have : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := isSimpleGroup_m11_kernel
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11) with h | h
  · exact h
  · exfalso
    let a : ↥CFSG.Blueprint.NativeSporadic.M11 :=
      ⟨_, Subgroup.subset_closure (Set.mem_insert _ _)⟩
    let b : ↥CFSG.Blueprint.NativeSporadic.M11 :=
      ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    have ha : a ∈ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := h ▸ Subgroup.mem_top a
    have hab := congrArg (fun x : ↥CFSG.Blueprint.NativeSporadic.M11 =>
      ((x : Equiv.Perm (Fin 11)) 0 : ℕ)) (Subgroup.mem_center_iff.mp ha b)
    revert hab
    decide

section Local

variable {G : Type} [Group G]

theorem mk_involution_central3 (Ω : Set (Subgroup G)) (z : G) (hz : z ∈ locLayer Ω z)
    (w : locQuot Ω z) :
    w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hz⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hz⟩ * w := by
  obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} w'.2)

theorem mk_involution_ne_one3 [Finite G] (Ω : Set (Subgroup G)) {z : G} (h2 : orderOf z = 2)
    (hz : z ∈ locLayer Ω z) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hz⟩ ≠ 1 := by
  intro h
  have hO : (⟨z, hz⟩ : ↥(locLayer Ω z)) ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
    (QuotientGroup.eq_one_iff _).mp h
  have h3 : orderOf (⟨z, hz⟩ : ↥(locLayer Ω z)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have h4 : orderOf (⟨⟨z, hz⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h3
  have h5 := orderOf_dvd_natCard (⟨⟨z, hz⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
  rw [h4] at h5
  have := CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z))
  exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h5)

end Local

section Top

variable {G : Type} [Group G]

theorem commutes_self_of_locImg_top3 {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    (hP1 : LocalOddCentral Ω {z}) (htop : locImg Ω z K = ⊤) {L : Subgroup G}
    (hL : L ≤ locLayer Ω z) (hKL : Commutes K L) : Commutes L L := by
  intro l₁ hl₁ l₂ hl₂
  let a₁ : ↥(locLayer Ω z) := ⟨l₁, hL hl₁⟩
  let a₂ : ↥(locLayer Ω z) := ⟨l₂, hL hl₂⟩
  have hm : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) a₁ ∈
      locImg Ω z K := by
    rw [htop]
    trivial
  obtain ⟨b, hb, hba⟩ := hm
  have hb' : (b : G) ∈ K := Subgroup.mem_subgroupOf.mp hb
  have ho : b⁻¹ * a₁ ∈ classicalInvolutionOddCore ↥(locLayer Ω z) := QuotientGroup.eq.mp hba
  have hoc : b⁻¹ * a₁ ∈ Subgroup.center ↥(locLayer Ω z) := hP1 ho
  have hbc : b * a₂ = a₂ * b := Subtype.ext (hKL b hb' l₂ hl₂)
  have hcc : a₂ * (b⁻¹ * a₁) = (b⁻¹ * a₁) * a₂ := Subgroup.mem_center_iff.mp hoc a₂
  have e1 : a₁ = b * (b⁻¹ * a₁) := by group
  have h1 : a₁ * a₂ = a₂ * a₁ := by
    calc a₁ * a₂ = (b * (b⁻¹ * a₁)) * a₂ := by rw [← e1]
      _ = b * ((b⁻¹ * a₁) * a₂) := by rw [mul_assoc]
      _ = b * (a₂ * (b⁻¹ * a₁)) := by rw [hcc]
      _ = (b * a₂) * (b⁻¹ * a₁) := by rw [← mul_assoc]
      _ = (a₂ * b) * (b⁻¹ * a₁) := by rw [hbc]
      _ = a₂ * (b * (b⁻¹ * a₁)) := by rw [mul_assoc]
      _ = a₂ * a₁ := by rw [← e1]
  exact congrArg Subtype.val h1

theorem false_of_locImg_top3 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) (hconn : RouteD.DeltaConnected Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z})
    (htop : locImg Ω z K = ⊤) : False := by
  have hsub : Ω ⊆ {K} := by
    refine subset_of_adj_closed hconn (𝔖 := {K}) (Set.singleton_subset_iff.mpr hK)
      (Set.singleton_nonempty K) ?_
    intro N hN L hL hLN hNL
    rw [Set.mem_singleton_iff] at hN
    subst hN
    exfalso
    have hLz : L ≤ Subgroup.centralizer ({z} : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hNL z hz.mem l hl).symm
    have hLY : L ≤ locLayer Ω z := le_centralizingLayer ⟨hL, hLz⟩
    obtain ⟨w, hw⟩ := hΩ.classical L hL
    exact not_commutes_self3 hw (commutes_self_of_locImg_top3 hP1 htop hLY hNL)
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hΩ.generated]
    exact iSup₂_le fun L hL => by rw [Set.mem_singleton_iff.mp (hsub hL)]
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ K := by rw [hKtop]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hz.subnormal hg)
  rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hzc
  have h2 := hz.orderOf_eq_two
  rw [hzc, orderOf_one] at h2
  omega

end Top


theorem eq_one_of_central_comp3 (hMFZ : RouteD.Gaps.FundNoncentral 3) {X : Type} [Group X]
    (c : CompData) (hv : c.Valid) (hc : c ≠ CompData.sl23) (φ : c.G →* X)
    (hker : φ.ker ≤ Subgroup.center c.G) {R : Subgroup c.G} (hR : R ∈ c.fund) {r : c.G}
    (hr : r ∈ R) (hcent : ∀ y : c.G, φ r * φ y = φ y * φ r) : r = 1 := by
  have hcomm : ∀ y : c.G, r * y * r⁻¹ * y⁻¹ ∈ φ.ker := by
    intro y
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc φ r * φ y * (φ r)⁻¹ * (φ y)⁻¹ = (φ y * φ r) * (φ r)⁻¹ * (φ y)⁻¹ := by rw [hcent y]
      _ = 1 := by group
  rcases hv with ⟨t, n, hft, hadm, rfl⟩ | rfl | rfl
  · have hpsl : ¬ (t = .PSL ∧ n = 2) := by
      rintro ⟨rfl, rfl⟩
      obtain ⟨-, -, -, -, h⟩ := hadm
      exact h (by norm_num)
    exact hMFZ t n 1 hft hadm hpsl R hR r hr fun y => hker (hcomm y)
  · exact absurd rfl hc
  · have h1 : r ∈ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := hker (hcomm y)
      rw [center_m11_eq_bot, Subgroup.mem_bot] at h
      calc y * r = (r * y * r⁻¹ * y⁻¹)⁻¹ * (r * y) := by group
        _ = r * y := by rw [h, inv_one, one_mul]
    rw [center_m11_eq_bot, Subgroup.mem_bot] at h1
    exact h1

theorem shapePiece3_zero_of_mfz (hMFZ : RouteD.Gaps.FundNoncentral 3) (c : CompData) :
    ShapePiece3 0 c := by
  intro G _ _ _ hnab K z hR hshape
  exfalso
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := hshape
  have hsub : Subsingleton ι :=
    (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1
  obtain ⟨hex, hP1⟩ := hR.setup
  have hΩ := hR.inClass
  have hz := hR.cls
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hmem : locImg (conjClass3 K) z K ∈ locFamily (conjClass3 K) z :=
    mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  obtain ⟨i, R, hRf, hRK⟩ := D.fundamental _ hmem
  have hzY : z ∈ locLayer (conjClass3 K) z := le_centralizingLayer hKz hz.mem
  have hxK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z))
      ⟨z, hzY⟩ ∈ locImg (conjClass3 K) z K := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  rw [hRK] at hxK
  obtain ⟨r, hrR, hr⟩ := hxK
  by_cases hc : D.kind i = CompData.sl23
  ·
    have hRtop : R = ⊤ := by
      have key : ∀ c' : CompData, c' = CompData.sl23 → ∀ R' : Subgroup c'.G, R' ∈ c'.fund →
          R' = ⊤ := by
        rintro c' rfl R' hR'
        exact hR'
      exact key _ hc R hRf
    have hrange : (D.hom i).range = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← D.generate]
      refine iSup_le fun j => ?_
      obtain rfl : j = i := Subsingleton.elim j i
      exact le_rfl
    have htop : locImg (conjClass3 K) z K = ⊤ := by
      rw [hRK, hRtop, Subgroup.map_top, hrange]
    exact false_of_locImg_top3 hnab hΩ ((CoreAssembly.deltaConnected_iff K).mp hR.conn) hK hz hP1
      htop
  ·
    have hr1 : r = 1 :=
      eq_one_of_central_comp3 hMFZ (D.kind i) (D.valid i) hc (D.hom i) (D.ker_le_center i) hRf hrR
        fun y => by
          rw [hr]
          exact (mk_involution_central3 (conjClass3 K) z hzY (D.hom i y)).symm
    rw [hr1, map_one] at hr
    exact mk_involution_ne_one3 (conjClass3 K) hz.orderOf_eq_two hzY hr.symm

theorem pieceNoA1₃_of_mfz (hMFZ : RouteD.Gaps.FundNoncentral 3) : PieceNoA1₃ :=
  fun t n => shapePiece3_zero_of_mfz hMFZ (CompData.model t n)

section Unconditional


theorem shapePiece3_zero (c : CompData) : ShapePiece3 0 c :=
  shapePiece3_zero_of_mfz (RouteD.Gaps.fundNoncentral 3) c

theorem pieceNoA1₃ : PieceNoA1₃ :=
  pieceNoA1₃_of_mfz (RouteD.Gaps.fundNoncentral 3)

end Unconditional

end CFSG.ClassicalInvolution.Q3.Q3W
