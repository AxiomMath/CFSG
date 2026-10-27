module

public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCModel
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Omega

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaNbr_of_sylow_le_centralizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J R : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K)
    {z : G} (hz : IsUniqueInvolution K z) (hR : IsSylow2In R J) (hRset : R ∈ RSet Ω)
    (hRc : R ≤ Subgroup.centralizer ({z} : Set G)) : J ∈ omegaNbr Ω K := by
  have h8 := hΩ.eight_le_of_mem_RSet hp hRset
  exact ⟨hJ, hne, R, hRset, hR.1, hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hne.symm hz hR.1
    hR.2.1 (by omega) hRc⟩

end Omega

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

namespace ChainCtx

include C

theorem exists_conj_eq_of_commutes (h3 : C.D.rank C.i₁ = 3) (hIn : InClass p f Ω)
    (hex : ExactMembers Ω) (hp1 : LocalOddCentral Ω {z}) (hT : ∀ J ∈ twinSet Ω C.K, J = C.K)
    {M : Subgroup G} (hM : M ∈ Ω) {w : G} (hw : IsClassicalMember p f M w)
    (hKM : Commutes C.K M) (hzw : z ≠ w) {N : Subgroup G} (hN : N ∈ centMembers Ω (z * w))
    (hcomm : ∀ k ∈ C.K, ∀ n ∈ N,
      k * n * k⁻¹ * n⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z * w} : Set G))) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({z * w} : Set G)),
      conjSub o N = C.K ∨ conjSub o N = M := by
  classical
  have hzK : z ∈ C.K := C.hKz.mem
  have hwM : w ∈ M := hw.mem
  have hzwc : z * w = w * z := hKM z hzK w hwM
  have hz2 : z * z = 1 := C.hKz.sq
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨x, hx⟩ : ∃ x, x = z * w := ⟨_, rfl⟩
  rw [← hx] at hN hcomm ⊢
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hx]
    calc z * (z * w) = z * (w * z) := by rw [hzwc]
      _ = z * w * z := by rw [mul_assoc]
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  set O := oddCoreIn Cx with hO
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn Cx
  obtain ⟨R, hRset, hRN, -⟩ := exists_mem_RSet_ge hN.1
    (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have hRC : ∀ y ∈ R, y ∈ Cx := fun y hy => hN.2 (hRN.1 hy)
  obtain ⟨n, hnO, hfix⟩ := exists_conj_fixed_of_isPGroup (A := R) (N := O) hRN.2.1 hOodd
    (fun y hy m hm => conj_mem_oddCoreIn (hRC y hy) hm) hz2
    (fun m hm => conj_mem_oddCoreIn hzx hm)
    (fun y hy => by
      have h1 := hcomm z hzK y (hRN.1 hy)
      rw [hzinv] at h1
      simpa [mul_assoc] using h1)
  have hnC : n ∈ Cx := oddCoreIn_le _ hnO
  have hoO : n⁻¹ ∈ O := O.inv_mem hnO
  refine ⟨n⁻¹, hoO, ?_⟩
  set N' := conjSub n⁻¹ N with hN'
  have hN'Ω : N' ∈ Ω := hIn.conjInvariant n⁻¹ N hN.1
  have hN'x : N' ≤ Cx := by
    intro y hy
    have h1 : n * y * n⁻¹ ∈ N := by
      have := mem_conjSub_iff.mp hy
      simpa using this
    have h2 : n * y * n⁻¹ ∈ Cx := hN.2 h1
    have e : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnC) h2) hnC
  have hR'syl : IsSylow2In (conjSub n⁻¹ R) N' := IsSylow2In.conj hRN n⁻¹
  have hR'set : conjSub n⁻¹ R ∈ RSet Ω := mem_RSet_of_isSylow2In hN'Ω hR'syl
  have hR'z : conjSub n⁻¹ R ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    have h1 : n * y * n⁻¹ ∈ R := by
      have := mem_conjSub_iff.mp hy
      simpa using this
    have e1 : (n * y * n⁻¹) * (n * z * n⁻¹) = (n * z * n⁻¹) * (n * y * n⁻¹) := by
      have := hfix _ h1
      calc (n * y * n⁻¹) * (n * z * n⁻¹)
          = ((n * y * n⁻¹) * (n * z * n⁻¹) * (n * y * n⁻¹)⁻¹) * (n * y * n⁻¹) := by group
        _ = (n * z * n⁻¹) * (n * y * n⁻¹) := by rw [this]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * z = n⁻¹ * ((n * y * n⁻¹) * (n * z * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * z * n⁻¹) * (n * y * n⁻¹)) * n := by rw [e1]
      _ = z * y := by group
  by_cases hN'K : N' = C.K
  · exact Or.inl hN'K
  right
  have hN'nbr : N' ∈ omegaNbr Ω C.K :=
    mem_omegaNbr_of_sylow_le_centralizer C.hp C.hq C.hΩ C.hK hN'Ω hN'K C.hKz hR'syl hR'set hR'z
  have hKN' : Commutes C.K N' :=
    AscE186.commutes_of_mem_omegaNbr C.hp C.hq (C.hΩ.toExact hex) C.hK hN'nbr
  have hN'z : N' ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKN' z hzK y hy).symm
  have hN'w : N' ≤ Subgroup.centralizer ({w} : Set G) := by
    intro y hy
    have h1 : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hN'z hy)
    have h2 : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hN'x hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw' : w = z * x := by
      rw [hx, ← mul_assoc, hz2, one_mul]
    rw [hw']
    calc y * (z * x) = (y * z) * x := by rw [mul_assoc]
      _ = (z * y) * x := by rw [h1]
      _ = z * (y * x) := by rw [mul_assoc]
      _ = z * (x * y) := by rw [h2]
      _ = z * x * y := by rw [mul_assoc]
  by_contra hN'M
  have hMw : IsUniqueInvolution M w :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hw
  have hMN'nbr : N' ∈ omegaNbr Ω M :=
    AscE186.mem_omegaNbr_of_le_centralizer C.hp C.hq C.hΩ hM hN'Ω hN'M hMw hN'w
  have hMN' : Commutes M N' :=
    AscE186.commutes_of_mem_omegaNbr C.hp C.hq (C.hΩ.toExact hex) hM hMN'nbr
  have hMz : M ≤ Subgroup.centralizer ({z} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKM z hzK m hm).symm
  have hMK : M ≠ C.K := by
    intro h
    apply hzw
    have : IsUniqueInvolution C.K w := h ▸ hMw
    exact C.hKz.eq this
  exact C.not_commutes_pair h3 hIn hex hp1 hT ⟨hM, hMz⟩ ⟨hN'Ω, hN'z⟩ hMK hN'K (Ne.symm hN'M)
    hMN'

theorem cover_two [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (h3 : C.D.rank C.i₁ = 3)
    (hIn : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hp1 : LocalOddCentral Ω {z}) (hT : ∀ J ∈ twinSet Ω C.K, J = C.K) {M : Subgroup G}
    (hM : M ∈ Ω) {w : G} (hw : IsClassicalMember p f M w) (hKM : Commutes C.K M) (hzw : z ≠ w) :
    ∀ N ∈ centMembers Ω (z * w),
      InCommonComponent (z * w) N C.K ∨ InCommonComponent (z * w) N M := by
  classical
  have hzK : z ∈ C.K := C.hKz.mem
  have hwM : w ∈ M := hw.mem
  have hz2 : z * z = 1 := C.hKz.sq
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hx1 : z * w ≠ 1 := by
    intro h
    apply hzw
    rw [eq_inv_of_mul_eq_one_right h]
    exact (inv_eq_of_mul_eq_one_right hz2).symm
  have hnc : ¬ ({z * w} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hx1
  have hcent : ∀ {L : Subgroup G} {a b : G}, L ≤ Subgroup.centralizer ({a} : Set G) →
      L ≤ Subgroup.centralizer ({b} : Set G) → L ≤ Subgroup.centralizer ({a * b} : Set G) := by
    intro L a b ha hb y hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (ha hy)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hb hy)
    rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have hKx : C.K ∈ centMembers Ω (z * w) :=
    ⟨C.hK, hcent (le_centralizer_of_isClassicalMember hKcl) fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hKM k hk w hwM)⟩
  have hMx : M ∈ centMembers Ω (z * w) :=
    ⟨hM, hcent (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hKM z hzK m hm).symm)
      (le_centralizer_of_isClassicalMember hw)⟩
  have := memberJoin_normal (a := z * w) hIn.conjInvariant
  obtain ⟨D⟩ := lieDecomposition_memberImages C.hp ModelFacts.modelClauseZero
    fundamentalWholeA1 hIn hIH hnc
  have hQ : ∀ i, CFSG.IsComponent (D.Q i) := fun i =>
    (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i)
  obtain ⟨a, ha⟩ := D.exists_le _ (⟨C.K, hKx, rfl⟩ : modOdd (z * w) C.K ∈ memberImages Ω (z * w))
  obtain ⟨b, hb⟩ := D.exists_le _ (⟨M, hMx, rfl⟩ : modOdd (z * w) M ∈ memberImages Ω (z * w))
  intro N hN
  by_cases hNK : InCommonComponent (z * w) N C.K
  · exact Or.inl hNK
  right
  have hcomm := Balance.Theorem5.comm_mem_oddCoreIn_of_not_inCommonComponent C.hp hIn hIH hnc
    hKx hN (fun ⟨Q, hQc, h1, h2⟩ => hNK ⟨Q, hQc, h2, h1⟩)
  obtain ⟨o, ho, hcases⟩ :=
    C.exists_conj_eq_of_commutes h3 hIn hex hp1 hT hM hw hKM hzw hN hcomm
  have himg : modOdd (z * w) (conjSub o N) = modOdd (z * w) N :=
    modOdd_conjSub_of_mem_oddCoreIn ho
  rcases hcases with h | h
  · exfalso
    apply hNK
    refine ⟨D.Q a, hQ a, ?_, ha⟩
    rw [← himg, h]
    exact ha
  · refine ⟨D.Q b, hQ b, ?_, hb⟩
    rw [← himg, h]
    exact hb

end ChainCtx

end Local

end CFSG.ClassicalInvolution.Asc77
