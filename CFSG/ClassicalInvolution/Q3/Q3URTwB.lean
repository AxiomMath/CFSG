module

public import CFSG.ClassicalInvolution.Q3.Q3URTwA
public import CFSG.ClassicalInvolution.Q3.Q3URThree1
public import CFSG.ClassicalInvolution.Q3.Q3WASTInner
public import CFSG.ClassicalInvolution.Q3.Q3URDict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (conjSign)
open scoped MatrixGroups

section Layer

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.conjSub_eq_of_commute_roots (c : UCtx3 m Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i i' : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ)
    (hcomm : Commute i i') {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    conjSub w L' = L' := by
  have hwY : w ∈ locLayer Ω z := le_centralizingLayer hL hw
  have hψi : c.d.ψ i = locMk Ω z ⟨w, hwY⟩ :=
    psiU_root_inv3 c.hm c.d hRi hLR (le_centralizingLayer hL) hw hw2
  have hle : conjSub i R' ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hRi'.eq_longRootGroupSU two_ne_zero_gf9] at hy ⊢
    exact conj_mem_longRootGroupSU_of_commute (typeU_suMat_commute hcomm) hy
  have hnormR : conjSub i R' = R' := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj i).injective]
  have himg : locImg Ω z (conjSub w L') = locImg Ω z L' := by
    have h := locImg_conjSub_layer (Ω := Ω) (x := z) L' ⟨w, hwY⟩
    rw [show ((⟨w, hwY⟩ : ↥(locLayer Ω z)) : G) = w from rfl] at h
    rw [h, hLR', ← hψi]
    have h' := map_conjSub_hom3 c.d.ψ i R'
    rw [hnormR] at h'
    exact h'.symm
  have hmem : conjSub w L' ∈ centralizingMembers Ω {z} := by
    refine ⟨c.hΩ.conjInvariant w L' hL'.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hL'.2 ha
    have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := hL.2 hw
    have : a = w * (w⁻¹ * a * w) * w⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hwC hx') (inv_mem hwC)
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hmem hL' himg

end Layer

section LayerDich

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem UCtx3.layer_dichotomy {J : Subgroup G} {w : G} (c : UCtx3 2 Ω J w) {K : Subgroup G}
    {z : G} (hK : K ∈ centralizingMembers Ω {w}) (hKJ : K ≠ J) (hz : IsClassicalMember3 K z)
    {t : G} (ht1 : t * w * t⁻¹ = w) (ht2 : t * t = 1)
    (htK : K ≤ Subgroup.centralizer ({t} : Set G)) (_htJ : conjSub t J = J) :
    (∀ N ∈ centralizingMembers Ω {w}, N ≠ J → N ≤ Subgroup.centralizer ({t} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {w}, N ≠ J →
        N ≤ Subgroup.centralizer ({t * z} : Set G)) := by
  classical
  obtain ⟨R, i, hRi, hKR, hψi⟩ := c.exists_rootData hK hKJ hz
  obtain ⟨g, hRg, hig⟩ := hRi
  obtain ⟨θ, hθ⟩ : ∃ θ : Su (GaloisField 3 2) 3 1 (2 + 1) →* locQuot Ω w,
      θ = c.d.ψ.comp (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hθx : ∀ x, θ x = c.d.ψ (g * x * g⁻¹) := fun x => by rw [hθ]; rfl
  have hθker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (2 + 1)) := by
    rw [hθ]
    exact ker_comp_conj_le_center c.d.ψ c.d.ker_le g
  have hθrange : θ.range = c.d.ψ.range := by
    rw [hθ]
    exact range_comp_conj c.d.ψ g
  have hψθ : ∀ r, c.d.ψ r ∈ θ.range := fun r => by
    rw [hθrange]
    exact ⟨r, rfl⟩
  set σ := locAut c.hΩ.conjInvariant ht1 with hσdef
  have hσσ : ∀ a, σ (σ a) = a := locAut_locAut c.hΩ.conjInvariant ht1 ht2
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hstabψ : ∀ x, σ (c.d.ψ x) ∈ c.d.ψ.range := c.locAut_stab nd ht1
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x => by
    rw [hθrange, hθx]
    exact hstabψ _
  have hfix : ∀ A : Su (GaloisField 3 2) 3 1 2,
      σ (θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A)) =
        θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A) := by
    intro A
    have hmem : θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A) ∈ locImg Ω w K := by
      rw [hKR, hθx]
      refine ⟨g * blockEmb2 (GaloisField 3 2) 3 1 2 0 A * g⁻¹, ?_, rfl⟩
      rw [hRg]
      exact ⟨blockEmb2 (GaloisField 3 2) 3 1 2 0 A, ⟨A, rfl⟩, rfl⟩
    exact ((locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht1 hK).mp htK) _ hmem
  obtain ⟨ε, hσθ⟩ := innerDiag_three_su3 card_gf9 (by norm_num) le_rfl
    su2_pow_three_mem_commutator (fun x hx => center_orderOf_not_dvd_three_su3 (by omega) hx) θ
    hθker σ hσσ hstab hfix
  have hlocal : ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → ∀ a ∈ locImg Ω w N,
      ∃ x, a = θ x := by
    intro N hN hNJ a ha
    obtain ⟨zN, hzN⟩ := c.hΩ.classical N hN.1
    obtain ⟨R', i', -, hR', -⟩ := c.exists_rootData hN hNJ hzN
    rw [hR'] at ha
    obtain ⟨r, -, rfl⟩ := ha
    obtain ⟨x, hx⟩ := hψθ r
    exact ⟨x, hx.symm⟩
  have hε : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases hε ε with rfl | rfl
  · left
    intro N hN hNJ
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht1 hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    exact (hσθ x).trans (by rw [conjSign_twoOneSigns_zero])
  · right
    intro N hN hNJ
    have hzY : z ∈ locLayer Ω w := le_centralizingLayer hK hz.mem
    have hzw : z * w * z⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hK.2 hz.mem)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have htz : (t * z) * w * (t * z)⁻¹ = w := by
      calc (t * z) * w * (t * z)⁻¹ = t * (z * w * z⁻¹) * t⁻¹ := by group
        _ = w := by rw [hzw, ht1]
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    rw [locAut_mul3 c.hΩ.conjInvariant ht1 hzw htz, locAut_eq_conj3 c.hΩ.conjInvariant hzY hzw]
    have hzbar : locMk Ω w ⟨z, hzY⟩ = θ (rootInvSU (GaloisField 3 2) 3 1 c.hn) := by
      rw [hθx]
      have : g * rootInvSU (GaloisField 3 2) 3 1 c.hn * g⁻¹ = i := by rw [hig]
      rw [this]
      exact hψi.symm
    rw [hzbar, ← map_inv, ← map_mul, ← map_mul]
    show σ (θ _) = _
    rw [hσθ, conjSign_twoOneSigns_one]

end LayerDich

section Member


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_uctx3_member (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K : Subgroup G}
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember3 K z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (hshape : LocalShapeC3 1 (CompData.model .PSU (2 + 1)) Ω z) {J : Subgroup G} {w : G}
    (hJ : J ∈ Ω) (hw : IsClassicalMember3 J w) : Nonempty (UCtx3 2 Ω J w) := by
  obtain ⟨g, hg⟩ := hsingle J hJ
  have hw' : w = g * z * g⁻¹ := involution_unique3 hw (hg ▸ hz.conj g)
  subst hw'
  have hshape' := hshape.conjShape3 hΩ.conjInvariant g
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictU (m := 2) (by omega) hΩ hJ hw hshape'
  exact ⟨{ hm := le_rfl
           hΩ := hΩ
           hex := hex
           hK := hJ
           hz := hw
           hP1 := localOddCentral_conj hΩ.conjInvariant g z hP1
           hO3 := localOddThreeFree3_conj hΩ.conjInvariant g z hO3
           d := d
           hlift := Or.inl (by omega) }⟩

end Member

end CFSG.ClassicalInvolution.Q3.Q3W
