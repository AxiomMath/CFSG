module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNBarA
public import CFSG.GH74.GLS.C3.Layer1.Th2L627N

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.IV26
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem mem_normalizer_of_mem_centralizer
    (hr4 : pRank 2 G ≤ 4) {x : G} {K : Subgroup G} (hxK : IsIL2Pair x K)
    (hL : HasL2Model (kBar K) Odd) {c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    c ∈ normalizer (K : Set G) := by
  have hnorm := Th2.L625.normal_of_pRank_le_four hr4 hxK hL
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨hnorm c hc k, fun hk => ?_⟩
  have := hnorm c⁻¹ (inv_mem hc) _ hk
  simpa [mul_assoc] using this

theorem hform_Mb
    (hr4 : pRank 2 G ≤ 4) {x : G} {K : Subgroup G} (hxK : IsIL2Pair x K)
    (hL : HasL2Model (kBar K) Odd) (h1 : pRank 2 ↥(CxK x K) ≤ 1) (hxM : x ∈ M) (hKM : K ≤ M) :
    ∀ u : Mb M, orderOf u = 2 → (∀ k ∈ imgM M K, u * k = k * u) →
      u * eb M hxM = eb M hxM * u → u = eb M hxM := by
  intro u hu2 huK hux
  have hx2 : orderOf x = 2 := hxK.1
  obtain ⟨g, hgM, hgx, hg2, hgu⟩ := exists_involution_lift hxM hx2 hu2 hux
  have hgC : g ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hgx
  have hnorm := Th2.L625.normal_of_pRank_le_four hr4 hxK hL
  have hgK : g ∈ normalizer (K : Set G) := mem_normalizer_of_mem_centralizer hr4 hxK hL hgC
  have hgO : g ∈ normalizer (pPrimeCoreOf 2 K : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf hgK
  have hcomm : ∀ k ∈ K, ⁅k, g⁆ ∈ pPrimeCoreOf 2 K := by
    intro k hk
    have hkM : k ∈ M := hKM hk
    have hkg : ⁅k, g⁆ ∈ K := by
      have h1' : g * k⁻¹ * g⁻¹ ∈ K := by
        have := hnorm g hgC k⁻¹ (inv_mem hk)
        exact this
      rw [commutatorElement_def]
      have : k * g * k⁻¹ * g⁻¹ = k * (g * k⁻¹ * g⁻¹) := by group
      rw [this]
      exact K.mul_mem hk h1'
    have hkgM : ⁅k, g⁆ ∈ M := hKM hkg
    have hbar : barMk ↥M ⟨⁅k, g⁆, hkgM⟩ = 1 := by
      have e : (⟨⁅k, g⁆, hkgM⟩ : ↥M) = ⁅(⟨k, hkM⟩ : ↥M), (⟨g, hgM⟩ : ↥M)⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [e, map_commutatorElement, hgu]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (huK _ (mem_imgM_iff.2 ⟨⟨k, hkM⟩, hk, rfl⟩)).symm
    have hmem : ⁅k, g⁆ ∈ pPrimeCoreOf 2 M :=
      (barMk_eq_one_iff_mem_pPrimeCoreOf (M := M) ⟨⁅k, g⁆, hkgM⟩).1 hbar
    exact Th2.inf_le_pPrimeCoreOf hKM ⟨hmem, hkg⟩
  have hgD : g ∈ CxK x K := ⟨hgC, hgK, hgO, hcomm⟩
  have hxD : x ∈ CxK x K := hxK.x_mem_CxK
  by_contra hne
  have hgx' : g ≠ x := by
    intro h
    apply hne
    rw [← hgu]
    subst h
    rfl
  have := C3.Layer1.U1a.two_le_pRank_of_commute hgD hxD hg2 hx2 hgx hgx'
  omega


theorem unbal_Mb
    (hr4 : pRank 2 G ≤ 4) {x y : G} {K : Subgroup G} (hxK : IsIL2Pair x K)
    (hL : HasL2Model (kBar K) Odd) (hxM : x ∈ M) (hyM : y ∈ M) (hy2 : orderOf y = 2) (hKM : K ≤ M)
    (hW : ¬ (pPrimeCoreOf 2 (centralizer ({y} : Set G) ⊓ M) ⊓ centralizer ({x} : Set G) ≤
      centralizerSection K (pPrimeCoreOf 2 K))) :
    ¬ (pPrimeCoreOf 2 (centralizer ({eb M hyM} : Set (Mb M))) ⊓
        centralizer ({eb M hxM} : Set (Mb M)) ≤
      centralizerSection (imgM M K) (pPrimeCoreOf 2 (imgM M K))) := by
  intro hX
  apply hW
  rintro w ⟨hwO, hwC⟩
  have hwH : w ∈ centralizer ({y} : Set G) ⊓ M := TwoThin.pPrimeCoreOf_le _ hwO
  have hwM : w ∈ M := hwH.2
  have hwb1 : barMk ↥M ⟨w, hwM⟩ ∈ pPrimeCoreOf 2 (centralizer ({eb M hyM} : Set (Mb M))) :=
    barMk_mem_pPrimeCoreOf_centralizer hyM hy2 hwO hwM
  have hwb2 : barMk ↥M ⟨w, hwM⟩ ∈ centralizer ({eb M hxM} : Set (Mb M)) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hwC)
  have hsec := hX ⟨hwb1, hwb2⟩
  have hwK : w ∈ normalizer (K : Set G) := mem_normalizer_of_mem_centralizer hr4 hxK hL hwC
  have hwO' : w ∈ normalizer (pPrimeCoreOf 2 K : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf hwK
  refine ⟨hwK, hwO', fun k hk => ?_⟩
  have hkM : k ∈ M := hKM hk
  have hkw : ⁅k, w⁆ ∈ K := by
    have h1 : w * k⁻¹ * w⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 hwK k⁻¹).1 (inv_mem hk)
      exact this
    rw [commutatorElement_def]
    have : k * w * k⁻¹ * w⁻¹ = k * (w * k⁻¹ * w⁻¹) := by group
    rw [this]
    exact K.mul_mem hk h1
  have hkwM : ⁅k, w⁆ ∈ M := hKM hkw
  have hcomm := hsec.2.2 (barMk ↥M ⟨k, hkM⟩) (mem_imgM_iff.2 ⟨⟨k, hkM⟩, hk, rfl⟩)
  refine mem_pPrimeCoreOf_of_barMk_mem hKM hkw ?_
  have e : (⟨⁅k, w⁆, hkwM⟩ : ↥M) = ⁅(⟨k, hkM⟩ : ↥M), (⟨w, hwM⟩ : ↥M)⁆ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_commutatorElement]
  exact hcomm

theorem rank_facts {S : Subgroup G} {x : G} (hr4 : pRank 2 G = 4) (hxM : x ∈ M) (hSM : S ≤ M)
    (hT : IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)))
    (hstar : IsStar2 x) :
    4 ≤ pRank 2 ↥(centralizer ({eb M hxM} : Set (Mb M))) ∧
      pRank 2 ↥(centralizer ({x} : Set G) ⊓ M) = pRank 2 ↥M := by
  have hTrank : pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) = pRank 2 G := by
    rw [pRank_eq_of_isSylowOf hT]
    exact hstar.2
  obtain ⟨A, hAT, hA⟩ := exists_isEStar_le hTrank
  have hAS : A ≤ S := hAT.trans inf_le_left
  have hAC : A ≤ centralizer ({x} : Set G) := hAT.trans inf_le_right
  have hAM : A ≤ M := hAS.trans hSM
  have hcard : Nat.card ↥A = 2 ^ 4 := by rw [hA.2, hr4]
  have hAp : IsPGroup 2 ↥A := by
    have := hA.1
    exact IsElementaryAbelian.isPGroup 2 ↥A
  constructor
  · obtain ⟨e⟩ := equiv_imgM hAM hAp
    have hel : CFSG.IsElementaryAbelian 2 ↥(imgM M A) := isElementaryAbelian_of_mulEquiv' e.symm hA.1
    have hcardb : Nat.card ↥(imgM M A) = 2 ^ 4 := by rw [← Nat.card_congr e.toEquiv]; exact hcard
    have hle : imgM M A ≤ centralizer ({eb M hxM} : Set (Mb M)) := by
      intro v hv
      obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hv
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hAC hm))
    exact le_pRank_of_elem hle hel hcardb
  · have h1 : 4 ≤ pRank 2 ↥(centralizer ({x} : Set G) ⊓ M) :=
      le_pRank_of_elem (le_inf hAC hAM) hA.1 hcard
    have h2 : 4 ≤ pRank 2 ↥M := le_pRank_of_elem hAM hA.1 hcard
    have h3 : pRank 2 ↥(centralizer ({x} : Set G) ⊓ M) ≤ pRank 2 G :=
      Bg.pRank_subgroup_le one_lt_two _
    have h4 : pRank 2 ↥M ≤ pRank 2 G := Bg.pRank_subgroup_le one_lt_two _
    omega


theorem isTerminalSub_of_unique_involution {X : Type} [Group X] [Finite X] {K : Subgroup X} {x : X}
    (hx2 : orderOf x = 2) (hxK : ∀ k ∈ K, x * k = k * x)
    (hcomp : IsCompIn (centralizer ({x} : Set X)) K)
    (hh : ∀ u : X, orderOf u = 2 → (∀ k ∈ K, u * k = k * u) → u * x = x * u → u = x) :
    IsTerminalSub K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxD : x ∈ centralizer (K : Set X) := Subgroup.mem_centralizer_iff.2 fun k hk => (hxK k hk).symm
  have hxp : IsPGroup 2 ↥(zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx2]; norm_num)
  obtain ⟨Q, hQ, hxQ⟩ := C3.Layer1.Iv251.exists_isSylowOf_ge (zpowers_le.2 hxD) hxp
  have hQp : IsPGroup 2 ↥Q := hQ.isPGroup
  have hxQ' : x ∈ Q := hxQ (mem_zpowers x)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxQ'
    rw [hxQ', orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  obtain ⟨z, hzQ, hz2, hzc⟩ := C3.Layer1.Iv251.exists_central_involution hQp le_rfl
    Subgroup.le_normalizer hQ0
  have hzD : z ∈ centralizer (K : Set X) := hQ.le hzQ
  have hzx : z = x := hh z hz2 (fun k hk => (Subgroup.mem_centralizer_iff.1 hzD k hk).symm)
    (hzc x hxQ')
  have hxcen : ∀ p ∈ Q, x * p = p * x := fun p hp => hzx ▸ hzc p hp
  refine isTerminalSub_of_Q hQ fun ε hε hε2 => ?_
  have hεD : ε ∈ centralizer (K : Set X) := hQ.le hε
  have : ε = x := hh ε hε2 (fun k hk => (Subgroup.mem_centralizer_iff.1 hεD k hk).symm)
    (hxcen ε hε).symm
  rw [this]
  exact hcomp

end CFSG.GH74.GLS.C3.Layer1.EndN
