module

public import CFSG.ClassicalInvolution.Q3.Q3CLApi
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen611
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyD
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

namespace Sec7

open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

theorem commutator_mem_oddCoreOf_of_commute (hcl : ClassicalClause Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {u a b : G} (hu : u ∈ J) (hu2 : IsPGroup 2 (Subgroup.zpowers u))
    (huu : u * u ≠ 1) (ha : a ∈ J) (hb : b ∈ J) (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J :=
  hcl.commOdd J hJ u a b hu hu2 huu ha hb hau hbu

theorem mem_oddCoreOf_of_odd (hcl : ClassicalClause Ω) {J W : Subgroup G} (hJ : J ∈ Ω) {u : G}
    (huJ : u ∈ J) (huW : u ∈ W) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1)
    {d : G} (hdC : d ∈ J ⊓ Subgroup.centralizer (W : Set G)) (hodd : Odd (orderOf d)) :
    d ∈ oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) := by
  set C := J ⊓ Subgroup.centralizer (W : Set G) with hCdef
  set D := C ⊓ oddCoreOf J with hDdef
  have hCJ : C ≤ J := inf_le_left
  have hCu : ∀ c ∈ C, c * u = u * c := fun c hc =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) u huW).symm
  have hDodd : Odd (Nat.card D) :=
    (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hCND : C ≤ Subgroup.normalizer (D : Set G) := fun c hc =>
    mem_normalizer_inf (Subgroup.le_normalizer hc)
      (mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hCJ hc)))
  have hE : Odd (Nat.card ↥(Subgroup.zpowers d ⊔ D)) :=
    odd_card_sup_of_le_normalizer' (Subgroup.zpowers_le.mpr (hCND hdC))
      (by rw [Nat.card_zpowers]; exact hodd) hDodd
  have hEC : Subgroup.zpowers d ⊔ D ≤ C := sup_le (Subgroup.zpowers_le.mpr hdC) inf_le_left
  have hCNE : C ≤ Subgroup.normalizer ((Subgroup.zpowers d ⊔ D : Subgroup G) : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_conjSub_eq]
    refine conjSub_eq_of_le_self ?_
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub]
    refine sup_le ?_ ?_
    · rw [conjSub, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have hcomm : d⁻¹ * c * d⁻¹⁻¹ * c⁻¹ ∈ D := by
        refine ⟨?_, commutator_mem_oddCoreOf_of_commute hcl hJ huJ hu2 huu
          (J.inv_mem (hCJ hdC)) (hCJ hc) (hCu _ (C.inv_mem hdC)) (hCu c hc)⟩
        exact C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hdC) hc) (C.inv_mem (C.inv_mem hdC)))
          (C.inv_mem hc)
      have e : (MulAut.conj c).toMonoidHom d = d * (d⁻¹ * c * d⁻¹⁻¹ * c⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
        (Subgroup.mem_sup_right hcomm)
    · rw [mem_normalizer_iff_conjSub_eq.mp (hCND hc)]
      exact le_sup_right
  have h1 := Balance.le_oddCoreIn_of_normalizes hEC hCNE hE
  rw [← oddCoreOf_eq_oddCoreIn] at h1
  exact h1 (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))

theorem exists_pow_two_pow_mem (hcl : ClassicalClause Ω) {J W : Subgroup G} (hJ : J ∈ Ω)
    (hWJ : W ≤ Subgroup.normalizer (J : Set G)) (hUc : IsCyclic ↥(J ⊓ W))
    (hU2 : IsPGroup 2 ↥(J ⊓ W)) {u : G} (huU : u ∈ J ⊓ W) (huu : u * u ≠ 1) {h : G}
    (hhJ : h ∈ J) (hhW : h ∈ Subgroup.normalizer (W : Set G)) :
    ∃ n : ℕ, h ^ (2 ^ n) ∈ oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) := by
  obtain ⟨n, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  refine ⟨n, ?_⟩
  have hdvd : 2 ^ n ∣ orderOf h := ⟨m, hnm⟩
  have hord : orderOf (h ^ (2 ^ n)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hnm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos n)]
  have hodd : Odd (orderOf (h ^ (2 ^ n))) := hord ▸ hm
  have hJ' : h ^ (2 ^ n) ∈ J := J.pow_mem hhJ _
  have hW' : h ^ (2 ^ n) ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hhW _
  have hC := mem_centralizer_of_odd hWJ hUc hU2 hJ' hW' hodd
  exact mem_oddCoreOf_of_odd hcl hJ (Subgroup.mem_inf.mp huU).1 (Subgroup.mem_inf.mp huU).2
    (hU2.to_le (Subgroup.zpowers_le.mpr huU)) huu ⟨hJ', hC⟩ hodd

theorem le_normalizer_of_mem_etaGIn (hΩ : HypOmegaGen Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) {S : Sylow 2 G}
    {γ : Set (Subgroup G)} (hγ : γ ∈ etaGIn Ω (S : Subgroup G)) {U : Subgroup G} (hU : U ∈ γ)
    {K : Subgroup G} (hK : K ∈ Ω) (hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  have hUU := mem_USet_of_mem_etaG hγ.1 hU
  obtain ⟨K', hK', hUK'⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hUU
  by_cases hKK' : K = K'
  · subst hKK'
    exact hUK'.trans (Subgroup.le_normalizer)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hA : K ⊓ (⨆ V ∈ γ, V) ∈ γ := h611 S γ hγ.1 hγ.2 K hK hKS
  have hAU := mem_USet_of_mem_etaG hγ.1 hA
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hAU
  have hzA : z ∈ K ⊓ (⨆ V ∈ γ, V) :=
    hz.mem_of_le inf_le_left (Sec6Gen.isPGroup_of_mem_USet hΩ hAU) (by omega)
  have hzW : z ∈ ⨆ V ∈ γ, V := (Subgroup.mem_inf.mp hzA).2
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUU
  refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hK' hKK' hz hUK'
    (Sec6Gen.isPGroup_of_mem_USet hΩ hUU) (by omega) fun u hu => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact habel γ hγ.1 u (le_iSup₂_of_le (f := fun V (_ : V ∈ γ) => V) U hU le_rfl hu) z hzW

theorem le_normalizer_of_mem_DSet (hΩ : HypOmegaGen Ω)
    (habel : Sec7.EtaAbelian Ω) (h611 : Sec7.EtaMeets Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R K : Subgroup G} (hR : R ∈ DSet Ω W) (hK : K ∈ Ω) (hRK : R ≤ K) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  have hW2 := isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, rfl⟩ := hW
  have hRW : IsPGroup 2 ↥(R ⊔ ⨆ U ∈ η, U) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hR.1) hW2 hR.2
  obtain ⟨S₁, hS₁⟩ := hRW.exists_le_sylow
  have hγ : η ∈ etaGIn Ω (S₁ : Subgroup G) :=
    ⟨hη, fun V hV => (le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV le_rfl).trans
      (le_sup_right.trans hS₁)⟩
  have hKS : 2 < Nat.card ↥(K ⊓ (S₁ : Subgroup G)) := by
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR.1
    have := Subgroup.card_le_of_le (le_inf hRK (le_sup_left.trans hS₁))
    omega
  exact iSup₂_le fun U hU => le_normalizer_of_mem_etaGIn hΩ habel h611 hγ hU hK hKS

theorem oddCoreOf_inf_centralizer_le_OCW (hcl : ClassicalClause Ω) {J W : Subgroup G}
    (hJ : J ∈ Ω) {z : G} (hz : IsUniqueInvolution J z) (hzW : z ∈ W) :
    oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) ≤ OCW W := by
  have hsub := hcl.isSubnormal_of_uniqueInvolution hJ hz
  have hCW : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzW)
  have h1 := isSubnormal_inf hsub (Subgroup.centralizer (W : Set G))
  rw [inf_eq_right.mpr hCW] at h1
  rw [oddCoreOf_eq_oddCoreIn, OCW, oddCoreOf_eq_oddCoreIn]
  exact Balance.oddCoreIn_le_of_isSubnormal h1

theorem isSylow2In_of_mem_RSet_of_le (hΩ : HypOmegaGen Ω) {R J : Subgroup G}
    (hR : R ∈ RSet Ω) (hJ : J ∈ Ω) (hRJ : R ≤ J) : IsSylow2In R J := by
  obtain ⟨J', hJ', hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  rwa [Sec6Gen.eq_of_le_of_le hΩ hJ' hJ hRJ'.2.1 (by omega) hRJ'.1 hRJ] at hRJ'

theorem keyOn (hΩ : HypOmegaGen Ω) (hcl : ClassicalClause Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) : KeyOn Ω := by
  intro W hW R hR T hT J hJ hRJ hTJ
  have hRsyl := isSylow2In_of_mem_RSet_of_le hΩ hR.1 hJ hRJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR.1
  have hWJ := le_normalizer_of_mem_DSet hΩ habel h611 hW hR hJ hRJ
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hR.1)
    (isPGroup_of_mem_WSet hW) hR.2).exists_le_sylow
  have hJS₁ : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRJ (le_sup_left.trans hS₁))
    omega
  have hU : J ⊓ W ∈ η := by
    have := h611 S₁ η hη (fun V hV => (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV
      le_rfl : V ≤ W).trans (le_sup_right.trans hS₁)) J hJ hJS₁
    rwa [← hWη] at this
  have hUU := mem_USet_of_mem_etaG hη hU
  obtain ⟨-, -, -, -, -, -, hUc, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUU
  have hU2 : IsPGroup 2 ↥(J ⊓ W) := Sec6Gen.isPGroup_of_mem_USet hΩ hUU
  obtain ⟨g, hg⟩ := hUc.exists_generator
  have hgord : orderOf (g : G) = Nat.card ↥(J ⊓ W) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have huu : (g : G) * g ≠ 1 := by
    intro h
    have := Nat.le_of_dvd two_pos
      (orderOf_dvd_of_pow_eq_one (x := (g : G)) (n := 2) (by rw [pow_two]; exact h))
    omega
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hzU : z ∈ J ⊓ W := hz.mem_of_le inf_le_left hU2 (by omega)
  have hOH : oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) ≤
      J ⊓ Subgroup.normalizer (W : Set G) :=
    (oddCoreOf_le_self _).trans
      (inf_le_inf_left J (Subgroup.centralizer_le_normalizer (W : Set G)))
  have hHO : J ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) : Set G) :=
    fun h hh => mem_normalizer_oddCoreOf_of_mem_normalizer
      (mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_inf.mp hh).1)
        (normalizer_le_normalizer_centralizer W (Subgroup.mem_inf.mp hh).2))
  have hRH : IsSylow2In R (J ⊓ Subgroup.normalizer (W : Set G)) :=
    ⟨le_inf hRJ hR.2, hRsyl.2.1, fun V' hV'H hV'2 hRV' =>
      hRsyl.2.2 V' (hV'H.trans inf_le_left) hV'2 hRV'⟩
  have hle := le_sup_of_pow_mem hOH hHO hRH fun h hh =>
    exists_pow_two_pow_mem hcl hJ hWJ hUc hU2 g.2 huu (Subgroup.mem_inf.mp hh).1
      (Subgroup.mem_inf.mp hh).2
  have hOX := oddCoreOf_inf_centralizer_le_OCW hcl hJ hz (Subgroup.mem_inf.mp hzU).2
  intro t ht
  exact sup_le (le_sup_left.trans le_sup_left) (hOX.trans le_sup_right) (hle ⟨hTJ ht, hT.2 ht⟩)

theorem l7_1Key (hP : PartIHypG Ω) : KeyOn Ω :=
  keyOn hP.hyp hP.cls
    (fun _ ⟨_, hS, hinv⟩ => (Sec6Gen.eta_abelian_of_cyc66 hP.hyp (Sec6Gen.cyc66 hP.hyp) hS hinv).1)
    (Sec6Gen.l6_11Gen G Ω hP.hyp)

end Sec7


end CFSG.ClassicalInvolution.Q3.Q3CL
