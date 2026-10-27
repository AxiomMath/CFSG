module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Fusion
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10W
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AZ

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank Equiv
open scoped commutatorElement

theorem subgroupOf_perfect {G : Type*} [Group G] {J L : Subgroup G} (hJL : J ≤ L)
    (hJp : ⁅J, J⁆ = J) : ⁅J.subgroupOf L, J.subgroupOf L⁆ = J.subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hJL, hJp]

theorem exists_conj_of_equiv {H : Type*} [Group H] {L : Subgroup H} {M : Type*} [Group M]
    (e : L ≃* M) {ι z : H} (hι : ι ∈ L) (hz : z ∈ L) {w : M}
    (hw : w * e ⟨ι, hι⟩ * w⁻¹ = e ⟨z, hz⟩) : ∃ g ∈ L, g⁻¹ * ι * g = z := by
  have h1 : e.symm w * ⟨ι, hι⟩ * (e.symm w)⁻¹ = ⟨z, hz⟩ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hw]
  refine ⟨((e.symm w : L) : H)⁻¹, inv_mem (e.symm w).2, ?_⟩
  have h2 := congrArg Subtype.val h1
  rw [inv_inv]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2

theorem ne_one_and_sq_of_orderOf {H : Type*} [Group H] {L : Subgroup H} {x : H} (hx : x ∈ L)
    (h2 : orderOf x = 2) : (⟨x, hx⟩ : L) ≠ 1 ∧ (⟨x, hx⟩ : L) * ⟨x, hx⟩ = 1 := by
  refine ⟨fun h1 => ?_, Subtype.ext ?_⟩
  · have : x = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · rw [Subgroup.coe_mul, ← sq, ← h2, pow_orderOf_eq_one]
    rfl

theorem exists_conj_of_oracle {H : Type*} [Group H] {L : Subgroup H} {M : Type*} [Group M]
    (e : L ≃* M) {s : ℕ}
    (hconj : ∀ (u y z' : M) (J' : Subgroup M), u ≠ 1 → u ^ 2 = 1 → J' ≤ centralizer {u} →
      ⁅J', J'⁆ = J' → y ∈ J' → orderOf y = s → z' ∈ J' → z' * z' = 1 → z' ≠ 1 →
        ∃ w, w * u * w⁻¹ = z')
    {ι : H} (hι : ι ∈ L) (hι2 : orderOf ι = 2) {J₁ : Subgroup H} (hJL : J₁ ≤ L)
    (hJC : J₁ ≤ centralizer {ι}) (hJp : ⁅J₁, J₁⁆ = J₁) {v : H} (hv : v ∈ J₁)
    (hvs : orderOf v = s) {z : H} (hz : z ∈ J₁) (hz2 : orderOf z = 2) :
    ∃ g ∈ L, g⁻¹ * ι * g = z := by
  set J' := (J₁.subgroupOf L).map e.toMonoidHom with hJ'
  obtain ⟨hι1, hιι⟩ := ne_one_and_sq_of_orderOf hι hι2
  obtain ⟨hz1, hzz⟩ := ne_one_and_sq_of_orderOf (hJL hz) hz2
  have hu1 : e ⟨ι, hι⟩ ≠ 1 := by rwa [Ne, MulEquiv.map_eq_one_iff]
  have hu2 : e ⟨ι, hι⟩ ^ 2 = 1 := by rw [← map_pow, sq, hιι, map_one]
  have hJC' : J' ≤ centralizer {e ⟨ι, hι⟩} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJC (mem_subgroupOf.mp hx)))
  have hJp' : ⁅J', J'⁆ = J' := by rw [hJ', ← map_commutator, subgroupOf_perfect hJL hJp]
  have hmem : ∀ x (hx : x ∈ J₁), e ⟨x, hJL hx⟩ ∈ J' := fun x hx =>
    ⟨⟨x, hJL hx⟩, mem_subgroupOf.mpr hx, rfl⟩
  have hys : orderOf (e ⟨v, hJL hv⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hvs]
  obtain ⟨w, hw⟩ := hconj _ _ _ J' hu1 hu2 hJC' hJp' (hmem v hv) hys (hmem z hz)
    (by rw [← map_mul, hzz, map_one]) (by rwa [Ne, MulEquiv.map_eq_one_iff])
  exact exists_conj_of_equiv e hι (hJL hz) hw

theorem support_card_of_alt_involution {σ : Perm (Fin 10)} (hA : σ ∈ alternatingGroup (Fin 10))
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) : σ.support.card = 4 ∨ σ.support.card = 8 := by
  obtain ⟨hc, hpar, hpos⟩ := CatFactsSmall.cycleType_of_involution h2 h1
  have hle : σ.support.card ≤ 10 := by simpa using Finset.card_le_univ σ.support
  have hsign := Perm.sign_of_cycleType σ
  rw [hc, Multiset.sum_replicate, Multiset.card_replicate,
    Equiv.Perm.mem_alternatingGroup.1 hA] at hsign
  set k := σ.support.card / 2 with hk
  have hev : Even k := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have : (-1 : ℤˣ) ^ (k • 2 + k) = -1 := by
      rw [smul_eq_mul, show k * 2 + k = 3 * k by ring]
      exact (Odd.mul (by decide) hodd).neg_one_pow
    rw [this] at hsign
    exact absurd hsign (by decide)
  obtain ⟨j, hj⟩ := hev
  omega

theorem exists_conj_A10 {H : Type*} [Group H] {L : Subgroup H}
    (e : L ≃* alternatingGroup (Fin 10)) {ι : H} (hι : ι ∈ L) (hι2 : orderOf ι = 2)
    {J₁ : Subgroup H} (hJL : J₁ ≤ L) (hJC : J₁ ≤ centralizer {ι}) (hJp : ⁅J₁, J₁⁆ = J₁)
    (h5 : 5 ∣ Nat.card J₁) {z : H} (hz : z ∈ J₁) (hz2 : orderOf z = 2) :
    ∃ g ∈ L, g⁻¹ * ι * g = z := by
  classical
  set φ : L →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    e.injective (Subtype.ext (by simpa [hφ] using hab))
  obtain ⟨hι1, hιι⟩ := ne_one_and_sq_of_orderOf hι hι2
  obtain ⟨hz1, hzz⟩ := ne_one_and_sq_of_orderOf (hJL hz) hz2
  set τ := φ ⟨ι, hι⟩ with hτ
  set σ := φ ⟨z, hJL hz⟩ with hσ
  have hτA : τ ∈ alternatingGroup (Fin 10) := (e _).2
  have hσA : σ ∈ alternatingGroup (Fin 10) := (e _).2
  have hτ2 : τ * τ = 1 := by rw [hτ, ← map_mul, hιι, map_one]
  have hσ2 : σ * σ = 1 := by rw [hσ, ← map_mul, hzz, map_one]
  have hτ1 : τ ≠ 1 := fun h => hι1 (hφinj (by rw [← hτ, h, map_one]))
  have hσ1 : σ ≠ 1 := fun h => hz1 (hφinj (by rw [← hσ, h, map_one]))
  set J'' := (J₁.subgroupOf L).map φ with hJ''
  have hperf : ⁅J'', J''⁆ = J'' := by rw [hJ'', ← map_commutator, subgroupOf_perfect hJL hJp]
  have hc : ∀ l ∈ J'', l * τ = τ * l := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hτ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJC (mem_subgroupOf.mp hx)))
  have hσJ : σ ∈ J'' := ⟨⟨z, hJL hz⟩, mem_subgroupOf.mpr hz, rfl⟩
  rcases support_card_of_alt_involution hτA hτ2 hτ1 with h4 | h8
  · have hfix := CatFactsSmall.fix_support_of_perfect hτ2 h4.le hperf hc
    have hσS : ∀ x ∉ τ.supportᶜ, σ x = x := fun x hx =>
      hfix σ hσJ x (by simpa using hx)
    have hcompl : τ.supportᶜ.card = 6 := by rw [Finset.card_compl, h4, Fintype.card_fin]
    have hσ4 := CatFactsSmall.support_card_eq_four hσA hσ2 hσ1 hσS (by omega)
    obtain ⟨π, hπA, hπ⟩ := CatFactsSmall.exists_alt_conj_of_support_four hτ2 hτ1 hσ2 hσ1 h4 hσ4
    refine exists_conj_of_equiv e hι (hJL hz) (w := ⟨π, hπA⟩) (Subtype.ext ?_)
    simpa [hτ, hσ, hφ] using hπ
  · exfalso
    have hC := CatFactsSmall.card_centralizer_involution hτ2 hτ1
    rw [h8, Fintype.card_fin] at hC
    have hle : J'' ≤ centralizer {τ} := fun l hl => mem_centralizer_singleton_iff.mpr (hc l hl)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hC, hJ'', Subgroup.card_map_of_injective hφinj,
      Nat.card_congr (subgroupOfEquivOfLe hJL).toEquiv] at hdvd
    have : (5 : ℕ) ∣ (10 - 8).factorial * 2 ^ (8 / 2) * (8 / 2).factorial := h5.trans hdvd
    exact absurd this (by decide)

end AZ

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank AZ

theorem cf82AZ : CF82AZ := by
  intro H _ _ p f hp hp2 hf _ hC htype hL4 hU4 ι hιL hι2 J₁ hJC hcomp hJtype z hz hz2
  classical
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  have hJp : ⁅J₁, J₁⁆ = J₁ := commutator_eq_self_of_isPComponent hJC hcomp
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have hsJ₁ : s ∣ Nat.card J₁ := hsJ.trans (Subgroup.card_quotient_dvd_card _)
  have := Fact.mk hs
  obtain ⟨⟨v, hv⟩, hvs⟩ := exists_prime_orderOf_dvd_card' (G := J₁) s hsJ₁
  rw [Subgroup.orderOf_mk] at hvs
  rcases htype with hL | hU | hA
  · have hq := hL4 hL
    obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
    let : Fintype F := Fintype.ofFinite F
    have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
    set e' : ↥(generalizedFitting H) ≃*
        LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F :=
      eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
        (QuotientGroup.quotientMulEquivOfEq
          (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm))
    have hJL := le_of_perfect _ hC (fun u v => commutator_mem_range_conj_of_mulEquiv e'
      (fun u v => LinearOut.out_comm_projectiveSL_four (by rw [hFq]; exact hq) u v) u v) hJp
    have hF' : Fintype.card F % 4 = 3 := by rw [hFq]; exact hq
    exact exists_conj_of_oracle eL
      (fun u y z' J' hu1 hu2 hJ' hJp' hy hys hz' hzz hz1 => exists_conj_L4 hF' hs hs2
        (by rw [hFq]; exact hsq) hu1 hu2 hys (mem_centralizer_singleton_iff.mp (hJ' hy)).symm
        hu1 hu2 hJ' hJp' hy hys hz' hzz hz1)
      hιL hι2 hJL hJC hJp hv hvs hz hz2
  · have hq := hU4 hU
    obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
    have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
      ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
    have hJL := le_of_perfect _ hC (fun u v => commutator_mem_range_conj_of_mulEquiv eU
      (fun u v => UnitaryOut.out_comm_statedSU_four hUF hp2 hq u v) u v) hJp
    exact exists_conj_of_oracle eU
      (fun u y z' J' hu1 hu2 hJ' hJp' hy hys hz' hzz hz1 => exists_conj_U4 hUF hp2 hq hs hs2
        hsq hu1 hu2 hys (mem_centralizer_singleton_iff.mp (hJ' hy)).symm
        hu1 hu2 hJ' hJp' hy hys hz' hzz hz1)
      hιL hι2 hJL hJC hJp hv hvs hz hz2
  · obtain ⟨eA⟩ := hA
    have hJL := le_of_perfect _ hC (fun u v => commutator_mem_range_conj_of_mulEquiv eA
      out_comm_alternatingGroup_ten u v) hJp
    have h5 : 5 ∣ Nat.card J₁ :=
      (five_dvd_card_of_isSec8JType hp hp2 hJtype).trans (Subgroup.card_quotient_dvd_card _)
    exact exists_conj_A10 eA hιL hι2 hJL hJC hJp h5 hz hz2

end CFSG.ComponentClassification.CatFactsL4U4
