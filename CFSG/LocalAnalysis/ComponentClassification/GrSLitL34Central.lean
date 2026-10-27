module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace L34Central

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowTwoIn_le {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) :
    ∃ S : Subgroup G, IsSylowTwoIn S H ∧ Q ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨(P : Subgroup H).map H.subtype, ⟨map_subtype_le _, P, ?_⟩, ?_⟩
  · exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  · intro q hq
    exact ⟨⟨q, hQH hq⟩, hP (mem_subgroupOf.mpr hq), rfl⟩

omit [Finite G] in
theorem isPGroup_sup_zpowers {a x : G} (ha : a * a = 1) (hx : x * x = 1)
    (hax : a * x = x * a) : IsPGroup 2 ↥(zpowers a ⊔ zpowers x) := by
  refine IsPGroup.to_sup_of_normal_right' (isElemTwo_zpowers ha).isPGroup
    (isElemTwo_zpowers hx).isPGroup ?_
  rw [zpowers_le]
  refine mem_normalizer_iff.mpr fun y => ?_
  have hcomm : ∀ z ∈ zpowers x, a * z = z * a := by
    intro z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute a x from hax) k).eq
  constructor
  · intro hy
    rwa [hcomm y hy, mul_inv_cancel_right]
  · intro hy
    have h := hcomm _ hy
    have : y = a * y * a⁻¹ := by
      calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = a⁻¹ * ((a * y * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * y * a⁻¹)) := by rw [h]
        _ = a * y * a⁻¹ := by group
    rw [this]
    exact hy

theorem le_index_of_l34 {J : Subgroup G} (h : IsL34Type (J ⧸ Open.fusionZStar J)) :
    20160 ≤ (pPrimeCore 2 ↥J).index := by
  have h1 : (Open.fusionZStar ↥J).index = 20160 := by
    rw [index_eq_card]
    exact GSThmB.card_of_lieModel_L34 h
  have h2 : (Open.fusionZStar ↥J).index ∣ (pPrimeCore 2 ↥J).index :=
    index_dvd_of_le (Sol78.pPrimeCore_le_fusionZStar ↥J)
  rw [h1] at h2
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) h2

omit [Finite G] in
theorem two_dvd_card_of_l34 {J : Subgroup G} (h : IsL34Type (J ⧸ Open.fusionZStar J)) :
    2 ∣ Nat.card J := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar ↥J),
    GSThmB.card_of_lieModel_L34 h]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem mem_normalizer_of_map_le {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj g).injective])

omit [Finite G] in
theorem conjugate_eq_of_mem_normalizer {J : Subgroup G} {s : G}
    (hs : s ∈ normalizer (J : Set G)) : conjugate J s = J :=
  mem_normalizer_iff_map_conj_eq.mp (inv_mem hs)

theorem le_normalizer_inf_centralizer {S J : Subgroup G} (hSJ : S ≤ normalizer (J : Set G)) :
    S ≤ normalizer ((S ⊓ centralizer (J : Set G) : Subgroup G) : Set G) := by
  intro s hs
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨hhS, hhC⟩ := mem_inf.mp hh
  have hsJ := hSJ hs
  refine mem_inf.mpr ⟨mul_mem (mul_mem hs hhS) (inv_mem hs), ?_⟩
  rw [mem_centralizer_iff] at hhC ⊢
  intro j hj
  have hj' : s⁻¹ * j * s ∈ J := by
    have := (mem_normalizer_iff.mp (inv_mem hsJ) j).mp hj
    rwa [inv_inv] at this
  have hc := hhC _ hj'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc j * (s * h * s⁻¹) = s * ((s⁻¹ * j * s) * h) * s⁻¹ := by group
    _ = s * (h * (s⁻¹ * j * s)) * s⁻¹ := by rw [hc]
    _ = s * h * s⁻¹ * j := by group

end L34Central

end CFSG.ComponentClassification.GrSLit
