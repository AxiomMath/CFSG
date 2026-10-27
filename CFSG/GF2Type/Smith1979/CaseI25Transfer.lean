module

public import CFSG.GF2Type.Smith1979.CaseI25Fusion
public import CFSG.GF2Type.Smith1979.CaseIClosure
public import CFSG.LargeExtraspecial.S111CNorm
public import CFSG.RankThree.PartOne.S12.Transfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace CaseI25Transfer

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7

section Generic

theorem exists_quotient_of_character {G : Type} [Group G] (P : Subgroup G)
    (ψ : P →* Multiplicative (ZMod 2)) {c : G} (hc : c ∈ P) (hψc : ψ ⟨c, hc⟩ ≠ 1)
    (hfus : ∀ x : G, ∀ h : x * c * x⁻¹ ∈ P, ψ ⟨x * c * x⁻¹, h⟩ = ψ ⟨c, hc⟩) :
    ∃ Q : Subgroup G, Q ≤ P ∧ (Q.subgroupOf P).Normal ∧
      (∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P) ∧ c ∉ Q ∧
      ∀ x : G, ∀ h : x * c * x⁻¹ ∈ P, ∃ q ∈ Q, x * c * x⁻¹ = c * q := by
  have hmem : ∀ y : G, ∀ hy : y ∈ P, y ∈ (ψ.ker).map P.subtype ↔ ψ ⟨y, hy⟩ = 1 := by
    intro y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
      rw [← hz']
      exact MonoidHom.mem_ker.mp hz
    · intro h
      exact ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr h, rfl⟩
  have hQeq : ((ψ.ker).map P.subtype).subgroupOf P = ψ.ker := by
    ext z
    rw [Subgroup.mem_subgroupOf, hmem (z : G) z.2, MonoidHom.mem_ker]
  refine ⟨(ψ.ker).map P.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨z, -, rfl⟩
    exact z.2
  · rw [hQeq]
    infer_instance
  · intro x y
    rw [hQeq, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    exact (commutatorElement_eq_one_iff_mul_comm (g₁ := ψ x) (g₂ := ψ y)).mpr (mul_comm _ _)
  · intro hcQ
    exact hψc ((hmem c hc).mp hcQ)
  · intro x h
    have hqP : c⁻¹ * (x * c * x⁻¹) ∈ P := P.mul_mem (P.inv_mem hc) h
    refine ⟨c⁻¹ * (x * c * x⁻¹), (hmem _ hqP).mpr ?_, (mul_inv_cancel_left c _).symm⟩
    have e1 : (⟨c⁻¹ * (x * c * x⁻¹), hqP⟩ : P) = (⟨c, hc⟩ : P)⁻¹ * ⟨x * c * x⁻¹, h⟩ := rfl
    rw [e1, map_mul, map_inv, hfus x h, inv_mul_cancel]

open scoped IsMulCommutative in
theorem not_mem_commutator_of_fusion {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : CFSG.RankThree.PartOne.IsSylowOf 2 P ⊤) (hQP : Q ≤ P)
    (hQn : (Q.subgroupOf P).Normal) (hab : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P)
    {c : G} (hcP : c ∈ P) (hc2 : orderOf c = 2) (hcQ : c ∉ Q)
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q) :
    c ∉ _root_.commutator G := by
  haveI := hQn
  have hcomm : _root_.commutator P ≤ Q.subgroupOf P := by
    change ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Q.subgroupOf P
    rw [Subgroup.commutator_le]
    intro x _ y _
    simpa [commutatorElement_def] using hab x y
  haveI : IsMulCommutative (P ⧸ Q.subgroupOf P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let ϕ : P →* P ⧸ Q.subgroupOf P := QuotientGroup.mk' (Q.subgroupOf P)
  have hconj : ∀ x : G, ∀ h : x⁻¹ * c * x ∈ P, ϕ ⟨x⁻¹ * c * x, h⟩ = ϕ ⟨c, hcP⟩ := by
    intro x h
    obtain ⟨q, hq, hqe⟩ := hfus x⁻¹ (by simpa using h)
    have hsplit : (⟨x⁻¹ * c * x, h⟩ : P) = ⟨c, hcP⟩ * ⟨q, hQP hq⟩ :=
      Subtype.ext (by simpa using hqe)
    have hq1 : ϕ ⟨q, hQP hq⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := Q.subgroupOf P) _).mpr (Subgroup.mem_subgroupOf.mpr hq)
    rw [hsplit, map_mul, hq1, mul_one]
  have hVc := CFSG.RankThree.PartOne.Transfer.transfer_apply_eq_pow_index ϕ hcP hc2 hconj
  have hsq : c ^ 2 = 1 := by
    rw [← hc2]
    exact pow_orderOf_eq_one _
  have hpow : ϕ ⟨c, hcP⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have h2 : (⟨c, hcP⟩ : P) ^ 2 = 1 := Subtype.ext hsq
    rw [h2, map_one]
  have hne : ϕ ⟨c, hcP⟩ ≠ 1 := fun h =>
    hcQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := Q.subgroupOf P) _).mp h))
  have hord : orderOf (ϕ ⟨c, hcP⟩) = 2 := orderOf_eq_prime hpow hne
  obtain ⟨-, -, hndvd⟩ := hP
  rw [Subgroup.relIndex_top_right] at hndvd
  have hVne : MonoidHom.transfer ϕ c ≠ 1 := by
    intro h
    rw [hVc] at h
    have h2 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h2
    exact hndvd h2
  have hker : _root_.commutator G ≤ (MonoidHom.transfer ϕ).ker := by
    change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ (MonoidHom.transfer ϕ).ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro hc
  apply hVne
  have hxk := hker hc
  rw [MonoidHom.mem_ker] at hxk
  exact hxk

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def nuOn (ν : NLbar S g →* Multiplicative (ZMod 2))
    (P : Subgroup S.Mbar) (hP : P ≤ (NLbar S g).subgroupOf S.Mbar) :
    P →* Multiplicative (ZMod 2) :=
  ν.comp ((subgroupOfEquivOfLe (fun x hx => hx.1 : NLbar S g ≤ S.Mbar)).toMonoidHom.comp
    (Subgroup.inclusion hP))

theorem mem_NLbar_of_mem_Lbar {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ NLbar S g :=
  ⟨S.Lbar_le_Mbar g ht, le_normalizer (H := S.Lbar g) ht⟩

theorem nu_conj_eq (ν : NLbar S g →* Multiplicative (ZMod 2)) (a y : NLbar S g) :
    ν (a * y * a⁻¹) = ν y := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

@[expose] def tM {t : S.O} (ht : t ∈ S.Lbar g) : S.Mbar := ⟨t, S.Lbar_le_Mbar g ht⟩

theorem orderOf_tM_eq_two (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    orderOf (tM ht) = 2 := by
  have hsq : tM ht ^ 2 = 1 :=
    Subtype.ext (by rw [pow_two]; exact mul_self_of_mem_Lbar S H.conj_mem ht)
  exact orderOf_eq_prime hsq (fun h => ht1 (congrArg Subtype.val h))

theorem exists_sylow_data (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    ∃ P : Subgroup S.Mbar, CFSG.RankThree.PartOne.IsSylowOf 2 P ⊤ ∧ tM ht ∈ P ∧
      ∀ x ∈ P, (x : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
  haveI : Finite S.Mbar := inferInstance
  obtain ⟨Ps, hLP, hPN⟩ := S11.exists_sylow_le_normalizer H.conj_mem C
  have hcP : tM ht ∈ (Ps : Subgroup S.Mbar) := by
    obtain ⟨x, hx, hxt⟩ := hLP ht
    have hx' : x = tM ht := Subtype.ext hxt
    rw [← hx']
    exact hx
  have hsyl : CFSG.RankThree.PartOne.IsSylowOf 2 (Ps : Subgroup S.Mbar) ⊤ := by
    unfold CFSG.RankThree.PartOne.IsSylowOf
    refine ⟨le_top, Ps.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Ps.not_dvd_index
  exact ⟨Ps, hsyl, hcP, fun x hx => hPN (Subgroup.mem_map_of_mem _ hx)⟩

section Fusion

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem nu_fusion (ν : NLbar S g →* Multiplicative (ZMod 2)) {P : Subgroup S.Mbar}
    (hPN : ∀ x ∈ P, (x : S.O) ∈ normalizer (S.Lbar g : Set S.O)) (hcP : tM ht ∈ P)
    (hPle : P ≤ (NLbar S g).subgroupOf S.Mbar) :
    ∀ x : S.Mbar, ∀ h : x * tM ht * x⁻¹ ∈ P,
      nuOn ν P hPle ⟨x * tM ht * x⁻¹, h⟩ = nuOn ν P hPle ⟨tM ht, hcP⟩ := by
  intro x h
  have hxN : (x : S.O) * t * (x : S.O)⁻¹ ∈ normalizer (S.Lbar g : Set S.O) := hPN _ h
  have hL : (x : S.O) * t * (x : S.O)⁻¹ ∈ S.Lbar g :=
    CaseI25Fusion.conj_mem_Lbar_of_mem_normalizer hCE H hNo C ht ht1 hVQ hΩ hN h6 x.2 hxN
  have hD : (x : S.O) * t * (x : S.O)⁻¹ ∈ Delta S g t := by
    rw [CaseIClosure.Delta_eq_class_inter H C ht]
    exact ⟨hL, x, x.2, rfl⟩
  obtain ⟨n, hn, hnx⟩ := hD
  have e : (⟨(x : S.O) * t * (x : S.O)⁻¹, mem_NLbar_of_mem_Lbar hL⟩ : NLbar S g) =
      ⟨n, hn⟩ * ⟨t, mem_NLbar_of_mem_Lbar ht⟩ * ⟨n, hn⟩⁻¹ := Subtype.ext hnx
  have key := nu_conj_eq ν ⟨n, hn⟩ ⟨t, mem_NLbar_of_mem_Lbar ht⟩
  rw [← e] at key
  exact key

theorem not_mem_commutator_Mbar (ν : NLbar S g →* Multiplicative (ZMod 2))
    (hν : ν ⟨t, mem_NLbar_of_mem_Lbar ht⟩ ≠ 1) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype := by
  haveI : Finite S.Mbar := inferInstance
  obtain ⟨P, hsyl, hcP, hPN⟩ := exists_sylow_data H C ht
  have hPle : P ≤ (NLbar S g).subgroupOf S.Mbar := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2, hPN x hx⟩
  obtain ⟨Q, hQP, hQn, hab, hcQ, hfus⟩ :=
    exists_quotient_of_character P (nuOn ν P hPle) hcP hν
      (nu_fusion hCE H hNo C ht ht1 hVQ hΩ hN h6 ν hPN hcP hPle)
  have hc := not_mem_commutator_of_fusion hsyl hQP hQn hab hcP
    (orderOf_tM_eq_two H ht ht1) hcQ hfus
  intro hmem
  obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp hmem
  have hxc : x = tM ht := Subtype.ext hxt
  rw [hxc] at hx
  exact hc hx

end Fusion

end CaseI25Transfer

end CFSG.GF2Type.Smith1979
