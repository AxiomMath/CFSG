module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.Sporadic.Recognition.HSMultiplierCert

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem catalogNoHSOdd_of_kgPumpTableT
    (hT : HSStd.Zassenhaus.Outer.KGPumpTableT) :
    CatalogNoHSOdd := by
  intro H _ _ N hF hidx hcat _ M v hv hM hodd
  have : N.Normal := hF.normal
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hvN : ∀ x ∈ N, v * x * v⁻¹ ∈ N := fun x hx => (inferInstance : N.Normal).conj_mem x hx v
  set τ := HSStd.Zassenhaus.Outer.tauAut N hv2 hvN with hτdef
  have hτ2 : τ * τ = 1 := HSStd.Zassenhaus.Outer.tauAut_sq N hv2 hvN
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hc : v ∈ centralizer (N : Set H) := by
      rw [mem_centralizer_iff]
      intro n hn
      have h := congrArg (fun σ : MulAut ↥N => ((σ ⟨n, hn⟩ : ↥N) : H)) h1
      simp only [hτdef, HSStd.Zassenhaus.Outer.tauAut_apply, MulAut.one_apply] at h
      calc n * v = (v * n * v⁻¹) * v := by rw [h]
        _ = v * n := by group
    have hvN' : v ∈ N := hF.centralizer_le hc
    have hz : (⟨v, hvN'⟩ : ↥N) ∈ center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((mem_centralizer_iff.1 hc) g g.2)
    have := hF.isSimpleGroup
    have hZN : center ↥N = ⊥ := by
      rcases (inferInstance : (center ↥N).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hF.nonabelian
        have ha : a ∈ center ↥N := h ▸ Subgroup.mem_top a
        exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
    rw [hZN, Subgroup.mem_bot] at hz
    have hv1 : v = 1 := congrArg Subtype.val hz
    rw [hv1, orderOf_one] at hv
    exact absurd hv (by decide)
  have hMq : CFSG.IsQuasisimple ↥M := hodd.1
  have hMN : M ≤ N := Induction.Hyp.le_of_perfect_of_index_le_two hidx hMq.1
  have hMC : M ≤ centralizer ({v} : Set H) := hM.1
  set M' : Subgroup ↥N := M.subgroupOf N with hM'def
  have hM'le : M' ≤ HSStd.autCentralizer τ := by
    intro x hx
    rw [HSStd.Zassenhaus.Outer.mem_autCentralizer_tauAut_iff]
    exact mem_centralizer_singleton_iff.1 (hMC (Subgroup.mem_subgroupOf.1 hx))
  let e : ↥M' ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMN
  have hM'q : CFSG.IsQuasisimple ↥M' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hMq
  have hZ : center ↥M = ⊥ := by
    obtain ⟨eq⟩ := hodd.2.2
    have hle := CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate hMq.1
      (eq : ↥M ⧸ center ↥M ≃* CFSG.Blueprint.NativeSporadic.HS)
    have hpos : 0 < Nat.card ↥(center ↥M) := Nat.card_pos
    have hodd' : Odd (Nat.card ↥(center ↥M)) := hodd.2.1
    have h1 : Nat.card ↥(center ↥M) = 1 := by
      rcases hodd' with ⟨k, hk⟩
      omega
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hZ' : center ↥M' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ center ↥M := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hx y]
    rw [hZ, Subgroup.mem_bot] at hex
    rw [Subgroup.mem_bot]
    exact e.injective (hex.trans (map_one e).symm)
  let f : ↥(HSStd.autCentralizer τ) →* ↥(centralizer ({v} : Set H)) :=
    (N.subtype.comp (HSStd.autCentralizer τ).subtype).codRestrict _ (fun x =>
      mem_centralizer_singleton_iff.2
        ((HSStd.Zassenhaus.Outer.mem_autCentralizer_tauAut_iff N hv2 hvN x.1).1 x.2))
  have hcomap : M'.subgroupOf (HSStd.autCentralizer τ) =
      (M.subgroupOf (centralizer ({v} : Set H))).comap f := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hM'def]
    rfl
  have hsn : (M'.subgroupOf (HSStd.autCentralizer τ)).IsSubnormal := by
    rw [hcomap]
    exact Subgroup.IsSubnormal.comap f hM.2.2
  have hp : IsPGroup 2 ↥(center ↥M') := by
    rw [hZ']
    exact IsPGroup.of_bot
  have hs : IsSporadic (↥M' ⧸ center ↥M') .HS := by
    obtain ⟨g⟩ := isSporadic_of_center_eq_bot hZ hodd.2.2
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).trans
      (e.trans g)⟩
  obtain ⟨-, -, h3, -⟩ := hT ↥N hcat hF.isSimpleGroup τ hτ2 hτ1 M' hM'le hM'q hsn hp
  have h2 := (h3 hs).2
  rw [hZ'] at h2
  simp at h2

end CFSG.EvenSporadicStandard.Induction.Balance
