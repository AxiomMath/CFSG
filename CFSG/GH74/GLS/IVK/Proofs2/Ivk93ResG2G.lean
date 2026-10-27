module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResG2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OneCls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L4G

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Ree (ReeTag)


theorem ivk93res_g2 : ∀ (G : Type) [Group G] [Finite G] (z : G) (ε : Bool)
    (S : Subgroup G) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S →
    Stage1L4 G z S ε q L₁ L₂ → (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
      HasTwoInvolutionClasses (HBar H) →
      ∀ p f : ℕ, p ^ f = q → ¬ LieModel ↥(generalizedFitting (HBar H)) .G2 0 p f := by
  intro G _ _ z ε S q L₁ L₂ hctx hp hone H hne hCH hV hs hn hPerf h2 p f hpf hM
  classical
  have hz2 := hctx.orderOf_z
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  set J : Subgroup (HBar H) := generalizedFitting (HBar H) with hJ
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hM
  have hqodd : Odd q := hp.pair.odd
  have hgt3 := hp.pair.gt3
  have hodd : Odd (Nat.card F) := by rw [hcard, hpf]; exact hqodd
  have h5 : 5 ≤ Nat.card F := by
    rw [hcard, hpf]
    obtain ⟨m, hm⟩ := hqodd
    omega
  have hchar : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd
  have hJone : ∀ a b : ↥J, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
    intro a b ha hb
    exact Ivk47ab.isConj_of_equiv e
      (CFSG.LieType.HighestRoot.g2_involutions_isConj hchar (e a) (e b)
        (by rw [MulEquiv.orderOf_eq]; exact ha) (by rw [MulEquiv.orderOf_eq]; exact hb))
  obtain ⟨v, hv2, hvJ⟩ : ∃ v : HBar H, orderOf v = 2 ∧ v ∉ J := by
    obtain ⟨a, b, ha, hb, hab⟩ := h2
    by_contra hcon
    have hall : ∀ w : HBar H, orderOf w = 2 → w ∈ J := fun w hw =>
      by_contra fun hn => hcon ⟨w, hw, hn⟩
    have haJ := hall a ha
    have hbJ := hall b hb
    have h1 := MonoidHom.map_isConj J.subtype
      (hJone ⟨a, haJ⟩ ⟨b, hbJ⟩ (by rw [← Subgroup.orderOf_coe]; exact ha)
        (by rw [← Subgroup.orderOf_coe]; exact hb))
    exact hab h1
  have hv1 : v ^ 2 = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2] at this
  let α : MulAut ↥J := MulAut.conjNormal v
  have hα2 : α ^ 2 = 1 := by
    rw [← map_pow, hv1, map_one]
  have hαv : ∀ x : ↥J, ((α x : ↥J) : HBar H) = v * x * v⁻¹ := fun x => rfl
  let e' : ↥J ≃* ↥(adjointGroup ReeTag.G2.tag F) := e
  let α' : MulAut (adjointGroup ReeTag.G2.tag F) := MulAut.congr e' α
  have happ : ∀ y, α' y = e' (α (e'.symm y)) := fun y => rfl
  have hα'2 : α' ^ 2 = 1 := by
    show (MulAut.congr e' α) ^ 2 = 1
    rw [← map_pow, hα2, map_one]
  have hnot : α' ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range := by
    rintro ⟨g, hg⟩
    set j : ↥J := e'.symm g with hj
    have hconj : ∀ x : ↥J, (j : HBar H) * x * (j : HBar H)⁻¹ = v * x * v⁻¹ := by
      intro x
      have h1 : (MulAut.conj g) (e' x) = α' (e' x) := by rw [hg]
      rw [happ, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
      have h3 : α x = j * x * j⁻¹ := by
        have := congrArg e'.symm h1
        rw [MulEquiv.symm_apply_apply] at this
        rw [← this, hj]
        simp
      rw [← hαv x, h3]
      rfl
    have hcen : (v⁻¹ * (j : HBar H)) ∈ Subgroup.centralizer (J : Set (HBar H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h4 := hconj ⟨x, hx⟩
      calc x * (v⁻¹ * (j : HBar H)) = v⁻¹ * (v * x * v⁻¹) * (j : HBar H) := by group
        _ = v⁻¹ * ((j : HBar H) * x * (j : HBar H)⁻¹) * (j : HBar H) := by rw [← h4]
        _ = v⁻¹ * (j : HBar H) * x := by group
    have hcenJ : v⁻¹ * (j : HBar H) ∈ J := CFSG.centralizer_generalizedFitting_le (HBar H) hcen
    apply hvJ
    have : v = (j : HBar H) * (v⁻¹ * (j : HBar H))⁻¹ := by group
    rw [this]
    exact J.mul_mem j.2 (J.inv_mem hcenJ)
  obtain ⟨K, hKfix, hKs, hKn, hKbig⟩ :=
    ivk93res_g2_outer_involution hodd h5 hα'2 hnot
  let KX : Subgroup (HBar H) := (K.map e'.symm.toMonoidHom).map J.subtype
  let eKX : ↥K ≃* ↥KX :=
    (K.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).trans
      (Subgroup.equivMapOfInjective _ _ J.subtype_injective)
  have hKXs : IsSimpleGroup ↥KX := (MulEquiv.isSimpleGroup_congr eKX).1 hKs
  have hKXn : ∃ a b : ↥KX, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hKn
    exact ⟨eKX x, eKX y, fun h => hxy (eKX.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hKXc : KX ≤ Subgroup.centralizer ({v} : Set (HBar H)) := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : α' k = k := hKfix hk
    have h2 : α (e'.symm k) = e'.symm k := by
      rw [happ] at h1
      have := congrArg e'.symm h1
      rwa [MulEquiv.symm_apply_apply] at this
    have h3 := hαv (e'.symm k)
    rw [h2] at h3
    change (e'.symm k : HBar H) * v = v * (e'.symm k : HBar H)
    calc (e'.symm k : HBar H) * v = (v * (e'.symm k : HBar H) * v⁻¹) * v := by rw [← h3]
      _ = v * (e'.symm k : HBar H) := by group
  have hbig : (q * (q ^ 2 - 1)) ^ 2 < 2 * Nat.card ↥KX := by
    rw [← Nat.card_congr eKX.toEquiv, ← hpf, ← hcard]
    exact hKbig
  exact false_of_big_simple_centralizer hp.pair hz2 hone hv2 hKXs hKXn hKXc hbig

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
