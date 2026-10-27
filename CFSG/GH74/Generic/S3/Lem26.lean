module

public import CFSG.GH74.Generic.S3.Prop21Leaves
public import CFSG.GH74.Generic.S45.PumpLeaves

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_central_of_weakly_closed {w v : G} {P : Subgroup G}
    (hP : IsSylowOf 2 P (centralizer ({w} : Set G))) (hwP : w ∈ P) (hvP : v ∈ P)
    (hvc : ∀ a ∈ P, a * v = v * a) (hv2 : v * v = 1)
    (hweak : ∀ z : G, z ∈ P → (∀ a ∈ P, a * z = z * a) → z * z = 1 →
      (∃ g : G, g * v * g⁻¹ = z) → z = v) :
    ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ v ∈ S ∧ ∀ s ∈ S, s * v = v * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_ge (le_top : P ≤ ⊤) hP.isPGroup
  refine ⟨S, hS, hPS hvP, ?_⟩
  have hCw : S ⊓ centralizer ({w} : Set G) = P :=
    hP.eq_of_le (le_inf hPS hP.le) inf_le_right hS.isPGroup.to_inf_left
  set U : Subgroup G := S ⊓ centralizer ({v} : Set G) with hU
  have hPU : P ≤ U := fun x hx => ⟨hPS hx, mem_centralizer_singleton_iff.2 (hvc x hx)⟩
  have hUS : U = S := by
    by_contra hne
    have : Group.IsNilpotent ↥S := hS.isPGroup.isNilpotent
    have hH : U.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hne
      exact le_antisymm inf_le_left (Subgroup.subgroupOf_eq_top.mp h)
    obtain ⟨n, hn1, hn2⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hH)
    have hnU : ∀ u ∈ U, (n : G)⁻¹ * u * n ∈ U := by
      intro u hu
      have huS : u ∈ S := hu.1
      have hh : (⟨u, huS⟩ : ↥S) ∈ U.subgroupOf S := hu
      have := (Subgroup.mem_normalizer_iff.mp hn1 (n⁻¹ * ⟨u, huS⟩ * n)).mpr (by
        have e : n * (n⁻¹ * ⟨u, huS⟩ * n) * n⁻¹ = ⟨u, huS⟩ := by group
        rw [e]; exact hh)
      exact this
    set m : G := (n : G) * v * (n : G)⁻¹ with hm
    have hmc : ∀ u ∈ U, u * m = m * u := by
      intro u hu
      have h1 := mem_centralizer_singleton_iff.1 (hnU u hu).2
      calc u * m = (n : G) * ((n : G)⁻¹ * u * n) * v * (n : G)⁻¹ := by rw [hm]; group
        _ = (n : G) * (v * ((n : G)⁻¹ * u * n)) * (n : G)⁻¹ := by rw [mul_assoc _ _ v, h1, ← mul_assoc]
        _ = m * u := by rw [hm]; group
    have hmS : m ∈ S := S.mul_mem (S.mul_mem n.2 (hPS hvP)) (S.inv_mem n.2)
    have hmP : m ∈ P := by
      rw [← hCw]
      refine ⟨hmS, mem_centralizer_singleton_iff.2 ?_⟩
      exact (hmc w (hPU hwP)).symm
    have hmm : m * m = 1 := by
      calc m * m = (n : G) * (v * v) * (n : G)⁻¹ := by rw [hm]; group
        _ = 1 := by rw [hv2]; group
    have hmv : m = v := hweak m hmP (fun a ha => hmc a (hPU ha)) hmm ⟨n, hm.symm⟩
    have hnv : (n : G) * v = v * n := by
      have : (n : G) * v * (n : G)⁻¹ = v := by rw [← hm]; exact hmv
      calc (n : G) * v = (n : G) * v * (n : G)⁻¹ * n := by group
        _ = v * n := by rw [this]
    apply hn2
    exact ⟨n.2, mem_centralizer_singleton_iff.2 hnv⟩
  intro s hs
  have : s ∈ U := hUS ▸ hs
  exact mem_centralizer_singleton_iff.1 this.2

end Sylow

@[expose] def B_S3_Z_P : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G),
      Conf2A G t p f v w Iv Iw Ivw P →
      ∀ z ∈ P, (∀ a ∈ P, a * z = z * a) → z * z = 1 → z = 1 ∨ z = w ∨ z = v ∨ z = v * w

theorem b_S3_lemma26_transfer_of_zP (h63 : S45.B_III8_6_3) (hZ : B_S3_Z_P) :
    B_S3_lemma26_transfer := by
  intro G _ _ hG t p f v w Iv Iw Ivw P hconf
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hconf.v_inv, pow_two] at this
  have hweak : ∀ z : G, z ∈ P → (∀ a ∈ P, a * z = z * a) → z * z = 1 →
      (∃ g : G, g * v * g⁻¹ = z) → z = v := by
    intro z hzP hzc hzz ⟨g, hg⟩
    rcases hZ G hG t p f v w Iv Iw Ivw P hconf z hzP hzc hzz with h | h | h | h
    · exfalso
      have hv1 : v = 1 := mul_eq_left.mp (mul_inv_eq_one.mp (hg.trans h))
      have := hconf.v_inv
      rw [hv1, orderOf_one] at this
      omega
    · exact absurd (isConj_iff.mpr ⟨g, hg.trans h⟩) hconf.notConj_w
    · exact h
    · exact absurd (isConj_iff.mpr ⟨g, hg.trans h⟩) hconf.notConj_vw
  have hcen := exists_sylow_central_of_weakly_closed hconf.sylow_w hconf.w_P hconf.v_P hconf.v_central
    hv2 hweak
  refine h63 G hG.simple hG.nonab w hconf.w_inv P hconf.sylow_w v hconf.v_P hconf.v_central
    hconf.v_inv hcen ?_
  intro g hgP hgc
  have hz2 : (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := by
    calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  exact ⟨1, Subgroup.one_mem _, by rw [hweak _ hgP hgc hz2 ⟨g, rfl⟩]; group⟩

end CFSG.GH74.Generic.S3
