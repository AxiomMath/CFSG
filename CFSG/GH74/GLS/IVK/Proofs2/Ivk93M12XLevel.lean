module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Shape
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74

namespace XLevel

theorem mem_sylow_of_comm {X : Type} [Group X] {x : X} (hx : orderOf x = 2) (T : Sylow 2 X)
    (hT : ∀ t ∈ (T : Subgroup X), t * x = x * t) : x ∈ (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpx : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  have hnorm : zpowers x ≤ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hT)
  have h1 := T.is_maximal' (T.isPGroup'.to_sup_of_normal_left' hpx hnorm) le_sup_left
  have h2 : x ∈ (T : Subgroup X) ⊔ zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [h1] at h2

theorem isCentralInvolution_fitting {X : Type} [Group X] [Finite X] {x : X} (hx : orderOf x = 2)
    (hxJ : x ∈ generalizedFitting X) (T : Sylow 2 X)
    (hT : ∀ t ∈ (T : Subgroup X), t * x = x * t) :
    IsCentralInvolution (⟨x, hxJ⟩ : ↥(generalizedFitting X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJnorm : (generalizedFitting X).Normal := LocalCores.generalized_fitting_characteristic.2
  have hxT : x ∈ (T : Subgroup X) := mem_sylow_of_comm hx T hT
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal T (N := generalizedFitting X)
  refine ⟨?_, Q, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]; exact hx
  · rw [hQ, Subgroup.mem_subgroupOf]; exact ⟨hxT, hxJ⟩
  · intro s hs
    rw [hQ, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (hT _ hs.1)

def cenIncl {X : Type} [Group X] {x : X} (hxJ : x ∈ generalizedFitting X) :
    ↥(centralizer ({(⟨x, hxJ⟩ : ↥(generalizedFitting X))} : Set ↥(generalizedFitting X))) →*
      ↥(centralizer ({x} : Set X)) where
  toFun c := ⟨((c : ↥(generalizedFitting X)) : X),
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem cenIncl_injective {X : Type} [Group X] {x : X} (hxJ : x ∈ generalizedFitting X) :
    Function.Injective (cenIncl hxJ) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun e : ↥(centralizer ({x} : Set X)) => (e : X)) h

theorem cenIncl_range {X : Type} [Group X] {x : X} (hxJ : x ∈ generalizedFitting X) :
    (cenIncl hxJ).range = (generalizedFitting X).subgroupOf (centralizer ({x} : Set X)) := by
  ext ⟨d, hd⟩
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc⟩
    have := congrArg (fun e : ↥(centralizer ({x} : Set X)) => (e : X)) hc
    simp only [cenIncl, MonoidHom.coe_mk, OneHom.coe_mk] at this
    subst this
    exact c.1.2
  · intro hdJ
    refine ⟨⟨⟨d, hdJ⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hd)

theorem normal_cenIncl_range {X : Type} [Group X] {x : X} (hxJ : x ∈ generalizedFitting X)
    [(generalizedFitting X).Normal] : (cenIncl hxJ).range.Normal := by
  rw [cenIncl_range]
  refine ⟨fun a ha g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  exact (inferInstance : (generalizedFitting X).Normal).conj_mem _ ha g

theorem odd_ker_comp {A B P : Type} [Group A] [Group B] [Group P] (ι : A →* B)
    (hι : Function.Injective ι) (ρ : B →* P) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k)) :
    ∀ k ∈ (ρ.comp ι).ker, Odd (orderOf k) := by
  intro k hk
  have h := hodd _ (show ι k ∈ ρ.ker from hk)
  rwa [orderOf_injective ι hι k] at h

theorem normal_range_comp {A B P : Type} [Group A] [Group B] [Group P] (ι : A →* B)
    (ρ : B →* P) (hρ : Function.Surjective ρ) (hι : ι.range.Normal) :
    (ρ.comp ι).range.Normal := by
  rw [MonoidHom.range_comp]
  exact hι.map ρ hρ

theorem conjNormal_fitting_injective {X : Type} [Group X] [Finite X]
    [(generalizedFitting X).Normal] (hs : IsSimpleGroup ↥(generalizedFitting X))
    (hn : ∃ a b : ↥(generalizedFitting X), a * b ≠ b * a) :
    Function.Injective (MulAut.conjNormal : X →* MulAut ↥(generalizedFitting X)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcent : g ∈ centralizer ((generalizedFitting X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := congrArg (fun φ : MulAut ↥(generalizedFitting X) => (φ ⟨h, hh⟩ : X)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have hgJ : g ∈ generalizedFitting X := CFSG.centralizer_generalizedFitting_le X hcent
  have hz : (⟨g, hgJ⟩ : ↥(generalizedFitting X)) ∈ center ↥(generalizedFitting X) := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcent k k.2)
  have hbot : center ↥(generalizedFitting X) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (center ↥(generalizedFitting X)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      have ha : a ∈ center ↥(generalizedFitting X) := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  rw [hbot, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem conjNormal_mem_stabilizer {X : Type} [Group X] [(generalizedFitting X).Normal] {x : X}
    (hxJ : x ∈ generalizedFitting X) {c : X} (hc : c ∈ centralizer ({x} : Set X)) :
    (MulAut.conjNormal c : MulAut ↥(generalizedFitting X)) ∈
      MulAction.stabilizer (MulAut ↥(generalizedFitting X))
        (⟨x, hxJ⟩ : ↥(generalizedFitting X)) := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  show c * x * c⁻¹ = x
  rw [Subgroup.mem_centralizer_singleton_iff.1 hc, mul_assoc, mul_inv_cancel, mul_one]

theorem dvd_card_of_surjective {C P : Type} [Group C] [Group P] (ρ : C →* P)
    (hρ : Function.Surjective ρ) {n : ℕ} (hn : Nat.card P = n) : n ∣ Nat.card C := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have h2 : Nat.card (C ⧸ ρ.ker) = Nat.card P :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
  rw [h1, h2, hn]
  exact Dvd.intro _ rfl

end XLevel

theorem xlevel {X : Type} [Group X] [Finite X] (x : X) (hx : orderOf x = 2)
    (hxJ : x ∈ generalizedFitting X) (hs : IsSimpleGroup ↥(generalizedFitting X))
    (hn : ∃ a b : ↥(generalizedFitting X), a * b ≠ b * a)
    (hT : ∃ T : Sylow 2 X, ∀ t ∈ (T : Subgroup X), t * x = x * t)
    {P : Type} [Group P] [Finite P] (zc : P) (hP : BarShape P zc)
    (ρ : ↥(centralizer ({x} : Set X)) →* P) (hρ : Function.Surjective ρ)
    (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k))
    (hρx : ρ ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = zc) :
    IsCentralInvolution (⟨x, hxJ⟩ : ↥(generalizedFitting X)) ∧
    (∃ ρJ : ↥(centralizer ({(⟨x, hxJ⟩ : ↥(generalizedFitting X))} :
        Set ↥(generalizedFitting X))) →* P,
      (∀ k ∈ ρJ.ker, Odd (orderOf k)) ∧
      ρJ ⟨⟨x, hxJ⟩, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = zc ∧ ρJ.range.Normal) ∧
    192 ∣ Nat.card ↥(MulAction.stabilizer (MulAut ↥(generalizedFitting X))
      (⟨x, hxJ⟩ : ↥(generalizedFitting X))) := by
  obtain ⟨T, hT⟩ := hT
  have hJnorm : (generalizedFitting X).Normal := LocalCores.generalized_fitting_characteristic.2
  refine ⟨XLevel.isCentralInvolution_fitting hx hxJ T hT,
    ⟨ρ.comp (XLevel.cenIncl hxJ),
      XLevel.odd_ker_comp _ (XLevel.cenIncl_injective hxJ) ρ hodd, hρx,
      XLevel.normal_range_comp _ ρ hρ (XLevel.normal_cenIncl_range hxJ)⟩, ?_⟩
  have hle : (centralizer ({x} : Set X)).map
      (MulAut.conjNormal : X →* MulAut ↥(generalizedFitting X)) ≤
      MulAction.stabilizer (MulAut ↥(generalizedFitting X))
        (⟨x, hxJ⟩ : ↥(generalizedFitting X)) := by
    rintro _ ⟨c, hc, rfl⟩
    exact XLevel.conjNormal_mem_stabilizer hxJ hc
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (XLevel.conjNormal_fitting_injective hs hn)] at h1
  exact (XLevel.dvd_card_of_surjective ρ hρ hP.card_eq).trans h1

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
