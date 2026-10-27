module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A P : Type} [Group A] [Group P] {ρ : A →* P}

theorem isSubnormal_subgroupOf_of_normal_le {G : Type*} [Group G] {H K C : Subgroup G}
    (hHK : H ≤ K) (hKC : K ≤ C) (hn : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hK : (K.subgroupOf C).IsSubnormal) : (H.subgroupOf C).IsSubnormal := by
  have hle : H.subgroupOf C ≤ K.subgroupOf C := fun x hx => hHK hx
  have hnorm : ((H.subgroupOf C).subgroupOf (K.subgroupOf C)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact hn (k : G) hk (h : G) hh
  exact Subgroup.IsSubnormal.trans hle hnorm.isSubnormal hK

@[expose] def coverDerived (ρ : A →* P) (X : Subgroup P) : Subgroup A :=
  (commutator ↥(X.comap ρ)).map (X.comap ρ).subtype

theorem coverDerived_le (X : Subgroup P) : coverDerived ρ X ≤ X.comap ρ :=
  Subgroup.map_subtype_le _

theorem conj_mem_coverDerived (X : Subgroup P) {k h : A} (hk : k ∈ X.comap ρ)
    (hh : h ∈ coverDerived ρ X) : k * h * k⁻¹ ∈ coverDerived ρ X := by
  obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
  refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * h' * ⟨k, hk⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (commutator ↥(X.comap ρ)).Normal).conj_mem h' hh' ⟨k, hk⟩

@[expose] def coverDerivedHom (ρ : A →* P) (X : Subgroup P) : ↥(coverDerived ρ X) →* ↥X :=
  (ρ.comp (coverDerived ρ X).subtype).codRestrict X (fun a => coverDerived_le (ρ := ρ) X a.2)

namespace OddCentralCover

variable (h : OddCentralCover ρ)
include h

theorem subgroupComap_ker_le_center (X : Subgroup P) :
    (ρ.subgroupComap X).ker ≤ center ↥(X.comap ρ) := by
  intro p hp
  have hp1 : ρ (p : A) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
  have hc : (p : A) ∈ center A := h.ker_le_center (MonoidHom.mem_ker.mpr hp1)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (g : A))

theorem exists_mem_coverDerived {X : Subgroup P} (hX : CFSG.IsQuasisimple ↥X) {q : P}
    (hq : q ∈ X) : ∃ a ∈ coverDerived ρ X, ρ a = q := by
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective
    (ρ.subgroupComap X) (MonoidHom.subgroupComap_surjective ρ X h.surjective)
    (h.subgroupComap_ker_le_center X) hX.1
  obtain ⟨c, hc⟩ := hsurj ⟨q, hq⟩
  refine ⟨((c : ↥(X.comap ρ)) : A), Subgroup.mem_map.mpr ⟨(c : ↥(X.comap ρ)), c.2, rfl⟩, ?_⟩
  exact congrArg Subtype.val hc

theorem isQuasisimple_coverDerived {X : Subgroup P} (hX : CFSG.IsQuasisimple ↥X) :
    CFSG.IsQuasisimple ↥(coverDerived ρ X) := by
  have h1 := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective
    (ρ.subgroupComap X) (MonoidHom.subgroupComap_surjective ρ X h.surjective)
    (h.subgroupComap_ker_le_center X) hX
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((commutator ↥(X.comap ρ)).equivMapOfInjective (X.comap ρ).subtype
      (X.comap ρ).subtype_injective) h1

theorem mem_coverDerived {X : Subgroup P} (hX : CFSG.IsQuasisimple ↥X) {w : A} (hw : w * w = 1)
    (hwX : ρ w ∈ X) : w ∈ coverDerived ρ X := by
  obtain ⟨x, hx, hxw⟩ := h.exists_mem_coverDerived hX hwX
  rw [← h.pow_card_ker_eq hw hxw]
  exact Subgroup.pow_mem _ hx _

theorem exists_mul_self_eq_one_mem_coverDerived {X : Subgroup P} (hX : CFSG.IsQuasisimple ↥X)
    {u : P} (hu : u * u = 1) (huX : u ∈ X) :
    ∃ a ∈ coverDerived ρ X, a * a = 1 ∧ ρ a = u := by
  obtain ⟨x, hx, hxu⟩ := h.exists_mem_coverDerived hX huX
  have hpow := h.pow_card_ker (a := x) (by rw [hxu]; exact hu)
  exact ⟨x ^ Nat.card ρ.ker, Subgroup.pow_mem _ hx _, hpow.1, by rw [hpow.2, hxu]⟩

theorem isComponentIn_coverDerived {w : A} (hw : w * w = 1) {X : Subgroup P}
    (hX : IsComponentIn X (centralizer ({ρ w} : Set P))) :
    IsComponentIn (coverDerived ρ X) (centralizer ({w} : Set A)) := by
  have hq : CFSG.IsQuasisimple ↥X := hX.isQuasisimple
  have hPre : X.comap ρ ≤ centralizer ({w} : Set A) := by
    intro a ha
    exact (SetLike.ext_iff.mp (h.centralizer_singleton_eq_comap hw) a).mpr (hX.1 ha)
  have hle : coverDerived ρ X ≤ centralizer ({w} : Set A) := (coverDerived_le X).trans hPre
  have hmem : ∀ c : ↥(centralizer ({w} : Set A)), ρ (c : A) ∈ centralizer ({ρ w} : Set P) := by
    intro c
    exact (SetLike.ext_iff.mp (h.centralizer_singleton_eq_comap hw) (c : A)).mp c.2
  let ψ : ↥(centralizer ({w} : Set A)) →* ↥(centralizer ({ρ w} : Set P)) :=
    ((ρ.comp (centralizer ({w} : Set A)).subtype)).codRestrict _ hmem
  have h1 : (((X.subgroupOf (centralizer ({ρ w} : Set P)))).comap ψ).IsSubnormal :=
    hX.2.2.comap ψ
  have h2 : (X.comap ρ).subgroupOf (centralizer ({w} : Set A)) =
      ((X.subgroupOf (centralizer ({ρ w} : Set P)))).comap ψ := by
    ext c
    rfl
  rw [← h2] at h1
  refine ⟨hle, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (h.isQuasisimple_coverDerived hq)
  · exact isSubnormal_subgroupOf_of_normal_le (coverDerived_le X) hPre
      (fun k hk x hx => conj_mem_coverDerived X hk hx) h1

theorem oddCentralCover_coverDerivedHom {X : Subgroup P} (hX : CFSG.IsQuasisimple ↥X) :
    OddCentralCover (coverDerivedHom ρ X) := by
  have hker : ∀ p : ↥(coverDerived ρ X), p ∈ (coverDerivedHom ρ X).ker → (p : A) ∈ ρ.ker := by
    intro p hp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
  refine ⟨?_, ?_, ?_⟩
  · intro q
    obtain ⟨a, ha, haq⟩ := h.exists_mem_coverDerived hX q.2
    exact ⟨⟨a, ha⟩, Subtype.ext haq⟩
  · intro p hp
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (h.ker_le_center (hker p hp)) (g : A))
  · have hle : ((coverDerivedHom ρ X).ker).map (coverDerived ρ X).subtype ≤ ρ.ker := by
      rintro _ ⟨p, hp, rfl⟩
      exact hker p hp
    have hcard : Nat.card ((coverDerivedHom ρ X).ker) =
        Nat.card (((coverDerivedHom ρ X).ker).map (coverDerived ρ X).subtype) :=
      Nat.card_congr (((coverDerivedHom ρ X).ker).equivMapOfInjective _
        (coverDerived ρ X).subtype_injective).toEquiv
    rw [hcard]
    exact h.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end OddCentralCover

end CFSG.OddStandard.SmallF3.Omega
