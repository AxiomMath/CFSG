module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_eq_of_isSylowTwoIn {t : G} {S P : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G))) (hP : IsPGroup 2 P) (hSP : S ≤ P) :
    P ⊓ centralizer ({t} : Set G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.2
  have hle : S.subgroupOf (centralizer ({t} : Set G)) ≤
      (P ⊓ centralizer ({t} : Set G)).subgroupOf (centralizer ({t} : Set G)) :=
    Subgroup.subgroupOf_mono _ (le_inf hSP hS.1)
  have hp : IsPGroup 2 ((P ⊓ centralizer ({t} : Set G)).subgroupOf
      (centralizer ({t} : Set G))) := hP.to_inf_left.comap_subtype
  have hmax : (P ⊓ centralizer ({t} : Set G)).subgroupOf (centralizer ({t} : Set G)) =
      S.subgroupOf (centralizer ({t} : Set G)) := by
    have h1 := Sylow.is_maximal' Q hp (by rw [hQ]; exact hle)
    rwa [hQ] at h1
  have hmap := congrArg (Subgroup.map (centralizer ({t} : Set G)).subtype) hmax
  rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right,
    Subgroup.map_subgroupOf_eq_of_le hS.1] at hmap

theorem isExtremalIn_of_isSylowTwoIn {t : G} {S P : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G)))
    (hPS : P ⊓ centralizer ({t} : Set G) = S) :
    CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.2
  have hp : IsPGroup 2 S := by
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({t} : Set G))) := hQ ▸ Q.isPGroup'
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1)
  have hidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G)) := by
    have h1 : S.relIndex (centralizer ({t} : Set G)) =
        (S.subgroupOf (centralizer ({t} : Set G))).index := rfl
    rw [h1]
    rw [← hQ]
    exact Q.not_dvd_index
  change CFSG.GH74.GLS.Bg.Thompson.IsSylowIn 2 (P ⊓ centralizer ({t} : Set G))
    (centralizer ({t} : Set G))
  rw [hPS]
  exact ⟨hS.1, hp, hidx⟩

theorem commute_of_shear {t z x : G} (ht : orderOf t = 2) (hz : orderOf z = 2)
    {S : Subgroup G} (hS : IsSylowTwoIn S (centralizer ({t} : Set G))) (P : Sylow 2 G)
    (hSP : S ≤ (P : Subgroup G))
    (hZ : ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z ∨ w = t ∨ w = z * t)
    (hxP : x ∈ (P : Subgroup G)) (hxt : x⁻¹ * t * x = z * t) (hxz : x⁻¹ * z * x = z) :
    ∀ p ∈ (P : Subgroup G), p * z = z * p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer ({t} : Set G)
  obtain ⟨Q, hQ⟩ := hS.2
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hSp : IsPGroup 2 S := by
    have h1 : IsPGroup 2 (S.subgroupOf C) := hQ ▸ Q.isPGroup'
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1)
  have htS : t ∈ S := by
    have htCent : t ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (hS.1 hs)
    have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (S : Set G) :=
      (Subgroup.zpowers_le.mpr htCent).trans (Subgroup.centralizer_le_normalizer (S : Set G))
    have hzt2 : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, ht])
    have hsup2 : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers t) :=
      IsPGroup.to_sup_of_normal_left' hSp hzt2 hnorm
    have hsupC : S ⊔ Subgroup.zpowers t ≤ C :=
      sup_le hS.1 (Subgroup.zpowers_le.mpr htC)
    have hpSub : IsPGroup 2 ((S ⊔ Subgroup.zpowers t).subgroupOf C) := hsup2.comap_subtype
    have hle : (Q : Subgroup ↥C) ≤ (S ⊔ Subgroup.zpowers t).subgroupOf C := by
      rw [hQ]
      exact Subgroup.subgroupOf_mono C le_sup_left
    have heq : (S ⊔ Subgroup.zpowers t).subgroupOf C = S.subgroupOf C := by
      have h1 := Sylow.is_maximal' Q hpSub hle
      rwa [hQ] at h1
    have hmap := congrArg (Subgroup.map C.subtype) heq
    rw [Subgroup.map_subgroupOf_eq_of_le hsupC, Subgroup.map_subgroupOf_eq_of_le hS.1] at hmap
    exact Subgroup.zpowers_le.mp (hmap ▸ le_sup_right)
  have htP : t ∈ (P : Subgroup G) := hSP htS
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hbot
    have ht1 : t ∈ (⊥ : Subgroup G) := hbot ▸ htP
    rw [Subgroup.mem_bot] at ht1
    rw [ht1] at ht
    simp at ht
  have : Nontrivial ↥(P : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (P : Subgroup G)).mpr hPne
  have hcenter : Nontrivial (Subgroup.center ↥(P : Subgroup G)) :=
    IsPGroup.center_nontrivial P.isPGroup'
  have hcentP : IsPGroup 2 (Subgroup.center ↥(P : Subgroup G)) :=
    P.isPGroup'.to_subgroup (Subgroup.center ↥(P : Subgroup G))
  have hcard : 2 ∣ Nat.card (Subgroup.center ↥(P : Subgroup G)) := by
    obtain ⟨n, hn0, hn⟩ := (IsPGroup.nontrivial_iff_card hcentP).mp hcenter
    exact hn.symm ▸ dvd_pow_self 2 (ne_of_gt hn0)
  obtain ⟨wC, hwCord⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  let w : G := (wC : ↥(P : Subgroup G))
  have hword : orderOf w = 2 := by
    have h1 : orderOf w = orderOf (wC : ↥(P : Subgroup G)) :=
      Subgroup.orderOf_coe (wC : ↥(P : Subgroup G))
    have h2 : orderOf (wC : ↥(P : Subgroup G)) = orderOf wC :=
      Subgroup.orderOf_coe wC
    rw [h1, h2, hwCord]
  have hwcentral : ∀ p ∈ (P : Subgroup G), p * w = w * p := by
    intro p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp wC.2 ⟨p, hp⟩)
  have hwP : w ∈ (P : Subgroup G) := wC.1.2
  have hwt : t * w = w * t := hwcentral t htP
  have hwC : w ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm
  have hPp : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  have hPSinf : (P : Subgroup G) ⊓ C = S :=
    inf_centralizer_eq_of_isSylowTwoIn hS hPp hSP
  have hwS : w ∈ S := by
    rw [← hPSinf]
    exact ⟨hwP, hwC⟩
  have hwScent : ∀ s ∈ S, s * w = w * s := fun s hs => hwcentral s (hSP hs)
  have hxw : x⁻¹ * w * x = w := by
    have hcomm := hwcentral x hxP
    calc x⁻¹ * w * x = x⁻¹ * (w * x) := by group
      _ = x⁻¹ * (x * w) := by rw [← hcomm]
      _ = w := by group
  rcases hZ w hwS hwScent hword with hwz | hwt' | hwzt
  · intro p hp
    rw [← hwz]
    exact hwcentral p hp
  · exfalso
    have h1 : z * t = t := by
      rw [hwt', hxt] at hxw
      exact hxw
    have hz1 : z = 1 := by
      have h := congrArg (fun y => y * t⁻¹) h1
      calc z = (z * t) * t⁻¹ := by group
        _ = t * t⁻¹ := h
        _ = 1 := by group
    rw [hz1] at hz
    simp at hz
  · exfalso
    have hzz : z * z = 1 := by
      have h := pow_orderOf_eq_one z
      rw [hz, pow_two] at h
      exact h
    have h2 : x⁻¹ * (z * t) * x = z * t := by
      rw [← hwzt]
      exact hxw
    have h3 : z * (z * t) = z * t := by
      calc z * (z * t) = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by rw [hxz, hxt]
        _ = x⁻¹ * (z * t) * x := by group
        _ = z * t := h2
    have h1 : t = z * t := by
      calc t = (z * z) * t := by rw [hzz, one_mul]
        _ = z * (z * t) := by group
        _ = z * t := h3
    have hz1 : z = 1 := by
      have h := congrArg (fun y => y * t⁻¹) h1
      calc z = (z * t) * t⁻¹ := by group
        _ = t * t⁻¹ := h.symm
        _ = 1 := by group
    rw [hz1] at hz
    simp at hz

end CFSG.ComponentClassification.GrSLit.L34Sec5S
