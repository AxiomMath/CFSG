module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74.Generic CFSG.RankThree.PerfectCover Subgroup

variable {S L : Type} [Group S] [Group L]

theorem exists_section_of_odd [Finite S] (π : S →* L) (hπ : Function.Surjective π)
    (hk : π.ker ≤ center S) (hk2 : IsPGroup 2 ↥π.ker) {J : Subgroup L}
    (hJ : IsQuasisimple ↥J) {Y : Type} [Group Y] (e : ↥J ⧸ center ↥J ≃* Y)
    (hM : Odd (Nat.card (hopfMultiplier Y))) :
    ∃ D : Subgroup S, D.map π = J ∧ ∀ x ∈ D, π x = 1 → x = 1 := by
  classical
  set Jh : Subgroup S := J.comap π with hJh
  set f : ↥Jh →* ↥J := (π.comp Jh.subtype).codRestrict J (fun x => x.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨s, rfl⟩ := hπ j
    exact ⟨⟨s, hj⟩, rfl⟩
  have hfk : f.ker ≤ center ↥Jh := by
    intro x hx
    have hx' : (x : S) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hk hx') g)
  obtain ⟨-, hP, hsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective f hfs hfk hJ.1
  set D₀ : Subgroup ↥Jh := commutator ↥Jh with hD₀
  set g : ↥D₀ →* ↥J := f.comp D₀.subtype with hg
  have hgk : g.ker ≤ center ↥D₀ := by
    intro x hx
    have hxc : (x : ↥Jh) ∈ center ↥Jh := hfk hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc y)
  set g' : ↥D₀ →* Y := e.toMonoidHom.comp ((QuotientGroup.mk' (center ↥J)).comp g) with hg'
  have hg's : Function.Surjective g' :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hsurj)
  have hg'k : g'.ker = center ↥D₀ := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hP g hsurj hgk]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    change e (QuotientGroup.mk (g x)) = 1 ↔ g x ∈ center ↥J
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hZ : Odd (Nat.card ↥(center ↥D₀)) := by
    have hd := card_ker_dvd_hopfMultiplier hP g' hg's hg'k.le
    rw [hg'k] at hd
    exact Odd.of_dvd_nat hM hd
  have hginj : ∀ x : ↥D₀, g x = 1 → x = 1 := by
    intro x hx
    have hx1 : ((x : ↥Jh) : S) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    have hxZ : x ∈ center ↥D₀ := hgk hx
    obtain ⟨k, hk'⟩ := hk2 ⟨_, hx1⟩
    have hpow : x ^ (2 ^ k) = 1 := by
      have h1 : ((x : ↥Jh) : S) ^ (2 ^ k) = 1 := congrArg Subtype.val hk'
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    have hdvd1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    have hdvd2 : orderOf x ∣ Nat.card ↥(center ↥D₀) := Subgroup.orderOf_dvd_natCard _ hxZ
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(center ↥D₀)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZ)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2)
  refine ⟨D₀.map Jh.subtype, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨_, ⟨d, -, rfl⟩, rfl⟩
      exact d.2
    · intro hy
      obtain ⟨d, hd⟩ := hsurj ⟨y, hy⟩
      exact ⟨(d : ↥Jh), ⟨d, d.2, rfl⟩, congrArg Subtype.val hd⟩
  · rintro _ ⟨d, hd, rfl⟩ hx
    have h1 : g ⟨d, hd⟩ = 1 := Subtype.ext hx
    have h2 := hginj ⟨d, hd⟩ h1
    have h3 : d = 1 := congrArg Subtype.val h2
    rw [h3]
    rfl

theorem exists_commuting_lift [Finite S] (π : S →* L) (hπ : Function.Surjective π)
    (hk : π.ker ≤ center S) (hk2 : IsPGroup 2 ↥π.ker) {J : Subgroup L}
    (hJ : IsQuasisimple ↥J) {Y : Type} [Group Y] (e : ↥J ⧸ center ↥J ≃* Y)
    (hM : Odd (Nat.card (hopfMultiplier Y))) {u₁ u₂ : L} (hu₁ : u₁ ∈ J) (hu₂ : u₂ ∈ J)
    (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (h₁₂ : u₁ * u₂ = u₂ * u₁) :
    ∃ v₁ v₂ : S, π v₁ = u₁ ∧ π v₂ = u₂ ∧ v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ := by
  obtain ⟨D, hD, hinj⟩ := exists_section_of_odd π hπ hk hk2 hJ e hM
  have hu₁' : u₁ ∈ D.map π := by rw [hD]; exact hu₁
  have hu₂' : u₂ ∈ D.map π := by rw [hD]; exact hu₂
  obtain ⟨v₁, hv₁, rfl⟩ := hu₁'
  obtain ⟨v₂, hv₂, rfl⟩ := hu₂'
  refine ⟨v₁, v₂, rfl, rfl, ?_, ?_, ?_⟩
  · exact hinj _ (D.mul_mem hv₁ hv₁) (by rw [map_mul, h₁])
  · exact hinj _ (D.mul_mem hv₂ hv₂) (by rw [map_mul, h₂])
  · have hc := hinj (v₁ * v₂ * (v₂ * v₁)⁻¹)
      (D.mul_mem (D.mul_mem hv₁ hv₂) (D.inv_mem (D.mul_mem hv₂ hv₁)))
      (by rw [map_mul, map_inv, map_mul, map_mul, h₁₂, mul_inv_cancel])
    exact mul_inv_eq_one.1 hc

end CFSG.GH74.Generic.BProg.B2.T4.PGV
