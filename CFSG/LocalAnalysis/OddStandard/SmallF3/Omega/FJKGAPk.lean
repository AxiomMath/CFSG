module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fj_central_not_mem_pocket {A : Type} [Group A] [Finite A] {y z : A} {B : Subgroup A}
    (hy2 : y * y = 1) (hy1 : y ≠ 1) (hz : z ∈ center A) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hyz : y ≠ z) (hyB : y ∈ B) (hSL : IsSL23Mod ↥B) : z ∉ B := by
  intro hzB
  obtain ⟨e⟩ := hSL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddcard : Odd (Nat.card (CFSG.oddCore ↥B)) := by
    rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := ↥B)]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥B))
  set ψ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥B)) with hψ
  have hker : ∀ x : ↥B, x * x = 1 → ψ x = 1 → x = 1 := by
    intro x hxx hx
    have hmk : QuotientGroup.mk' (oddCore ↥B) x = 1 := by
      apply e.injective
      simpa [hψ] using hx
    have hmem : x ∈ oddCore ↥B := by
      have hmk' : (x : ↥B ⧸ oddCore ↥B) = 1 := by simpa using hmk
      exact (QuotientGroup.eq_one_iff (N := oddCore ↥B) x).mp hmk'
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hoddcard (Subgroup.orderOf_dvd_natCard _ hmem)
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have h1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  have hsl : ∀ g h : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      g * g = 1 → h * h = 1 → g ≠ 1 → h ≠ 1 → g * h = 1 := by
    decide +kernel
  let y' : ↥B := ⟨y, hyB⟩
  let z' : ↥B := ⟨z, hzB⟩
  have hy'2 : y' * y' = 1 := Subtype.ext hy2
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hψy : ψ y' ≠ 1 := fun h => hy'1 (hker y' hy'2 h)
  have hψz : ψ z' ≠ 1 := fun h => hz'1 (hker z' hz'2 h)
  have hψyy : ψ y' * ψ y' = 1 := by rw [← map_mul, hy'2, map_one]
  have hψzz : ψ z' * ψ z' = 1 := by rw [← map_mul, hz'2, map_one]
  have hcomm : y' * z' = z' * y' := Subtype.ext (Subgroup.mem_center_iff.mp hz y)
  have hyz2 : (y' * z') * (y' * z') = 1 := by
    calc (y' * z') * (y' * z') = y' * (z' * y') * z' := by group
      _ = y' * (y' * z') * z' := by rw [← hcomm]
      _ = (y' * y') * (z' * z') := by group
      _ = 1 := by rw [hy'2, hz'2, one_mul]
  have hyz1 : y' * z' = 1 :=
    hker _ hyz2 (by rw [map_mul]; exact hsl _ _ hψyy hψzz hψy hψz)
  apply hyz
  have h1 : y * z = 1 := congrArg Subtype.val hyz1
  calc y = y * (z * z) := by rw [hz2, mul_one]
    _ = (y * z) * z := by rw [mul_assoc]
    _ = z := by rw [h1, one_mul]

private theorem fj_isSubnormal_subgroupOf_trans {G : Type*} [Group G] {H K M : Subgroup G}
    (hHK : H ≤ K) (hKM : K ≤ M) (hH : (H.subgroupOf K).IsSubnormal)
    (hK : (K.subgroupOf M).IsSubnormal) : (H.subgroupOf M).IsSubnormal := by
  refine Subgroup.IsSubnormal.trans (K := K.subgroupOf M) (fun x hx => hHK hx) ?_ hK
  have h := hH.comap (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom
  convert h using 1
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem fj_pocket_map_cover {A C : Type} [Group A] [Group C] (φ : A →* C)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center A) {b : A} {B : Subgroup A}
    (hB : Sl23PocketIn ⊤ b B) (hdis : Disjoint B φ.ker) :
    Sl23PocketIn ⊤ (φ b) (B.map φ) := by
  obtain ⟨hbB, hBD, hsub, hSL⟩ := hB
  obtain ⟨D, hD⟩ : ∃ D : Subgroup A, D = ⊤ ⊓ centralizer ({b} : Set A) := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Subgroup C, D' = ⊤ ⊓ centralizer ({φ b} : Set C) := ⟨_, rfl⟩
  rw [← hD] at hBD hsub
  unfold Sl23PocketIn
  rw [← hD']
  have hmemD : ∀ g : A, g ∈ D ↔ g * b = b * g := fun g => by
    rw [hD, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨mem_top _, h⟩⟩
  have hmemD' : ∀ c : C, c ∈ D' ↔ c * φ b = φ b * c := fun c => by
    rw [hD', mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨mem_top _, h⟩⟩
  have hmemDt : ∀ g : A, g ∈ D'.comap φ ↔ φ g * φ b = φ b * φ g := fun g => by
    rw [mem_comap, hmemD']
  have hDDt : D ≤ D'.comap φ := by
    intro d hd
    rw [hmemDt, ← map_mul, ← map_mul, (hmemD d).mp hd]
  have hconj : ∀ g ∈ D'.comap φ, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    have hgb : φ g * φ b = φ b * φ g := (hmemDt g).mp hg
    have hdb : d * b = b * d := (hmemD d).mp hd
    set z : A := b⁻¹ * (g * b * g⁻¹) with hz
    have hφz : φ z = 1 := by
      simp only [hz, map_mul, map_inv]
      rw [hgb]
      group
    have hzc : ∀ x : A, x * z = z * x :=
      Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hφz))
    have hgbg : g * b * g⁻¹ = b * z := by rw [hz]; group
    set c : A := g * d * g⁻¹ with hcdef
    have hc : c * (b * z) = (b * z) * c := by
      rw [← hgbg]
      calc c * (g * b * g⁻¹) = g * (d * b) * g⁻¹ := by rw [hcdef]; group
        _ = g * (b * d) * g⁻¹ := by rw [hdb]
        _ = g * b * g⁻¹ * c := by rw [hcdef]; group
    have h3 : (c * b) * z = (b * c) * z := by
      calc (c * b) * z = c * (b * z) := mul_assoc _ _ _
        _ = (b * z) * c := hc
        _ = b * (z * c) := mul_assoc _ _ _
        _ = b * (c * z) := by rw [← hzc c]
        _ = (b * c) * z := (mul_assoc _ _ _).symm
    exact (hmemD c).mpr (mul_right_cancel h3)
  have hnormDt : (D.subgroupOf (D'.comap φ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj (g : A) g.2 (n : A) hn
  have hsubDt : (B.subgroupOf (D'.comap φ)).IsSubnormal :=
    fj_isSubnormal_subgroupOf_trans hBD hDDt hsub hnormDt.isSubnormal
  let ψ : ↥(D'.comap φ) →* ↥D' := φ.subgroupComap D'
  have hψ : Function.Surjective ψ := MonoidHom.subgroupComap_surjective φ D' hφ
  have heq : (B.subgroupOf (D'.comap φ)).map ψ = (B.map φ).subgroupOf D' := by
    ext ⟨c, hc⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨a, ha⟩, haB, haψ⟩
      exact ⟨a, haB, congrArg Subtype.val haψ⟩
    · rintro ⟨a, haB, hac⟩
      have ha : a ∈ D'.comap φ := by
        rw [mem_comap, hac]
        exact hc
      exact ⟨⟨a, ha⟩, haB, Subtype.ext hac⟩
  have hsubC : ((B.map φ).subgroupOf D').IsSubnormal := by
    rw [← heq]
    exact hsubDt.map hψ
  have hker0 : (φ.domRestrict B).ker = ⊥ := by
    rw [MonoidHom.ker_domRestrict]
    exact Subgroup.subgroupOf_eq_bot.mpr hdis.symm
  have hinj : Function.Injective (φ.domRestrict B) := (MonoidHom.ker_eq_bot_iff _).mp hker0
  have hsl : IsSL23Mod ↥(B.map φ) :=
    isSL23Mod_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range (f := φ) (K := B)))) hSL
  refine ⟨Subgroup.mem_map_of_mem φ hbB, ?_, hsubC, hsl⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [hmemD']
  rw [← map_mul, ← map_mul, (hmemD a).mp (hBD ha)]

end CFSG.OddStandard.SmallF3.Omega
