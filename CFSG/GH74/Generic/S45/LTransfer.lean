module

public import CFSG.GH74.Generic.S45.PumpLeaves
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.Generic.S45

open CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12 CFSG.GH74.GLS.Stage1.Thm6.Sec12b
open Subgroup
open scoped commutatorElement

section Characters

theorem isCyclic_range_units_complex {H : Type} [Group H] [Finite H] (φ : H →* ℂˣ) :
    IsCyclic φ.range := by
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  exact isCyclic_of_injective_ringHom (R := ℂ) ((Units.coeHom ℂ).comp φ.range.subtype) (by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    exact h)

theorem exists_zpow_mem_ker_of_range_cyclic {H : Type} [Group H] [Finite H] (φ : H →* ℂˣ) :
    ∃ b : H, ∀ t : H, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ φ.ker := by
  have hc := isCyclic_range_units_complex φ
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨b, hb⟩ := φ.rangeRestrict_surjective g
  refine ⟨b, fun t => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (φ.rangeRestrict t))
  refine ⟨k, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow]
  have h1 : φ.rangeRestrict t = g ^ k := hk.symm
  have h2 : φ.rangeRestrict (b ^ k) = g ^ k := by rw [map_zpow, hb]
  have h3 : φ (b ^ k) = φ t := by
    have := congrArg (fun z : φ.range => (z : ℂˣ)) (h2.trans h1.symm)
    simpa using this
  rw [← map_zpow, h3, inv_mul_cancel]

theorem exists_hom_units_of_not_mem_commutator {H C : Type} [Group H] [Group C] [Finite C]
    (ι : H →* C) {h : H} (hh : ι h ∉ commutator C) :
    ∃ φ : H →* ℂˣ, (∀ k : H, ι k ∈ commutator C → φ k = 1) ∧ φ h ≠ 1 := by
  let ρ : H →* Abelianization C := Abelianization.of.comp ι
  have hρ : ρ h ≠ 1 := by
    intro h1
    apply hh
    rw [← Abelianization.ker_of C]
    exact h1
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization C) ℂ hρ
  refine ⟨χ.comp ρ, fun k hk => ?_, hχ⟩
  have h1 : ρ k = 1 := by
    rw [← Abelianization.ker_of C] at hk
    exact hk
  simp [h1]

end Characters

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylow2In_of_isSylow2In_top {T H : Subgroup G} (hT : IsSylow2In T ⊤) (hTH : T ≤ H) :
    IsSylow2In T H := by
  refine ⟨hTH, hT.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_index hTH
  have h2 : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [Subgroup.relIndex_top_right] at this
  intro hdvd
  exact h2 (h1 ▸ Dvd.dvd.mul_right hdvd _)

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self_eq_one {x : G} (hx : x * x = 1) :
    IsPGroup 2 ↥(zpowers x) := by
  intro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  show (x ^ m) ^ (2 ^ 1) = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hx2]

theorem mem_of_isSylow2In_centralizer {x : G} (hx : x * x = 1) {P : Subgroup G}
    (hP : IsSylow2In P (centralizer ({x} : Set G))) : x ∈ P := by
  have hzle : zpowers x ≤ centralizer ({x} : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  obtain ⟨P', hP', hxP'⟩ := exists_sylow2_ge (isPGroup_zpowers_of_mul_self_eq_one hx) hzle
  obtain ⟨c, hc, hPP'⟩ := sylow2_exists_conj hP hP'
  have hxP'' : x ∈ P' := hxP' (mem_zpowers x)
  rw [hPP', mem_Hconj] at hxP''
  have hcx : c * x * c⁻¹ = x := by
    have := mem_centralizer_singleton_iff.1 hc
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [this]
      _ = x := by group
  rwa [hcx] at hxP''

theorem exists_sylow_central_containing {y : G} {P S₀ : Subgroup G} (hP2 : IsPGroup 2 ↥P)
    (hPy : ∀ p ∈ P, p * y = y * p) (hS₀ : IsSylow2In S₀ ⊤) (hyS : y ∈ S₀)
    (hyc : ∀ s ∈ S₀, s * y = y * s) :
    ∃ Q : Subgroup G, P ≤ Q ∧ IsSylow2In Q ⊤ ∧ y ∈ Q ∧ ∀ q ∈ Q, q * y = y * q := by
  have hPC : P ≤ centralizer ({y} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2 (hPy p hp)
  have hS₀C : S₀ ≤ centralizer ({y} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hyc s hs)
  obtain ⟨Q, hQC, hPQ⟩ := exists_sylow2_ge hP2 hPC
  have hS₀' : IsSylow2In S₀ (centralizer ({y} : Set G)) := isSylow2In_of_isSylow2In_top hS₀ hS₀C
  obtain ⟨c, hcC, hQeq⟩ := sylow2_exists_conj hS₀' hQC
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hcC
  have hcy' : c * y * c⁻¹ = y := by
    rw [hcy]
    group
  refine ⟨Q, hPQ, ?_, ?_, ?_⟩
  · have h1 := sylow2_conj hS₀ c
    have h2 : Hconj c (⊤ : Subgroup G) = ⊤ := by
      ext a
      simp
    rw [h2, ← hQeq] at h1
    exact h1
  · rw [hQeq, mem_Hconj, hcy']
    exact hyS
  · intro q hq
    rw [hQeq, mem_Hconj] at hq
    have h1 := hyc _ hq
    have h2 : c * (q * y) * c⁻¹ = c * (y * q) * c⁻¹ := by
      calc c * (q * y) * c⁻¹ = c * q * c⁻¹ * (c * y * c⁻¹) := by group
        _ = c * q * c⁻¹ * y := by rw [hcy']
        _ = y * (c * q * c⁻¹) := h1
        _ = (c * y * c⁻¹) * (c * q * c⁻¹) := by rw [hcy']
        _ = c * (y * q) * c⁻¹ := by group
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact h3

end Sylow

section Fusion

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_centralizer_conj {x y : G} {Q P : Subgroup G}
    (hP : IsSylow2In P (centralizer ({x} : Set G))) (hyQ : y ∈ Q) (hyc : ∀ q ∈ Q, q * y = y * q)
    (hfus : ∀ g : G, g * y * g⁻¹ ∈ P → (∀ p ∈ P, p * (g * y * g⁻¹) = (g * y * g⁻¹) * p) →
      ∃ c ∈ centralizer ({x} : Set G), c * y * c⁻¹ = g * y * g⁻¹)
    {x' : G} (hx'Q : x' ∈ Q) (hconj : ∃ g : G, g⁻¹ * x * g = x') (hext : IsExtremal Q x') :
    ∃ h ∈ centralizer ({y} : Set G), x' = h * x * h⁻¹ := by
  obtain ⟨g, rfl⟩ := hconj
  have h1 : IsSylow2In (Hconj g P) (centralizer ({g⁻¹ * x * g} : Set G)) := by
    have := sylow2_conj hP g
    rwa [Hconj_centralizer] at this
  obtain ⟨d, hd, hdeq⟩ := sylow2_exists_conj h1 hext
  rw [Hconj_mul d g P] at hdeq
  have hd' : d * (g⁻¹ * x * g) = (g⁻¹ * x * g) * d := mem_centralizer_singleton_iff.1 hd
  have hx'eq : (g * d)⁻¹ * x * (g * d) = g⁻¹ * x * g := by
    calc (g * d)⁻¹ * x * (g * d) = d⁻¹ * (g⁻¹ * x * g) * d := by group
      _ = d⁻¹ * (d * (g⁻¹ * x * g)) := by rw [hd']; group
      _ = g⁻¹ * x * g := by group
  have hyx' : g⁻¹ * x * g * y = y * (g⁻¹ * x * g) := hyc _ hx'Q
  have hyP : y ∈ Hconj (g * d) P := by
    rw [← hdeq]
    exact ⟨hyQ, mem_centralizer_singleton_iff.2 hyx'.symm⟩
  have hyP' : (g * d) * y * (g * d)⁻¹ ∈ P := hyP
  have hcomm : ∀ p ∈ P, p * ((g * d) * y * (g * d)⁻¹) = ((g * d) * y * (g * d)⁻¹) * p := by
    intro p hp
    have hq : (g * d)⁻¹ * p * (g * d) ∈ Hconj (g * d) P := by
      show (g * d) * ((g * d)⁻¹ * p * (g * d)) * (g * d)⁻¹ ∈ P
      simpa [mul_assoc] using hp
    rw [← hdeq] at hq
    have h2 := hyc _ hq.1
    calc p * ((g * d) * y * (g * d)⁻¹)
        = (g * d) * (((g * d)⁻¹ * p * (g * d)) * y) * (g * d)⁻¹ := by group
      _ = (g * d) * (y * ((g * d)⁻¹ * p * (g * d))) * (g * d)⁻¹ := by rw [h2]
      _ = ((g * d) * y * (g * d)⁻¹) * p := by group
  obtain ⟨c, hcx, hcy⟩ := hfus (g * d) hyP' hcomm
  have hcx' : c * x = x * c := mem_centralizer_singleton_iff.1 hcx
  refine ⟨(g * d)⁻¹ * c, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    calc (g * d)⁻¹ * c * y = (g * d)⁻¹ * (c * y * c⁻¹) * c := by group
      _ = (g * d)⁻¹ * ((g * d) * y * (g * d)⁻¹) * c := by rw [hcy]
      _ = y * ((g * d)⁻¹ * c) := by group
  · rw [← hx'eq]
    calc (g * d)⁻¹ * x * (g * d) = (g * d)⁻¹ * (x * c * c⁻¹) * (g * d) := by group
      _ = (g * d)⁻¹ * (c * x * c⁻¹) * (g * d) := by rw [← hcx']
      _ = ((g * d)⁻¹ * c) * x * ((g * d)⁻¹ * c)⁻¹ := by group

end Fusion

section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_commutator_of_fusion (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {x y : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxy : x ∈ centralizer ({y} : Set G))
    {P Q : Subgroup G} (hP : IsSylow2In P (centralizer ({x} : Set G)))
    (hQ : IsSylow2In Q ⊤) (hxQ : x ∈ Q) (hyQ : y ∈ Q) (hyc : ∀ q ∈ Q, q * y = y * q)
    (hfus : ∀ g : G, g * y * g⁻¹ ∈ P → (∀ p ∈ P, p * (g * y * g⁻¹) = (g * y * g⁻¹) * p) →
      ∃ c ∈ centralizer ({x} : Set G), c * y * c⁻¹ = g * y * g⁻¹) :
    (⟨x, hxy⟩ : ↥(centralizer ({y} : Set G))) ∈ commutator ↥(centralizer ({y} : Set G)) := by
  by_contra hnot
  have hQC : Q ≤ centralizer ({y} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.2 (hyc q hq)
  let ι : ↥Q →* ↥(centralizer ({y} : Set G)) := Subgroup.inclusion hQC
  obtain ⟨φ, hφ1, hφx⟩ :=
    exists_hom_units_of_not_mem_commutator ι (h := (⟨x, hxQ⟩ : ↥Q)) hnot
  let N : Subgroup G := φ.ker.map Q.subtype
  have hNQ : N ≤ Q := Subgroup.map_subtype_le _
  have hmemN : ∀ (z : G) (hz : z ∈ Q), z ∈ N ↔ φ ⟨z, hz⟩ = 1 := by
    intro z hz
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro h
      exact ⟨⟨z, hz⟩, h, rfl⟩
  have hnorm : ∀ t ∈ Q, ∀ q ∈ N, t * q * t⁻¹ ∈ N := by
    intro t ht q hq
    have hqQ : q ∈ Q := hNQ hq
    have hmem : t * q * t⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem ht hqQ) (Q.inv_mem ht)
    rw [hmemN _ hmem]
    have h1 := (hmemN q hqQ).1 hq
    have : (⟨t * q * t⁻¹, hmem⟩ : ↥Q) = ⟨t, ht⟩ * ⟨q, hqQ⟩ * ⟨t, ht⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
  have hxN : x ∉ N := fun h => hφx ((hmemN x hxQ).1 h)
  have hne : N ≠ Q := fun h => hxN (h ▸ hxQ)
  obtain ⟨b, hb⟩ := exists_zpow_mem_ker_of_range_cyclic φ
  have hcyc : ∃ b ∈ Q, ∀ t ∈ Q, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ N := by
    refine ⟨(b : G), b.2, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := hb ⟨t, ht⟩
    refine ⟨k, ⟨(b ^ k)⁻¹ * ⟨t, ht⟩, hk, ?_⟩⟩
    simp
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hord : ∀ v ∈ Q, v ∉ N → orderOf x ≤ orderOf v := by
    intro v _ hvN
    have hv1 : v ≠ 1 := fun h => hvN (h ▸ N.one_mem)
    have hpos : 0 < orderOf v := orderOf_pos v
    have hne1 : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.1 h)
    rw [hxord]
    omega
  have hext2 : ∀ x' ∈ Q, (∃ g : G, g⁻¹ * x * g = x') → IsExtremal Q x' → x⁻¹ * x' ∈ N := by
    intro x' hx'Q hconj hextr
    obtain ⟨h, hh, hx'⟩ := exists_mem_centralizer_conj hP hyQ hyc hfus hx'Q hconj hextr
    have hmem : x⁻¹ * x' ∈ Q := Q.mul_mem (Q.inv_mem hxQ) hx'Q
    rw [hmemN _ hmem]
    apply hφ1
    have : ι ⟨x⁻¹ * x', hmem⟩ = ⁅(⟨x, hxy⟩ : ↥(centralizer ({y} : Set G)))⁻¹, ⟨h, hh⟩⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, ι, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inclusion, inv_inv]
      rw [hx']
      group
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨g₀, hg₀N, hg₀ext⟩ := transfer_conj ig_15_15 hs hnab hQ hNQ hnorm hne hcyc hxQ hxN hord
    (fun x' hx'Q hconj hextr => Or.inr (hext2 x' hx'Q hconj hextr))
  have h1 := hext2 _ (hNQ hg₀N) ⟨g₀, rfl⟩ hg₀ext
  apply hxN
  have : x = (g₀⁻¹ * x * g₀) * (x⁻¹ * (g₀⁻¹ * x * g₀))⁻¹ := by group
  rw [this]
  exact N.mul_mem hg₀N (N.inv_mem h1)

end Core

theorem b_III8_6_3 : B_III8_6_3 := by
  intro G _ _ hs hnab x hx P hP y hyP hyc _ hS hfus
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsSylow2In P (centralizer ({x} : Set G)) := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  obtain ⟨S₀, hS₀, hyS, hycS⟩ := hS
  have hS₀' : IsSylow2In S₀ ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS₀
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, pow_two] at this
    exact this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hxy : x ∈ centralizer ({y} : Set G) := by
    have := mem_centralizer_singleton_iff.1 (hP'.1 hyP)
    exact mem_centralizer_singleton_iff.2 this.symm
  obtain ⟨Q, hPQ, hQ, hyQ, hycQ⟩ := exists_sylow_central_containing hP'.2.1 hyc hS₀' hyS hycS
  have hxQ : x ∈ Q := hPQ (mem_of_isSylow2In_centralizer hx2 hP')
  exact ⟨hxy, mem_commutator_of_fusion hs hnab hx2 hx1 hxy hP' hQ hxQ hyQ hycQ hfus⟩

end CFSG.GH74.Generic.S45
