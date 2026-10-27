module

public import CFSG.GH74.Uniqueness.SU.SU13TC2CBar
public import CFSG.GH74.Uniqueness.SU.KI8CStmt
public import CFSG.GH74.Uniqueness.SU.SU13TC1Main

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G]

theorem kI8c_out (hKI8c : K.KI8c) {C : Subgroup G}
    (hone : K.OneInvClass (Mbar C))
    {z : G} (hzC : z ∈ C) (hz : orderOf z = 2)
    {R : Subgroup G} (hR : IsSylowIn C R) (hzR : z ∈ R) (hRz : ∀ r ∈ R, r * z = z * r)
    {E : Subgroup G} (hE : oc (C ⊓ centralizer ({z} : Set G)) = E)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hkl : Nonempty (Mbar (C ⊓ centralizer ({z} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    (E ≤ oc C ∧ (Nonempty (Mbar C ≃* A4) ∨ CFSG.Blueprint.LieModel (Mbar C) .PSL 2 5 1)) ∨
    (Nat.card (E ⊓ oc C : Subgroup G) * 3 = Nat.card E ∧
      (CFSG.Blueprint.LieModel (Mbar C) .PSL 2 11 1 ∨ CFSG.Blueprint.LieModel (Mbar C) .PSL 2 13 1)) := by
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hMC : M ≤ C := inf_le_left
  let zc : ↥C := ⟨z, hzC⟩
  have hzc2 : zc * zc = 1 := by
    apply Subtype.ext
    change z * z = 1
    rw [← sq]; exact sq_eq_one_of_orderOf_eq_two hz
  have hzcord : orderOf zc = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz
  set zb : Mbar C := proj C zc with hzb
  have hzb1 : zb ≠ 1 := by
    intro h
    have h1 : zc ∈ pPrimeCore 2 ↥C := by
      rw [← ker_proj C]; exact h
    have h2 : z ∈ oc C := mem_oc.mpr ⟨hzC, h1⟩
    exact not_mem_oc_of_involution hz h2
  have hzb2 : orderOf zb = 2 := by
    refine orderOf_eq_prime ?_ hzb1
    rw [hzb, ← map_pow]
    have : zc ^ 2 = 1 := by rw [pow_two]; exact hzc2
    rw [this, map_one]
  obtain ⟨T, hT⟩ := exists_sylow_barImage C hR
  have hzbT : zb ∈ (T : Subgroup (Mbar C)) := by
    rw [hT]; exact (mem_barImage C).mpr ⟨zc, hzR, rfl⟩
  have hTc : ∀ t ∈ (T : Subgroup (Mbar C)), t * zb = zb * t := by
    intro t ht
    rw [hT] at ht
    obtain ⟨r, hr, rfl⟩ := (mem_barImage C).mp ht
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hRz r hr
  have hcomm : ∀ m : ↥M, proj C (Subgroup.inclusion hMC m) * zb = zb * proj C (Subgroup.inclusion hMC m) := by
    intro m
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp m.2).2)
  let Φ : ↥M →* ↥(centralizer ({zb} : Set (Mbar C))) :=
    ((proj C).comp (Subgroup.inclusion hMC)).codRestrict (centralizer ({zb} : Set (Mbar C)))
      (fun m => mem_centralizer_singleton_iff.mpr (hcomm m))
  have hΦ : Function.Surjective Φ := by
    intro y
    have hy : y.1 ∈ (centralizer ({zc} : Set ↥C)).map (proj C) :=
      (centralizer_map_eq (proj C) (proj_surjective C) (odd_card_ker_proj C) hzc2).le y.2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    have hcM : (c : G) ∈ M := mem_inf.mpr ⟨c.2, by
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp hc
      exact congrArg Subtype.val this⟩
    refine ⟨⟨c, hcM⟩, Subtype.ext ?_⟩
    exact hcy
  have hΦker : ∀ m : ↥M, Φ m = 1 ↔ (⟨(m : G), hMC m.2⟩ : ↥C) ∈ pPrimeCore 2 ↥C := by
    intro m
    constructor
    · intro h
      have h1 : proj C (Subgroup.inclusion hMC m) = 1 := congrArg Subtype.val h
      rw [← ker_proj C]; exact h1
    · intro h
      apply Subtype.ext
      have : proj C (Subgroup.inclusion hMC m) = 1 := by
        rw [← MonoidHom.mem_ker, ker_proj C]; exact h
      exact this
  have hkerodd : ¬ 2 ∣ Nat.card Φ.ker := by
    let κ : ↥Φ.ker →* ↥(pPrimeCore 2 ↥C) :=
      ((Subgroup.inclusion hMC).comp Φ.ker.subtype).codRestrict (pPrimeCore 2 ↥C)
        (fun m => (hΦker m.1).mp m.2)
    have hinj : Function.Injective κ := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥(pPrimeCore 2 ↥C) => ((w : ↥C) : G)) hab
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
    have := Odd.of_dvd_nat hodd hdvd
    intro h2
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  have hpre := (CFSG.prime_complement_kernel_core_preimage (p := 2) Φ hΦ hkerodd).1
  let ψ : ↥M →* K.CBar (Mbar C) zb :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({zb} : Set (Mbar C))))).comp Φ
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer ({zb} : Set (Mbar C))))).comp hΦ
  have hψker : ψ.ker = pPrimeCore 2 ↥M := by
    rw [← hpre]
    ext m
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  let e1 : Mbar M ≃* K.CBar (Mbar C) zb :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  obtain ⟨κ⟩ := hkl
  have hGL' : Nonempty (K.CBar (Mbar C) zb ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    ⟨e1.symm.trans κ⟩
  have hO : pPrimeCore 2 (Mbar C) = ⊥ := GLS.pPrimeCore_quotient_eq_bot (↥C)
  let ρ : ↥M →* Mbar C := (proj C).comp (Subgroup.inclusion hMC)
  have hEM : E ≤ M := hE ▸ oc_le M
  have hEC : E ≤ C := hEM.trans hMC
  have hmemE : ∀ m : ↥M, (m : G) ∈ E ↔ m ∈ pPrimeCore 2 ↥M := by
    intro m
    rw [← hE]
    constructor
    · intro h
      exact (mem_oc.mp h).2
    · intro h
      exact mem_oc.mpr ⟨m.2, h⟩
  have hOCmem : ∀ x : Mbar C, x ∈ K.OC (Mbar C) zb ↔ ∃ m : ↥M, (m : G) ∈ E ∧ ρ m = x := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨m, rfl⟩ := hΦ y
      have hm : m ∈ pPrimeCore 2 ↥M := by
        rw [← hpre]; exact hy
      exact ⟨m, (hmemE m).mpr hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      have hm' : m ∈ pPrimeCore 2 ↥M := (hmemE m).mp hm
      rw [← hpre] at hm'
      exact ⟨Φ m, hm', rfl⟩
  have hOCab : Open.IsElemAbelian 3 (K.OC (Mbar C) zb) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m₁, hm₁, h₁⟩ := (hOCmem a.1).mp a.2
      obtain ⟨m₂, hm₂, h₂⟩ := (hOCmem b.1).mp b.2
      apply Subtype.ext
      change (a : Mbar C) * b = b * a
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEab _ hm₁ _ hm₂)
    · obtain ⟨m, hm, rfl⟩ := (hOCmem x).mp hx
      rw [← map_pow]
      have : m ^ 3 = 1 := Subtype.ext (hE3 _ hm)
      rw [this, map_one]
  let ρE : ↥E →* Mbar C := (proj C).comp (Subgroup.inclusion hEC)
  have hρErange : ρE.range = K.OC (Mbar C) zb := by
    ext x
    rw [hOCmem]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.1, hEM a.2⟩, a.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m.1, hm⟩, rfl⟩
  have hρEker : ρE.ker = (E ⊓ oc C : Subgroup G).subgroupOf E := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (Subgroup.inclusion hEC a) ∈ pPrimeCore 2 ↥C := by rw [← ker_proj C]; exact h
      exact mem_inf.mpr ⟨a.2, mem_oc.mpr ⟨hEC a.2, h1⟩⟩
    · intro h
      obtain ⟨-, h2⟩ := mem_inf.mp h
      obtain ⟨hh3, h3⟩ := mem_oc.mp h2
      show proj C (Subgroup.inclusion hEC a) = 1
      rw [← MonoidHom.mem_ker, ker_proj C]
      exact h3
  have hcardE : Nat.card ρE.ker * Nat.card (K.OC (Mbar C) zb) = Nat.card E := by
    have := Subgroup.card_ker_mul_card_range ρE
    rwa [hρErange] at this
  have hcardker : Nat.card ρE.ker = Nat.card (E ⊓ oc C : Subgroup G) := by
    rw [hρEker]
    have h1 : Nat.card (((E ⊓ oc C : Subgroup G).subgroupOf E).map E.subtype) =
        Nat.card ((E ⊓ oc C : Subgroup G).subgroupOf E) :=
      Subgroup.card_map_of_injective E.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_left : E ⊓ oc C ≤ E)] at h1
    exact h1.symm
  rw [hcardker] at hcardE
  have hc := hKI8c (Mbar C) hO hone T zb hzbT hzb2 hTc hGL' hOCab
  rcases hc with ⟨hbot, hmodel⟩ | ⟨hthree, hmodel⟩
  · left
    refine ⟨?_, hmodel⟩
    have h1 : Nat.card (K.OC (Mbar C) zb) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [h1, mul_one] at hcardE
    have heq : E ⊓ oc C = E :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ oc C ≤ E) (by rw [hcardE])
    intro x hx
    have hx' : x ∈ E ⊓ oc C := heq.symm ▸ hx
    exact hx'.2
  · right
    refine ⟨?_, hmodel⟩
    rw [hthree] at hcardE
    exact hcardE

end CFSG.GH74.Uniqueness.SU.SU13
