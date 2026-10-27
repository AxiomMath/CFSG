module

public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import all CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.HardMathSupport.Lang.Coordinator.ThreePrimeLift
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.Lift
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftCover

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Lang.Coordinator

theorem exists_mulEquiv_over
    {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (hq : 2 < p ^ f) {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3) (hz : Subgroup.center K ≠ ⊥) :
    ∃ φ : unitarySU p f F 3 ≃* K, ∀ s, e (QuotientGroup.mk (φ s)) = unitaryProj h 3 s := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  let β : unitarySU p f F 3 →* unitaryPSU h 3 := unitaryProj h 3
  let η : K →* unitaryPSU h 3 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hβ : Function.Surjective β := unitaryProj_surjective h 3
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : ∀ z, η z = 1 ↔ z ∈ Subgroup.center K := fun z => by
    change e (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hcen : η.ker ≤ Subgroup.center K := fun z hz => (hηker z).1 hz
  have hsec := CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central h.card_eq_sq h.one_le
    (n := 3) (by norm_num) (by decide) (fun hh => by simp only [Prod.mk.injEq] at hh; omega)
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := β) hη)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center (β := β) hcen)
  obtain ⟨α, hα, hαsurj⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.exists_surjective_lift hK hβ hcen hsec
  obtain ⟨⟨z, hzc⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have hz1 : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  obtain ⟨s, hs⟩ := hαsurj z
  have hβker : β.ker = unitaryScalars h 3 := ker_unitaryProj h 3
  have hsker : s ∈ β.ker := by
    rw [MonoidHom.mem_ker, ← hα, hs]
    exact (hηker z).2 hzc
  have hαker : α.ker ≤ unitaryScalars h 3 := fun t ht => by
    rw [← hβker, MonoidHom.mem_ker, ← hα, MonoidHom.mem_ker.1 ht, map_one]
  have hcard : Nat.card (unitaryScalars h 3) ∣ 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.ker_eq_bot_of_card_dvd_prime Nat.prime_three α hαker hcard
      ⟨s, hβker ▸ hsker, by rw [hs]; exact hz1⟩
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαsurj⟩, fun s => hα s⟩

theorem perfect_aut_eq_of_central {G : Type*} [Group G] (hG : commutator G = ⊤) (θ ζ : G ≃* G)
    (hc : ∀ s, θ s * (ζ s)⁻¹ ∈ Subgroup.center G) : θ = ζ := by
  have key := fixed_of_mem_commutator (ζ.symm.trans θ) ⊤ (fun w _ => by
    simpa using hc (ζ.symm w))
  have hT : ⁅(⊤ : Subgroup G), ⊤⁆ = ⊤ := hG
  ext s
  have := key (ζ s) (by rw [hT]; exact Subgroup.mem_top _)
  simpa using this

section Irred

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def suIota (n : ℕ) :
    unitarySU p f K n ≃* gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)

theorem suIota_val (n : ℕ) (s : unitarySU p f K n) : ((suIota h n s : GL (Fin n) K)) = s := rfl

theorem psi_unitaryProj (n : ℕ) (s : unitarySU p f K n) :
    CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h n (unitaryProj h n s) =
      ((suIota h n s : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rfl

end Irred

theorem exists_irred_alternative
    {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (hperf : commutator ↥L = ⊤) (hZ1 : Subgroup.center ↥L ≠ ⊥)
    (eU : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU h 3) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X))
    (B : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hβ : ∀ z, CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3 (eU (centerQuotientConj L huN z)) =
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) B
        (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3 (eU z)))
    (ω : K) (H : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hωn : h.bar ω * ω = 1)
    (hH3 : (H : GL (Fin 3) K) ^ 3 = 1)
    (hBH : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((H : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω⁻¹ • (((H : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) :
    ∃ y ∈ L, y ^ 3 = 1 ∧ ∃ c ∈ L, u * y * u⁻¹ = c * y ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * u = u * c ∧
      ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_over h hq hperf eU hZ1
  set ψ := CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3 with hψ
  let G := unitarySU p f K 3
  let ζ : G ≃* G :=
    ((suIota h 3).trans (primeFormConjSU h _ B)).trans (suIota h 3).symm
  have hζ : ∀ s : G, ((ζ s : G) : GL (Fin 3) K) = (B : GL (Fin 3) K) * s * (B : GL (Fin 3) K)⁻¹ :=
    fun s => rfl
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨u, huN⟩
  have hα : ∀ l : ↥L, ((α l : ↥L) : X) = u * l * u⁻¹ := fun l => rfl
  let ζL : ↥L ≃* ↥L := φ.symm.trans (ζ.trans φ)
  have hζL : ∀ s : G, ζL (φ s) = φ (ζ s) := fun s => by simp [ζL]
  have hcen : ∀ l : ↥L, l ∈ Subgroup.center ↥L ↔ eU (QuotientGroup.mk l) = 1 := fun l => by
    rw [map_eq_one_iff eU eU.injective, QuotientGroup.eq_one_iff]
  have hagree : ∀ s : G, eU (QuotientGroup.mk (α (φ s))) = eU (QuotientGroup.mk (φ (ζ s))) := by
    intro s
    apply ψ.injective
    have h1 := hβ (QuotientGroup.mk (φ s))
    rw [centerQuotientConj_mk, hφ s, psi_unitaryProj, primeFormConjHom_mk] at h1
    rw [h1, hφ (ζ s), psi_unitaryProj]
    rfl
  have hperfL : ∀ l : ↥L, α l = ζL l := by
    have := perfect_aut_eq_of_central hperf α ζL ?_
    · intro l; exact DFunLike.congr_fun this l
    · intro l
      obtain ⟨s, rfl⟩ := φ.surjective l
      rw [hcen, hζL, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hagree,
        mul_inv_cancel]
  have hconj : ∀ s : G, u * (φ s : X) * u⁻¹ = (φ (ζ s) : X) := fun s => by
    have := congrArg Subtype.val (hperfL (φ s))
    rwa [hα, hζL] at this
  have hω0 : ω ≠ 0 := fun h0 => by simp [h0] at hω3
  let cu : Kˣ := Units.mk0 ω⁻¹ (inv_ne_zero hω0)
  have hcu : (cu : K) = ω⁻¹ := rfl
  have hnorm : h.norm (cu : K) = 1 := by
    rw [hcu, UnitaryFieldData.norm, map_inv₀, ← mul_inv, mul_comm, hωn, inv_one]
  have hcu3 : cu ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcu, inv_pow, hω3, inv_one, Units.val_one]
  let c0 : G := ⟨GeneralLinearGroup.scalar (Fin 3) cu, scalar_mem_unitarySU h (by norm_num) hnorm hcu3⟩
  have hc0mem : c0 ∈ unitaryScalars h 3 := ⟨cu, hnorm, hcu3, rfl⟩
  have hc0pow : c0 ^ 3 = 1 := by
    apply Subtype.ext
    change (GeneralLinearGroup.scalar (Fin 3) cu) ^ 3 = 1
    rw [← map_pow, hcu3, map_one]
  have hc0ne : c0 ≠ 1 := by
    intro h1
    have h2 := congrArg (fun g : G => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [c0, GeneralLinearGroup.coe_scalar] at h2
    have h3 : (cu : K) = 1 := by rw [h2]; rfl
    exact hω1 (by simpa [hcu] using h3)
  have hzp : Subgroup.zpowers c0 = unitaryScalars h 3 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hc0mem
    · rw [Nat.card_zpowers, orderOf_eq_prime hc0pow hc0ne, card_unitaryScalars h (by norm_num)]
      exact Nat.gcd_le_left _ (by norm_num)
  have hcenter : ∀ l : ↥L, l ∈ Subgroup.center ↥L ↔ l ∈ Subgroup.zpowers (φ c0) := fun l => by
    obtain ⟨s, rfl⟩ := φ.surjective l
    rw [hcen, hφ, ← MonoidHom.mem_ker, ker_unitaryProj, ← hzp, Subgroup.mem_zpowers_iff,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩
    · rintro ⟨k, hk⟩; exact ⟨k, φ.injective (by simpa using hk)⟩
  have hζc0 : ζ c0 = c0 := by
    apply Subtype.ext
    rw [hζ]
    change (B : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) cu * (B : GL (Fin 3) K)⁻¹ = _
    rw [commute_scalar cu (B : GL (Fin 3) K), mul_inv_cancel_right]
  let H' : G := (suIota h 3).symm H
  have hH'val : ((H' : G) : GL (Fin 3) K) = (H : GL (Fin 3) K) := rfl
  have hBH' : (B : GL (Fin 3) K) * (H : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) cu * ((H : GL (Fin 3) K) * (B : GL (Fin 3) K)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, hBH]
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, hcu]
  have hζH' : ζ H' = c0 * H' := by
    apply Subtype.ext
    rw [hζ, Subgroup.coe_mul, hH'val]
    change _ = GeneralLinearGroup.scalar (Fin 3) cu * (H : GL (Fin 3) K)
    rw [hBH', mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  have hH'3 : H' ^ 3 = 1 := by
    apply Subtype.ext
    change ((H' : G) : GL (Fin 3) K) ^ 3 = 1
    rw [hH'val]; exact hH3
  have hconjc : u * (φ c0 : X) * u⁻¹ = (φ c0 : X) := by
    have := hconj c0
    rwa [hζc0] at this
  refine ⟨φ H', (φ H').2, ?_, φ c0, (φ c0).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hH'3, map_one]; rfl
  · rw [hconj, hζH', map_mul]; rfl
  · intro h1
    have h2 : φ c0 = 1 := Subtype.ext h1
    exact hc0ne (by simpa using h2)
  · rw [← Subgroup.coe_pow, ← map_pow, hc0pow, map_one]; rfl
  · calc (φ c0 : X) * u = (u * (φ c0 : X) * u⁻¹) * u := by rw [hconjc]
      _ = u * (φ c0 : X) := by group
  · intro x hx
    have h1 : (∀ l ∈ L, x * l = l * x) ↔ (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      constructor
      · intro hl l; exact Subtype.ext (hl l l.2).symm
      · intro hl l hlL; exact (congrArg Subtype.val (hl ⟨l, hlL⟩)).symm
    rw [h1, hcenter, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext (by simpa using hk)⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
