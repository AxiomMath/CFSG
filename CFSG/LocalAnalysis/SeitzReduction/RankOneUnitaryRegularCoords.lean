module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStart

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Coords

variable {G : Type*} [Group G] {E : Type*} [Field E]

structure U3RootCoords (T₁ : Subgroup G) (σ : E →+* E) (u v : G → E) : Prop where
  rel : ∀ y ∈ T₁, v y + σ (v y) + u y * σ (u y) = 0
  mul_u : ∀ y ∈ T₁, ∀ y' ∈ T₁, u (y * y') = u y + u y'
  mul_v : ∀ y ∈ T₁, ∀ y' ∈ T₁, v (y * y') = v y + v y' - u y * σ (u y')
  inj : ∀ y ∈ T₁, ∀ y' ∈ T₁, u y = u y' → v y = v y' → y = y'
  surj : ∀ a b : E, b + σ b + a * σ a = 0 → ∃ y ∈ T₁, u y = a ∧ v y = b
  u_surj : ∀ a : E, ∃ y ∈ T₁, u y = a

namespace U3RootCoords

variable {T₁ : Subgroup G} {σ : E →+* E} {u v : G → E} (hc : U3RootCoords T₁ σ u v)
include hc

theorem u_one : u 1 = 0 := by
  have h := hc.mul_u 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem u_inv {y : G} (hy : y ∈ T₁) : u y⁻¹ = -u y := by
  have h := hc.mul_u y⁻¹ (inv_mem hy) y hy
  rw [inv_mul_cancel, hc.u_one] at h
  linear_combination -h

theorem u_mul_inv {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) : u (y⁻¹ * y') = u y' - u y := by
  rw [hc.mul_u _ (inv_mem hy) _ hy', hc.u_inv hy]
  ring

theorem sq [CharP E 2] {y : G} (hy : y ∈ T₁) : u (y ^ 2) = 0 ∧ v (y ^ 2) = u y * σ (u y) := by
  rw [pow_two]
  refine ⟨?_, ?_⟩
  · rw [hc.mul_u y hy y hy]
    exact CharTwo.add_self_eq_zero _
  · rw [hc.mul_v y hy y hy, CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq]

theorem v_mul_of_u_eq_zero {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) (hu : u y = 0) :
    v (y * y') = v y + v y' := by
  rw [hc.mul_v y hy y' hy', hu, zero_mul, sub_zero]

theorem sigma_v_of_u_eq_zero [CharP E 2] {y : G} (hy : y ∈ T₁) (hu : u y = 0) :
    σ (v y) = v y := by
  have h := hc.rel y hy
  rw [hu, zero_mul, add_zero] at h
  have h2 : σ (v y) = -v y := by linear_combination h
  rw [h2, CharTwo.neg_eq]

theorem exists_addEquiv_conj [Finite E] {n : G} (hnT : n ∈ normalizer (T₁ : Set G))
    (hnA : ∀ y ∈ T₁, u y = 0 → u (n * y * n⁻¹) = 0)
    (hnA' : ∀ y ∈ T₁, u (n * y * n⁻¹) = 0 → u y = 0) :
    ∃ φ : E ≃+ E, ∀ y ∈ T₁, u (n * y * n⁻¹) = φ (u y) := by
  classical
  choose s hsT hsu using hc.u_surj
  have hconjT : ∀ y ∈ T₁, n * y * n⁻¹ ∈ T₁ := fun y hy => (mem_normalizer_iff.mp hnT y).mp hy
  set F : E → E := fun a => u (n * s a * n⁻¹) with hF
  have hFu : ∀ y ∈ T₁, u (n * y * n⁻¹) = F (u y) := by
    intro y hy
    have h1 : u ((s (u y))⁻¹ * y) = 0 := by rw [hc.u_mul_inv (hsT _) hy, hsu, sub_self]
    have h2 := hnA _ (mul_mem (inv_mem (hsT _)) hy) h1
    have e : n * ((s (u y))⁻¹ * y) * n⁻¹ = (n * s (u y) * n⁻¹)⁻¹ * (n * y * n⁻¹) := by group
    rw [e, hc.u_mul_inv (hconjT _ (hsT _)) (hconjT _ hy)] at h2
    simp only [hF]
    linear_combination h2
  have hFadd : ∀ a b, F (a + b) = F a + F b := by
    intro a b
    have e : n * (s a * s b) * n⁻¹ = (n * s a * n⁻¹) * (n * s b * n⁻¹) := by group
    have h1 := hFu (s a * s b) (mul_mem (hsT a) (hsT b))
    rw [hc.mul_u _ (hsT a) _ (hsT b), hsu, hsu, e,
      hc.mul_u _ (hconjT _ (hsT a)) _ (hconjT _ (hsT b))] at h1
    exact h1.symm
  have hinj : Function.Injective F := by
    intro a b hab
    have h1 : F (a + -b) = 0 := by
      rw [hFadd]
      have hneg : F (-b) = -F b := by
        have := hFadd b (-b)
        rw [add_neg_cancel] at this
        have h0 : F 0 = 0 := by
          have := hFadd 0 0
          rw [add_zero] at this
          linear_combination -this
        rw [h0] at this
        linear_combination -this
      rw [hneg, hab, add_neg_cancel]
    have h2 : u (s (a + -b)) = 0 := hnA' _ (hsT _) h1
    rw [hsu] at h2
    linear_combination h2
  have hbij : Function.Bijective F := Finite.injective_iff_bijective.mp hinj
  exact ⟨AddEquiv.ofBijective (AddMonoidHom.mk' F hFadd) hbij, fun y hy => hFu y hy⟩

end U3RootCoords

end Coords

section Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.GH74.Uniqueness.Bender

variable {G : Type*} [Group G] {E : Type} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] noncomputable def u3Coord {L : Subgroup G}
    (φ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) (y : G) : hermitianUnipotentCoord J := by
  classical
  exact if hy : ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ then
    (unitaryCoverRootEquiv J hJ).symm ⟨φ ⟨y, hy.1⟩, hy.2⟩ else 1

theorem hermitianUnipotentPSU_u3Coord {L : Subgroup G}
    (φ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) {y : G} (hyL : y ∈ L)
    (hy : φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ) :
    hermitianUnipotentPSU J hJ (u3Coord J hJ φ y) = φ ⟨y, hyL⟩ := by
  have hy' : ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ := ⟨hyL, hy⟩
  rw [u3Coord, dite_eq_left_of_eq_true (eq_true hy'), ← unitaryCoverRootEquiv_val,
    MulEquiv.apply_symm_apply]

theorem u3RootCoords_of_mulEquiv [Finite E] [CharP E 2] {L T₁ : Subgroup G}
    (φ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hT₁ : ∀ y : G, y ∈ T₁ ↔ ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ) :
    U3RootCoords T₁ (J.conj : E →+* E) (fun y => (u3Coord J hJ φ y).1.1)
      (fun y => (u3Coord J hJ φ y).1.2) := by
  have hkey : ∀ y ∈ T₁, ∃ hyL : y ∈ L,
      hermitianUnipotentPSU J hJ (u3Coord J hJ φ y) = φ ⟨y, hyL⟩ := fun y hy => by
    obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
    exact ⟨hyL, hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR⟩
  have hmul : ∀ y ∈ T₁, ∀ y' ∈ T₁,
      u3Coord J hJ φ (y * y') = u3Coord J hJ φ y * u3Coord J hJ φ y' := by
    intro y hy y' hy'
    obtain ⟨hyL, h1⟩ := hkey y hy
    obtain ⟨hy'L, h2⟩ := hkey y' hy'
    obtain ⟨hyy'L, h3⟩ := hkey (y * y') (mul_mem hy hy')
    apply CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
    rw [map_mul, h1, h2, h3, ← map_mul]
    rfl
  have hsurj : ∀ z : hermitianUnipotentCoord J, ∃ y ∈ T₁, u3Coord J hJ φ y = z := by
    intro z
    set w := hermitianUnipotentPSU J hJ z
    have hwR : w ∈ unitaryCoverRoot J hJ := ⟨z, rfl⟩
    have hyL : ((φ.symm w : L) : G) ∈ L := (φ.symm w).2
    have hφ : φ ⟨((φ.symm w : L) : G), hyL⟩ = w := by
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    have hyT : ((φ.symm w : L) : G) ∈ T₁ := (hT₁ _).mpr ⟨hyL, by rw [hφ]; exact hwR⟩
    refine ⟨_, hyT, CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ ?_⟩
    obtain ⟨hyL', h1⟩ := hkey _ hyT
    rw [h1, hφ]
  refine ⟨fun y _ => (u3Coord J hJ φ y).2, fun y hy y' hy' => ?_, fun y hy y' hy' => ?_,
    fun y hy y' hy' hu hv => ?_, fun a b hab => ?_, fun a => ?_⟩
  · rw [hmul y hy y' hy']
    rfl
  · rw [hmul y hy y' hy']
    rfl
  · obtain ⟨hyL, h1⟩ := hkey y hy
    obtain ⟨hy'L, h2⟩ := hkey y' hy'
    have he : u3Coord J hJ φ y = u3Coord J hJ φ y' := Subtype.ext (Prod.ext hu hv)
    have := congrArg Subtype.val (φ.injective (h1.symm.trans ((congrArg _ he).trans h2)))
    exact this
  · obtain ⟨y, hyT, hy⟩ := hsurj ⟨(a, b), hab⟩
    exact ⟨y, hyT, by rw [hy], by rw [hy]⟩
  · obtain ⟨r, hr⟩ := unitaryCoverRootFirstCoord_surjective J q hcard hfixed hJ
      (Multiplicative.ofAdd a)
    obtain ⟨y, hyT, hy⟩ := hsurj ((unitaryCoverRootEquiv J hJ).symm r)
    refine ⟨y, hyT, ?_⟩
    rw [hy]
    exact congrArg Multiplicative.toAdd hr

end Model

namespace U3Start

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_model_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (_ : Nat.card E = (2 ^ f) ^ 2)
      (_ : Nat.card {x : E // J.conj x = x} = 2 ^ f)
      (φ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J),
      (∀ y : G, y ∈ szT₁ L T ↔ ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ) ∧
      (∀ y : G, y ∈ szA₁ (szT₁ L T) ↔
        ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ rootCenter (unitaryCoverRoot J hJ)) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hφQ, -⟩ :=
    hB.exists_standard_iso_unitary Q hc.sq_eq_one hc.not_mem
  have hZ : rootCenter (unitaryCoverRoot J hJ) = (rootCenter (Q : Subgroup L)).map φ.toMonoidHom := by
    rw [← hφQ, rootCenter_map]
  refine ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, fun y => ⟨fun hy => ?_, ?_⟩, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · have hyL : y ∈ L := szT₁_le_right L T hy
    refine ⟨hyL, ?_⟩
    rw [← hφQ]
    exact ⟨⟨y, hyL⟩, (hmemQ _).mpr hy, rfl⟩
  · rintro ⟨hyL, hyR⟩
    rw [← hφQ] at hyR
    obtain ⟨y', hy'Q, hy'⟩ := hyR
    have : y' = ⟨y, hyL⟩ := φ.injective hy'
    rw [this] at hy'Q
    exact (hmemQ _).mp hy'Q
  · have hyL : y ∈ L := szT₁_le_right L T (szA₁_le _ hy)
    refine ⟨hyL, ?_⟩
    rw [hZ]
    exact ⟨⟨y, hyL⟩, (hmemZ _).mpr hy, rfl⟩
  · rintro ⟨hyL, hyR⟩
    rw [hZ] at hyR
    obtain ⟨y', hy'Q, hy'⟩ := hyR
    have : y' = ⟨y, hyL⟩ := φ.injective hy'
    rw [this] at hy'Q
    exact (hmemZ _).mp hy'Q

theorem exists_rootCoords_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
      Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
      Nat.card {x : E // σ x = x} = 2 ^ f ∧
      ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
        ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0) := by
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hT₁, hA₁⟩ := h.exists_model_of_card_sylow hS2
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  refine ⟨E, hE, hF, inferInstance, (J.conj : E →+* E), hcard,
    huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed, hfixed,
    fun y => (u3Coord J hJ φ y).1.1, fun y => (u3Coord J hJ φ y).1.2,
    u3RootCoords_of_mulEquiv J hJ φ (2 ^ f) hcard hfixed hT₁, fun y hy => ?_⟩
  obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
  have hkey := hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR
  rw [hA₁]
  constructor
  · rintro ⟨hyL', hyZ⟩
    obtain ⟨z, hz0, hz⟩ := (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mp hyZ
    have : z = u3Coord J hJ φ y := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hz, hkey])
    simp only
    rw [← this]
    exact hz0
  · intro hu
    refine ⟨hyL, (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mpr
      ⟨u3Coord J hJ φ y, hu, hkey⟩⟩

end U3Start

end CFSG.SeitzReduction.RankOne
