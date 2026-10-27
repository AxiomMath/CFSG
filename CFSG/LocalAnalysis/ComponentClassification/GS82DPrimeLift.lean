module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP4Lift

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup CFSG.ComponentClassification.GS82PumpInputs.P4
open scoped MatrixGroups commutatorElement

theorem exists_sl2_section_lift
    {E A : Type} [Group E] [Group A] [Finite E] [Finite A]
    (ρ : E →* A) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E)
    {q₀ : ℕ} (hq₀ : Odd q₀) (h5 : 5 ≤ q₀) (hA : HarrisLit.IsSLTwoOver q₀ (A ⧸ pPrimeCore 2 A))
    {c : A} (hc : c ∈ center A) (hcc : c * c = 1) :
    ∃ P : Subgroup E, Group.IsPerfect ↥P ∧ HarrisLit.IsSLTwoOver q₀ (↥P ⧸ pPrimeCore 2 ↥P) ∧
      ∃ t ∈ P, t * t = 1 ∧ ρ t = c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hFq, ⟨eA⟩⟩ := hA
  set OA := pPrimeCore 2 A with hOA
  have hOAodd : Odd (Nat.card OA) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let θA : A →* SL(2, F) := eA.toMonoidHom.comp (QuotientGroup.mk' OA)
  have hθA : Function.Surjective θA := eA.surjective.comp (QuotientGroup.mk'_surjective OA)
  have hθAker : ∀ a : A, θA a = 1 ↔ a ∈ OA := by
    intro a
    change eA (QuotientGroup.mk a) = 1 ↔ _
    rw [map_eq_one_iff eA eA.injective, QuotientGroup.eq_one_iff]
  have hFodd : Odd (Nat.card F) := by rw [Nat.card_eq_fintype_card, hFq]; exact hq₀
  have hF5 : 5 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hFq]; exact h5
  have hOSL : pPrimeCore 2 SL(2, F) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eA, CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.map_bot]
  set θ : E →* SL(2, F) := θA.comp ρ with hθdef
  have hθ : Function.Surjective θ := hθA.comp hρ
  have hSL : Group.IsPerfect SL(2, F) := LinearGroups.special_linear_dimension_two_perfect
    (LieType.Steinberg.CentralExt.SL2Closed.exists_four_of_five_le hF5)
  have htop : Group.IsPerfect ↥(⊤ : Subgroup SL(2, F)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := SL(2, F))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := SL(2, F))).symm.surjective
  obtain ⟨P, hP, hPm⟩ := exists_perfect_map_eq θ hθ htop
  set θP : ↥P →* SL(2, F) := θ.comp P.subtype with hθPdef
  have hθP : Function.Surjective θP := by
    intro s
    have hs : s ∈ P.map θ := by rw [hPm]; exact mem_top s
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨⟨x, hx⟩, rfl⟩
  have h2c : ∀ x : ↥P, θP x = 1 → ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ center ↥P := by
    intro x hx k hxk
    have h1 : ρ (x : E) ∈ OA := (hθAker _).mp hx
    have h2 : ρ (x : E) ^ 2 ^ k = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hxk, Subgroup.coe_one, map_one]
    have h3 : ρ (x : E) = 1 := eq_one_of_pow_two_pow_eq_one hOAodd h1 k h2
    have h4 : (x : E) ∈ center E := hker (MonoidHom.mem_ker.mpr h3)
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp h4 g)
  have hcomm : ∀ k ∈ θP.ker, ∀ g : ↥P, ⁅k, g⁆ ∈ pPrimeCore 2 ↥P := by
    set D := θP.ker with hDdef
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
    have hT2 : ∀ x ∈ (T : Subgroup ↥D), ((x : ↥P)) ∈ center ↥P := by
      intro x hx
      obtain ⟨k, hk⟩ := T.isPGroup' ⟨x, hx⟩
      have hk' : (x : ↥P) ^ 2 ^ k = 1 := by
        have := congrArg (fun y : ↥(T : Subgroup ↥D) => ((y : ↥D) : ↥P)) hk
        simpa using this
      exact h2c _ x.2 k hk'
    have hTc : (T : Subgroup ↥D) ≤ center ↥D := fun x hx =>
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hT2 x hx) g)
    have hNC : normalizer ((T : Subgroup ↥D) : Set ↥D) ≤
        centralizer ((T : Subgroup ↥D) : Set ↥D) := by
      intro g _
      rw [mem_centralizer_iff]
      intro x hx
      exact (mem_center_iff.mp (hTc hx) g).symm
    have hcompl := MonoidHom.ker_transferSylow_isComplement' T hNC
    have hNO : (MonoidHom.transferSylow T hNC).ker ≤ pPrimeCore 2 ↥D :=
      le_sSup ⟨MonoidHom.normal_ker _, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (MonoidHom.not_dvd_card_ker_transferSylow T hNC)⟩
    have hDO : (pPrimeCore 2 ↥D).map D.subtype ≤ pPrimeCore 2 ↥P := by
      rw [ABGLocalTools.pPrimeCore_map_subtype_eq_inf (MonoidHom.normal_ker θP)]
      exact inf_le_right
    intro k hk g
    obtain ⟨⟨o, t⟩, hot⟩ := hcompl.2 ⟨k, hk⟩
    set o' : ↥P := ((o : ↥D) : ↥P) with ho'
    set t' : ↥P := ((t : ↥D) : ↥P) with ht'
    have hkot : k = o' * t' := by
      have := congrArg Subtype.val hot
      simpa using this.symm
    have ho : o' ∈ pPrimeCore 2 ↥P := hDO ⟨o, hNO o.2, rfl⟩
    have ht : t' * g = g * t' := (mem_center_iff.mp (hT2 t t.2) g).symm
    have hcomm_t : ⁅o' * t', g⁆ = o' * (g * o'⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      calc o' * t' * g * (o' * t')⁻¹ * g⁻¹ = o' * (t' * g) * t'⁻¹ * o'⁻¹ * g⁻¹ := by group
        _ = o' * (g * t') * t'⁻¹ * o'⁻¹ * g⁻¹ := by rw [ht]
        _ = o' * (g * o'⁻¹ * g⁻¹) := by group
    rw [hkot, hcomm_t]
    exact mul_mem ho ((pPrimeCore_normal (p := 2) (G := ↥P)).conj_mem _ (inv_mem ho) g)
  have hodd := odd_card_ker_of_sl2 hP hFodd hF5 hOSL θP hθP hcomm
  have hkerP : θP.ker = pPrimeCore 2 ↥P := by
    refine le_antisymm (le_sSup ⟨MonoidHom.normal_ker _, Nat.coprime_two_left.mpr hodd⟩) ?_
    have h1 : (pPrimeCore 2 ↥P).map θP ≤ pPrimeCore 2 SL(2, F) := map_pPrimeCore_le θP hθP
    rw [hOSL, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot] at h1
    exact h1
  have hPSL : HarrisLit.IsSLTwoOver q₀ (↥P ⧸ pPrimeCore 2 ↥P) :=
    ⟨F, inferInstance, inferInstance, hFq, ⟨(QuotientGroup.quotientMulEquivOfEq hkerP.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θP hθP)⟩⟩
  obtain ⟨s, hs⟩ := hθP (θA c)
  set m := Nat.card θP.ker with hm
  have hss : s * s ∈ θP.ker := by
    rw [MonoidHom.mem_ker, map_mul, hs, ← map_mul, hcc, map_one]
  have hsm : (s * s) ^ m = 1 := by
    have h1 : (⟨s * s, hss⟩ : θP.ker) ^ m = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  have hw : θA c * θA c = 1 := by rw [← map_mul, hcc, map_one]
  set t : E := ((s ^ m : ↥P) : E) with ht
  have htt : t * t = 1 := by
    rw [ht, ← Subgroup.coe_mul, ← pow_add, ← two_mul, pow_mul, sq, hsm]
    rfl
  refine ⟨P, hP, hPSL, t, (s ^ m).2, htt, ?_⟩
  have hθt : θA (ρ t) = θA c := by
    change θP (s ^ m) = θA c
    rw [map_pow, hs]
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, sq, hw, one_pow, one_mul]
  have h1 : ρ t * c⁻¹ ∈ OA := by
    rw [← hθAker, map_mul, map_inv, hθt, mul_inv_cancel]
  have h2 : (ρ t * c⁻¹) ^ 2 ^ 1 = 1 := by
    have hρt : ρ t * ρ t = 1 := by rw [← map_mul, htt, map_one]
    rw [pow_one, (Commute.inv_right (mem_center_iff.mp hc (ρ t))).mul_pow, sq, sq, hρt,
      ← mul_inv_rev, hcc, inv_one, one_mul]
  exact mul_inv_eq_one.mp (eq_one_of_pow_two_pow_eq_one hOAodd h1 1 h2)

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
