module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenD
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.HeldB.AutModel

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem nonempty_coreQuot_held
    {N : Type} [Group N] [Finite N] (hN : commutator N = ⊤)
    (ψ : N ⧸ Open.fusionZStar N ≃* Blueprint.NativeSporadic.He) :
    Nonempty (N ⧸ pPrimeCore 2 N ≃* Blueprint.NativeSporadic.He) := by
  have hHe : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  set eZ : (N ⧸ pPrimeCore 2 N) ⧸ center (N ⧸ pPrimeCore 2 N) ≃* Blueprint.NativeSporadic.He :=
    (Sol78.coreQuotientCenterEquiv N).trans ψ with heZdef
  have hperf : Group.IsPerfect (N ⧸ pPrimeCore 2 N) := by
    rw [Group.isPerfect_def]
    have h1 := map_commutator (⊤ : Subgroup N) ⊤ (QuotientGroup.mk' (pPrimeCore 2 N))
    rw [← _root_.commutator_def, hN,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective (pPrimeCore 2 N)),
      ← _root_.commutator_def] at h1
    exact h1.symm
  have hq : CFSG.IsQuasisimple (N ⧸ pPrimeCore 2 N) := by
    refine ⟨hperf, @MulEquiv.isSimpleGroup _ _ _ _ hHe eZ, ?_⟩
    obtain ⟨a, b, hab⟩ := GrSLit.exists_mul_ne_held
    exact ⟨eZ.symm a, eZ.symm b, fun h => hab (eZ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ : center (N ⧸ pPrimeCore 2 N) = ⊥ :=
    Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate _ hq ⟨eZ⟩
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    eZ⟩

theorem card_inf_centralizer_conj {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H)
    (y : M) :
    Nat.card ↥(H ⊓ centralizer ({g * y * g⁻¹} : Set M)) =
      Nat.card ↥(H ⊓ centralizer ({y} : Set M)) := by
  have h1 : (H ⊓ centralizer ({y} : Set M)).map (MulAut.conj g).toMonoidHom =
      H ⊓ centralizer ({g * y * g⁻¹} : Set M) := by
    ext z
    rw [mem_map, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwH, hwy⟩ := mem_inf.mp hw
      rw [mem_centralizer_singleton_iff] at hwy
      refine ⟨mul_mem (mul_mem hg hwH) (inv_mem hg), ?_⟩
      change g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹)
      calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
        _ = g * (y * w) * g⁻¹ := by rw [hwy]
        _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group
    · rintro ⟨hzH, hzy⟩
      refine ⟨g⁻¹ * z * g, mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) hzH) hg, ?_⟩, ?_⟩
      · rw [mem_centralizer_singleton_iff]
        calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [hzy]
          _ = y * (g⁻¹ * z * g) := by group
      · change g * (g⁻¹ * z * g) * g⁻¹ = z
        group
  rw [← h1, card_map_of_injective (MulAut.conj g).injective]

theorem two_pow_nine_dvd_card_fixed_of_inner
    {G : Type} [Group G] [Finite G] (Θ : G ≃* heP) (s : MulAut G) (hs2 : s * s = 1)
    (x : heAutGroup) (hx : heConjR x = MulAut.congr Θ s)
    (hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP) :
    2 ^ 9 ∣ Nat.card (Open.signalizerFixedSubgroup s) := by
  have hbij := ctbh_full_automorphism_permutation_model.1
  have h1 : Nat.card (Open.signalizerFixedSubgroup s) =
      Nat.card ↥(heP ⊓ centralizer {(x : Equiv.Perm (Fin 8330))}) := by
    rw [← card_map_of_injective (f := Θ.toMonoidHom) Θ.injective,
      HeGen.map_signalizerFixedSubgroup_congr Θ s, ← hx,
      HeGen.signalizerFixedSubgroup_eq_fixedSubgroup, ← map_fixedSubgroup_heConjR x,
      card_map_of_injective heP.subtype_injective]
  rw [h1]
  have hxx : x * x = 1 := by
    apply hbij.1
    rw [map_mul, hx, map_one, ← map_mul, hs2, map_one]
  by_cases hx1 : (x : Equiv.Perm (Fin 8330)) = 1
  · rw [hx1]
    have h2 : heP ⊓ centralizer ({(1 : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) =
        heP := by
      apply inf_of_le_left
      intro z _
      rw [mem_centralizer_singleton_iff, mul_one, one_mul]
    rw [h2, card_heP]
    norm_num
  · have hx2 : orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
      refine orderOf_eq_prime ?_ hx1
      rw [sq, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]
    rcases involution_conj_cases hxP hx2 with ⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩
    · rw [hxc, card_inf_centralizer_conj hc]
      have h3 := card_heP_cent0
      rw [centralizerIn] at h3
      rw [h3]
      norm_num
    · rw [hxc, card_inf_centralizer_conj hc]
      have h3 := card_heP_cent1
      rw [centralizerIn] at h3
      rw [h3]
      norm_num

end CFSG.ComponentClassification.SolMax
