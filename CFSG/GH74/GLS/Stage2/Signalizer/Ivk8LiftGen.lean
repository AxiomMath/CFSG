module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped Pointwise

theorem centralizer_map_two {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : Odd (Nat.card N)) {W' : Subgroup M} (hW : IsPGroup 2 ↥W') (hWN : W' ⊓ N = ⊥) :
    centralizer ((W'.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) =
      (centralizer (W' : Set M)).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hcomm : ∀ w ∈ W', h * w * h⁻¹ * w⁻¹ ∈ N := by
      intro w hw
      have h1 : QuotientGroup.mk' N w * QuotientGroup.mk' N h =
          QuotientGroup.mk' N h * QuotientGroup.mk' N w :=
        Subgroup.mem_centralizer_iff.mp hx (QuotientGroup.mk' N w) ⟨w, hw, rfl⟩
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    have hWN' : W'.subgroupOf N = ⊥ := Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hWN)
    have hindex : ¬ 2 ∣ W'.relIndex (N ⊔ W') := by
      rw [relIndex_sup_eq_relIndex_of_normal N W', Subgroup.relIndex, hWN', Subgroup.index_bot]
      exact fun hd => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hd)
    have hSyl : IsSylowOf 2 W' (N ⊔ W') := isSylowOf_iff.mpr ⟨le_sup_right, hW, hindex⟩
    set W'' : Subgroup M := W'.map (MulAut.conj h).toMonoidHom with hW''
    have hmem'' : ∀ y, y ∈ W'' ↔ ∃ w ∈ W', y = h * w * h⁻¹ := by
      intro y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    have hW''P : W'' ≤ N ⊔ W' := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := (hmem'' y).mp hy
      have : h * w * h⁻¹ = (h * w * h⁻¹ * w⁻¹) * w := by group
      rw [this]
      exact Subgroup.mul_mem_sup (hcomm w hw) hw
    have hcard'' : Nat.card W'' = 2 ^ (Nat.card ↥(N ⊔ W')).factorization 2 := by
      rw [hW'', Subgroup.card_map_of_injective (MulAut.conj h).injective]
      exact hSyl.card_eq
    have hSyl'' : IsSylowOf 2 W'' (N ⊔ W') := isSylowOf_of_card hW''P hcard''
    obtain ⟨k, hkP, hk⟩ := hSyl.exists_mem_conj hSyl''
    obtain ⟨n, hn, w₀, hw₀, hkdef⟩ := Subgroup.mem_sup_of_normal_left.mp hkP
    subst hkdef
    refine ⟨n⁻¹ * h, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw
      have hin : n⁻¹ * (h * w * h⁻¹) * n ∈ W' := by
        have h1 := (hk (h * w * h⁻¹)).mp ((hmem'' _).mpr ⟨w, hw, rfl⟩)
        have h2 : (n * w₀)⁻¹ * (h * w * h⁻¹) * (n * w₀) =
            w₀⁻¹ * (n⁻¹ * (h * w * h⁻¹) * n) * w₀ := by group
        rw [h2] at h1
        have h3 := W'.mul_mem (W'.mul_mem hw₀ h1) (W'.inv_mem hw₀)
        simpa [mul_assoc] using h3
      have hinN : (n⁻¹ * (h * w * h⁻¹) * n) * w⁻¹ ∈ N := by
        have h4 : (n⁻¹ * (h * w * h⁻¹) * n) * w⁻¹ =
            n⁻¹ * (h * w * h⁻¹ * w⁻¹) * (w * n * w⁻¹) := by group
        rw [h4]
        exact N.mul_mem (N.mul_mem (N.inv_mem hn) (hcomm w hw))
          (Subgroup.Normal.conj_mem inferInstance n hn w)
      have h5 : (n⁻¹ * (h * w * h⁻¹) * n) * w⁻¹ ∈ W' ⊓ N :=
        ⟨W'.mul_mem hin (W'.inv_mem hw), hinN⟩
      rw [hWN, Subgroup.mem_bot] at h5
      have h6 : n⁻¹ * (h * w * h⁻¹) * n = w := mul_inv_eq_one.mp h5
      have h7 : (n⁻¹ * h) * w * (n⁻¹ * h)⁻¹ = w := by simpa [mul_assoc] using h6
      exact (mul_inv_eq_iff_eq_mul.mp h7).symm
    · simp [map_mul, (QuotientGroup.eq_one_iff n).mpr hn]
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hg w hw
    show QuotientGroup.mk' N w * QuotientGroup.mk' N g =
      QuotientGroup.mk' N g * QuotientGroup.mk' N w
    rw [← map_mul, ← map_mul, this]


theorem exists_lift_two_centralizer {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : Odd (Nat.card N)) (W : Subgroup (M ⧸ N)) (hW : IsPGroup 2 ↥W) :
    ∃ W' : Subgroup M, IsPGroup 2 ↥W' ∧ W'.map (QuotientGroup.mk' N) = W ∧ W' ⊓ N = ⊥ ∧
      centralizer (W : Set (M ⧸ N)) = (centralizer (W' : Set M)).map (QuotientGroup.mk' N) := by
  obtain ⟨W', hW', hmap, hbot⟩ := exists_two_lift N hN W hW
  refine ⟨W', hW', hmap, hbot, ?_⟩
  rw [← hmap]
  exact centralizer_map_two N hN hW' hbot


theorem exists_lift_two_centralizer_bar {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (W : Subgroup (HBar H)) (hW : IsPGroup 2 ↥W) :
    ∃ W' : Subgroup ↥H, IsPGroup 2 ↥W' ∧ W'.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = W ∧
      W' ⊓ pPrimeCore 2 ↥H = ⊥ ∧
      centralizer (W : Set (HBar H)) =
        (centralizer (W' : Set ↥H)).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :=
  exists_lift_two_centralizer (pPrimeCore 2 ↥H)
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H))) W hW

theorem exists_lift_pElement {X Y : Type} [Group X] [Finite X] [Group Y] (φ : X →* Y)
    (hφ : Function.Surjective φ) {p : ℕ} [Fact p.Prime] {y : Y} {j : ℕ} (hy : y ^ (p ^ j) = 1) :
    ∃ x : X, φ x = y ∧ ∃ k : ℕ, x ^ (p ^ k) = 1 := by
  have hW : IsPGroup p ↥(Subgroup.zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨j, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨P⟩ : Nonempty (Sylow p ↥((Subgroup.zpowers y).comap φ)) := inferInstance
  have hP := map_sylow_comap_eq φ hφ (Subgroup.zpowers y) hW P
  have hyP : y ∈ (P.map ((Subgroup.zpowers y).comap φ).subtype).map φ := by
    rw [hP]; exact Subgroup.mem_zpowers y
  obtain ⟨x, hx, hxy⟩ := hyP
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x', hx'⟩
  have h1 : x' ^ p ^ k = 1 := congrArg Subtype.val hk
  refine ⟨(x' : X), hxy, k, ?_⟩
  have h2 := congrArg Subtype.val h1
  simpa using h2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
