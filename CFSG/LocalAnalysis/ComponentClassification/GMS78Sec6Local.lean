module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Model
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot
public import CFSG.LocalAnalysis.ComponentClassification.GMS78UnitaryLocal

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.ComponentClassification.RankTwoStandard CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mul_central_of_odd {H : Type*} [Group H] [Finite H] {P Z : Subgroup H}
    (hP : IsPGroup 2 P) (hZ : Odd (Nat.card Z)) (hZc : Z ≤ center H) {a p z : H}
    (ha : ∃ n : ℕ, a ^ 2 ^ n = 1) (hp : p ∈ P) (hz : z ∈ Z) (h : a = p * z) : a = p := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
  have hm' : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hzc : Commute p z := mem_center_iff.mp (hZc hz) p
  have hz2 : z ^ 2 ^ (n + m) = 1 := by
    have h1 : a ^ 2 ^ (n + m) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
    have h2 : p ^ 2 ^ (n + m) = 1 := by rw [pow_add, mul_comm, pow_mul, hm', one_pow]
    rw [h, hzc.mul_pow, h2, one_mul] at h1
    exact h1
  have hzo : Odd (orderOf z) := by
    have h := Subgroup.orderOf_dvd_natCard Z hz
    exact hZ.of_dvd_nat h
  have h1 : orderOf z ∣ 2 ^ (n + m) := orderOf_dvd_of_pow_eq_one hz2
  have h2 : orderOf z = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp h1 with ⟨k, -, hk⟩
    rcases k with _ | k
    · simpa using hk
    · rw [hk, pow_succ] at hzo
      exact absurd hzo (by simp [Nat.not_odd_iff_even])
  rw [orderOf_eq_one_iff] at h2
  rw [h, h2, mul_one]

omit [Finite G] in
theorem inf_centralizer_map_subtype {L : Subgroup G} (K' : Subgroup L) :
    L ⊓ centralizer ((K'.map L.subtype : Subgroup G) : Set G) =
      (centralizer (K' : Set L)).map L.subtype := by
  ext x
  constructor
  · rintro ⟨hxL, hxc⟩
    refine ⟨⟨x, hxL⟩, mem_centralizer_iff.mpr fun k hk => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.mp hxc) (k : G) ⟨k, hk, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hy) k hk)

theorem exists_u3TorusK {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) (hP : IsSylowOf 2 P L) :
    ∃ K : Subgroup G, K ≤ L ∧ Odd (Nat.card K) ∧
      P ⊔ K = L ⊓ normalizer (P : Set G) ⊓
        centralizer ((P ⊓ centralizer (P : Set G) : Subgroup G) : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
        Nonempty (rankTwoQuot ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ ≃*
          Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  obtain ⟨Kf, _, _, _, J, hJ, hcard, hfixed, φ, S, hS, hRS⟩ := exists_mulEquiv_root hf e R
  set ρ : L →* ProjectiveSpecialUnitaryMatrixGroup J :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hρdef
  have hρ : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set P' : Subgroup L := P.subgroupOf L
  set A₁ : Subgroup G := P ⊓ centralizer (P : Set G)
  have hP' : IsPGroup 2 P' := hP.isPGroup.comap_subtype
  have hroot : P'.map ρ = unitaryCoverRoot J hJ := by
    rw [← hS, ← hRS, hρdef, ← map_map, ← hR]
    congr 1
    ext y
    rw [MonoidHom.mem_range, mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hP.le x.2⟩, x.2, rfl⟩
  have hPZ : P' ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L) hP'.to_inf_left hZ
      inf_le_right
  have hinjP : ∀ p ∈ P', ρ p = 1 → p = 1 := fun p hp h1 => by
    have : p ∈ P' ⊓ center L := mem_inf.mpr ⟨hp, hker ▸ MonoidHom.mem_ker.mpr h1⟩
    rwa [hPZ, mem_bot] at this
  have hrootP : ∀ x ∈ unitaryCoverRoot J hJ, ∃ p ∈ P', ρ p = x := fun x hx => by
    rw [← hroot] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩
  have hNA := u3_torusK_le_normalizer J hJ
  have hCA := u3_torusK_le_centralizer J hJ hf hcard hfixed
  set K' : Subgroup L := (u3TorusK J hJ).comap ρ
  set K : Subgroup G := K'.map L.subtype
  have hZK : center L ≤ K' := fun z hz => by
    rw [← hker] at hz
    show ρ z ∈ u3TorusK J hJ
    rw [MonoidHom.mem_ker.mp hz]
    exact one_mem _
  have hKP : ∀ k ∈ K', ∀ p ∈ P', k * p * k⁻¹ ∈ P' := by
    intro k hk p hp
    have h1 : ρ (k * p * k⁻¹) ∈ unitaryCoverRoot J hJ := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hNA hk) _).mp (by rw [← hroot]; exact ⟨p, hp, rfl⟩)
    obtain ⟨p₂, hp₂, hp₂e⟩ := hrootP _ h1
    have hz : p₂⁻¹ * (k * p * k⁻¹) ∈ center L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hp₂e, inv_mul_cancel]
    have hpow : ∃ n : ℕ, (k * p * k⁻¹) ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hP' ⟨p, hp⟩
      refine ⟨n, ?_⟩
      have hn' : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [conj_pow, hn', mul_one, mul_inv_cancel]
    have := eq_of_mul_central_of_odd hP' hZ le_rfl hpow hp₂ hz (by group)
    rw [this]
    exact hp₂
  have hA₁ : ∀ a : L, (a : G) ∈ A₁ → ρ a ∈ sylowCenter (unitaryCoverRoot J hJ) := by
    intro a ha
    have haP : a ∈ P' := (mem_inf.mp ha).1
    refine mem_sylowCenter.mpr ⟨by rw [← hroot]; exact ⟨a, haP, rfl⟩, fun t ht => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hrootP t ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp (mem_inf.mp ha).2) (q : G) hq)
  have hA₁' : ∀ z ∈ sylowCenter (unitaryCoverRoot J hJ), ∃ a : L, (a : G) ∈ A₁ ∧ ρ a = z := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hrootP z (mem_sylowCenter.mp hz).1
    refine ⟨p, mem_inf.mpr ⟨hp, mem_centralizer_iff.mpr fun q hq => ?_⟩, rfl⟩
    have hq' : (⟨q, hP.le hq⟩ : L) ∈ P' := hq
    have hc := (mem_sylowCenter.mp hz).2 (ρ ⟨q, hP.le hq⟩) (by rw [← hroot]; exact ⟨_, hq', rfl⟩)
    have h1 : (⟨q, hP.le hq⟩ : L) * p * (⟨q, hP.le hq⟩ : L)⁻¹ * p⁻¹ = 1 := by
      apply hinjP
      · exact mul_mem (mul_mem (mul_mem hq' hp) (inv_mem hq')) (inv_mem hp)
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
    have h2 : (⟨q, hP.le hq⟩ : L) * p = p * (⟨q, hP.le hq⟩ : L) := by
      calc (⟨q, hP.le hq⟩ : L) * p =
            (⟨q, hP.le hq⟩ : L) * p * (⟨q, hP.le hq⟩ : L)⁻¹ * p⁻¹ * (p * (⟨q, hP.le hq⟩ : L)) := by
            group
        _ = p * (⟨q, hP.le hq⟩ : L) := by rw [h1, one_mul]
    exact congrArg Subtype.val h2
  have hKA : ∀ k ∈ K', ∀ a : L, (a : G) ∈ A₁ → k * a = a * k := by
    intro k hk a ha
    have haP : a ∈ P' := (mem_inf.mp ha).1
    have h1 : k * a * k⁻¹ * a⁻¹ = 1 := by
      apply hinjP
      · exact mul_mem (hKP k hk a haP) (inv_mem haP)
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have := (mem_centralizer_iff.mp (hCA hk)) (ρ a) (hA₁ a ha)
        rw [← this]
        group
    calc k * a = k * a * k⁻¹ * a⁻¹ * (a * k) := by group
      _ = a * k := by rw [h1, one_mul]
  have h4 : ∃ s : Finset (unitaryCoverFixedField J), s.card = 4 := by
    have : Fintype (unitaryCoverFixedField J) := Fintype.ofFinite _
    have hc : 4 ≤ (Finset.univ : Finset (unitaryCoverFixedField J)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_unitaryCoverFixedField hfixed]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have : CharP (unitaryCoverFixedField J) 2 := by
    have : Fintype (unitaryCoverFixedField J) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow
      (by rw [← Nat.card_eq_fintype_card, card_unitaryCoverFixedField hfixed])
  refine ⟨K, map_subtype_le K', ?_, ?_, unitaryCoverFixedField J, inferInstance, inferInstance,
    inferInstance, card_unitaryCoverFixedField hfixed, ?_⟩
  ·
    rw [show Nat.card K = Nat.card K' from Subgroup.card_map_of_injective L.subtype_injective,
      card_comap_of_surjective' ρ hρ, hker]
    exact (u3_odd_card_torusK J hJ hf hcard hfixed).mul hZ
  · apply le_antisymm
    · refine sup_le (le_inf (le_inf hP.le le_normalizer) ?_) ?_
      · intro x hx
        exact mem_centralizer_iff.mpr fun a ha =>
          ((mem_centralizer_iff.mp (mem_inf.mp ha).2) x hx).symm
      · rintro _ ⟨k, hk, rfl⟩
        refine mem_inf.mpr ⟨mem_inf.mpr ⟨k.2, ?_⟩, mem_centralizer_iff.mpr fun a ha => ?_⟩
        · refine mem_normalizer_iff.mpr fun p => ⟨fun hp => ?_, fun hp => ?_⟩
          · exact hKP k hk ⟨p, hP.le hp⟩ hp
          · have hpL : p ∈ L := by
              have h := L.mul_mem (L.mul_mem (L.inv_mem k.2) (hP.le hp)) k.2
              simpa [mul_assoc] using h
            have h := hKP k⁻¹ (inv_mem hk) ⟨(k : G) * p * (k : G)⁻¹, hP.le hp⟩ hp
            have e : (k⁻¹ * ⟨(k : G) * p * (k : G)⁻¹, hP.le hp⟩ * k⁻¹⁻¹ : L) = ⟨p, hpL⟩ :=
              Subtype.ext (by simp [mul_assoc])
            rw [e] at h
            exact h
        · have haL : a ∈ L := hP.le (mem_inf.mp ha).1
          exact (congrArg Subtype.val (hKA k hk ⟨a, haL⟩ ha)).symm
    · rintro x ⟨⟨hxL, hxN⟩, hxC⟩
      set x' : L := ⟨x, hxL⟩
      have hxN' : ρ x' ∈ normalizer ((unitaryCoverRoot J hJ : Subgroup _) : Set _) := by
        rw [← hroot]
        refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
        · obtain ⟨p, hp, rfl⟩ := hy
          refine ⟨x' * p * x'⁻¹, ?_, by simp⟩
          exact (mem_normalizer_iff.mp hxN (p : G)).mp hp
        · obtain ⟨p, hp, hpe⟩ := hy
          refine ⟨x'⁻¹ * p * x', ?_, ?_⟩
          · have h := (mem_normalizer_iff.mp (inv_mem hxN) (p : G)).mp hp
            rw [inv_inv] at h
            show ((x'⁻¹ * p * x' : L) : G) ∈ P
            exact h
          · rw [map_mul, map_mul, map_inv, hpe]
            group
      have hxC' : ρ x' ∈ centralizer ((sylowCenter (unitaryCoverRoot J hJ) : Subgroup _) :
          Set _) := by
        rw [mem_centralizer_iff]
        intro z hz
        obtain ⟨a, ha, rfl⟩ := hA₁' z hz
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext ((mem_centralizer_iff.mp hxC) (a : G) ha)
      obtain ⟨r, hr, t, ht, hrt⟩ :=
        u3_exists_eq_mul_of_mem_normalizer J hJ hf hcard hfixed hxN' hxC'
      obtain ⟨p, hp, rfl⟩ := hrootP r hr
      obtain ⟨k, rfl⟩ := hρ t
      have hz : (p * k)⁻¹ * x' ∈ center L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hrt]
        group
      have hkz : k * ((p * k)⁻¹ * x') ∈ K' := mul_mem ht (hZK hz)
      have hx' : x' = p * (k * ((p * k)⁻¹ * x')) := by group
      have hx : x = (p : G) * ((k * ((p * k)⁻¹ * x') : L) : G) := congrArg Subtype.val hx'
      rw [hx]
      exact mul_mem_sup hp ⟨_, hkz, rfl⟩
  ·
    set eJ := u3SubLineEquiv J hJ
    have hJperf : ⁅u3SubLine J hJ, u3SubLine J hJ⁆ = u3SubLine J hJ := by
      have hp := CFSG.LinearGroups.special_linear_isPerfect
        (K := unitaryCoverFixedField J) (n := 2) le_rfl (Or.inr h4)
      have : Group.IsPerfect (u3SubLine J hJ) :=
        Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom) eJ.symm.surjective
      exact (Subgroup.isPerfect_iff).mp this
    have hJZ : center (u3SubLine J hJ) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : eJ z ∈ center (Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨w, rfl⟩ := eJ.surjective y
        rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w]
      rw [u3_center_SL2_eq_bot, mem_bot] at h1
      rw [mem_bot]
      exact eJ.injective (h1.trans (map_one eJ).symm)
    obtain ⟨eX⟩ := nonempty_quotCenter_commutator_equiv ρ hρ hker.le
      (u3_centralizer_torusK J hJ hf hcard hfixed)
      (fun x hx y hy => u3_commute_subLine_torusK J hJ hx hy) hJperf hJZ
    have hX : ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ =
        (⁅centralizer (K' : Set L), centralizer (K' : Set L)⁆).map L.subtype := by
      rw [inf_centralizer_map_subtype, map_commutator]
    have eS := (⁅centralizer (K' : Set L), centralizer (K' : Set L)⁆).equivMapOfInjective
      L.subtype L.subtype_injective
    exact ⟨(quotCenterCongr ((MulEquiv.subgroupCongr hX).trans eS.symm)).trans
      (eX.trans eJ)⟩

end CFSG.ComponentClassification.GMS78
