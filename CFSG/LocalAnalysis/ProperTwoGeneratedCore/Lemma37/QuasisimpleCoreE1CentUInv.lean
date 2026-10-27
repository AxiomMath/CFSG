module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3FusionBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem quasiMk_ne_of_involution {w : quasiNormalizer u} (hww : w * w = 1)
    (hw1 : (w : J) ≠ 1) (hwe : (w : J) ≠ centralElt J) :
    quasiMk u w ≠ 1 ∧ quasiMk u w ≠ quasiCentral u := by
  set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
  refine ⟨fun h1 => hw1 (congrArg Subtype.val
    (eq_one_of_mem_oddCore ((QuotientGroup.eq_one_iff w).mp h1) hww)), fun h1 => ?_⟩
  have hO : w⁻¹ * e₀ ∈ pPrimeCore 2 (quasiNormalizer u) :=
    QuotientGroup.eq.mp (h1.trans d.quasiMk_centralElt.symm)
  have hsq : w⁻¹ * e₀ * (w⁻¹ * e₀) = 1 := Subtype.ext (by
    have hww' : (w : J) * w = 1 := by simpa using congrArg Subtype.val hww
    have hw' : (w : J)⁻¹ = w := inv_eq_of_mul_eq_one_right hww'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, hw']
    rw [show (w : J) * centralElt J * (w * centralElt J) =
        w * (centralElt J * w) * centralElt J by group, ← (d.setting.commute_centralElt w).eq,
      show (w : J) * (w * centralElt J) * centralElt J = (w * w) * (centralElt J * centralElt J)
        by group, hww', d.setting.centralElt_mul_self, one_mul])
  have h2 := eq_one_of_mem_oddCore hO hsq
  exact hwe (by rw [show w = e₀ from (inv_mul_eq_one.mp h2)])

theorem exists_mul_eq_of_involution {g : QuasiQuotient u} (hgg : g * g = 1) (hg1 : g ≠ 1)
    (hge : g ≠ quasiCentral u) :
    ∃ l ∈ L, ∃ k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)), l * k = g ∧
      l * l = quasiCentral u ∧ k * k = quasiCentral u := by
  have hKn := d.oneComponent.centralizer_normal
  have hee := d.quasiCentral_mul_self
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  obtain ⟨l, hl, k, hk, hlk⟩ := Subgroup.mem_sup_of_normal_right.mp (d.star.2.2.2 _ hord)
  have hcl : l * k = k * l := Subgroup.mem_centralizer_iff.mp hk l hl
  have hsq : l * l * (k * k) = 1 := by
    rw [← hgg, ← hlk]
    calc l * l * (k * k) = l * (l * k) * k := by group
      _ = l * (k * l) * k := by rw [hcl]
      _ = l * k * (l * k) := by group
  have hllK : l * l ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hk hk)
  rcases d.eq_of_mem_of_mem_centralizer (L.mul_mem hl hl) hllK with hll | hll
  · exfalso
    rw [hll, one_mul] at hsq
    rcases d.eq_of_mem_of_mul_self hl hll with rfl | rfl <;>
      rcases d.eq_of_mem_centralizer_of_mul_self hk hsq with rfl | rfl
    · exact hg1 (by rw [← hlk, mul_one])
    · exact hge (by rw [← hlk, one_mul])
    · exact hge (by rw [← hlk, mul_one])
    · exact hg1 (by rw [← hlk, hee])
  · refine ⟨l, hl, k, hk, hlk, hll, ?_⟩
    rw [hll] at hsq
    calc k * k = quasiCentral u * quasiCentral u * (k * k) := by rw [hee, one_mul]
      _ = quasiCentral u * (quasiCentral u * (k * k)) := by group
      _ = quasiCentral u := by rw [hsq, mul_one]

theorem exists_eq_quasiBar_mul {w : quasiNormalizer u} (hww : w * w = 1)
    (hw1 : (w : J) ≠ 1) (hwe : (w : J) ≠ centralElt J)
    (huw : (u * w) * (u * w) = centralElt J) :
    ∃ l ∈ L, l * l = quasiCentral u ∧ quasiMk u w = quasiBar u * l := by
  have he := d.quasiMk_centralElt
  have hee := d.quasiCentral_mul_self
  have hw2 : quasiMk u w * quasiMk u w = 1 := by rw [← map_mul, hww, map_one]
  obtain ⟨hwne1, hwnee⟩ := d.quasiMk_ne_of_involution hww hw1 hwe
  obtain ⟨l, hl, k, hk, hlk, hll, -⟩ := d.exists_mul_eq_of_involution hw2 hwne1 hwnee
  have hlu : l * quasiBar u = quasiBar u * l :=
    Subgroup.mem_centralizer_iff.mp d.quasiBar_mem_centralizer l hl
  have huw' : quasiBar u * quasiMk u w * (quasiBar u * quasiMk u w) = quasiCentral u := by
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg (quasiMk u) (Subtype.ext huw)
  have huk : quasiBar u * k * (quasiBar u * k) = 1 := by
    rw [← hlk] at huw'
    have h1 : quasiBar u * (l * k) * (quasiBar u * (l * k)) =
        l * l * (quasiBar u * k * (quasiBar u * k)) := by
      calc quasiBar u * (l * k) * (quasiBar u * (l * k)) =
          (quasiBar u * l) * k * ((quasiBar u * l) * k) := by group
        _ = (l * quasiBar u) * k * ((l * quasiBar u) * k) := by rw [hlu]
        _ = l * (quasiBar u * k * l) * (quasiBar u * k) := by group
        _ = l * (l * (quasiBar u * k)) * (quasiBar u * k) := by
          rw [show quasiBar u * k * l = l * (quasiBar u * k) from
            (Subgroup.mem_centralizer_iff.mp (Subgroup.mul_mem _ d.quasiBar_mem_centralizer hk)
              l hl).symm]
        _ = l * l * (quasiBar u * k * (quasiBar u * k)) := by group
    rw [h1, hll] at huw'
    calc quasiBar u * k * (quasiBar u * k) =
        quasiCentral u * quasiCentral u * (quasiBar u * k * (quasiBar u * k)) := by
          rw [hee, one_mul]
      _ = quasiCentral u * (quasiCentral u * (quasiBar u * k * (quasiBar u * k))) := by group
      _ = 1 := by rw [huw', hee]
  have huinv : (quasiBar u)⁻¹ = quasiBar u * quasiCentral u := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc]
    exact hee
  rcases d.eq_of_mem_centralizer_of_mul_self
      (Subgroup.mul_mem _ d.quasiBar_mem_centralizer hk) huk with h1 | h1
  ·
    refine ⟨l * quasiCentral u, L.mul_mem hl d.quasiCentral_mem, ?_, ?_⟩
    · have h2 : l * quasiCentral u * (l * quasiCentral u) =
          l * l * (quasiCentral u * quasiCentral u) := by
        calc l * quasiCentral u * (l * quasiCentral u) =
            l * (quasiCentral u * l) * quasiCentral u := by group
          _ = l * (l * quasiCentral u) * quasiCentral u := by rw [d.commute_quasiCentral l]
          _ = l * l * (quasiCentral u * quasiCentral u) := by group
      rw [h2, hll, hee, mul_one]
    · rw [← hlk, show k = (quasiBar u)⁻¹ from eq_inv_of_mul_eq_one_right h1, huinv,
        ← mul_assoc, hlu, mul_assoc]
  ·
    refine ⟨l, hl, hll, ?_⟩
    have hk' : k = quasiBar u := by
      calc k = (quasiBar u)⁻¹ * (quasiBar u * k) := by group
        _ = quasiBar u := by rw [h1, huinv, mul_assoc, hee, mul_one]
    rw [← hlk, hk', hlu]

theorem v_mem_partCLeft : x * u * x⁻¹ ∈ partCLeft T L :=
  d.caseC3BCD.swap_right u d.caseC3BCD.partC.self_mem

theorem v_mem : x * u * x⁻¹ ∈ quasiNormalizer u :=
  mem_quasiNormalizer_of_mem_partCSylow (partCLeft_le d.v_mem_partCLeft)

theorem v_mul_self : x * u * x⁻¹ * (x * u * x⁻¹) = centralElt J := by
  rw [show x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ by group, d.caseC3BCD.partC.sq,
    d.caseC3BCD.partC.conj_centralElt]

theorem vBar_mem : quasiMk u ⟨x * u * x⁻¹, d.v_mem⟩ ∈ L ∧
    quasiMk u ⟨x * u * x⁻¹, d.v_mem⟩ * quasiMk u ⟨x * u * x⁻¹, d.v_mem⟩ = quasiCentral u := by
  refine ⟨quasiMk_mem_of_mem_partCLeft d.v_mem_partCLeft _, ?_⟩
  rw [← map_mul, ← d.quasiMk_centralElt]
  exact congrArg (quasiMk u) (Subtype.ext d.v_mul_self)

theorem exists_conj_quasiBar_mul {l₁ l₂ : QuasiQuotient u} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L)
    (hl₁l₁ : l₁ * l₁ = quasiCentral u) (hl₂l₂ : l₂ * l₂ = quasiCentral u) :
    ∃ ω ∈ L, ∃ c : QuasiQuotient u, (c = 1 ∨ c = quasiCentral u) ∧
      ω * (quasiBar u * l₁) * ω⁻¹ = quasiBar u * l₂ * c := by
  have hinv : ∀ {l : QuasiQuotient u} (hl : l ∈ L), l * l = quasiCentral u →
      (((⟨l, hl⟩ : L) : L) : L ⧸ Subgroup.center L) *
          (((⟨l, hl⟩ : L) : L) : L ⧸ Subgroup.center L) = 1 ∧
        (((⟨l, hl⟩ : L) : L) : L ⧸ Subgroup.center L) ≠ 1 := by
    intro l hl hll
    refine ⟨?_, fun h1 => ?_⟩
    · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      have : (⟨l, hl⟩ : L) * ⟨l, hl⟩ = ⟨quasiCentral u, d.quasiCentral_mem⟩ := Subtype.ext hll
      rw [this]
      exact d.oneComponent.mem_center d.baseConfig
    · rcases d.eq_of_mem_center ((QuotientGroup.eq_one_iff _).mp h1) with h2 | h2
      · change l = 1 at h2
        rw [h2, mul_one] at hll
        exact d.quasiCentral_ne_one hll.symm
      · change l = quasiCentral u at h2
        rw [h2, d.quasiCentral_mul_self] at hll
        exact d.quasiCentral_ne_one hll.symm
  obtain ⟨h1, h1'⟩ := hinv hl₁ hl₁l₁
  obtain ⟨h2, h2'⟩ := hinv hl₂ hl₂l₂
  obtain ⟨ω, hωL, c, hcZ, hω⟩ := exists_conj_mul_eq_of_alternating d.eA h1 h1' h2 h2'
    d.quasiBar_mem_centralizer
  exact ⟨ω, hωL, c, d.eq_of_mem_center hcZ, hω⟩

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
