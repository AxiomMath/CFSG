module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeLift
public import CFSG.LocalAnalysis.AGLEmbedding.CentralizerTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem mem_normalizer_commutator_of_mem_normalizer {Y : Type*} [Group Y] {H : Subgroup Y}
    {t : Y} (ht : t ∈ Subgroup.normalizer (H : Set Y)) :
    t ∈ Subgroup.normalizer ((⁅H, H⁆ : Subgroup Y) : Set Y) := by
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_commutator, h]

theorem eq_or_eq_of_map_subtype_layer {Y : Type*} [Group Y] (K : Subgroup Y) {A W : Subgroup K}
    {t : K}
    (hlay : ∀ Y₀ : Subgroup K, A ≤ Y₀ → Y₀ ≤ W → t ∈ Subgroup.normalizer (Y₀ : Set K) →
      Y₀ = A ∨ Y₀ = W)
    {Y₀ : Subgroup Y} (hAY : A.map K.subtype ≤ Y₀) (hYW : Y₀ ≤ W.map K.subtype)
    (htY : (t : Y) ∈ Subgroup.normalizer (Y₀ : Set Y)) :
    Y₀ = A.map K.subtype ∨ Y₀ = W.map K.subtype := by
  have hYeq : (Y₀.subgroupOf K).map K.subtype = Y₀ := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left (hYW.trans (Subgroup.map_subtype_le _))
  have hAY' : A ≤ Y₀.subgroupOf K := fun a ha =>
    Subgroup.mem_subgroupOf.mpr (hAY (Subgroup.mem_map_of_mem _ ha))
  have hYW' : Y₀.subgroupOf K ≤ W := by
    intro y hy
    obtain ⟨w', hw', he⟩ := hYW (Subgroup.mem_subgroupOf.mp hy)
    rw [← Subtype.ext he]
    exact hw'
  have htY' : t ∈ Subgroup.normalizer ((Y₀.subgroupOf K : Subgroup K) : Set K) :=
    Subgroup.le_normalizer_comap K.subtype htY
  rcases hlay _ hAY' hYW' htY' with h | h
  · left
    rw [← hYeq, h]
  · right
    rw [← hYeq, h]

theorem map_mk_inf_comap_eq {Q : Type*} [Group Q] {O : Subgroup Q} [O.Normal] {U : Subgroup Q}
    {V' : Subgroup (Q ⧸ O)} (hV' : V' ≤ U.map (QuotientGroup.mk' O)) :
    (U ⊓ V'.comap (QuotientGroup.mk' O)).map (QuotientGroup.mk' O) = V' := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := hV' hv
    exact ⟨x, ⟨hx, hv⟩, rfl⟩

section Lift

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (O : Subgroup Q) [O.Normal]
  (hO : p.Coprime (Nat.card O))
include hp hO

theorem card_inf_comap_eq {U : Subgroup Q} (hU : IsPGroup p U) {V' : Subgroup (Q ⧸ O)}
    (hV' : V' ≤ U.map (QuotientGroup.mk' O)) :
    Nat.card (U ⊓ V'.comap (QuotientGroup.mk' O) : Subgroup Q) = Nat.card V' := by
  rw [← card_map_mk_of_isPGroup hp O hO (hU.to_le inf_le_left), map_mk_inf_comap_eq hV']

theorem inf_comap_commute {U : Subgroup Q} (hU : IsPGroup p U) {Z' V' : Subgroup (Q ⧸ O)}
    (hZc : ∀ a ∈ Z', ∀ v ∈ V', a * v = v * a) :
    ∀ x ∈ U ⊓ Z'.comap (QuotientGroup.mk' O), ∀ w ∈ U ⊓ V'.comap (QuotientGroup.mk' O),
      x * w = w * x := fun _ hx _ hw =>
  commute_of_mk_commute hp O hO hU hx.1 hw.1 (hZc _ hx.2 _ hw.2)

theorem inf_comap_le_commutator {U : Subgroup Q} (hU : IsPGroup p U)
    {Z' V' : Subgroup (Q ⧸ O)} (hZU : Z' ≤ U.map (QuotientGroup.mk' O))
    (hVU : V' ≤ U.map (QuotientGroup.mk' O)) (hZder : Z' ≤ ⁅V', V'⁆) :
    U ⊓ Z'.comap (QuotientGroup.mk' O) ≤
      ⁅U ⊓ V'.comap (QuotientGroup.mk' O), U ⊓ V'.comap (QuotientGroup.mk' O)⁆ := by
  refine le_of_map_mk_le hp O hO hU inf_le_left
    ((Subgroup.commutator_le_self _).trans inf_le_left) ?_
  rw [map_mk_inf_comap_eq hZU, Subgroup.map_commutator, map_mk_inf_comap_eq hVU]
  exact hZder

theorem exists_lift_layer {U B : Subgroup Q} (hU : IsPGroup p U) (hOB : O ≤ B)
    {Z' V' : Subgroup (Q ⧸ O)} (hZV : Z' ≤ V') (hVU : V' ≤ U.map (QuotientGroup.mk' O))
    {c : Q ⧸ O} (hcB : c ∈ B.map (QuotientGroup.mk' O))
    (hcV : c ∈ Subgroup.normalizer (V' : Set (Q ⧸ O)))
    (hcZ : c ∈ Subgroup.normalizer (Z' : Set (Q ⧸ O)))
    (hnt : ∃ u ∈ V', c * u * c⁻¹ * u⁻¹ ∉ Z')
    (hlay : ∀ Y' : Subgroup (Q ⧸ O), Z' ≤ Y' → Y' ≤ V' →
      c ∈ Subgroup.normalizer (Y' : Set (Q ⧸ O)) → Y' = Z' ∨ Y' = V') :
    ∃ t ∈ B, QuotientGroup.mk' O t = c ∧
      t ∈ Subgroup.normalizer ((U ⊓ V'.comap (QuotientGroup.mk' O) : Subgroup Q) : Set Q) ∧
      t ∈ Subgroup.normalizer ((U ⊓ Z'.comap (QuotientGroup.mk' O) : Subgroup Q) : Set Q) ∧
      (∃ w ∈ U ⊓ V'.comap (QuotientGroup.mk' O),
        t * w * t⁻¹ * w⁻¹ ∉ U ⊓ Z'.comap (QuotientGroup.mk' O)) ∧
      ∀ Y : Subgroup Q, U ⊓ Z'.comap (QuotientGroup.mk' O) ≤ Y →
        Y ≤ U ⊓ V'.comap (QuotientGroup.mk' O) → t ∈ Subgroup.normalizer (Y : Set Q) →
        Y = U ⊓ Z'.comap (QuotientGroup.mk' O) ∨ Y = U ⊓ V'.comap (QuotientGroup.mk' O) := by
  set mk := QuotientGroup.mk' O with hmk
  have hZU : Z' ≤ U.map mk := hZV.trans hVU
  have hW₀map := map_mk_inf_comap_eq hVU
  have hA₀map := map_mk_inf_comap_eq hZU
  have hA₀W₀ : U ⊓ Z'.comap mk ≤ U ⊓ V'.comap mk := inf_le_inf_left _ (Subgroup.comap_mono hZV)
  have hW₀p : IsPGroup p (U ⊓ V'.comap mk : Subgroup Q) := hU.to_le inf_le_left
  obtain ⟨b, hb, rfl⟩ := hcB
  obtain ⟨t, htB, htW, hmt⟩ := exists_lift_mem_normalizer hp O hO hW₀p hOB hb
    (by rw [hW₀map]; exact hcV)
  have htA : t ∈ Subgroup.normalizer ((U ⊓ Z'.comap mk : Subgroup Q) : Set Q) :=
    mem_normalizer_of_mk_mem_normalizer hp O hO hW₀p hA₀W₀ htW (by rw [hA₀map, hmt]; exact hcZ)
  refine ⟨t, htB, hmt, htW, htA, ?_, fun Y hAY hYW htY => ?_⟩
  · obtain ⟨u, hu, hcu⟩ := hnt
    rw [← hW₀map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    refine ⟨w, hw, fun hmem => hcu ?_⟩
    have h1 : mk (t * w * t⁻¹ * w⁻¹) ∈ Z' := hmem.2
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv, hmt] at h1
  · refine eq_or_eq_of_map_mk_layer hp O hO hW₀p hA₀W₀ le_rfl ?_ hAY hYW htY
    intro Y' h1 h2 h3
    rw [hA₀map] at h1
    rw [hW₀map] at h2
    rw [hmt] at h3
    rw [hA₀map, hW₀map]
    exact hlay Y' h1 h2 h3

end Lift

theorem coprime_six_orderOf_of_pow_mem {Q : Type*} [Group Q] {O : Subgroup Q} [Finite O]
    {t : Q} (ht5 : t ^ 5 ∈ O) (hOodd : Odd (Nat.card O)) (hO3 : Nat.Coprime 3 (Nat.card O)) :
    Nat.Coprime 6 (orderOf t) := by
  have htord : orderOf t ∣ 5 * Nat.card O := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨t ^ 5, ht5⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
    rw [pow_mul]
    have h2 := congrArg (fun x : O => (x : Q)) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  refine Nat.Coprime.coprime_dvd_right htord ?_
  refine Nat.Coprime.mul_right (by norm_num) ?_
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  exact Nat.coprime_mul_iff_left.mpr ⟨Odd.coprime_two_left hOodd, hO3⟩

end CFSG.AGLEmbedding
