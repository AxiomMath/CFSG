module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Family
public import CFSG.LocalAnalysis.GL83PartI.I_22_6.Fixed

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def torsionCentre (p : ℕ) (L : Subgroup G) : Subgroup G where
  carrier := {v | v ∈ L ∧ (∀ w ∈ L, v * w = w * v) ∧ v ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haL, hac, hap⟩ ⟨hbL, hbc, hbp⟩
    refine ⟨L.mul_mem haL hbL, fun w hw => ?_, ?_⟩
    · calc a * b * w = a * (b * w) := mul_assoc _ _ _
        _ = a * (w * b) := by rw [hbc w hw]
        _ = (a * w) * b := (mul_assoc _ _ _).symm
        _ = (w * a) * b := by rw [hac w hw]
        _ = w * (a * b) := mul_assoc _ _ _
    · have hcomm : Commute a b := hac b hbL
      rw [hcomm.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨L.one_mem, fun w _ => by rw [one_mul, mul_one], one_pow p⟩
  inv_mem' := by
    rintro a ⟨haL, hac, hap⟩
    refine ⟨L.inv_mem haL, fun w hw => ?_, by rw [inv_pow, hap, inv_one]⟩
    have h : Commute a w := hac w hw
    exact h.inv_left.eq

theorem mem_torsionCentre {p : ℕ} {L : Subgroup G} {v : G} :
    v ∈ torsionCentre p L ↔ v ∈ L ∧ (∀ w ∈ L, v * w = w * v) ∧ v ^ p = 1 := Iff.rfl

theorem conj_mem_torsionCentre {p : ℕ} {L : Subgroup G} {c : G} (hc : cj c L = L) {v : G}
    (hv : v ∈ torsionCentre p L) : c * v * c⁻¹ ∈ torsionCentre p L := by
  obtain ⟨hvL, hvc, hvp⟩ := hv
  refine ⟨?_, fun w hw => ?_, ?_⟩
  · have h : c * v * c⁻¹ ∈ cj c L := mul_mem_cj hvL
    rwa [hc] at h
  · have hw' : c⁻¹ * w * c ∈ L := by
      have h : w ∈ cj c L := by rwa [hc]
      exact mem_cj.1 h
    have h := hvc _ hw'
    calc c * v * c⁻¹ * w = c * (v * (c⁻¹ * w * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * w * c) * v) * c⁻¹ := by rw [h]
      _ = w * (c * v * c⁻¹) := by group
  · rw [conj_pow, hvp, mul_one, mul_inv_cancel]

theorem le_normalizer_torsionCentre {p : ℕ} {B : Subgroup G} {𝒦 : Set (Subgroup G)}
    (hF : IsFam p B 𝒦) :
    B ≤ Subgroup.normalizer (torsionCentre p (layer 𝒦) : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => conj_mem_torsionCentre (hF.cj_layer hc) hv, fun hv => ?_⟩
  have h := conj_mem_torsionCentre (hF.cj_layer (B.inv_mem hc)) hv
  have e : c⁻¹ * (c * v * c⁻¹) * c⁻¹⁻¹ = v := by group
  rwa [e] at h

theorem IsFam.dvd_card_cen [Finite G] {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    {𝒦 : Set (Subgroup G)} (hF : IsFam p B 𝒦)
    (hSC : ∀ y ∈ Subgroup.centralizer (B : Set G), y ^ p = 1 → y ∈ B)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) (hZ : p ∣ Nat.card (Subgroup.center K₀)) :
    p ∣ Nat.card (cen B K₀) := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hZ
  have hz₀K : ((z : K₀) : G) ∈ K₀ := (z : K₀).2
  have hz₀ord : orderOf ((z : K₀) : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz₀c : ∀ y ∈ K₀, y * ((z : K₀) : G) = ((z : K₀) : G) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)
  have hz₀L : ∀ y ∈ layer 𝒦, y * ((z : K₀) : G) = ((z : K₀) : G) * y := by
    have hle : layer 𝒦 ≤ Subgroup.centralizer ({((z : K₀) : G)} : Set G) := by
      refine iSup₂_le fun K hK y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      by_cases hKK : K = K₀
      · subst hKK
        exact (hz₀c y hy).symm
      · exact (hF.comm K hK K₀ hK₀ hKK y hy _ hz₀K).symm
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (hle hy) _ rfl).symm
  have hzV : ((z : K₀) : G) ∈ torsionCentre p (layer 𝒦) :=
    ⟨le_layer hK₀ hz₀K, fun w hw => (hz₀L w hw).symm, by
      rw [← hz₀ord]
      exact pow_orderOf_eq_one _⟩
  have hVdvd : p ∣ Nat.card (torsionCentre p (layer 𝒦)) := by
    have h := orderOf_dvd_natCard (⟨_, hzV⟩ : torsionCentre p (layer 𝒦))
    rwa [Subgroup.orderOf_mk, hz₀ord] at h
  obtain ⟨v, hvV, hv1, hvB⟩ := exists_ne_one_commute_of_isPGroup (isPGroup_of_elem hF.elem)
    (le_normalizer_torsionCentre hF) hVdvd
  obtain ⟨hvL, hvc, hvp⟩ := hvV
  have hvB' : v ∈ B := hSC v (Subgroup.mem_centralizer_iff.2 fun c hc => hvB c hc) hvp
  have hvcen : v ∈ cen B K₀ := mem_cen.2 ⟨hvB', fun x hx => hvc x (le_layer hK₀ hx)⟩
  have hvord : orderOf v = p := orderOf_eq_prime hvp hv1
  have h := orderOf_dvd_natCard (⟨v, hvcen⟩ : cen B K₀)
  rwa [Subgroup.orderOf_mk, hvord] at h

end GL83.CompFam
