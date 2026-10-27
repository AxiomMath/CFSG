module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique

theorem exists_sylow_le_containing {X : Type} [Group X] [Finite X] (H F : Subgroup X)
    (hFH : F ≤ H) (hF : IsPGroup 2 F) (hindex : ¬ 2 ∣ H.index) :
    ∃ Q : Subgroup X, Q ≤ H ∧ F ≤ Q ∧ IsSylowTwoOf Q ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : IsPGroup 2 (F.subgroupOf H) := hF.comap_of_injective H.subtype Subtype.coe_injective
  obtain ⟨R, hR⟩ := hF'.exists_le_sylow
  refine ⟨(R : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, fun f hf => ?_, ?_⟩
  · exact ⟨⟨f, hFH hf⟩, hR (Subgroup.mem_subgroupOf.mpr hf), rfl⟩
  · rw [isSylowTwoOf_top_iff]
    refine ⟨R.isPGroup'.map H.subtype, ?_⟩
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact R.not_dvd_index h
    · exact hindex h

@[expose] def SelfCentralizingFusionData (X : Type) [Group X] : Prop :=
  ∃ H E : Subgroup X, E ≤ H ∧ ¬ 2 ∣ H.index ∧ (∀ h ∈ H, ∀ x ∈ E, h * x * h⁻¹ ∈ E) ∧
    IsPGroup 2 E ∧
    (∀ D : Subgroup X, D ≤ E → (∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D) → D = ⊥ ∨ D = E) ∧
    (∀ h ∈ H, (∀ x ∈ E, h * x = x * h) → h ∈ E) ∧
    ∃ e ∈ E, ∃ g : X, e * e = 1 ∧ g * e * g⁻¹ ∈ H ∧ g * e * g⁻¹ ∉ E

theorem noStronglyClosedElemAbelian_of_selfCentralizingFusionData {X : Type} [Group X] [Finite X]
    (hX : SelfCentralizingFusionData X) : NoStronglyClosedElemAbelian X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, E, hEH, hindex, hnorm, hE2, hmin, hcent, e, he, g, he2, hgH, hgE⟩ := hX
  set m : X := g * e * g⁻¹ with hm
  have hm2 : m * m = 1 := by
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hz2 : IsPGroup 2 (Subgroup.zpowers m) := by
    have h1 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hm2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  have hmN : Subgroup.zpowers m ≤ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm m hgH x hx, fun hx => ?_⟩
    have := hnorm m⁻¹ (H.inv_mem hgH) _ hx
    simpa [mul_assoc] using this
  have hF2 : IsPGroup 2 (Subgroup.zpowers m ⊔ E : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hz2 hE2 hmN
  have hFH : (Subgroup.zpowers m ⊔ E : Subgroup X) ≤ H :=
    sup_le ((Subgroup.zpowers_le).mpr hgH) hEH
  obtain ⟨Q, hQH, hFQ, hQsyl⟩ := exists_sylow_le_containing H _ hFH hF2 hindex
  have hEQ : E ≤ Q := le_trans le_sup_right hFQ
  have hmQ : m ∈ Q := hFQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers m))
  refine noStronglyClosedElemAbelian_of_sylow Q hQsyl fun A hA => ?_
  by_contra hA1
  have hQp : IsPGroup 2 Q := hQsyl.2.1
  have : Group.IsNilpotent Q := hQp.isNilpotent
  have hAQ : A ≤ Q := hA.le
  have hAn : (A.subgroupOf Q).Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hx' : (x : X) ∈ A := hx
    have hconj : (((y : X)⁻¹)⁻¹ * (x : X) * (y : X)⁻¹) ∈ Q := by
      simpa using Q.mul_mem (Q.mul_mem y.2 x.2) (Q.inv_mem y.2)
    have := hA.closed (x : X) hx' ((y : X)⁻¹) hconj
    show (y : X) * (x : X) * (y : X)⁻¹ ∈ A
    simpa using this
  have hAne : A.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAQ ha⟩ : Q) ∈ A.subgroupOf Q := ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hAne)
  have hcA : ((c : Q) : X) ∈ A := c.2.1
  have hcQ : ((c : Q) : X) ∈ Q := (c : Q).2
  have hcc : ∀ q ∈ Q, ((c : Q) : X) * q = q * ((c : Q) : X) := by
    intro q hq
    have := Subgroup.mem_center_iff.mp c.2.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hc1' : ((c : Q) : X) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext h'))
  have hcE : ((c : Q) : X) ∈ E := hcent _ (hQH hcQ) fun x hx => hcc x (hEQ hx)
  have hBn : ∀ h ∈ H, ∀ d ∈ A ⊓ E, h * d * h⁻¹ ∈ A ⊓ E := by
    intro h hh d hd
    have hdE : h * d * h⁻¹ ∈ E := hnorm h hh d hd.2
    refine ⟨?_, hdE⟩
    have := hA.closed d hd.1 h⁻¹ (by simpa using hEQ hdE)
    simpa using this
  have hBne : A ⊓ E ≠ ⊥ := by
    intro hbot
    have : ((c : Q) : X) ∈ A ⊓ E := ⟨hcA, hcE⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hc1' this
  have hEA : E ≤ A := by
    rcases hmin (A ⊓ E) inf_le_right hBn with h | h
    · exact absurd h hBne
    · rw [← h]; exact inf_le_left
  have hAE : A ≤ E := by
    intro a ha
    refine hcent a (hQH (hAQ ha)) fun x hx => ?_
    have := hA.elem.1.is_comm.comm ⟨a, ha⟩ ⟨x, hEA hx⟩
    exact congrArg Subtype.val this
  have heA : e ∈ A := hEA he
  have hmA : m ∈ A := by
    have := hA.closed e heA g⁻¹ (by simpa [hm] using hmQ)
    simpa [hm] using this
  exact hgE (hAE hmA)

end CFSG.QuasithinUnique.K1
