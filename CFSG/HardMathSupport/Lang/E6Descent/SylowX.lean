module

public import CFSG.HardMathSupport.Lang.E6Descent.SylowNormal
public import CFSG.HardMathSupport.Lang.E6Descent.FixedElementary

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

theorem card_eq_one_or_three_of_isPGroup {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (hle : Nat.card G ≤ 3) : Nat.card G = 1 ∨ Nat.card G = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hG
  rw [hn] at hle ⊢
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · exfalso
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega

theorem centralizes_of_card_le_three {X : Type*} [Group X] (Z : Subgroup X) [Finite Z]
    (hZp : IsPGroup 3 Z) (hZ3 : Nat.card Z ≤ 3) (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    {u : X} (hu3 : u ^ 3 = 1) (hN : u ∈ Subgroup.normalizer (Z : Set X)) :
    ∀ z ∈ Z, u * z = z * u := by
  have hcard := card_eq_one_or_three_of_isPGroup hZp hZ3
  rcases hcard with h1 | h3
  · intro z hz
    have : Z = ⊥ := Subgroup.card_eq_one.mp h1
    rw [this, Subgroup.mem_bot] at hz
    subst hz; simp
  · have hexp : ∀ a ∈ Z, a ^ 3 = 1 := by
      intro a ha
      have := pow_card_eq_one' (G := Z) (x := (⟨a, ha⟩ : Z))
      rw [h3] at this
      simpa using congrArg Subtype.val this
    have hcube := card_le_card_centralizer_cube Z hcomm hexp hu3 hN
    set C := Z ⊓ Subgroup.centralizer ({u} : Set X) with hC
    have hCdvd : Nat.card C ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le (inf_le_left : C ≤ Z)
    have hC3 : Nat.card C = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hCdvd with h | h
      · rw [h3, h] at hcube; omega
      · exact h
    have hCZ : C = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hC3, h3])
    intro z hz
    have : z ∈ C := hCZ ▸ hz
    have hzc : z ∈ Subgroup.centralizer ({u} : Set X) := this.2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hzc).symm

theorem exists_noncentral_fixed_of_sylow (hB : RankBoundTStar)
    {X : Type} [Group X] [Finite X] {L Z F₀ T₀ : Subgroup X}
    (hZL : Z ≤ L) (hZcen : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZfull : ∀ y ∈ L, (∀ l ∈ L, y * l = l * y) → y ∈ Z)
    (hZp : IsPGroup 3 Z) (hZ3 : Nat.card Z ≤ 3)
    {u : X} (hu3 : u ^ 3 = 1) (huN : u ∈ Subgroup.normalizer (L : Set X)) (huL : u ∉ L)
    (hF₀L : F₀ ≤ L) (hZF₀ : Z ≤ F₀) (hF₀p : IsPGroup 3 F₀)
    (hF₀c : ∀ a ∈ F₀, ∀ b ∈ F₀, a * b * a⁻¹ * b⁻¹ ∈ Z) (hF₀e : ∀ a ∈ F₀, a ^ 3 ∈ Z)
    (hF₀o : 27 * Nat.card Z ≤ Nat.card F₀)
    (hT₀L : T₀ ≤ L) (hT₀p : IsPGroup 3 T₀) (hT₀o : 81 * Nat.card Z ≤ Nat.card T₀) :
    ∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧ y * u = u * y ∧ y ∉ Z := by
  set H : Subgroup X := L ⊔ Subgroup.zpowers u with hHdef
  have hLH : L ≤ H := le_sup_left
  have huH : u ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hHN : H ≤ Subgroup.normalizer (L : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 huN)
  have hZnorm : ∀ g ∈ Subgroup.normalizer (L : Set X), ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    have hgi : g⁻¹ ∈ Subgroup.normalizer (L : Set X) := Subgroup.inv_mem _ hg
    have hl : g * z * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg z).1 (hZL hz)
    apply hZfull _ hl
    intro l hl'
    have hl'' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgi l).1 hl'
    have h1 := hZcen z hz _ hl''
    calc g * z * g⁻¹ * l = g * (z * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * l * g⁻¹⁻¹) * z) * g⁻¹ := by rw [h1]
      _ = l * (g * z * g⁻¹) := by group
  have hNZ : u ∈ Subgroup.normalizer (Z : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hZnorm u huN h hh
    · intro hh
      have := hZnorm u⁻¹ (Subgroup.inv_mem _ huN) _ hh
      simpa [mul_assoc] using this
  have : Finite Z := inferInstance
  have huZ := centralizes_of_card_le_three Z hZp hZ3 (fun a ha b hb => hZcen a ha b (hZL hb))
    hu3 hNZ
  have hZH : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z := by
    intro z hz h hh
    have hle : H ≤ Subgroup.centralizer ({z} : Set X) := by
      refine sup_le ?_ ?_
      · intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hZcen z hz l hl).symm
      · refine Subgroup.zpowers_le.2 ?_
        exact Subgroup.mem_centralizer_singleton_iff.mpr (huZ z hz)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  have hHtop : L.subgroupOf H ⊔ Subgroup.zpowers (⟨u, huH⟩ : ↥H) = ⊤ := by
    have h1 : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
    have h2 : (Subgroup.zpowers (⟨u, huH⟩ : ↥H)).map H.subtype = Subgroup.zpowers u := by
      rw [MonoidHom.map_zpowers]; rfl
    have h3 : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, h1, h2, h3]
  have hZH' : Z ≤ H := hZL.trans hLH
  have hF₀H : F₀ ≤ H := hF₀L.trans hLH
  have hT₀H : T₀ ≤ H := hT₀L.trans hLH
  obtain ⟨y, hyL, hyp, hyu, hyZ⟩ := exists_noncentral_fixed_of_sylow_normal hB
    (H := ↥H) (L := L.subgroupOf H) (Z := Z.subgroupOf H) (F₀ := F₀.subgroupOf H)
    (T₀ := T₀.subgroupOf H) (u := (⟨u, huH⟩ : ↥H))
    (fun z hz => hZL hz) (fun z hz h => Subtype.ext (hZH z hz h h.2))
    (hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZH').symm)
    (by rw [card_subgroupOf_of_le hZH']; exact hZ3)
    (Subtype.ext (by simpa using hu3)) (fun h => huL h) hHtop
    (fun a ha => hF₀L ha) (fun z hz => hZF₀ hz) (hF₀p.of_equiv (Subgroup.subgroupOfEquivOfLe hF₀H).symm)
    (fun a ha b hb => hF₀c a ha b hb) (fun a ha => hF₀e a ha)
    (by rw [card_subgroupOf_of_le hZH', card_subgroupOf_of_le hF₀H]; exact hF₀o)
    (fun t ht => hT₀L ht) (hT₀p.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀H).symm)
    (by rw [card_subgroupOf_of_le hZH', card_subgroupOf_of_le hT₀H]; exact hT₀o)
  refine ⟨(y : X), hyL, ?_, congrArg Subtype.val hyu, hyZ⟩
  obtain ⟨k, hk⟩ := hyp ⟨y, Subgroup.mem_zpowers y⟩
  exact CFSG.AGLEmbedding.FixedThree.isPGroup_zpowers_of_pow_eq_one (k := k)
    (by simpa using congrArg (fun w : Subgroup.zpowers y => ((w : ↥H) : X)) hk)

end CFSG.HardMathSupport.Lang.E6Descent
