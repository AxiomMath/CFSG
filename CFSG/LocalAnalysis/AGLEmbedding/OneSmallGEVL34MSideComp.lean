module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeDiag

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem L34MSide.comm_of_mem_two [Finite Y] {L L' : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hL' : IsComponentOf L' ⊤) (hne : L ≠ L') {x : Y} (hx' : x ∈ L') :
    ∀ l ∈ L, x * l = l * x := fun _ hl => (commute_of_mem_ne hL hL' hne hl hx').symm

omit [Finite Y] in
theorem L34MSide.noncentral_conj {L : Subgroup Y} {x : Y} (hx : ∃ l ∈ L, x * l ≠ l * x)
    (n : Y) :
    ∃ l ∈ L.map (MulAut.conj n).toMonoidHom, n * x * n⁻¹ * l ≠ l * (n * x * n⁻¹) := by
  obtain ⟨l, hl, hne⟩ := hx
  refine ⟨n * l * n⁻¹, conj_mem_map_conj n hl, fun h => hne ?_⟩
  have h2 : n⁻¹ * (n * x * n⁻¹ * (n * l * n⁻¹)) * n =
      n⁻¹ * (n * l * n⁻¹ * (n * x * n⁻¹)) * n := by
    rw [h]
  simpa [mul_assoc] using h2

omit [Finite Y] in
theorem L34MSide.normal_of_unique {L₀ : Subgroup Y} (hL₀ : IsComponentOf L₀ ⊤)
    (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀) : L₀.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := huniq _ (isComponentOf_map_conj hL₀ g)
  rw [← h]
  exact conj_mem_map_conj g hn

theorem L34MSide.unique_normal_of_mem {z : Y}
    (hzcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → z ∉ Subgroup.centralizer (L : Set Y))
    {L₀ : Subgroup Y} (hL₀ : IsComponentOf L₀ ⊤) (hz : z ∈ L₀) :
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀) ∧ L₀.Normal := by
  have huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀ := by
    intro L hL
    by_contra hne
    apply hzcomp L hL
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (L34MSide.comm_of_mem_two hL hL₀ hne hz l hl).symm
  exact ⟨huniq, L34MSide.normal_of_unique hL₀ huniq⟩

theorem L34MSide.le_of_normal_of_three_dvd {T : Subgroup Y} (S : Sylow 3 Y)
    (hcenter : ∀ x ∈ (S : Subgroup Y), (∀ y ∈ (S : Subgroup Y), x * y = y * x) → x ∈ T)
    (htr : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * t * n⁻¹ = s)
    {N : Subgroup Y} (hN : N.Normal) (h3 : 3 ∣ Nat.card N) : T ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxp : IsPGroup 3 (Subgroup.zpowers (x : Y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← hx]
    exact orderOf_injective N.subtype N.subtype_injective x
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q S
  have hxS : g * (x : Y) * g⁻¹ ∈ (S : Subgroup Y) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨x, hQ (Subgroup.mem_zpowers _), by simp [MulAut.conj_apply]⟩
  have hxN : g * (x : Y) * g⁻¹ ∈ N := hN.conj_mem _ x.2 g
  have hx1 : g * (x : Y) * g⁻¹ ≠ 1 := by
    intro h
    have : (x : Y) = 1 := by
      have := congrArg (fun w => g⁻¹ * w * g) h
      simpa [mul_assoc] using this
    have hx1' : x = 1 := Subtype.ext this
    rw [hx1', orderOf_one] at hx
    omega
  have hSnil : Group.IsNilpotent (S : Subgroup Y) := S.isPGroup'.isNilpotent
  set H := N.subgroupOf (S : Subgroup Y) with hH
  have hHn : H.Normal := Subgroup.normal_subgroupOf
  have hHne : H ≠ ⊥ := by
    intro h
    have : (⟨_, hxS⟩ : (S : Subgroup Y)) ∈ H := Subgroup.mem_subgroupOf.mpr hxN
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (congrArg Subtype.val this)
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  have hwN : ((w : (S : Subgroup Y)) : Y) ∈ N := Subgroup.mem_subgroupOf.mp hw.1
  have hwc : ∀ y ∈ (S : Subgroup Y), (w : Y) * y = y * (w : Y) := by
    intro y hy
    have := Subgroup.mem_center_iff.mp hw.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  have hwT : ((w : (S : Subgroup Y)) : Y) ∈ T := hcenter _ (w : (S : Subgroup Y)).2 hwc
  have hw1' : ((w : (S : Subgroup Y)) : Y) ≠ 1 := by
    intro h
    apply hw1
    exact Subtype.ext (Subtype.ext h)
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]; exact N.one_mem
  obtain ⟨n, hn⟩ := htr _ hwT hw1' s hs hs1
  rw [← hn]
  exact hN.conj_mem _ hwN n

theorem L34MSide.three_dvd_card_component (hcore : primeComplementCore (G := Y) 3 = ⊥)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : 3 ∣ Nat.card L := by
  have h3 := prime_dvd_card_center_quotient_of_isComponentOf Nat.prime_three hcore hL
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)]
  exact Dvd.dvd.mul_right h3 _

omit [Finite Y] in
theorem L34MSide.mem_zpowers_of_mem_zpowers {z w : Y} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hw : w ∈ Subgroup.zpowers z) (hw1 : w ≠ 1) : z ∈ Subgroup.zpowers w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, ho]
  have h := mem_zpowers_of_prime_card hcard (g := ⟨w, hw⟩)
    (g' := ⟨z, Subgroup.mem_zpowers z⟩) (fun h => hw1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite Y] in
theorem L34MSide.ne_one_of_noncentral {L : Subgroup Y} {x : Y} (hx : ∃ l ∈ L, x * l ≠ l * x) :
    x ≠ 1 := by
  rintro rfl
  obtain ⟨l, -, h⟩ := hx
  exact h (by simp)

omit [Finite Y] in
theorem L34MSide.conj_comm_of_normal {L : Subgroup Y} (hN : L.Normal) {t : Y}
    (ht : ∀ l ∈ L, t * l = l * t) (m : Y) : ∀ l ∈ L, m * t * m⁻¹ * l = l * (m * t * m⁻¹) := by
  intro l hl
  have hl' : m⁻¹ * l * m ∈ L := by
    have := hN.conj_mem l hl m⁻¹
    simpa using this
  have e := ht _ hl'
  calc m * t * m⁻¹ * l = m * (t * (m⁻¹ * l * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * l * m) * t) * m⁻¹ := by rw [e]
    _ = l * (m * t * m⁻¹) := by group

end CFSG.AGLEmbedding
