module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Labelled
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem card_Gxy_eleven (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    {ω : G} (hωa : ω ∈ Gx a) (hω : orderOf ω = 11) : Nat.card ↥(Gxy a ω) = 22 := by
  obtain ⟨z', b', u', hF⟩ := exists_labelled_facts hI h
  have hωa_order : orderOf (⟨ω, hωa⟩ : ↥(Gx a)) = 11 := by
    rw [Subgroup.orderOf_mk]
    exact hω
  obtain ⟨e1⟩ := hF.table_eleven ⟨ω, hωa⟩ hωa_order
  obtain ⟨e2⟩ := nonempty_mulEquiv_Gxy (G := G) (a := a) (x := ω) hωa
  have hcard : Nat.card (Multiplicative (ZMod 11) × Multiplicative (ZMod 2)) = 22 := by
    rw [Nat.card_prod (Multiplicative (ZMod 11)) (Multiplicative (ZMod 2))]
    have h11 : Nat.card (Multiplicative (ZMod 11)) = 11 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h11, h2]
  exact (Nat.card_congr (e2.trans e1).toEquiv).trans hcard

theorem padicValNat_card_Gx_eleven (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) {ω : G} (hωa : ω ∈ Gx a) (hω : orderOf ω = 11) :
    padicValNat 2 (Nat.card ↥(Gx ω)) = 1 := by
  let L : Subgroup G := Gxy a ω
  let K : Subgroup G := Gx ω
  have hLK : L ≤ K := by
    intro x hx
    exact (mem_Gxy.mp hx).2
  have haK : a ∈ K := mem_Gx.mpr (mem_Gx.mp hωa).symm
  have haL : a ∈ L := mem_Gxy.mpr ⟨self_mem_Gx a, haK⟩
  have ha_ne_one : a ≠ 1 := by
    intro h1
    have h2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  let aL : ↥L := ⟨a, haL⟩
  have haL_order : orderOf aL = 2 := by
    change orderOf (⟨a, haL⟩ : ↥L) = 2
    rw [Subgroup.orderOf_mk, h.orderOf_a]
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers aL) := by
    change IsPGroup 2 ↥(Subgroup.zpowers (⟨a, haL⟩ : ↥L))
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_a, pow_one]
  obtain ⟨T, hTle⟩ := hzp.exists_le_sylow
  have hLcard : Nat.card ↥L = 22 := by
    simpa only [L] using card_Gxy_eleven hI h hωa hω
  have hpad22 : padicValNat 2 22 = 1 := by
    have hmul : padicValNat 2 22 = padicValNat 2 2 + padicValNat 2 11 := by
      have hh := padicValNat.mul (p := 2) (a := 2) (b := 11) (by norm_num) (by norm_num)
      simpa using hh
    rw [hmul, padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 11)]
  have hTcardS : Nat.card T = 2 := by
    rw [Sylow.card_eq_multiplicity T, Nat.factorization_def (Nat.card ↥L) Nat.prime_two,
      hLcard, hpad22, pow_one]
  have hTcard : Nat.card ↥(T : Subgroup ↥L) = 2 := hTcardS
  have hcard_eq : Nat.card ↥(T : Subgroup ↥L) = Nat.card ↥(Subgroup.zpowers aL) := by
    rw [hTcard, Nat.card_zpowers, haL_order]
  have hTeq' : Subgroup.zpowers aL = (T : Subgroup ↥L) :=
    Subgroup.eq_of_le_of_card_ge hTle (le_of_eq hcard_eq)
  have hTeq : (T : Subgroup ↥L) = Subgroup.zpowers aL := hTeq'.symm
  have hN : ∀ n ∈ K, n ∈ Subgroup.normalizer
      (((T : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) → n ∈ L := by
    intro n hnK hnN
    have hmap : ((T : Subgroup ↥L).map L.subtype : Subgroup G) = Subgroup.zpowers a := by
      rw [hTeq]
      exact (MonoidHom.map_zpowers L.subtype aL).trans rfl
    have hnNa : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
      have hh := (Subgroup.mem_set_normalizer_iff.mp hnN) a
      rw [hmap] at hh
      exact hh.mp (Subgroup.mem_zpowers a)
    have hxeq : n * a * n⁻¹ = a := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnNa
      have hkmod : a ^ (k % 2) = n * a * n⁻¹ := by
        have h' := zpow_mod_orderOf a k
        rw [h.orderOf_a] at h'
        exact h'.trans hk
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        have h1' : n * a * n⁻¹ = 1 := by rw [← hkmod, h0, zpow_zero]
        have ha1 : a = 1 := by
          have hc := congrArg (fun y => n⁻¹ * y * n) h1'
          calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
            _ = n⁻¹ * 1 * n := by rw [hc]
            _ = 1 := by group
        exact ha_ne_one ha1
      · rw [← hkmod, h1, zpow_one]
    change n ∈ Gxy a ω
    rw [mem_Gxy]
    refine ⟨mem_Gx.mpr ?_, hnK⟩
    have hcomm : n * a = a * n := by
      have hc := congrArg (fun y => y * n) hxeq
      simpa [mul_assoc] using hc
    exact hcomm.symm
  have hpadK := padicValNat_card_eq_of_normalizer_le hLK T hN
  show padicValNat 2 (Nat.card ↥K) = 1
  rw [hpadK, hTcard]
  exact padicValNat_self

end CFSG.EvenSporadicStandard.HNRecog.Section3
