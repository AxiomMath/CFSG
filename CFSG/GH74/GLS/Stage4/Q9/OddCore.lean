module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem card_oddCore_odd (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have hle : CFSG.oddCore H ≤ CFSG.pPrimeCore 2 H :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : Nat.card (CFSG.oddCore H) ∣ Nat.card (CFSG.pPrimeCore 2 H) :=
    Subgroup.card_dvd_of_le hle
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := H)))

theorem zstar_ambient {G : Type*} [Group G] [Finite G] (A : Subgroup G) {z : G} (hzA : z ∈ A)
    (hz : orderOf z = 2) (S : Subgroup G) (hSA : S ≤ A) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex A) (hzS : z ∈ S) (hzZ : ∀ s ∈ S, s * z = z * s)
    (hwc : ∀ g ∈ A, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z) :
    ∃ O : Subgroup G, O ≤ A ∧ (∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) ∧ Odd (Nat.card O) ∧
      (∀ a ∈ A, ∃ c ∈ A, c * z = z * c ∧ ∃ o ∈ O, a = c * o) ∧
      (∀ N : Subgroup G, N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) → Odd (Nat.card N) →
        N ≤ O) := by
  have hS'p : IsPGroup 2 (S.subgroupOf A) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSA).symm
  let T : Sylow 2 A := hS'p.toSylow hSidx
  have hTmem : ∀ x : A, x ∈ (T : Subgroup A) ↔ (x : G) ∈ S := fun x => Iff.rfl
  let z' : (T : Subgroup A) := ⟨⟨z, hzA⟩, (hTmem _).mpr hzS⟩
  have hzZ' : z' ∈ center (T : Subgroup A) := by
    rw [mem_center_iff]
    intro w
    apply Subtype.ext
    apply Subtype.ext
    exact hzZ _ ((hTmem _).mp w.2)
  have hz' : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe z']
    change orderOf (⟨z, hzA⟩ : A) = 2
    rw [Subgroup.orderOf_mk, hz]
  have hwc' : ∀ g : A, g⁻¹ * (z' : A) * g ∈ (T : Subgroup A) → g⁻¹ * (z' : A) * g = z' := by
    intro g hg
    have h := hwc (g : G)⁻¹ (inv_mem g.2) (by simpa using (hTmem _).mp hg)
    apply Subtype.ext
    simpa using h
  obtain ⟨hfac, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.glauberman_zStar_central_sylow_involution_univ
      T z' hzZ' hz' hwc'
  have hnormal : (CFSG.oddCore A).Normal := inferInstance
  refine ⟨(CFSG.oddCore A).map A.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro a ha o ho
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ho
    exact Subgroup.mem_map.mpr ⟨⟨a, ha⟩ * k * ⟨a, ha⟩⁻¹, hnormal.conj_mem k hk ⟨a, ha⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact card_oddCore_odd A
  · intro a ha
    obtain ⟨c, hc, k, hk, hck⟩ := hfac ⟨a, ha⟩
    refine ⟨c, c.2, ?_, k, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, congrArg Subtype.val hck⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
  · intro N hNA hNnorm hNodd
    have hN'n : (N.subgroupOf A).Normal :=
      ⟨fun n hn g => hNnorm g g.2 n hn⟩
    have hN'odd : Odd (Nat.card (N.subgroupOf A)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv]
    have hle : N.subgroupOf A ≤ CFSG.oddCore A := le_sSup ⟨hN'n, hN'odd⟩
    calc N = (N.subgroupOf A).map A.subtype := (Subgroup.map_subgroupOf_eq_of_le hNA).symm
      _ ≤ (CFSG.oddCore A).map A.subtype := Subgroup.map_mono hle

theorem inverted_of_fixedpointfree {G : Type*} [Group G] [Finite G] {z : G} (hz : z * z = 1)
    (O : Subgroup G) (hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O)
    (hfix : ∀ o ∈ O, z * o * z⁻¹ = o → o = 1) :
    (∀ o ∈ O, z * o * z⁻¹ = o⁻¹) ∧ (∀ a ∈ O, ∀ b ∈ O, a * b = b * a) := by
  have hzz : ∀ o : G, z * (z * o * z⁻¹) * z⁻¹ = o := by
    intro o
    calc z * (z * o * z⁻¹) * z⁻¹ = (z * z) * o * (z * z)⁻¹ := by group
      _ = o := by rw [hz]; group
  have key : ∀ o : G, z * (o⁻¹ * (z * o * z⁻¹)) * z⁻¹ = (o⁻¹ * (z * o * z⁻¹))⁻¹ := by
    intro o
    calc z * (o⁻¹ * (z * o * z⁻¹)) * z⁻¹
        = (z * o⁻¹ * z⁻¹) * (z * (z * o * z⁻¹) * z⁻¹) := by group
      _ = (z * o⁻¹ * z⁻¹) * o := by rw [hzz o]
      _ = (o⁻¹ * (z * o * z⁻¹))⁻¹ := by group
  let f : O → O := fun o => ⟨(o : G)⁻¹ * (z * o * z⁻¹), mul_mem (inv_mem o.2) (hOz o o.2)⟩
  have hinj : Function.Injective f := by
    intro o o' h
    have h' : (o : G)⁻¹ * (z * o * z⁻¹) = (o' : G)⁻¹ * (z * o' * z⁻¹) := congrArg Subtype.val h
    have hx : z * ((o' : G) * (o : G)⁻¹) * z⁻¹ = (o' : G) * (o : G)⁻¹ := by
      calc z * ((o' : G) * (o : G)⁻¹) * z⁻¹
          = (z * o' * z⁻¹) * (z * o * z⁻¹)⁻¹ := by group
        _ = (o' * ((o' : G)⁻¹ * (z * o' * z⁻¹))) * (z * o * z⁻¹)⁻¹ := by group
        _ = (o' * ((o : G)⁻¹ * (z * o * z⁻¹))) * (z * o * z⁻¹)⁻¹ := by rw [h']
        _ = (o' : G) * (o : G)⁻¹ := by group
    have h1 := hfix _ (mul_mem o'.2 (inv_mem o.2)) hx
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  have hinv : ∀ p ∈ O, z * p * z⁻¹ = p⁻¹ := by
    intro p hp
    obtain ⟨o, ho⟩ := hsurj ⟨p, hp⟩
    have ho' : (o : G)⁻¹ * (z * o * z⁻¹) = p := congrArg Subtype.val ho
    rw [← ho']
    exact key o
  refine ⟨hinv, fun a ha b hb => ?_⟩
  have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
    calc a⁻¹ * b⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by rw [hinv a ha, hinv b hb]
      _ = z * (a * b) * z⁻¹ := by group
      _ = (a * b)⁻¹ := hinv _ (mul_mem ha hb)
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
  have h2 := congrArg (fun x => x⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h2
  exact h2.symm

end CFSG.GH74.GLS.Stage4.Q9
