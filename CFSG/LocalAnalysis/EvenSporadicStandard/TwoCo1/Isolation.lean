module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Facts
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open

variable {G : Type*} [Group G] {L : Subgroup G} {z : G} {c₂ c₃ : ℕ}

theorem eq_one_or_eq_of_mem_zpowers (hz : z ^ 2 = 1) {a : G} (ha : a ∈ zpowers z) :
    a = 1 ∨ a = z := by
  obtain ⟨k, hk⟩ := ha
  have hk' : a = z ^ k := hk.symm
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [hk', ← two_mul, zpow_mul]
    simp [hz]
  · right
    rw [hk', zpow_add, zpow_one, zpow_mul]
    simp [hz]

theorem conj_inv_mem (hCz : centralizer ({z} : Set G) = L) {g : G} (ht : g * z * g⁻¹ ∈ L) :
    g⁻¹ * z * g ∈ L := by
  rw [← hCz, mem_centralizer_singleton_iff] at ht
  rw [← hCz, mem_centralizer_singleton_iff]
  have h : Commute z (g * z * g⁻¹) := ht.symm
  have h2 : Commute (g⁻¹ * z * g) z := by
    have := Commute.map h (MulAut.conj g⁻¹)
    simpa [MulAut.conj_apply, mul_assoc] using this
  exact h2.eq

theorem not_hasEighthRoot_conj (hno8 : ∀ v ∈ L, v ^ 8 ≠ z)
    (hCz : centralizer ({z} : Set G) = L) (g : G) : ¬ HasEighthRoot L (g * z * g⁻¹) := by
  rintro ⟨v, -, hv⟩
  have h8 : (g⁻¹ * v * g) ^ 8 = z := by
    have := conj_pow (a := g⁻¹) (b := v) (i := 8)
    rw [inv_inv] at this
    rw [this, hv]
    group
  have hmem : g⁻¹ * v * g ∈ L := by
    rw [← hCz, mem_centralizer_singleton_iff, ← h8]
    exact ((Commute.refl _).pow_left 8).eq.symm
  exact hno8 _ hmem h8

theorem centIn_map_conj (hCz : centralizer ({z} : Set G) = L) {g t : G} (ht : t = g * z * g⁻¹) :
    (centIn L t).map (MulAut.conj g⁻¹).toMonoidHom = centIn L (g⁻¹ * z * g) := by
  have hψt : (MulAut.conj g⁻¹) t = z := by
    rw [MulAut.conj_apply, ht]
    group
  have hψz : (MulAut.conj g⁻¹) z = g⁻¹ * z * g := by
    rw [MulAut.conj_apply]
    group
  rw [centIn, Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    map_centralizer_singleton, hψt, hCz, ← hCz, map_centralizer_singleton, hψz, inf_comm]

theorem invType_conj {c : ℕ} (hno8 : ∀ v ∈ L, v ^ 8 ≠ z) (hz2 : orderOf z = 2)
    (hCz : centralizer ({z} : Set G) = L) {g t : G} (ht : t = g * z * g⁻¹)
    (hty : InvType L z c t) : InvType L z c (g⁻¹ * z * g) := by
  obtain ⟨htL, -, htz, -, htc⟩ := hty
  have hcard : Nat.card (centIn L (g⁻¹ * z * g)) = c := by
    rw [← centIn_map_conj hCz ht, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact htc
  refine ⟨conj_inv_mem hCz (ht ▸ htL), ?_, ?_, ?_, hcard⟩
  · have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective z
    rw [hz2] at this
    simpa [MulAut.conj_apply, mul_assoc] using this
  · intro h
    apply htz
    rw [ht]
    have h1 : g * z = z * g := by
      calc g * z = g * (g⁻¹ * z * g) := by rw [h]
        _ = z * g := by group
    rw [h1, mul_inv_cancel_right]
  · have := not_hasEighthRoot_conj hno8 hCz g⁻¹
    simpa using this

theorem Co0Facts.invType_three_of_fused (F : Co0Facts L z c₂ c₃)
    (hno8 : ∀ v ∈ L, v ^ 8 ≠ z) (hz2 : orderOf z = 2) (hCz : centralizer ({z} : Set G) = L)
    (hD : ∀ g : G, ¬ InvType L z c₂ (g * z * g⁻¹))
    {g t : G} (ht : t = g * z * g⁻¹) (htL : t ∈ L) (htz : t ≠ z) : InvType L z c₃ t := by
  have hord : orderOf t = 2 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    rw [hz2] at this
    rw [ht]
    simpa [MulAut.conj_apply] using this
  have hnr : ¬ HasEighthRoot L t := by
    rw [ht]
    exact not_hasEighthRoot_conj hno8 hCz g
  rcases F.classify t htL hord htz with hc | hc
  · exact (hD g (ht ▸ ⟨htL, hord, htz, hnr, hc⟩)).elim
  · exact ⟨htL, hord, htz, hnr, hc⟩

theorem centIn_map_conj_of_mem {h : G} (hh : h ∈ L) (y : G) :
    (centIn L y).map (MulAut.conj h).toMonoidHom = centIn L (h * y * h⁻¹) := by
  have hL : L.map (MulAut.conj h).toMonoidHom = L := by
    ext a
    rw [mem_map_conj]
    exact ⟨fun h' => by simpa [mul_assoc] using L.mul_mem (L.mul_mem hh h') (L.inv_mem hh),
      fun h' => L.mul_mem (L.mul_mem (L.inv_mem hh) h') hh⟩
  rw [centIn, Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hL, map_centralizer_singleton]
  rfl

variable [Finite G]

theorem Co0Facts.false_of_typeC (F : Co0Facts L z c₂ c₃) (hno8 : ∀ v ∈ L, v ^ 8 ≠ z)
    (hconj : ∀ y y', InvType L z c₃ y → InvType L z c₃ y' → ∃ h ∈ L, h * y' * h⁻¹ = y)
    (hz2 : orderOf z = 2) (hCz : centralizer ({z} : Set G) = L)
    (hD : ∀ g : G, ¬ InvType L z c₂ (g * z * g⁻¹)) {g t : G} (ht : t = g * z * g⁻¹)
    (hC : InvType L z c₃ t) : False := by
  obtain ⟨hzE, hEL, hcomm, hsq, hcardE, hcentE⟩ := F.pCore_typeC t hC
  obtain ⟨hcardS, htrans⟩ := F.orbit_typeC t hC
  generalize hE : pCoreOf 2 (centIn L t) = E at hzE hEL hcomm hsq hcardE hcentE hcardS htrans
  have hC' := invType_conj hno8 hz2 hCz ht hC
  obtain ⟨h, hhL, hh⟩ := hconj t _ hC hC'
  have hEmap : E = ((E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj h).toMonoidHom) := by
    have h1 : centIn L t = (centIn L (g⁻¹ * z * g)).map (MulAut.conj h).toMonoidHom := by
      rw [centIn_map_conj_of_mem hhL, hh]
    have h2 := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj h)
      (centIn L (g⁻¹ * z * g))
    have h3 := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g⁻¹) (centIn L t)
    rw [centIn_map_conj hCz ht] at h3
    have h4 : pCoreOf 2 (centIn L t) =
        ((pCoreOf 2 (centIn L t)).map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj h).toMonoidHom := by
      calc pCoreOf 2 (centIn L t)
          = pCoreOf 2 ((centIn L (g⁻¹ * z * g)).map (MulAut.conj h).toMonoidHom) := by rw [← h1]
        _ = (pCoreOf 2 (centIn L (g⁻¹ * z * g))).map (MulAut.conj h).toMonoidHom := h2
        _ = _ := by rw [h3]
    rwa [hE] at h4
  have hnorm : g * h⁻¹ ∈ normalizer (E : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    have : a ∈ E ↔ a ∈ ((E.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj h).toMonoidHom) := by
      constructor
      · intro ha
        rwa [← hEmap]
      · intro ha
        rwa [← hEmap] at ha
    rw [this, mem_map_conj, mem_map_conj]
    simp only [inv_inv, mul_inv_rev, mul_assoc]
  have hcomm' : h⁻¹ * z = z * h⁻¹ := by
    exact mem_centralizer_singleton_iff.1 (hCz ▸ L.inv_mem hhL)
  have hz_conj : g * h⁻¹ * z * (g * h⁻¹)⁻¹ = t := by
    rw [ht]
    calc g * h⁻¹ * z * (g * h⁻¹)⁻¹ = g * (h⁻¹ * z) * h * g⁻¹ := by group
      _ = g * (z * h⁻¹) * h * g⁻¹ := by rw [hcomm']
      _ = g * z * g⁻¹ := by group
  let N : Subgroup G := normalizer (E : Set G)
  have hΔeq : {s : G | ∃ n ∈ N, s = n * z * n⁻¹} =
      insert z {s : G | s ∈ E ∧ InvType L z c₃ s} := by
    ext s
    constructor
    · rintro ⟨n, hn, rfl⟩
      by_cases hsz : n * z * n⁻¹ = z
      · exact Or.inl hsz
      · have hsE : n * z * n⁻¹ ∈ E := (mem_normalizer_iff.1 hn z).1 hzE
        exact Or.inr ⟨hsE, F.invType_three_of_fused hno8 hz2 hCz hD rfl (hEL hsE) hsz⟩
    · rintro (rfl | ⟨hsE, hsT⟩)
      · exact ⟨1, one_mem _, by simp⟩
      · obtain ⟨n, hn, hns⟩ := htrans s hsE hsT
        refine ⟨n * (g * h⁻¹), mul_mem (Subgroup.mem_inf.1 hn).2 hnorm, ?_⟩
        rw [← hns, ← hz_conj]
        group
  have hzS : z ∉ {s : G | s ∈ E ∧ InvType L z c₃ s} := fun hz => hz.2.2.2.1 rfl
  have hcardΔ : Nat.card {s : G | ∃ n ∈ N, s = n * z * n⁻¹} = 2577 := by
    rw [hΔeq, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hzS (Set.toFinite _),
      ← Nat.card_coe_set_eq, hcardS]
  have hcent : centralizer (E : Set G) ≤ E := fun a ha => by
    have haL : a ∈ L := by
      rw [← hCz]
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ha z hzE).symm
    exact hcentE ⟨haL, ha⟩
  have h1 := card_conjOrbit_dvd N z
  have h2 := card_normalizer_dvd hcomm hsq hcardE hcent
  rw [hcardΔ] at h1
  exact not_dvd_859_card ((by norm_num : 859 ∣ 2577).trans (h1.trans h2))

theorem Co0Facts.false_of_fused (F : Co0Facts L z c₂ c₃) (hno8 : ∀ v ∈ L, v ^ 8 ≠ z)
    (hconj : ∀ y y', InvType L z c₃ y → InvType L z c₃ y' → ∃ h ∈ L, h * y' * h⁻¹ = y)
    (hD : ∀ g : G, ¬ InvType L z c₂ (g * z * g⁻¹))
    (hz2 : orderOf z = 2) (hCz : centralizer ({z} : Set G) = L) {g : G} (hne : g * z * g⁻¹ ≠ z)
    (hcomm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) : False := by
  have htL : g * z * g⁻¹ ∈ L := by
    rw [← hCz, mem_centralizer_singleton_iff]
    exact hcomm
  exact F.false_of_typeC hno8 hconj hz2 hCz hD rfl
    (F.invType_three_of_fused hno8 hz2 hCz hD rfl htL hne)

end CFSG.EvenSporadicStandard.TwoCo1
