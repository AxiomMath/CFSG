module

public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.ComponentClassification.AS81.HeEnd

open Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

variable {G : Type} [Group G] {H : Subgroup G}

@[expose] def transportHom (e : ↥H ≃* ↥heP) : ↥H →* Equiv.Perm (Fin 8330) :=
  heP.subtype.comp e.toMonoidHom

theorem transportHom_injective (e : ↥H ≃* ↥heP) : Function.Injective (transportHom e) :=
  heP.subtype_injective.comp e.injective

theorem exists_conj_of_conj (e : ↥H ≃* ↥heP) {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    {c : Equiv.Perm (Fin 8330)} (hc : c ∈ heP)
    (h : ((e ⟨x, hx⟩ : heP) : Equiv.Perm (Fin 8330)) = c * (e ⟨y, hy⟩ : heP) * c⁻¹) :
    ∃ w ∈ H, w * x * w⁻¹ = y := by
  set w : H := e.symm ⟨c, hc⟩ with hw
  refine ⟨((w⁻¹ : H) : G), (w⁻¹ : H).2, ?_⟩
  have h1 : e (w⁻¹ * ⟨x, hx⟩ * w) = e ⟨y, hy⟩ := by
    rw [map_mul, map_mul, map_inv, hw, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [coe_mul, coe_inv]
    rw [h]
    group
  have h2 := congrArg Subtype.val (e.injective h1)
  simpa [mul_assoc] using h2

theorem map_inf_centralizer_eq (e : ↥H ≃* ↥heP) {S : Set G} (hSH : S ⊆ H) :
    ((H ⊓ centralizer S).subgroupOf H).map (transportHom e) =
      heP ⊓ centralizer (transportHom e '' {x : H | (x : G) ∈ S}) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(e x).2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hc := mem_centralizer_iff.mp (mem_inf.mp (mem_subgroupOf.mp hx)).2 _ hs
    rw [← map_mul, ← map_mul]
    exact congrArg (transportHom e) (Subtype.ext hc)
  · rintro ⟨hyP, hyC⟩
    refine ⟨e.symm ⟨y, hyP⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨(e.symm ⟨y, hyP⟩).2, ?_⟩), ?_⟩
    · rw [mem_centralizer_iff]
      intro s hs
      have hc := mem_centralizer_iff.mp hyC (transportHom e ⟨s, hSH hs⟩) ⟨⟨s, hSH hs⟩, hs, rfl⟩
      have hy : transportHom e (e.symm ⟨y, hyP⟩) = y := by
        simp [transportHom]
      rw [← hy, ← map_mul, ← map_mul] at hc
      exact congrArg Subtype.val (transportHom_injective e hc)
    · simp [transportHom]

theorem card_inf_centralizer_eq (e : ↥H ≃* ↥heP) {S : Set G} (hSH : S ⊆ H) :
    Nat.card ↥(H ⊓ centralizer S) =
      Nat.card ↥(heP ⊓ centralizer (transportHom e '' {x : H | (x : G) ∈ S})) := by
  rw [← map_inf_centralizer_eq e hSH, card_map_of_injective (transportHom_injective e),
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]

theorem commutator_inf_centralizer_eq (e : ↥H ≃* ↥heP) {S : Set G} (hSH : S ⊆ H)
    (hp : ⁅heP ⊓ centralizer (transportHom e '' {x : H | (x : G) ∈ S}),
      heP ⊓ centralizer (transportHom e '' {x : H | (x : G) ∈ S})⁆ =
        heP ⊓ centralizer (transportHom e '' {x : H | (x : G) ∈ S})) :
    ⁅H ⊓ centralizer S, H ⊓ centralizer S⁆ = H ⊓ centralizer S := by
  set C := (H ⊓ centralizer S).subgroupOf H with hC
  rw [← map_inf_centralizer_eq e hSH, ← hC, ← map_commutator] at hp
  have hC' : ⁅C, C⁆ = C := map_injective (transportHom_injective e) hp
  have hmap : C.map H.subtype = H ⊓ centralizer S := by
    rw [hC, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  rw [← hmap, ← map_commutator, hC']

theorem mem_conjClass_heA0_of_fixCard {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heP)
    (hs2 : orderOf s = 2) (hf : fixCard s = 346) : s ∈ conjClass heP (heGenPerm 0) := by
  rcases involution_conj_cases hs hs2 with h | ⟨c, -, hc⟩
  · exact h
  · rw [hc, fixCard_conj, fixCard_heT1] at hf
    exact absurd hf (by norm_num)

theorem he_facts (e : ↥H ≃* ↥heP) {z : G} (hzH : z ∈ H)
    (hz : ((e ⟨z, hzH⟩ : heP) : Equiv.Perm (Fin 8330)) ∈ conjClass heP heT1P)
    {R : Subgroup G} (hRH : R ≤ H) (hR1 : R ≠ ⊥)
    (hR : ∀ (r : G) (hr : r ∈ R), r ≠ 1 →
      ((e ⟨r, hRH hr⟩ : heP) : Equiv.Perm (Fin 8330)) ∈ conjClass heP (heGenPerm 0))
    (hRp : ⁅heP ⊓ centralizer (((R.subgroupOf H).map (transportHom e) :
        Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330))),
      heP ⊓ centralizer (((R.subgroupOf H).map (transportHom e) :
        Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330)))⁆ =
      heP ⊓ centralizer (((R.subgroupOf H).map (transportHom e) :
        Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330))))
    (hRc : Nat.card ↥(heP ⊓ centralizer (((R.subgroupOf H).map (transportHom e) :
        Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330)))) = 80640) :
    (∀ u ∈ H, orderOf u = 2 →
      (∃ c ∈ H, c * u * c⁻¹ = z) ∨ ∃ r ∈ R, r ≠ 1 ∧ ∃ c ∈ H, c * u * c⁻¹ = r) ∧
    (∀ r ∈ R, r ≠ 1 → Nat.card ↥(H ⊓ centralizer ({r} : Set G)) = 161280) ∧
    ⁅H ⊓ centralizer (R : Set G), H ⊓ centralizer (R : Set G)⁆ = H ⊓ centralizer (R : Set G) ∧
    Nat.card ↥(H ⊓ centralizer (R : Set G)) = 80640 := by
  have himg : transportHom e '' {x : H | (x : G) ∈ (R : Set G)} =
      (((R.subgroupOf H).map (transportHom e) : Subgroup (Equiv.Perm (Fin 8330))) :
        Set (Equiv.Perm (Fin 8330))) := by
    rw [coe_map]
    rfl
  obtain ⟨⟨r₀, hr₀⟩, hr₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hr₀1' : r₀ ≠ 1 := fun h => hr₀1 (Subtype.ext h)
  refine ⟨fun u hu hu2 => ?_, fun r hr hr1 => ?_, ?_, ?_⟩
  · have hs2 : orderOf ((e ⟨u, hu⟩ : heP) : Equiv.Perm (Fin 8330)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hu2
    rcases involution_conj_cases (e ⟨u, hu⟩).2 hs2 with ⟨c, hc, hce⟩ | ⟨c, hc, hce⟩
    · obtain ⟨d, hd, hde⟩ := hR r₀ hr₀ hr₀1'
      right
      refine ⟨r₀, hr₀, hr₀1', exists_conj_of_conj e hu (hRH hr₀)
        (heP.mul_mem hc (heP.inv_mem hd)) ?_⟩
      rw [hce, hde]
      group
    · obtain ⟨d, hd, hde⟩ := hz
      left
      exact exists_conj_of_conj e hu hzH (heP.mul_mem hc (heP.inv_mem hd))
        (by rw [hce, hde]; group)
  · obtain ⟨d, hd, hde⟩ := hR r hr hr1
    have hS : ({r} : Set G) ⊆ H := Set.singleton_subset_iff.mpr (hRH hr)
    have himg1 : transportHom e '' {x : H | (x : G) ∈ ({r} : Set G)} =
        {((e ⟨r, hRH hr⟩ : heP) : Equiv.Perm (Fin 8330))} := by
      rw [show {x : H | (x : G) ∈ ({r} : Set G)} = {⟨r, hRH hr⟩} by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩, Set.image_singleton]
      rfl
    rw [card_inf_centralizer_eq e hS, himg1, hde,
      Nat.card_congr (infCentralizerConjEquiv hd (heGenPerm 0)).toEquiv]
    exact card_heP_cent0
  · exact commutator_inf_centralizer_eq e hRH (by rw [himg]; exact hRp)
  · rw [card_inf_centralizer_eq e hRH, himg]
    exact hRc

end CFSG.ComponentClassification.AS81.HeEnd
