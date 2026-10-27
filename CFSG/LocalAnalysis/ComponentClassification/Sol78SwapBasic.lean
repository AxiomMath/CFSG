module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup
open scoped commutatorElement

theorem nonempty_centralQuot_equiv_of_surjective {A R : Type*} [Group A] [Group R]
    (hA : IsQuasisimple A) (f : A →* R) (hf : Function.Surjective f)
    (hR : ∃ r : R, r ∉ center R) : Nonempty (A ⧸ center A ≃* R ⧸ center R) := by
  have hZ : center A ≤ (center R).comap f := by
    intro a ha
    rw [mem_comap, mem_center_iff]
    intro r
    obtain ⟨b, rfl⟩ := hf r
    rw [← map_mul, ← map_mul, mem_center_iff.mp ha b]
  set g := QuotientGroup.map (center A) (center R) f hZ with hg
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, rfl⟩ := hf r
    exact ⟨a, rfl⟩
  have : IsSimpleGroup (A ⧸ center A) := hA.2.1
  have hgi : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MonoidHom.normal_ker g).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨r, hr⟩ := hR
      obtain ⟨a, rfl⟩ := hf r
      have ha : (a : A ⧸ center A) ∈ g.ker := h ▸ mem_top _
      rw [MonoidHom.mem_ker, hg, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at ha
      exact hr ha
  exact ⟨MulEquiv.ofBijective g ⟨hgi, hgs⟩⟩

variable {X : Type*} [Group X]

theorem mem_coreActionKernel_of_subgroupOf {H M : Subgroup X} (hMH : M ≤ H) {g : H}
    (hg : g ∈ UnbalancedLayer.coreActionKernel (M.subgroupOf H)) :
    (g : X) ∈ UnbalancedLayer.coreActionKernel M := by
  refine ⟨UnbalancedLayer.mem_normalizer_of_subgroupOf hMH hg.1, fun j hj => ?_⟩
  have h := hg.2 ⟨j, hMH hj⟩ hj
  have h' := mem_map_of_mem H.subtype h
  rw [pPrimeCore_map_subgroupOf 2 M H hMH] at h'
  simpa using h'

theorem conj_eq_of_perfect {A : Subgroup X} (hA : ⁅A, A⁆ = A) {g : X}
    (hgA : g ∈ normalizer (A : Set X))
    (hc : ∀ u ∈ A, ∀ v ∈ A, u⁻¹ * (g * u * g⁻¹) * v = v * (u⁻¹ * (g * u * g⁻¹))) :
    ∀ u ∈ A, g * u * g⁻¹ = u := by
  set K : Subgroup X :=
    { carrier := {u | u ∈ A ∧ g * u * g⁻¹ = u}
      one_mem' := ⟨one_mem _, by group⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = a * b := by rw [ha', hb']
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        calc g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [ha'] } with hK
  have hcomm : ⁅A, A⁆ ≤ K := by
    rw [commutator_le]
    intro u hu v hv
    refine ⟨hA ▸ commutator_mem_commutator hu hv, ?_⟩
    set cu := u⁻¹ * (g * u * g⁻¹) with hcu
    set cv := v⁻¹ * (g * v * g⁻¹) with hcv
    have hgu : g * u * g⁻¹ = u * cu := by rw [hcu]; group
    have hgv : g * v * g⁻¹ = v * cv := by rw [hcv]; group
    have hcuA : ∀ w ∈ A, cu * w = w * cu := fun w hw => hc u hu w hw
    have hcvA : ∀ w ∈ A, cv * w = w * cv := fun w hw => hc v hv w hw
    have hcuv : cu * cv = cv * cu := by
      have hcvmem : cv ∈ A := by
        rw [hcv]
        exact mul_mem (inv_mem hv) ((mem_normalizer_iff.mp hgA v).mp hv)
      exact hcuA cv hcvmem
    have hcu' : cu⁻¹ * v = v * cu⁻¹ := by
      have := hcuA v hv
      calc cu⁻¹ * v = cu⁻¹ * (v * cu) * cu⁻¹ := by group
        _ = cu⁻¹ * (cu * v) * cu⁻¹ := by rw [this]
        _ = v * cu⁻¹ := by group
    have hcv' : cv⁻¹ * u = u * cv⁻¹ := by
      have := hcvA u hu
      calc cv⁻¹ * u = cv⁻¹ * (u * cv) * cv⁻¹ := by group
        _ = cv⁻¹ * (cv * u) * cv⁻¹ := by rw [this]
        _ = u * cv⁻¹ := by group
    calc g * ⁅u, v⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * v * g⁻¹⁆ := by
          rw [commutatorElement_def, commutatorElement_def]; group
      _ = ⁅u * cu, v * cv⁆ := by rw [hgu, hgv]
      _ = ⁅u, v⁆ := by
          rw [commutatorElement_def, commutatorElement_def]
          have e1 : u * cu * (v * cv) * (u * cu)⁻¹ * (v * cv)⁻¹ =
              u * (cu * v) * cv * cu⁻¹ * u⁻¹ * cv⁻¹ * v⁻¹ := by group
          rw [e1, hcuA v hv]
          have e2 : u * (v * cu) * cv * cu⁻¹ * u⁻¹ * cv⁻¹ * v⁻¹ =
              u * v * (cu * cv * cu⁻¹) * u⁻¹ * cv⁻¹ * v⁻¹ := by group
          rw [e2, hcuv]
          have e3 : u * v * (cv * cu * cu⁻¹) * u⁻¹ * cv⁻¹ * v⁻¹ =
              u * v * (cv * u⁻¹ * cv⁻¹) * v⁻¹ := by group
          rw [e3]
          have hcvu : cv * u⁻¹ = u⁻¹ * cv := by
            have := hcvA u⁻¹ (inv_mem hu)
            exact this
          rw [hcvu]
          group
  intro u hu
  rw [← hA] at hu
  exact (hcomm hu).2

theorem card_sup_mul_card_inf' [Finite X] {P S : Subgroup X}
    (hPS : P ≤ normalizer (S : Set X)) :
    Nat.card (P ⊔ S : Subgroup X) * Nat.card (P ⊓ S : Subgroup X) = Nat.card P * Nat.card S := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hPS
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPS
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient P S hPS
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf P)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf (P ⊔ S))
  have h3 : Nat.card (S.subgroupOf P) = Nat.card (P ⊓ S : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (S.subgroupOf (P ⊔ S)) = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h3] at h1
  rw [h4] at h2
  rw [h1, h2, Nat.card_congr e.toEquiv]
  ring

end CFSG.ComponentClassification.Sol78
