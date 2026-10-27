module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4RedB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace Vtx

variable {G : Type} [Group G]

@[expose] def StarRel (H K A B : Subgroup G) : Prop :=
  (∃ h ∈ H, A = conjSub h K) ∧ (∃ h ∈ H, B = conjSub h K) ∧ A ≠ B ∧
    ((∃ u ∈ B, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (A : Set G)) ∨
      (∃ u ∈ A, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (B : Set G)))

variable {M : Type} [Group M] [Finite M]

theorem e4QuatGraphFacts_at (φ : M →* G) (hφ : Function.Injective φ) (Kc : Subgroup G)
    (tw : List (Subgroup G)) (htw : tw.length ≤ 3) {K : Subgroup M} {s : M}
    (hd : QuatTwinDatum K s) (hKc : K.map φ = Kc)
    (hE : ∃ m : M, conjSub (φ m) Kc ≠ Kc ∧
      conjSub (φ m) Kc ≤ Subgroup.normalizer (Kc : Set G))
    (hD : ∀ m : M, Relation.ReflTransGen (StarRel φ.range Kc) Kc (conjSub (φ m) Kc))
    (hC : ∀ m : M, conjSub (φ m) Kc ≠ Kc →
      conjSub (φ m) Kc ≤ Subgroup.normalizer (Kc : Set G) → conjSub (φ m) Kc ∈ tw) :
    (∃ J ∈ CoreAssembly.conjClass K, J ∈ omegaNbr (CoreAssembly.conjClass K) K) ∧
      T3.DStarConnected (CoreAssembly.conjClass K) ∧
      ∀ B : Fin 5 → Subgroup M, (∀ i, B i ∈ CoreAssembly.conjClass K) → Function.Injective B →
        ¬ ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass K) (B i) := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : M, conjSub (φ m₀) (K.map φ) = Kc :=
    ⟨1, by rw [map_one, conjSub_one, hKc]⟩
  obtain ⟨eK⟩ := hd.q8
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  set K' := conjSub m₀ K with hK'
  have hK'map : K'.map φ = Kc := by rw [hK', ← conjSub_map, hm₀]
  have hmapc : ∀ m : M, (conjSub m K').map φ = conjSub (φ m) Kc := by
    intro m
    rw [← conjSub_map, hK'map]
  have hcl : ∀ J, J ∈ CoreAssembly.conjClass K ↔ ∃ m, J = conjSub m K' := by
    intro J
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨g * m₀⁻¹, ?_⟩
      show conjSub g K = conjSub (g * m₀⁻¹) K'
      rw [hK', ← conjSub_mul, inv_mul_cancel_right]
    · rintro ⟨m, rfl⟩
      refine ⟨m * m₀, ?_⟩
      show conjSub (m * m₀) K = conjSub m K'
      rw [hK', conjSub_mul]
  have hmem : ∀ m, conjSub m K' ∈ CoreAssembly.conjClass K := fun m => (hcl _).mpr ⟨m, rfl⟩
  have hK'mem : K' ∈ CoreAssembly.conjClass K := (hcl _).mpr ⟨1, (conjSub_one K').symm⟩
  have hK : K = conjSub m₀⁻¹ K' := by rw [hK', conjSub_inv_conjSub]
  have hne_of : ∀ m₁ m₂ : M, conjSub (φ m₁) Kc ≠ conjSub (φ m₂) Kc →
      conjSub m₁ K' ≠ conjSub m₂ K' := fun m₁ m₂ h e => h (by rw [← hmapc, ← hmapc, e])
  have hu_of : ∀ m₁ m₂ : M, (∃ u ∈ conjSub (φ m₁) Kc, orderOf u = 4 ∧
      u ∈ Subgroup.normalizer ((conjSub (φ m₂) Kc : Subgroup G) : Set G)) →
      ∃ v ∈ conjSub m₁ K', orderOf v = 4 ∧
        v ∈ Subgroup.normalizer ((conjSub m₂ K' : Subgroup M) : Set M) := by
    rintro m₁ m₂ ⟨u, hu, hu4, huN⟩
    rw [← hmapc] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [← hmapc, mem_normalizer_map_iff φ hφ] at huN
    exact ⟨v, hv, by rwa [orderOf_injective φ hφ] at hu4, huN⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨m, hne, hle⟩ := hE
    have hne' : conjSub m K' ≠ K' := fun e =>
      hne (by rw [← hmapc, e, hK'map])
    have hle' : conjSub m K' ≤ Subgroup.normalizer (K' : Set M) := by
      rw [← map_le_normalizer_map_iff φ hφ, hmapc, hK'map]
      exact hle
    refine ⟨conjSub m₀⁻¹ (conjSub m K'), by rw [← conjSub_mul]; exact hmem _,
      (mem_omegaNbr_conjClass_iff h2).mpr ⟨by rw [← conjSub_mul]; exact hmem _, ?_, ?_⟩⟩
    · rw [hK]
      exact fun e => hne' (conjSub_injective _ e)
    · rw [hK]
      exact conjSub_le_normalizer hle' m₀⁻¹
  ·
    have hpath : ∀ m : M, Relation.ReflTransGen
        (dstarAdj (CoreAssembly.conjClass K)) K' (conjSub m K') := by
      have key : ∀ B, Relation.ReflTransGen (StarRel φ.range Kc) Kc B → ∀ m : M,
          B = conjSub (φ m) Kc →
            Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass K)) K' (conjSub m K') := by
        intro B hB
        induction hB with
        | refl =>
          intro m hm
          have he : conjSub m K' = K' :=
            Subgroup.map_injective hφ (by rw [hmapc, hK'map, ← hm])
          rw [he]
        | tail _ hstep ih =>
          intro m hm
          obtain ⟨⟨_, ⟨m', rfl⟩, hA⟩, -, hne, hu⟩ := hstep
          refine (ih m' hA).tail ⟨hmem m, ?_⟩
          rw [hA, hm] at hne
          rw [hA, hm] at hu
          rcases hu with hu | hu
          · exact Or.inl ((mem_omegaStarNbr_conjClass_iff h2 h8).mpr
              ⟨hmem m, fun e => hne_of m' m hne e.symm, hu_of m m' hu⟩)
          · exact Or.inr ((mem_omegaStarNbr_conjClass_iff h2 h8).mpr
              ⟨hmem m', hne_of m' m hne, hu_of m' m hu⟩)
      exact fun m => key _ (hD m) m rfl
    have hrev : ∀ X, Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass K)) K' X →
        X ∈ CoreAssembly.conjClass K ∧
          Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass K)) X K' := by
      intro X hX
      induction hX with
      | refl => exact ⟨hK'mem, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        exact ⟨hstep.1, Relation.ReflTransGen.head ⟨ih.1, hstep.2.symm⟩ ih.2⟩
    intro A hA B hB
    obtain ⟨m₁, rfl⟩ := (hcl A).mp hA
    obtain ⟨m₂, rfl⟩ := (hcl B).mp hB
    exact ((hrev _ (hpath m₁)).2).trans (hpath m₂)
  ·
    classical
    intro B hB hinj hadj
    obtain ⟨m, hm⟩ := (hcl _).mp (hB 0)
    have hB'0 : conjSub m⁻¹ (B 0) = K' := by rw [hm, conjSub_inv_conjSub]
    have hB'mem : ∀ i, ∃ mi, conjSub m⁻¹ (B i) = conjSub mi K' := fun i => by
      obtain ⟨mi, hmi⟩ := (hcl _).mp (hB i)
      exact ⟨m⁻¹ * mi, by rw [hmi, conjSub_mul]⟩
    have hin : ∀ i : Fin 4, (conjSub m⁻¹ (B i.succ)).map φ ∈ tw := by
      intro i
      have h1 := (mem_omegaNbr_conjClass_iff h2).mp (hadj 0 i.succ (Fin.succ_ne_zero i).symm)
      have hne : conjSub m⁻¹ (B i.succ) ≠ K' := by
        rw [← hB'0]
        exact fun e => h1.2.1 (conjSub_injective _ e)
      have hle : conjSub m⁻¹ (B i.succ) ≤ Subgroup.normalizer (K' : Set M) := by
        rw [← hB'0]
        exact conjSub_le_normalizer h1.2.2 m⁻¹
      obtain ⟨mi, hmi⟩ := hB'mem i.succ
      rw [hmi] at hne hle ⊢
      rw [hmapc]
      refine hC mi (fun e => hne (Subgroup.map_injective hφ (by rw [hmapc, hK'map, e]))) ?_
      have h3 := (map_le_normalizer_map_iff φ hφ).mpr hle
      rwa [hmapc, hK'map] at h3
    have hinj' : Function.Injective fun i : Fin 4 => (conjSub m⁻¹ (B i.succ)).map φ := by
      intro i j hij
      exact Fin.succ_injective _ (hinj (conjSub_injective _ (Subgroup.map_injective hφ hij)))
    have hsub : (Finset.univ.image fun i : Fin 4 => (conjSub m⁻¹ (B i.succ)).map φ) ⊆
        tw.toFinset := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact List.mem_toFinset.mpr (hin i)
    have h4 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj', Finset.card_univ, Fintype.card_fin] at h4
    have h5 := List.toFinset_card_le tw
    omega

theorem e4QuatGraphFacts_of_model (H : Subgroup G) (Kc : Subgroup G) (tw : List (Subgroup G))
    (htw : tw.length ≤ 3)
    (hid : ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (hE : ∃ h ∈ H, conjSub h Kc ≠ Kc ∧ conjSub h Kc ≤ Subgroup.normalizer (Kc : Set G))
    (hD : ∀ h ∈ H, Relation.ReflTransGen (StarRel H Kc) Kc (conjSub h Kc))
    (hC : ∀ h ∈ H, conjSub h Kc ≠ Kc → conjSub h Kc ≤ Subgroup.normalizer (Kc : Set G) →
      conjSub h Kc ∈ tw) :
    E4QuatGraphFacts M := by
  intro K s hd
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hd
  have hmem : ∀ m : M, φ m ∈ H := fun m => hrange ▸ ⟨m, rfl⟩
  refine e4QuatGraphFacts_at φ hφ Kc tw htw hd hKc ?_ (fun m => ?_)
    (fun m hne hle => hC _ (hmem m) hne hle)
  · obtain ⟨h, hh, hne, hle⟩ := hE
    rw [← hrange] at hh
    obtain ⟨m, rfl⟩ := hh
    exact ⟨m, hne, hle⟩
  · rw [hrange]
    exact hD _ (hmem m)

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
