module

public import CFSG.GH74.Uniqueness.SU.SU13TA9NPerm

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup

@[expose] def NE : Subgroup (alternatingGroup (Fin 9)) :=
  normalizer (Ebar : Set (alternatingGroup (Fin 9)))

theorem toE_eq (i j k : Fin 3) :
    toE i j k = ea ^ (i : ℕ) * eb ^ (j : ℕ) * ec ^ (k : ℕ) :=
  Subtype.ext (by simp [toE, toP, Subgroup.coe_mul, coe_ea, coe_eb, coe_ec])

theorem mem_NE_of_conj {σ : alternatingGroup (Fin 9)} (ha : σ * ea * σ⁻¹ ∈ Ebar)
    (hb : σ * eb * σ⁻¹ ∈ Ebar) (hc : σ * ec * σ⁻¹ ∈ Ebar) : σ ∈ NE := by
  refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp (show n ∈ Ebar from hn)
  rw [toE_eq]
  have : σ * (ea ^ (i : ℕ) * eb ^ (j : ℕ) * ec ^ (k : ℕ)) * σ⁻¹ =
      (σ * ea * σ⁻¹) ^ (i : ℕ) * (σ * eb * σ⁻¹) ^ (j : ℕ) * (σ * ec * σ⁻¹) ^ (k : ℕ) := by
    rw [conj_pow, conj_pow, conj_pow]
    group
  rw [SetLike.mem_coe, this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha _) (Subgroup.pow_mem _ hb _))
    (Subgroup.pow_mem _ hc _)

theorem conj_mem_Ebar_of_mem_NE {σ x : alternatingGroup (Fin 9)} (hσ : σ ∈ NE) (hx : x ∈ Ebar) :
    σ * x * σ⁻¹ ∈ Ebar :=
  ((Subgroup.mem_normalizer_iff.mp hσ x).mp hx)

theorem Ebar_le_NE : Ebar ≤ NE := fun _ hx =>
  mem_NE_of_conj (Ebar.mul_mem (Ebar.mul_mem hx ea_mem_Ebar) (Ebar.inv_mem hx))
    (Ebar.mul_mem (Ebar.mul_mem hx eb_mem_Ebar) (Ebar.inv_mem hx))
    (Ebar.mul_mem (Ebar.mul_mem hx ec_mem_Ebar) (Ebar.inv_mem hx))

theorem exists_decomp_NE {σ : alternatingGroup (Fin 9)} (hσ : σ ∈ NE) :
    ∃ l₁ ∈ Gam, ∃ l₂ ∈ Lam2, ∃ l₃ ∈ Lam3, ∃ i j k : Fin 3,
      (σ : Perm (Fin 9)) = l₁ * l₂ * l₃ * toP i j k := by
  have key : ∀ x ∈ ({ea, eb, ec} : Set (alternatingGroup (Fin 9))),
      InE ((σ : Perm (Fin 9)) * (x : Perm (Fin 9)) * (σ : Perm (Fin 9))⁻¹) := by
    intro x hx
    obtain ⟨i, j, k, hijk⟩ := mem_Ebar_iff_toE.mp (conj_mem_Ebar_of_mem_NE hσ (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ea_mem_Ebar
      · exact eb_mem_Ebar
      · exact ec_mem_Ebar : x ∈ Ebar))
    exact ⟨i, j, k, congrArg Subtype.val hijk⟩
  exact exists_decomp (key ea (by simp)) (key eb (by simp)) (key ec (by simp))

@[expose] def LL : List (Perm (Fin 9)) :=
  Gam.flatMap (fun a => Lam2.flatMap (fun b => Lam3.map (fun c => a * b * c)))

theorem length_LL_even : (LL.filter (fun l => decide (Perm.sign l = 1))).length = 24 := by decide

theorem mul_mem_LL {a b c : Perm (Fin 9)} (ha : a ∈ Gam) (hb : b ∈ Lam2) (hc : c ∈ Lam3) :
    a * b * c ∈ LL := by
  simp only [LL, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

theorem exists_even_LL {σ : alternatingGroup (Fin 9)} (hσ : σ ∈ NE) :
    ∃ l ∈ LL.filter (fun l => decide (Perm.sign l = 1)), ∃ i j k : Fin 3,
      (σ : Perm (Fin 9)) = l * toP i j k := by
  obtain ⟨l₁, hl₁, l₂, hl₂, l₃, hl₃, i, j, k, h⟩ := exists_decomp_NE hσ
  have hsign : Perm.sign (l₁ * l₂ * l₃) = 1 := by
    have h1 : Perm.sign (σ : Perm (Fin 9)) = 1 := Perm.mem_alternatingGroup.mp σ.2
    rw [h, map_mul, sign_toP, mul_one] at h1
    exact h1
  refine ⟨l₁ * l₂ * l₃, ?_, i, j, k, h⟩
  rw [List.mem_filter]
  exact ⟨mul_mem_LL hl₁ hl₂ hl₃, by simpa using hsign⟩

theorem card_NE_le : Nat.card NE ≤ 648 := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Perm (Fin 9)), S =
      (LL.filter (fun l => decide (Perm.sign l = 1))).toFinset.biUnion (fun l =>
        (Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3)).image
          (fun p => l * toP p.1 p.2.1 p.2.2)) := ⟨_, rfl⟩
  have hS : S.card ≤ 648 := by
    rw [hSdef]
    calc _ ≤ ∑ l ∈ (LL.filter (fun l => decide (Perm.sign l = 1))).toFinset,
          ((Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3)).image
          (fun p => l * toP p.1 p.2.1 p.2.2)).card := Finset.card_biUnion_le
      _ ≤ ∑ _l ∈ (LL.filter (fun l => decide (Perm.sign l = 1))).toFinset, 27 :=
          Finset.sum_le_sum (fun l _ => Finset.card_image_le.trans (by simp))
      _ = (LL.filter (fun l => decide (Perm.sign l = 1))).toFinset.card * 27 := by
          simp [Finset.sum_const]
      _ ≤ 24 * 27 := by
          apply Nat.mul_le_mul_right
          calc (LL.filter (fun l => decide (Perm.sign l = 1))).toFinset.card
              ≤ (LL.filter (fun l => decide (Perm.sign l = 1))).length := List.toFinset_card_le _
            _ = 24 := length_LL_even
      _ = 648 := by norm_num
  have hsub : ∀ σ : NE, ((σ : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ S := by
    intro σ
    obtain ⟨l, hl, i, j, k, h⟩ := exists_even_LL σ.2
    rw [hSdef, Finset.mem_biUnion]
    refine ⟨l, List.mem_toFinset.mpr hl, ?_⟩
    rw [Finset.mem_image]
    exact ⟨(i, j, k), Finset.mem_univ _, h.symm⟩
  have hinj : Function.Injective (fun σ : NE => (⟨((σ : alternatingGroup (Fin 9)) : Perm (Fin 9)),
      hsub σ⟩ : S)) := fun σ τ h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card NE ≤ Nat.card S := Nat.card_le_card_of_injective _ hinj
    _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 648 := hS

theorem Pst_le_NE : Pst ≤ NE := by
  have hrel : Ebar.relIndex Pst = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Ebar) (K := Pst)
    rw [inf_of_le_left Ebar_le_Pst, card_Ebar, card_Pst] at h
    omega
  have hN : (Ebar.subgroupOf Pst).Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    show Ebar.relIndex Pst = (Nat.card Pst).minFac
    rw [hrel, card_Pst]
    norm_num
  intro σ hσ
  refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
  have hn' : n ∈ Ebar := hn
  have := hN.conj_mem ⟨n, Ebar_le_Pst hn'⟩ (Subgroup.mem_subgroupOf.mpr hn') ⟨σ, hσ⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem mem_NE_of_InE {σ : alternatingGroup (Fin 9)}
    (ha : InE ((σ : Perm (Fin 9)) * pa * (σ : Perm (Fin 9))⁻¹))
    (hb : InE ((σ : Perm (Fin 9)) * pb * (σ : Perm (Fin 9))⁻¹))
    (hc : InE ((σ : Perm (Fin 9)) * pc * (σ : Perm (Fin 9))⁻¹)) : σ ∈ NE := by
  have key : ∀ (x : alternatingGroup (Fin 9)),
      InE ((σ : Perm (Fin 9)) * (x : Perm (Fin 9)) * (σ : Perm (Fin 9))⁻¹) →
        σ * x * σ⁻¹ ∈ Ebar := by
    intro x ⟨i, j, k, h⟩
    have : σ * x * σ⁻¹ = toE i j k := Subtype.ext h
    rw [this]
    exact mem_Ebar_iff_toE.mpr ⟨i, j, k, rfl⟩
  exact mem_NE_of_conj (key ea ha) (key eb hb) (key ec hc)

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
