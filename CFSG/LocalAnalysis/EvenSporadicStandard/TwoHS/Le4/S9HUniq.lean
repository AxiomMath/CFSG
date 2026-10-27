module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HCount

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

namespace ECoord

variable {G : Type*} [Group G]

theorem le_of_abelian_of_mat_mem [Finite G] (C : ECoord G)
    (E' : Subgroup G) (hab : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a) (hcard : 256 ≤ Nat.card E')
    (hnorm : ∀ x ∈ E', x ∈ normalizer (C.E : Set G))
    (hmat : ∀ x ∈ E', C.mat x ∈ shatList)
    (hcent : ∀ x ∈ E', C.mat x = 1 → x ∈ C.E)
    (hSub : ∀ T : Finset M4, (∀ A ∈ T, A ∈ shatList) → (∀ A ∈ T, ∀ B ∈ T, A * B ∈ T) →
      (1 : M4) ∈ T → (∃ A ∈ T, A ≠ 1) →
      T.card * (Finset.univ.filter fun v : V4 => ∀ A ∈ T, A *ᵥ v = v).card < 256) :
    E' ≤ C.E := by
  intro x hx
  by_contra hxE
  have hA1 : C.mat x ≠ 1 := fun h => hxE (hcent x hx h)
  set K : Subgroup G := E' ⊓ centralizer (C.E : Set G)
  have hKE : ∀ e ∈ K, e ∈ C.E := fun e he =>
    hcent e he.1 ((C.mat_eq_one_iff (hnorm e he.1)).2 fun a ha =>
      (mem_centralizer_iff.1 he.2 a ha).symm)
  have hfix : ∀ y ∈ E', ∀ e ∈ K, C.mat y *ᵥ C.vec e = C.vec e := by
    intro y hy e he
    have hconj : y * e * y⁻¹ = e := by
      rw [hab y hy e he.1, mul_inv_cancel_right]
    have := C.vec_conj (hnorm y hy) (hKE e he)
    rw [hconj] at this
    exact this.symm
  have hinj : Set.InjOn C.vec (K : Set G) := fun e he e' he' h => by
    rw [← C.elt_vec (hKE e he), h, C.elt_vec (hKE e' he')]
  have hfac := C.card_inf_centralizer_mul_ncard_image E' hnorm
  set R : Set M4 := C.mat '' (E' : Set G)
  have hRfin : R.Finite := (Set.toFinite _).image _
  set T : Finset M4 := hRfin.toFinset
  have hTR : ∀ A, A ∈ T ↔ A ∈ R := fun A => hRfin.mem_toFinset
  have hTcard : T.card = R.ncard := (Set.ncard_eq_toFinset_card R hRfin).symm
  have hT1 : ∀ A ∈ T, A ∈ shatList := fun A hA => by
    obtain ⟨y, hy, rfl⟩ := (hTR A).1 hA
    exact hmat y hy
  have hT2 : ∀ A ∈ T, ∀ B ∈ T, A * B ∈ T := by
    intro A hA B hB
    obtain ⟨y, hy, rfl⟩ := (hTR A).1 hA
    obtain ⟨z, hz, rfl⟩ := (hTR B).1 hB
    exact (hTR _).2 ⟨y * z, E'.mul_mem hy hz, C.mat_mul (hnorm y hy) (hnorm z hz)⟩
  have hT3 : (1 : M4) ∈ T := (hTR 1).2 ⟨1, E'.one_mem, C.mat_one⟩
  have hT4 : ∃ A ∈ T, A ≠ 1 := ⟨C.mat x, (hTR _).2 ⟨x, hx, rfl⟩, hA1⟩
  have hlt := hSub T hT1 hT2 hT3 hT4
  set F : Finset V4 := Finset.univ.filter fun v : V4 => ∀ A ∈ T, A *ᵥ v = v
  have hKF : Nat.card K ≤ F.card := by
    have h1 : (K : Set G).ncard ≤ (↑F : Set V4).ncard := by
      refine Set.ncard_le_ncard_of_injOn C.vec (fun e he => ?_) hinj (Finset.finite_toSet _)
      simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      intro A hA
      obtain ⟨y, hy, rfl⟩ := (hTR A).1 hA
      exact hfix y hy e he
    rw [Set.ncard_coe_finset] at h1
    rwa [← Nat.card_coe_set_eq] at h1
  have h256 : 256 ≤ T.card * F.card := by
    calc 256 ≤ Nat.card E' := hcard
      _ = Nat.card K * R.ncard := hfac.symm
      _ = R.ncard * Nat.card K := Nat.mul_comm _ _
      _ ≤ T.card * F.card := by rw [hTcard]; exact Nat.mul_le_mul le_rfl hKF
  omega

theorem mem_normalizer_of_conj_le_of_forall [Finite G] (C : ECoord G)
    (S : Subgroup G) (hES : C.E ≤ S)
    (hE : ∀ E' : Subgroup G, E' ≤ S → (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) →
      256 ≤ Nat.card E' → E' ≤ C.E)
    (g : G) (hg : ∀ x, x ∈ S ↔ g * x * g⁻¹ ∈ S) : g ∈ normalizer (C.E : Set G) := by
  set E' : Subgroup G := C.E.map (MulAut.conj g).toMonoidHom with hE'
  have hmemE' : ∀ x, x ∈ E' ↔ ∃ e ∈ C.E, g * e * g⁻¹ = x := fun x => by
    simp [hE', Subgroup.mem_map, MulAut.conj_apply]
  have hE'S : E' ≤ S := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hmemE' x).1 hx
    exact (hg e).1 (hES he)
  have hab : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    obtain ⟨e, he, rfl⟩ := (hmemE' a).1 ha
    obtain ⟨e', he', rfl⟩ := (hmemE' b).1 hb
    calc g * e * g⁻¹ * (g * e' * g⁻¹) = g * (e * e') * g⁻¹ := by group
      _ = g * (e' * e) * g⁻¹ := by rw [C.comm he he']
      _ = g * e' * g⁻¹ * (g * e * g⁻¹) := by group
  have hcardE' : Nat.card E' = 256 := by
    rw [← C.natCard_E]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle : E' ≤ C.E := hE E' hE'S hab hcardE'.ge
  have heq : E' = C.E := Subgroup.eq_of_le_of_card_ge hle (by rw [C.natCard_E, hcardE'])
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hle ((hmemE' _).2 ⟨h, hh, rfl⟩), fun hh => ?_⟩
  rw [← heq] at hh
  obtain ⟨e, he, hee⟩ := (hmemE' _).1 hh
  rwa [← mul_left_cancel (mul_right_cancel hee)]

theorem mem_normalizer_of_conj_le [Finite G] (C : ECoord G)
    (S : Subgroup G) (hES : C.E ≤ S) (hnorm : ∀ x ∈ S, x ∈ normalizer (C.E : Set G))
    (hmat : ∀ x ∈ S, C.mat x ∈ shatList) (hcent : ∀ x ∈ S, C.mat x = 1 → x ∈ C.E)
    (hSub : ∀ T : Finset M4, (∀ A ∈ T, A ∈ shatList) → (∀ A ∈ T, ∀ B ∈ T, A * B ∈ T) →
      (1 : M4) ∈ T → (∃ A ∈ T, A ≠ 1) →
      T.card * (Finset.univ.filter fun v : V4 => ∀ A ∈ T, A *ᵥ v = v).card < 256)
    (g : G) (hg : ∀ x, x ∈ S ↔ g * x * g⁻¹ ∈ S) : g ∈ normalizer (C.E : Set G) :=
  C.mem_normalizer_of_conj_le_of_forall S hES
    (fun E' hE'S hab hcard => C.le_of_abelian_of_mat_mem E' hab hcard
      (fun x hx => hnorm x (hE'S hx)) (fun x hx => hmat x (hE'S hx))
      (fun x hx => hcent x (hE'S hx)) hSub) g hg

end ECoord

end CFSG.EvenSporadicStandard.TwoHS
