module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutAlt8Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutAlt8Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutResidue
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Perm

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.M24Std

theorem not_alt8_of_outerFusion {X : Type} [Group X] [Finite X] {z : X} (hz2 : z * z = 1)
    (hC : Nonempty (centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × Perm (Fin 6)))
    (hF : OuterFusion X z) (e : egaLayer X ≃* alternatingGroup (Fin 8))
    (hz : z ∉ egaLayer X ⊔ centralizer (egaLayer X : Set X)) : False := by
  classical
  obtain ⟨φ⟩ := hC
  let σ : X →* Perm (Fin 8) := permOf e
  have hτ2 : σ z ^ 2 = 1 := by rw [sq, ← map_mul, hz2, map_one]
  have hsign : sign (σ z) = -1 := by
    by_contra hne
    have h1 : sign (σ z) = 1 := by
      rcases Int.units_eq_one_or (sign (σ z)) with h | h
      · exact h
      · exact absurd h hne
    let g : alternatingGroup (Fin 8) := ⟨σ z, mem_alternatingGroup.2 h1⟩
    have haE : ((e.symm g : egaLayer X) : X) ∈ egaLayer X := (e.symm g).2
    have hσa : σ ((e.symm g : egaLayer X) : X) = σ z := by
      have := permOf_of_mem e haE
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply] at this
      exact this
    have hcent : ((e.symm g : egaLayer X) : X)⁻¹ * z ∈ centralizer (egaLayer X : Set X) :=
      mem_centralizer_of_permOf_eq_one e (by
        show σ _ = 1
        rw [map_mul, map_inv, hσa, inv_mul_cancel])
    have hmul := Subgroup.mul_mem_sup haE hcent
    rw [mul_inv_cancel_left] at hmul
    exact hz hmul
  obtain ⟨k, hcyc, hk8, hkcard, hksign⟩ := exists_cycleType_eq_replicate_two hτ2
  rw [Fintype.card_fin] at hk8 hkcard
  have hk13 : k = 1 ∨ k = 3 := by
    have hodd : Odd k := by
      by_contra h
      rw [Nat.not_odd_iff_even] at h
      rw [h.neg_one_pow, hsign] at hksign
      exact absurd hksign (by decide)
    obtain ⟨m, hm⟩ := hodd
    omega
  have hcA := card_alternatingGroup_inf_centralizer_mul_two hτ2 (by simp)
  have hnum : (k = 1 ∧ Nat.card (centralizer ({σ z} : Set (Perm (Fin 8)))) = 1440 ∧
      Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({σ z} : Set (Perm (Fin 8))) :
        Subgroup (Perm (Fin 8))) = 720) ∨
      (k = 3 ∧ Nat.card (centralizer ({σ z} : Set (Perm (Fin 8)))) = 96 ∧
      Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({σ z} : Set (Perm (Fin 8))) :
        Subgroup (Perm (Fin 8))) = 48) := by
    rcases hk13 with rfl | rfl
    · left
      refine ⟨rfl, ?_, ?_⟩ <;> simp [Nat.factorial] at hkcard hcA ⊢ <;> omega
    · right
      refine ⟨rfl, ?_, ?_⟩ <;> simp [Nat.factorial] at hkcard hcA ⊢ <;> omega
  let C : Subgroup X := centralizer ({z} : Set X)
  let σC : C →* Perm (Fin 8) := σ.comp C.subtype
  have hCcard : Nat.card C = 1440 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    have h720 : Nat.card (Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h2, h720]
  have hRle : σC.range ≤ centralizer ({σ z} : Set (Perm (Fin 8))) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc : (c : X) * z = z * c := mem_centralizer_singleton_iff.1 c.2
    show σ c * σ z = σ z * σ c
    rw [← map_mul, ← map_mul, hc]
  have hAle : (alternatingGroup (Fin 8) ⊓ centralizer ({σ z} : Set (Perm (Fin 8))) :
      Subgroup (Perm (Fin 8))) ≤ σC.range := by
    intro π hπ
    obtain ⟨hπA, hπc⟩ := Subgroup.mem_inf.1 hπ
    let g : alternatingGroup (Fin 8) := ⟨π, hπA⟩
    have haE : ((e.symm g : egaLayer X) : X) ∈ egaLayer X := (e.symm g).2
    have hσa : σ ((e.symm g : egaLayer X) : X) = π := by
      have := permOf_of_mem e haE
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply] at this
      exact this
    have hzaE : z * ((e.symm g : egaLayer X) : X) * z⁻¹ ∈ egaLayer X :=
      (egaLayer_normal X).conj_mem _ haE z
    have h3 : σ (z * ((e.symm g : egaLayer X) : X) * z⁻¹) = σ ((e.symm g : egaLayer X) : X) := by
      rw [map_mul, map_mul, map_inv, hσa]
      have := mem_centralizer_singleton_iff.1 hπc
      rw [← this]
      group
    have h4 : e ⟨z * ((e.symm g : egaLayer X) : X) * z⁻¹, hzaE⟩ =
        e ⟨((e.symm g : egaLayer X) : X), haE⟩ :=
      Subtype.ext ((permOf_of_mem e hzaE).symm.trans (h3.trans (permOf_of_mem e haE)))
    have h5 := congrArg Subtype.val (e.injective h4)
    have h6 : ((e.symm g : egaLayer X) : X) * z = z * ((e.symm g : egaLayer X) : X) :=
      ((mul_inv_eq_iff_eq_mul.1 h5).symm)
    exact ⟨⟨((e.symm g : egaLayer X) : X), mem_centralizer_singleton_iff.2 h6⟩, hσa⟩
  let K : Subgroup C := σC.ker
  have hKnormal : K.Normal := MonoidHom.normal_ker σC
  have hKR : Nat.card K * Nat.card σC.range = 1440 := by
    have := K.card_mul_index
    rwa [Subgroup.index_ker, hCcard] at this
  have hRdvd := Subgroup.card_dvd_of_le hRle
  have hAdvd := Subgroup.card_dvd_of_le hAle
  have hKle30 : Nat.card K ≤ 30 := by
    have hR48 : 48 ≤ Nat.card σC.range := by
      have := Nat.le_of_dvd Nat.card_pos hAdvd
      rcases hnum with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
    by_contra h31
    have := Nat.mul_le_mul (not_le.1 h31) hR48
    omega
  let ψ : C →* Perm (Fin 6) := (MonoidHom.snd _ _).comp φ.toMonoidHom
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨c, hc⟩ := φ.surjective (1, s)
    exact ⟨c, by simp [ψ, hc]⟩
  have hNnormal : (K.map ψ).Normal := hKnormal.map ψ hψ
  have hNcard : Nat.card (K.map ψ) ≤ 30 :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd K ψ)).trans hKle30
  have hNbot : K.map ψ = ⊥ := perm_six_eq_bot_of_normal hNnormal hNcard
  have hKψ : ∀ c ∈ K, ψ c = 1 := fun c hc => by
    have : ψ c ∈ K.map ψ := Subgroup.mem_map_of_mem ψ hc
    rwa [hNbot, Subgroup.mem_bot] at this
  rcases hnum with ⟨hk1, -, -⟩ | ⟨-, hS96, -⟩
  · obtain ⟨b, hbmem, hb2, hb1, hconj⟩ := hF
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hbmem
    have hsupp : (σ z).support.card = 2 := by
      rw [← sum_cycleType, hcyc, hk1]
      simp
    obtain ⟨a, a', haa, hτ⟩ := card_support_eq_two.1 hsupp
    have hne : σ (c' : X) ≠ 1 := by
      intro h1
      have h2 := hKψ c' h1
      have h3 : (φ c').1 = 1 :=
        Abelianization.commutator_subset_ker ((MonoidHom.fst _ _).comp φ.toMonoidHom) hc'
      have h4 : φ c' = 1 := Prod.ext h3 h2
      exact hb1 (by rw [(map_eq_one_iff φ φ.injective).1 h4]; rfl)
    let σR : C →* centralizer ({swap a a'} : Set (Perm (Fin 8))) :=
      σC.codRestrict _ (fun c => by
        have := hRle ⟨c, rfl⟩
        rwa [hτ] at this)
    have hfix := fixes_of_swapChar_eq_one haa
      (Abelianization.commutator_subset_ker ((swapChar haa).comp σR) hc')
    have hdisj : Disjoint (σ z) (σ (c' : X)) := by
      intro x
      by_cases hx : x = a ∨ x = a'
      · right
        rcases hx with rfl | rfl
        exacts [hfix.1, hfix.2]
      · left
        rw [hτ]
        exact swap_apply_of_ne_of_ne (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))
    have hconj' : IsConj (σ z) (σ z * σ (c' : X)) := by
      have := MonoidHom.map_isConj σ hconj
      rwa [map_mul] at this
    have hct := isConj_iff_cycleType_eq.1 hconj'
    rw [hdisj.cycleType_mul, hcyc, hk1] at hct
    have h0 : (σ (c' : X)).cycleType = 0 := by simpa using hct
    exact hne (cycleType_eq_zero.1 h0)
  · have hR96 : Nat.card σC.range ≤ 96 := hS96 ▸ Nat.le_of_dvd Nat.card_pos hRdvd
    have hK15 : 15 ≤ Nat.card K := by
      by_contra h
      have := Nat.mul_le_mul (Nat.lt_succ_iff.1 (not_le.1 h)) hR96
      omega
    have hKinj : Function.Injective (fun c : K => (φ c.1).1) := by
      intro c c' h
      refine Subtype.ext (φ.injective (Prod.ext h ?_))
      have h1 := hKψ c.1 c.2
      have h2 := hKψ c'.1 c'.2
      exact h1.trans h2.symm
    have h2card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    have := Nat.card_le_card_of_injective _ hKinj
    omega

end CFSG.EvenSporadicStandard.M22Std
