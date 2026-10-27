module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Parabolic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem miyamotoPull_gramSU : miyamotoPull h L η (gramSU h (miyamotoJ4 K)) = L := by
  refine le_antisymm (miyamotoPull_le h L η _) fun x hx => ?_
  refine (mem_miyamotoPull h L η).2 ⟨η ⟨x, hx⟩, (η ⟨x, hx⟩).2, ?_⟩
  rw [MulEquiv.symm_apply_apply]

theorem miyamotoPull_sup {M N : Subgroup (GL (Fin 4) K)} (hM : M ≤ gramSU h (miyamotoJ4 K))
    (hN : N ≤ gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η (M ⊔ N) = miyamotoPull h L η M ⊔ miyamotoPull h L η N := by
  simp only [miyamotoPull]
  rw [subgroupOf_sup hM hN, Subgroup.map_sup, Subgroup.map_sup]

theorem miyamotoPull_bot : miyamotoPull h L η ⊥ = ⊥ := by
  simp [miyamotoPull]

theorem coe_symm_conj (g k : gramSU h (miyamotoJ4 K)) :
    ((η.symm (g * k * g⁻¹) : L) : G) =
      ((η.symm g : L) : G) * ((η.symm k : L) : G) * ((η.symm g : L) : G)⁻¹ := by
  simp only [map_mul, map_inv, coe_mul, coe_inv]

theorem miyamotoPull_inf_normalizer {M : Subgroup (GL (Fin 4) K)}
    (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η (gramSU h (miyamotoJ4 K) ⊓ normalizer (M : Set (GL (Fin 4) K))) =
      L ⊓ normalizer (miyamotoPull h L η M : Set G) := by
  ext x
  rw [mem_inf, mem_miyamotoPull]
  constructor
  · rintro ⟨g, ⟨-, hgN⟩, rfl⟩
    refine ⟨(η.symm g).2, mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
      rw [← coe_symm_conj]
      exact (symm_mem_miyamotoPull_iff h L η).2 ((mem_normalizer_iff.1 hgN k).1 hk)
    · obtain ⟨k, hk, e⟩ := (mem_miyamotoPull h L η).1 hy
      have hy' : y = ((η.symm (g⁻¹ * k * g⁻¹⁻¹) : L) : G) := by
        rw [coe_symm_conj, e, map_inv, coe_inv, inv_inv]
        group
      rw [hy']
      refine (symm_mem_miyamotoPull_iff h L η).2 ?_
      exact (mem_normalizer_iff.1 (inv_mem hgN) k).1 hk
  · rintro ⟨hxL, hxN⟩
    obtain ⟨g, hg⟩ : ∃ g : gramSU h (miyamotoJ4 K), η ⟨x, hxL⟩ = g := ⟨_, rfl⟩
    have hx : x = ((η.symm g : L) : G) := by rw [← hg, MulEquiv.symm_apply_apply]
    refine ⟨g, ⟨g.2, mem_normalizer_iff.2 fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩, hx.symm⟩
    · have hy := (symm_mem_miyamotoPull_iff h L η (g := ⟨k, hM hk⟩)).2 hk
      have := (mem_normalizer_iff.1 hxN _).1 hy
      rw [hx, ← coe_symm_conj, symm_mem_miyamotoPull_iff] at this
      exact this
    · have hkS : k ∈ gramSU h (miyamotoJ4 K) := by
        have key : k = (g : GL (Fin 4) K)⁻¹ * ((g : GL (Fin 4) K) * k * (g : GL (Fin 4) K)⁻¹) *
            (g : GL (Fin 4) K) := by group
        rw [key]
        exact mul_mem (mul_mem (inv_mem g.2) (hM hk)) g.2
      obtain ⟨k', rfl⟩ : ∃ k' : gramSU h (miyamotoJ4 K), (k' : GL (Fin 4) K) = k :=
        ⟨⟨k, hkS⟩, rfl⟩
      have hk' : ((g * k' * g⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ M := by
        rw [coe_mul, coe_mul, coe_inv]
        exact hk
      have hy := (symm_mem_miyamotoPull_iff h L η (M := M) (g := g * k' * g⁻¹)).2 hk'
      rw [coe_symm_conj, ← hx] at hy
      have := (mem_normalizer_iff.1 hxN _).2 hy
      exact (symm_mem_miyamotoPull_iff h L η).1 this

theorem normalizer_miyamotoA1G [CharP K 2] :
    L ⊓ normalizer (miyamotoA1G h L η : Set G) =
      miyamotoA1G h L η ⊔ (miyamotoI1G h L η ⊔ miyamotoN1G h L η) := by
  rw [← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h true false),
    normalizer_miyamotoA1 h, miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h true false)
      (sup_le (miyamotoI1_le_SU h) (miyamotoN1_le_gramSU h)),
    miyamotoPull_sup h L η (miyamotoI1_le_SU h) (miyamotoN1_le_gramSU h)]

theorem normalizer_miyamotoA2G [CharP K 2] :
    L ⊓ normalizer (miyamotoA2G h L η : Set G) =
      miyamotoA2G h L η ⊔ (miyamotoI2G h L η ⊔ miyamotoN2G h L η) := by
  rw [← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h false true),
    normalizer_miyamotoA2 h, miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true)
      (sup_le (miyamotoI2_le_SU h) (miyamotoN2_le_gramSU h)),
    miyamotoPull_sup h L η (miyamotoI2_le_SU h) (miyamotoN2_le_gramSU h)]

theorem normalizer_miyamotoZG [CharP K 2] :
    L ⊓ normalizer (miyamotoPull h L η (miyamotoZ h) : Set G) =
      L ⊓ normalizer (miyamotoA2G h L η : Set G) := by
  have hZ : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  rw [← miyamotoPull_inf_normalizer h L η hZ,
    ← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h false true),
    normalizer_miyamotoZ h]

theorem centralizer_miyamotoZG [CharP K 2] :
    L ⊓ centralizer (miyamotoPull h L η (miyamotoZ h) : Set G) =
      miyamotoA2G h L η ⊔ (miyamotoPull h L η (miyamotoI2pow h) ⊔ miyamotoN2G h L η) := by
  have hZ : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  have hpow : miyamotoI2pow h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoI2pow_le_I2 h).trans (miyamotoI2_le_SU h)
  have e1 := miyamotoPull_inf_centralizer h L η (gramSU h (miyamotoJ4 K)) hZ
  rw [miyamotoPull_gramSU] at e1
  rw [← e1, centralizer_miyamotoZ h, miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true)
    (sup_le hpow (miyamotoN2_le_gramSU h)), miyamotoPull_sup h L η hpow (miyamotoN2_le_gramSU h)]

theorem normalizer_miyamotoPG [CharP K 2] :
    L ⊓ normalizer (miyamotoPG h L η : Set G) = miyamotoPG h L η ⊔ miyamotoIG h L η := by
  rw [← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h false false),
    normalizer_miyamotoP h, miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false false)
      (miyamotoI_le_gramSU h)]

theorem miyamoto_two_one_two_centralizersG [CharP K 2] (hf : 2 ≤ f) :
    miyamotoPG h L η ⊓ centralizer (miyamotoI1G h L η : Set G) =
        miyamotoPull h L η (miyamotoRootA h) ∧
      miyamotoPG h L η ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) =
        miyamotoPull h L η (miyamotoRootC h) ∧
      miyamotoPG h L η ⊓ centralizer (miyamotoI2G h L η : Set G) =
        miyamotoPull h L η (miyamotoRootB h) ∧
      miyamotoPG h L η ⊓ centralizer (miyamotoI2r1G h L η : Set G) =
        miyamotoPull h L η (miyamotoZ h) := by
  have hI1r2 : miyamotoI1r2 h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoI1r2_le_I h).trans (miyamotoI_le_gramSU h)
  have hI2r1 : miyamotoI2r1 h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← miyamotoPull_inf_centralizer h L η _ (miyamotoI1_le_SU h),
      miyamotoP_inf_centralizer_I1 h hf]
  · rw [← miyamotoPull_inf_centralizer h L η _ hI1r2, miyamotoP_inf_centralizer_I1r2 h hf]
  · rw [← miyamotoPull_inf_centralizer h L η _ (miyamotoI2_le_SU h),
      miyamotoP_inf_centralizer_I2 h hf]
  · rw [← miyamotoPull_inf_centralizer h L η _ hI2r1, miyamotoP_inf_centralizer_I2r1 h hf]

theorem conjTransitiveOn_miyamotoPull {N H : Subgroup (GL (Fin 4) K)}
    (hN : N ≤ gramSU h (miyamotoJ4 K)) (htr : ConjTransitiveOn N H) :
    ConjTransitiveOn (miyamotoPull h L η N) (miyamotoPull h L η H) := by
  intro x hx y hy hx1 hy1
  obtain ⟨u, hu, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  obtain ⟨v, hv, rfl⟩ := (mem_miyamotoPull h L η).1 hy
  have hu1 : (u : GL (Fin 4) K) ≠ 1 := fun e => hx1 (by
    rw [show u = 1 from Subtype.ext e, map_one, coe_one])
  have hv1 : (v : GL (Fin 4) K) ≠ 1 := fun e => hy1 (by
    rw [show v = 1 from Subtype.ext e, map_one, coe_one])
  obtain ⟨g, hg, e⟩ := htr _ hu _ hv hu1 hv1
  refine ⟨((η.symm ⟨g, hN hg⟩ : L) : G), (symm_mem_miyamotoPull_iff h L η).2 hg, ?_⟩
  have e' : (⟨g, hN hg⟩ : gramSU h (miyamotoJ4 K))⁻¹ * u * ⟨g, hN hg⟩ = v := Subtype.ext e
  have : ((η.symm ⟨g, hN hg⟩ : L) : G)⁻¹ * ((η.symm u : L) : G) * ((η.symm ⟨g, hN hg⟩ : L) : G) =
      ((η.symm ((⟨g, hN hg⟩ : gramSU h (miyamotoJ4 K))⁻¹ * u * ⟨g, hN hg⟩) : L) : G) := by
    simp only [map_mul, map_inv, coe_mul, coe_inv]
  rw [this, e']

theorem miyamoto_two_one_threeG [CharP K 2] (hf : 2 ≤ f) :
    ConjTransitiveOn (miyamotoIG h L η)
        (miyamotoPG h L η ⊓ centralizer (miyamotoI1G h L η : Set G)) ∧
      ConjTransitiveOn (miyamotoIG h L η) (miyamotoPG h L η ⊓
        centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G)) ∧
      ConjTransitiveOn (miyamotoIG h L η)
        (miyamotoPG h L η ⊓ centralizer (miyamotoI2G h L η : Set G)) ∧
      ConjTransitiveOn (miyamotoIG h L η)
        (miyamotoPG h L η ⊓ centralizer (miyamotoI2r1G h L η : Set G)) := by
  obtain ⟨t1, t2, t3, t4⟩ := miyamoto_two_one_three h hf
  obtain ⟨c1, c2, c3, c4⟩ := miyamoto_two_one_two_centralizersG h L η hf
  have hI := miyamotoI_le_gramSU h
  rw [miyamotoP_inf_centralizer_I1 h hf] at t1
  rw [miyamotoP_inf_centralizer_I1r2 h hf] at t2
  rw [miyamotoP_inf_centralizer_I2 h hf] at t3
  rw [miyamotoP_inf_centralizer_I2r1 h hf] at t4
  rw [c1, c2, c3, c4]
  exact ⟨conjTransitiveOn_miyamotoPull h L η hI t1, conjTransitiveOn_miyamotoPull h L η hI t2,
    conjTransitiveOn_miyamotoPull h L η hI t3, conjTransitiveOn_miyamotoPull h L η hI t4⟩

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
