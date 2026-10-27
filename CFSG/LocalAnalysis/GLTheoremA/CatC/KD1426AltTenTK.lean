module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTenKlein

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenTK

variable {Y : Type} [Group Y] [Finite Y]

theorem lift_T {K B : Subgroup Y} (hK : K.Normal) (hB : CFSG.Open.IsElemAbelian 3 B)
    (π : ↥K ≃* alternatingGroup (Fin 10))
    (ψ : ↥B →* alternatingGroup (Fin 10))
    (hψequiv : ∀ (b : ↥B) (k : ↥K),
      π (KD264Inner.conjKequiv K hK (b : Y) k) = ψ b * π k * (ψ b)⁻¹)
    {σ : ↥(alternatingGroup (Fin 10))} (h3 : σ ^ 3 = 1)
    (hσc : ((σ : ↥(alternatingGroup (Fin 10))) : Equiv.Perm (Fin 10)).support.card = 3)
    (hσP : σ ∈ ψ.range) (hPc : Nat.card ψ.range = 27) :
    ∃ TY : Subgroup Y, Nat.card TY = 4 ∧ CFSG.Open.IsElemAbelian 2 TY ∧
      TY ≤ ((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype ∧
      B ≤ Subgroup.normalizer (TY : Set Y) ∧ ⁅B, TY⁆ = TY := by
  classical
  obtain ⟨TA, hTAcard, hTAel, hTAF, hTAnorm, hTAcov⟩ :=
    KD1426AltTenKlein.klein_on_P h3 hσc (KD1426Common.isElemAbelian_range hB ψ) hσP hPc
  set TK : Subgroup ↥K := TA.comap π.toMonoidHom with hTKdef
  have hπsurj : Function.Surjective π := π.surjective
  have hπinj : Function.Injective π := π.injective
  have hTKmem : ∀ k : ↥K, k ∈ TK ↔ π k ∈ TA := fun k => Subgroup.mem_comap
  have hTKcard : Nat.card TK = 4 := by
    have h1 : TK.map π.toMonoidHom = TA := by
      rw [hTKdef]
      exact Subgroup.map_comap_eq_self_of_surjective (f := π.toMonoidHom) hπsurj TA
    rw [← hTAcard, ← h1, Subgroup.card_map_of_injective (f := π.toMonoidHom) hπinj]
  have hTKel : CFSG.Open.IsElemAbelian 2 TK := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      apply hπinj
      have h1 := hTAel.1.is_comm.comm (⟨π a, (hTKmem a).1 a.2⟩ : ↥TA) ⟨π b, (hTKmem b).1 b.2⟩
      have h2 : π a * π b = π b * π a := congrArg Subtype.val h1
      simpa [map_mul] using h2
    · apply hπinj
      have h1 := hTAel.2 (π a) ((hTKmem a).1 ha)
      simpa [map_pow] using h1
  set TY : Subgroup Y := TK.map K.subtype with hTYdef
  have hTYmem : ∀ y : Y, y ∈ TY ↔ ∃ t ∈ TK, (t : Y) = y := fun y => by
    rw [hTYdef]
    constructor
    · intro h
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 h
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact Subgroup.mem_map.2 ⟨t, ht, rfl⟩
  have hTYcard : Nat.card TY = 4 := by
    rw [hTYdef, Subgroup.card_map_of_injective K.subtype_injective, hTKcard]
  have hTYel : CFSG.Open.IsElemAbelian 2 TY :=
    KD264Rank.isElemAbelian_map K.subtype_injective hTKel
  have hconjT : ∀ b : ↥B, ∀ t ∈ TK, KD264Inner.conjKequiv K hK (b : Y) t ∈ TK := by
    intro b t ht
    rw [hTKmem, hψequiv b t]
    exact hTAnorm (ψ b) (MonoidHom.mem_range.2 ⟨b, rfl⟩) (π t) ((hTKmem t).1 ht)
  have hBnormTY : ∀ b ∈ B, ∀ y ∈ TY, b * y * b⁻¹ ∈ TY := by
    intro b hb y hy
    obtain ⟨t, ht, rfl⟩ := (hTYmem y).1 hy
    rw [hTYmem]
    refine ⟨KD264Inner.conjKequiv K hK b t, hconjT ⟨b, hb⟩ t ht, ?_⟩
    exact KD264Inner.conjKequiv_apply K hK b t
  have hTYle : TY ≤ ((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := (hTYmem y).1 hy
    refine Subgroup.mem_map.2 ⟨t, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hTAF _ ((hTKmem t).1 ht)
  have hBnorm : B ≤ Subgroup.normalizer (TY : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hBnormTY b hb y hy
    · intro hy
      have := hBnormTY b⁻¹ (B.inv_mem hb) _ hy
      have key : b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y := by group
      rw [key] at this
      exact this
  have hcomm_eq : ⁅B, TY⁆ = TY := by
    apply le_antisymm
    · apply Subgroup.commutator_le.2
      intro b hb y hy
      rw [commutatorElement_def]
      exact TY.mul_mem (hBnormTY b hb y hy) (TY.inv_mem hy)
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := (hTYmem t).1 ht
      obtain ⟨d, hd, s0, hs0, hds⟩ := hTAcov (π t') ((hTKmem t').1 ht')
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hd
      have hs0' : π.symm s0 ∈ TK := by
        rw [hTKmem, MulEquiv.apply_symm_apply]
        exact hs0
      have hsπ : π (π.symm s0) = s0 := MulEquiv.apply_symm_apply π s0
      have hc_mem : KD264Inner.conjKequiv K hK (b : Y) (π.symm s0) * (π.symm s0)⁻¹ ∈ TK :=
        TK.mul_mem (hconjT b (π.symm s0) hs0') (TK.inv_mem hs0')
      have hc_π : π (KD264Inner.conjKequiv K hK (b : Y) (π.symm s0) * (π.symm s0)⁻¹) = π t' := by
        rw [map_mul, map_inv, hψequiv b (π.symm s0), hsπ]
        exact hds
      have hct : KD264Inner.conjKequiv K hK (b : Y) (π.symm s0) * (π.symm s0)⁻¹ = t' := by
        have h0 : π (KD264Inner.conjKequiv K hK (b : Y) (π.symm s0) * (π.symm s0)⁻¹ * t'⁻¹) = 1 := by
          rw [map_mul, map_inv, hc_π, mul_inv_cancel]
        exact mul_inv_eq_one.1 (π.injective (h0.trans (map_one π).symm))
      have hcm : ⁅(b : Y), ((π.symm s0 : ↥K) : Y)⁆ ∈ ⁅B, TY⁆ :=
        Subgroup.commutator_mem_commutator b.2 ((hTYmem _).2 ⟨π.symm s0, hs0', rfl⟩)
      have heq : ⁅(b : Y), ((π.symm s0 : ↥K) : Y)⁆ = (t' : Y) := by
        rw [← hct, commutatorElement_def]
        simp [KD264Inner.conjKequiv_apply, mul_assoc]
      rw [heq] at hcm
      exact hcm
  exact ⟨TY, hTYcard, hTYel, hTYle, hBnorm, hcomm_eq⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenTK

end
