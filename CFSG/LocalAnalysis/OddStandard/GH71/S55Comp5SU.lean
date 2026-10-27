module

public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularIso

public section

namespace CFSG.OddStandard.GH71.S55

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary

variable (Ω : Type) [Field Ω] (ℓ f : ℕ)

abbrev unitField [ExpChar Ω ℓ] : Subfield Ω :=
  RingHom.eqLocusField (iterateFrobenius Ω ℓ (2 * f)) (RingHom.id Ω)

variable {Ω ℓ f}

theorem mem_unitField_iff [ExpChar Ω ℓ] (c : Ω) : c ∈ unitField Ω ℓ f ↔ c ^ (ℓ ^ f) ^ 2 = c := by
  rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply, ← pow_mul, mul_comm f 2]

variable [Fact ℓ.Prime] [CharP Ω ℓ]

theorem card_unitField [IsAlgClosed Ω] (hf : 1 ≤ f) :
    Nat.card (unitField Ω ℓ f) = (ℓ ^ f) ^ 2 := by
  rw [← pow_mul, mul_comm f 2]
  exact CFSG.RankThree.Chevalley.natCard_eqLocusField_frob Fact.out (by omega)
    (fun c => iterateFrobenius_def ℓ (2 * f) c)

theorem nonempty_statedSU_mulEquiv [IsAlgClosed Ω] (hf : 1 ≤ f) {U : Subgroup (GL (Fin 3) Ω)}
    (hU : (U : Set (GL (Fin 3) Ω)) = CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (ℓ ^ f) ^ 2 ∧
      Nonempty (StatedSU 3 (ℓ ^ f) F ≃* U) := by
  classical
  set F := unitField Ω ℓ f with hFdef
  have hF := card_unitField (Ω := Ω) hf
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hF]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  have hmem : ∀ B : GL (Fin 3) F, B ∈ StatedSU 3 (ℓ ^ f) F ↔
      (B : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
        ((B : Matrix (Fin 3) (Fin 3) F).map (· ^ ℓ ^ f))ᵀ * (B : Matrix (Fin 3) (Fin 3) F) = 1 := by
    intro B
    rw [← SUid_eq_statedSU hF, mem_SUid, conjTr]
    have e : (B : Matrix (Fin 3) (Fin 3) F).map (CFSG.LieType.BorelTits.unitaryInvolution F ℓ f) =
        (B : Matrix (Fin 3) (Fin 3) F).map (· ^ ℓ ^ f) := by
      refine Matrix.ext fun i j => ?_
      exact CFSG.LieType.BorelTits.unitaryInvolution_apply F ℓ f _
    rw [e]
  set ι : GL (Fin 3) F →* GL (Fin 3) Ω := GeneralLinearGroup.map F.subtype with hι
  have hιe : ∀ B : GL (Fin 3) F, ((ι B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      (B : Matrix (Fin 3) (Fin 3) F).map F.subtype := fun B => by
    ext i j
    exact GeneralLinearGroup.map_apply _ i j B
  have hpow : ∀ M : Matrix (Fin 3) (Fin 3) F,
      (M.map F.subtype).map (· ^ ℓ ^ f) = (M.map (· ^ ℓ ^ f)).map F.subtype := fun M => by
    ext i j
    simp
  have hU' : ∀ X, X ∈ U ↔ X ∈ CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3 := fun X => by
    rw [← SetLike.mem_coe, hU]
  have hmap : ∀ B ∈ StatedSU 3 (ℓ ^ f) F, ι B ∈ U := by
    intro B hB
    obtain ⟨hdet, horth⟩ := (hmem B).1 hB
    rw [hU']
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [hιe]
      exact (mem_unitField_iff _).1 (B i j).2
    · rw [hιe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    · rw [hιe, hpow, ← transpose_map, ← Matrix.map_mul, horth, Matrix.map_one _ (map_zero _)
        (map_one _)]
  let φ : StatedSU 3 (ℓ ^ f) F →* U :=
    (ι.comp (StatedSU 3 (ℓ ^ f) F).subtype).codRestrict U fun B => hmap B B.2
  have hinj : Function.Injective φ := by
    intro A B h
    have h1 : ((ι A : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
        ((ι B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) :=
      congrArg (fun X : U => ((X : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)) h
    rw [hιe, hιe] at h1
    exact Subtype.ext (Units.ext (Matrix.map_injective Subtype.val_injective h1))
  have hsurj : Function.Surjective φ := by
    rintro ⟨X, hX⟩
    obtain ⟨hent, hdet, horth⟩ := (hU' X).1 hX
    set M : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j =>
      ⟨(X : Matrix (Fin 3) (Fin 3) Ω) i j, (mem_unitField_iff _).2 (hent i j)⟩
    have hM : M.map F.subtype = (X : Matrix (Fin 3) (Fin 3) Ω) := by
      ext i j
      rfl
    have hMdet : M.det = 1 := by
      apply F.subtype.injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, hdet, map_one]
    set B := GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero)
    have hB : (B : Matrix (Fin 3) (Fin 3) F) = M := rfl
    have hBmem : B ∈ StatedSU 3 (ℓ ^ f) F := by
      refine (hmem B).2 ⟨by rw [hB, hMdet], ?_⟩
      apply Matrix.map_injective Subtype.val_injective
      change ((M.map (· ^ ℓ ^ f))ᵀ * M).map F.subtype = (1 : Matrix (Fin 3) (Fin 3) F).map F.subtype
      rw [Matrix.map_mul, transpose_map, ← hpow, hM, horth, Matrix.map_one _ (map_zero _)
        (map_one _)]
    refine ⟨⟨B, hBmem⟩, Subtype.ext (Units.ext ?_)⟩
    change ((ι B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = _
    rw [hιe, hB, hM]
  exact ⟨F, inferInstance, inferInstance, hF, ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩⟩

end CFSG.OddStandard.GH71.S55
