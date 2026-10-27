module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCenterOverPSU

public section

namespace CFSG.AGLEmbedding.CenterOver

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups

section Order

variable {Y K : Type*} [Group Y] [Finite Y] [Group K] [Finite K]

theorem factorization_card_eq {p : ℕ} (hp : p.Prime) (φ : Y →* K) (hφ : Function.Surjective φ)
    (hcop : p.Coprime (Nat.card φ.ker)) :
    (Nat.card Y).factorization p = (Nat.card K).factorization p := by
  have h1 : Nat.card Y = Nat.card K * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  have hnd : ¬ p ∣ Nat.card φ.ker := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

end Order

section Transport

theorem eq_top_or_card_eq_psu {K' : Type} [Field K'] [Finite K'] (J : HermitianForm 3 K')
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hfix : Nat.card {x : K' // J.conj x = x} = p ^ f)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 2 < p ^ f) {L K : Type} [Group L] [Finite L] [Group K]
    [Finite K] [IsSimpleGroup K] (hKnc : ∃ a b : K, a * b ≠ b * a)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) (T₁ : Subgroup L)
    (hT₁ : T₁.map e.toMonoidHom = rootGroup J hJ) (T : Sylow p K) (Y : Subgroup L)
    (φ : Y →* K) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hZY : T₁ ⊓ Subgroup.centralizer (T₁ : Set L) ≤ Y) :
    Y = ⊤ ∨ Nat.card (T₁ ⊓ Subgroup.centralizer (T₁ : Set L) : Subgroup L) =
      Nat.card (T : Subgroup K) := by
  classical
  have hp : p.Prime := Fact.out
  have hYns : ¬ Group.IsSolvable Y := not_isSolvable_of_surjective hKnc φ hφ
  set Y' : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := Y.map e.toMonoidHom with hY'
  set Z : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := rootGroup J hJ ⊓
    Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) with hZ
  have hZmap : (T₁ ⊓ Subgroup.centralizer (T₁ : Set L)).map e.toMonoidHom = Z := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hT₁]
        exact ⟨x, hx1, rfl⟩
      · rw [← hT₁]
        exact (UnitaryModel.mem_centralizer_map_iff e T₁ x).2 hx2
    · rintro ⟨hy1, hy2⟩
      rw [← hT₁] at hy1 hy2
      obtain ⟨x, hx1, rfl⟩ := hy1
      exact ⟨x, ⟨hx1, (UnitaryModel.mem_centralizer_map_iff e T₁ x).1 hy2⟩, rfl⟩
  have hZY' : Z ≤ Y' := by
    rw [← hZmap]
    exact Subgroup.map_mono hZY
  have hY'ns : ¬ Group.IsSolvable Y' := fun hs =>
    hYns (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective).toMonoidHom)
      (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective).injective)
  have hZcard : Nat.card Z = p ^ f := (unitalData_psu J hJ hK' hfix hp2 hf).pf
  have hZcard' : Nat.card (T₁ ⊓ Subgroup.centralizer (T₁ : Set L) : Subgroup L) = p ^ f := by
    rw [← hZcard, ← hZmap]
    exact (Subgroup.card_map_of_injective e.injective).symm
  rcases overgroup_psu J hJ hK' hfix hp2 hf hq Y' hZY' hY'ns with h | h
  · left
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : e x ∈ Y' := h ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact (e.injective hyx) ▸ hy
  · right
    have hv := factorization_card_eq hp φ hφ hcop
    have hTcard : Nat.card (T : Subgroup K) = p ^ (Nat.card K).factorization p :=
      T.card_eq_multiplicity
    have hY'Y : Nat.card Y' = Nat.card Y := Subgroup.card_map_of_injective e.injective
    have hle1 : Nat.card (T : Subgroup K) ≤ p ^ f := by
      obtain ⟨Q₀⟩ : Nonempty (Sylow p Y') := inferInstance
      have hQ₀ : Nat.card Q₀ = p ^ (Nat.card Y').factorization p := Q₀.card_eq_multiplicity
      have hinj : Function.Injective Y'.subtype := Subtype.val_injective
      set S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
        (Q₀ : Subgroup Y').map Y'.subtype with hS
      have hSle : S ≤ Y' := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hSe := Subgroup.equivMapOfInjective (Q₀ : Subgroup Y') Y'.subtype hinj
      have hSp : IsPGroup p S :=
        Q₀.isPGroup'.of_surjective hSe.toMonoidHom hSe.surjective
      have hSc : Nat.card S = Nat.card Q₀ := (Subgroup.card_map_of_injective hinj)
      have := h S hSle hSp
      rwa [hSc, hQ₀, hY'Y, hv, ← hTcard] at this
    have hle2 : p ^ f ≤ Nat.card (T : Subgroup K) := by
      have hd : p ^ f ∣ Nat.card Y' := hZcard ▸ Subgroup.card_dvd_of_le hZY'
      rw [hY'Y] at hd
      have hf' : f ≤ (Nat.card Y).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hd
      rw [hv] at hf'
      rw [hTcard]
      exact Nat.pow_le_pow_right hp.pos hf'
    rw [hZcard']
    exact le_antisymm hle2 hle1

end Transport

end CFSG.AGLEmbedding.CenterOver
