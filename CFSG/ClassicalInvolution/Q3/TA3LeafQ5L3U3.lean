module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Exit
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution Matrix
open scoped MatrixGroups commutatorElement

open Q5GL2

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
variable {F : Type} [Field F] {H : Subgroup (GL (Fin 2) F)}

theorem TightDatum.le_centralizer_of_gl2 (hD : TightDatum R S t) {N : Subgroup Y} [N.Normal]
    {π : H →* Y} (hrange : π.range = N ⊓ Subgroup.centralizer ({t} : Set Y)) (hk : CubeKer π)
    {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀)) (h4 : 4 ≤ Nat.card F₀)
    (eJ : slPart H ≃* SL(2, F₀)) :
    R ≤ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) := by
  have hJr : (slPart H).map π = (π.comp (slPart H).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eJ' : ↥((slPart H).map π) ≃* SL(2, F₀) :=
    (MulEquiv.subgroupCongr hJr).trans ((MonoidHom.ofInjective (injective_slPart hk)).symm.trans eJ)
  have : Group.IsPerfect ↥((slPart H).map π) := isPerfect_of_equiv_sl2 h4 eJ'
  have hJle : (slPart H).map π ≤ N ⊓ Subgroup.centralizer ({t} : Set Y) :=
    hrange ▸ Subgroup.map_le_range π _
  refine TightDatum.le_centralizer_of_maxPerfect hD (hJle.trans inf_le_left)
    (hJle.trans inf_le_right) ?_ (noOddNormal_of_equiv_sl2 hF₀ h4 eJ')
  intro M hMN hMt hMp
  have hMr : M ≤ π.range := hrange ▸ le_inf hMN hMt
  rw [← hMp]
  exact (Subgroup.commutator_mono hMr hMr).trans (commutator_range_le π)

theorem TightDatum.tightEx_of_gl2 (hD : TightDatum R S t) (hc : TightCls Y R S t)
    {N : Subgroup Y} [N.Normal] {π : H →* Y}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({t} : Set Y)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {N1 : H} (hN1 : (N1 : GL (Fin 2) F) = -1) (hπ1 : π N1 = t)
    {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀)) (h4 : 4 ≤ Nat.card F₀)
    (eJ : slPart H ≃* SL(2, F₀)) {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) :
    TightEx Y R S t := by
  have hRJ := TightDatum.le_centralizer_of_gl2 hD hrange hk hF₀ h4 eJ
  have hval : ∀ y ∈ N, y ∈ Subgroup.centralizer ({t} : Set Y) → ∃ A : H, π A = y :=
    fun y hyN hyt => by
      have : y ∈ π.range := hrange ▸ ⟨hyN, hyt⟩
      exact this
  have htN : t ∈ N := by
    have : π N1 ∈ N ⊓ Subgroup.centralizer ({t} : Set Y) := hrange ▸ ⟨N1, rfl⟩
    rw [← hπ1]
    exact this.1
  have hscal : ∀ A : H, π A ∈ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) →
      ∃ c : Fˣ, (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c := fun A hA =>
    exists_scalar_of_commute hk hcs fun B hB =>
      (Subgroup.mem_centralizer_iff.mp hA (π B) ⟨B, hB, rfl⟩).symm
  have hcomm : ∀ A B : H, (∃ c : Fˣ, (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c) →
      π A * π B = π B * π A := by
    rintro A B ⟨c, hcA⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcA, scalar_mul_comm]
  have hinv : ∀ v ∈ N, v ∈ Subgroup.centralizer ({t} : Set Y) →
      v ∈ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) → v * v = 1 →
        v = 1 ∨ v = t := by
    intro v hvN hvt hvJ hv2
    obtain ⟨A, rfl⟩ := hval v hvN hvt
    obtain ⟨c, hcA⟩ := hscal A hvJ
    rw [← hπ1]
    exact eq_or_of_scalar_sq hk hN1 hcA hv2
  have hsq : ∀ y ∈ N, y ∈ Subgroup.centralizer ({t} : Set Y) → y * y = t →
      y ∉ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) →
        y ∈ (slPart H).map π := by
    intro y hyN hyt hy2 hyJ
    obtain ⟨A, rfl⟩ := hval y hyN hyt
    refine mem_map_slPart_of_sq hk hN1 (by rw [hπ1]; exact hy2) fun c hcA => hyJ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, -, rfl⟩
    exact (hcomm A B ⟨c, hcA⟩).symm
  have hab : ∀ a ∈ R, a ∈ N → ∀ b ∈ R, b ∈ N → a * b = b * a := by
    intro a haR haN b hbR hbN
    obtain ⟨A, rfl⟩ := hval a haN (hD.cent haR)
    obtain ⟨B, rfl⟩ := hval b hbN (hD.cent hbR)
    exact hcomm A B (hscal A (hRJ haR))
  exact Or.inr (Or.inl ⟨TightDatum.tightEdgeless_of_sq hD hc.1 htN hRJ hsR hsN hs4 hinv hsq,
    TightDatum.not_tightActs3_of_cyclic4 hD hc.1 hsR hsN hs4 hab⟩)

end CFSG.ClassicalInvolution.Q3.TA3
