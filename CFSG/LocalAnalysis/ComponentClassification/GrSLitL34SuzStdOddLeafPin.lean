module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLeafQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuter

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78

theorem map_centralizer_le_invE_zero
    {S : Type} [Group S] {W : Subgroup S} {u : S} (hu : u ∈ W)
    {Ψ : S →* Equiv.Perm (Fin 1782)} (hΨM : ∀ x, Ψ x ∈ suzM) (hΨu : Ψ u = suzInv 0) :
    (centralizer (W : Set S)).map Ψ ≤ invE 0 := by
  rintro _ ⟨x, hx, rfl⟩
  have hxu : x * u = u * x := (Subgroup.mem_centralizer_iff.1 hx u hu).symm
  refine mem_invE_zero.2 ⟨hΨM x, ?_⟩
  rw [← hΨu, ← map_mul, ← map_mul, hxu]

theorem isPerfect_map_commutator
    {S : Type} [Group S] {W : Subgroup S}
    (hWc : Nat.card ↥⁅centralizer (W : Set S), centralizer (W : Set S)⁆ = 20160) {u : S}
    (hu : u ∈ W) {Ψ : S →* Equiv.Perm (Fin 1782)} (hinj : Function.Injective Ψ)
    (hΨM : ∀ x, Ψ x ∈ suzM) (hΨu : Ψ u = suzInv 0) :
    Group.IsPerfect ↥(⁅centralizer (W : Set S), centralizer (W : Set S)⁆.map Ψ) := by
  have hCE : (centralizer (W : Set S)).map Ψ ≤ invE 0 :=
    map_centralizer_le_invE_zero hu hΨM hΨu
  set H : Subgroup ↥(invE 0) := ((centralizer (W : Set S)).map Ψ).subgroupOf (invE 0) with hH
  have hHmap : H.map (invE 0).subtype = (centralizer (W : Set S)).map Ψ := by
    rw [hH, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hCE]
  have hcommH : (⁅H, H⁆).map (invE 0).subtype =
      ⁅(centralizer (W : Set S)).map Ψ, (centralizer (W : Set S)).map Ψ⁆ := by
    rw [Subgroup.map_commutator, hHmap]
  have hcardH : Nat.card ↥⁅H, H⁆ =
      Nat.card ↥⁅centralizer (W : Set S), centralizer (W : Set S)⁆ := by
    rw [← Subgroup.card_map_of_injective (K := ⁅H, H⁆) (f := (invE 0).subtype)
      (invE 0).subtype_injective, hcommH]
    rw [← Subgroup.map_commutator (f := Ψ), Subgroup.card_map_of_injective hinj]
  have hc : Nat.card ↥⁅H, H⁆ = Nat.card suzD := by
    rw [hcardH, hWc, card_suzD]
  have h2 : Nat.card rho0.range = Nat.card suzD * 2 := by
    rw [card_range_rho0, card_suzD]
  have hperf : Group.IsPerfect ↥⁅H, H⁆ :=
    Quot2Data.isPerfect_commutator suz_quot2Data h2 hc
  have hEq : (⁅H, H⁆).map (invE 0).subtype =
      (⁅centralizer (W : Set S), centralizer (W : Set S)⁆).map Ψ := by
    rw [hcommH, Subgroup.map_commutator]
  rw [← hEq]
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.equivMapOfInjective ⁅H, H⁆ (invE 0).subtype
      (invE 0).subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective ⁅H, H⁆ (invE 0).subtype (invE 0).subtype_injective).surjective

theorem exists_mem_ker_rho0
    {S : Type} [Group S]
    {W : Subgroup S} (hW2 : ∀ w ∈ W, w * w = 1)
    (hWc : Nat.card ↥⁅centralizer (W : Set S), centralizer (W : Set S)⁆ = 20160) {u : S}
    (hu : u ∈ W) {Ψ : S →* Equiv.Perm (Fin 1782)} (hinj : Function.Injective Ψ)
    (hΨM : ∀ x, Ψ x ∈ suzM) (hΨu : Ψ u = suzInv 0) {w : S} (hw : w ∈ W) :
    ∃ hwE : Ψ w ∈ invE 0, (⟨Ψ w, hwE⟩ : invE 0) ∈ rho0.ker := by
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left (hW2 a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left (hW2 b hb)
    have hab : a * b * (a * b) = 1 := hW2 (a * b) (W.mul_mem ha hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have hwC : w ∈ centralizer (W : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hWcomm x hx w hw
  have hwE : Ψ w ∈ invE 0 :=
    map_centralizer_le_invE_zero hu hΨM hΨu ⟨w, hwC, rfl⟩
  refine ⟨hwE, suz_inner_ker (K := ⁅centralizer (W : Set S), centralizer (W : Set S)⁆.map Ψ)
    hwE ?_ ?_ ?_ ?_⟩
  · exact (Subgroup.map_mono (Subgroup.commutator_le_self _)).trans
      (map_centralizer_le_invE_zero hu hΨM hΨu)
  · exact isPerfect_map_commutator hWc hu hinj hΨM hΨu
  · rw [Subgroup.card_map_of_injective hinj, hWc]
  · rintro k ⟨y, hy, rfl⟩
    have hyC : y ∈ centralizer (W : Set S) := Subgroup.commutator_le_self _ hy
    have hwy : w * y = y * w := Subgroup.mem_centralizer_iff.1 hyC w hw
    rw [← map_mul, ← map_mul, hwy]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
