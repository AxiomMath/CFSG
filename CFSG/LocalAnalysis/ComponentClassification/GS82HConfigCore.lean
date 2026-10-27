module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP4Lift
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigNorm

public section

namespace CFSG.ComponentClassification.GSThmB.HConfig

open CFSG Subgroup LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem nonempty_quot_equiv_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) :=
  ⟨QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)⟩

theorem isSLTwoOver_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {q : ℕ}
    (h : HarrisLit.IsSLTwoOver q (A ⧸ pPrimeCore 2 A)) :
    HarrisLit.IsSLTwoOver q (B ⧸ pPrimeCore 2 B) := by
  obtain ⟨F, hF, hFt, hFq, ⟨eA⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_quot_equiv_of_mulEquiv e
  exact ⟨F, hF, hFt, hFq, ⟨e'.symm.trans eA⟩⟩

theorem nonempty_quot_equiv_of_central_surj
    {E A : Type} [Group E] [Group A] [Finite E] [Finite A] (hE : Group.IsPerfect E)
    (ρ : E →* A) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E) {q₀ : ℕ}
    (hq₀ : Odd q₀) (h5 : 5 ≤ q₀) (hA : HarrisLit.IsSLTwoOver q₀ (A ⧸ pPrimeCore 2 A)) :
    Nonempty (E ⧸ pPrimeCore 2 E ≃* A ⧸ pPrimeCore 2 A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hFq, ⟨eA⟩⟩ := hA
  set OA := pPrimeCore 2 A with hOA
  have hOAodd : Odd (Nat.card OA) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let θA : A →* SL(2, F) := eA.toMonoidHom.comp (QuotientGroup.mk' OA)
  have hθA : Function.Surjective θA := eA.surjective.comp (QuotientGroup.mk'_surjective OA)
  have hθAker : ∀ a : A, θA a = 1 ↔ a ∈ OA := by
    intro a
    change eA (QuotientGroup.mk a) = 1 ↔ _
    rw [map_eq_one_iff eA eA.injective, QuotientGroup.eq_one_iff]
  have hFodd : Odd (Nat.card F) := by rw [Nat.card_eq_fintype_card, hFq]; exact hq₀
  have hF5 : 5 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hFq]; exact h5
  have hOSL : pPrimeCore 2 SL(2, F) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eA, CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.map_bot]
  set θ : E →* SL(2, F) := θA.comp ρ with hθdef
  have hθ : Function.Surjective θ := hθA.comp hρ
  have h2c : ∀ x : E, θ x = 1 → ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ center E := by
    intro x hx k hxk
    have h1 : ρ x ∈ OA := (hθAker _).mp hx
    have h2 : ρ x ^ 2 ^ k = 1 := by rw [← map_pow, hxk, map_one]
    exact hker (MonoidHom.mem_ker.mpr
      (GS82PumpInputs.P4.eq_one_of_pow_two_pow_eq_one hOAodd h1 k h2))
  have hcomm : ∀ k ∈ θ.ker, ∀ g : E, ⁅k, g⁆ ∈ pPrimeCore 2 E := by
    set D := θ.ker with hDdef
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
    have hT2 : ∀ x ∈ (T : Subgroup ↥D), ((x : E)) ∈ center E := by
      intro x hx
      obtain ⟨k, hk⟩ := T.isPGroup' ⟨x, hx⟩
      have hk' : (x : E) ^ 2 ^ k = 1 := by
        have := congrArg (fun y : ↥(T : Subgroup ↥D) => ((y : ↥D) : E)) hk
        simpa using this
      exact h2c _ x.2 k hk'
    have hTc : (T : Subgroup ↥D) ≤ center ↥D := fun x hx =>
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hT2 x hx) g)
    have hNC : normalizer ((T : Subgroup ↥D) : Set ↥D) ≤
        centralizer ((T : Subgroup ↥D) : Set ↥D) := by
      intro g _
      rw [mem_centralizer_iff]
      intro x hx
      exact (mem_center_iff.mp (hTc hx) g).symm
    have hcompl := MonoidHom.ker_transferSylow_isComplement' T hNC
    have hNO : (MonoidHom.transferSylow T hNC).ker ≤ pPrimeCore 2 ↥D :=
      le_sSup ⟨MonoidHom.normal_ker _, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (MonoidHom.not_dvd_card_ker_transferSylow T hNC)⟩
    have hDO : (pPrimeCore 2 ↥D).map D.subtype ≤ pPrimeCore 2 E := by
      rw [ABGLocalTools.pPrimeCore_map_subtype_eq_inf (MonoidHom.normal_ker θ)]
      exact inf_le_right
    intro k hk g
    obtain ⟨⟨o, t⟩, hot⟩ := hcompl.2 ⟨k, hk⟩
    set o' : E := ((o : ↥D) : E) with ho'
    set t' : E := ((t : ↥D) : E) with ht'
    have hkot : k = o' * t' := by
      have := congrArg Subtype.val hot
      simpa using this.symm
    have ho : o' ∈ pPrimeCore 2 E := hDO ⟨o, hNO o.2, rfl⟩
    have ht : t' * g = g * t' := (mem_center_iff.mp (hT2 t t.2) g).symm
    have hcomm_t : ⁅o' * t', g⁆ = o' * (g * o'⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      calc o' * t' * g * (o' * t')⁻¹ * g⁻¹ = o' * (t' * g) * t'⁻¹ * o'⁻¹ * g⁻¹ := by group
        _ = o' * (g * t') * t'⁻¹ * o'⁻¹ * g⁻¹ := by rw [ht]
        _ = o' * (g * o'⁻¹ * g⁻¹) := by group
    rw [hkot, hcomm_t]
    exact mul_mem ho ((pPrimeCore_normal (p := 2) (G := E)).conj_mem _ (inv_mem ho) g)
  have hodd := GS82PumpInputs.P4.odd_card_ker_of_sl2 hE hFodd hF5 hOSL θ hθ hcomm
  have hle1 : θ.ker ≤ pPrimeCore 2 E := le_sSup ⟨θ.normal_ker, Nat.coprime_two_left.mpr hodd⟩
  have hle2 : pPrimeCore 2 E ≤ θ.ker := by
    have h1 : (pPrimeCore 2 E).map θ ≤ pPrimeCore 2 SL(2, F) := map_pPrimeCore_le θ hθ
    rw [hOSL, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot] at h1
    exact h1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (le_antisymm hle1 hle2).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ)).trans eA.symm⟩

theorem orbJoin_le_centralizer_of_mem [Finite G] {B K : Subgroup G} (hK : IsComponent K)
    {m : G} (hmD : m ∈ orbRest B K) (hmB : m ∈ centralizer (B : Set G)) :
    orbJoin B K ≤ centralizer ({m} : Set G) := by
  unfold orbJoin
  refine iSup₂_le fun b hb => ?_
  intro x hx
  rw [mem_cj] at hx
  rw [mem_centralizer_singleton_iff]
  have hmK : Commute (b⁻¹ * x * b) m := mem_centralizer_iff.mp (orbRest_le_centralizer hK hmD) _ hx
  have hmb : b * m * b⁻¹ = m := by rw [mem_centralizer_iff.mp hmB b hb, mul_inv_cancel_right]
  calc x * m = x * (b * m * b⁻¹) := by rw [hmb]
    _ = b * ((b⁻¹ * x * b) * m) * b⁻¹ := by group
    _ = b * (m * (b⁻¹ * x * b)) * b⁻¹ := by rw [hmK.eq]
    _ = (b * m * b⁻¹) * x := by group
    _ = m * x := by rw [hmb]

end CFSG.ComponentClassification.GSThmB.HConfig
