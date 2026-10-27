module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes
public import CFSG.Sporadic.SuzOddCore.CompQuot

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup

theorem pPrimeCore_two_eq_oddCore (X : Type*) [Group X] : pPrimeCore 2 X = CFSG.oddCore X := by
  unfold pPrimeCore CFSG.oddCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

variable {X : Type*} [Group X] [Finite X]

theorem pPrimeCore_eq_bot_of_isPComponent (hO : pPrimeCore 2 X = ⊥) {L : Subgroup X}
    (hL : IsPComponent 2 L) : pPrimeCore 2 L = ⊥ := by
  obtain ⟨-, -, hs, -⟩ := hL
  exact GrSLit.pPrimeCore_eq_bot_of_isSubnormal hO hs

theorem isComponent_of_isPComponent (hO : pPrimeCore 2 X = ⊥) {L : Subgroup X}
    (hL : IsPComponent 2 L) : IsComponent L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).1 hL
  exact ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_bot_of_isPComponent hO hL)).trans
      QuotientGroup.quotientBot)).1 hq, hs⟩

theorem fusionZStar_eq_center_of_isPComponent (hO : pPrimeCore 2 X = ⊥) {L : Subgroup X}
    (hL : IsPComponent 2 L) : Open.fusionZStar L = center L :=
  GrSLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot (pPrimeCore_eq_bot_of_isPComponent hO hL)

theorem nonempty_quotient_center_equiv {E K : Type*} [Group E] [Group K] [Finite E]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : Group.IsSolvable ρ.ker)
    (D : Subgroup K) (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    (hDnc : ∃ a b : D, a * b ≠ b * a) {B : Subgroup E} (hB : IsComponent B) :
    Nonempty (B ⧸ center B ≃* D) := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : ⁅B.map ρ, B.map ρ⁆ = B.map ρ := by rw [← Subgroup.map_commutator, hBB]
  have hle : B.map ρ ≤ D := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (Sporadic.SuzOddCore.commutator_le_of_index_two hDi)
  have hsubD : ((B.map ρ).subgroupOf D).IsSubnormal := (hsub.map hρ).subgroupOf
  rcases hsubD.eq_bot_or_top_of_isSimpleGroup hDs with h | h
  ·
    exfalso
    have : Nontrivial B := LocalCores.isQuasisimple_nontrivial hq
    have hBk : B ≤ ρ.ker := by
      intro b hb
      rw [MonoidHom.mem_ker]
      have : (⟨ρ b, hle ⟨b, hb, rfl⟩⟩ : D) ∈ (B.map ρ).subgroupOf D := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨b, hb, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · have hBD : B.map ρ = D := by
      apply le_antisymm hle
      intro d hd
      have : (⟨d, hd⟩ : D) ∈ (B.map ρ).subgroupOf D := h ▸ Subgroup.mem_top _
      rwa [Subgroup.mem_subgroupOf] at this
    set ρB : B →* K := ρ.comp B.subtype
    have hrange : ρB.range = D := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hBD]
    have hkerB : ρB.ker = center B := by
      apply le_antisymm
      · rcases LocalCores.quasisimple_normal_subgroups hq ρB.normal_ker with h1 | h1
        · exfalso
          obtain ⟨a, b, hab⟩ := hDnc
          obtain ⟨x, hx⟩ := (hrange ▸ a.2 : (a : K) ∈ ρB.range)
          have hx1 : x ∈ ρB.ker := h1 ▸ Subgroup.mem_top x
          rw [MonoidHom.mem_ker, hx] at hx1
          apply hab
          have : a = 1 := Subtype.ext hx1
          rw [this, one_mul, mul_one]
        · exact h1
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hzD : ρB z ∈ D := by rw [← hrange]; exact ⟨z, rfl⟩
        have hc : (⟨ρB z, hzD⟩ : D) ∈ center D := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          exact (Sporadic.SuzOddCore.center_map_le ρ B hz (g : K) (by rw [hBD]; exact g.2)).symm
        rw [Sporadic.SuzOddCore.center_eq_bot_of_simple' hDs hDnc, Subgroup.mem_bot] at hc
        exact congrArg Subtype.val hc
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerB.symm).trans
      ((QuotientGroup.quotientKerEquivRange ρB).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.ComponentClassification.GrSLit.HeldFix
