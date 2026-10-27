module

public import CFSG.ClassicalInvolution.Asc77.AscS24Lift
public import CFSG.ClassicalInvolution.Asc77.AscS24Cent

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan
open CFSG.Open (classicalInvolutionOddCore IsElemAbelian)
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

namespace Ctx


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem s_mem_centralizer_e0 : C.D.F.ρ₃.r ∈ Subgroup.centralizer ({C.e0} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc C.D.F.ρ₃.r * C.e0 = C.D.F.ρ₃.r * C.e0 * C.D.F.ρ₃.r⁻¹ * C.D.F.ρ₃.r := by group
    _ = C.e0 * C.D.F.ρ₃.r := by rw [C.conj_s_e0]

theorem s_mem_J : C.D.F.ρ₃.r ∈ conjSub g⁻¹ K := by
  have := C.D.F.ρ₃.hRK.1 C.D.F.ρ₃.hr
  rwa [C.hJ] at this

theorem r_mem_K : C.D.F.ρ.r ∈ K := by
  have := C.D.F.ρ.hRK.1 C.D.F.ρ.hr
  rwa [C.hK] at this

theorem t_mem_K' : C.D.F.ρ'.r ∈ K' := by
  have := C.D.F.ρ'.hRK.1 C.D.F.ρ'.hr
  rwa [C.hK'] at this

theorem oddQuotMk_s_z_ne (hz : z ∈ Subgroup.centralizer ({C.e0} : Set G))
    (hu : u ∈ Subgroup.centralizer ({C.e0} : Set G)) :
    oddQuotMk C.e0 ⟨C.D.F.ρ₃.r, C.s_mem_centralizer_e0⟩ * oddQuotMk C.e0 ⟨z, hz⟩ ≠
      oddQuotMk C.e0 ⟨z, hz⟩ * oddQuotMk C.e0 ⟨C.D.F.ρ₃.r, C.s_mem_centralizer_e0⟩ := by
  intro h
  have hsz : C.D.F.ρ₃.r * z = u * z * C.D.F.ρ₃.r := by
    calc C.D.F.ρ₃.r * z = C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ * C.D.F.ρ₃.r := by group
      _ = u * z * C.D.F.ρ₃.r := by rw [C.conj_s_z]
  have h1 : (⟨C.D.F.ρ₃.r, C.s_mem_centralizer_e0⟩ : ↥(Subgroup.centralizer ({C.e0} : Set G))) *
      ⟨z, hz⟩ = ⟨u, hu⟩ * ⟨z, hz⟩ * ⟨C.D.F.ρ₃.r, C.s_mem_centralizer_e0⟩ := Subtype.ext hsz
  have h2 := congrArg (oddQuotMk C.e0) h1
  rw [map_mul, map_mul, map_mul, h] at h2
  have h3 : oddQuotMk C.e0 ⟨u, hu⟩ = 1 := by
    have h4 := mul_right_cancel h2
    have h5 : 1 * oddQuotMk C.e0 ⟨z, hz⟩ = oddQuotMk C.e0 ⟨u, hu⟩ * oddQuotMk C.e0 ⟨z, hz⟩ := by
      rw [one_mul]; exact h4
    exact (mul_right_cancel h5).symm
  have h6 := eq_one_of_oddQuotMk_eq_one (a := C.e0) (x := ⟨u, hu⟩) (Subtype.ext C.u_sq) h3
  exact C.u_ne_one (congrArg Subtype.val h6)

theorem modOdd_pair_of_dichotomy [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    (hLt : LayerLieType p f Ω C.e0 t 3) {lin uni : Prop}
    (hSP : ∀ (D : LocalLieSystemAt p f (exactFamily Ω C.e0) C.e0) (i : Fin D.card),
      D.tag i = t →
        ModelFacts.StandardPairDichotomyTypes p (D.tag i) (D.rank i) (D.exp i) lin uni) :
    (lin ∧ ∃ W', LinearBlockStandardPair (GaloisField p f) W' (modOdd C.e0 K)
        (modOdd C.e0 (conjSub g⁻¹ K))) ∨
      (uni ∧ ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W' (modOdd C.e0 K)
        (modOdd C.e0 (conjSub g⁻¹ K))) := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hc2 := C.e0_isPGroup hZ
  have hKt := C.K_mem_tq_e0 hZ
  have hJt := C.J_mem_tq_e0 hZ
  have hne : (tqMembers Ω C.e0).Nonempty := ⟨K, hKt⟩
  have hKC := C.K_le_centralizer_e0 hZ hL
  have hJC := C.J_le_centralizer_e0 hZ hL
  have hKe : exactCore C.e0 K = K := exactCore_eq_self C.K_classical.perfect hKC
  have hJe : exactCore C.e0 (conjSub g⁻¹ K) = conjSub g⁻¹ K :=
    exactCore_eq_self C.J_classical.perfect hJC
  have hzC : z ∈ Subgroup.centralizer ({C.e0} : Set G) := hKC C.hs.hz.mem
  have huC : u ∈ Subgroup.centralizer ({C.e0} : Set G) := hJC C.J_classical.mem
  have hnc := C.oddQuotMk_s_z_ne hzC huC
  have hzK : ∀ y ∈ modOdd C.e0 K, oddQuotMk C.e0 ⟨z, hzC⟩ * y = y * oddQuotMk C.e0 ⟨z, hzC⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hzk : z * (k : G) = k * z := C.hs.hz.commute_of_mem hk'
    rw [← map_mul, ← map_mul]
    exact congrArg (oddQuotMk C.e0) (Subtype.ext hzk)
  have hsJ' : oddQuotMk C.e0 ⟨C.D.F.ρ₃.r, C.s_mem_centralizer_e0⟩ ∈ modOdd C.e0 (conjSub g⁻¹ K) :=
    oddQuotMk_mem_modOdd C.s_mem_J C.s_mem_centralizer_e0
  have hzK' : oddQuotMk C.e0 ⟨z, hzC⟩ ∈ modOdd C.e0 K := oddQuotMk_mem_modOdd C.hs.hz.mem hzC
  obtain ⟨D, hD1, i, hDt, hDr⟩ := exists_local_of_layerLieType hLt
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i with hψ
  have hG2 : D.tag i ≠ .G2 := by rcases ht with h | h <;> rw [hDt, h] <;> decide
  have hD4 : D.tag i ≠ .trialityD4 := by rcases ht with h | h <;> rw [hDt, h] <;> decide
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd h hD4
  have h5 : 5 ≤ p ^ D.exp i := by rw [hexp]; exact hq
  have h4 : 4 ≤ p ^ D.exp i := by omega
  obtain ⟨R₁, hR₁, hmod₁⟩ := exists_fund_of_mem' hΩ hc2 hne D hD1 hKt i
  obtain ⟨R₂, hR₂, hmod₂⟩ := exists_fund_of_mem' hΩ hc2 hne D hD1 hJt i
  obtain ⟨τ₁, hτ₁R, hτ₁2, hτ₁1, hτ₁c⟩ := exists_tau hp D i h5 hG2 hD4 hR₁
  obtain ⟨τ₂, hτ₂R, hτ₂2, hτ₂1, hτ₂c⟩ := exists_tau hp D i h5 hG2 hD4 hR₂
  have hz₁ := oddQuotMk_involution' hp hΩ hc2 D i h4 hKt C.K_classical hR₁ hτ₁c hmod₁.symm
  have hu₂ := oddQuotMk_involution' hp hΩ hc2 D i h4 hJt C.J_classical hR₂ hτ₂c hmod₂.symm
  set hzC' := exactCore_le_centralizer C.e0 K (mem_exactCore C.K_classical hc2 hKt.2)
  set huC' := exactCore_le_centralizer C.e0 (conjSub g⁻¹ K)
    (mem_exactCore C.J_classical hc2 hJt.2)
  have hodd : Odd (Nat.card (Subgroup.center (compModel D i).K)) := by
    have hT6 : AschTight.S1911.IsT6Tag (D.tag i) (D.rank i) := by
      rcases ht with h | h
      · exact Or.inl ⟨hDt.trans h, hDr⟩
      · exact Or.inr (Or.inl ⟨hDt.trans h, hDr⟩)
    exact AschTight.S19M.factM3 p (D.exp i) Fact.out hp (D.tag i) (D.rank i) hT6 (D.admissible i)
  have hfin : Finite (compModel D i).K :=
    ModelFacts.finite_modelUniv hp Fact.out (ih8_isFundTag_mf (D.isFundTag i)) (D.admissible i)
  have hzu : (⟨z, hzC'⟩ : ↥(Subgroup.centralizer ({C.e0} : Set G))) * ⟨u, huC'⟩ =
      ⟨u, huC'⟩ * ⟨z, hzC'⟩ := Subtype.ext C.comm_uz.symm
  have hτcomm : τ₁ * τ₂ = τ₂ * τ₁ := by
    refine commute_of_map_commute ψ
      (secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D i) hodd
      hτ₁2 hτ₂2 ?_
    rw [← hz₁, ← hu₂, ← map_mul, ← map_mul, hzu]
  have ho₁ : orderOf τ₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ₁2) hτ₁1
  have ho₂ : orderOf τ₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ₂2) hτ₂1
  rw [hKe] at hmod₁
  rw [hJe] at hmod₂
  rcases (hSP D i hDt).map_of_commute hp h5 ψ
      (secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D i)
      (ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR₁)
      (ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR₂) hτ₁R hτ₂R ho₁ ho₂ hτcomm
    with h | h | ⟨hl, W', hW⟩ | ⟨hu, W', hW⟩
  · exfalso
    rw [hmod₁, hmod₂] at h
    exact hnc (hzK _ (h ▸ hsJ')).symm
  · exfalso
    rw [hmod₁, hmod₂] at h
    exact hnc (h _ hzK' _ hsJ').symm
  · rw [hmod₁, hmod₂, hexp] at hW
    exact Or.inl ⟨hl, W', hW⟩
  · rw [hmod₁, hmod₂, hexp] at hW
    exact Or.inr ⟨hu, W', hW⟩

theorem modOdd_standardPair [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    (piSign p f = true → ∃ W', LinearBlockStandardPair (GaloisField p f) W' (modOdd C.e0 K)
        (modOdd C.e0 (conjSub g⁻¹ K))) ∧
      (piSign p f = false → ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W'
        (modOdd C.e0 K) (modOdd C.e0 (conjSub g⁻¹ K))) := by
  refine ⟨fun hπ => ?_, fun hπ => ?_⟩
  · have hLt : LayerLieType p f Ω C.e0 .PSL 3 := by simpa [hπ] using hL
    rcases C.modOdd_pair_of_dichotomy hZ hL (Or.inl rfl) hLt (lin := True) (uni := False)
        (fun D i hDi => by
          have hadm := D.admissible i
          rw [hDi] at hadm
          have := ModelFacts.standardPairDichotomyTypes_psl hadm
          rwa [← hDi] at this) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact h.elim
  · have hLt : LayerLieType p f Ω C.e0 .PSU 3 := by simpa [hπ] using hL
    rcases C.modOdd_pair_of_dichotomy hZ hL (Or.inr rfl) hLt (lin := False) (uni := True)
        (fun D i hDi => by
          have hadm := D.admissible i
          rw [hDi] at hadm
          have := ModelFacts.standardPairDichotomyTypes_psu hadm
          rwa [← hDi] at this) with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.elim
    · exact h

theorem standardPair [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    (piSign p f = true →
      LinearBlockStandardPair (GaloisField p f) (K ⊔ conjSub g⁻¹ K) K (conjSub g⁻¹ K)) ∧
    (piSign p f = false →
      UnitaryBlockStandardPair (GaloisField p (2 * f)) p f (K ⊔ conjSub g⁻¹ K) K
        (conjSub g⁻¹ K)) := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hXc : K ⊔ conjSub g⁻¹ K ≤ Subgroup.centralizer ({C.e0} : Set G) :=
    sup_le (C.K_le_centralizer_e0 hZ hL) (C.J_le_centralizer_e0 hZ hL)
  have hKp : K ≤ ⁅K, K⁆ := (Subgroup.isPerfect_iff.mp C.K_classical.perfect).ge
  have hJp : conjSub g⁻¹ K ≤ ⁅conjSub g⁻¹ K, conjSub g⁻¹ K⁆ :=
    (Subgroup.isPerfect_iff.mp C.J_classical.perfect).ge
  have hcent := C.sup_le_centralizer_oddCore hZ hL
  obtain ⟨hlin, huni⟩ := C.modOdd_standardPair hZ hL
  refine ⟨fun hπ => ?_, fun hπ => ?_⟩
  · obtain ⟨W', hW⟩ := hlin hπ
    have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
    have hF : RouteD.OddCoverSL3 (GaloisField p f) :=
      CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} hcard hq
    exact linear_lift_of_centralizes (by rw [hcard]; omega) hF hXc hKp hJp hcent hW
  · obtain ⟨W', hW⟩ := huni hπ
    have hK₀ : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
    have hF : RouteD.OddCoverSU3 (GaloisField p (2 * f)) p f := RouteD.oddCoverSU3 hp hK₀ hq
    exact unitary_lift_of_centralizes hK₀ hq hF hXc hKp hJp hcent hW

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
