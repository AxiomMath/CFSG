module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5UniFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Count
public import CFSG.RankThree.PartTwo.KFacts.AutPSL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator

section Transport

variable {Lb P : Type*} [Group Lb] [Group P] (e : Lb ⧸ Subgroup.center Lb ≃* P)

@[expose] noncomputable def centerQuotHom : Lb →* P :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Lb))

@[expose] noncomputable def centerQuotAut : MulAut Lb →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp (autCenterQuot Lb)

theorem centerQuotHom_surjective : Function.Surjective (centerQuotHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_centerQuotHom : (centerQuotHom e).ker = Subgroup.center Lb := by
  ext x
  rw [MonoidHom.mem_ker, centerQuotHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem centerQuotAut_apply (β : MulAut Lb) (x : Lb) :
    centerQuotHom e (β x) = centerQuotAut e β (centerQuotHom e x) := by
  simp [centerQuotHom, centerQuotAut, MulAut.congr_apply, autCenterQuot_mk]

theorem centerQuotAut_injective (hK : commutator Lb = ⊤) : Function.Injective (centerQuotAut e) :=
  (MulAut.congr e).injective.comp (autCenterQuot_injective_of_perfect hK)

theorem centerQuotAut_conj (x : Lb) :
    centerQuotAut e (MulAut.conj x) = MulAut.conj (centerQuotHom e x) := by
  ext y
  obtain ⟨z, rfl⟩ := centerQuotHom_surjective e y
  rw [← centerQuotAut_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem innerAut_le_map_centerQuotAut : innerAut P ≤ (innerAut Lb).map (centerQuotAut e) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := centerQuotHom_surjective e y
  exact ⟨MulAut.conj x, ⟨x, rfl⟩, centerQuotAut_conj e x⟩

end Transport

variable {G : Type} [Group G] [Finite G]

theorem isCompLocallyBalanced_five_projectiveSL {X B : Subgroup G} (hBX : B ≤ X)
    (hB : IsElemAbelian 5 B) (hrank : GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B)
    {L : Subgroup G} (hL : GLAPComponent 5 X L) {F : Type} [Field F] [Finite F] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP F ℓ] (hK : Nat.card F = ℓ ^ f)
    (h5 : 5 ∣ Nat.card F - 1) (h2 : ringChar F ≠ 2)
    (e : barOf 5 L ⧸ Subgroup.center (barOf 5 L) ≃* projectiveSL 5 F) :
    IsCompLocallyBalanced 5 2 B L := by
  have hp : Nat.Prime 5 := Nat.prime_five
  have hperf : commutator (barOf 5 L) = ⊤ := (isQuasisimple_barOf hp hL).1
  have hodd := CFSG.HardMathSupport.Timmesfeld.Balance.Alt.odd_card_center_barOf hp
    (by norm_num) L
  set Γ := centerQuotHom e with hΓ
  set ψ := centerQuotAut e with hψ
  have hΓs := centerQuotHom_surjective e
  have hΓk := ker_centerQuotHom e
  refine isCompLocallyBalanced_five_of_data hBX hB hrank hL ((linearAutGroup 5 F).comap ψ) ?_
    ((heisUpper_projectiveSL hp (by norm_num) h5).of_injective ψ (centerQuotAut_injective e hperf)
      (innerAut_le_map_centerQuotAut e))
    (hasCentTorus_two_projectiveSL_five hΓs hΓk hodd h5)
    (hasCentTorus_three_projectiveSL_five hΓs hΓk hodd h5 h2).hasTorusFixed_one
    (fun β hβR hβ5 => hasTorusFixed_three_projectiveSL_five hΓs hΓk hodd hℓ hf hK h5 h2
      (b := ψ β) (fun x => centerQuotAut_apply e β x) hβR (by rw [← map_pow, hβ5, map_one]))
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_comap, centerQuotAut_conj]
  obtain ⟨g, hg⟩ := proj_surjective 5 F (Γ x)
  rw [← hg, ← conjAut_toGL]
  exact conjAut_mem_linearAutGroup _

theorem isCompLocallyBalanced_five_primeFormP {X B : Subgroup G} (hBX : B ≤ X)
    (hB : IsElemAbelian 5 B) (hrank : GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B)
    {L : Subgroup G} (hL : GLAPComponent 5 X L) {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (h5 : 5 ∣ ℓ ^ f + 1) (h2 : ringChar K ≠ 2)
    (e : barOf 5 L ⧸ Subgroup.center (barOf 5 L) ≃* primeFormP h (idGram K 5)) :
    IsCompLocallyBalanced 5 2 B L := by
  have hp : Nat.Prime 5 := Nat.prime_five
  have hperf : commutator (barOf 5 L) = ⊤ := (isQuasisimple_barOf hp hL).1
  have hodd := CFSG.HardMathSupport.Timmesfeld.Balance.Alt.odd_card_center_barOf hp
    (by norm_num) L
  set Γ := centerQuotHom e with hΓ
  set ψ := centerQuotAut e with hψ
  have hΓs := centerQuotHom_surjective e
  have hΓk := ker_centerQuotHom e
  refine isCompLocallyBalanced_five_of_data hBX hB hrank hL
    ((primeFormD h (idGram K 5)).comap ψ) ?_
    ((heisUpper_primeFormP h hp (by norm_num) (by omega) (by omega) h5).of_injective ψ
      (centerQuotAut_injective e hperf) (innerAut_le_map_centerQuotAut e))
    (hasCentTorus_two_primeFormP_five h hΓs hΓk hodd h5)
    (hasCentTorus_three_primeFormP_five h hΓs hΓk hodd h5 h2).hasTorusFixed_one
    (fun β hβR hβ5 => hasTorusFixed_three_primeFormP_five h hΓs hΓk hodd h5 h2
      (b := ψ β) (fun x => centerQuotAut_apply e β x) hβR (by rw [← map_pow, hβ5, map_one]))
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_comap, centerQuotAut_conj]
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (normOneScalars h (gramSU h (idGram K 5)) 5) (Γ x)
  rw [← hg, QuotientGroup.mk'_apply, ← primeFormConjHom_eq_conj]
  exact ⟨_, rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator
