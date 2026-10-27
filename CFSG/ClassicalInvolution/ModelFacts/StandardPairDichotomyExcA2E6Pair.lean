module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Form
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Factor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits

section RankOne

variable {K : Type} [Field K]

theorem mem_stdRankOne_e6_iff' {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (r : ↥(adjointGroup .E6 K)) :
    r ∈ stdRankOne (e6AdjDatum K) β ↔
      ∃ A : SL2 K, (r : ModGL .E6 K) = rootSL2 .E6 K β A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .E6) hβ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E6 K hβ).1
  change r ∈ rootGroup (rootOperatorFamily .E6) K β ⊔
    rootGroup (rootOperatorFamily .E6) K (-β) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem rootSL2_HSL_eq_thetaDiag_E6 {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) (c : Kˣ) :
    rootSL2 .E6 K β (HSL c) = rootDiagUnit .E6 (thetaDiag β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E6 K hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  change rootTorusSL2 .E6 K β c = _
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E6 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E6 a : ModGL .E6 K) : Module.End K (RootModule .E6 K))
      (rootVec .E6 K (Pi.single i 1))) = ((a i : Kˣ) : K) • rootVec .E6 K (Pi.single i 1) := by
    change rootDiag a (rootVec .E6 K (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E6 i), hs]
  rw [h2] at h1
  have hne : rootVec .E6 K (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E6 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective K hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_isRoot_E6 hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

end RankOne

section Involutions

variable {K : Type} [Field K]

theorem eq_signDiagE6_of_orderOf_eq_two (hK : ringChar K ≠ 2) {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) {c : ↥(adjointGroup .E6 K)}
    (hc : c ∈ stdRankOne (e6AdjDatum K) β) (hc2 : orderOf c = 2) :
    (c : ModGL .E6 K) = signDiagE6 K β := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hinj : Function.Injective (rootSL2 .E6 K β) :=
    ((exceptional_Lang_root_rank_one_data .E6 K β).2.2.2.2.2.2.2.1 hK).1
  obtain ⟨A, hA⟩ := (mem_stdRankOne_e6_iff' hβ c).1 hc
  obtain ⟨hc1, hne⟩ := (orderOf_eq_prime_iff (p := 2)).1 hc2
  have hAA : A * A = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hA]
    have := congrArg (fun x : ↥(adjointGroup .E6 K) => (x : ModGL .E6 K)) hc1
    simpa [sq] using this
  rcases sl2_sq_eq_one_A2 h2 hAA with rfl | rfl
  · exfalso
    apply hne
    exact Subtype.ext (by rw [hA, map_one]; rfl)
  · rw [hA]
    exact rootSL2_HSL_eq_thetaDiag_E6 hβ (-1)

theorem signDiagE6_mem_stdRankOne {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    (⟨signDiagE6 K β, by
        rw [signDiagE6, ← rootSL2_HSL_eq_thetaDiag_E6 hβ (-1)]
        exact rootSL2_mem_adjointGroup _ _⟩ : ↥(adjointGroup .E6 K)) ∈
      stdRankOne (e6AdjDatum K) β :=
  (mem_stdRankOne_e6_iff' hβ _).2 ⟨HSL (-1), (rootSL2_HSL_eq_thetaDiag_E6 hβ (-1)).symm⟩

theorem conj_mem_stdRankOne_of_mem_h1E6 {g : ↥(adjointGroup .E6 K)}
    (hg : (g : ModGL .E6 K) ∈ h1E6 K) {x : ↥(adjointGroup .E6 K)}
    (hx : x ∈ stdRankOne (e6AdjDatum K) thetaE6) :
    g * x * g⁻¹ ∈ stdRankOne (e6AdjDatum K) thetaE6 := by
  obtain ⟨B, hB⟩ := (mem_stdRankOne_e6_iff' isRoot_thetaE6 x).1 hx
  obtain ⟨n, hn, A, hgA⟩ := hg
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E6 hn (A * B * A⁻¹)
  refine (mem_stdRankOne_e6_iff' isRoot_thetaE6 _).2 ⟨A', ?_⟩
  rw [← hA']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgA, hB, map_mul, map_inv]
  group

theorem mem_h1E6_of_commute_signDiagE6 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E6 K)}
    (hu : (u : ModGL .E6 K) * signDiagE6 K thetaE6 = signDiagE6 K thetaE6 * (u : ModGL .E6 K)) :
    (u : ModGL .E6 K) ∈ h1E6 K := by
  have hcT : (u : ModGL .E6 K) ∈ toralCentralizer .E6 K (thetaDiag thetaE6 (-1 : Kˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨u.2, ?_⟩
    show signDiagE6 K thetaE6 * (u : ModGL .E6 K) * (signDiagE6 K thetaE6)⁻¹ = u
    rw [mul_inv_eq_iff_eq_mul, hu]
  exact toralRootGroup_le_h1E6 hK
    (toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inl rfl))) hK
      (thetaDiag_neg_one_sign_E6 thetaE6) hcT)

theorem map_conj_stdRankOne_theta_E6 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E6 K)}
    (hu : (u : ModGL .E6 K) * signDiagE6 K thetaE6 = signDiagE6 K thetaE6 * (u : ModGL .E6 K)) :
    (stdRankOne (e6AdjDatum K) thetaE6).map (MulAut.conj u).toMonoidHom =
      stdRankOne (e6AdjDatum K) thetaE6 := by
  have hu1 := mem_h1E6_of_commute_signDiagE6 hK hu
  have hu' : ((u⁻¹ : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈ h1E6 K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hu1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact conj_mem_stdRankOne_of_mem_h1E6 hu1 hr
  · intro hx
    refine ⟨u⁻¹ * x * u, ?_, ?_⟩
    · have := conj_mem_stdRankOne_of_mem_h1E6 hu' hx
      simpa using this
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

end Involutions

section Partner

theorem isPartnerE6_of_isPartner {p e : ℕ} [Fact p.Prime] {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (hp : IsPartner (e6Datum (GaloisField p e)).isFiniteType thetaE6 δ) :
    IsPartnerE6 δ := by
  obtain ⟨c, hc, hform⟩ := form_eq_iform_tag .E6 (e6Datum (GaloisField p e)).isFiniteType
  refine ⟨hδ, ?_⟩
  rw [IsPartner, lenSq, hform, hform] at hp
  have h3 : c * (2 * (iform thetaE6 δ : ℚ)) = c * (-2) := by
    have : (iform δ δ : ℚ) = 2 := by exact_mod_cast iform_self_isRoot_E6 hδ
    rw [this] at hp
    linear_combination hp
  have h4 := mul_left_cancel₀ hc.ne' h3
  have : (iform thetaE6 δ : ℚ) = -1 := by linarith
  exact_mod_cast this

end Partner

section KLevel

variable {p e : ℕ} [Fact p.Prime]

theorem map_stdRankOne_e6_root {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    (stdRankOne (e6Datum (GaloisField p e)) β).map (e6Isogeny (GaloisField p e)) =
      stdRankOne (e6AdjDatum (GaloisField p e)) β := by
  change ((e6Datum (GaloisField p e)).rootGroup β ⊔
      (e6Datum (GaloisField p e)).rootGroup (-β)).map (e6Isogeny (GaloisField p e)) =
    rootGroup (rootOperatorFamily .E6) (GaloisField p e) β ⊔
      rootGroup (rootOperatorFamily .E6) (GaloisField p e) (-β)
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_e6Isogeny_rootGroup _ hβ)
    (map_e6Isogeny_rootGroup _ (IsRoot.neg hβ))

theorem ker_e6Isogeny_le_center :
    (e6Isogeny (GaloisField p e)).ker ≤ Subgroup.center (E6sc p e) :=
  ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField p e))
    (e6Isogeny_ne_one (GaloisField p e))

theorem isLongestRoot_e6Datum (hadm : StatedLieAdmissible .E6 0 p e)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    ModelFacts.IsLongestRoot (e6Datum (GaloisField p e)) β :=
  isLongestRoot_of_mem_roots_of_forall_single _ rfl
    (fun k => isLongestRoot_single .E6 0 p e Fact.out trivial hadm k trivial)
    ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField p e)).2 hβ)

theorem stdRankOne_mem_longestFundamental_E6 (hadm : StatedLieAdmissible .E6 0 p e)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    stdRankOne (e6Datum (GaloisField p e)) β ∈ longestFundamental (e6Datum (GaloisField p e)) := by
  refine ⟨1, β, isLongestRoot_e6Datum hadm hβ, ?_⟩
  have : (MulAut.conj (1 : E6sc p e)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [this, Subgroup.map_id]
  rfl

theorem injOn_e6Isogeny_stdRankOne (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p e)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    ∀ x ∈ stdRankOne (e6Datum (GaloisField p e)) β,
      e6Isogeny (GaloisField p e) x = 1 → x = 1 := by
  classical
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .E6) trivial hadm
    (by decide) (by decide)
    (longestFundamental_subset .E6 _ (stdRankOne_mem_longestFundamental_E6 hadm hβ))
  obtain ⟨-, eβ, -⟩ :=
    (exceptional_Lang_root_rank_one_data .E6 (GaloisField p e) β).2.2.2.2.2.2.2.1 hK
  set R := stdRankOne (e6Datum (GaloisField p e)) β with hR
  let ψ : E6sc p e →* ModGL .E6 (GaloisField p e) :=
    (adjointGroup .E6 (GaloisField p e)).subtype.comp (e6Isogeny (GaloisField p e))
  have hψ : R.map ψ = rootRankOneGroup .E6 (GaloisField p e) β := by
    have hmap := map_stdRankOne_e6_root (p := p) (e := e) hβ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : e6Isogeny (GaloisField p e) x ∈ stdRankOne (e6AdjDatum (GaloisField p e)) β := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx
      obtain ⟨A, hA⟩ := (mem_stdRankOne_e6_iff' hβ _).1 hx'
      exact ⟨A, hA.symm⟩
    · rintro ⟨A, rfl⟩
      have hx' : (⟨rootSL2 .E6 (GaloisField p e) β A, rootSL2_mem_adjointGroup _ _⟩ :
          ↥(adjointGroup .E6 (GaloisField p e))) ∈
            stdRankOne (e6AdjDatum (GaloisField p e)) β :=
        (mem_stdRankOne_e6_iff' hβ _).2 ⟨A, rfl⟩
      rw [← hmap] at hx'
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hx'
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  let φ' : R →* ↥(rootRankOneGroup .E6 (GaloisField p e) β) :=
    (ψ.comp R.subtype).codRestrict _ (fun x => by
      have h := Subgroup.mem_map_of_mem ψ x.2
      rw [hψ] at h
      exact h)
  have hsurj : Function.Surjective φ' := fun y => by
    have hy : (y : ModGL .E6 (GaloisField p e)) ∈ R.map ψ := by
      rw [hψ]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφ' := injective_of_surjective_of_equiv_sl2 φ eβ.symm φ' hsurj
  intro x hx h1
  have e1 : ((φ' ⟨x, hx⟩ : ↥(rootRankOneGroup .E6 (GaloisField p e) β)) :
      ModGL .E6 (GaloisField p e)) = ψ x := rfl
  have e2 : ((φ' 1 : ↥(rootRankOneGroup .E6 (GaloisField p e) β)) :
      ModGL .E6 (GaloisField p e)) = 1 := by
    rw [map_one]
    rfl
  have h2 : ψ x = 1 := by
    show ((e6Isogeny (GaloisField p e) x : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) = 1
    rw [h1]
    rfl
  have : (⟨x, hx⟩ : R) = 1 := hφ' (Subtype.ext (e1.trans (h2.trans e2.symm)))
  exact congrArg Subtype.val this

theorem e6Isogeny_involution (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p e)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) {c : E6sc p e}
    (hc : c ∈ stdRankOne (e6Datum (GaloisField p e)) β) (ho : orderOf c = 2) :
    ((e6Isogeny (GaloisField p e) c : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) = signDiagE6 (GaloisField p e) β := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  obtain ⟨h1, h2⟩ := (orderOf_eq_prime_iff (p := 2)).1 ho
  have hmem : e6Isogeny (GaloisField p e) c ∈ stdRankOne (e6AdjDatum (GaloisField p e)) β := by
    rw [← map_stdRankOne_e6_root (p := p) (e := e) hβ]
    exact Subgroup.mem_map_of_mem _ hc
  refine eq_signDiagE6_of_orderOf_eq_two hK hβ hmem ?_
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, h1, map_one]
  · intro h
    exact h2 (injOn_e6Isogeny_stdRankOne hp2 hadm hβ c hc h)

theorem map_conj_map_e6 (g : E6sc p e) (S : Subgroup (E6sc p e)) :
    (S.map (MulAut.conj g).toMonoidHom).map (e6Isogeny (GaloisField p e)) =
      (S.map (e6Isogeny (GaloisField p e))).map
        (MulAut.conj (e6Isogeny (GaloisField p e) g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem eq_of_mem_longestFundamental_E6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .E6 0 p e)
    {R R' : Subgroup (E6sc p e)} (hR : R ∈ longestFundamental (e6Datum (GaloisField p e)))
    (hR' : R' ∈ longestFundamental (e6Datum (GaloisField p e)))
    {c c' : E6sc p e} (hc : c ∈ R) (hc' : c' ∈ R') (ho : orderOf c = 2) (ho' : orderOf c' = 2)
    (h : ((e6Isogeny (GaloisField p e) c : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) = e6Isogeny (GaloisField p e) c') : R = R' := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .E6 (e6Datum (GaloisField p e)) :=
    fundamentalSingleClass .E6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e6Datum (GaloisField p e)) thetaE6 ∈
      Generic.fundamentalSubgroups .E6 (e6Datum (GaloisField p e)) :=
    ⟨1, thetaE6, Or.inl (isLongestRoot_e6Datum hadm isRoot_thetaE6),
      (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R (longestFundamental_subset .E6 _ hR)
  obtain ⟨g', hg'⟩ := hsingle _ hθmem R' (longestFundamental_subset .E6 _ hR')
  have hd : g⁻¹ * c * g ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6 :=
    Generic.mem_conjSub_iff.1 (hg ▸ hc)
  have hd' : g'⁻¹ * c' * g' ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6 :=
    Generic.mem_conjSub_iff.1 (hg' ▸ hc')
  have ord : ∀ (y x : E6sc p e), orderOf x = 2 → orderOf (y⁻¹ * x * y) = 2 := fun y x hx => by
    rw [← hx]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective x
    simpa [MulAut.conj_apply] using this
  have z1 := e6Isogeny_involution hp2 hadm isRoot_thetaE6 hd (ord g c ho)
  have z1' := e6Isogeny_involution hp2 hadm isRoot_thetaE6 hd' (ord g' c' ho')
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at z1 z1'
  set gb := e6Isogeny (GaloisField p e) g with hgb
  set gb' := e6Isogeny (GaloisField p e) g' with hgb'
  have hcg : (e6Isogeny (GaloisField p e) c : ModGL .E6 (GaloisField p e)) =
      (gb : ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 *
        (gb : ModGL .E6 (GaloisField p e))⁻¹ := by
    rw [← z1]
    group
  have hcg' : (e6Isogeny (GaloisField p e) c' : ModGL .E6 (GaloisField p e)) =
      (gb' : ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 *
        (gb' : ModGL .E6 (GaloisField p e))⁻¹ := by
    rw [← z1']
    group
  have hu : (((gb'⁻¹ * gb : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e))) * signDiagE6 (GaloisField p e) thetaE6 =
      signDiagE6 (GaloisField p e) thetaE6 *
        (((gb'⁻¹ * gb : ↥(adjointGroup .E6 (GaloisField p e))) : ModGL .E6 (GaloisField p e))) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h2 := hcg.symm.trans (h.trans hcg')
    calc (↑gb')⁻¹ * ↑gb * signDiagE6 (GaloisField p e) thetaE6 =
        (↑gb')⁻¹ * (↑gb * signDiagE6 (GaloisField p e) thetaE6 * (↑gb)⁻¹) * ↑gb := by group
      _ = (↑gb')⁻¹ * (↑gb' * signDiagE6 (GaloisField p e) thetaE6 * (↑gb')⁻¹) * ↑gb := by rw [h2]
      _ = signDiagE6 (GaloisField p e) thetaE6 * ((↑gb')⁻¹ * ↑gb) := by group
  have hconj := map_conj_stdRankOne_theta_E6 hK hu
  have hRε : R.map (e6Isogeny (GaloisField p e)) =
      (stdRankOne (e6AdjDatum (GaloisField p e)) thetaE6).map (MulAut.conj gb).toMonoidHom := by
    rw [hg]
    show ((stdRankOne (e6Datum (GaloisField p e)) thetaE6).map
      (MulAut.conj g).toMonoidHom).map (e6Isogeny (GaloisField p e)) = _
    rw [map_conj_map_e6, map_stdRankOne_e6_root isRoot_thetaE6]
  have hRε' : R'.map (e6Isogeny (GaloisField p e)) =
      (stdRankOne (e6AdjDatum (GaloisField p e)) thetaE6).map (MulAut.conj gb').toMonoidHom := by
    rw [hg']
    show ((stdRankOne (e6Datum (GaloisField p e)) thetaE6).map
      (MulAut.conj g').toMonoidHom).map (e6Isogeny (GaloisField p e)) = _
    rw [map_conj_map_e6, map_stdRankOne_e6_root isRoot_thetaE6]
  have hmap : R.map (e6Isogeny (GaloisField p e)) = R'.map (e6Isogeny (GaloisField p e)) := by
    rw [hRε, hRε']
    have h3 : (MulAut.conj gb).toMonoidHom =
        (MulAut.conj gb').toMonoidHom.comp (MulAut.conj (gb'⁻¹ * gb)).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    rw [h3, ← Subgroup.map_map, hconj]
  exact eq_of_map_eq_of_isPerfect (e6Isogeny (GaloisField p e)) ker_e6Isogeny_le_center
    (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm hR)
    (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm hR') hmap

theorem conj_stdRankOne_theta_E6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .E6 0 p e) {u : E6sc p e}
    (hu : ((e6Isogeny (GaloisField p e) u : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 =
      signDiagE6 (GaloisField p e) thetaE6 *
        ((e6Isogeny (GaloisField p e) u : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e))) :
    (stdRankOne (e6Datum (GaloisField p e)) thetaE6).map (MulAut.conj u).toMonoidHom =
      stdRankOne (e6Datum (GaloisField p e)) thetaE6 := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hθ := stdRankOne_mem_longestFundamental_E6 hadm (p := p) (e := e) isRoot_thetaE6
  refine eq_of_map_eq_of_isPerfect (e6Isogeny (GaloisField p e)) ker_e6Isogeny_le_center
    (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm
      (map_conj_mem_longestFundamental u hθ))
    (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm hθ) ?_
  rw [map_conj_map_e6, map_stdRankOne_e6_root isRoot_thetaE6]
  exact map_conj_stdRankOne_theta_E6 hK hu

end KLevel

end CFSG.ClassicalInvolution.ModelFacts.Levi
