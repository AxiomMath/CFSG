module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Form
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Factor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits

section RankOne

variable {K : Type} [Field K]

theorem mem_stdRankOne_e7_iff' {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (r : ↥(adjointGroup .E7 K)) :
    r ∈ stdRankOne (e7AdjDatum K) β ↔
      ∃ A : SL2 K, (r : ModGL .E7 K) = rootSL2 .E7 K β A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .E7) hβ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E7 K hβ).1
  change r ∈ rootGroup (rootOperatorFamily .E7) K β ⊔
    rootGroup (rootOperatorFamily .E7) K (-β) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem rootSL2_HSL_eq_thetaDiag_E7 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : Kˣ) :
    rootSL2 .E7 K β (HSL c) = rootDiagUnit .E7 (thetaDiag β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E7 K hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  change rootTorusSL2 .E7 K β c = _
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E7 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E7 a : ModGL .E7 K) : Module.End K (RootModule .E7 K))
      (rootVec .E7 K (Pi.single i 1))) = ((a i : Kˣ) : K) • rootVec .E7 K (Pi.single i 1) := by
    change rootDiag a (rootVec .E7 K (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E7 i), hs]
  rw [h2] at h1
  have hne : rootVec .E7 K (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E7 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective K hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_isRoot_E7 hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

end RankOne

section Involutions

variable {K : Type} [Field K]

theorem eq_signDiagE7_of_orderOf_eq_two (hK : ringChar K ≠ 2) {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : IsRoot .E7 β) {c : ↥(adjointGroup .E7 K)}
    (hc : c ∈ stdRankOne (e7AdjDatum K) β) (hc2 : orderOf c = 2) :
    (c : ModGL .E7 K) = signDiagE7 K β := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hinj : Function.Injective (rootSL2 .E7 K β) :=
    ((exceptional_Lang_root_rank_one_data .E7 K β).2.2.2.2.2.2.2.1 hK).1
  obtain ⟨A, hA⟩ := (mem_stdRankOne_e7_iff' hβ c).1 hc
  obtain ⟨hc1, hne⟩ := (orderOf_eq_prime_iff (p := 2)).1 hc2
  have hAA : A * A = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hA]
    have := congrArg (fun x : ↥(adjointGroup .E7 K) => (x : ModGL .E7 K)) hc1
    simpa [sq] using this
  rcases sl2_sq_eq_one_A2 h2 hAA with rfl | rfl
  · exfalso
    apply hne
    exact Subtype.ext (by rw [hA, map_one]; rfl)
  · rw [hA]
    exact rootSL2_HSL_eq_thetaDiag_E7 hβ (-1)

theorem signDiagE7_mem_stdRankOne {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    (⟨signDiagE7 K β, by
        rw [signDiagE7, ← rootSL2_HSL_eq_thetaDiag_E7 hβ (-1)]
        exact rootSL2_mem_adjointGroup _ _⟩ : ↥(adjointGroup .E7 K)) ∈
      stdRankOne (e7AdjDatum K) β :=
  (mem_stdRankOne_e7_iff' hβ _).2 ⟨HSL (-1), (rootSL2_HSL_eq_thetaDiag_E7 hβ (-1)).symm⟩

theorem conj_mem_stdRankOne_of_mem_h1E7 {g : ↥(adjointGroup .E7 K)}
    (hg : (g : ModGL .E7 K) ∈ h1E7 K) {x : ↥(adjointGroup .E7 K)}
    (hx : x ∈ stdRankOne (e7AdjDatum K) thetaE7) :
    g * x * g⁻¹ ∈ stdRankOne (e7AdjDatum K) thetaE7 := by
  obtain ⟨B, hB⟩ := (mem_stdRankOne_e7_iff' isRoot_thetaE7 x).1 hx
  obtain ⟨n, hn, A, hgA⟩ := hg
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E7 hn (A * B * A⁻¹)
  refine (mem_stdRankOne_e7_iff' isRoot_thetaE7 _).2 ⟨A', ?_⟩
  rw [← hA']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgA, hB, map_mul, map_inv]
  group

theorem mem_h1E7_of_commute_signDiagE7 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E7 K)}
    (hu : (u : ModGL .E7 K) * signDiagE7 K thetaE7 = signDiagE7 K thetaE7 * (u : ModGL .E7 K)) :
    (u : ModGL .E7 K) ∈ h1E7 K := by
  have hcT : (u : ModGL .E7 K) ∈ toralCentralizer .E7 K (thetaDiag thetaE7 (-1 : Kˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨u.2, ?_⟩
    show signDiagE7 K thetaE7 * (u : ModGL .E7 K) * (signDiagE7 K thetaE7)⁻¹ = u
    rw [mul_inv_eq_iff_eq_mul, hu]
  exact toralRootGroup_le_h1E7 hK
    (toralCentralizer_le_toralRootGroup_thetaE7 hK hcT)

theorem map_conj_stdRankOne_theta_E7 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E7 K)}
    (hu : (u : ModGL .E7 K) * signDiagE7 K thetaE7 = signDiagE7 K thetaE7 * (u : ModGL .E7 K)) :
    (stdRankOne (e7AdjDatum K) thetaE7).map (MulAut.conj u).toMonoidHom =
      stdRankOne (e7AdjDatum K) thetaE7 := by
  have hu1 := mem_h1E7_of_commute_signDiagE7 hK hu
  have hu' : ((u⁻¹ : ↥(adjointGroup .E7 K)) : ModGL .E7 K) ∈ h1E7 K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hu1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact conj_mem_stdRankOne_of_mem_h1E7 hu1 hr
  · intro hx
    refine ⟨u⁻¹ * x * u, ?_, ?_⟩
    · have := conj_mem_stdRankOne_of_mem_h1E7 hu' hx
      simpa using this
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

end Involutions

section Partner

theorem isPartnerE7_of_isPartner {p e : ℕ} [Fact p.Prime] {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : IsRoot .E7 δ) (hp : IsPartner (e7Datum (GaloisField p e)).isFiniteType thetaE7 δ) :
    IsPartnerE7 δ := by
  obtain ⟨c, hc, hform⟩ := form_eq_iform_tag .E7 (e7Datum (GaloisField p e)).isFiniteType
  refine ⟨hδ, ?_⟩
  rw [IsPartner, lenSq, hform, hform] at hp
  have h3 : c * (2 * (iform thetaE7 δ : ℚ)) = c * (-2) := by
    have : (iform δ δ : ℚ) = 2 := by exact_mod_cast iform_self_isRoot_E7 hδ
    rw [this] at hp
    linear_combination hp
  have h4 := mul_left_cancel₀ hc.ne' h3
  have : (iform thetaE7 δ : ℚ) = -1 := by linarith
  exact_mod_cast this

end Partner

section KLevel

variable {p e : ℕ} [Fact p.Prime]

theorem map_stdRankOne_e7_root {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    (stdRankOne (e7Datum (GaloisField p e)) β).map (e7Isogeny (GaloisField p e)) =
      stdRankOne (e7AdjDatum (GaloisField p e)) β := by
  change ((e7Datum (GaloisField p e)).rootGroup β ⊔
      (e7Datum (GaloisField p e)).rootGroup (-β)).map (e7Isogeny (GaloisField p e)) =
    rootGroup (rootOperatorFamily .E7) (GaloisField p e) β ⊔
      rootGroup (rootOperatorFamily .E7) (GaloisField p e) (-β)
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_e7Isogeny_rootGroup _ hβ)
    (map_e7Isogeny_rootGroup _ (IsRoot.neg hβ))

theorem ker_e7Isogeny_le_center :
    (e7Isogeny (GaloisField p e)).ker ≤ Subgroup.center (E7sc p e) :=
  ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField p e))
    (exists_e7Isogeny_ne_one (GaloisField p e))

theorem isLongestRoot_e7Datum (hadm : StatedLieAdmissible .E7 0 p e)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ModelFacts.IsLongestRoot (e7Datum (GaloisField p e)) β :=
  isLongestRoot_of_mem_roots_of_forall_single _ rfl
    (fun k => isLongestRoot_single .E7 0 p e Fact.out trivial hadm k trivial)
    ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p e)).2 hβ)

theorem stdRankOne_mem_longestFundamental_E7 (hadm : StatedLieAdmissible .E7 0 p e)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    stdRankOne (e7Datum (GaloisField p e)) β ∈ longestFundamental (e7Datum (GaloisField p e)) := by
  refine ⟨1, β, isLongestRoot_e7Datum hadm hβ, ?_⟩
  have : (MulAut.conj (1 : E7sc p e)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [this, Subgroup.map_id]
  rfl

theorem injOn_e7Isogeny_stdRankOne (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E7 0 p e)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ∀ x ∈ stdRankOne (e7Datum (GaloisField p e)) β,
      e7Isogeny (GaloisField p e) x = 1 → x = 1 := by
  classical
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .E7) trivial hadm
    (by decide) (by decide)
    (longestFundamental_subset .E7 _ (stdRankOne_mem_longestFundamental_E7 hadm hβ))
  obtain ⟨-, eβ, -⟩ :=
    (exceptional_Lang_root_rank_one_data .E7 (GaloisField p e) β).2.2.2.2.2.2.2.1 hK
  set R := stdRankOne (e7Datum (GaloisField p e)) β with hR
  let ψ : E7sc p e →* ModGL .E7 (GaloisField p e) :=
    (adjointGroup .E7 (GaloisField p e)).subtype.comp (e7Isogeny (GaloisField p e))
  have hψ : R.map ψ = rootRankOneGroup .E7 (GaloisField p e) β := by
    have hmap := map_stdRankOne_e7_root (p := p) (e := e) hβ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : e7Isogeny (GaloisField p e) x ∈ stdRankOne (e7AdjDatum (GaloisField p e)) β := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx
      obtain ⟨A, hA⟩ := (mem_stdRankOne_e7_iff' hβ _).1 hx'
      exact ⟨A, hA.symm⟩
    · rintro ⟨A, rfl⟩
      have hx' : (⟨rootSL2 .E7 (GaloisField p e) β A, rootSL2_mem_adjointGroup _ _⟩ :
          ↥(adjointGroup .E7 (GaloisField p e))) ∈
            stdRankOne (e7AdjDatum (GaloisField p e)) β :=
        (mem_stdRankOne_e7_iff' hβ _).2 ⟨A, rfl⟩
      rw [← hmap] at hx'
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hx'
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  let φ' : R →* ↥(rootRankOneGroup .E7 (GaloisField p e) β) :=
    (ψ.comp R.subtype).codRestrict _ (fun x => by
      have h := Subgroup.mem_map_of_mem ψ x.2
      rw [hψ] at h
      exact h)
  have hsurj : Function.Surjective φ' := fun y => by
    have hy : (y : ModGL .E7 (GaloisField p e)) ∈ R.map ψ := by
      rw [hψ]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφ' := injective_of_surjective_of_equiv_sl2 φ eβ.symm φ' hsurj
  intro x hx h1
  have e1 : ((φ' ⟨x, hx⟩ : ↥(rootRankOneGroup .E7 (GaloisField p e) β)) :
      ModGL .E7 (GaloisField p e)) = ψ x := rfl
  have e2 : ((φ' 1 : ↥(rootRankOneGroup .E7 (GaloisField p e) β)) :
      ModGL .E7 (GaloisField p e)) = 1 := by
    rw [map_one]
    rfl
  have h2 : ψ x = 1 := by
    show ((e7Isogeny (GaloisField p e) x : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) = 1
    rw [h1]
    rfl
  have : (⟨x, hx⟩ : R) = 1 := hφ' (Subtype.ext (e1.trans (h2.trans e2.symm)))
  exact congrArg Subtype.val this

theorem e7Isogeny_involution (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E7 0 p e)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) {c : E7sc p e}
    (hc : c ∈ stdRankOne (e7Datum (GaloisField p e)) β) (ho : orderOf c = 2) :
    ((e7Isogeny (GaloisField p e) c : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) = signDiagE7 (GaloisField p e) β := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  obtain ⟨h1, h2⟩ := (orderOf_eq_prime_iff (p := 2)).1 ho
  have hmem : e7Isogeny (GaloisField p e) c ∈ stdRankOne (e7AdjDatum (GaloisField p e)) β := by
    rw [← map_stdRankOne_e7_root (p := p) (e := e) hβ]
    exact Subgroup.mem_map_of_mem _ hc
  refine eq_signDiagE7_of_orderOf_eq_two hK hβ hmem ?_
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, h1, map_one]
  · intro h
    exact h2 (injOn_e7Isogeny_stdRankOne hp2 hadm hβ c hc h)

theorem map_conj_map_e7 (g : E7sc p e) (S : Subgroup (E7sc p e)) :
    (S.map (MulAut.conj g).toMonoidHom).map (e7Isogeny (GaloisField p e)) =
      (S.map (e7Isogeny (GaloisField p e))).map
        (MulAut.conj (e7Isogeny (GaloisField p e) g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem eq_of_mem_longestFundamental_E7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .E7 0 p e)
    {R R' : Subgroup (E7sc p e)} (hR : R ∈ longestFundamental (e7Datum (GaloisField p e)))
    (hR' : R' ∈ longestFundamental (e7Datum (GaloisField p e)))
    {c c' : E7sc p e} (hc : c ∈ R) (hc' : c' ∈ R') (ho : orderOf c = 2) (ho' : orderOf c' = 2)
    (h : ((e7Isogeny (GaloisField p e) c : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) = e7Isogeny (GaloisField p e) c') : R = R' := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .E7 (e7Datum (GaloisField p e)) :=
    fundamentalSingleClass .E7 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e7Datum (GaloisField p e)) thetaE7 ∈
      Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField p e)) :=
    ⟨1, thetaE7, Or.inl (isLongestRoot_e7Datum hadm isRoot_thetaE7),
      (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R (longestFundamental_subset .E7 _ hR)
  obtain ⟨g', hg'⟩ := hsingle _ hθmem R' (longestFundamental_subset .E7 _ hR')
  have hd : g⁻¹ * c * g ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7 :=
    Generic.mem_conjSub_iff.1 (hg ▸ hc)
  have hd' : g'⁻¹ * c' * g' ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7 :=
    Generic.mem_conjSub_iff.1 (hg' ▸ hc')
  have ord : ∀ (y x : E7sc p e), orderOf x = 2 → orderOf (y⁻¹ * x * y) = 2 := fun y x hx => by
    rw [← hx]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective x
    simpa [MulAut.conj_apply] using this
  have z1 := e7Isogeny_involution hp2 hadm isRoot_thetaE7 hd (ord g c ho)
  have z1' := e7Isogeny_involution hp2 hadm isRoot_thetaE7 hd' (ord g' c' ho')
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at z1 z1'
  set gb := e7Isogeny (GaloisField p e) g with hgb
  set gb' := e7Isogeny (GaloisField p e) g' with hgb'
  have hcg : (e7Isogeny (GaloisField p e) c : ModGL .E7 (GaloisField p e)) =
      (gb : ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 *
        (gb : ModGL .E7 (GaloisField p e))⁻¹ := by
    rw [← z1]
    group
  have hcg' : (e7Isogeny (GaloisField p e) c' : ModGL .E7 (GaloisField p e)) =
      (gb' : ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 *
        (gb' : ModGL .E7 (GaloisField p e))⁻¹ := by
    rw [← z1']
    group
  have hu : (((gb'⁻¹ * gb : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e))) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        (((gb'⁻¹ * gb : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e))) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h2 := hcg.symm.trans (h.trans hcg')
    calc (↑gb')⁻¹ * ↑gb * signDiagE7 (GaloisField p e) thetaE7 =
        (↑gb')⁻¹ * (↑gb * signDiagE7 (GaloisField p e) thetaE7 * (↑gb)⁻¹) * ↑gb := by group
      _ = (↑gb')⁻¹ * (↑gb' * signDiagE7 (GaloisField p e) thetaE7 * (↑gb')⁻¹) * ↑gb := by rw [h2]
      _ = signDiagE7 (GaloisField p e) thetaE7 * ((↑gb')⁻¹ * ↑gb) := by group
  have hconj := map_conj_stdRankOne_theta_E7 hK hu
  have hRε : R.map (e7Isogeny (GaloisField p e)) =
      (stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7).map (MulAut.conj gb).toMonoidHom := by
    rw [hg]
    show ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map
      (MulAut.conj g).toMonoidHom).map (e7Isogeny (GaloisField p e)) = _
    rw [map_conj_map_e7, map_stdRankOne_e7_root isRoot_thetaE7]
  have hRε' : R'.map (e7Isogeny (GaloisField p e)) =
      (stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7).map (MulAut.conj gb').toMonoidHom := by
    rw [hg']
    show ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map
      (MulAut.conj g').toMonoidHom).map (e7Isogeny (GaloisField p e)) = _
    rw [map_conj_map_e7, map_stdRankOne_e7_root isRoot_thetaE7]
  have hmap : R.map (e7Isogeny (GaloisField p e)) = R'.map (e7Isogeny (GaloisField p e)) := by
    rw [hRε, hRε']
    have h3 : (MulAut.conj gb).toMonoidHom =
        (MulAut.conj gb').toMonoidHom.comp (MulAut.conj (gb'⁻¹ * gb)).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    rw [h3, ← Subgroup.map_map, hconj]
  exact eq_of_map_eq_of_isPerfect (e7Isogeny (GaloisField p e)) ker_e7Isogeny_le_center
    (commutator_eq_of_mem_longestFundamental (t := .E7) hp2 hq trivial hadm hR)
    (commutator_eq_of_mem_longestFundamental (t := .E7) hp2 hq trivial hadm hR') hmap

theorem conj_stdRankOne_theta_E7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .E7 0 p e) {u : E7sc p e}
    (hu : ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e))) :
    (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (MulAut.conj u).toMonoidHom =
      stdRankOne (e7Datum (GaloisField p e)) thetaE7 := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hθ := stdRankOne_mem_longestFundamental_E7 hadm (p := p) (e := e) isRoot_thetaE7
  refine eq_of_map_eq_of_isPerfect (e7Isogeny (GaloisField p e)) ker_e7Isogeny_le_center
    (commutator_eq_of_mem_longestFundamental (t := .E7) hp2 hq trivial hadm
      (map_conj_mem_longestFundamental u hθ))
    (commutator_eq_of_mem_longestFundamental (t := .E7) hp2 hq trivial hadm hθ) ?_
  rw [map_conj_map_e7, map_stdRankOne_e7_root isRoot_thetaE7]
  exact map_conj_stdRankOne_theta_E7 hK hu

end KLevel

end CFSG.ClassicalInvolution.ModelFacts.Levi
