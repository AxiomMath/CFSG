module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Normal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSocle
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ERowO

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.HarrisLit.Hin
open GrSLit.L34Facts

theorem assembly_isSubnormal_iff {G : Type*} [Group G] {K H : Subgroup G} (hKH : K ≤ H) :
    Assembly.IsSubnormal K H ↔ (K.subgroupOf H).IsSubnormal :=
  Assembly.IsSubnormal.iff_subgroupOf hKH

theorem isTwoComponentIn_of_isComponentOf {G : Type*} [Group G] [Finite G] {J A : Subgroup G}
    (hJ : Assembly.IsComponentOf J A) (h2 : Even (Nat.card J)) : IsTwoComponentIn J A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := (isComponentOf_iff_isComponent_subgroupOf hJ.1).mp hJ
  refine (isTwoComponentIn_iff hJ.1).mpr
    (isPComponent_of_isComponent_of_not_le 2 hK fun hle => ?_)
  have hcard : Nat.card ↥(J.subgroupOf A) = Nat.card J :=
    Nat.card_congr (subgroupOfEquivOfLe hJ.1).toEquiv
  have hdvd : Nat.card ↥(J.subgroupOf A) ∣ Nat.card ↥(pPrimeCore 2 ↥A) :=
    Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl ((even_iff_two_dvd.mp h2).trans hdvd)
    (pPrimeCore_coprime_card (p := 2) (G := ↥A))

variable {Y : Type} [Group Y]

theorem isTwoComponentIn_map_conj_of_normal (hZ : center Y = ⊥) {τ : MulAut Y}
    {L : Subgroup Y} (hL : IsTwoComponentIn L (fixedPoints τ))
    (hLn : ∀ c ∈ fixedPoints τ, ∀ l ∈ L, c * l * c⁻¹ ∈ L) :
    IsTwoComponentIn (L.map (MulAut.conj : Y →* MulAut Y))
      (centralizer ({τ} : Set (MulAut Y))) := by
  set L' := L.map (MulAut.conj : Y →* MulAut Y)
  set W := (MulAut.conj : Y →* MulAut Y).range
  set CA := centralizer ({τ} : Set (MulAut Y))
  have hL'CA : L' ≤ CA := by
    rintro _ ⟨l, hl, rfl⟩
    exact (conj_mem_centralizer_iff hZ τ l).mpr (hL.1 hl)
  have hL'W : L' ≤ W := map_le_range _ _
  have hn1 : (L'.subgroupOf (W ⊓ CA)).Normal := by
    rw [normal_subgroupOf_iff (le_inf hL'W hL'CA)]
    rintro _ k ⟨l, hl, rfl⟩ ⟨⟨y, rfl⟩, hy⟩
    have hyC : y ∈ fixedPoints τ := (conj_mem_centralizer_iff hZ τ y).mp hy
    refine ⟨y * l * y⁻¹, hLn y hyC l hl, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hn2 : ((W ⊓ CA).subgroupOf CA).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    rintro h k ⟨hW, hCA⟩ hk
    exact ⟨(OuterAutomorphisms.inner_normal Y).conj_mem h hW k,
      CA.mul_mem (CA.mul_mem hk hCA) (CA.inv_mem hk)⟩
  have hsn : Assembly.IsSubnormal L' CA :=
    .step (le_inf hL'W hL'CA) hn1 (.step inf_le_right hn2 (.refl CA))
  exact ⟨hL'CA, (assembly_isSubnormal_iff hL'CA).mp hsn, isTwoQuasisimple_of_mulEquiv
    (L.equivMapOfInjective _ (conj_injective_of_center hZ)) hL.2.2⟩

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem false_of_twin (h : Config G p m τ K) {P : Type*} [Group P]
    {ρ : MulAut (G ⧸ center G) →* MulAut P} (hinj : Function.Injective ρ)
    (hF : generalizedFitting (MulAut (G ⧸ center G)) =
      (MulAut.conj : G ⧸ center G →* MulAut (G ⧸ center G)).range)
    (hCW : (generalizedFitting (MulAut (G ⧸ center G)) ⊓
        centralizer ({quotAut τ} : Set (MulAut (G ⧸ center G)))).map ρ =
      OuterAutomorphisms.inner P ⊓ centralizer {ρ (quotAut τ)})
    {J : Subgroup (MulAut P)}
    (hJ : Assembly.IsComponentOf J (OuterAutomorphisms.inner P ⊓ centralizer {ρ (quotAut τ)}))
    (hev : Even (Nat.card J))
    (hne : J ≠ ((K.map (QuotientGroup.mk' (center G))).map
      (MulAut.conj : G ⧸ center G →* MulAut (G ⧸ center G))).map ρ) : False := by
  have := h.simple_bar
  have hcj := conj_injective_of_center (CatLeaf.center_eq_bot_of_simple h.nonabelian_bar)
  have hJr : OuterAutomorphisms.inner P ⊓ centralizer {ρ (quotAut τ)} ≤ ρ.range := by
    rw [← hCW]
    exact map_le_range _ _
  have hJ₁ := OddClassSelector.isComponentOf_comap_of_le_range ρ hinj hJ hJr
  rw [← hCW, comap_map_eq_self_of_injective hinj, hF] at hJ₁
  obtain ⟨hJ₀, hJ₀map⟩ := OddClassSelector.isComponentOf_comap_conj hcj hJ₁
  have hcard : Nat.card ↥((J.comap ρ).comap MulAut.conj) = Nat.card ↥J := by
    rw [← Subgroup.card_map_of_injective hcj, hJ₀map, ← Subgroup.card_map_of_injective hinj,
      map_comap_eq_self (hJ.1.trans hJr)]
  have heq := h.eq_bar (isTwoComponentIn_of_isComponentOf hJ₀ (by rw [hcard]; exact hev))
  apply hne
  have h1 : J.comap ρ = (K.map (QuotientGroup.mk' (center G))).map MulAut.conj := by
    rw [← hJ₀map, heq]
  rw [← h1, map_comap_eq_self (hJ.1.trans hJr)]

theorem eq_of_psl4 (h : Config G p m τ K) {k : ℕ}
    (hL : Blueprint.LieModel (G ⧸ center G) .PSL 4 p k) : m = 2 * k := by
  classical
  have := h.simple_bar
  have hnab := h.nonabelian_bar
  have := finite_mulAut (Y := G ⧸ center G)
  obtain ⟨eW, hWn, -, -, hWC, -⟩ := autSocle hnab
  have := hWn
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  obtain ⟨⟨-, he, -⟩, F, _, _, hkF, ⟨φ₀⟩⟩ := statedClassicalModel_of_lieModel' (.inl rfl) hL
  let φ : ↥(generalizedFitting (MulAut (G ⧸ center G))) ≃* projectiveSL 4 F :=
    eW.symm.trans (φ₀.trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F)))
  have hZP := OddSelector.center_projectiveSL_eq_bot (k := F) (by norm_num : 3 ≤ 4)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hWC φ hZP
  set σ := quotAut τ with hσ
  set Kb := K.map (QuotientGroup.mk' (center G)) with hKb
  set X := Kb.map (MulAut.conj : G ⧸ center G →* MulAut (G ⧸ center G)) with hX
  have hcj := conj_injective_of_center hZ
  have hKc := h.isTwoComponentIn_bar
  have hconj : ∀ c ∈ fixedPoints σ, ∀ l ∈ Kb, c * l * c⁻¹ ∈ Kb := by
    intro c hc l hl
    have h1 := h.bar_normal.conj_mem ⟨l, hKc.1 hl⟩ (by rw [mem_subgroupOf]; exact hl) ⟨c, hc⟩
    rw [mem_subgroupOf] at h1
    exact h1
  have hXt := isTwoComponentIn_map_conj_of_normal hZ hKc hconj
  have hXF : X ≤ generalizedFitting (MulAut (G ⧸ center G)) := hF ▸ map_le_range _ _
  have hXp : IsPComponent 2 (X.subgroupOf (centralizer ({σ} : Set (MulAut (G ⧸ center G))))) :=
    (isTwoComponentIn_iff hXt.1).mp hXt
  have hXm : Blueprint.LieModel (↥X ⧸ pPrimeCore 2 ↥X) .PSL 2 p m :=
    GSThmB.OddQuot.lieModel_of_equiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (Kb.equivMapOfInjective _ hcj)) h.lieModel_bar
  have h5 : 5 ≤ p ^ m := by have := h.seven_le; omega
  obtain ⟨hcore, hcase⟩ := GSThmB.Catalog7L4M.psl4_component_type hWC h.prime h.ne_two he hkF
    φ hinj hρW h.orderOf_bar hXF hXt.1 hXp h.prime h.ne_two h5 hXm
  rcases hcase with ⟨hsq, -⟩ | ⟨-, -, A, hρA, hAT, ψ, hψ, -⟩
  · rw [hkF, ← pow_mul] at hsq
    have := Nat.pow_right_injective h.prime.two_le hsq
    omega
  exfalso
  have hXC : Assembly.IsComponentOf X (centralizer ({σ} : Set (MulAut (G ⧸ center G)))) := by
    have hq : IsQuasisimple ↥X := LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot) hXt.2.2.2
    exact ⟨hXt.1, (assembly_isSubnormal_iff hXt.1).mpr hXt.2.1,
      (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq⟩
  obtain ⟨-, -, hCW, hL₁⟩ := OddSelector.socle_images φ hinj hρW hXF hXC
  have hsplit : ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm A⁻¹ x = 0 := by
    obtain ⟨S, hS, hS0⟩ := Catalog7L4E.exists_singular_plane ψ
    refine ⟨S, hS, fun x hx => ?_⟩
    rw [CatalogueBLinearHigherB.matrixQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
      CatalogueBLinearHigherB.matrixForm_apply, hψ x, hS0 x hx]
  obtain ⟨J, hJ, hJne, ⟨eJ⟩⟩ := exists_twin_component h.prime h.ne_two he hkF hL₁ hρA hAT hsplit
  have hFodd : Odd (Nat.card F) := by rw [hkF]; exact (h.prime.odd_of_ne_two h.ne_two).pow
  refine h.false_of_twin hinj hF hCW hJ ?_ hJne
  rw [Nat.card_congr eJ.toEquiv, GSThmB.Catalog7Std.card_psl2_of_odd hFodd rfl]
  exact even_mul_sq_sub_div_two hFodd

end Config

end CFSG.ComponentClassification.HarrisLit.N36
