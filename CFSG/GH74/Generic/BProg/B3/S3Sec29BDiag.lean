module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29BBasic
public import CFSG.GH74.Generic.BProg.B3.S3Sec29BDiagAux

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

namespace S3Sec29BDiag

variable {G : Type} [Group G] [Finite G]

theorem ker_le_pPrimeCore {Cb I : Subgroup G} (hI : I ≤ Cb) :
    ((TwoThin.barMk ↥Cb).comp (Subgroup.inclusion hI)).ker ≤ pPrimeCore 2 ↥I := by
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥Cb)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hker : Odd (Nat.card ((TwoThin.barMk ↥Cb).comp (Subgroup.inclusion hI)).ker) := by
    have h : ¬ 2 ∣ Nat.card ((TwoThin.barMk ↥Cb).comp (Subgroup.inclusion hI)).ker :=
      B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hI) (Subgroup.inclusion_injective hI)
        (pPrimeCore 2 ↥Cb) hodd
    exact Nat.odd_iff.2 (by omega)
  exact le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hker⟩

theorem eq_one_of_center_eq_bot {Z : Type} [Group Z] {M : Subgroup Z} (hcen : center ↥M = ⊥)
    {z : Z} (hzM : z ∈ M) (hzc : ∀ c ∈ M, c * z = z * c) : z = 1 := by
  have hmem : (⟨z, hzM⟩ : ↥M) ∈ center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  rw [hcen, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end S3Sec29BDiag

theorem lemma296a {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29 G x K A B Q y b D J)
    (hI : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) (Ly29 K b))
    (hSL : HasSL2Model (↥(Ly29 K b) ⧸ pPrimeCore 2 ↥(Ly29 K b)) (fun q => Odd q ∧ 5 ≤ q)) :
    Ly29 K b ≤ cSec J := by
  classical
  by_contra hn
  obtain ⟨hb2, hJb, hbC⟩ := h.obs_data
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.2.2.1.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2 : orderOf x = 2 := h.circ.1.1.1.1
  obtain ⟨hAB, hxB, hBCx, hBel, -, -, hBeq⟩ := h.ext
  have hbx : b ∈ centralizer ({x} : Set G) := hBCx h.b_mem
  have hxb : x ∈ centralizer ({b} : Set G) := TwoThin.mem_centralizer_symm hbx
  set I : Subgroup G := Ly29 K b with hIdef
  have hIK : I ≤ K ⊓ centralizer ({b} : Set G) := hI.1
  have hIY : I ≤ centralizer ({b} : Set G) := hIK.trans inf_le_right
  have hIx : I ≤ centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G) :=
    hIK.trans (inf_le_inf_right _ hKC)
  have hID : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G)) I := by
    have hsubK : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
      obtain ⟨Kb, -, hsub, -⟩ := hK.2
      exact hsub
    have hsub : ((K ⊓ centralizer ({b} : Set G)).subgroupOf
        (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G))).IsSubnormal := by
      have h1 := TwoThin.isSubnormal_inf_subgroupOf hsubK
        (inf_le_left : centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G) ≤
          centralizer ({x} : Set G))
      have h2 : (K ⊓ centralizer ({b} : Set G)).subgroupOf
          (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G)) =
          K.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G)) := by
        ext m
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · exact fun hm => hm.1
        · intro hm
          exact ⟨hm, (Subgroup.mem_inf.1 m.2).2⟩
      rwa [h2]
    exact B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hKC) hsub hI
  have hso : orderOf (⟨x, hxb⟩ : ↥(centralizer ({b} : Set G))) = 2 :=
    TwoThin.orderOf_mk_centralizer hxb hx2
  have hΛC := TwoThin.le_centralizer_mk (Λ := I) hIx hxb
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hID hxb
  obtain ⟨-, -, L, hL, hcases, -, -, -⟩ := TwoThin.pumpupY_structure hso hΛC hΛ2
  have hJ' := TwoThin.isPCompIn_two_iff.1 hJb
  set barM : ↥(centralizer ({b} : Set G)) →* TwoThin.barQ ↥(centralizer ({b} : Set G)) :=
    TwoThin.barMk ↥(centralizer ({b} : Set G)) with hbarM
  set s : ↥(centralizer ({b} : Set G)) := ⟨x, hxb⟩ with hs
  set JY : Subgroup ↥(centralizer ({b} : Set G)) := J.subgroupOf (centralizer ({b} : Set G))
    with hJY
  have hM : IsComponent (JY.map barM) := TwoThin.isComponent_map_barMk hJ'.2
  set L' : Subgroup (TwoThin.barQ ↥(centralizer ({b} : Set G))) := conjSub (barM s)⁻¹ L with hL'
  have hL'c : IsComponent L' :=
    LocalCores.isComponent_map_mulEquiv (MulAut.conj (barM s)⁻¹) hL
  by_cases hcase : JY.map barM = L ∨ JY.map barM = L'
  swap
  ·
    push Not at hcase
    obtain ⟨hc1', hc2'⟩ := hcase
    have hc1 : ⁅JY.map barM, L⁆ = ⊥ := (distinct_components_commute hM hL).resolve_left hc1'
    have hc2 : ⁅JY.map barM, L'⁆ = ⊥ := (distinct_components_commute hM hL'c).resolve_left hc2'
    apply hn
    intro q hq
    have hqC : q ∈ centralizer ({b} : Set G) := hIY hq
    have hqΛ : (⟨q, hqC⟩ : ↥(centralizer ({b} : Set G))) ∈
        I.subgroupOf (centralizer ({b} : Set G)) := Subgroup.mem_subgroupOf.2 hq
    refine TwoThin.mem_centralizerSection_of_map_eq hJ'.1 hJ'.2 hqC ?_
    intro m hm
    have hm' : barM m ∈ JY.map barM := ⟨m, hm, rfl⟩
    have hz : barM ⟨q, hqC⟩ ∈ (I.subgroupOf (centralizer ({b} : Set G))).map barM :=
      ⟨_, hqΛ, rfl⟩
    have hcL : ∀ c ∈ L, c * barM m = barM m * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1) hm')
        c hc
    have hcL' : ∀ c ∈ L', c * barM m = barM m * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc2) hm')
        c hc
    have hcomm : barM ⟨q, hqC⟩ * barM m = barM m * barM ⟨q, hqC⟩ := by
      rcases hcases with ⟨-, hIL⟩ | ⟨-, hAB, hIsd⟩
      · exact hcL _ (hIL hz)
      · obtain ⟨l, hl⟩ := hIsd hz
        rw [← hl, swapDiag_apply]
        have h1 := hcL (l : TwoThin.barQ ↥(centralizer ({b} : Set G))) l.2
        have h2 := hcL' ((barM s)⁻¹ * (l : TwoThin.barQ ↥(centralizer ({b} : Set G))) * barM s)
          (conj_mem_conjSub l.2)
        calc ((l : TwoThin.barQ ↥(centralizer ({b} : Set G))) *
              ((barM s)⁻¹ * l * barM s)) * barM m
            = l * (((barM s)⁻¹ * l * barM s) * barM m) := by group
          _ = l * (barM m * ((barM s)⁻¹ * l * barM s)) := by rw [h2]
          _ = (l * barM m) * ((barM s)⁻¹ * l * barM s) := by group
          _ = (barM m * l) * ((barM s)⁻¹ * l * barM s) := by rw [h1]
          _ = barM m * (l * ((barM s)⁻¹ * l * barM s)) := by group
    rw [map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  ·
    obtain ⟨hdih, hsimp⟩ := S3Sec29BDiagAux.type_data h.type
    obtain ⟨e1⟩ := TwoThin.hat_equiv_subgroupOf hJ'.1
    have hsubJ : JY.IsSubnormal := by
      obtain ⟨Kb, -, hsub, -⟩ := hJb.2
      exact hsub
    obtain ⟨e2⟩ := TwoThin.hat_equiv_map (M := JY) hsubJ
    let eJ : (↥J ⧸ pPrimeCore 2 ↥J) ≃* ↥(JY.map barM) := e1.trans e2
    have hdihM : CFSG.GorensteinWalter.HasDihedralSylowTwo ↥(JY.map barM) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eJ.symm hdih
    have hsimpM : IsSimpleGroup ↥(JY.map barM) := (MulEquiv.isSimpleGroup_congr eJ).mp hsimp
    have hcenM : center ↥(JY.map barM) = ⊥ :=
      B1.center_eq_bot_of_simple_of_quasisimple hsimpM hM.1
    set ρ₀ : ↥I →* TwoThin.barQ ↥(centralizer ({b} : Set G)) :=
      barM.comp (Subgroup.inclusion hIY) with hρ₀
    have hρ₀mem : ∀ i : ↥I,
        ρ₀ i ∈ (I.subgroupOf (centralizer ({b} : Set G))).map barM := fun i =>
      ⟨⟨(i : G), hIY i.2⟩, Subgroup.mem_subgroupOf.2 i.2, rfl⟩
    have key : ∃ ρ : ↥I →* ↥(JY.map barM), ∀ i, ρ i = 1 → ρ₀ i = 1 := by
      rcases hcases with ⟨hLL, hIL⟩ | ⟨hLL, hAB, hIsd⟩
      · have hML : JY.map barM = L := by
          rcases hcase with h1 | h1
          · exact h1
          · rw [h1]
            exact hLL
        refine ⟨ρ₀.codRestrict _ (fun i => ?_), fun i hi => ?_⟩
        · rw [hML]
          exact hIL (hρ₀mem i)
        · have := congrArg Subtype.val hi
          simpa using this
      · set sd := swapDiag hAB with hsd
        have hLc : L ≤ centralizer (L' : Set (TwoThin.barQ ↥(centralizer ({b} : Set G)))) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 hAB
        have hL'c' : L' ≤ centralizer (L : Set (TwoThin.barQ ↥(centralizer ({b} : Set G)))) := by
          rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
          exact hAB
        have hsdinj : Function.Injective sd := by
          rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
          intro x' hx'
          have hxm := mem_inf_of_mem_ker_swapDiag hAB hx'
          obtain ⟨hxL, hxL'⟩ := Subgroup.mem_inf.1 hxm
          have h1 : (x' : TwoThin.barQ ↥(centralizer ({b} : Set G))) = 1 := by
            rcases hcase with hML | hML
            · refine S3Sec29BDiag.eq_one_of_center_eq_bot hcenM (hML ▸ hxL) fun c hc => ?_
              have hcL : c ∈ L := hML ▸ hc
              exact (Subgroup.mem_centralizer_iff.1 (hLc hcL) _ hxL').symm
            · refine S3Sec29BDiag.eq_one_of_center_eq_bot hcenM (hML ▸ hxL') fun c hc => ?_
              have hcL : c ∈ L' := hML ▸ hc
              exact (Subgroup.mem_centralizer_iff.1 (hL'c' hcL) _ hxL).symm
          exact Subtype.ext h1
        have hmem : ∀ i : ↥I, ρ₀ i ∈ sd.range := fun i => hIsd (hρ₀mem i)
        let τ : ↥I →* ↥L :=
          ((MonoidHom.ofInjective hsdinj).symm : ↥sd.range ≃* ↥L).toMonoidHom.comp
            (ρ₀.codRestrict sd.range hmem)
        have hτ : ∀ i, sd (τ i) = ρ₀ i := by
          intro i
          have h2 : MonoidHom.ofInjective hsdinj (τ i) = ⟨ρ₀ i, hmem i⟩ :=
            (MonoidHom.ofInjective hsdinj).apply_symm_apply ⟨ρ₀ i, hmem i⟩
          have h3 := congrArg Subtype.val h2
          rwa [MonoidHom.ofInjective_apply] at h3
        rcases hcase with hML | hML
        · refine ⟨(MulEquiv.subgroupCongr hML.symm).toMonoidHom.comp τ, fun i hi => ?_⟩
          have h1 : τ i = 1 :=
            (MulEquiv.subgroupCongr hML.symm).injective (hi.trans (map_one _).symm)
          rw [← hτ i, h1, map_one]
        · let cE : ↥L ≃* ↥L' := (MulAut.conj (barM s)⁻¹).subgroupMap L
          refine ⟨(MulEquiv.subgroupCongr hML.symm).toMonoidHom.comp
            (cE.toMonoidHom.comp τ), fun i hi => ?_⟩
          have h2 := (MulEquiv.subgroupCongr hML.symm).injective (hi.trans (map_one _).symm)
          have h1 : τ i = 1 := cE.injective (h2.trans (map_one cE).symm)
          rw [← hτ i, h1, map_one]
    obtain ⟨ρ, hρ⟩ := key
    obtain ⟨F, hF, hFin, ⟨hodd, h5⟩, ⟨eS⟩⟩ := hSL
    let e : (↥I ⧸ pPrimeCore 2 ↥I) ≃* SL(2, F) :=
      eS.trans (specialLinearGroupEquivStatedSL 2 F).symm
    have hcp : CharP F (ringChar F) := ringChar.charP F
    have hfact : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
    have hp2 : ringChar F ≠ 2 := by
      intro h2
      have : Fintype F := Fintype.ofFinite F
      have h3 := (FiniteField.even_card_iff_char_two (F := F)).mp h2
      rw [← Nat.card_eq_fintype_card] at h3
      have h4 := Nat.odd_iff.1 hodd
      omega
    exact S3Sec29BDiagAux.false_of_sl2_quotient hdihM (pPrimeCore 2 ↥I) hp2 e ρ
      (fun i hi => S3Sec29BDiag.ker_le_pPrimeCore hIY
        (MonoidHom.mem_ker.2 (hρ i (MonoidHom.mem_ker.1 hi))))

end CFSG.GH74.Generic.BProg.B3
