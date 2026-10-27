module

public import CFSG.GH74.Generic.S3.LyB2Block
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.BenderSuzuki.MatrixGroups
  Subgroup CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

theorem false_of_exc_in_sl2
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {L : Type} [Group L]
    (e : L ≃* SL(2, F)) (P : Subgroup L) {K₀ : Type} [Group K₀] (hK₀ : IsExcB2 K₀)
    (φ : ↥P →* K₀) (hφ : Function.Surjective φ) : False := by
  let ρ : L →* PSL2MatrixGroup F :=
    (QuotientGroup.mk' (center SL(2, F))).comp e.toMonoidHom
  refine false_of_exc_quotient hodd ρ ?_ P hK₀ φ hφ
  intro g hg
  have h1 : e g ∈ center SL(2, F) := (QuotientGroup.eq_one_iff _).1 hg
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro h
  apply e.injective
  simpa using h1 (e h)

theorem closure_exc
    {G : Type} [Group G] [Finite G] (hgen : Gen4 G) (hKP : IsKProperSimple G)
    (hKG : TwoThinKGroupFactQ Gen4Cen) (hG2 : G2Table G)
    {x : G} {K : Subgroup G} {x' : G} {K' : Subgroup G} (hP : IsB2Pair x K)
    (hExc : ¬ HasSL2Model (↥K ⧸ pPrimeCore 2 ↥K) Odd) (hlt : PumpUpLT 2 x K x' K')
    (htype : x ∈ K ∨ x' ∈ K) :
    InB2 (↥K' ⧸ pPrimeCore 2 ↥K') ∧ ¬ HasSL2Model (↥K' ⧸ pPrimeCore 2 ↥K') Odd := by
  have hKB : InB2 (↥K ⧸ pPrimeCore 2 ↥K) := hP.2
  have hExcK : IsExcB2 (↥K ⧸ pPrimeCore 2 ↥K) := ⟨hKB, hExc⟩
  obtain ⟨⟨hxo, -, hKc⟩, ⟨hx'o, -, -⟩, hx'x, hx'K, hK'p⟩ := hlt
  obtain ⟨Λ, hΛX, hΛlay, -, -, hΛW, h2el, hcovΛ⟩ := pumpup_cover hx'o hKc hx'K
  have hxY : x ∈ centralizer ({x'} : Set G) := mem_centralizer_symm hx'x
  set Y' := centralizer ({x'} : Set G) with hY'
  have hso : orderOf (⟨x, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛlay hΛE hK'p
  have himg := (hiff _ hK'2).mp hK'J
  have hΛK : Λ ≤ K := hΛX.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛX.trans inf_le_right
  let e : ↥(Λ.subgroupOf Y') ≃* ↥Λ := Subgroup.subgroupOfEquivOfLe hΛY
  let ψ : ↥(Λ.subgroupOf Y') →* (↥K ⧸ pPrimeCore 2 ↥K) := (hatMap hΛK).comp e.toMonoidHom
  have hψs : Function.Surjective ψ := (hatMap_surjective hΛK hcovΛ).comp e.surjective
  have hψo : Odd (Nat.card ψ.ker) := by
    have h1 : ψ.ker = (hatMap hΛK).ker.comap e.toMonoidHom := (MonoidHom.comap_ker _ _).symm
    rw [h1]
    exact (odd_card_ker_hatMap hΛK).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ e.injective)
  let ρ : ↥(Λ.subgroupOf Y') →* ↥((Λ.subgroupOf Y').map (barMk ↥Y')) :=
    ((barMk ↥Y').comp (Λ.subgroupOf Y').subtype).codRestrict _ fun l => ⟨l, l.2, rfl⟩
  have hρs : Function.Surjective ρ := by
    intro k
    obtain ⟨c, hc, hck⟩ := k.2
    exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
  have hρo : Odd (Nat.card ρ.ker) := by
    have h1 : ρ.ker = ((barMk ↥Y').domRestrict (Λ.subgroupOf Y')).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [h1]
    exact OddKernel.odd_card_restriction_kernel (barMk ↥Y') odd_card_ker_barMk _
  have hker : ρ.ker ≤ ψ.ker :=
    normal_odd_le_ker ψ hψs (pPrimeCore_quotient_eq_bot ↥K) ρ.ker hρo
  obtain ⟨φ, hφs, hφo, -⟩ := exists_odd_quotient_of_ker_le ρ hρs ψ hψs hker hψo
  have hIC : (Λ.subgroupOf Y').map (barMk ↥Y') ≤
      centralizer ({barMk ↥Y' ⟨x, hxY⟩} : Set (barQ ↥Y')) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hso).le
  have hIpc : IsPCompIn 2 (centralizer ({barMk ↥Y' ⟨x, hxY⟩} : Set (barQ ↥Y')))
      ((Λ.subgroupOf Y').map (barMk ↥Y')) :=
    isPCompIn_two_iff.mpr ⟨hIC, isTwoComponent_map_barMk hso hΛC hΛ2⟩
  have hIperf : ⁅(Λ.subgroupOf Y').map (barMk ↥Y'), (Λ.subgroupOf Y').map (barMk ↥Y')⁆ =
      (Λ.subgroupOf Y').map (barMk ↥Y') :=
    GSThmB.commutator_eq_self_of_isPComponent hIpc.1 hIpc.2
  have hK'Y : K' ≤ Y' := hK'p.1.trans (pumpUp_le_centralizer K x')
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hK'Y
  obtain ⟨e2⟩ := hat_equiv_map
    (Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top)
  have heL : Nonempty ((↥K' ⧸ pPrimeCore 2 ↥K') ≃* ↥L) := by
    rcases himg with h | h
    · exact ⟨e1.trans (e2.trans (MulEquiv.subgroupCongr h))⟩
    · let e4 : ↥(conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L) ≃* ↥L :=
        (Subgroup.equivMapOfInjective L (MulAut.conj (barMk ↥Y' ⟨x, hxY⟩)⁻¹).toMonoidHom
          (MulAut.conj (barMk ↥Y' ⟨x, hxY⟩)⁻¹).injective).symm
      exact ⟨e1.trans (e2.trans ((MulEquiv.subgroupCongr h).trans e4))⟩
  have hkey : InB2 ↥L ∧ ¬ HasSL2Model ↥L Odd := by
    by_cases hG2L : InG2 ↥L
    · exfalso
      obtain ⟨hxL, hZ, hBlock⟩ := hG2 x' hx'o L hL hG2L
      rcases htype with hxK | hx'K'
      ·
        have hx2 : x ^ (2 ^ 1) = 1 := by
          have := pow_orderOf_eq_one x
          rwa [hxo, ← pow_one 2] at this
        have hxΛ : x ∈ Λ := h2el x (Subgroup.mem_inf.mpr ⟨hxK, hxY⟩) ⟨1, hx2⟩
        have hsI : barMk ↥Y' ⟨x, hxY⟩ ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
          ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hxΛ, rfl⟩
        have hs2 : barMk ↥Y' ⟨x, hxY⟩ * barMk ↥Y' ⟨x, hxY⟩ = 1 := by
          have h2 := pow_orderOf_eq_one (barMk ↥Y' ⟨x, hxY⟩)
          rwa [orderOf_barMk hso, pow_two] at h2
        rcases hcases with ⟨hLs, hAL⟩ | ⟨hLs, hAB, hAD⟩
        · have hsL : barMk ↥Y' ⟨x, hxY⟩ ∈ L := hAL hsI
          let sL : ↥L := ⟨barMk ↥Y' ⟨x, hxY⟩, hsL⟩
          have hsL2 : sL * sL = 1 := Subtype.ext hs2
          have hsL1 : sL ≠ 1 := by
            intro h
            have h1 : barMk ↥Y' ⟨x, hxY⟩ = 1 := congrArg Subtype.val h
            have h2 := orderOf_barMk hso
            rw [h1, orderOf_one] at h2
            omega
          let I' : Subgroup ↥L := ((Λ.subgroupOf Y').map (barMk ↥Y')).subgroupOf L
          let eP : ↥I' ≃* ↥((Λ.subgroupOf Y').map (barMk ↥Y')) :=
            Subgroup.subgroupOfEquivOfLe hAL
          have hI'C : I' ≤ centralizer ({sL} : Set ↥L) := by
            intro g hg
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hIC hg))
          have hI'perf : ⁅I', I'⁆ = I' := by
            have h1 : Group.IsPerfect ↥((Λ.subgroupOf Y').map (barMk ↥Y')) :=
              Subgroup.isPerfect_iff.2 hIperf
            have h2 : Group.IsPerfect ↥I' :=
              Group.IsPerfect.ofSurjective (f := eP.symm.toMonoidHom) eP.symm.surjective
            exact Subgroup.isPerfect_iff.1 h2
          exact exc_false_of_blockData hBlock hsL2 hsL1 hI'C hI'perf hExcK
            (φ.comp eP.toMonoidHom) (hφs.comp eP.surjective)
        · have hmem : barMk ↥Y' ⟨x, hxY⟩ ∈ L ⊔ conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L := by
            obtain ⟨l, hl⟩ := hAD hsI
            have := swapDiag_mem_sup hAB l
            rw [hl] at this
            exact this
          exact hLs (conjSub_eq_of_mem_sup hAB (inv_mem hmem))
      ·
        have hx'2 : x' ^ (2 ^ 1) = 1 := by
          have := pow_orderOf_eq_one x'
          rwa [hx'o, ← pow_one 2] at this
        have hx'Y : x' ∈ Y' := Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
        have hx'Λ : x' ∈ Λ := h2el x' (Subgroup.mem_inf.mpr ⟨hx'K', hx'Y⟩) ⟨1, hx'2⟩
        have huI : xbar x' ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
          ⟨⟨x', hx'Y⟩, Subgroup.mem_subgroupOf.mpr hx'Λ, rfl⟩
        rcases hcases with ⟨hLs, hAL⟩ | ⟨hLs, hAB, hAD⟩
        · exact hxL (hAL huI)
        · obtain ⟨l₀, hl₀⟩ := hAD huI
          have hcen : l₀ ∈ center ↥L := by
            rw [Subgroup.mem_center_iff]
            intro l
            have hu : (l : barQ ↥Y') * xbar x' = xbar x' * l :=
              Subgroup.mem_center_iff.1 (xbar_mem_center x') (l : barQ ↥Y')
            have hc1 : (l : barQ ↥Y') *
                ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') * barMk ↥Y' ⟨x, hxY⟩) =
                ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') * barMk ↥Y' ⟨x, hxY⟩) * l :=
              commute_of_commutator_conj_eq_bot hAB l.2 (conj_mem_conjSub (t := barMk ↥Y' ⟨x, hxY⟩) l₀.2)
            have hδ : (l₀ : barQ ↥Y') * ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
                barMk ↥Y' ⟨x, hxY⟩) = xbar x' := by
              rw [← swapDiag_apply hAB l₀, hl₀]
            rw [← hδ] at hu
            apply Subtype.ext
            show (l : barQ ↥Y') * (l₀ : barQ ↥Y') = (l₀ : barQ ↥Y') * l
            apply mul_right_cancel (b := (barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
              barMk ↥Y' ⟨x, hxY⟩)
            calc (l : barQ ↥Y') * (l₀ : barQ ↥Y') * ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
                  barMk ↥Y' ⟨x, hxY⟩)
                = (l : barQ ↥Y') * ((l₀ : barQ ↥Y') * ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ *
                  (l₀ : barQ ↥Y') * barMk ↥Y' ⟨x, hxY⟩)) := by simp only [mul_assoc]
              _ = ((l₀ : barQ ↥Y') * ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
                  barMk ↥Y' ⟨x, hxY⟩)) * l := hu
              _ = (l₀ : barQ ↥Y') * (((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
                  barMk ↥Y' ⟨x, hxY⟩) * l) := by simp only [mul_assoc]
              _ = (l₀ : barQ ↥Y') * (l * ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
                  barMk ↥Y' ⟨x, hxY⟩)) := by rw [hc1]
              _ = (l₀ : barQ ↥Y') * l * ((barMk ↥Y' ⟨x, hxY⟩)⁻¹ * (l₀ : barQ ↥Y') *
                  barMk ↥Y' ⟨x, hxY⟩) := by simp only [mul_assoc]
          rw [hZ, Subgroup.mem_bot] at hcen
          have h1 : xbar x' = 1 := by
            rw [← hl₀, hcen, map_one]
          exact xbar_ne_one hx'o h1
    · have hC2T2 : InC2 ↥L ∨ InT2 ↥L := by
        by_contra h
        rw [not_or] at h
        exact hG2L ⟨inCalK2_of_isComponent hKP hx'o hL, h.1, h.2⟩
      have hLB : InB2 ↥L := by
        rcases hcases with ⟨hLs, hAL⟩ | ⟨hLs, hAB, hAD⟩
        · exact hKG.1 (barQ ↥Y') (gen4Cen_barQ hgen hx'o) (barMk ↥Y' ⟨x, hxY⟩) L _ _
            (orderOf_barMk hso) hL hC2T2 hLs hIpc hAL hKB ⟨φ, hφs, hφo⟩
        · exact hKG.2 (barQ ↥Y') (gen4Cen_barQ hgen hx'o) (barMk ↥Y' ⟨x, hxY⟩) L _ _ hAB
            (orderOf_barMk hso) hL hC2T2 hLs hIpc hAD hKB ⟨φ, hφs, hφo⟩
      refine ⟨hLB, ?_⟩
      rintro ⟨F₁, hF₁, hfin₁, hodd₁, ⟨eS⟩⟩
      let eL : ↥L ≃* SL(2, F₁) := eS.trans (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F₁)
      rcases hcases with ⟨hLs, hAL⟩ | ⟨hLs, hAB, hAD⟩
      · let P : Subgroup ↥L := ((Λ.subgroupOf Y').map (barMk ↥Y')).subgroupOf L
        let eP : ↥P ≃* ↥((Λ.subgroupOf Y').map (barMk ↥Y')) := Subgroup.subgroupOfEquivOfLe hAL
        exact false_of_exc_in_sl2 hodd₁ eL P hExcK (φ.comp eP.toMonoidHom) (hφs.comp eP.surjective)
      · let δ := swapDiag hAB
        let P : Subgroup ↥L := ((Λ.subgroupOf Y').map (barMk ↥Y')).comap δ
        let ι : ↥P →* ↥((Λ.subgroupOf Y').map (barMk ↥Y')) :=
          (δ.comp P.subtype).codRestrict _ (fun g => g.2)
        have hι : Function.Surjective ι := by
          intro i
          obtain ⟨l, hl⟩ := hAD i.2
          exact ⟨⟨l, Subgroup.mem_comap.2 (by rw [hl]; exact i.2)⟩, Subtype.ext hl⟩
        exact false_of_exc_in_sl2 hodd₁ eL P hExcK (φ.comp ι) (hφs.comp hι)
  obtain ⟨eK⟩ := heL
  exact ⟨inB2_of_mulEquiv eK.symm hkey.1, fun ⟨F, hF, hfin, hodd, ⟨eS⟩⟩ =>
    hkey.2 ⟨F, hF, hfin, hodd, ⟨eK.symm.trans eS⟩⟩⟩

end CFSG.GH74.Generic.S3
