module

public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.GLS.TwoThin.KGroup
public import CFSG.GH74.GLS.TwoThin.Reduction

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

theorem b2PumpupClosed_of_kgroupQ {Q : GroupPred}
    (hQ : ∀ x : G, orderOf x = 2 → Q (barQ ↥(centralizer ({x} : Set G))))
    (hL2 : L2Sub G (fun K _ => InC2 K ∨ InT2 K))
    (hKG : TwoThinKGroupFactQ Q) : B2PumpupClosed G := by
  intro x K x' K' hKB hlt
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
  have hLB : InB2 ↥L := by
    rcases hcases with ⟨hLs, hAL⟩ | ⟨hLs, hAB, hAD⟩
    · exact hKG.1 (barQ ↥Y') (hQ x' hx'o) (barMk ↥Y' ⟨x, hxY⟩) L _ _ (orderOf_barMk hso) hL
        (hL2 x' hx'o L hL) hLs hIpc hAL hKB ⟨φ, hφs, hφo⟩
    · exact hKG.2 (barQ ↥Y') (hQ x' hx'o) (barMk ↥Y' ⟨x, hxY⟩) L _ _ hAB (orderOf_barMk hso) hL
        (hL2 x' hx'o L hL) hLs hIpc hAD hKB ⟨φ, hφs, hφo⟩
  have hK'Y : K' ≤ Y' := hK'p.1.trans (pumpUp_le_centralizer K x')
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hK'Y
  obtain ⟨e2⟩ := hat_equiv_map
    (Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top)
  rcases himg with h | h
  · exact inB2_of_mulEquiv ((e1.trans (e2.trans (MulEquiv.subgroupCongr h))).symm) hLB
  · let e4 : ↥(conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L) ≃* ↥L :=
      (Subgroup.equivMapOfInjective L (MulAut.conj (barMk ↥Y' ⟨x, hxY⟩)⁻¹).toMonoidHom
        (MulAut.conj (barMk ↥Y' ⟨x, hxY⟩)⁻¹).injective).symm
    exact inB2_of_mulEquiv
      ((e1.trans (e2.trans ((MulEquiv.subgroupCongr h).trans e4))).symm) hLB

end CFSG.GH74.GLS.TwoThin
