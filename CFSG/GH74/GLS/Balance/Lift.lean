module

public import CFSG.GH74.GLS.Balance.Defs
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv
import CFSG.ClassicalInvolution.SolvableCase.SL2Three
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv
open scoped MatrixGroups commutatorElement

private theorem sl2Three_exp : ∀ n : SL(2, ZMod 3), n ^ 12 = 1 := by decide +kernel

private theorem sl2Three_comm_aux :
    ∀ n : SL(2, ZMod 3), n ≠ 1 → n ^ 3 = 1 → ∃ g : SL(2, ZMod 3), ⁅g, n⁆ ≠ 1 ∧ ⁅g, n⁆ ^ 4 = 1 := by
  decide +kernel

theorem sl2Three_odd_normal_eq_bot (N : Subgroup SL(2, ZMod 3)) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  by_contra hne
  have hne' : n ≠ 1 := fun h => hne (by rw [h]; exact one_mem _)
  have hodd : ∀ m ∈ N, Odd (orderOf m) := fun m hm => by
    have : orderOf (⟨m, hm⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hN this
  have h12 : orderOf n ∣ 12 := orderOf_dvd_of_pow_eq_one (sl2Three_exp n)
  have h3 : n ^ 3 = 1 := by
    have h13 : orderOf n ∣ 3 := by
      have hmem : orderOf n ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨h12, by norm_num⟩
      have key : ∀ d ∈ Nat.divisors 12, Odd d → d ∣ 3 := by decide
      exact key _ hmem (hodd n hn)
    exact orderOf_dvd_iff_pow_eq_one.mp h13
  obtain ⟨g, hg1, hg4⟩ := sl2Three_comm_aux n hne' h3
  have hcomm : ⁅g, n⁆ ∈ N := by
    have : ⁅g, n⁆ = (g * n * g⁻¹) * n⁻¹ := commutatorElement_def g n
    rw [this]
    exact mul_mem (Subgroup.Normal.conj_mem inferInstance n hn g) (inv_mem hn)
  have hord := hodd _ hcomm
  have h4 : orderOf ⁅g, n⁆ ∣ 4 := orderOf_dvd_of_pow_eq_one hg4
  have h5 : orderOf ⁅g, n⁆ ∣ 1 := by
    have hmem : orderOf ⁅g, n⁆ ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨h4, by norm_num⟩
    have key : ∀ d ∈ Nat.divisors 4, Odd d → d ∣ 1 := by decide
    exact key _ hmem hord
  exact hg1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5))

theorem hasSolvableTwoComponentSL23_iff (Y : Type*) [Group Y] :
    HasSolvableTwoComponentSL23 Y ↔
      ∃ W : Subgroup (Y ⧸ pPrimeCore 2 Y), W.IsSubnormal ∧ Nonempty (↥W ≃* SL(2, ZMod 3)) := by
  constructor
  · rintro ⟨W, hW, F, hF, hFin, hcard, ⟨e⟩⟩
    obtain ⟨e'⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hcard
    exact ⟨W, hW, ⟨(e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans
      e'⟩⟩
  · rintro ⟨W, hW, ⟨e⟩⟩
    refine ⟨W, hW, ZMod 3, inferInstance, inferInstance, by rw [Nat.card_zmod], ⟨?_⟩⟩
    exact e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 3))

theorem odd_card_ker_comp {A B C : Type*} [Group A] [Group B] [Group C] [Finite A]
    (f : A →* B) (g : B →* C) (hf : Function.Surjective f) (hfo : Odd (Nat.card f.ker))
    (hgo : Odd (Nat.card g.ker)) : Odd (Nat.card (g.comp f).ker) := by
  have : Finite B := Finite.of_surjective f hf
  have : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have h1 := Subgroup.card_ker_mul_card_range (g.comp f)
  have h2 := Subgroup.card_ker_mul_card_of_surjective hf
  have h3 := Subgroup.card_ker_mul_card_range g
  have hr : (g.comp f).range = g.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, Subgroup.map_top]
  rw [hr] at h1
  have hpos : 0 < Nat.card g.range := Nat.card_pos
  have : Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (g.comp f).ker * Nat.card g.range = Nat.card A := h1
      _ = Nat.card f.ker * Nat.card B := h2.symm
      _ = Nat.card f.ker * (Nat.card g.ker * Nat.card g.range) := by rw [h3]
      _ = (Nat.card f.ker * Nat.card g.ker) * Nat.card g.range := by ring
  rw [this]
  exact hfo.mul hgo

theorem isSolvTwoCompSL23_of_subnormal {C : Type*} [Group C] [Finite C] (Vt : Subgroup C)
    (hsub : Vt.IsSubnormal) (χ : ↥Vt →* SL(2, ZMod 3)) (hχ : Function.Surjective χ)
    (hker : ∀ n : ↥Vt, χ n = 1 → (n : C) ∈ pPrimeCore 2 C) :
    IsSolvTwoCompSL23 C (Vt ⊔ pPrimeCore 2 C) := by
  set π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  refine ⟨Vt.map π, hsub.map hπs, ?_, ?_⟩
  · set ρ : ↥Vt →* ↥(Vt.map π) := π.subgroupMap Vt with hρ
    have hρs : Function.Surjective ρ := MonoidHom.subgroupMap_surjective π Vt
    have hρker : ρ.ker = (pPrimeCore 2 C).subgroupOf Vt := by
      rw [hρ, Subgroup.ker_subgroupMap, hπ, QuotientGroup.ker_mk']
    have hker_eq : ρ.ker = χ.ker := by
      ext n
      constructor
      · intro hn
        have hN : Subgroup.Normal (ρ.ker.map χ) := Subgroup.Normal.map inferInstance χ hχ
        have hOdd : Odd (Nat.card (ρ.ker.map χ)) := by
          have h1 : Nat.card (ρ.ker.map χ) ∣ Nat.card ρ.ker := Subgroup.card_map_dvd ρ.ker χ
          have h2 : Odd (Nat.card ρ.ker) := by
            have hM : ρ.ker.map Vt.subtype ≤ pPrimeCore 2 C := by
              rintro _ ⟨m, hm, rfl⟩
              rw [hρker] at hm
              exact hm
            have h3 : Nat.card (ρ.ker.map Vt.subtype) = Nat.card ρ.ker :=
              Subgroup.card_map_of_injective Vt.subtype_injective
            have h4 : Nat.card (ρ.ker.map Vt.subtype) ∣ Nat.card (pPrimeCore 2 C) :=
              Subgroup.card_dvd_of_le hM
            rw [← h3]
            exact Odd.of_dvd_nat (TwoThin.odd_card_pPrimeCore C) h4
          exact Odd.of_dvd_nat h2 h1
        have := sl2Three_odd_normal_eq_bot (ρ.ker.map χ) hOdd
        have hm : χ n ∈ ρ.ker.map χ := ⟨n, hn, rfl⟩
        rw [this] at hm
        exact Subgroup.mem_bot.mp hm
      · intro hn
        rw [hρker]
        exact hker n hn
    exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker_eq)).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχ)⟩
  · rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

@[expose] def xC {G : Type*} [Group G] {x y : G} (hxy : Commute x y) :
    ↥(centralizer ({y} : Set G)) :=
  ⟨x, mem_centralizer_singleton_iff.mpr hxy⟩

theorem exists_solvTwoComp_of_fixed {G : Type} [Group G] [Finite G] {x y : G}
    (hx : orderOf x = 2) (hxy : Commute x y) {L : Subgroup G} (hL : IsIntrinsic x L)
    (hy : orderOf y = 2) (hyN : y ∈ normalizer (L : Set G))
    (hsolv : HasSolvableTwoComponentSL23 ↥(fixedSubgroup (↥L ⧸ pPrimeCore 2 ↥L)
      (inducedQuotAut L (pPrimeCore 2 ↥L) ⟨y, hyN⟩))) :
    ∃ V : Subgroup ↥(centralizer ({y} : Set G)),
      IsSolvTwoCompSL23In (centralizer ({xC hxy} : Set ↥(centralizer ({y} : Set G)))) V ∧
        xC hxy ∈ V := by
  classical
  obtain ⟨hLC, hrk, hxL⟩ := hL
  have hLCx : L ≤ centralizer ({x} : Set G) := hLC.1
  have hLsub : (L.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hsub, -⟩ := hLC.2
    exact hsub
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  set x' : ↥Cy := xC hxy with hx'
  set C' : Subgroup ↥Cy := centralizer ({x'} : Set ↥Cy) with hC'
  set Hg : Subgroup (Hat L) := fixedSubgroup (Hat L) (phi L y hyN) with hHg
  set q : ↥Hg →* ↥Hg ⧸ pPrimeCore 2 ↥Hg := QuotientGroup.mk' (pPrimeCore 2 ↥Hg) with hq
  obtain ⟨W, hWsub, ⟨eW⟩⟩ := (hasSolvableTwoComponentSL23_iff _).mp hsolv
  let f : ↥C' →* ↥(centralizer ({x} : Set G)) :=
    (Cy.subtype.comp C'.subtype).codRestrict (centralizer ({x} : Set G)) (fun g => by
      have h1 := mem_centralizer_singleton_iff.mp g.2
      have h2 := congrArg Subtype.val h1
      exact mem_centralizer_singleton_iff.mpr h2)
  set U : Subgroup ↥C' := (L.subgroupOf (centralizer ({x} : Set G))).comap f with hU
  have hUsub : U.IsSubnormal := hLsub.comap f
  have hmemU : ∀ u : ↥C', u ∈ U ↔ (((u : ↥Cy) : G)) ∈ L := fun u => Iff.rfl
  let j : ↥U →* ↥(L ⊓ Cy) :=
    ((Cy.subtype.comp C'.subtype).comp U.subtype).codRestrict (L ⊓ Cy) (fun u =>
      ⟨(hmemU _).mp u.2, ((u : ↥C') : ↥Cy).2⟩)
  have hjinj : Function.Injective j := by
    intro a b hab
    have h : (((j a : ↥(L ⊓ Cy)) : G)) = ((j b : ↥(L ⊓ Cy)) : G) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hjsurj : Function.Surjective j := by
    rintro ⟨a, haL, haCy⟩
    have hax : a * x = x * a := mem_centralizer_singleton_iff.mp (hLCx haL)
    have hC'mem : (⟨a, haCy⟩ : ↥Cy) ∈ C' := by
      rw [hC', mem_centralizer_singleton_iff]
      exact Subtype.ext hax
    exact ⟨⟨⟨⟨a, haCy⟩, hC'mem⟩, haL⟩, rfl⟩
  let r : ↥(L ⊓ Cy) →* ↥Hg := fixedRestrict L hyN
  have hrsurj : Function.Surjective r := fixedRestrict_surjective L hy hyN
  have hrodd : Odd (Nat.card r.ker) := odd_card_ker_fixedRestrict L hyN
  let ψ : ↥U →* ↥Hg ⧸ pPrimeCore 2 ↥Hg := q.comp (r.comp j)
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hψsurj : Function.Surjective ψ := hqsurj.comp (hrsurj.comp hjsurj)
  have hjker : Odd (Nat.card j.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff j).mpr hjinj, Subgroup.card_bot]
    exact odd_one
  have hrjodd : Odd (Nat.card (r.comp j).ker) := odd_card_ker_comp j r hjsurj hjker hrodd
  have hqker : Odd (Nat.card q.ker) := by
    rw [hq, QuotientGroup.ker_mk']
    exact TwoThin.odd_card_pPrimeCore _
  have hψodd : Odd (Nat.card ψ.ker) :=
    odd_card_ker_comp (r.comp j) q (hrsurj.comp hjsurj) hrjodd hqker
  have hψker : ∀ u : ↥U, ψ u = 1 → ((u : ↥C') : ↥C') ∈ pPrimeCore 2 ↥C' := by
    intro u hu
    have hle : ψ.ker ≤ pPrimeCore 2 ↥U :=
      le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hψodd⟩
    have hmem : u ∈ pPrimeCore 2 ↥U := hle (MonoidHom.mem_ker.mpr hu)
    exact CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hUsub ⟨u, hmem, rfl⟩
  have hxCy : x ∈ Cy := mem_centralizer_singleton_iff.mpr hxy
  have hx'C' : x' ∈ C' := mem_centralizer_singleton_iff.mpr rfl
  let x'' : ↥C' := ⟨x', hx'C'⟩
  have hx''U : x'' ∈ U := hxL
  have hψx : ψ ⟨x'', hx''U⟩ ∈ W := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq1 : CFSG.IsQuasisimple (Hat L) := TwoThin.isQuasisimple_hat hLC
    have hr1 : CFSG.pRank 2 (Hat L) ≤ 1 := ((pRank_hat L).trans hrk).le
    obtain ⟨-, ⟨z, hz, hzuniq⟩, -⟩ := quasisimple_rank_one_unique_central_involution hq1 hr1
    have hx2 : orderOf (hatMk L ⟨x, hxL⟩) = 2 :=
      TwoThin.orderOf_barMk (Y := ↥L) (s := ⟨x, hxL⟩) (by rw [Subgroup.orderOf_mk]; exact hx)
    have hxz : hatMk L ⟨x, hxL⟩ = z := hzuniq _ hx2
    have hWcard : Nat.card W = 24 := by
      rw [Nat.card_congr eW.toEquiv, CFSG.ClassicalInvolution.natCard_sl2Three]
    obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 (by rw [hWcard]; norm_num)
    obtain ⟨h, hh⟩ := hqsurj (w₀ : ↥Hg ⧸ pPrimeCore 2 ↥Hg)
    have hw₀sq : (w₀ : ↥Hg ⧸ pPrimeCore 2 ↥Hg) ^ 2 = 1 := by
      have := pow_orderOf_eq_one w₀
      rw [hw₀] at this
      exact congrArg Subtype.val this
    have hh2 : h ^ 2 ∈ pPrimeCore 2 ↥Hg := by
      have : q (h ^ 2) = 1 := by rw [map_pow, hh, hw₀sq]
      rw [hq] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have hmodd : Odd (orderOf (h ^ 2)) := by
      have h1 : orderOf (⟨h ^ 2, hh2⟩ : pPrimeCore 2 ↥Hg) ∣ Nat.card (pPrimeCore 2 ↥Hg) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat (TwoThin.odd_card_pPrimeCore _) h1
    set m := orderOf (h ^ 2) with hm
    have hh'2 : (h ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hm, pow_orderOf_eq_one]
    obtain ⟨k, hk⟩ := hmodd
    have hqh' : q (h ^ m) = (w₀ : ↥Hg ⧸ pPrimeCore 2 ↥Hg) := by
      rw [map_pow, hh, hk, pow_succ, pow_mul, hw₀sq, one_pow, one_mul]
    have hh'1 : h ^ m ≠ 1 := by
      intro h1
      rw [h1, map_one] at hqh'
      have : w₀ = 1 := Subtype.ext hqh'.symm
      rw [this, orderOf_one] at hw₀
      exact absurd hw₀ (by norm_num)
    have hh'ord : orderOf (h ^ m) = 2 := orderOf_eq_prime hh'2 hh'1
    have hcoe : orderOf ((h ^ m : ↥Hg) : Hat L) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hh'ord
    have hh'z : ((h ^ m : ↥Hg) : Hat L) = z := hzuniq _ hcoe
    have hc₀ : ((r ⟨x, hxL, hxCy⟩ : ↥Hg) : Hat L) = z := by
      rw [fixedRestrict_apply]; exact hxz
    have hrh : r ⟨x, hxL, hxCy⟩ = h ^ m := Subtype.ext (hc₀.trans hh'z.symm)
    have : ψ ⟨x'', hx''U⟩ = q (h ^ m) := by
      show q (r (j ⟨x'', hx''U⟩)) = _
      rw [← hrh]
      rfl
    rw [this, hqh']
    exact w₀.2
  set Vt : Subgroup ↥C' := (W.comap ψ).map U.subtype with hVt
  have hVtsub : Vt.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_ hUsub
    have h1 : (Vt.subgroupOf U) = W.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
    rw [h1]
    exact hWsub.comap ψ
  let eV : ↥(W.comap ψ) ≃* ↥Vt := (W.comap ψ).equivMapOfInjective U.subtype U.subtype_injective
  let χ : ↥Vt →* SL(2, ZMod 3) :=
    eW.toMonoidHom.comp ((ψ.subgroupComap W).comp eV.symm.toMonoidHom)
  have hχsurj : Function.Surjective χ := by
    intro s
    obtain ⟨w, hw⟩ := eW.surjective s
    obtain ⟨u, hu⟩ := hψsurj (w : ↥Hg ⧸ pPrimeCore 2 ↥Hg)
    refine ⟨eV ⟨u, by rw [Subgroup.mem_comap, hu]; exact w.2⟩, ?_⟩
    show eW ((ψ.subgroupComap W) (eV.symm (eV _))) = s
    rw [MulEquiv.symm_apply_apply, ← hw]
    congr 1
    exact Subtype.ext hu
  have hχker : ∀ n : ↥Vt, χ n = 1 → (n : ↥C') ∈ pPrimeCore 2 ↥C' := by
    intro n hn
    have h1 : (ψ.subgroupComap W) (eV.symm n) = 1 := eW.map_eq_one_iff.mp hn
    have h2 : ψ ((eV.symm n : ↥(W.comap ψ)) : ↥U) = 1 := by
      have := congrArg Subtype.val h1
      exact this
    have h3 := hψker _ h2
    have h4 : (n : ↥C') = (((eV.symm n : ↥(W.comap ψ)) : ↥U) : ↥C') := by
      conv_lhs => rw [← eV.apply_symm_apply n]
      rfl
    rw [h4]
    exact h3
  have hV := isSolvTwoCompSL23_of_subnormal Vt hVtsub χ hχsurj hχker
  refine ⟨(Vt ⊔ pPrimeCore 2 ↥C').map C'.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C'.subtype_injective]
    exact hV
  · refine ⟨x'', Subgroup.mem_sup_left ?_, rfl⟩
    exact ⟨⟨x'', hx''U⟩, Subgroup.mem_comap.mpr hψx, rfl⟩

theorem mem_oPrimeResidualOf_of_sq {X : Type*} [Group X] {V : Subgroup X} {g : X} (hg : g ∈ V)
    (h2 : g ^ 2 = 1) : g ∈ oPrimeResidualOf 2 V :=
  ⟨⟨g, hg⟩, Subgroup.subset_closure ⟨1, by rw [pow_one]; exact Subtype.ext h2⟩, rfl⟩

theorem ig_balance_fAut_solv_of (h : SolvableL2PrimeBalance) : IG_balance_fAut_solv := by
  intro G _ _ _hG x y hx hy hxy L hL hyN hsolv
  obtain ⟨V, hV, hxV⟩ := exists_solvTwoComp_of_fixed hx hxy hL hy hyN hsolv
  have hx' : orderOf (xC hxy) = 2 := by
    rw [xC, Subgroup.orderOf_mk]; exact hx
  have hres : xC hxy ∈ oPrimeResidualOf 2 V := by
    refine mem_oPrimeResidualOf_of_sq hxV ?_
    have := pow_orderOf_eq_one (xC hxy)
    rwa [hx'] at this
  rcases h _ (xC hxy) hx' V hV with h1 | ⟨L', hL', -, hRL'⟩
  · exact Or.inl ⟨xC hxy, h1 hres, rfl⟩
  · refine Or.inr ⟨L'.map (centralizer ({y} : Set G)).subtype, ⟨Subgroup.map_subtype_le _, ?_⟩,
      ⟨xC hxy, hRL' hres, rfl⟩⟩
    have e : (L'.map (centralizer ({y} : Set G)).subtype).subgroupOf (centralizer ({y} : Set G)) =
        L' := Subgroup.comap_map_eq_self_of_injective (centralizer ({y} : Set G)).subtype_injective L'
    rw [e]
    exact hL'

end CFSG.GH74.GLS.Balance
