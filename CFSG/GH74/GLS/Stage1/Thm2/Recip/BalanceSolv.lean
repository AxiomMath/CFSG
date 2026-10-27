module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.TwoThin.DPair
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial

theorem exists_isPCompIn_of_mem_pCompIn_inf {G : Type} [Group G] [Finite G] {x y : G}
    (hx : orderOf x = 2) (hxY : x ∈ centralizer ({y} : Set G)) {Λ : Subgroup G}
    (hΛW : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) Λ)
    (hxΛ : x ∈ Λ) :
    ∃ K : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) K ∧ x ∈ K := by
  set Y' := centralizer ({y} : Set G) with hY'
  have hso : orderOf (⟨x, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hx
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  have hsmem : barMk ↥Y' ⟨x, hxY⟩ ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
    ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hxΛ, rfl⟩
  have hvert : conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L = L ∧
      (Λ.subgroupOf Y').map (barMk ↥Y') ≤ L := by
    rcases hcases with h | ⟨hLs, hAB, hAD⟩
    · exact h
    · exfalso
      have hmem : barMk ↥Y' ⟨x, hxY⟩ ∈ L ⊔ conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L := by
        obtain ⟨l, hl⟩ := hAD hsmem
        have := swapDiag_mem_sup hAB l
        rw [hl] at this
        exact this
      exact hLs (conjSub_eq_of_mem_sup hAB (inv_mem hmem))
  have hsL : barMk ↥Y' ⟨x, hxY⟩ ∈ L := hvert.2 hsmem
  have hLc : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hL2 := TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ L hLc
  obtain ⟨M, hM2, hMmap⟩ := OddKernelTwoComponents.exists_lift (barMk ↥Y') barMk_surjective
    odd_card_ker_barMk L hL2
  have hx2 : (⟨x, hxY⟩ : ↥Y') ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one (⟨x, hxY⟩ : ↥Y')
    rwa [hso, ← pow_one 2] at this
  have hzx : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hxY⟩ : ↥Y')) :=
    isPGroup_zpowers_of_pow_eq_one hx2
  have hle : (Subgroup.zpowers (⟨x, hxY⟩ : ↥Y')).map (barMk ↥Y') ≤ M.map (barMk ↥Y') := by
    rw [hMmap, MonoidHom.map_zpowers]
    exact (Subgroup.zpowers_le).mpr hsL
  have hxM : (⟨x, hxY⟩ : ↥Y') ∈ M :=
    le_of_isPGroup_of_map_le (barMk ↥Y') barMk_surjective odd_card_ker_barMk _ M hzx hM2.1 hle
      (Subgroup.mem_zpowers _)
  refine ⟨M.map Y'.subtype, ?_, ⟨⟨x, hxY⟩, hxM, rfl⟩⟩
  refine isPCompIn_two_iff.mpr ⟨Subgroup.map_subtype_le M, ?_⟩
  have hsub : (M.map Y'.subtype).subgroupOf Y' = M :=
    Subgroup.comap_map_eq_self_of_injective Y'.subtype_injective M
  rw [hsub]
  exact hM2

theorem exists_fixed_mul_of_odd {G : Type*} [Group G] {O : Subgroup G} {t k : G}
    (hO : Odd (Nat.card O)) (ht2 : t * t = 1)
    (htO : ∀ o ∈ O, t * o * t⁻¹ ∈ O) (hk : k⁻¹ * (t * k * t⁻¹) ∈ O) :
    ∃ c : G, t * c = c * t ∧ ∃ o ∈ O, k = c * o := by
  have h1 : t * t = 1 := ht2
  have h2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
  have : Finite O := Nat.finite_of_card_ne_zero hO.pos.ne'
  set a : G := k⁻¹ * (t * k * t⁻¹) with ha
  have haO : a ∈ O := hk
  have haa : a * (t * a * t⁻¹) = 1 := by
    calc a * (t * a * t⁻¹) = k⁻¹ * (t * t) * k * (t⁻¹ * t⁻¹) := by simp only [ha]; group
      _ = 1 := by rw [h1, h2]; group
  let f : O → O := fun o => ⟨a * (t * o * t⁻¹), O.mul_mem haO (htO o o.2)⟩
  have hf : Function.Involutive f := by
    intro o
    apply Subtype.ext
    change a * (t * (a * (t * (o : G) * t⁻¹)) * t⁻¹) = o
    calc a * (t * (a * (t * (o : G) * t⁻¹)) * t⁻¹)
        = (a * (t * a * t⁻¹)) * ((t * t) * (o : G) * (t⁻¹ * t⁻¹)) := by group
      _ = o := by rw [haa, h1, h2]; group
  obtain ⟨o₀, ho₀⟩ := exists_fixedPoint_of_involutive_of_odd hO f hf
  have ho₀' : a * (t * (o₀ : G) * t⁻¹) = o₀ := congrArg Subtype.val ho₀
  refine ⟨k * o₀, ?_, (o₀⁻¹ : O), (o₀⁻¹ : O).2, by simp⟩
  calc t * (k * (o₀ : G)) = (k * a) * (t * (o₀ : G) * t⁻¹) * t := by simp only [ha]; group
    _ = k * (a * (t * (o₀ : G) * t⁻¹)) * t := by group
    _ = k * (o₀ : G) * t := by rw [ho₀']

theorem exists_centralizer_lift_of_phi_fixed {G : Type} [Group G] [Finite G] (L : Subgroup G)
    {y : G} (hy2 : orderOf y = 2) (hy : y ∈ normalizer (L : Set G)) {q : Hat L}
    (hq : phi L y hy q = q) :
    ∃ (c : G) (hc : c ∈ L), y * c = c * y ∧ hatMk L ⟨c, hc⟩ = q := by
  obtain ⟨k, rfl⟩ := hatMk_surjective L q
  rw [phi_mk] at hq
  have hk0 : k⁻¹ * ⟨y * (k : G) * y⁻¹, (mem_normalizer_iff.mp hy k).mp k.2⟩ ∈ pPrimeCore 2 ↥L :=
    QuotientGroup.eq.mp hq.symm
  have hk : (k : G)⁻¹ * (y * (k : G) * y⁻¹) ∈ pPrimeCoreOf 2 L :=
    ⟨_, hk0, rfl⟩
  have hsq : y * y = 1 := by rw [← pow_two]; exact hy2 ▸ pow_orderOf_eq_one y
  have hOL : pPrimeCoreOf 2 L ≤ L := pPrimeCoreOf_le L
  obtain ⟨c, hcy, o, ho, hkc⟩ := exists_fixed_mul_of_odd (card_pPrimeCoreOf_odd L) hsq
    (fun o ho => ((mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf hy)) o).mp ho) hk
  have hcL : c ∈ L := by
    have : c = (k : G) * o⁻¹ := by rw [hkc]; group
    rw [this]
    exact mul_mem k.2 (inv_mem (hOL ho))
  refine ⟨c, hcL, hcy, ?_⟩
  have e : k = ⟨c, hcL⟩ * ⟨o, hOL ho⟩ := Subtype.ext hkc
  rw [e, map_mul, (hatMk_eq_one_iff L ⟨o, hOL ho⟩).mpr ho, mul_one]

@[expose] noncomputable def fixedRestrict {G : Type} [Group G] [Finite G] (L : Subgroup G) {y : G}
    (hy : y ∈ normalizer (L : Set G)) :
    ↥(L ⊓ centralizer ({y} : Set G)) →*
      ↥(fixedSubgroup (Hat L) (phi L y hy)) :=
  (hatMap (inf_le_left : L ⊓ centralizer ({y} : Set G) ≤ L)).codRestrict _ fun c => by
    have hc := (Subgroup.mem_inf.mp c.2).2
    have hyc : y * (c : G) = (c : G) * y := (mem_centralizer_singleton_iff.mp hc).symm
    show phi L y hy (hatMk L (Subgroup.inclusion inf_le_left c)) =
      hatMk L (Subgroup.inclusion inf_le_left c)
    rw [phi_mk]
    congr 1
    apply Subtype.ext
    show y * (c : G) * y⁻¹ = (c : G)
    rw [hyc]
    exact mul_inv_cancel_right _ _

theorem fixedRestrict_apply {G : Type} [Group G] [Finite G] (L : Subgroup G) {y : G}
    (hy : y ∈ normalizer (L : Set G)) (c : ↥(L ⊓ centralizer ({y} : Set G))) :
    ((fixedRestrict L hy c : ↥(fixedSubgroup (Hat L) (phi L y hy))) : Hat L) =
      hatMk L ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ := rfl

theorem fixedRestrict_surjective {G : Type} [Group G] [Finite G] (L : Subgroup G) {y : G}
    (hy2 : orderOf y = 2) (hy : y ∈ normalizer (L : Set G)) :
    Function.Surjective (fixedRestrict L hy) := by
  rintro ⟨q, hq⟩
  obtain ⟨c, hcL, hcy, hcq⟩ := exists_centralizer_lift_of_phi_fixed L hy2 hy (q := q) hq
  refine ⟨⟨c, Subgroup.mem_inf.mpr ⟨hcL, mem_centralizer_singleton_iff.mpr hcy.symm⟩⟩, ?_⟩
  apply Subtype.ext
  rw [fixedRestrict_apply]
  exact hcq

theorem odd_card_ker_fixedRestrict {G : Type} [Group G] [Finite G] (L : Subgroup G) {y : G}
    (hy : y ∈ normalizer (L : Set G)) : Odd (Nat.card (fixedRestrict L hy).ker) := by
  have h := odd_card_ker_hatMap (inf_le_left : L ⊓ centralizer ({y} : Set G) ≤ L)
  have hker : (fixedRestrict L hy).ker =
      (hatMap (inf_le_left : L ⊓ centralizer ({y} : Set G) ≤ L)).ker :=
    MonoidHom.ker_codRestrict _ _ _
  rw [hker]
  exact h

theorem exists_involution_of_isPComponent {F : Type} [Group F] [Finite F] {L' : Subgroup F}
    (hL' : IsPComponent 2 L') : ∃ u : F, u ∈ L' ∧ orderOf u = 2 := by
  have hq := isQuasisimple_hat_of_isPComponent hL'
  have hnotodd : ¬ Odd (Nat.card (↥L' ⧸ pPrimeCore 2 ↥L')) := fun hodd =>
    not_isSolvable_of_isQuasisimple hq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have heven : Even (Nat.card (↥L' ⧸ pPrimeCore 2 ↥L')) := Nat.not_odd_iff_even.mp hnotodd
  have hdvd : 2 ∣ Nat.card ↥L' :=
    (even_iff_two_dvd.mp heven).trans
      (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L')).symm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') 2 hdvd
  exact ⟨(u : F), u.2, by rw [Subgroup.orderOf_coe]; exact hu⟩

theorem involution_mem_isPComponent {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hxL : x ∈ L) (hx2 : orderOf x = 2) (hq : CFSG.IsQuasisimple (Hat L))
    (hr : CFSG.pRank 2 (Hat L) ≤ 1) {F : Subgroup (Hat L)} {L' : Subgroup ↥F}
    (hL' : IsPComponent 2 L') (f : ↥F) (hf : (f : Hat L) = hatMk L ⟨x, hxL⟩) : f ∈ L' := by
  obtain ⟨u, huL', hu2⟩ := exists_involution_of_isPComponent hL'
  obtain ⟨-, ⟨z, hz, hzuniq⟩, -⟩ := quasisimple_rank_one_unique_central_involution hq hr
  have hu : (u : Hat L) = z :=
    hzuniq _ (by show orderOf (u : Hat L) = 2; rw [Subgroup.orderOf_coe]; exact hu2)
  have hxo : orderOf (hatMk L ⟨x, hxL⟩) = 2 :=
    orderOf_barMk (Y := ↥L) (s := ⟨x, hxL⟩) (by rw [Subgroup.orderOf_mk]; exact hx2)
  have hxz : hatMk L ⟨x, hxL⟩ = z := hzuniq _ hxo
  have : f = u := Subtype.ext (hf.trans (hxz.trans hu.symm))
  rw [this]
  exact huL'

theorem IG_balance_fAut_nonsolv : ∀ (G : Type) [Group G] [Finite G] (x y : G), orderOf x = 2 →
    orderOf y = 2 → Commute x y → ∀ L : Subgroup G, IsIntrinsic x L →
      ∀ hy : y ∈ normalizer (L : Set G),
        (∃ L' : Subgroup ↥(fixedSubgroup (↥L ⧸ pPrimeCore 2 ↥L)
            (inducedQuotAut L (pPrimeCore 2 ↥L) ⟨y, hy⟩)), IsPComponent 2 L') →
        (x ∈ O22 (centralizer ({y} : Set G)) ∨
          ∃ K : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) K ∧ x ∈ K) := by
  intro G _ _ x y hx hy2 hxy L hL hy ⟨L', hL'⟩
  right
  obtain ⟨hLC, hrk, hxL⟩ := hL
  have hxY : x ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hxy
  set X : Subgroup G := L ⊓ centralizer ({y} : Set G) with hX
  have hL'2 : TwoComponents.IsTwoComponent L' :=
    (CatalogueBAlternating.pComponent_two_iff L').mp hL'
  obtain ⟨Λz, hΛz, hΛzmap⟩ := OddKernelTwoComponents.exists_lift (fixedRestrict L hy)
    (fixedRestrict_surjective L hy2 hy) (odd_card_ker_fixedRestrict L hy) L' hL'2
  set Λ : Subgroup G := Λz.map X.subtype with hΛdef
  have hΛX : Λ ≤ X := Subgroup.map_subtype_le Λz
  have hsub : Λ.subgroupOf X = Λz :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective Λz
  have hΛpc : IsPCompIn 2 X Λ := isPCompIn_two_iff.mpr ⟨hΛX, by rw [hsub]; exact hΛz⟩
  have hΛW : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) Λ := by
    set W := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hW
    have hXW : X ≤ W := le_inf ((inf_le_left : X ≤ L).trans hLC.1) inf_le_right
    refine isPCompIn_two_iff.mpr ⟨hΛX.trans hXW, ?_⟩
    have hKsub : (L.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
      Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hLC).2.1
        Subgroup.IsSubnormal.top
    have hsubW : (X.subgroupOf W).IsSubnormal := by
      have h1 := isSubnormal_inf_subgroupOf hKsub (inf_le_left : W ≤ centralizer ({x} : Set G))
      have h2 : X.subgroupOf W = L.subgroupOf W := by
        ext a
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hX]
        exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.mp a.2).2⟩⟩
      rwa [h2]
    exact TwoComponentTransport.extend_nested Λ _ W hΛX hXW hsubW (isPCompIn_two_iff.mp hΛpc).2
  have hxX : x ∈ X := Subgroup.mem_inf.mpr ⟨hxL, hxY⟩
  have hxX2 : (⟨x, hxX⟩ : ↥X) ^ (2 ^ 1) = 1 := by
    have h := pow_orderOf_eq_one (⟨x, hxX⟩ : ↥X)
    rwa [Subgroup.orderOf_mk, hx, ← pow_one 2] at h
  have hzx : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hxX⟩ : ↥X)) :=
    isPGroup_zpowers_of_pow_eq_one hxX2
  have hq : CFSG.IsQuasisimple (Hat L) := isQuasisimple_hat hLC
  have hr : CFSG.pRank 2 (Hat L) ≤ 1 := ((pRank_hat L).trans hrk).le
  have hxbar : fixedRestrict L hy ⟨x, hxX⟩ ∈ L' :=
    involution_mem_isPComponent hxL hx hq hr hL' _ (fixedRestrict_apply L hy ⟨x, hxX⟩)
  have hle : (Subgroup.zpowers (⟨x, hxX⟩ : ↥X)).map (fixedRestrict L hy) ≤
      Λz.map (fixedRestrict L hy) := by
    rw [hΛzmap, MonoidHom.map_zpowers]
    exact (Subgroup.zpowers_le).mpr hxbar
  have hxΛz : (⟨x, hxX⟩ : ↥X) ∈ Λz :=
    le_of_isPGroup_of_map_le (fixedRestrict L hy) (fixedRestrict_surjective L hy2 hy)
      (odd_card_ker_fixedRestrict L hy) _ Λz hzx hΛz.1 hle (Subgroup.mem_zpowers _)
  have hxΛ : x ∈ Λ := ⟨⟨x, hxX⟩, hxΛz, rfl⟩
  exact exists_isPCompIn_of_mem_pCompIn_inf hx hxY hΛW hxΛ

@[expose] def IG_balance_fAut_solv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x y : G), orderOf x = 2 →
    orderOf y = 2 → Commute x y → ∀ L : Subgroup G, IsIntrinsic x L →
      ∀ hy : y ∈ normalizer (L : Set G),
        HasSolvableTwoComponentSL23 ↥(fixedSubgroup (↥L ⧸ pPrimeCore 2 ↥L)
            (inducedQuotAut L (pPrimeCore 2 ↥L) ⟨y, hy⟩)) →
        (x ∈ O22 (centralizer ({y} : Set G)) ∨
          ∃ K : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) K ∧ x ∈ K)

theorem IG_balance_fAut_of_solv (h : IG_balance_fAut_solv) : IG_balance_fAut := by
  intro G _ _ hG x y hx hy hxy L hL hF
  obtain ⟨hyN, -, -, -, -, hcomp | hsolv⟩ := hF
  · exact IG_balance_fAut_nonsolv G x y hx hy hxy L hL hyN hcomp
  · exact h G hG x y hx hy hxy L hL hyN hsolv

end CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv
