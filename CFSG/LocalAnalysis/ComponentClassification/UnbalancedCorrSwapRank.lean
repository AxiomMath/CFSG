module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le' {p : ℕ} {E E' : Subgroup G} (hE : Open.IsElemAbelian p E)
    (hle : E' ≤ E) : Open.IsElemAbelian p E' := by
  obtain ⟨hc, hpow⟩ := hE
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hpow x (hle hx)⟩
  have h1 := congrArg Subtype.val (hc.is_comm.comm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩)
  exact h1

theorem pRank_le_add_one_of_relIndex_eq_two {R U : Subgroup G} (hidx : R.relIndex U = 2) :
    pRank 2 ↥U ≤ pRank 2 ↥R + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbr : ∀ Q : Subgroup G, pRank 2 ↥Q = Open.pRank 2 Q := fun Q =>
    (SectionRank.pRank_eq_open_pRank_top 2 Q).trans (SectionRank.pRank_eq_pRank_top_subgroup Q).symm
  rw [hbr, hbr]
  obtain ⟨E, hEU, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) one_lt_two U
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  obtain ⟨k, hk⟩ := (hE2.to_le (inf_le_left : E ⊓ R ≤ E)).exists_card_eq
  have hk' : k ≤ Open.pRank 2 R :=
    SectionRank.le_pRank one_lt_two inf_le_right (isElemAbelian_of_le' hE inf_le_left) hk
  have h1 : R.relIndex E ≤ 2 := by
    rw [← hidx]
    exact relIndex_le_of_le_right hEU (by rw [hidx]; norm_num)
  have h2 := relIndex_mul_card (H := R) (K := E)
  rw [inf_comm, hk, hcard] at h2
  have h3 : 2 ^ Open.pRank 2 U ≤ 2 ^ (k + 1) := by
    rw [← h2, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ h1
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

theorem pRank_add_le_of_commute {F R Q : Subgroup G} (hFQ : F ≤ Q) (hRQ : R ≤ Q)
    (hFR : ⁅F, R⁆ = ⊥) (hFRbot : F ⊓ R = ⊥) : pRank 2 ↥F + pRank 2 ↥R ≤ pRank 2 ↥Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbr : ∀ Q : Subgroup G, pRank 2 ↥Q = Open.pRank 2 Q := fun Q =>
    (SectionRank.pRank_eq_open_pRank_top 2 Q).trans (SectionRank.pRank_eq_pRank_top_subgroup Q).symm
  rw [hbr, hbr, hbr]
  obtain ⟨E₁, hE₁F, hE₁, hc₁⟩ := SectionRank.exists_pRank (p := 2) one_lt_two F
  obtain ⟨E₂, hE₂R, hE₂, hc₂⟩ := SectionRank.exists_pRank (p := 2) one_lt_two R
  have hcomm : ∀ (x : E₁) (y : E₂), Commute (E₁.subtype x) (E₂.subtype y) := by
    intro x y
    have h1 := commutator_eq_bot_iff_le_centralizer.mp hFR (hE₁F x.2)
    exact (mem_centralizer_iff.mp h1 y (hE₂R y.2)).symm
  let f : E₁ × E₂ →* G := MonoidHom.noncommCoprod E₁.subtype E₂.subtype hcomm
  have hf : ∀ x : E₁ × E₂, f x = (x.1 : G) * x.2 := fun x => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf] at hx
    have h1 : (x.1 : G) = (x.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have h2 : (x.1 : G) ∈ F ⊓ R :=
      mem_inf.mpr ⟨hE₁F x.1.2, h1 ▸ inv_mem (hE₂R x.2.2)⟩
    rw [hFRbot, mem_bot] at h2
    have h3 : (x.2 : G) = 1 := by
      rw [h2] at h1
      exact (inv_eq_one.mp h1.symm)
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hrange : f.range ≤ Q := by
    rintro _ ⟨x, rfl⟩
    rw [hf]
    exact mul_mem (hFQ (hE₁F x.1.2)) (hRQ (hE₂R x.2.2))
  refine SectionRank.le_pRank_of_injective one_lt_two ?_ ?_ ?_ f hfinj hrange
  · intro x y
    obtain ⟨hc₁', -⟩ := hE₁
    obtain ⟨hc₂', -⟩ := hE₂
    exact Prod.ext (hc₁'.is_comm.comm _ _) (hc₂'.is_comm.comm _ _)
  · intro x
    obtain ⟨-, hp₁⟩ := hE₁
    obtain ⟨-, hp₂⟩ := hE₂
    exact Prod.ext (Subtype.ext (by simpa using hp₁ _ x.1.2))
      (Subtype.ext (by simpa using hp₂ _ x.2.2))
  · rw [Nat.card_prod, hc₁, hc₂, pow_add]

theorem pRank_eq_pRank_quotient_pPrimeCore (X : Type*) [Group X] [Finite X] :
    pRank 2 X = pRank 2 (X ⧸ pPrimeCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
    SectionRank.pRank_quotient_eq (pPrimeCore 2 X)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card)]

theorem swapped_correspondence_centralizer_rank_bound {a b : G} {J L : Subgroup G}
    (h : UnbalancedGS.GSCorr a J b L) (hne : conjugate L a ≠ L)
    (hd : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) {U : Subgroup G}
    (hU2 : IsPGroup 2 U)
    (hUle : U ≤ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) ⊓ normalizer (J : Set G))
    (haU : a ∈ U)
    (hJU : ∀ u ∈ U, ∀ j ∈ J, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 J).map J.subtype) :
    ∃ R : Subgroup G,
      (R : Set G) = {u | u ∈ U ∧ ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * u⁻¹ * k * u ∈
        (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype} ∧
      zpowers a ⊓ R = ⊥ ∧ zpowers a ⊔ R = U ∧ (∀ x ∈ zpowers a, ∀ y ∈ R, x * y = y * x) ∧
      R.relIndex U = 2 ∧
      (∃ F : Subgroup G, F ≤ conjugate L a ∧
        (∃ P : Sylow 2 ↥(conjugate L a),
          (P : Subgroup ↥(conjugate L a)) = F.subgroupOf (conjugate L a)) ∧
        ⁅F, R⁆ = ⊥ ∧ F ⊓ R = ⊥ ∧
        F ⊔ R ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L) ∧
      pRank 2 ↥L + pRank 2 ↥U - 1 ≤
        pRank 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L) ∧
      pRank 2 ↥L = pRank 2 ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison h
  have hnc := (correspondence_normal_closure h rfl rfl rfl).2.2.2
  have hcorr := h
  obtain ⟨hao, hbo, hab, hJa, hJ, hLb, hL, hbN, hcomm, -⟩ := hcorr
  set H := centralizer ({b} : Set G) with hHdef
  set N := (pPrimeCore 2 H).map H.subtype with hNdef
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  have haa : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haH : a ∈ H := mem_centralizer_singleton_iff.mpr hab
  have hUa : ∀ u ∈ U, u ∈ centralizer ({a} : Set G) := fun u hu =>
    (mem_inf.mp (mem_inf.mp (hUle hu)).1).1
  have hUb : ∀ u ∈ U, u ∈ H := fun u hu => (mem_inf.mp (mem_inf.mp (hUle hu)).1).2
  have hUJ : ∀ u ∈ U, u ∈ normalizer (J : Set G) := fun u hu => (mem_inf.mp (hUle hu)).2
  have hLaH : conjugate L a ≤ H := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem haH) (hLb hy)) haH
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
  have hKH : L ⊔ conjugate L a ≤ H := sup_le hLb hLaH
  have hL₂ : IsPComponent 2 ((conjugate L a).subgroupOf H) := by
    have h1 := isPComponent_conjugate hL (⟨a, haH⟩ : H)
    rwa [conjugate_subgroupOf_eq] at h1
  have hLsub : (L.subgroupOf H).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hL
    exact hs
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨α, -, -, hABc, hAq, -, -, -, -, ⟨eT, heT⟩, -, hiff, -⟩ := hcmp.2.2.1 hne haH
  have hDbot : UnbalancingLocal.corrImage b L ⊓ UnbalancingLocal.corrImage b (conjugate L a) =
      ⊥ := hiff.mp (by rw [← index_eq_card, ← index_eq_card]; exact hd)
  have hγ := corrImage_conj_mem h haH
  have hΔ := corrImage_gsFixedLayer_eq h hne haH
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set A := UnbalancingLocal.corrImage b L with hAdef
  set B := UnbalancingLocal.corrImage b (conjugate L a) with hBdef
  set abar : UnbalancingLocal.CorrQuotient b :=
    ((⟨a, haH⟩ : H) : UnbalancingLocal.CorrQuotient b) with habardef
  have hAnt : Nontrivial A := by
    have : IsSimpleGroup (A ⧸ center A) := hAq.2.1
    exact (QuotientGroup.mk'_surjective (center A)).nontrivial
  have hTJ : T ≤ J := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left
  have hTH : T ≤ H := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_right
  have hOT1 : ∀ t : T, t ∈ pPrimeCore 2 T → π ⟨t, hTH t.2⟩ = 1 := by
    intro t ht
    have h1 := heT t (hTH t.2)
    have h2 : (t : T ⧸ pPrimeCore 2 T) = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    rw [h2, map_one, Subgroup.coe_one] at h1
    exact h1.symm
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hTsupJ : T ⊔ (pPrimeCore 2 J).map J.subtype = J :=
    gsFixedLayer_sup_map_pPrimeCore hbo hJq hbN hcomm
  obtain ⟨hcoreJ, eJ, heJ⟩ := restriction_quotient_mulEquiv hTJ hTsupJ
  have hUT : ∀ u ∈ U, u ∈ normalizer (T : Set G) := by
    intro u hu
    have : (pLayer ↥(J ⊓ H) 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (J ⊓ H) (pLayer ↥(J ⊓ H) 2)
      (normalizer_inf_mem (hUJ u hu) (le_normalizer (hUb u hu)))
  have hcent : ∀ u ∈ U, ∀ t ∈ T, ∀ (h₁ : u⁻¹ * t * u ∈ H) (h₂ : t ∈ H),
      π ⟨u⁻¹ * t * u, h₁⟩ = π ⟨t, h₂⟩ := by
    intro u hu t ht h₁ h₂
    have hx : t⁻¹ * (u⁻¹ * t * u) ∈ T ⊓ (pPrimeCore 2 J).map J.subtype := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem ht) ?_, ?_⟩
      · have h3 := (mem_normalizer_iff.mp (inv_mem (hUT u hu)) t).mp ht
        rwa [inv_inv] at h3
      · have h3 := hJU u hu t (hTJ ht)
        rwa [show t⁻¹ * (u⁻¹ * t * u) = t⁻¹ * u⁻¹ * t * u by group]
    rw [← hcoreJ] at hx
    obtain ⟨o, ho, hoeq⟩ := mem_map.mp hx
    have h3 := hOT1 o ho
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    have heq : (⟨t, h₂⟩ : H)⁻¹ * ⟨u⁻¹ * t * u, h₁⟩ = ⟨(o : G), hTH o.2⟩ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      exact hoeq.symm
    rw [heq]
    exact h3
  have hBA : ∀ y ∈ B, ∃ z ∈ A, y = abar * z * abar⁻¹ := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hy
    have hm' : (m : G) ∈ conjugate L a := hm
    rw [mem_conjugate_iff] at hm'
    have hmH : a * (m : G) * a⁻¹ ∈ H := hLb hm'
    refine ⟨π ⟨a * m * a⁻¹, hmH⟩, ⟨⟨a * m * a⁻¹, hmH⟩, hm', rfl⟩, ?_⟩
    have h1 : (⟨a * m * a⁻¹, hmH⟩ : H) = ⟨a, haH⟩ * m * (⟨a, haH⟩ : H)⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    show π m = π ⟨a, haH⟩ * (π ⟨a, haH⟩ * π m * (π ⟨a, haH⟩)⁻¹) * (π ⟨a, haH⟩)⁻¹
    rw [show π ⟨a, haH⟩ * (π ⟨a, haH⟩ * π m * (π ⟨a, haH⟩)⁻¹) * (π ⟨a, haH⟩)⁻¹ =
      π (⟨a, haH⟩ * ⟨a, haH⟩) * π m * (π (⟨a, haH⟩ * ⟨a, haH⟩))⁻¹ by
        rw [map_mul]
        group]
    rw [show (⟨a, haH⟩ : H) * ⟨a, haH⟩ = 1 from Subtype.ext haa, map_one]
    group
  set R := U ⊓ normalizer (L : Set G) with hRdef
  have hRU : R ≤ U := inf_le_left
  have hfix : ∀ (u : G) (hu : u ∈ R), ∀ z ∈ A ⊔ B,
      (π ⟨u, hUb u (hRU hu)⟩)⁻¹ * z * π ⟨u, hUb u (hRU hu)⟩ = z := by
    intro u hu
    set ub := π ⟨u, hUb u (hRU hu)⟩ with hubdef
    set γ : MulAut (UnbalancingLocal.CorrQuotient b) := MulAut.conj ub⁻¹ with hγdef
    have hγx : ∀ x, γ x = ub⁻¹ * x * ub := fun x => by
      rw [hγdef, MulAut.conj_apply, inv_inv]
    have hγa : γ abar = abar := by
      rw [hγx, habardef, hubdef, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [show (u : G)⁻¹ * a * u = u⁻¹ * (a * u) by group,
        ← mem_centralizer_singleton_iff.mp (hUa u (hRU hu)), inv_mul_cancel_left]
    have hγA : ∀ z ∈ A, γ z ∈ A := by
      intro z hz
      obtain ⟨l, hl, rfl⟩ := mem_map.mp hz
      have huL : u⁻¹ ∈ normalizer (L : Set G) := inv_mem (mem_inf.mp hu).2
      have hl' := (mem_normalizer_iff.mp huL (l : G)).mp hl
      rw [inv_inv] at hl'
      refine ⟨⟨u, hUb u (hRU hu)⟩⁻¹ * l * ⟨u, hUb u (hRU hu)⟩, ?_, ?_⟩
      · show (((⟨u, hUb u (hRU hu)⟩ : H)⁻¹ * l * ⟨u, hUb u (hRU hu)⟩ : H) : G) ∈ L
        simpa using hl'
      · rw [hγx, map_mul, map_mul, map_inv]
    have hγΔ : ∀ z ∈ A, γ (z * (abar * z * abar⁻¹)) = z * (abar * z * abar⁻¹) := by
      intro z hz
      obtain ⟨t, ht, htz⟩ := mem_map.mp ((hΔ _).mpr ⟨z, hz, rfl⟩)
      rw [← htz, hγx]
      have ht' : (t : G) ∈ T := ht
      have h1 : (u : G)⁻¹ * t * u ∈ H := mul_mem (mul_mem (inv_mem (hUb u (hRU hu))) t.2)
        (hUb u (hRU hu))
      have h2 := hcent u (hRU hu) t ht' h1 t.2
      rw [show ub⁻¹ * π t * ub = π ⟨(u : G)⁻¹ * t * u, h1⟩ by
        rw [hubdef, ← map_inv, ← map_mul, ← map_mul]
        rfl, h2]
    have hfixA : ∀ z ∈ A, γ z = z := by
      intro z hz
      have h1 := hγΔ z hz
      rw [map_mul, map_mul, map_mul, map_inv, hγa] at h1
      have hw := hγA z hz
      have h2 : z⁻¹ * γ z = abar * (z * (γ z)⁻¹) * abar⁻¹ := by
        calc z⁻¹ * γ z = z⁻¹ * (γ z * (abar * γ z * abar⁻¹)) * (abar * γ z * abar⁻¹)⁻¹ := by
              group
          _ = z⁻¹ * (z * (abar * z * abar⁻¹)) * (abar * γ z * abar⁻¹)⁻¹ := by rw [h1]
          _ = abar * (z * (γ z)⁻¹) * abar⁻¹ := by group
      have h3 : z⁻¹ * γ z ∈ A ⊓ B := by
        refine mem_inf.mpr ⟨mul_mem (inv_mem hz) hw, ?_⟩
        rw [h2]
        exact hγ _ (mul_mem hz (inv_mem hw))
      rw [hDbot, mem_bot] at h3
      calc γ z = z * (z⁻¹ * γ z) := by group
        _ = z := by rw [h3, mul_one]
    have hfixB : ∀ y ∈ B, γ y = y := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hBA y hy
      rw [map_mul, map_mul, map_inv, hγa, hfixA z hz]
    intro z hz
    have hle : A ⊔ B ≤ MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id _) :=
      sup_le (fun z hz => hfixA z hz) (fun y hy => hfixB y hy)
    have h1 : γ z = z := hle hz
    rwa [hγx] at h1
  have hNK : L ⊔ conjugate L a ≤ normalizer (N : Set G) := fun k hk =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pPrimeCore 2 H)
      (le_normalizer (hKH hk))
  have hRmem : ∀ u ∈ R, ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * u⁻¹ * k * u ∈ N := by
    intro u hu k hk
    have hstep : ∀ y ∈ L ⊔ conjugate L a, ∀ hy : y ∈ H,
        y⁻¹ * u⁻¹ * y * u ∈ N := by
      intro y hy hyH
      have hyAB : π ⟨y, hyH⟩ ∈ A ⊔ B := by
        have h1 : (⟨y, hyH⟩ : H) ∈ (L ⊔ conjugate L a).subgroupOf H := hy
        have h2 : (L ⊔ conjugate L a).subgroupOf H =
            L.subgroupOf H ⊔ (conjugate L a).subgroupOf H := by
          apply map_injective H.subtype_injective
          rw [map_subgroupOf_eq_of_le hKH, Subgroup.map_sup, map_subgroupOf_eq_of_le hLb,
            map_subgroupOf_eq_of_le hLaH]
        rw [h2] at h1
        have h3 := mem_map_of_mem π h1
        rw [Subgroup.map_sup] at h3
        exact h3
      have h1 := hfix u hu _ hyAB
      have huH := hUb u (hRU hu)
      have hzH : y⁻¹ * u⁻¹ * y * u ∈ H :=
        mul_mem (mul_mem (mul_mem (inv_mem hyH) (inv_mem huH)) hyH) huH
      refine ⟨⟨y⁻¹ * u⁻¹ * y * u, hzH⟩, ?_, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mp
      have h2 : (⟨y⁻¹ * u⁻¹ * y * u, hzH⟩ : H) =
          (⟨y, hyH⟩ : H)⁻¹ * ((⟨u, huH⟩ : H)⁻¹ * ⟨y, hyH⟩ * ⟨u, huH⟩) := by
        apply Subtype.ext
        simp only [coe_mul, coe_inv]
        group
      rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h3 : (((⟨u, huH⟩ : H)⁻¹ * ⟨y, hyH⟩ * ⟨u, huH⟩ : H) : UnbalancingLocal.CorrQuotient b) =
          π ⟨y, hyH⟩ := by
        rw [← h1]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rfl
      rw [h3]
      exact inv_mul_cancel _
    exact hstep k hk (hKH hk)
  have hRset : (R : Set G) = {u | u ∈ U ∧ ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * u⁻¹ * k * u ∈ N} := by
    ext u
    constructor
    · intro hu
      exact ⟨(mem_inf.mp hu).1, hRmem u hu⟩
    · rintro ⟨hu, hk⟩
      refine mem_inf.mpr ⟨hu, ?_⟩
      apply mem_normalizer_of_conjugate_eq
      obtain ⟨-, hperm⟩ := hnc u (mem_inf.mpr ⟨hUb u hu, hUJ u hu⟩)
      have hmem : conjugate L u ∈ ({L, conjugate L a} : Set (Subgroup G)) := by
        rw [← hperm]
        exact ⟨L, Or.inl rfl, rfl⟩
      rcases hmem with h1 | h1
      · exact h1
      · exfalso
        apply (Subgroup.nontrivial_iff_ne_bot A).mp hAnt
        rw [eq_bot_iff, ← hDbot]
        intro z hz
        refine mem_inf.mpr ⟨hz, ?_⟩
        obtain ⟨l, hl, rfl⟩ := mem_map.mp hz
        have hl' : (l : G) ∈ L := hl
        have huH := hUb u hu
        have h2 : (u : G)⁻¹ * l * u ∈ conjugate L a := by
          rw [← h1]
          exact conj_mem_conjugate hl' u
        have h3 : (u : G)⁻¹ * l * u ∈ H := mul_mem (mul_mem (inv_mem huH) l.2) huH
        have h4 := hk l (le_sup_left (a := L) hl')
        refine ⟨⟨(u : G)⁻¹ * l * u, h3⟩, h2, ?_⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        obtain ⟨n, hn, hneq⟩ := mem_map.mp h4
        have h5 : (⟨(u : G)⁻¹ * l * u, h3⟩ : H)⁻¹ * l = n⁻¹ := by
          apply Subtype.ext
          simp only [coe_mul, coe_inv]
          rw [show ((n : H) : G) = (l : G)⁻¹ * u⁻¹ * l * u from hneq]
          group
        rw [h5]
        exact inv_mem hn
  have haR : a ∉ R := by
    intro haR
    exact hne (conjugate_eq_of_mem_normalizer (mem_inf.mp haR).2)
  have hcover : ∀ u ∈ U, u ∉ R → u * a ∈ R := by
    intro u hu huR
    obtain ⟨-, hperm⟩ := hnc u (mem_inf.mpr ⟨hUb u hu, hUJ u hu⟩)
    have hmem : conjugate L u ∈ ({L, conjugate L a} : Set (Subgroup G)) := by
      rw [← hperm]
      exact ⟨L, Or.inl rfl, rfl⟩
    rcases hmem with h1 | h1
    · exact absurd (mem_inf.mpr ⟨hu, mem_normalizer_of_conjugate_eq h1⟩) huR
    · refine mem_inf.mpr ⟨mul_mem hu haU, mem_normalizer_of_conjugate_eq ?_⟩
      rw [← conjugate_conjugate, h1, conjugate_conjugate, haa, conjugate_one]
  have hzbot : zpowers a ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxR⟩ := mem_inf.mp hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxa
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, zpow_two, haa, one_zpow]
      exact one_mem _
    · exfalso
      apply haR
      rwa [zpow_add, zpow_mul, zpow_two, haa, one_zpow, one_mul, zpow_one] at hxR
  have hzsup : zpowers a ⊔ R = U := by
    apply le_antisymm (sup_le (zpowers_le.mpr haU) hRU)
    intro u hu
    by_cases huR : u ∈ R
    · exact mem_sup_right huR
    · have h1 := hcover u hu huR
      rw [show u = (u * a) * a⁻¹ by group]
      exact mul_mem (mem_sup_right h1) (mem_sup_left (inv_mem (mem_zpowers a)))
  have hzcomm : ∀ x ∈ zpowers a, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hya : Commute a y := (mem_centralizer_singleton_iff.mp (hUa y (hRU hy))).symm
    exact (hya.zpow_left k).eq
  have hRLa : R ≤ normalizer ((conjugate L a : Subgroup G) : Set G) := by
    intro u hu
    apply mem_normalizer_of_conjugate_eq
    rw [conjugate_conjugate_comm L (mem_centralizer_singleton_iff.mp (hUa u (hRU hu))),
      conjugate_eq_of_mem_normalizer (mem_inf.mp hu).2]
  set V := conjugate L a ⊔ R with hVdef
  have hLaV : conjugate L a ≤ V := le_sup_left
  have hVN : V ≤ normalizer ((conjugate L a : Subgroup G) : Set G) := sup_le le_normalizer hRLa
  have hR2 : IsPGroup 2 (R.subgroupOf V) := (hU2.to_le hRU).comap_subtype
  obtain ⟨D, hDR⟩ := hR2.exists_le_sylow
  set S := (D : Subgroup V).map V.subtype with hSdef
  have hSV : S ≤ V := map_subtype_le _
  have hSsyl : ∃ P : Sylow 2 V, (P : Subgroup V) = S.subgroupOf V :=
    ⟨D, (comap_map_eq_self_of_injective V.subtype_injective _).symm⟩
  obtain ⟨P, hP⟩ := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSV hSsyl
    hLaV hVN
  have hS2 : IsPGroup 2 S := D.isPGroup'.map V.subtype
  have hRS : R ≤ S := by
    intro r hr
    exact ⟨⟨r, le_sup_right (a := conjugate L a) hr⟩, hDR hr, rfl⟩
  set F := S ⊓ conjugate L a with hFdef
  have hFLa : F ≤ conjugate L a := inf_le_right
  have hFS : F ≤ S := inf_le_left
  have hFR : ⁅F, R⁆ = ⊥ := by
    refine eq_bot_of_le_two_group_of_le_odd hS2 hNodd ?_ ?_
    · rw [commutator_le]
      intro f hf r hr
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hFS hf) (hRS hr)) (inv_mem (hFS hf))) (inv_mem (hRS hr))
    · rw [commutator_le]
      intro f hf r hr
      have h1 := hRmem r⁻¹ (inv_mem hr) f⁻¹ (inv_mem (le_sup_right (a := L) (hFLa hf)))
      rwa [inv_inv, inv_inv, ← commutatorElement_def] at h1
  have hFRbot : F ⊓ R = ⊥ := by
    refine eq_bot_of_le_two_group_of_le_odd hS2 hNodd (inf_le_left.trans hFS) ?_
    intro f hf
    obtain ⟨hfF, hfR⟩ := mem_inf.mp hf
    have hfLa := hFLa hfF
    have hfa : f * a = a * f := mem_centralizer_singleton_iff.mp (hUa f (hRU hfR))
    have hfL : f ∈ L := by
      have h1 : f ∈ conjugate L a := hfLa
      rw [mem_conjugate_iff, ← hfa, mul_inv_cancel_right] at h1
      exact h1
    have hfH : f ∈ H := hLb hfL
    have h2 : π ⟨f, hfH⟩ ∈ A ⊓ B := mem_inf.mpr ⟨⟨⟨f, hfH⟩, hfL, rfl⟩, ⟨⟨f, hfH⟩, hfLa, rfl⟩⟩
    rw [hDbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  have hOLG : ∀ y ∈ L, ∀ hy : y ∈ H, (⟨y, hy⟩ : H) ∈ pPrimeCore 2 H →
      y ∈ (pPrimeCore 2 L).map L.subtype := by
    intro y hyL hyH hyN
    rw [← pPrimeCore_map_subgroupOf 2 L H hLb]
    have h1 : (⟨y, hyH⟩ : H) ∈ (pPrimeCore 2 (L.subgroupOf H)).map (L.subgroupOf H).subtype := by
      rw [map_pPrimeCore_eq_inf_of_isSubnormal hLsub]
      exact mem_inf.mpr ⟨hyL, hyN⟩
    exact ⟨⟨y, hyH⟩, h1, rfl⟩
  have hLL₂ : L.subgroupOf H ≠ (conjugate L a).subgroupOf H := by
    intro heq
    apply hne
    have h1 := congrArg (Subgroup.map H.subtype) heq
    rw [map_subgroupOf_eq_of_le hLb, map_subgroupOf_eq_of_le hLaH] at h1
    exact h1.symm
  obtain ⟨hL₂N, -, hLcore, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hL hL₂).2 hLL₂
  have hFQ : F ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L := by
    intro f hf
    have hfLa := hFLa hf
    have hfH : f ∈ H := hLaH hfLa
    have hfN : f ∈ normalizer (L : Set G) :=
      mem_normalizer_of_subgroupOf hLb
        (hL₂N (show (⟨f, hfH⟩ : H) ∈ (conjugate L a).subgroupOf H from hfLa))
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hfH, hfN⟩, mem_coreActionKernel.mpr ⟨hfN, fun l hl => ?_⟩⟩
    have hlH : l ∈ H := hLb hl
    have h1 : ⁅(⟨l, hlH⟩ : H)⁻¹, (⟨f, hfH⟩ : H)⁻¹⁆ ∈
        ⁅L.subgroupOf H, (conjugate L a).subgroupOf H⁆ :=
      commutator_mem_commutator (inv_mem (show (⟨l, hlH⟩ : H) ∈ L.subgroupOf H from hl))
        (inv_mem (show (⟨f, hfH⟩ : H) ∈ (conjugate L a).subgroupOf H from hfLa))
    have h2 := mem_map_of_mem H.subtype (mem_inf.mp (hLcore h1)).1
    rw [pPrimeCore_map_subgroupOf 2 L H hLb] at h2
    have h3 : H.subtype ⁅(⟨l, hlH⟩ : H)⁻¹, (⟨f, hfH⟩ : H)⁻¹⁆ = l⁻¹ * f⁻¹ * l * f := by
      simp [commutatorElement_def]
    rwa [h3] at h2
  have hRQ : R ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L := by
    intro r hr
    have hrH := hUb r (hRU hr)
    have hrN := (mem_inf.mp hr).2
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hrH, hrN⟩, mem_coreActionKernel.mpr ⟨hrN, fun l hl => ?_⟩⟩
    have hlH : l ∈ H := hLb hl
    have h1 := (mem_normalizer_iff.mp (inv_mem hrN) l).mp hl
    rw [inv_inv] at h1
    have hyL : l⁻¹ * r⁻¹ * l * r ∈ L := by
      rw [show l⁻¹ * r⁻¹ * l * r = l⁻¹ * (r⁻¹ * l * r) by group]
      exact mul_mem (inv_mem hl) h1
    have hyH : l⁻¹ * r⁻¹ * l * r ∈ H :=
      mul_mem (mul_mem (mul_mem (inv_mem hlH) (inv_mem hrH)) hlH) hrH
    obtain ⟨n, hn, hneq⟩ := mem_map.mp (hRmem r hr l (le_sup_left (a := L) hl))
    have hneq' : n = ⟨l⁻¹ * r⁻¹ * l * r, hyH⟩ := Subtype.ext hneq
    exact hOLG _ hyL hyH (hneq' ▸ hn)
  have hLJ : pRank 2 ↥L = pRank 2 ↥J := by
    obtain ⟨δ, hδs, -, hδk, -⟩ := exists_diagonal_hom hABc hγ hΔ
    have hδi : Function.Injective δ := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have h1 : (u : UnbalancingLocal.CorrQuotient b) ∈ A ⊓ B :=
        mem_inf.mpr ⟨u.2, ((hδk u).mp hu).1⟩
      rw [hDbot, mem_bot] at h1
      exact Subtype.ext h1
    let δe : ↥A ≃* ↥(UnbalancingLocal.corrImage b T) := MulEquiv.ofBijective δ ⟨hδi, hδs⟩
    obtain ⟨eL, -⟩ := exists_restriction_quotient_equiv_of_subnormal hLb hLsub
    let e : J ⧸ pPrimeCore 2 J ≃* L ⧸ pPrimeCore 2 L :=
      eJ.symm.trans (eT.trans (δe.symm.trans eL.symm))
    rw [pRank_eq_pRank_quotient_pPrimeCore ↥L, pRank_eq_pRank_quotient_pPrimeCore ↥J,
      pRank_eq_of_mulEquiv one_lt_two e]
  have hFL : pRank 2 ↥F = pRank 2 ↥L := by
    have h1 := (SectionRank.pRank_sylow P).2
    have e₁ : ↥F ≃* ↥(P : Subgroup ↥(conjugate L a)) :=
      (subgroupOfEquivOfLe hFLa).symm.trans (MulEquiv.subgroupCongr hP.symm)
    have e₂ : ↥(conjugate L a) ≃* ↥L :=
      (L.equivMapOfInjective (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective).symm
    rw [pRank_eq_of_mulEquiv one_lt_two e₁, h1, pRank_eq_of_mulEquiv one_lt_two e₂]
  have hidx : R.relIndex U = 2 := by
    show (R.subgroupOf U).index = 2
    rw [index_eq_two_iff]
    refine ⟨⟨a, haU⟩, fun u => ?_⟩
    by_cases huR : (u : G) ∈ R
    · refine Or.inr ⟨huR, fun h1 => haR ?_⟩
      have h2 : (u : G) * a ∈ R := h1
      have h3 := mul_mem (inv_mem huR) h2
      rwa [inv_mul_cancel_left] at h3
    · exact Or.inl ⟨hcover u u.2 huR, huR⟩
  have hUR := pRank_le_add_one_of_relIndex_eq_two hidx
  have hFRQ := pRank_add_le_of_commute hFQ hRQ hFR hFRbot
  refine ⟨R, hRset, hzbot, hzsup, hzcomm, hidx, ⟨F, hFLa, ⟨P, hP⟩, hFR, hFRbot, sup_le hFQ hRQ⟩,
    ?_, hLJ⟩
  have h1 : pRank 2 ↥L + pRank 2 ↥U - 1 ≤ pRank 2 ↥F + pRank 2 ↥R := by
    rw [hFL]
    omega
  exact h1.trans hFRQ

end CFSG.ComponentClassification.UnbalancedCorr
