module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitSLLift
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoverExclusion

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

theorem isSubnormal_subgroupOf_of_le {G : Type*} [Group G] {A D C : Subgroup G} (hDC : D ≤ C)
    (h : (A.subgroupOf C).IsSubnormal) : (A.subgroupOf D).IsSubnormal := by
  have h1 := h.subgroupOf (K := D.subgroupOf C)
  have heq : A.subgroupOf D = ((A.subgroupOf C).subgroupOf (D.subgroupOf C)).comap
      (subgroupOfEquivOfLe hDC).symm.toMonoidHom := by
    ext x
    exact Iff.rfl
  rw [heq]
  exact h1.comap _

theorem isSubnormal_commutator_comap {Q B : Type} [Group Q] [Group B] (σ : Q →* B)
    {S C : Subgroup B} (hSC : S ≤ C) (h : (S.subgroupOf C).IsSubnormal) :
    (⁅S.comap σ, S.comap σ⁆.subgroupOf (C.comap σ)).IsSubnormal := by
  have hT₁C : S.comap σ ≤ C.comap σ := comap_mono hSC
  let σ' : C.comap σ →* C := (σ.comp (C.comap σ).subtype).codRestrict C (fun x => x.2)
  have h1 : ((S.comap σ).subgroupOf (C.comap σ)).IsSubnormal := by
    have heq : (S.comap σ).subgroupOf (C.comap σ) = (S.subgroupOf C).comap σ' := by
      ext x
      exact Iff.rfl
    rw [heq]
    exact h.comap σ'
  have hle : ⁅S.comap σ, S.comap σ⁆ ≤ S.comap σ := commutator_self_le _
  have hn : (⁅S.comap σ, S.comap σ⁆.subgroupOf (S.comap σ)).Normal := by
    rw [normal_subgroupOf_iff hle]
    intro x k hx hk
    have heq : k * x * k⁻¹ = ⁅k, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem (commutator_mem_commutator hk (hle hx)) hx
  have h2 := isSubnormal_subgroupOf_subgroupOf hT₁C hn.isSubnormal
  exact Subgroup.IsSubnormal.trans (fun x hx => hle hx) h2 h1

theorem isPComponent_of_mulEquiv_sl {Q : Type*} [Group Q] [Finite Q] {T C : Subgroup Q}
    (hTC : T ≤ C) (hsub : (T.subgroupOf C).IsSubnormal) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) (eT : T ≃* SL(2, GaloisField p n)) : IsPComponent 2 (T.subgroupOf C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n hn]
    omega
  have hTq : IsQuasisimple T :=
    LocalCores.isQuasisimple_of_mulEquiv eT.symm (isQuasisimple_sl_two h4)
  have hcore := pPrimeCore_eq_bot_of_mulEquiv_sl hp2 h5 eT
  refine (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T C hTC).mpr ⟨hsub, ?_, ?_⟩
  · exact CatalogueBPrimeJoin.primeResidual_eq_top_of_corefree_quasisimple 2 hTq hcore
  · exact LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm hTq

theorem hull_lift (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers)
    {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (ρ : G →* MulAut (K ⧸ centralPreimage (pPrimeCore 2 K)))
    (hρK : ∀ k : K, ρ (k : G) = MulAut.conj (k : K ⧸ centralPreimage (pPrimeCore 2 K)))
    (hZ : center (K ⧸ centralPreimage (pPrimeCore 2 K)) = ⊥)
    (hsol : Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ centralPreimage (pPrimeCore 2 K))))
    {a₀ : G} (ha₀ : a₀ * a₀ = 1) (haρ : orderOf (ρ.rangeRestrict a₀) = 2) {E₀ : Subgroup G}
    (hEodd : Odd (Nat.card (E₀.map ρ.rangeRestrict))) {u : ρ.range} (hu : orderOf u = 2)
    {S : Subgroup ρ.range} (hSu : S ≤ centralizer ({u} : Set ρ.range))
    (hSc : IsPComponent 2 (S.subgroupOf (centralizer ({u} : Set ρ.range))))
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) (eS : S ≃* SL(2, GaloisField p n))
    (hSZ : (center S).map S.subtype = zpowers u)
    (hprop : ActsProperly (ρ.rangeRestrict a₀) (E₀.map ρ.rangeRestrict) S ⊥) :
    ∃ T : Subgroup (K ⧸ pPrimeCore 2 K), ∃ γK ∈ T, orderOf γK = 2 ∧
      T ≤ centralizer ({γK} : Set (K ⧸ pPrimeCore 2 K)) ∧
      IsPComponent 2 (T.subgroupOf (centralizer ({γK} : Set (K ⧸ pPrimeCore 2 K)))) ∧
      Nonempty (T ≃* SL(2, GaloisField p n)) ∧
      (∀ x ∈ T, conjQuotAction K (pPrimeCore 2 K) a₀ x ∈ T) ∧
      (∀ e ∈ E₀, ∀ x ∈ T, conjQuotAction K (pPrimeCore 2 K) e x ∈ T) ∧
      conjQuotAction K (pPrimeCore 2 K) a₀ γK = γK ∧
      (∃ x ∈ T, conjQuotAction K (pPrimeCore 2 K) a₀ x ≠ x) ∧
      ∃ e ∈ E₀, ∃ x ∈ T, conjQuotAction K (pPrimeCore 2 K) e x ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρone : ∀ k : K, ρ (k : G) = 1 ↔ k ∈ centralPreimage (pPrimeCore 2 K) := by
    intro k
    rw [hρK]
    constructor
    · intro h
      have hc : (k : K ⧸ centralPreimage (pPrimeCore 2 K)) ∈
          center (K ⧸ centralPreimage (pPrimeCore 2 K)) := by
        rw [mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (K ⧸ centralPreimage (pPrimeCore 2 K)) => φ g) h
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * (k : K ⧸ centralPreimage (pPrimeCore 2 K))
            = (k * g * (k : K ⧸ centralPreimage (pPrimeCore 2 K))⁻¹) * k := by rw [h1]
          _ = k * g := by group
      rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hc
      exact hc
    · intro h
      have h1 : (k : K ⧸ centralPreimage (pPrimeCore 2 K)) = 1 :=
        (QuotientGroup.eq_one_iff k).mpr h
      rw [h1, map_one]
  have hRle : pPrimeCore 2 K ≤ (ρ.rangeRestrict.comp K.subtype).ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact (hρone r).mpr (le_centralPreimage _ hr)
  obtain ⟨σ, hσmk⟩ : ∃ σ : K ⧸ pPrimeCore 2 K →* ρ.range,
      ∀ k : K, σ (k : K ⧸ pPrimeCore 2 K) = ρ.rangeRestrict (k : G) :=
    ⟨QuotientGroup.lift _ (ρ.rangeRestrict.comp K.subtype) hRle, fun k => rfl⟩
  have hσker : σ.ker ≤ center (K ⧸ pPrimeCore 2 K) := by
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have h2 := MonoidHom.mem_ker.mp hq
    rw [hσmk] at h2
    exact (hρone k).mp (congrArg Subtype.val h2)
  have hσker2 : IsPGroup 2 σ.ker :=
    (center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)).to_le
      hσker
  have hSperf : ⁅S, S⁆ = S := commutator_self_of_isPComponent hSu hSc
  have : Group.IsPerfect S := Subgroup.isPerfect_iff.mpr hSperf
  have hSr : S ≤ σ.range := by
    intro s hs
    obtain ⟨q, hq⟩ := OuterAutomorphisms.perfect_action_inner (ρ.range.subtype.comp S.subtype)
      ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨(k : K ⧸ pPrimeCore 2 K), Subtype.ext ?_⟩
    rw [hσmk]
    change ρ (k : G) = ((s : ρ.range) : MulAut (K ⧸ centralPreimage (pPrimeCore 2 K)))
    rw [hρK]
    exact hq.symm
  obtain ⟨hTS, hTinj⟩ := exists_sl_lift hGA hGC σ hσker hσker2 hSr hSperf hp2 hn eS
  obtain ⟨T, hT⟩ : ∃ T, T = ⁅S.comap σ, S.comap σ⁆ := ⟨_, rfl⟩
  rw [← hT] at hTS hTinj
  have hφmem : ∀ x : T, σ x ∈ S := fun x => by
    rw [← hTS]
    exact mem_map_of_mem σ x.2
  let φ : T →* S := (σ.comp T.subtype).codRestrict S hφmem
  have hφbij : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have h1 : σ ((x : K ⧸ pPrimeCore 2 K) * (y : K ⧸ pPrimeCore 2 K)⁻¹) = 1 := by
        rw [map_mul, map_inv, mul_inv_eq_one]
        exact congrArg Subtype.val hxy
      exact Subtype.ext (mul_inv_eq_one.mp (hTinj _ (mul_mem x.2 (inv_mem y.2)) h1))
    · rintro ⟨s, hs⟩
      rw [← hTS] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact ⟨⟨x, hx⟩, rfl⟩
  let eT : T ≃* SL(2, GaloisField p n) := (MulEquiv.ofBijective φ hφbij).trans eS
  have h5 : 5 ≤ p ^ n :=
    five_le_of_isPerfect_sl hp2 hn
      (Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective)
  obtain ⟨γK, hγKT, hγK2, hγK1, hγKc, hγKu⟩ := exists_central_involution hp2 hn eT
  have hσγ : σ γK = u := by
    have hc : ∀ s ∈ S, σ γK * s = s * σ γK := by
      intro s hs
      rw [← hTS] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      rw [← map_mul, ← map_mul, hγKc x hx]
    have hmem : σ γK ∈ (center S).map S.subtype :=
      ⟨⟨σ γK, hφmem ⟨γK, hγKT⟩⟩, mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm, rfl⟩
    rw [hSZ] at hmem
    have hu2 : u ^ 2 = 1 := by
      have h := pow_orderOf_eq_one u
      rwa [hu] at h
    rcases eq_one_or_eq_of_mem_zpowers hu2 hmem with h | h
    · exact absurd (hTinj γK hγKT h) hγK1
    · exact h
  have hequiv : ∀ (g : G) (q : K ⧸ pPrimeCore 2 K),
      σ (conjQuotAction K (pPrimeCore 2 K) g q) =
        ρ.rangeRestrict g * σ q * (ρ.rangeRestrict g)⁻¹ := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hl : g * (k : G) * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ k.2 g
      rw [conjQuotAction_mk' g k hl, hσmk, hσmk]
      change ρ.rangeRestrict (g * k * g⁻¹) = _
      rw [map_mul, map_mul, map_inv]
  have hTinv : ∀ g : G, ρ.rangeRestrict g ∈ normalizer (S : Set ρ.range) →
      ∀ x ∈ T, conjQuotAction K (pPrimeCore 2 K) g x ∈ T := by
    intro g hg x hx
    have hT₁c : (S.comap σ).map (conjQuotAction K (pPrimeCore 2 K) g).toMonoidHom ≤
        S.comap σ := by
      rintro _ ⟨y, hy, rfl⟩
      change σ (conjQuotAction K (pPrimeCore 2 K) g y) ∈ S
      rw [hequiv]
      exact (mem_normalizer_iff.mp hg _).mp hy
    have h1 : T.map (conjQuotAction K (pPrimeCore 2 K) g).toMonoidHom ≤ T := by
      rw [hT, map_commutator]
      exact commutator_mono hT₁c hT₁c
    exact h1 (mem_map_of_mem _ hx)
  have htS : ρ.rangeRestrict a₀ ∈ normalizer (S : Set ρ.range) :=
    (hprop.1 (subset_closure (Set.mem_insert _ _))).1
  have hES : ∀ e ∈ E₀, ρ.rangeRestrict e ∈ normalizer (S : Set ρ.range) :=
    fun e he => (hprop.1 (subset_closure (Set.mem_insert_of_mem _ (mem_map_of_mem _ he)))).1
  have hcent : ∀ g : G, (∀ x ∈ T, conjQuotAction K (pPrimeCore 2 K) g x = x) →
      ∀ s ∈ S, ⁅s, ρ.rangeRestrict g⁆ ∈ (⊥ : Subgroup ρ.range) := by
    intro g hg s hs
    rw [← hTS] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    have h1 := hequiv g x
    rw [hg x hx] at h1
    rw [mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    calc σ x * ρ.rangeRestrict g
        = (ρ.rangeRestrict g * σ x * (ρ.rangeRestrict g)⁻¹) * ρ.rangeRestrict g := by rw [← h1]
      _ = ρ.rangeRestrict g * σ x := by group
  have hcc : ∀ q, conjQuotAction K (pPrimeCore 2 K) a₀
      (conjQuotAction K (pPrimeCore 2 K) a₀ q) = q := by
    intro q
    rw [← MulAut.mul_apply, ← map_mul, ha₀, map_one, MulAut.one_apply]
  have hfixγ := fixed_of_unique_central hγKT hγK1 hγKc hγKu
    (conjQuotAction K (pPrimeCore 2 K) a₀) (hTinv _ htS) hcc
  have hTC : T ≤ centralizer ({γK} : Set (K ⧸ pPrimeCore 2 K)) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hγKc x hx).symm
  have hCC : centralizer ({γK} : Set (K ⧸ pPrimeCore 2 K)) ≤
      (centralizer ({u} : Set ρ.range)).comap σ := by
    intro x hx
    rw [mem_comap, mem_centralizer_singleton_iff, ← hσγ, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp hx]
  have hsub : (T.subgroupOf (centralizer ({γK} : Set (K ⧸ pPrimeCore 2 K)))).IsSubnormal := by
    have h1 := isSubnormal_commutator_comap σ hSu (isPComponent_data hSu hSc).1
    rw [← hT] at h1
    exact isSubnormal_subgroupOf_of_le hCC h1
  refine ⟨T, γK, hγKT, hγK2, hTC, isPComponent_of_mulEquiv_sl hTC hsub hp2 h5 eT, ⟨eT⟩,
    hTinv _ htS, fun e he => hTinv e (hES e he), hfixγ, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_mem_of_orderOf_two_of_odd hEodd haρ
      (hprop.2.1 _ (subset_closure (Set.mem_insert _ _)) (hcent a₀ hall))
  · obtain ⟨_, ⟨h, hh, rfl⟩, s, hs, hse⟩ := hprop.2.2
    refine ⟨h, hh, ?_⟩
    by_contra hall
    push Not at hall
    exact hse (hcent h hall s hs)

variable {X : Type} [Group X] [Finite X]

theorem propA_false (hI : TBInputs) (hX : TBSetting X) {b a : X}
    {Y E : Subgroup X} (hC : IsUnbalancingConfig b a Y E)
    (hodd : OddLieType (Y ⧸ Open.fusionZStar Y))
    (hnot : ∀ p f : ℕ, p.Prime → p ≠ 2 → ¬ LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb, ha, hab, hYb, hYc, hEa, hEb, hYa, hYE⟩ := id hC
  obtain ⟨haY, hEY⟩ := hC.normalizes
  have hYn : (Y.subgroupOf (hull Y a E)).Normal := hull_normal hYa.le hYE.le
  obtain ⟨hKq, hZ, hM4, haρ, hEρ⟩ := hull_data hC hodd hnot
  have hYH : Y ≤ hull Y a E := le_hull_left Y a E
  have hEH : E ≤ hull Y a E := le_hull_right Y a E
  have haH : a ∈ hull Y a E := mem_hull_elem Y a E
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hYq := twoComponent_coreQuotient_quasisimple hYb hYc
  have hnt : Nontrivial (Y ⧸ pPrimeCore 2 Y) := by
    have := hYq.2.1
    exact (QuotientGroup.mk'_surjective (center (Y ⧸ pPrimeCore 2 Y))).nontrivial
  have hY1 : (E.subgroupOf (hull Y a E)).map (conjQuotAction (Y.subgroupOf (hull Y a E))
      (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).rangeRestrict ≠ ⊥ := by
    obtain ⟨e₀, he₀, x₀, hx₀⟩ := exists_moved_of_commutator_eq hEY hYE hnt
    have hne : ¬ ∀ m ∈ Y, ⁅m, e₀⁆ ∈ oddCoreIn Y := fun h =>
      hx₀ (by rw [(oddQuotAction_eq_one_iff _).mpr h, MulAut.one_apply])
    have h1 := rangeRestrict_ne_one_of_not_trivial hYH hYq (hEH he₀) (hEY he₀) hne
    intro hbot
    apply h1
    have h2 := mem_map_of_mem (conjQuotAction (Y.subgroupOf (hull Y a E))
      (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).rangeRestrict
      (show (⟨e₀, hEH he₀⟩ : hull Y a E) ∈ E.subgroupOf (hull Y a E) from he₀)
    rw [hbot, mem_bot] at h2
    exact h2
  obtain ⟨u, hu, S, hSu, hSc, ⟨p, n, hpf, hp2, hn, ⟨eS⟩⟩, hSZ, hprop⟩ :=
    hI.propA _ hM4 _ haρ _ hY1 hEρ
  obtain ⟨⟨hsimple, hnonab⟩, -⟩ := normal_quasisimple_section_automorphism_image
    (Y.subgroupOf (hull Y a E)) (pPrimeCore 2 (Y.subgroupOf (hull Y a E))) hKq
  have hHb : hull Y a E ≤ centralizer ({b} : Set X) := (config_almost_simple hC).1
  have hHtop : hull Y a E ≠ ⊤ :=
    (lt_of_le_of_lt hHb (centralizer_lt_top (hX.not_mem_center hb))).ne
  have hKH := kGroupOver_of_kProper SectionRank.catalog_of_mulEquiv catalog_of_abelian_simple
    hX.kProper _ hHtop
  have hcat := hKH _ _ hsimple
  have hsol := @hI.schreier _ _ _ hsimple hnonab hcat
  have hEodd : Odd (Nat.card ((E.subgroupOf (hull Y a E)).map
      (conjQuotAction (Y.subgroupOf (hull Y a E))
        (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).rangeRestrict)) :=
    Nat.coprime_two_left.mp ((coprime_card_oddCentralizerCore _).coprime_dvd_right
      (card_dvd_of_le hEρ))
  obtain ⟨T, γK, hγKT, hγK2, hTC, hTc, ⟨eT⟩, haT, hET, hfixγ, hant, hent⟩ :=
    hull_lift hI.griessTable hI.griessCovers (Y.subgroupOf (hull Y a E)) _
      (fun k => conjQuotAction_coe k) hZ hsol (a₀ := ⟨a, haH⟩) (Subtype.ext ha2) haρ hEodd hu
      hSu hSc hp2 hn eS hSZ hprop
  have hJM : ∀ g : hull Y a E, (g : X) ∈ normalizer (Y : Set X) := fun g =>
    UnbalancedLayer.mem_normalizer_of_subgroupOf hYH (by
      rw [normalizer_eq_top_iff.mpr hYn]
      exact mem_top g)
  have hdict : ∀ (g : hull Y a E) (q : Y.subgroupOf (hull Y a E) ⧸
      pPrimeCore 2 (Y.subgroupOf (hull Y a E))),
      Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hYH)
          (conjQuotAction (Y.subgroupOf (hull Y a E)) (pPrimeCore 2 (Y.subgroupOf (hull Y a E)))
            g q) =
        oddQuotAction Y ⟨g, hJM g⟩
          (Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hYH) q) :=
    fun g q => quotientPPrimeCoreCongr_conjQuotAction hYH g (hJM g) q
  generalize Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hYH) = ι at hdict
  obtain ⟨hT'C, hT'c⟩ := isPComponent_centralizer_map ι hTC hTc
  have hφaγ : oddQuotAction Y ⟨a, haY⟩ (ι γK) = ι γK := by
    rw [show (⟨a, haY⟩ : normalizer (Y : Set X)) =
      ⟨((⟨a, haH⟩ : hull Y a E) : X), hJM _⟩ from rfl, ← hdict, hfixγ]
  have hγ2 : ι γK ^ 2 = 1 := by
    rw [← map_pow]
    have h := pow_orderOf_eq_one γK
    rw [hγK2] at h
    rw [h, map_one]
  have hγ1 : ι γK ≠ 1 := by
    intro h
    have h1 : γK = 1 := ι.injective (h.trans (map_one ι).symm)
    rw [h1, orderOf_one] at hγK2
    omega
  obtain ⟨γ, hγY, hγ, hγa, hγz⟩ := exists_involution_lift_mk (by rw [pow_two]; exact ha2) haY
    hγ2 hγ1 hφaγ
  have hTmap : ∀ g : hull Y a E, (∀ x ∈ T, conjQuotAction (Y.subgroupOf (hull Y a E))
      (pPrimeCore 2 (Y.subgroupOf (hull Y a E))) g x ∈ T) →
      ∀ x ∈ T.map ι.toMonoidHom, oddQuotAction Y ⟨g, hJM g⟩ x ∈ T.map ι.toMonoidHom := by
    rintro g hg _ ⟨y, hy, rfl⟩
    change oddQuotAction Y ⟨g, hJM g⟩ (ι y) ∈ T.map ι.toMonoidHom
    rw [← hdict]
    exact mem_map_of_mem _ (hg y hy)
  refine false_of_quotient_component hI hX hC haY hEY hγY hγ hγa (T := T.map ι.toMonoidHom)
    (by rw [hγz]; exact hT'C) (by rw [hγz]; exact hT'c)
    (by rw [hγz]; exact mem_map_of_mem _ hγKT) hp2 hn ((ι.subgroupMap T).symm.trans eT)
    (hTmap ⟨a, haH⟩ haT) (fun e he => hTmap ⟨e, hEH he⟩ (hET _ he)) ?_ ?_
  · obtain ⟨x, hx, hxa⟩ := hant
    refine ⟨ι x, mem_map_of_mem _ hx, fun h => hxa (ι.injective ?_)⟩
    rw [hdict]
    exact h
  · obtain ⟨e, he, x, hx, hxe⟩ := hent
    refine ⟨(e : X), he, ι x, mem_map_of_mem _ hx, fun h => hxe (ι.injective ?_)⟩
    rw [hdict]
    exact h

theorem chevalleyExclusion_of_inputs (hI : TBInputs) :
    ChevalleyExclusion := by
  intro X _ _ _ hnonab hK hz hU b a Y E hC hodd
  by_contra hcon
  exact propA_false hI ⟨inferInstance, hnonab, hK, hz, hU⟩ hC hodd
    fun p f hp hp2 hm => hcon ⟨p, f, hp, hp2, hm⟩

end CFSG.ComponentClassification.TBLit
