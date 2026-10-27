module

public import CFSG.CharacterTheory.Semidihedral.StationaryOddLocalization
public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupCyclingOddControl
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusion
public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupOddCycling
public import CFSG.CharacterTheory.Semidihedral.LocalPrimeFailureSupport
public import CFSG.Dihedral.OriginalSylowControl

public section

namespace CFSG.Semidihedral.StationaryLayerCover

open scoped Pointwise
open CFSG.Open CFSG.DihedralBlueprint
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Semidihedral.StationaryOddLocalization

variable {G : Type} [Group G]

theorem isPerfect_of_nonabelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    have hcomm := isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)
    exact (hab (hcomm a b)).elim
  · exact h

theorem exists_fixedFree_normalizer_element [Finite G] [Group.IsPerfect G] {n : ℕ}
    (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) (V : Subgroup G)
    (hVS : V ≤ S) [hV : IsKleinFour V] :
    ∃ g ∈ Subgroup.normalizer (V : Set G), ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v := by
  classical
  have hrange := ((CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S f).1
    V hVS hV).1
  let c : {x : V // x ≠ 1} ≃ Fin 3 :=
    Finite.equivFinOfCardEq CFSG.Semidihedral.Local.card_nontrivial
  let ψ : MulAut V ≃* Equiv.Perm (Fin 3) :=
    (MulEquiv.ofBijective _ CFSG.Semidihedral.Local.nontrivialPerm_bijective).trans
      c.permCongrHom
  have hψ : ∀ (σ : MulAut V) (x : {x : V // x ≠ 1}),
      ψ σ (c x) = c (CFSG.Semidihedral.Local.nontrivialPerm V σ x) := by
    intro σ x
    change c (CFSG.Semidihedral.Local.nontrivialPerm V σ (c.symm (c x))) = _
    rw [Equiv.symm_apply_apply]
  obtain ⟨ρ, hρ3, hρ1⟩ := CFSG.Semidihedral.Local.perm_three_exists_cycle
  obtain ⟨y, hy⟩ : ψ.symm ρ ∈ V.normalizerMonoidHom.range := by
    rw [hrange]
    trivial
  refine ⟨y, y.2, fun v hv hv1 hfix => ?_⟩
  let x : {x : V // x ≠ 1} := ⟨⟨v, hv⟩, fun h1 => hv1 (congrArg Subtype.val h1)⟩
  have hx : CFSG.Semidihedral.Local.nontrivialPerm V (ψ.symm ρ) x = x := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hy
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    change (((ψ.symm ρ) ⟨v, hv⟩ : V) : G) = v
    rw [← h]
    exact hfix
  have h := hψ (ψ.symm ρ) x
  rw [MulEquiv.apply_symm_apply, hx] at h
  exact CFSG.Semidihedral.Local.perm_three_fixed_free ρ hρ3 hρ1 (c x) h

theorem mem_of_odd_orderOf_of_mem_sup {Z K : Subgroup G}
    (hcomm : ∀ a ∈ Z, ∀ k ∈ K, Commute a k) (hinf : Z ⊓ K = ⊥) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    {x : G} (hx : x ∈ Z ⊔ K) (hodd : Odd (orderOf x)) : x ∈ K := by
  have hZK : Z ≤ Subgroup.normalizer (K : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun k hk => (hcomm z hz k hk).eq.symm)
  have hx' : x ∈ (Z : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z K hZK]
    exact hx
  obtain ⟨z, hz, k, hk, rfl⟩ := hx'
  obtain ⟨j, hj⟩ := hodd
  have hpow : z ^ orderOf (z * k) * k ^ orderOf (z * k) = 1 := by
    rw [← (hcomm z hz k hk).mul_pow, pow_orderOf_eq_one]
  have hzm : z ^ orderOf (z * k) ∈ Z ⊓ K := by
    refine ⟨Z.pow_mem hz _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact K.inv_mem (K.pow_mem hk _)
  rw [hinf, Subgroup.mem_bot, hj, pow_succ, pow_mul, hZ2 z hz, one_pow, one_mul] at hzm
  show z * k ∈ K
  rw [hzm, one_mul]
  exact hk

theorem isSylowIn_map_conj [Finite G] {ell : ℕ} {P D : Subgroup G} (hP : IsSylowIn ell P D)
    {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    IsSylowIn ell (P.map (MulAut.conj g).toMonoidHom) D := by
  obtain ⟨hPD, hPp, hmax⟩ := hP
  refine ⟨?_, hPp.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hPD hy)
  · intro X hXD hXp hPX
    have hcomap : X.comap (MulAut.conj g).toMonoidHom = P := by
      refine hmax _ ?_ (hXp.comap_of_injective _ (MulAut.conj g).injective)
        (Subgroup.map_le_iff_le_comap.mp hPX)
      intro x hx
      exact (Subgroup.mem_normalizer_iff.mp hg x).mpr (hXD hx)
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective]

theorem exists_mul_mem_normalizer [Finite G] {ell : ℕ} (hell : ell.Prime) {P D : Subgroup G}
    (hP : IsSylowIn ell P D) {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    ∃ d ∈ D, d * g ∈ Subgroup.normalizer (P : Set G) := by
  have : Fact ell.Prime := ⟨hell⟩
  obtain ⟨P₁, hP₁⟩ := (isSylowIn_iff_exists_sylow ell P D).mp hP
  obtain ⟨P₂, hP₂⟩ := (isSylowIn_iff_exists_sylow ell _ D).mp (isSylowIn_map_conj hP hg)
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D P₂ P₁
  refine ⟨d, d.2, ?_⟩
  have h1 : ((d • P₂ : Sylow ell D) : Subgroup D).map D.subtype =
      ((P₂ : Subgroup D).map D.subtype).map (MulAut.conj (d : G)).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    exact CFSG.Semidihedral.Local.map_subtype_map_conj D (P₂ : Subgroup D) d
  rw [hd, hP₁, hP₂, Subgroup.map_map] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : (MulAut.conj (d : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom x ∈ P := by
      rw [h1]
      exact Subgroup.mem_map_of_mem _ hx
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, mul_assoc] using hmem
  · intro hx
    rw [h1] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have := congrArg (fun z => (d * g)⁻¹ * z * (d * g)) hyx
      simp only [mul_inv_rev] at this
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
        mul_inv_cancel, mul_one, one_mul] using this
    exact hyx' ▸ hy

theorem mk_mem_center_of_commutator_mem {A : Subgroup G} {t : G} (htA : t ∈ A)
    (h : ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ (CFSG.pPrimeCore 2 A).map A.subtype) :
    (QuotientGroup.mk (⟨t, htA⟩ : A) : A ⧸ CFSG.pPrimeCore 2 A) ∈
      Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : a * ⟨t, htA⟩ * a⁻¹ * (⟨t, htA⟩ : A)⁻¹ ∈ CFSG.pPrimeCore 2 A := by
    obtain ⟨r, hr, hreq⟩ := h a a.2
    have heq : a * ⟨t, htA⟩ * a⁻¹ * (⟨t, htA⟩ : A)⁻¹ = r := Subtype.ext hreq.symm
    rw [heq]
    exact hr
  have h1 : (QuotientGroup.mk (a * ⟨t, htA⟩ * a⁻¹ * (⟨t, htA⟩ : A)⁻¹) :
      A ⧸ CFSG.pPrimeCore 2 A) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem le_normalizer_map_pPrimeCore (H : Subgroup G) :
    H ≤ Subgroup.normalizer (((CFSG.pPrimeCore 2 H).map H.subtype : Subgroup G) : Set G) :=
  CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized H H H.le_normalizer
    (CFSG.pPrimeCore 2 H)

theorem inf_map_pPrimeCore_le [Finite G] {A K : Subgroup G} (hAK : A ≤ K) :
    A ⊓ (CFSG.pPrimeCore 2 K).map K.subtype ≤ (CFSG.pPrimeCore 2 A).map A.subtype := by
  let X := A ⊓ (CFSG.pPrimeCore 2 K).map K.subtype
  have hXA : X ≤ A := inf_le_left
  have hn : (X.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((le_inf Subgroup.le_normalizer (hAK.trans (le_normalizer_map_pPrimeCore K))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hodd : Nat.Coprime 2 (Nat.card (X.subgroupOf A)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXA).toEquiv]
    have hR : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact hR.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hle : X.subgroupOf A ≤ CFSG.pPrimeCore 2 A := le_sSup ⟨hn, hodd⟩
  have hmap := Subgroup.map_mono (f := A.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hXA] at hmap

theorem exists_mem_normalizer_not_mem [Finite G] {ell : ℕ} [Fact ell.Prime] {Q U : Subgroup G}
    (hQ : IsPGroup ell Q) (hUQ : U ≤ Q) (hQU : ¬ Q ≤ U) :
    ∃ x ∈ Q, x ∈ Subgroup.normalizer (U : Set G) ∧ x ∉ U := by
  have hlt : U.subgroupOf Q < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hQU (Subgroup.subgroupOf_eq_top.mp h)
  have h := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition hQ hlt
  obtain ⟨x, hxN, hxU⟩ := IsConcreteLE.exists_of_lt h
  have hcomap : (Subgroup.normalizer (U : Set G)).comap Q.subtype =
      Subgroup.normalizer (U.subgroupOf Q : Set Q) :=
    Subgroup.comap_normalizer_eq_of_le_range (hUQ.trans_eq Q.range_subtype.symm)
  rw [← hcomap] at hxN
  exact ⟨x, x.2, hxN, hxU⟩

theorem centralizer_map_subtype_subgroupOf (C : Subgroup G) (A : Subgroup C) :
    (Subgroup.centralizer ((A.map C.subtype : Subgroup G) : Set G)).subgroupOf C =
      Subgroup.centralizer (A : Set C) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    exact Subtype.ext (h a ⟨a, ha, rfl⟩)
  · rintro h _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (h a ha)

theorem mem_normalizer_zpowers_of_inv {t y : G} (h : t * y * t⁻¹ = y⁻¹) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (t * y * t⁻¹) = _
  rw [h, Subgroup.zpowers_inv]

theorem false_of_localized_fixed_subgroup [Finite G] {ell : ℕ} (hell : ell.Prime)
    (hellodd : Odd ell) {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    {t s : G} (ht : orderOf t = 2) (V : Subgroup G) [IsKleinFour V] (htV : t ∈ V)
    (ht1 : t ≠ 1) (hsV : s ∈ V)
    (hCV : ∀ x : G, x ∈ Subgroup.centralizer ({t} : Set G) →
      x ∈ Subgroup.centralizer ({s} : Set G) → x ∈ Subgroup.centralizer (V : Set G))
    {D PD Q F : Subgroup G} (hDC : D ≤ Subgroup.centralizer (V : Set G))
    (hoddD : ∀ x ∈ Subgroup.centralizer (V : Set G), Odd (orderOf x) → x ∈ D)
    (hPD : IsSylowIn ell PD D) (hQp : IsPGroup ell Q) (hPDQ : PD ≤ Q)
    (hVQ : V ≤ Subgroup.normalizer (Q : Set G))
    (hQt : Q ≤ Subgroup.centralizer ({t} : Set G)) (hQD : Q ⊓ D = PD) (hQPD : ¬ Q ≤ PD)
    (hFPD : F ≤ PD) (hFt : F ≤ Subgroup.centralizer ({t} : Set G))
    {g h : G} (hgH : g ∈ Subgroup.normalizer (PD : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hg : ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v)
    (hhH : h ∈ Subgroup.normalizer (PD : Set G)) (hh : h * s * h⁻¹ = t)
    (hfac : ∀ x : Subgroup.normalizer (F : Set G),
      ∃ a ∈ CFSG.pPrimeCore 2 (Subgroup.normalizer (F : Set G)),
        ∃ c ∈ Subgroup.centralizer ({t} : Set G), (a : G) * c = (x : G))
    (hloc : ∀ W : Subgroup G, W ≤ Subgroup.normalizer (F : Set G) → IsPGroup ell W →
      t ∈ Subgroup.normalizer (W : Set G) → W ≤ Subgroup.centralizer ({t} : Set G)) :
    False := by
  have : Fact ell.Prime := ⟨hell⟩
  let H := Subgroup.normalizer (PD : Set G)
  let A := Subgroup.centralizer (PD : Set G)
  let K := Subgroup.normalizer (F : Set G)
  let R := (CFSG.pPrimeCore 2 H).map H.subtype
  obtain ⟨x, hxQ, hxN, hxPD⟩ := exists_mem_normalizer_not_mem hQp hPDQ hQPD
  have hAH : A ≤ H := Subgroup.centralizer_le_normalizer _
  have hVA : V ≤ A :=
    (Subgroup.le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le hPD.1)
  have hVH : V ≤ H := hVA.trans hAH
  have htA : t ∈ A := hVA htV
  have hAK : A ≤ K :=
    (Subgroup.centralizer_le hFPD).trans (Subgroup.centralizer_le_normalizer _)
  have htK : t ∈ K := hAK htA
  have hfacK : ∀ y ∈ K, ∃ a ∈ (CFSG.pPrimeCore 2 K).map K.subtype,
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), a * c = y := by
    intro y hy
    obtain ⟨a, ha, c, hc, hac⟩ := hfac ⟨y, hy⟩
    exact ⟨a, ⟨a, ha, rfl⟩, c, hc, hac⟩
  have hcommA : ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ (CFSG.pPrimeCore 2 A).map A.subtype := by
    intro a ha
    have hR : a * t * a⁻¹ * t⁻¹ ∈ (CFSG.pPrimeCore 2 K).map K.subtype :=
      CFSG.Semidihedral.LocalPrimeFailure.commutator_mem_of_factor htK
        (le_normalizer_map_pPrimeCore K) hfacK a (hAK ha)
    have hA : a * t * a⁻¹ * t⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha)) (A.inv_mem htA)
    exact inf_map_pPrimeCore_le hAK ⟨hA, hR⟩
  have htc := mk_mem_center_of_commutator_mem (hVA htV) hcommA
  have hcyc :=
    (CFSG.Semidihedral.Local.four_group_cycling_normal_subgroup_controls_invariant_odd_subgroups
      n hn S f H A V hAH inferInstance hVA t htV ht1 htc g hgH hgV hg).2.2.2.2.2.2.2
  let P₁ := Q ⊓ H
  have hP₁p : IsPGroup ell P₁ := hQp.to_le inf_le_left
  have hP₁odd : Odd (Nat.card P₁) := odd_card_of_pgroup hell hellodd P₁ hP₁p
  have hVP₁ : V ≤ Subgroup.normalizer (P₁ : Set G) :=
    (le_inf hVQ (hVH.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hP₁R : P₁ ≤ R := hcyc P₁ inf_le_right hP₁odd hVP₁
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := le_normalizer_map_pPrimeCore H
  have hRcop : Nat.Coprime 2 (Nat.card R) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨W, hW, hP₁W, hVW⟩ := normalized_sylow_containing 2 ell Nat.prime_two hell V R P₁
    hV2 (hVH.trans hHR) hRcop hP₁R hP₁p hVP₁
  have hWp : IsPGroup ell W := hW.2.1
  have htW : t ∈ Subgroup.normalizer (W : Set G) := hVW htV
  have hsWn : s ∈ Subgroup.normalizer (W : Set G) := hVW hsV
  have hxW : x ∈ W := hP₁W ⟨hxQ, hxN⟩
  have hsW : ¬ W ≤ Subgroup.centralizer ({s} : Set G) := by
    intro hWs
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := hCV x (hQt hxQ) (hWs hxW)
    have hxodd : Odd (orderOf x) :=
      (odd_card_of_pgroup hell hellodd Q hQp).of_dvd_nat (Subgroup.orderOf_dvd_natCard Q hxQ)
    have hxD := hoddD x hxV hxodd
    exact hxPD (hQD ▸ ⟨hxQ, hxD⟩)
  have htWC : ¬ W ≤ Subgroup.centralizer ({t} : Set G) := by
    intro hWt
    obtain ⟨Ws, hWs⟩ := (isSylowIn_iff_exists_sylow ell W R).mp hW
    have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp hRcop
    have htR : t ∈ Subgroup.normalizer (R : Set G) := hHR (hVH htV)
    have hhR : h ∈ Subgroup.normalizer (R : Set G) := hHR hhH
    let Wh := W.map (MulAut.conj h).toMonoidHom
    have hWhR : Wh ≤ R := by
      rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hhR w).mp (hW.1 hw)
    have htWh : t ∈ Subgroup.normalizer (Wh : Set G) := by
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hsWn
      rw [Subgroup.map_equiv_normalizer_eq] at h1
      change h * s * h⁻¹ ∈ _ at h1
      rwa [hh] at h1
    have hWhC := centralized_invariant_pgroups_of_centralized_sylow hell t ht R hRodd htR Ws
      (by rw [hWs]; exact htW) (by rw [hWs]; exact hWt) Wh hWhR (hWp.map _) htWh
    apply hsW
    intro w hw
    have hmem' : h * w * h⁻¹ * t = t * (h * w * h⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (hWhC (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hw))
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hh] at hmem'
    have h2 : h * (w * s) * h⁻¹ = h * (s * w) * h⁻¹ := by
      calc h * (w * s) * h⁻¹ = h * w * h⁻¹ * (h * s * h⁻¹) := by group
        _ = h * s * h⁻¹ * (h * w * h⁻¹) := hmem'
        _ = h * (s * w) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨y, hyW, -, hyinv, hycomm, hyC⟩ :=
    odd_pgroup_inverted_centralizing_witness hell hellodd t ht W hWp htW htWC
  have hFW : F ≤ W := fun z hz =>
    hP₁W ⟨hPDQ (hFPD hz), Subgroup.le_normalizer (hFPD hz)⟩
  have hyK : y ∈ K := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hycomm z ⟨hFW hz, hFt hz⟩).eq.symm
  have hlocy := hloc (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyK)
    (hWp.to_le (Subgroup.zpowers_le.mpr hyW)) (mem_normalizer_zpowers_of_inv hyinv)
  exact hyC (hlocy (Subgroup.mem_zpowers y))

end CFSG.Semidihedral.StationaryLayerCover
