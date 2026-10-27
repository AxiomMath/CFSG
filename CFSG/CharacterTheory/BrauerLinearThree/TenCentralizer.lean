module

public import CFSG.CharacterTheory.BrauerLinearThree.TenFourGroup
public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusSubgroups

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.Semidihedral.Principal
open CFSG.Semidihedral (r s)

theorem centralizer_eq_of_le_torus
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ)
    (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ → Subgroup.centralizer (U : Set G) = K := by
  intro s₀ V D W K U hUW hU1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hW1, hWcyc, hWodd, -, ⟨hsup, hdisj, hcomm⟩, hcentW, hCH, -,
      ⟨d, hd, hd4, hd2, hds, hdW, -, -, -, -⟩, hMH, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hW1 : W ≠ ⊥ := hW1
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have hcomm : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := hcomm
  have hcentW : ∀ w ∈ W, w ≠ 1 → C t ⊓ Subgroup.centralizer {w} = D := hcentW
  have hd : d ∈ C t ⊓ Subgroup.normalizer (W : Set G) := hd
  have hCH : C t ⊓ Subgroup.normalizer (W : Set G) = C t ⊓ Subgroup.normalizer (V : Set G) := hCH
  have hds : d * s₀ * d⁻¹ = t * s₀ := hds
  have hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹ := hdW
  obtain ⟨hzt, ht2, -, -, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have hWD : W ≤ D := hsup ▸ le_sup_right
  have hDC : D ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  obtain ⟨w₁, hw₁, hw₁1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra! hall
    exact hW1 ((Subgroup.eq_bot_iff_forall _).mpr hall)
  have hCW : C t ⊓ Subgroup.centralizer (W : Set G) = D := by
    apply le_antisymm
    · rw [← hcentW w₁ hw₁ hw₁1]
      exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw₁))
    · exact le_inf hDC hDK
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'
  have hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t := by
    intro x hx hx4
    have hy : orderOf (fS.symm ⟨x, hx⟩) = 4 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hx4
    have h := congrArg (fun w => ((fS w : S) : G))
      (semidihedral_order_four_square n hn _ hy)
    simpa only [map_pow, Subgroup.coe_pow, MulEquiv.apply_symm_apply, hzt] using h
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : V ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have hsurj : Function.Surjective V.normalizerMonoidHom := MonoidHom.range_eq_top.mp
    ((CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS hV).1
  have hdC : d ∈ C t := (Subgroup.mem_inf.mp hd).1
  have hdM : d ∈ Subgroup.normalizer (V : Set G) := (Subgroup.mem_inf.mp (hCH ▸ hd)).2
  obtain ⟨-, -, -, -, -, -, htrans⟩ := cyclic_torus_normalizer_sylow S V rfl hSC hS4 hV
    hs2 hst W hWcyc hWodd hW1 hsup hdisj hCW hsurj hdC hdM hd4 hd2 hds hdW
  obtain ⟨-, -, -, -, -, -, hU⟩ :=
    perfect_trivial_core_every_torus_subgroup_has_inversion_normalizer_and_central_cyclic_odd_core
      n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  set A := Subgroup.centralizer (U : Set G) with hAdef
  obtain ⟨⟨P, hP⟩, -, hAt, -, -, -, -, -, hRW, -, -, -, hAeq, -, -, -⟩ := hU U hUW hU1
  have hP : (P : Subgroup A).map A.subtype = V := hP
  have hAt : A ⊓ Subgroup.centralizer ({t} : Set G) = D := hAt
  have hRW : (CFSG.pPrimeCore 2 A).map A.subtype ≤ W := hRW
  have hKA : K ≤ A := Subgroup.centralizer_le hUW
  have hWA : W ≤ A := hWD.trans (hDK.trans hKA)
  have hVA : V ≤ A := hVD.trans (hDK.trans hKA)
  have htA : t ∈ A := hVA htV
  have hPV : (P : Subgroup A) = V.subgroupOf A := by
    rw [← hP, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have hV' : IsKleinFour (V.subgroupOf A) := by
    let e := Subgroup.subgroupOfEquivOfLe hVA
    exact ⟨by rw [Nat.card_congr e.toEquiv, hV.card_four],
      by rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two]⟩
  have htV' : (⟨t, htA⟩ : A) ∈ V.subgroupOf A := htV
  have ht' : orderOf (⟨t, htA⟩ : A) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  have hC' : Subgroup.centralizer ({(⟨t, htA⟩ : A)} : Set A) =
      V.subgroupOf A ⊔ W.subgroupOf A := by
    rw [← Subgroup.subgroupOf_sup hVA hWA, hsup]
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, ← hAt]
    constructor
    · intro hx
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2)
  have hVW' : ∀ v ∈ V.subgroupOf A, ∀ w ∈ W.subgroupOf A, v * w = w * v := fun v hv w hw =>
    Subtype.ext (hcomm v hv w hw)
  have hWab' : ∀ a ∈ W.subgroupOf A, ∀ b ∈ W.subgroupOf A, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hWcomm a ha b hb)
  have hWodd' : Odd (Nat.card (W.subgroupOf A)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWA).toEquiv]
    exact hWodd
  have htrans' : ∀ v ∈ V.subgroupOf A, v ≠ 1 →
      ∃ a : A, a * ⟨t, htA⟩ * a⁻¹ = v := by
    intro v hv hv1
    obtain ⟨k, hk, hkt⟩ := htrans v hv (fun h => hv1 (Subtype.ext h))
    exact ⟨⟨k, hKA hk⟩, Subtype.ext hkt⟩
  have hle := TenFourGroup.le_pPrimeCore_of_kleinFour_sylow (V.subgroupOf A) (W.subgroupOf A) P
    hPV hV' ⟨t, htA⟩ htV' ht' hC' hVW' hWab' hWodd' htrans'
  have hWR : W ≤ (CFSG.pPrimeCore 2 A).map A.subtype := fun w hw =>
    ⟨⟨w, hWA hw⟩, hle hw, rfl⟩
  have hReq : (CFSG.pPrimeCore 2 A).map A.subtype = W := le_antisymm hRW hWR
  have hAeq' : A = Subgroup.centralizer
      (((CFSG.pPrimeCore 2 A).map A.subtype : Subgroup G) : Set G) := hAeq
  change A = Subgroup.centralizer (W : Set G)
  rw [hAeq', hReq]

theorem conj_le_of_centralizer_eq {G : Type} [Group G] [Finite G] {W K : Subgroup G}
    (hOK : (CFSG.pPrimeCore 2 K).map K.subtype = W)
    (hCK : ∀ x ∈ W, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = K) {g w : G} (hw : w ∈ W)
    (hw1 : w ≠ 1) (hgw : g * w * g⁻¹ ∈ W) {x : G} (hx : x ∈ W) : g * x * g⁻¹ ∈ W := by
  have hgw1 : g * w * g⁻¹ ≠ 1 := fun h => hw1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this)
  have hWK : W ≤ K := hOK ▸ Subgroup.map_subtype_le _
  have hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro k hk
    rw [← hCK _ hgw hgw1, Subgroup.mem_centralizer_singleton_iff]
    rw [← hCK w hw hw1, Subgroup.mem_centralizer_singleton_iff] at hk
    calc g * k * g⁻¹ * (g * w * g⁻¹) = g * (k * w) * g⁻¹ := by group
      _ = g * (w * k) * g⁻¹ := by rw [hk]
      _ = g * w * g⁻¹ * (g * k * g⁻¹) := by group
  have hgK' : ∀ k ∈ K, g⁻¹ * k * g ∈ K := by
    intro k hk
    rw [← hCK w hw hw1, Subgroup.mem_centralizer_singleton_iff]
    rw [← hCK _ hgw hgw1, Subgroup.mem_centralizer_singleton_iff] at hk
    calc g⁻¹ * k * g * w = g⁻¹ * (k * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * k) * g := by rw [hk]
      _ = w * (g⁻¹ * k * g) := by group
  set Wg : Subgroup G := W.map (MulAut.conj g).toMonoidHom with hWg
  have hWgK : Wg ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hgK y (hWK hy)
  have hWn : ∀ k ∈ K, ∀ y ∈ W, k * y * k⁻¹ ∈ W := by
    intro k hk y hy
    rw [← hOK] at hy ⊢
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨k, hk⟩ * z * ⟨k, hk⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem z hz _, rfl⟩
  have hWgn : (Wg.subgroupOf K).Normal := by
    constructor
    intro y hy k
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨g⁻¹ * k * g * z * (g⁻¹ * k * g)⁻¹, hWn _ (hgK' k k.2) z hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at hzy ⊢
    rw [← hzy]
    group
  have hWgodd : Odd (Nat.card (Wg.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWgK).toEquiv, hWg,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have : Odd (Nat.card (CFSG.pPrimeCore 2 K)) :=
      Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    rw [← hOK, Subgroup.card_map_of_injective K.subtype_injective]
    exact this
  have hle : Wg.subgroupOf K ≤ CFSG.pPrimeCore 2 K :=
    le_sSup ⟨hWgn, Nat.coprime_two_left.mpr hWgodd⟩
  have hmem : g * x * g⁻¹ ∈ Wg := ⟨x, hx, rfl⟩
  rw [← hOK]
  exact ⟨⟨_, hWgK hmem⟩, hle hmem, rfl⟩

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {W K : Subgroup G}
    (hOK : (CFSG.pPrimeCore 2 K).map K.subtype = W)
    (hCK : ∀ x ∈ W, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = K) {g w : G} (hw : w ∈ W)
    (hw1 : w ≠ 1) (hgw : g * w * g⁻¹ ∈ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_le_of_centralizer_eq hOK hCK hw hw1 hgw hx, fun hx => ?_⟩
  have hgw1 : g * w * g⁻¹ ≠ 1 := fun h => hw1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this)
  have hback : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ ∈ W := by
    rw [inv_inv, show g⁻¹ * (g * w * g⁻¹) * g = w by group]
    exact hw
  have h := conj_le_of_centralizer_eq hOK hCK hgw hgw1 hback hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

end CFSG.BrauerLinearThree
