module

import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31PairAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonTriv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

section Bar

variable {G : Type} [Group G] [Finite G] {z : G}

theorem l31c_eq_one_of_toBar {R : Subgroup G} (hR : IsPGroup 2 ↥R) {r : G} (hr : r ∈ R)
    (hrC : r ∈ Cen z) (h : toBar z ⟨r, hrC⟩ = 1) : r = 1 := by
  have hmem : (⟨r, hrC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 h
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h1 : orderOf (⟨⟨r, hrC⟩, hmem⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
      Nat.card (pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
  have e1 : orderOf (⟨⟨r, hrC⟩, hmem⟩ : ↥(pPrimeCore 2 ↥(Cen z))) = orderOf r := by
    rw [← Subgroup.orderOf_coe (⟨⟨r, hrC⟩, hmem⟩ : ↥(pPrimeCore 2 ↥(Cen z))),
      ← Subgroup.orderOf_coe (⟨r, hrC⟩ : ↥(Cen z))]
  have e2 : orderOf (⟨r, hr⟩ : ↥R) = orderOf r := by
    rw [← Subgroup.orderOf_coe (⟨r, hr⟩ : ↥R)]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨r, hr⟩
  have hodd' : Odd (orderOf r) := by
    rw [← e1]
    exact Odd.of_dvd_nat hodd h1
  rw [← e2, hk] at hodd'
  have hk0 : k = 0 := by
    by_contra hne
    have : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.mpr hodd') this
  rw [hk0, pow_zero] at hk
  have : orderOf r = 1 := by rw [← e2, hk]
  exact orderOf_eq_one_iff.mp this

theorem l31c_mem_zpowers_of_toBar (hz2 : z * z = 1) {R : Subgroup G} (hR : IsPGroup 2 ↥R)
    (hzR : z ∈ R) {n : G} (hn : n ∈ R) (hnC : n ∈ Cen z)
    (h : toBar z ⟨n, hnC⟩ ∈ zpowers (toBar z ⟨z, z_mem_cen z⟩)) : n ∈ zpowers z := by
  have hzz : (toBar z ⟨z, z_mem_cen z⟩) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← map_mul]
    have : (⟨z, z_mem_cen z⟩ * ⟨z, z_mem_cen z⟩ : ↥(Cen z)) = 1 := Subtype.ext hz2
    rw [this, map_one]
  obtain ⟨m, hm0⟩ := h
  have hm : (toBar z ⟨z, z_mem_cen z⟩) ^ m = toBar z ⟨n, hnC⟩ := hm0
  rw [zpow_eq_zpow_emod m hzz] at hm
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · rw [h0, zpow_zero] at hm
    have : n = 1 := l31c_eq_one_of_toBar hR hn hnC hm.symm
    rw [this]
    exact one_mem _
  · rw [h1, zpow_one] at hm
    have hc : z⁻¹ * n ∈ Cen z := (Cen z).mul_mem ((Cen z).inv_mem (z_mem_cen z)) hnC
    have hcR : z⁻¹ * n ∈ R := R.mul_mem (R.inv_mem hzR) hn
    have h1' : toBar z ⟨z⁻¹ * n, hc⟩ = 1 := by
      have e : (⟨z⁻¹ * n, hc⟩ : ↥(Cen z)) = ⟨z, z_mem_cen z⟩⁻¹ * ⟨n, hnC⟩ := rfl
      rw [e, map_mul, map_inv, hm, inv_mul_cancel]
    have := l31c_eq_one_of_toBar hR hcR hc h1'
    have hnz : n = z := by
      have h2 : n = z * (z⁻¹ * n) := by group
      rw [h2, this, mul_one]
    rw [hnz]
    exact mem_zpowers z

omit [Finite G] in
theorem l31c_barOf_perfect {P : Subgroup G} (hPC : P ≤ Cen z) (hP : Group.IsPerfect ↥P) :
    Group.IsPerfect ↥(barOf z P) := by
  have : Group.IsPerfect ↥(P.subgroupOf (Cen z)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPC).symm.surjective
  exact Group.IsPerfect.map (toBar z)

theorem l31c_barOf_not_solvable {P : Subgroup G} (hPC : P ≤ Cen z) (hP : Group.IsPerfect ↥P)
    (hns : ¬ Group.IsSolvable ↥P) : ¬ Group.IsSolvable ↥(barOf z P) := by
  have hperf := l31c_barOf_perfect hPC hP
  intro hsol
  apply hns
  have hbot : barOf z P = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(barOf z P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hsol
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let φ : ↥P →* ↥(pPrimeCore 2 ↥(Cen z)) :=
    { toFun := fun p => ⟨⟨p, hPC p.2⟩, by
        have : toBar z ⟨p, hPC p.2⟩ ∈ barOf z P := ⟨⟨p, hPC p.2⟩, p.2, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff _).1 this⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    exact congrArg (fun t : ↥(pPrimeCore 2 ↥(Cen z)) => ((t : ↥(Cen z)) : G)) h
  have hdvd : Nat.card ↥P ∣ Nat.card (pPrimeCore 2 ↥(Cen z)) :=
    Subgroup.card_dvd_of_injective φ hφ
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Odd.of_dvd_nat hodd hdvd)

end Bar

section Classical

variable {G : Type} [Group G] {z : G} {S : Subgroup G}

theorem l31c_all_comps {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : PairShape z q₁ q₂ L₁ L₂) :
    ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁ ∨ K = L₂ := by
  intro K hK
  have : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hp.comps]
    exact hK
  simpa using this

@[expose] def L31Reach (L₁ L₂ : Subgroup (CentralizerBar z)) (q : ℕ)
    (c : CentralizerBar z) : Prop :=
  c ∈ L₁ ⊔ L₂ ∨ ∃ T : Subgroup (CentralizerBar z), c ∈ T ∧ InducedPGL2 L₁ T q ∧ InducedPGL2 L₂ T q

theorem l31c_classical_data [Finite G] {k : Kind} (hctx : Stage2Ctx G z k S)
    (hk : IsClassicalKind k) :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), PairShape z q q L₁ L₂ ∧
      ∀ u ∈ S, ∀ hu : u ∈ Cen z, toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) →
        L31Reach L₁ L₂ q (toBar z ⟨u, hu⟩) := by
  rcases hk with rfl | ⟨ε, rfl⟩
  · cases hctx.data with
    | psp4 h =>
      obtain ⟨q, L₁, L₂, hq⟩ := h
      refine ⟨q, L₁, L₂, PairShape.of_pair hq.pair, fun u huS hu hn => Or.inl ?_⟩
      have hRC := mem_RC_of_nonswap hq huS hu hn
      rw [hq.pair.prod.1]
      exact toBar_mem_LBar hRC.2
  · cases hctx.data with
    | l4 _ h =>
      obtain ⟨q, L₁, L₂, hq⟩ := h
      have hpair := PairShape.of_pair hq.pair
      refine ⟨q, L₁, L₂, hpair, fun u huS hu hn₁ => Or.inr ⟨barOf z (S1 S z), ?_, hq.pgl.1,
        hq.pgl.2⟩⟩
      have hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) :=
        L29Pair.mem_normalizer_of_mem_normalizer hpair.ne hpair.isComponent₂
          (l31c_all_comps hpair) hn₁
      have hS1 := mem_S1_of_normalizes hpair huS hu hn₁ hn₂
      exact ⟨⟨u, hu⟩, Subgroup.mem_subgroupOf.mpr hS1, rfl⟩

theorem l31c_swaps_of_swapsComps {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : PairShape z q₁ q₂ L₁ L₂) {u : G} (h : SwapsComps z u) : Swaps z u L₁ L₂ := by
  obtain ⟨L₁', L₂', -, hc', hsw⟩ := h
  rw [hp.comps] at hc'
  rcases Set.pair_eq_pair_iff.mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsw
  · obtain ⟨ht, h1, h2⟩ := hsw
    exact ⟨ht, h2, h1⟩

theorem l31c_swap_conj {L₁ L₂ : Subgroup (CentralizerBar z)} {t : G} (hsw : Swaps z t L₁ L₂) :
    ∃ ht : t ∈ Cen z, (∀ a ∈ L₁, toBar z ⟨t, ht⟩ * a * (toBar z ⟨t, ht⟩)⁻¹ ∈ L₂) ∧
      (∀ b ∈ L₂, toBar z ⟨t, ht⟩ * b * (toBar z ⟨t, ht⟩)⁻¹ ∈ L₁) := by
  obtain ⟨ht, h1, h2⟩ := hsw
  refine ⟨ht, fun a ha => ?_, fun b hb => ?_⟩
  · rw [← h2] at ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have : toBar z ⟨t, ht⟩ * (MulAut.conj (toBar z ⟨t, ht⟩)⁻¹).toMonoidHom b *
        (toBar z ⟨t, ht⟩)⁻¹ = b := by
      simp
      group
    rw [this]
    exact hb
  · rw [← h1] at hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    have : toBar z ⟨t, ht⟩ * (MulAut.conj (toBar z ⟨t, ht⟩)⁻¹).toMonoidHom a *
        (toBar z ⟨t, ht⟩)⁻¹ = a := by
      simp
      group
    rw [this]
    exact ha

theorem l31c_inf_central {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : PairShape z q₁ q₂ L₁ L₂) [Finite G] (hz2 : orderOf z = 2) :
    ∀ ζ ∈ L₁ ⊓ L₂, ∀ y : CentralizerBar z, ζ * y = y * ζ := by
  intro ζ hζ y
  rw [inf_eq_zpowers_zbar hp hz2] at hζ
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
  exact Commute.zpow_left (zbar_central z y) m

theorem l31c_key [Finite G] {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : PairShape z q q L₁ L₂) (hz2 : orderOf z = 2) {P : Subgroup (CentralizerBar z)}
    (hP : P ≤ L₁ ⊔ L₂) (hPperf : Group.IsPerfect ↥P) (hPns : ¬ Group.IsSolvable ↥P)
    {t : CentralizerBar z} (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂)
    (h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁) (hPt : ∀ p ∈ P, t * p = p * t) {c : CentralizerBar z}
    (hcn : c ∈ normalizer (L₁ : Set (CentralizerBar z))) (hreach : L31Reach L₁ L₂ q c)
    (hcP : ∀ p ∈ P, c * p = p * c) : c ∈ L₁ ⊓ L₂ := by
  obtain ⟨hsup, hcomm, hI⟩ := hp.prod
  have h4 : 4 ≤ q := by have := hp.gt₁; omega
  obtain ⟨-, hZ₁c, -⟩ := Stage2.Local.sl2_model_facts hp.odd₁ h4 hp.sl₁
  obtain ⟨-, hZ₂c, -⟩ := Stage2.Local.sl2_model_facts hp.odd₂ h4 hp.sl₂
  have hZ₁ : ∀ x ∈ L₁, (∀ y ∈ L₁, x * y = y * x) → x ∈ L₂ := fun x hx hxc =>
    central_mem_of_card_inf hcomm hZ₁c hI hx (fun c hc => (hxc c hc).symm)
  have hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, x * y = y * x) → x ∈ L₁ := fun x hx hxc =>
    central_mem_of_card_inf (A := L₂) (B := L₁) (fun b hb a ha => (hcomm a ha b hb).symm) hZ₂c
      (by rwa [inf_comm]) hx (fun c hc => (hxc c hc).symm)
  obtain ⟨F₁, hF₁, hFin₁, hq₁, ⟨e₁⟩⟩ := hp.sl₁
  obtain ⟨F₂, hF₂, hFin₂, hq₂, ⟨e₂⟩⟩ := hp.sl₂
  have hq₁' : Nat.card F₁ = q := hq₁
  have hq₂' : Nat.card F₂ = q := hq₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hq₁']; exact hp.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hq₂']; exact hp.odd₂
  have hcn₂ : c ∈ normalizer (L₂ : Set (CentralizerBar z)) :=
    L29Pair.mem_normalizer_of_mem_normalizer hp.ne hp.isComponent₂ (l31c_all_comps hp) hcn
  rcases hreach with hc | ⟨T, hcT, hpgl₁, hpgl₂⟩
  · exact l31_centralizer_diag hcomm hZ₁ hZ₂ hodd₁ hodd₂ e₁ e₂ h12 h21 hP hPperf hPns hPt hc hcP
  · obtain ⟨X₁, X₂, hX₁, hX₂, hns₁, hns₂, key⟩ := l31_diag_proj hcomm h12 h21 hP hPperf hPns hPt
    obtain ⟨hc1, hc2⟩ := key c (fun a ha => (Subgroup.mem_normalizer_iff.mp hcn a).mp ha)
      (fun b hb => (Subgroup.mem_normalizer_iff.mp hcn₂ b).mp hb)
      (fun ζ hζ => (l31c_inf_central hp hz2 ζ hζ c).symm) hcP
    have c1 : c ∈ centralizer (L₁ : Set (CentralizerBar z)) :=
      l31_pgl_trivial hp.odd₁ hpgl₁ hX₁ hns₁ hcT hc1
    have c2 : c ∈ centralizer (L₂ : Set (CentralizerBar z)) :=
      l31_pgl_trivial hp.odd₂ hpgl₂ hX₂ hns₂ hcT hc2
    exact centralizer_pair_le_inf hp c (fun a ha => (Subgroup.mem_centralizer_iff.mp c1 a ha).symm)
      (fun b hb => (Subgroup.mem_centralizer_iff.mp c2 b hb).symm)

end Classical

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
