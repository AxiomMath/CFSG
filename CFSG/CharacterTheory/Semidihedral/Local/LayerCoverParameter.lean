module

public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Semidihedral.Local

theorem statedClassicalModel_PSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem not_isCyclic_sylow_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) {p : ℕ} [Fact p.Prime] (h : ∀ U : Sylow p Y, ¬ IsCyclic U) (U : Sylow p X) :
    ¬ IsCyclic U := by
  intro hU
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have hcard : Nat.card ((U : Subgroup X).map e.toMonoidHom) =
      p ^ (Nat.card Y).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  have hS : (Sylow.ofCard _ hcard : Subgroup Y) = (U : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_ofCard _ _
  apply h (Sylow.ofCard _ hcard)
  exact isCyclic_of_surjective (((U : Subgroup X).equivMapOfInjective _ e.injective).trans
    (MulEquiv.subgroupCongr hS.symm)).toMonoidHom (MulEquiv.surjective _)

theorem centralizer_layer_cover_preserves_actual_local_parameter {C : Type} [Group C] [Finite C]
    (t : C) (htc : t ∈ Subgroup.center C) (ht : orderOf t = 2) [(Subgroup.zpowers t).Normal]
    [IsSimpleGroup (CFSG.generalizedFitting (C ⧸ (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t)))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (C ⧸ (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t)),
      a * b ≠ b * a)
    (heven : Even (Nat.card
      (CFSG.generalizedFitting (C ⧸ (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t)))))
    (hcentral : Subgroup.centralizer
      ((CFSG.generalizedFitting (C ⧸ (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t))) :
        Set (C ⧸ (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t))) = ⊥)
    (B : Subgroup C) (htB : t ∈ B)
    (hLB : CFSG.generalizedFitting (C ⧸ (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t)) ≤
      B.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 C ⊔ Subgroup.zpowers t))) :
    let N := CFSG.pPrimeCore 2 C
    let Γ := C ⧸ (N ⊔ Subgroup.zpowers t)
    let π : C →* Γ := QuotientGroup.mk' (N ⊔ Subgroup.zpowers t)
    let L := CFSG.generalizedFitting Γ
    let R := CFSG.pPrimeCore 2 B
    let Δ := B ⧸ (R ⊔ (Subgroup.zpowers t).subgroupOf B)
    let J := CFSG.generalizedFitting Δ
    R.map B.subtype = B ⊓ N ∧
      ∃ ι : Δ →* Γ, Function.Injective ι ∧
        (∀ b : B, ι (QuotientGroup.mk' (R ⊔ (Subgroup.zpowers t).subgroupOf B) b) = π b) ∧
        ι.range = B.map π ∧ J.map ι = L ∧ Subgroup.centralizer (J : Set Δ) = ⊥ ∧
        (∃ e : J ≃* L, ∀ x : J, (e x : Γ) = ι x) ∧
        (∀ p f : ℕ, p.Prime → Odd p → 1 ≤ f →
          CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p f →
          CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 2 p f) ∧
        ((∀ U : Sylow 2 L, ¬ IsCyclic U) → ∀ U : Sylow 2 J, ¬ IsCyclic U) := by
  intro N Γ π L R Δ J
  have _hunused : t ∈ Subgroup.center C := htc
  have hLn : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := Γ)).2
  have hcopN : Nat.Coprime 2 (Nat.card N) := CFSG.pPrimeCore_coprime_card (p := 2) (G := C)
  have hcopR : Nat.Coprime 2 (Nat.card R) := CFSG.pPrimeCore_coprime_card (p := 2) (G := B)
  have hNB : N.subgroupOf B ≤ R := by
    refine le_sSup ⟨inferInstance, hcopN.coprime_dvd_right ?_⟩
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hU : R.map (π.comp B.subtype) = ⊥ := by
    have hUL : ∀ l ∈ L, ∀ u ∈ R.map (π.comp B.subtype),
        l * u * l⁻¹ ∈ R.map (π.comp B.subtype) := by
      intro l hl u hu
      obtain ⟨b, hb, rfl⟩ := hLB hl
      obtain ⟨r, hr, rfl⟩ := hu
      refine ⟨⟨b, hb⟩ * r * ⟨b, hb⟩⁻¹,
        (CFSG.pPrimeCore_normal (p := 2) (G := B)).conj_mem r hr ⟨b, hb⟩, ?_⟩
      simp only [map_mul, map_inv]
      rfl
    have hUodd : Odd (Nat.card (R.map (π.comp B.subtype))) :=
      Nat.coprime_two_left.mp (hcopR.coprime_dvd_right (Subgroup.card_map_dvd _ _))
    have hinf : R.map (π.comp B.subtype) ⊓ L = ⊥ := by
      have hnorm : ((R.map (π.comp B.subtype) ⊓ L).subgroupOf L).Normal := by
        constructor
        intro x hx l
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact ⟨hUL l l.2 x hx.1, L.mul_mem (L.mul_mem l.2 hx.2) (L.inv_mem l.2)⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((R.map (π.comp B.subtype) ⊓ L).subgroupOf L) with h | h
      · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
      · exfalso
        have hle : L ≤ R.map (π.comp B.subtype) :=
          (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
        have hdvd := Subgroup.card_dvd_of_le hle
        exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hUodd hdvd)) heven
    have hUC : R.map (π.comp B.subtype) ≤ Subgroup.centralizer (L : Set Γ) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : l * u * l⁻¹ * u⁻¹ ∈ R.map (π.comp B.subtype) :=
        Subgroup.mul_mem _ (hUL l hl u hu) (Subgroup.inv_mem _ hu)
      have h2 : l * u * l⁻¹ * u⁻¹ ∈ L := by
        have h3 : u * l⁻¹ * u⁻¹ ∈ L := hLn.conj_mem _ (L.inv_mem hl) u
        have h4 := L.mul_mem hl h3
        rwa [← mul_assoc, ← mul_assoc] at h4
      have h5 : l * u * l⁻¹ * u⁻¹ = 1 := by
        have h6 : l * u * l⁻¹ * u⁻¹ ∈ R.map (π.comp B.subtype) ⊓ L := ⟨h1, h2⟩
        rw [hinf] at h6
        exact h6
      calc l * u = l * u * l⁻¹ * u⁻¹ * (u * l) := by group
        _ = u * l := by rw [h5, one_mul]
    rw [hcentral] at hUC
    exact le_bot_iff.mp hUC
  have hRN : ∀ r : B, r ∈ R → (r : C) ∈ N := by
    intro r hr
    have h1 : π (r : C) = 1 := by
      have h2 : (π.comp B.subtype) r ∈ R.map (π.comp B.subtype) := Subgroup.mem_map_of_mem _ hr
      rw [hU] at h2
      exact h2
    have h2 : (r : C) ∈ N ⊔ Subgroup.zpowers t := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_right.mp h2
    have hz2 : z ^ 2 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht,
        pow_orderOf_eq_one, one_zpow]
    have hq2 : (QuotientGroup.mk' N (r : C)) ^ 2 = 1 := by
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [← hnz, map_mul, hn1, one_mul, ← map_pow, hz2, map_one]
    have hodd : Odd (orderOf r) :=
      Nat.coprime_two_left.mp (hcopR.coprime_dvd_right (Subgroup.orderOf_dvd_natCard R hr))
    have hqm : (QuotientGroup.mk' N (r : C)) ^ orderOf r = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
    have hord : orderOf (QuotientGroup.mk' N (r : C)) = 1 := by
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq2) (orderOf_dvd_of_pow_eq_one hqm)
      rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), Nat.dvd_one] at h3
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hord)
  have hR : R.map B.subtype = B ⊓ N := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact ⟨r.2, hRN r hr⟩
    · rintro x ⟨hxB, hxN⟩
      exact ⟨⟨x, hxB⟩, hNB hxN, rfl⟩
  have hker : (π.comp B.subtype).ker = R ⊔ (Subgroup.zpowers t).subgroupOf B := by
    apply le_antisymm
    · intro x hx
      have h2 : (x : C) ∈ N ⊔ Subgroup.zpowers t := (QuotientGroup.eq_one_iff _).mp hx
      obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_right.mp h2
      have hzB : z ∈ B := Subgroup.zpowers_le.mpr htB hz
      have hnB : n ∈ B := by
        have h3 := B.mul_mem x.2 (B.inv_mem hzB)
        rwa [← hnz, mul_inv_cancel_right] at h3
      have hx' : x = ⟨n, hnB⟩ * ⟨z, hzB⟩ := Subtype.ext hnz.symm
      rw [hx']
      exact Subgroup.mul_mem_sup (hNB hn) hz
    · refine sup_le (fun r hr => ?_) (fun z hz => ?_)
      · exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (hRN r hr))
      · exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right hz)
  let ι : Δ →* Γ :=
    QuotientGroup.lift (R ⊔ (Subgroup.zpowers t).subgroupOf B) (π.comp B.subtype) hker.ge
  have hι : ∀ b : B, ι (QuotientGroup.mk' (R ⊔ (Subgroup.zpowers t).subgroupOf B) b) = π b :=
    fun _ => rfl
  have hinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  have hrange : ι.range = B.map π := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨QuotientGroup.mk' _ ⟨c, hc⟩, rfl⟩
  have hLrange : L ≤ ι.range := by
    rw [hrange]
    exact hLB
  have hLΔn : (L.comap ι).Normal := hLn.comap ι
  let e0 : L.comap ι ≃* L := ((L.comap ι).equivMapOfInjective ι hinj).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLrange))
  have : IsSimpleGroup (L.comap ι) := e0.isSimpleGroup
  have hnc : ∃ a b : L.comap ι, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e0.symm a, e0.symm b, fun h => hab ?_⟩
    have h1 := congrArg e0 h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  have hCΔ : Subgroup.centralizer ((L.comap ι : Subgroup Δ) : Set Δ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : ι x ∈ Subgroup.centralizer (L : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨y, rfl⟩ := hLrange hl
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx y hl]
    rw [hcentral, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact hinj (h1.trans (map_one ι).symm)
  have hJ : J = L.comap ι :=
    CFSG.Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot
      (L.comap ι) hnc hCΔ
  have hJL : J.map ι = L := by
    rw [hJ]
    exact Subgroup.map_comap_eq_self hLrange
  let e : J ≃* L := (MulEquiv.subgroupCongr hJ).trans e0
  refine ⟨hR, ι, hinj, hι, hrange, hJL, by rw [hJ]; exact hCΔ, ⟨e, fun _ => rfl⟩, ?_, ?_⟩
  · intro p f _ _ _ hmodel
    exact statedClassicalModel_PSL_of_mulEquiv e hmodel
  · intro hncL
    exact not_isCyclic_sylow_of_mulEquiv e hncL

end CFSG.Semidihedral.Local
