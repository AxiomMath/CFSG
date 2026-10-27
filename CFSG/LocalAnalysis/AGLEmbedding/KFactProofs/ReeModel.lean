module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.LieType.Ree.SmallReeFrattini
public import CFSG.Walter.Ree.Model.Cells

public section

namespace CFSG.AGLEmbedding.ReeModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

section Derived

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem nonempty_derivedCentralQuotient_reeGamma (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (ReeTag.G2.reeGamma K a) ≃*
      ReeTag.G2.reeGamma K a) := by
  have hcomm := (ReeTag.ree_generic_fixed_group_perfect .G2 a ha K hK).2.1
  have hD : ⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ = ReeTag.G2.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e₁ : ↥⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ ≃* ReeTag.G2.reeGamma K a :=
    MulEquiv.subgroupCongr hD
  have hZ : Subgroup.center ↥⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center (ReeTag.G2.reeGamma K a) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e₁.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [ReeTag.center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e₁.injective (hz'.trans (map_one e₁).symm))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₁)⟩

theorem nonempty_derivedCentralQuotient_equiv_reeGamma (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
        fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃* ReeTag.G2.reeGamma K a) := by
  have hH := ReeTag.reeGamma_eq_reeFixedGroup (t := .G2) (K := K) (a := a)
  show Nonempty (CFSG.Blueprint.DerivedCentralQuotient (reeFixedGroup ReeTag.G2.tag K
      ReeTag.G2.perm fun i => if i ∈ ReeTag.G2.longSet then ReeTag.G2.prime ^ a
        else ReeTag.G2.prime ^ (a + 1)) ≃* ReeTag.G2.reeGamma K a)
  rw [← hH]
  exact nonempty_derivedCentralQuotient_reeGamma ha hK

end Derived

instance instCharPGaloisFieldG2 (n : ℕ) : CharP (GaloisField 3 n) ReeTag.G2.prime :=
  inferInstanceAs (CharP (GaloisField 3 n) 3)

theorem nonempty_reeGamma_equiv (a : ℕ) (ha : 1 ≤ a)
    (hv : (TauCeti.LieTypeIndex.reeG2 a).Valid) :
    Nonempty (ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.reeG2 a, hv⟩) := by
  have hcard : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨f⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hcard
  obtain ⟨g⟩ := nonempty_derivedCentralQuotient_equiv_reeGamma
    (K := GaloisField 3 (2 * a + 1)) ha hcard
  exact ⟨g.symm.trans f⟩

theorem exists_equiv_reeGamma {L : Type} [Group L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ a : ℕ, 1 ≤ a ∧ d.1.fieldExponent = 2 * a + 1 ∧
      Nonempty (L ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) := by
  obtain ⟨-, m, hm, hdm, hfe⟩ := hd.exists_eq
  obtain ⟨x, hx⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.reeG2 m := hdm
  obtain ⟨f⟩ := nonempty_reeGamma_equiv m hm hx
  obtain ⟨e⟩ := h
  exact ⟨m, hm, hfe, ⟨e.trans f.symm⟩⟩

theorem exists_equiv_map_eq {L G : Type*} [Group L] [Finite L] [Group G] {p : ℕ} [Fact p.Prime]
    (e : L ≃* G) (U : Sylow p L) (P : Sylow p G) :
    ∃ e' : L ≃* G, (U : Subgroup L).map e'.toMonoidHom = P := by
  have : Finite G := Finite.of_equiv L e.toEquiv
  set U' := U.mapSurjective (f := (e : L →* G)) e.surjective with hU'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U' P
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h2 : ((g • U' : Sylow p G) : Subgroup G) =
      (U' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hg, hU', Sylow.coe_mapSurjective, Subgroup.map_map] at h2
  exact h2.symm

theorem isCoatom_of_stabilizer_transitive {G Ω : Type*} [Group G] [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] (ξ : Ω) (H : Subgroup G) (hH : MulAction.stabilizer G ξ = H)
    (h2 : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ h ∈ H, h • ω = ω') (hnt : ∃ ω : Ω, ω ≠ ξ) :
    IsCoatom H := by
  have hmem : ∀ g : G, g ∈ H ↔ g • ξ = ξ := fun g => by rw [← hH, MulAction.mem_stabilizer_iff]
  refine ⟨?_, fun A hHA => ?_⟩
  · intro htop
    obtain ⟨ω, hω⟩ := hnt
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ξ ω
    exact hω (by rw [← hg]; exact (hmem g).1 (htop ▸ Subgroup.mem_top g))
  · obtain ⟨x, hxA, hxH⟩ := IsConcreteLE.exists_of_lt hHA
    rw [eq_top_iff]
    intro g _
    by_cases hg : g ∈ H
    · exact hHA.le hg
    · have hx : x • ξ ≠ ξ := fun h => hxH ((hmem x).2 h)
      have hg' : g • ξ ≠ ξ := fun h => hg ((hmem g).2 h)
      obtain ⟨h, hh, hhx⟩ := h2 _ _ hx hg'
      have hmem' : (h * x)⁻¹ * g ∈ H := by
        rw [hmem, mul_smul, ← hhx, ← mul_smul h x ξ, inv_smul_smul]
      have hA : g = (h * x) * ((h * x)⁻¹ * g) := by group
      rw [hA]
      exact mul_mem (mul_mem (hHA.le hh) hxA) (hHA.le hmem')

section Std

variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]

@[expose] noncomputable def stdU : Subgroup ↥(ReeTag.G2.reeGamma K a) :=
  (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)

@[expose] noncomputable def stdB : Subgroup ↥(ReeTag.G2.reeGamma K a) :=
  (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)

variable {a K}

theorem std_facts (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∃ P : Sylow 3 ↥(ReeTag.G2.reeGamma K a), (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) =
      stdU a K) ∧
    Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) = stdB a K ∧
    IsCoatom (stdB a K) ∧
    Nat.card ↥(ReeTag.G2.reeGamma K a) =
      (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1) := by
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, hcardΓ, hP, hstab, hUn, hNU, hNUV⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have := htrans
  have hNU' : Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) = stdB a K := hNU
  refine ⟨hP, hNU', ?_, hcardΓ⟩
  refine isCoatom_of_stabilizer_transitive (QuotientGroup.mk 1) (stdB a K) hstab
    (fun ω ω' hω hω' => ?_) ⟨_, hηξ⟩
  obtain ⟨u, hu, -⟩ := hreg ω ω' hω hω'
  exact ⟨u, hNU' ▸ Subgroup.le_normalizer
    (show (u : ↥(ReeTag.G2.reeGamma K a)) ∈ stdU a K from u.2), hu⟩

end Std

section Center

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

@[expose] noncomputable def zHom (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Multiplicative K →* ↥(ReeTag.G2.reeGamma K a) where
  toFun c := ⟨smallReeCoord a K 0 0 (Multiplicative.toAdd c),
    ReeTag.reeFixedPosUnipotent_le_reeGamma
      (smallReeCoord_mem_reeFixedPosUnipotent hK 0 0 (Multiplicative.toAdd c))⟩
  map_one' := Subtype.ext smallReeCoord_zero
  map_mul' c e := Subtype.ext (by
    have h := smallReeCoord_zero_mul (a := a) (K := K) 0 (Multiplicative.toAdd c) 0
      (Multiplicative.toAdd e)
    rw [add_zero] at h
    exact h.symm)

theorem coe_zHom (hK : Nat.card K = 3 ^ (2 * a + 1)) (c : Multiplicative K) :
    ((zHom hK c : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      smallReeCoord a K 0 0 (Multiplicative.toAdd c) :=
  rfl

theorem zHom_injective (hK : Nat.card K = 3 ^ (2 * a + 1)) : Function.Injective (zHom hK) := by
  intro c e h
  have h1 : ((zHom hK c : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      ((zHom hK e : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) :=
    congrArg Subtype.val h
  rw [coe_zHom, coe_zHom] at h1
  have h2 := smallReeCoordU_injective hK (t := 0) (b := 0) (c := Multiplicative.toAdd c)
    (t' := 0) (b' := 0) (c' := Multiplicative.toAdd e) (Subtype.ext h1)
  exact Multiplicative.toAdd.injective h2.2.2

theorem zHom_range (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (zHom hK).range = stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup
      ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) := by
  have hcen := ReeTag.center_reeFixedPosUnipotent (K := K) (a := a) hK
  ext x
  simp only [MonoidHom.mem_range, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨c, rfl⟩
    have hx : (zHom hK c : ↥(ReeTag.G2.reeGamma K a)) ∈ stdU a K :=
      Subgroup.mem_subgroupOf.2 (smallReeCoord_mem_reeFixedPosUnipotent hK 0 0 _)
    refine ⟨hx, fun y hy => ?_⟩
    have hy' : (y : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hy
    have hz : (⟨(zHom hK c : ↥(ReeTag.G2.reeGamma K a)), Subgroup.mem_subgroupOf.1 hx⟩ :
        ↥(ReeTag.G2.reeFixedPosUnipotent K a)) ∈ Subgroup.center _ := by
      rw [hcen, Subgroup.mem_subgroupOf]
      exact ⟨Multiplicative.toAdd c, rfl⟩
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hz ⟨(y : ModGL ReeTag.G2.tag K), hy'⟩)
    exact Subtype.ext h
  · rintro ⟨hx, hc⟩
    have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hx
    have hz : (⟨(x : ModGL ReeTag.G2.tag K), hx'⟩ : ↥(ReeTag.G2.reeFixedPosUnipotent K a)) ∈
        Subgroup.center _ := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have hg : (⟨(g : ModGL ReeTag.G2.tag K), ReeTag.reeFixedPosUnipotent_le_reeGamma g.2⟩ :
          ↥(ReeTag.G2.reeGamma K a)) ∈ stdU a K := Subgroup.mem_subgroupOf.2 g.2
      have h := congrArg Subtype.val (hc _ hg)
      exact Subtype.ext h
    rw [hcen, Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc'⟩ := hz
    exact ⟨Multiplicative.ofAdd c, Subtype.ext hc'.symm⟩

theorem exists_normalizer_mul (hK : Nat.card K = 3 ^ (2 * a + 1)) (μ : Kˣ) :
    ∃ g ∈ Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
        Set ↥(ReeTag.G2.reeGamma K a)),
      ∀ c : Multiplicative K, g * zHom hK c * g⁻¹ =
        zHom hK (Multiplicative.ofAdd ((μ : K) * Multiplicative.toAdd c)) := by
  have hcop : (Nat.card Kˣ).Coprime (3 ^ a) := by
    rw [Nat.card_units, hK]
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have h3 : 3 ^ (2 * a + 1) = 3 * 3 ^ (2 * a) := by ring
    have h1 : 1 ≤ 3 ^ (2 * a) := Nat.one_le_pow _ _ (by norm_num)
    omega
  obtain ⟨s, hs⟩ := (powCoprime hcop).surjective μ
  rw [powCoprime_apply] at hs
  have hsT : smallReeTorusElt a K s ∈ ReeTag.G2.reeFixedTorus K a :=
    ReeTag.smallReeTorusElt_mem hK s
  have hsΓ : smallReeTorusElt a K s ∈ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedBorel_le_reeGamma (ReeTag.reeFixedTorus_le_reeFixedBorel hsT)
  have hNU := (std_facts hK).2.1
  refine ⟨⟨smallReeTorusElt a K s, hsΓ⟩, ?_, fun c => ?_⟩
  · rw [hNU]
    exact Subgroup.mem_subgroupOf.2 (ReeTag.reeFixedTorus_le_reeFixedBorel hsT)
  · apply Subtype.ext
    have h := ReeTag.smallReeTorusElt_conj_smallReeCoord hK s 0 0 (Multiplicative.toAdd c)
    rw [mul_zero, mul_zero] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_zHom]
    refine h.trans ?_
    rw [coe_zHom, toAdd_ofAdd, ← hs]
    simp

end Center

section Transport

variable {L G : Type*} [Group L] [Group G]

theorem mem_centralizer_image_iff (e : L ≃* G) (S : Set L) (x : L) :
    e x ∈ Subgroup.centralizer (e '' S) ↔ x ∈ Subgroup.centralizer S := by
  simp only [Subgroup.mem_centralizer_iff, Set.forall_mem_image, ← map_mul, e.injective.eq_iff]

theorem mem_centralizer_map_iff (e : L ≃* G) (S : Subgroup L) (x : L) :
    e x ∈ Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup G) : Set G) ↔
      x ∈ Subgroup.centralizer (S : Set L) := by
  rw [Subgroup.coe_map]
  exact mem_centralizer_image_iff e _ x

theorem mem_map_iff (e : L ≃* G) (S : Subgroup L) (x : L) :
    e x ∈ S.map e.toMonoidHom ↔ x ∈ S := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem isElemAbelian_map_iff {p : ℕ} (e : L ≃* G) (E : Subgroup L) :
    CFSG.Open.IsElemAbelian p (E.map e.toMonoidHom) ↔ CFSG.Open.IsElemAbelian p E := by
  unfold CFSG.Open.IsElemAbelian
  rw [← Subgroup.le_centralizer_iff_isMulCommutative,
    ← Subgroup.le_centralizer_iff_isMulCommutative]
  refine and_congr ?_ ?_
  · constructor
    · intro h x hx
      exact (mem_centralizer_map_iff e E x).1 (h ((mem_map_iff e E x).2 hx))
    · rintro h _ ⟨x, hx, rfl⟩
      exact (mem_centralizer_map_iff e E x).2 (h hx)
  · constructor
    · intro h x hx
      have := h (e x) ((mem_map_iff e E x).2 hx)
      rw [← map_pow, ← map_one e] at this
      exact e.injective this
    · rintro h _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, h x hx, map_one]

theorem mem_range_comp_symm {A : Type*} [Group A] (e : L ≃* G) (f : A →* G) (x : L) :
    x ∈ ((e.symm : G →* L).comp f).range ↔ e x ∈ f.range := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by simp⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by simp [hc]⟩

end Transport

theorem involution_conj_aux {G : Type*} [Group G] (U H : Subgroup G) (J : G)
    (hHn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hUH : ∀ x ∈ U, x ∈ H → x = 1)
    (hOdd : Odd (Nat.card U)) (hJ : J * J = 1)
    (hH2 : ∀ h ∈ H, h * h = 1 → h = 1 ∨ h = J)
    (t u' h : G) (hu' : u' ∈ U) (hh : h ∈ H) (htd : t = u' * h) (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ u ∈ U, t = u * J * u⁻¹ := by
  have htt : u' * h * (u' * h) = 1 := by rw [← htd]; exact ht
  have hhh : h * h = 1 := by
    have h0 : u' * (h * u' * h⁻¹) * (h * h) = 1 := by
      calc u' * (h * u' * h⁻¹) * (h * h) = u' * h * (u' * h) := by group
        _ = 1 := htt
    have h1 : h * h = (u' * (h * u' * h⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h0
    have h2 : h * h ∈ U := by
      rw [h1]
      exact U.inv_mem (U.mul_mem hu' (hHn h hh u' hu'))
    exact hUH _ h2 (H.mul_mem hh hh)
  have hpow : u' ^ Nat.card U = 1 := by
    have := pow_card_eq_one' (G := U) (x := ⟨u', hu'⟩)
    exact congrArg Subtype.val this
  rcases hH2 h hh hhh with rfl | rfl
  ·
    exfalso
    apply ht1
    rw [htd, mul_one] at ht ⊢
    have h2 : orderOf u' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
    have h3 : orderOf u' ∣ Nat.card U := orderOf_dvd_of_pow_eq_one hpow
    have h4 : Nat.gcd 2 (Nat.card U) = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_two_left]; exact hOdd
    have h5 := Nat.dvd_gcd h2 h3
    rw [h4, Nat.dvd_one] at h5
    exact orderOf_eq_one_iff.1 h5
  ·
    have hJinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hJ
    have hφ : h * u' * h = u'⁻¹ := by
      have h0 : u' * (h * u' * h) = 1 := by
        calc u' * (h * u' * h) = u' * h * (u' * h) := by group
          _ = 1 := htt
      exact eq_inv_of_mul_eq_one_right h0
    have hφ' : h * u'⁻¹ * h = u' := by
      have := congrArg (fun x => x⁻¹) hφ
      simpa [mul_assoc, hJinv] using this
    have hc : ∀ (x : G) (n : ℕ), h * x ^ n * h = (h * x * h) ^ n := by
      intro x n
      have := map_pow (MulAut.conj h) x n
      simpa [MulAut.conj_apply, hJinv] using this
    obtain ⟨m, hm⟩ := hOdd
    refine ⟨u' ^ (m + 1), pow_mem hu' _, ?_⟩
    have e1 : h * (u' ^ (m + 1))⁻¹ * h = u' ^ (m + 1) := by
      rw [← inv_pow, hc, hφ']
    have e2 : u' ^ (m + 1) * u' ^ (m + 1) = u' := by
      rw [← pow_add, show m + 1 + (m + 1) = Nat.card U + 1 by omega, pow_succ, hpow, one_mul]
    have e3 : h * (u' ^ (m + 1))⁻¹ = u' ^ (m + 1) * h := by
      have := eq_mul_inv_of_mul_eq e1
      rwa [hJinv] at this
    calc t = u' * h := htd
      _ = (u' ^ (m + 1) * u' ^ (m + 1)) * h := by rw [e2]
      _ = u' ^ (m + 1) * (u' ^ (m + 1) * h) := by rw [mul_assoc]
      _ = u' ^ (m + 1) * (h * (u' ^ (m + 1))⁻¹) := by rw [e3]
      _ = u' ^ (m + 1) * h * (u' ^ (m + 1))⁻¹ := by rw [mul_assoc]

section Involution

open CFSG.Walter.Ree.Model

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

@[expose] noncomputable def jElt (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ↥(ReeTag.G2.reeGamma K a) :=
  ⟨smallReeH a K (-1), ReeTag.reeFixedBorel_le_reeGamma
    (ReeTag.reeFixedTorus_le_reeFixedBorel (smallReeH_mem hK (-1)))⟩

theorem jElt_mul_self (hK : Nat.card K = 3 ^ (2 * a + 1)) : jElt hK * jElt hK = 1 :=
  Subtype.ext smallReeH_neg_one_mul_self

theorem jElt_ne_one (hK : Nat.card K = 3 ^ (2 * a + 1)) : jElt hK ≠ 1 := by
  intro h
  have h1 : smallReeH a K (-1) = smallReeH a K 1 := by
    rw [smallReeH_one]
    exact congrArg Subtype.val h
  have h2 : (-1 : Kˣ) = 1 := smallReeH_injective h1
  have h3 : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := congrArg Units.val h2
  have h4 : ringChar K ≠ 2 := by
    have : CharP K 3 := (small_Ree_field_power_identities a K hK).1
    rw [ringChar.eq K 3]
    decide
  rw [Units.val_neg, Units.val_one] at h3
  exact Ring.neg_one_ne_one_of_char_ne_two h4 h3

theorem orderOf_jElt (hK : Nat.card K = 3 ^ (2 * a + 1)) : orderOf (jElt hK) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact jElt_mul_self hK) (jElt_ne_one hK)

theorem jElt_mem_normalizer (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    jElt hK ∈ Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) := by
  rw [(std_facts hK).2.1]
  exact Subgroup.mem_subgroupOf.2 (ReeTag.reeFixedTorus_le_reeFixedBorel (smallReeH_mem hK (-1)))

theorem involution_conj_std (hK : Nat.card K = 3 ^ (2 * a + 1)) (t : ↥(ReeTag.G2.reeGamma K a))
    (ht : t ∈ Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))) (ht2 : orderOf t = 2) :
    ∃ u ∈ stdU a K, t = u * jElt hK * u⁻¹ := by
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := std_facts hK
  have hmul : t * t = 1 := by
    rw [← pow_two, ← ht2]
    exact pow_orderOf_eq_one t
  have hne : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  rw [hNU] at ht
  have htB : (t : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a :=
    Subgroup.mem_subgroupOf.1 ht
  rw [← SetLike.mem_coe,
    (ReeTag.ree_fixed_Bruhat_decomposition ReeTag.G2 a K).2.1] at htB
  obtain ⟨u', hu', h, hh, hteq⟩ := Set.mem_mul.1 htB
  have hu'Γ : u' ∈ ReeTag.G2.reeGamma K a := ReeTag.reeFixedPosUnipotent_le_reeGamma hu'
  have hhΓ : h ∈ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedBorel_le_reeGamma (ReeTag.reeFixedTorus_le_reeFixedBorel hh)
  refine involution_conj_aux (stdU a K) ((ReeTag.G2.reeFixedTorus K a).subgroupOf _) (jElt hK)
    ?_ ?_ ?_ (jElt_mul_self hK) ?_ t ⟨u', hu'Γ⟩ ⟨h, hhΓ⟩ (Subgroup.mem_subgroupOf.2 hu')
    (Subgroup.mem_subgroupOf.2 hh) (Subtype.ext hteq.symm) hmul hne
  · intro x hx y hy
    have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a :=
      Subgroup.mem_subgroupOf.1 hx
    have hy' : (y : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hy
    have hn := Subgroup.mem_normalizer_iff.1
      (ReeTag.reeFixedTorus_le_normalizer_reeFixedPosUnipotent hx') (y : ModGL ReeTag.G2.tag K)
    exact Subgroup.mem_subgroupOf.2 (hn.1 hy')
  · intro x hx hx'
    exact Subtype.ext (ReeTag.eq_one_of_mem_reeFixedPosUnipotent_of_mem_reeFixedTorus
      (Subgroup.mem_subgroupOf.1 hx) (Subgroup.mem_subgroupOf.1 hx'))
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup'
    rw [← hP, hn]
    exact Odd.pow (by decide)
  · intro x hx hxx
    have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a :=
      Subgroup.mem_subgroupOf.1 hx
    obtain ⟨s, hs⟩ := ReeTag.exists_smallReeTorusElt_eq hx'
    have h1 : smallReeH a K (s * s) = smallReeH a K 1 := by
      rw [smallReeH_mul, smallReeH_one]
      have := congrArg Subtype.val hxx
      simp only [Subgroup.coe_mul, OneMemClass.coe_one] at this
      rw [← hs] at this
      exact this
    have h2 : s * s = 1 := smallReeH_injective h1
    have h3 : (s : K) * (s : K) = 1 := by
      have := congrArg Units.val h2
      simpa using this
    rcases mul_self_eq_one_iff.1 h3 with h4 | h4
    · left
      have : s = 1 := Units.ext h4
      subst this
      exact Subtype.ext (by rw [← hs]; exact smallReeH_one)
    · right
      have : s = -1 := Units.ext (by rw [h4, Units.val_neg, Units.val_one])
      subst this
      exact Subtype.ext hs.symm

@[expose] noncomputable def xHom (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Multiplicative K →* ↥(ReeTag.G2.reeGamma K a) where
  toFun b := ⟨smallReeCoord a K 0 (Multiplicative.toAdd b) 0,
    ReeTag.reeFixedPosUnipotent_le_reeGamma
      (smallReeCoord_mem_reeFixedPosUnipotent hK 0 (Multiplicative.toAdd b) 0)⟩
  map_one' := Subtype.ext smallReeCoord_zero
  map_mul' b d := Subtype.ext (by
    have h := smallReeCoord_zero_mul (a := a) (K := K) (Multiplicative.toAdd b) 0
      (Multiplicative.toAdd d) 0
    rw [add_zero] at h
    exact h.symm)

theorem coe_xHom (hK : Nat.card K = 3 ^ (2 * a + 1)) (b : Multiplicative K) :
    ((xHom hK b : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      smallReeCoord a K 0 (Multiplicative.toAdd b) 0 :=
  rfl

theorem xHom_injective (hK : Nat.card K = 3 ^ (2 * a + 1)) : Function.Injective (xHom hK) := by
  intro c e h
  have h1 : ((xHom hK c : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      ((xHom hK e : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) :=
    congrArg Subtype.val h
  rw [coe_xHom, coe_xHom] at h1
  have h2 := smallReeCoordU_injective hK (t := 0) (b := Multiplicative.toAdd c) (c := 0)
    (t' := 0) (b' := Multiplicative.toAdd e) (c' := 0) (Subtype.ext h1)
  exact Multiplicative.toAdd.injective h2.2.1

theorem xHom_range (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (xHom hK).range = stdU a K ⊓ Subgroup.centralizer ({jElt hK} :
      Set ↥(ReeTag.G2.reeGamma K a)) := by
  have hmid := coe_reeFixedPosUnipotent_inf_centralizer (K := K) (a := a) hK
  ext x
  rw [MonoidHom.mem_range, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hx : ((x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧
      (x : ModGL ReeTag.G2.tag K) ∈ Subgroup.centralizer ({smallReeH a K (-1)} :
        Set (ModGL ReeTag.G2.tag K))) ↔ (x : ModGL ReeTag.G2.tag K) ∈ smallReeMidX a K := by
    rw [← hmid, SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : ((xHom hK b : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) ∈
        smallReeMidX a K := ⟨Multiplicative.toAdd b, rfl⟩
    obtain ⟨h1, h2⟩ := hx.2 hb
    refine ⟨h1, Subtype.ext ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 h2
  · rintro ⟨h1, h2⟩
    have h3 : (x : ModGL ReeTag.G2.tag K) ∈ Subgroup.centralizer ({smallReeH a K (-1)} :
        Set (ModGL ReeTag.G2.tag K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h2)
    obtain ⟨b, hb⟩ := hx.1 ⟨h1, h3⟩
    exact ⟨Multiplicative.ofAdd b, Subtype.ext hb⟩

theorem isElemAbelian_xHom_range (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    CFSG.Open.IsElemAbelian 3 (xHom hK).range := by
  refine ⟨inferInstance, ?_⟩
  rintro _ ⟨b, rfl⟩
  have h3 : CharP K 3 := (small_Ree_field_power_identities a K hK).1
  rw [← map_pow]
  have : b ^ 3 = 1 := by
    rw [← ofAdd_toAdd b, ← ofAdd_nsmul, nsmul_eq_mul]
    have : ((3 : ℕ) : K) = 0 := CharP.cast_eq_zero K 3
    rw [this, zero_mul]
    rfl
  rw [this, map_one]

theorem card_xHom_range (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (xHom hK).range = 3 ^ (2 * a + 1) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (xHom_injective hK)).toEquiv, ← hK]
  exact Nat.card_congr Multiplicative.toAdd

theorem not_centralizer_le_normalizer (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ¬ Subgroup.centralizer ({jElt hK} : Set ↥(ReeTag.G2.reeGamma K a)) ≤
      Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
        Set ↥(ReeTag.G2.reeGamma K a)) := by
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  have hmem : CFSG.LieType.Chevalley.canonicalRep (CFSG.LieType.Chevalley.coxeterSystem
      ReeTag.G2.tag) K w₀ ∈ smallReeInvCentralizer a K :=
    canonicalRep_mem_smallReeInvCentralizer hw₀
  have hmem' := Subgroup.mem_inf.1 hmem
  intro hle
  have hc : (⟨_, hmem'.1⟩ : ↥(ReeTag.G2.reeGamma K a)) ∈
      Subgroup.centralizer ({jElt hK} : Set ↥(ReeTag.G2.reeGamma K a)) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hmem'.2))
  have h1 := hle hc
  rw [(std_facts hK).2.1] at h1
  exact ReeTag.canonicalRep_longest_not_mem_reeFixedBorel hK hw₀ (Subgroup.mem_subgroupOf.1 h1)

end Involution

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem isSolvable_of_stabilizer {Γ : Type*} [Group Γ] (U : Subgroup Γ)
    (hB : Group.IsSolvable ↥(Subgroup.normalizer (U : Set Γ)))
    (hO : Group.IsSolvable (Outer Γ)) (A : Subgroup (MulAut Γ))
    (hA : ∀ α ∈ A, U.map α.toMonoidHom = U) : Group.IsSolvable A := by
  set S₀ : Subgroup Γ := A.comap (MulAut.conj : Γ →* MulAut Γ) with hS₀
  have hle : S₀ ≤ Subgroup.normalizer (U : Set Γ) := by
    intro x hx
    have h1 := hA _ hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h2 : (MulAut.conj x) y ∈ U ↔ y ∈ U := by
      conv_lhs => rw [← h1]
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [← h2]
    simp [MulAut.conj_apply]
  have : Group.IsSolvable S₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  let f : S₀ →* A := ((MulAut.conj : Γ →* MulAut Γ).comp S₀.subtype).codRestrict A fun x => x.2
  let g : A →* Outer Γ := (QuotientGroup.mk' (inner Γ)).comp A.subtype
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro α hα
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hα
  obtain ⟨x, hx⟩ := hα
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  show (MulAut.conj : Γ →* MulAut Γ) x ∈ A
  rw [hx]
  exact α.2

section Solvable

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem isSolvable_stdB : Group.IsSolvable ↥(stdB a K) := by
  have h := (ReeTag.ree_fixed_Bruhat_decomposition ReeTag.G2 a K).2.2.2.2.2.2.2.1
  have hle : ReeTag.G2.reeFixedBorel K a ≤ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedBorel_le_reeGamma
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).injective

theorem inf_map_conj_eq_bot (hK : Nat.card K = 3 ^ (2 * a + 1))
    {g : ↥(ReeTag.G2.reeGamma K a)} (hg : g ∉ stdB a K) :
    stdU a K ⊓ (stdU a K).map (MulAut.conj g).toMonoidHom = ⊥ := by
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, hcardΓ, hP, hstab, hUn, hNU, hNUV⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have := htrans
  have hNU' : Subgroup.normalizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) = stdB a K := hNU
  have hUB : stdU a K ≤ stdB a K := hNU' ▸ Subgroup.le_normalizer
  have hstab' : ∀ x : ↥(ReeTag.G2.reeGamma K a), x ∈ stdB a K ↔
      x • (QuotientGroup.mk 1 : ↥(ReeTag.G2.reeGamma K a) ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) =
          QuotientGroup.mk 1 := fun x => by
    rw [← MulAction.mem_stabilizer_iff, hstab]
    rfl
  have hω : g • (QuotientGroup.mk 1 : ↥(ReeTag.G2.reeGamma K a) ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) ≠ QuotientGroup.mk 1 :=
    fun h => hg ((hstab' g).2 h)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxU, y, hy, hyx⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have hfix : x • (g • (QuotientGroup.mk 1 : ↥(ReeTag.G2.reeGamma K a) ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a))) =
        g • (QuotientGroup.mk 1 : ↥(ReeTag.G2.reeGamma K a) ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) := by
    have hxy : x = g * y * g⁻¹ := hyx.symm
    rw [hxy, mul_smul, mul_smul, inv_smul_smul]
    rw [(hstab' y).1 (hUB hy)]
  obtain ⟨u, -, hu⟩ := hreg _ _ hω hω
  have h1 := hu ⟨x, hxU⟩ hfix
  have h2 := hu 1 (by simp)
  have := h1.trans h2.symm
  exact congrArg Subtype.val this

end Solvable

section Rank

variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]

@[expose] noncomputable def stdU1 : Subgroup ↥(ReeTag.G2.reeGamma K a) :=
  (smallReeU1 a K).subgroupOf (ReeTag.G2.reeGamma K a)

variable {a K}

theorem smallReeU1_le_reeFixedPosUnipotent (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    smallReeU1 a K ≤ ReeTag.G2.reeFixedPosUnipotent K a := by
  rintro _ ⟨b, c, rfl⟩
  exact smallReeCoord_mem_reeFixedPosUnipotent hK 0 b c

theorem stdU1_le_stdU (hK : Nat.card K = 3 ^ (2 * a + 1)) : stdU1 a K ≤ stdU a K :=
  fun _ hx => Subgroup.mem_subgroupOf.2 (smallReeU1_le_reeFixedPosUnipotent hK
    (Subgroup.mem_subgroupOf.1 hx))

theorem card_stdU1 (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (stdU1 a K) = (3 ^ (2 * a + 1)) ^ 2 := by
  have hle : smallReeU1 a K ≤ ReeTag.G2.reeGamma K a :=
    (smallReeU1_le_reeFixedPosUnipotent hK).trans ReeTag.reeFixedPosUnipotent_le_reeGamma
  rw [stdU1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact card_smallReeU1 hK

theorem mem_stdU1_of_pow_three (hK : Nat.card K = 3 ^ (2 * a + 1))
    {x : ↥(ReeTag.G2.reeGamma K a)} (hx : x ∈ stdU a K) (h3 : x ^ 3 = 1) : x ∈ stdU1 a K := by
  have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a :=
    Subgroup.mem_subgroupOf.1 hx
  obtain ⟨t, b, c, hxe⟩ := exists_smallReeCoordU_eq hK (⟨(x : ModGL ReeTag.G2.tag K), hx'⟩ :
    ↥(ReeTag.G2.reeFixedPosUnipotent K a))
  have hxe' : (x : ModGL ReeTag.G2.tag K) = smallReeCoord a K t b c :=
    (congrArg Subtype.val hxe).symm
  have h1 : smallReeCoord a K t b c ^ 3 = 1 := by
    rw [← hxe']
    exact congrArg Subtype.val h3
  rw [smallReeCoord_pow_three hK] at h1
  have h2 := smallReeCoordU_injective hK (t := 0) (b := 0) (c := -(t ^ 2 * smallReeSigma a t))
    (t' := 0) (b' := 0) (c' := 0) (Subtype.ext (h1.trans smallReeCoord_zero.symm))
  have ht : t = 0 := by
    have h4 : t ^ 2 * smallReeSigma a t = 0 := neg_eq_zero.1 h2.2.2
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact pow_eq_zero_iff (by norm_num) |>.1 h5
    · exact pow_eq_zero_iff (by positivity) |>.1 h5
  rw [stdU1, Subgroup.mem_subgroupOf, hxe']
  exact (mem_smallReeU1_iff hK t b c).2 ht

theorem zHom_range_le_stdU1 (hK : Nat.card K = 3 ^ (2 * a + 1)) : (zHom hK).range ≤ stdU1 a K := by
  rintro _ ⟨c, rfl⟩
  exact Subgroup.mem_subgroupOf.2 ⟨0, Multiplicative.toAdd c, rfl⟩

end Rank

section SylowRank

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem card_le_of_pow_three_le_stdU (hK : Nat.card K = 3 ^ (2 * a + 1))
    (D : Subgroup ↥(ReeTag.G2.reeGamma K a)) (hle : D ≤ stdU a K) (h3 : ∀ x ∈ D, x ^ 3 = 1) :
    Nat.card D ≤ (3 ^ (2 * a + 1)) ^ 2 ∧ ((3 ^ (2 * a + 1)) ^ 2 < 3 * Nat.card D →
      stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
        Set ↥(ReeTag.G2.reeGamma K a)) ≤ D) := by
  have hD1 : D ≤ stdU1 a K := fun x hx => mem_stdU1_of_pow_three hK (hle hx) (h3 x hx)
  have hcard := card_stdU1 hK
  refine ⟨hcard ▸ Subgroup.card_le_of_le hD1, fun hlt => ?_⟩
  have hdvd : Nat.card D ∣ (3 ^ (2 * a + 1)) ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hD1
  rw [← pow_mul] at hdvd hlt
  obtain ⟨j, hj, hjD⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hjD] at hlt
  have hj' : (2 * a + 1) * 2 ≤ j := by
    by_contra hcon
    have : j + 1 ≤ (2 * a + 1) * 2 := by omega
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) this
    rw [pow_succ] at this
    omega
  have hjeq : j = (2 * a + 1) * 2 := le_antisymm hj hj'
  have hDeq : D = stdU1 a K := by
    refine Subgroup.eq_of_le_of_card_ge hD1 ?_
    rw [hcard, ← pow_mul, hjD, hjeq]
  rw [← zHom_range hK, hDeq]
  exact zHom_range_le_stdU1 hK

end SylowRank

end CFSG.AGLEmbedding.ReeModel
