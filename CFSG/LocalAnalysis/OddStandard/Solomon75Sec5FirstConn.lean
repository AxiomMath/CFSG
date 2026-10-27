module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstTheta
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreGamma
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74L38Four

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.SignalizerFunctor.Helpers

open scoped commutatorElement

@[expose] def FourInE8 {X : Type} [Group X] (P : Subgroup X) : Prop :=
  ∀ U : Subgroup X, U ≤ P → Open.IsElemAbelian 2 U → Nat.card U = 4 →
    ∃ E : Subgroup X, E ≤ P ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E

@[expose] def AhatFourInE8 (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ T : Sylow 2 K,
    FourInE8 (T : Subgroup K)

theorem ahatFourInE8_of_coverSylowData {n : ℕ} (hD : CoverSylowData n) : AhatFourInE8 n :=
  fun K _ _ hK T U hUT hUab hU4 => hD.four_in_E8 K hK T U hUT hUab hU4

theorem FourInE8.of_mulEquiv {K K' : Type} [Group K] [Group K'] {S : Subgroup K}
    {S' : Subgroup K'} (e : ↥S ≃* ↥S') (h : FourInE8 S) : FourInE8 S' := by
  intro U hUS hUab hU4
  obtain ⟨E₀, hE₀S, hE₀ab, hE₀8, hUE₀⟩ := h (CoreAux.shapeMap e.symm U)
    (CoreAux.shapeMap_le e.symm U) (CoreAux.isElemAbelian_shapeMap e.symm hUab)
    (by rw [CoreAux.card_shapeMap e.symm hUS, hU4])
  refine ⟨CoreAux.shapeMap e E₀, CoreAux.shapeMap_le e E₀,
    CoreAux.isElemAbelian_shapeMap e hE₀ab, ?_, ?_⟩
  · rw [CoreAux.card_shapeMap e hE₀S]
    exact hE₀8
  · rw [← CoreAux.shapeMap_shapeMap_symm e hUS]
    exact CoreAux.shapeMap_mono e hUE₀

theorem rankThree_connected_of_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K']
    {S : Subgroup K} {S' : Subgroup K'} (e : ↥S ≃* ↥S')
    (h : ∀ E E' : Subgroup K, AhatData.RankThreeVertex S E → AhatData.RankThreeVertex S E' →
      Relation.ReflTransGen (AhatData.RankThreeAdj S) E E')
    {E E' : Subgroup K'} (hE : AhatData.RankThreeVertex S' E)
    (hE' : AhatData.RankThreeVertex S' E') :
    Relation.ReflTransGen (AhatData.RankThreeAdj S') E E' := by
  have hvert : ∀ {F : Subgroup K'}, AhatData.RankThreeVertex S' F →
      AhatData.RankThreeVertex S (CoreAux.shapeMap e.symm F) := fun {F} hF =>
    ⟨CoreAux.shapeMap_le e.symm F, CoreAux.isElemAbelian_shapeMap e.symm hF.2.1, by
      rw [CoreAux.card_shapeMap e.symm hF.1]
      exact hF.2.2⟩
  have hvert' : ∀ {F : Subgroup K}, AhatData.RankThreeVertex S F →
      AhatData.RankThreeVertex S' (CoreAux.shapeMap e F) := fun {F} hF =>
    ⟨CoreAux.shapeMap_le e F, CoreAux.isElemAbelian_shapeMap e hF.2.1, by
      rw [CoreAux.card_shapeMap e hF.1]
      exact hF.2.2⟩
  have hadj : ∀ F F' : Subgroup K, AhatData.RankThreeAdj S F F' →
      AhatData.RankThreeAdj S' (CoreAux.shapeMap e F) (CoreAux.shapeMap e F') := by
    rintro F F' ⟨hF, hF', h4⟩
    refine ⟨hvert' hF, hvert' hF', ?_⟩
    have hle : CoreAux.shapeMap e (F ⊓ F') ≤ CoreAux.shapeMap e F ⊓ CoreAux.shapeMap e F' :=
      le_inf (CoreAux.shapeMap_mono e inf_le_left) (CoreAux.shapeMap_mono e inf_le_right)
    calc 4 ≤ Nat.card ↥(F ⊓ F') := h4
      _ = Nat.card ↥(CoreAux.shapeMap e (F ⊓ F')) :=
        (CoreAux.card_shapeMap e (inf_le_left.trans hF.1)).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have key : Relation.ReflTransGen (AhatData.RankThreeAdj S')
      (CoreAux.shapeMap e (CoreAux.shapeMap e.symm E))
      (CoreAux.shapeMap e (CoreAux.shapeMap e.symm E')) :=
    Relation.ReflTransGen.lift (CoreAux.shapeMap e) hadj _ _ (h _ _ (hvert hE) (hvert hE'))
  rwa [CoreAux.shapeMap_shapeMap_symm e hE.1, CoreAux.shapeMap_shapeMap_symm e hE'.1] at key

section General

variable {G : Type} [Group G]

theorem W1V_mono {V U U' : Subgroup G} (h : U ≤ U') : W1V V U ≤ W1V V U' :=
  iSup₂_le fun u hu => iSup_le fun hu1 => le_iSup₂_of_le u (h hu) (le_iSup_of_le hu1 le_rfl)

theorem theta_le_W1V {V U : Subgroup G} {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    theta V u ≤ W1V V U :=
  le_iSup₂_of_le u hu (le_iSup_of_le hu1 le_rfl)

theorem theta_map_conj {V : Subgroup G} {g : G} (hg : g ∈ centralizer (V : Set G)) (b : G) :
    (theta V b).map (MulAut.conj g).toMonoidHom = theta V (g * b * g⁻¹) := by
  have hgV : g ∈ normalizer (V : Set G) := centralizer_le_normalizer _ hg
  have hgC : g ∈ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hg
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have h1 : (oddCoreOf (cen b)).map (MulAut.conj g).toMonoidHom =
      oddCoreOf (cen (g * b * g⁻¹)) := by
    rw [CoreAux.cen_conj, CoreAux.oddCoreOf_map_equiv (MulAut.conj g) (cen b)]
  have h2 : (oddCoreOf (centralizer (V : Set G))).map (MulAut.conj g).toMonoidHom =
      oddCoreOf (centralizer (V : Set G)) := by
    rw [← CoreAux.oddCoreOf_map_equiv (MulAut.conj g) (centralizer (V : Set G)),
      map_conj_eq_of_mem_normalizer hgC]
  have h3 : (cen b).map (MulAut.conj g).toMonoidHom = cen (g * b * g⁻¹) :=
    (CoreAux.cen_conj g b).symm
  unfold theta
  rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_inf_eq _ _ _ hinj, h1, h2, h3,
    map_conj_eq_of_mem_normalizer hgV]

theorem W1V_map_conj {V : Subgroup G} {g : G} (hg : g ∈ centralizer (V : Set G))
    (U : Subgroup G) :
    (W1V V U).map (MulAut.conj g).toMonoidHom = W1V V (U.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [W1V, Subgroup.map_iSup]
    refine iSup_le fun u => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hu => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hu1 => ?_
    rw [theta_map_conj hg]
    refine theta_le_W1V (u := g * u * g⁻¹) ⟨u, hu, by simp [MulAut.conj_apply]⟩ ?_
    intro h
    apply hu1
    have : (MulAut.conj g) u = (MulAut.conj g) 1 := by simpa [MulAut.conj_apply] using h
    exact (MulAut.conj g).injective this
  · refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
    obtain ⟨u, hu, rfl⟩ := hv
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hv1 (map_one _)
    rw [show (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ by simp [MulAut.conj_apply],
      ← theta_map_conj hg]
    exact Subgroup.map_mono (theta_le_W1V hu hu1)

theorem mem_normalizer_W1V {V U : Subgroup G} {g : G} (hg : g ∈ centralizer (V : Set G))
    (hgU : g ∈ normalizer (U : Set G)) : g ∈ normalizer ((W1V V U : Subgroup G) : Set G) :=
  mem_normalizer_of_map_conj_eq (by rw [W1V_map_conj hg, map_conj_eq_of_mem_normalizer hgU])

theorem le_normalizer_W1V {V E : Subgroup G} (hEV : E ≤ centralizer (V : Set G)) :
    E ≤ normalizer ((W1V V E : Subgroup G) : Set G) := fun x hx =>
  mem_normalizer_W1V (hEV hx) (Subgroup.le_normalizer hx)

variable [Finite G]

theorem exists_fourSub_of_le_card {B : Subgroup G} (hB : Open.IsElemAbelian 2 B)
    (h4 : 4 ≤ Nat.card B) :
    ∃ H : Subgroup G, H ≤ B ∧ Open.IsElemAbelian 2 H ∧ Nat.card H = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := isPGroup_two_of_sq (CoreAux.isElemAbelian_iff.mp hB).2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hle : Nat.card B ≤ 2 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card B := by
    rw [hk]
    exact Nat.pow_dvd_pow 2 hk2
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 2 hdvd
  refine ⟨V.map B.subtype, (Subgroup.map_subtype_le V), ?_, ?_⟩
  · exact CoreAux.isElemAbelian_mono (Subgroup.map_subtype_le V) hB
  · rw [Subgroup.card_map_of_injective B.subtype_injective, hV]
    norm_num

theorem exists_fixed_mem_coset_of_isPGroup {O V : Subgroup G} (hodd : Odd (Nat.card O))
    (hV : IsPGroup 2 V) (hVO : V ≤ normalizer (O : Set G)) {y : G}
    (hy : ∀ v ∈ V, y⁻¹ * (v * y * v⁻¹) ∈ O) :
    ∃ p ∈ O, y * p ∈ centralizer (V : Set G) := by
  classical
  have hsm : ∀ v : G, v ∈ V → ∀ p : G, p ∈ O → y⁻¹ * (v * (y * p) * v⁻¹) ∈ O := by
    intro v hv p hp
    have e : y⁻¹ * (v * (y * p) * v⁻¹) = (y⁻¹ * (v * y * v⁻¹)) * (v * p * v⁻¹) := by group
    rw [e]
    exact O.mul_mem (hy v hv) ((Subgroup.mem_normalizer_iff.1 (hVO hv) p).1 hp)
  let f : V → O → O := fun v p => ⟨y⁻¹ * ((v : G) * (y * (p : G)) * (v : G)⁻¹), hsm v v.2 p p.2⟩
  have hf1 : ∀ p : O, f 1 p = p := fun p => Subtype.ext (by simp [f])
  have hfm : ∀ (v w : V) (p : O), f (v * w) p = f v (f w p) := fun v w p => Subtype.ext (by
    simp only [f, Subgroup.coe_mul, mul_inv_rev]
    group)
  letI act : MulAction V O := { smul := f, one_smul := hf1, mul_smul := hfm }
  have hmod := hV.card_modEq_card_fixedPoints O
  have hne : (MulAction.fixedPoints V O).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hmod
    have h0 : Nat.card O ≡ 0 [MOD 2] := by simpa using hmod
    have h2 : 2 ∣ Nat.card O := Nat.modEq_zero_iff_dvd.1 h0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, p.2, ?_⟩
  rw [mem_centralizer_iff]
  intro v hv
  have hfix : (⟨v, hv⟩ : V) • p = p := hp ⟨v, hv⟩
  have h1 : y⁻¹ * (v * (y * (p : G)) * v⁻¹) = p := congrArg Subtype.val hfix
  calc v * (y * (p : G)) = (v * (y * (p : G)) * v⁻¹) * v := by group
    _ = (y * (y⁻¹ * (v * (y * (p : G)) * v⁻¹))) * v := by group
    _ = y * p * v := by rw [h1]

theorem mem_of_isSylowTwoIn_of_comm {W P : Subgroup G} (hP : IsSylowTwoIn W P) {t : G}
    (htW : t ∈ W) (ht2 : t * t = 1) (hcomm : ∀ p ∈ P, p * t = t * p) : t ∈ P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 P W := CFSG.ABGLocalTools.isSylowOf_iff.2 hP
  have hzp : IsPGroup 2 (zpowers t) := by
    refine isPGroup_two_of_sq fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, ht2, one_zpow]
  have hPn : P ≤ normalizer (zpowers t : Set G) := by
    intro p hp
    have hc : p ∈ centralizer ((zpowers t : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (Commute.zpow_left (show Commute t p from (hcomm p hp).symm) k).eq
    exact centralizer_le_normalizer _ hc
  have hQ : IsPGroup 2 (P ⊔ zpowers t : Subgroup G) := hS.isPGroup.to_sup_of_normal_right' hzp hPn
  have heq := hS.eq_of_le (le_sup_left : P ≤ P ⊔ zpowers t)
    (sup_le hS.le (Subgroup.zpowers_le.2 htW)) hQ
  have hmem : t ∈ P ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rwa [heq] at hmem

theorem le_iSup_inf_centralizer_of_hyperplane {E Y : Subgroup G} (hE : Open.IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (hEY : E ≤ normalizer (Y : Set G)) (hodd : Odd (Nat.card Y)) :
    Y ≤ ⨆ (B : Subgroup G) (_ : B ≤ E) (_ : 2 * Nat.card B = Nat.card E),
      Y ⊓ centralizer (B : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hE.2 x x.2) }
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : MulDistribMulAction E Y := Subgroup.conjMulDistribMulActionOfLeNormalizer E Y hEY
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := Y)
    (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
  intro x hx
  have hmem : (⟨x, hx⟩ : Y) ∈ ⨆ (B : Subgroup E) (_ : B.index = 2),
      CFSG.fixedPointSubgroup B Y := hgen ▸ Subgroup.mem_top _
  have hle : (⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B Y) ≤
      (⨆ (B : Subgroup G) (_ : B ≤ E) (_ : 2 * Nat.card B = Nat.card E),
        Y ⊓ centralizer (B : Set G)).comap Y.subtype := by
    refine iSup₂_le fun B hB => ?_
    intro y hy
    have hB' : B.map E.subtype ≤ E := Subgroup.map_subtype_le B
    have hcard : 2 * Nat.card (B.map E.subtype) = Nat.card E := by
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      have h := B.card_mul_index
      rw [hB] at h
      omega
    have hyc : (y : G) ∈ centralizer ((B.map E.subtype : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hya : (⟨b, hb⟩ : B) • y = y := hy ⟨b, hb⟩
      have hya' : ((b : E) : G) * y * ((b : E) : G)⁻¹ = y := congrArg Subtype.val hya
      calc ((b : E) : G) * y = ((b : E) : G) * y * ((b : E) : G)⁻¹ * ((b : E) : G) := by group
        _ = y * ((b : E) : G) := by rw [hya']
    exact Subgroup.mem_iSup_of_mem (B.map E.subtype) (Subgroup.mem_iSup_of_mem hB'
      (Subgroup.mem_iSup_of_mem hcard (show (y : G) ∈ Y ⊓ centralizer
        ((B.map E.subtype : Subgroup G) : Set G) from ⟨y.2, hyc⟩)))
  exact hle hmem

end General

section Transport

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_equiv_quot {A P : Subgroup X} (hP : IsSylowTwoIn A P) :
    ∃ T : Sylow 2 (↥A ⧸ pPrimeCore 2 ↥A),
      Nonempty (↥(T : Subgroup (↥A ⧸ pPrimeCore 2 ↥A)) ≃* ↥P) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPA, hP2, hPidx⟩ := hP
  set N := pPrimeCore 2 ↥A with hN
  let π : ↥A →* ↥A ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  let PA : Sylow 2 ↥A := IsPGroup.toSylow (P := P.subgroupOf A)
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm) hPidx
  refine ⟨Sylow.mapSurjective hπ PA, ?_⟩
  let φ : ↥P →* ↥A ⧸ N := π.comp (Subgroup.inclusion hPA)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : Subgroup.inclusion hPA x ∈ N := (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : X) ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨hPA x.2, hxN⟩
    obtain ⟨k, hk⟩ := hP2 x
    have hkX : (x : X) ^ 2 ^ k = 1 := by
      have := congrArg (fun w : ↥P => (w : X)) hk
      simpa using this
    exact Subtype.ext (Sec5Two.eq_one_of_mem_oddCoreOf_of_pow hmem hkX)
  have hPAcoe : (PA : Subgroup ↥A) = P.subgroupOf A := rfl
  have hrange : φ.range = (Sylow.mapSurjective hπ PA : Subgroup (↥A ⧸ N)) := by
    rw [Sylow.coe_mapSurjective hπ PA, hPAcoe, MonoidHom.range_comp,
      Subgroup.inclusion_range hPA]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hφinj).symm⟩

theorem rankThree_connected_of_sylow {n : ℕ} {z : X}
    {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}
    (h : Sec5Data X n z (zpowers z) S) {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P)
    {E E' : Subgroup X} (hE : AhatData.RankThreeVertex P E)
    (hE' : AhatData.RankThreeVertex P E') :
    Relation.ReflTransGen (AhatData.RankThreeAdj P) E E' := by
  obtain ⟨T, ⟨e⟩⟩ := exists_sylow_equiv_quot hP
  exact rankThree_connected_of_mulEquiv e
    (fun F F' hF hF' => rank_three_connected h.maxdeg.1 hA.2 T hF hF') hE hE'

theorem fourInE8_of_ahat {n : ℕ} (hR : AhatFourInE8 n) {z : X} {A P : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hP : IsSylowTwoIn A P) : FourInE8 P := by
  obtain ⟨T, ⟨e⟩⟩ := exists_sylow_equiv_quot hP
  exact FourInE8.of_mulEquiv e (hR _ hA.2 T)

end Transport

section SW6

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

private structure TwoCompData (X : Type) [Group X] [Finite X] (n : ℕ) (z : X)
    (A₁ A₂ V : Subgroup X) : Prop where
  hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁
  hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂
  h12 : A₁ ≠ A₂
  hV : Open.IsElemAbelian 2 V
  hV4 : Nat.card V = 4
  hVA : V ≤ A₂

private theorem W1V_eq_of_le (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V E U : Subgroup X}
    (hT : TwoCompData X n z A₁ A₂ V) (hE : Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E)
    (hEA : E ≤ A₁) (hEV : E ≤ centralizer (V : Set X)) (hUE : U ≤ E) (hU4 : Nat.card U = 4) :
    W1V V U = W1V V E := by
  refine le_antisymm (W1V_mono hUE) ?_
  obtain ⟨hodd, hcen⟩ := thetaV_complete h hT.hA₁ hT.hA₂ hT.h12 hT.hV hT.hV4 hT.hVA hE hE8 hEA hEV
  have hUN : U ≤ normalizer ((W1V V E : Subgroup X) : Set X) := hUE.trans (le_normalizer_W1V hEV)
  have hgen := CoreAux.le_iSup_inf_cen_of_four (CoreAux.isElemAbelian_mono hUE hE) hU4.ge hUN hodd
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  exact (hcen a (hUE ha) ha1).trans (theta_le_W1V ha ha1)

private theorem W1V_eq_of_adj (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V P : Subgroup X}
    (hT : TwoCompData X n z A₁ A₂ V) (hP : IsSylowTwoIn A₁ P)
    (hPV : P ≤ centralizer (V : Set X)) {E E' : Subgroup X}
    (hadj : AhatData.RankThreeAdj P E E') : W1V V E = W1V V E' := by
  obtain ⟨hE, hE', h4⟩ := hadj
  obtain ⟨U₀, hU₀, -, hU₀4⟩ := exists_fourSub_of_le_card
    (CoreAux.isElemAbelian_mono (inf_le_left : E ⊓ E' ≤ E) hE.2.1) h4
  have h1 := W1V_eq_of_le h hT hE.2.1 hE.2.2 (hE.1.trans hP.1) (hE.1.trans hPV)
    (hU₀.trans inf_le_left) hU₀4
  have h2 := W1V_eq_of_le h hT hE'.2.1 hE'.2.2 (hE'.1.trans hP.1) (hE'.1.trans hPV)
    (hU₀.trans inf_le_right) hU₀4
  rw [← h1, h2]

private theorem W1V_eq_of_vertices (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V P : Subgroup X}
    (hT : TwoCompData X n z A₁ A₂ V) (hP : IsSylowTwoIn A₁ P)
    (hPV : P ≤ centralizer (V : Set X)) {E E' : Subgroup X}
    (hE : AhatData.RankThreeVertex P E) (hE' : AhatData.RankThreeVertex P E') :
    W1V V E = W1V V E' := by
  have hc := rankThree_connected_of_sylow h hT.hA₁ hP hE hE'
  clear hE'
  induction hc with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (W1V_eq_of_adj h hT hP hPV hbc)

private theorem W1V_eq_of_fourSub_vertex (h : Sec5Data X n z (zpowers z) S)
    {A₁ A₂ V P : Subgroup X} (hT : TwoCompData X n z A₁ A₂ V) (hP : IsSylowTwoIn A₁ P)
    (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P) {E : Subgroup X}
    (hE : AhatData.RankThreeVertex P E) (H : FourSub P) : W1V V H.1 = W1V V E := by
  obtain ⟨E', hE'P, hE'ab, hE'8, hHE'⟩ := hR H.1 H.2.1 H.2.2.1 H.2.2.2
  rw [W1V_eq_of_le h hT hE'ab hE'8 (hE'P.trans hP.1) (hE'P.trans hPV) hHE' H.2.2.2]
  exact W1V_eq_of_vertices h hT hP hPV ⟨hE'P, hE'ab, hE'8⟩ hE

end SW6

section SW7

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

private theorem z_mem_sylow (h : Sec5Data X n z (zpowers z) S) {A₁ V P : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁) (hzV : z ∈ V) (hP : IsSylowTwoIn A₁ P)
    (hPV : P ≤ centralizer (V : Set X)) : z ∈ P := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z, pow_two] at this
  exact mem_of_isSylowTwoIn_of_comm hP (Sec5Two.z_mem_comp h hA₁) hz2
    (fun p hp => (mem_centralizer_iff.1 (hPV hp) z hzV).symm)

open CFSG.ComponentClassification.HarrisLit.T1.S74.L38 in
private theorem exists_vertex_mem_of_invol (h : Sec5Data X n z (zpowers z) S) {V P E₀ : Subgroup X}
    (hzV : z ∈ V) (hPV : P ≤ centralizer (V : Set X)) (hzP : z ∈ P) (hR : FourInE8 P)
    (hE₀ : AhatData.RankThreeVertex P E₀) {b : X} (hbP : b ∈ P) (hb2 : orderOf b = 2) :
    ∃ E : Subgroup X, AhatData.RankThreeVertex P E ∧ b ∈ E := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z, pow_two] at this
  have hz1 : z ≠ 1 := fun e => by
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have hb2' : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2, pow_two] at this
  have hb1 : b ≠ 1 := fun e => by
    rw [e, orderOf_one] at hb2
    omega
  have hzc : ∀ p ∈ P, p * z = z * p := fun p hp => (mem_centralizer_iff.1 (hPV hp) z hzV).symm
  by_cases hbz : b = z
  · by_cases hzE : z ∈ E₀
    · exact ⟨E₀, hE₀, hbz ▸ hzE⟩
    · have hcomm : ∀ v ∈ E₀, Commute v z := fun v hv => hzc v (hE₀.1 hv)
      obtain ⟨hab, hcard⟩ := isElemAbelian_sup_zpowers hE₀.2.1 hz2 hzE hcomm
      refine ⟨E₀ ⊔ zpowers z, ⟨sup_le hE₀.1 (Subgroup.zpowers_le.2 hzP), hab, ?_⟩, ?_⟩
      · rw [hcard]
        have := hE₀.2.2
        omega
      · rw [hbz]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  · have hcomm : Commute b z := hzc b hbP
    obtain ⟨E, hEP, hEab, hE8, hUE⟩ := hR (four b z hb2' hz2 hcomm) (four_le hbP hzP)
      (isElemAbelian_four b z hb2' hz2 hcomm) (card_four hb2' hz2 hcomm hb1 hz1 hbz)
    exact ⟨E, ⟨hEP, hEab, hE8⟩, hUE left_mem_four⟩

open CFSG.ComponentClassification.HarrisLit.T1.S74.L38 in
theorem fourInE8_of_invol {P : Subgroup X} {z₀ : X} (hzP : z₀ ∈ P) (hz2 : z₀ * z₀ = 1)
    (hz1 : z₀ ≠ 1) (hzc : ∀ p ∈ P, p * z₀ = z₀ * p)
    (h : ∀ b ∈ P, orderOf b = 2 →
      ∃ E : Subgroup X, E ≤ P ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ b ∈ E) :
    FourInE8 P := by
  intro U hUP hUab hU4
  have hoz : orderOf z₀ = 2 := orderOf_eq_prime (by rw [← pow_two] at hz2; exact hz2) hz1
  have hcomm : ∀ v ∈ U, Commute v z₀ := fun v hv => hzc v (hUP hv)
  by_cases hzU : z₀ ∈ U
  · have hnle : ¬ U ≤ zpowers z₀ := by
      intro hle
      have h2 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hoz] at h2
      omega
    obtain ⟨b, hbU, hbz⟩ := SetLike.not_le_iff_exists.1 hnle
    have hb1 : b ≠ 1 := fun e => hbz (by rw [e]; exact Subgroup.one_mem _)
    have hbb : b * b = 1 := mul_self_eq_one_of_isElemAbelian hUab hbU
    have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [← pow_two] at hbb; exact hbb) hb1
    have hbne : z₀ ≠ b := fun e => hbz (by rw [← e]; exact Subgroup.mem_zpowers z₀)
    obtain ⟨E, hEP, hEab, hE8, hbE⟩ := h b (hUP hbU) hb2
    have hUeq := eq_four hUab hU4 hzU hbU hz1 hb1 hbne
    by_cases hzE : z₀ ∈ E
    · exact ⟨E, hEP, hEab, hE8, by rw [hUeq]; exact four_le hzE hbE⟩
    · have hcE : ∀ v ∈ E, Commute v z₀ := fun v hv => hzc v (hEP hv)
      obtain ⟨hab, hcard⟩ := isElemAbelian_sup_zpowers hEab hz2 hzE hcE
      refine ⟨E ⊔ zpowers z₀, sup_le hEP (Subgroup.zpowers_le.2 hzP), hab, ?_, ?_⟩
      · rw [hcard]
        omega
      · rw [hUeq]
        exact four_le (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀))
          (Subgroup.mem_sup_left hbE)
  · obtain ⟨hab, hcard⟩ := isElemAbelian_sup_zpowers hUab hz2 hzU hcomm
    exact ⟨U ⊔ zpowers z₀, sup_le hUP (Subgroup.zpowers_le.2 hzP), hab, by omega,
      le_sup_left⟩

private theorem theta_le_W1V_of_invol (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V P : Subgroup X}
    (hT : TwoCompData X n z A₁ A₂ V) (hzV : z ∈ V) (hP : IsSylowTwoIn A₁ P)
    (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P) {E : Subgroup X}
    (hE : AhatData.RankThreeVertex P E) {b : X} (hbP : b ∈ P) (hb2 : orderOf b = 2) :
    theta V b ≤ W1V V E := by
  have hzP := z_mem_sylow h hT.hA₁ hzV hP hPV
  obtain ⟨E', hE', hbE'⟩ := exists_vertex_mem_of_invol h hzV hPV hzP hR hE hbP hb2
  have hb1 : b ≠ 1 := fun e => by
    rw [e, orderOf_one] at hb2
    omega
  rw [← W1V_eq_of_vertices h hT hP hPV hE' hE]
  exact theta_le_W1V hbE' hb1

theorem W1V_props (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V P : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hV : Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (hVA : V ≤ A₂) (hzV : z ∈ V)
    (hP : IsSylowTwoIn A₁ P) (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P)
    (U : FourSub P) :
    Odd (Nat.card (W1V V U.1)) ∧
      ∀ b ∈ P, orderOf b = 2 → theta V b ≤ W1V V U.1 := by
  have hT : TwoCompData X n z A₁ A₂ V := ⟨hA₁, hA₂, h12, hV, hV4, hVA⟩
  obtain ⟨E, hEP, hEab, hE8, hUE⟩ := hR U.1 U.2.1 U.2.2.1 U.2.2.2
  have hE : AhatData.RankThreeVertex P E := ⟨hEP, hEab, hE8⟩
  have hEU : W1V V U.1 = W1V V E :=
    W1V_eq_of_le h hT hEab hE8 (hEP.trans hP.1) (hEP.trans hPV) hUE U.2.2.2
  refine ⟨?_, fun b hb hb2 => ?_⟩
  · rw [hEU]
    exact (thetaV_complete h hA₁ hA₂ h12 hV hV4 hVA hEab hE8 (hEP.trans hP.1)
      (hEP.trans hPV)).1
  · rw [hEU]
    exact theta_le_W1V_of_invol h hT hzV hP hPV hR hE hb hb2

private theorem V_le_normalizer_A₁ {A₁ A₂ V : Subgroup X} (hT : TwoCompData X n z A₁ A₂ V) :
    V ≤ normalizer (A₁ : Set X) := fun v hv =>
  Sec5Two.K0_le_normalizer_comp hT.hA₁ (Sec5Two.comp_le_K0 hT.hA₂ (hT.hVA hv))

private theorem le_normalizer_W1V_of_vertex (h : Sec5Data X n z (zpowers z) S)
    {A₁ A₂ V P : Subgroup X} (hT : TwoCompData X n z A₁ A₂ V) (hP : IsSylowTwoIn A₁ P)
    (hPV : P ≤ centralizer (V : Set X)) {E Y : Subgroup X}
    (hE : AhatData.RankThreeVertex P E) (hEY : E ≤ normalizer (Y : Set X))
    (hodd : Odd (Nat.card Y)) (hYV : Y ≤ centralizer (V : Set X)) :
    Y ≤ normalizer ((W1V V E : Subgroup X) : Set X) := by
  have hE8 := hE.2.2
  have hgen := le_iSup_inf_centralizer_of_hyperplane hE.2.1 (by omega) hEY hodd
  refine hgen.trans (iSup_le fun B => iSup_le fun hBE => iSup_le fun hBcard => ?_)
  intro x hx
  have hBab : Open.IsElemAbelian 2 B := CoreAux.isElemAbelian_mono hBE hE.2.1
  have hB4 : 4 ≤ Nat.card B := by omega
  obtain ⟨H₀, hH₀B, -, hH₀4⟩ := exists_fourSub_of_le_card hBab hB4
  have hxH : x ∈ normalizer (H₀ : Set X) :=
    centralizer_le_normalizer _ ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hH₀B)) hx.2)
  have hW : W1V V H₀ = W1V V E :=
    W1V_eq_of_le h hT hE.2.1 hE.2.2 (hE.1.trans hP.1) (hE.1.trans hPV) (hH₀B.trans hBE) hH₀4
  rw [← hW]
  exact mem_normalizer_W1V (hYV hx.1) hxH

private theorem oddCoreOf_cen_le_normalizer (h : Sec5Data X n z (zpowers z) S)
    {A₁ A₂ V P : Subgroup X} (hT : TwoCompData X n z A₁ A₂ V) (hzV : z ∈ V)
    (hP : IsSylowTwoIn A₁ P) (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P)
    {E : Subgroup X} (hE : AhatData.RankThreeVertex P E) {b : X} (hbP : b ∈ P)
    (hb2 : orderOf b = 2) :
    oddCoreOf (centralizer ({b} : Set X)) ≤ normalizer ((W1V V E : Subgroup X) : Set X) := by
  have hzP := z_mem_sylow h hT.hA₁ hzV hP hPV
  obtain ⟨Eb, hEb, hbEb⟩ := exists_vertex_mem_of_invol h hzV hPV hzP hR hE hbP hb2
  rw [← W1V_eq_of_vertices h hT hP hPV hEb hE]
  have hVb : V ≤ centralizer ({b} : Set X) := fun v hv =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hPV hbP) v hv)
  have hVJ : V ≤ normalizer ((oddCoreOf (centralizer ({b} : Set X)) : Subgroup X) : Set X) :=
    fun v hv => le_normalizer_oddCoreOf (cen b) (hVb hv)
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := (CoreAux.isElemAbelian_iff.mp hT.hV).2
  have hfact := coprime_normalized_commutator_factorization 2 Nat.prime_two V
    (oddCoreOf (centralizer ({b} : Set X))) (isPGroup_two_of_sq hV2) hVJ
    (Nat.coprime_two_left.mpr (odd_card_oddCoreOf _))
  have hcomm : ⁅oddCoreOf (centralizer ({b} : Set X)), V⁆ ≤
      normalizer ((W1V V Eb : Subgroup X) : Set X) :=
    (le_sup_left : ⁅oddCoreOf (cen b), V⁆ ≤ theta V b).trans
      ((theta_le_W1V_of_invol h hT hzV hP hPV hR hEb hbP hb2).trans Subgroup.le_normalizer)
  have hEbb : Eb ≤ centralizer ({b} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.2 ((CoreAux.isElemAbelian_iff.mp hEb.2.1).1 x hx b hbEb)
  have hEbY : Eb ≤ normalizer ((oddCoreOf (centralizer ({b} : Set X)) ⊓
      centralizer (V : Set X) : Subgroup X) : Set X) := fun x hx =>
    mem_normalizer_inf (le_normalizer_oddCoreOf (cen b) (hEbb hx))
      (Subgroup.le_normalizer ((hEb.1.trans hPV) hx))
  have hYodd : Odd (Nat.card ↥(oddCoreOf (centralizer ({b} : Set X)) ⊓
      centralizer (V : Set X))) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hY := le_normalizer_W1V_of_vertex h hT hP hPV hEb hEbY hYodd inf_le_right
  calc oddCoreOf (centralizer ({b} : Set X))
      = ⁅oddCoreOf (centralizer ({b} : Set X)), V⁆ ⊔
        (oddCoreOf (centralizer ({b} : Set X)) ⊓ centralizer (V : Set X)) := hfact.symm
    _ ≤ _ := sup_le hcomm hY

private theorem oddCoreOf_A₁_le_normalizer (h : Sec5Data X n z (zpowers z) S)
    {A₁ A₂ V P : Subgroup X} (hT : TwoCompData X n z A₁ A₂ V) (hzV : z ∈ V)
    (hP : IsSylowTwoIn A₁ P) (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P)
    {E : Subgroup X} (hE : AhatData.RankThreeVertex P E) :
    oddCoreOf A₁ ≤ normalizer ((W1V V E : Subgroup X) : Set X) := by
  have hzP := z_mem_sylow h hT.hA₁ hzV hP hPV
  have hVN : V ≤ normalizer (A₁ : Set X) := V_le_normalizer_A₁ hT
  have hVJ : V ≤ normalizer ((oddCoreOf A₁ : Subgroup X) : Set X) := fun v hv =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hVN hv)
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := (CoreAux.isElemAbelian_iff.mp hT.hV).2
  have hfact := coprime_normalized_commutator_factorization 2 Nat.prime_two V (oddCoreOf A₁)
    (isPGroup_two_of_sq hV2) hVJ (Nat.coprime_two_left.mpr (odd_card_oddCoreOf _))
  have hJz : oddCoreOf A₁ ≤ oddCoreOf (centralizer ({z} : Set X)) :=
    (le_of_eq (Sec5Two.inf_core_eq hT.hA₁).symm).trans (inf_le_right.trans
      ((Sec5Two.core_K0_eq (n := n) (centralizer ({z} : Set X))).le.trans inf_le_right))
  have hcomm : ⁅oddCoreOf A₁, V⁆ ≤ normalizer ((W1V V E : Subgroup X) : Set X) :=
    ((Subgroup.commutator_mono_left hJz).trans
      (le_sup_left : ⁅oddCoreOf (cen z), V⁆ ≤ theta V z)).trans
      ((theta_le_W1V_of_invol h hT hzV hP hPV hR hE hzP h.orderOf_z).trans Subgroup.le_normalizer)
  have hEJ : E ≤ normalizer ((oddCoreOf A₁ : Subgroup X) : Set X) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hP.1 (hE.1 hx)))
  have hEY : E ≤ normalizer ((oddCoreOf A₁ ⊓ centralizer (V : Set X) : Subgroup X) : Set X) :=
    fun x hx => mem_normalizer_inf (hEJ hx) (Subgroup.le_normalizer ((hE.1.trans hPV) hx))
  have hYodd : Odd (Nat.card ↥(oddCoreOf A₁ ⊓ centralizer (V : Set X))) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hY := le_normalizer_W1V_of_vertex h hT hP hPV hE hEY hYodd inf_le_right
  calc oddCoreOf A₁ = ⁅oddCoreOf A₁, V⁆ ⊔ (oddCoreOf A₁ ⊓ centralizer (V : Set X)) := hfact.symm
    _ ≤ _ := sup_le hcomm hY

private theorem exists_decomp_of_normalizer {A₁ A₂ V P Q : Subgroup X}
    (hT : TwoCompData X n z A₁ A₂ V) (hPV : P ≤ centralizer (V : Set X)) (hQP : Q ≤ P) {g : X}
    (hgA : g ∈ A₁) (hg : g ∈ normalizer (Q : Set X)) :
    ∃ m : X, m ∈ A₁ ∧ m ∈ centralizer (V : Set X) ∧ m ∈ normalizer (Q : Set X) ∧
      ∃ o ∈ oddCoreOf A₁, g = m * o := by
  have hVN : V ≤ normalizer (A₁ : Set X) := V_le_normalizer_A₁ hT
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := (CoreAux.isElemAbelian_iff.mp hT.hV).2
  have hVQ : V ≤ normalizer (Q : Set X) := fun v hv => by
    refine centralizer_le_normalizer Q ?_
    rw [mem_centralizer_iff]
    intro q hq
    exact (mem_centralizer_iff.1 (hPV (hQP hq)) v hv).symm
  have hVR : V ≤ normalizer ((oddCoreOf A₁ ⊓ normalizer (Q : Set X) : Subgroup X) : Set X) :=
    fun v hv => mem_normalizer_inf (mem_normalizer_oddCoreOf_of_mem_normalizer (hVN hv))
      (Subgroup.le_normalizer (hVQ hv))
  have hRodd : Odd (Nat.card ↥(oddCoreOf A₁ ⊓ normalizer (Q : Set X))) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hy : ∀ v ∈ V, g⁻¹ * (v * g * v⁻¹) ∈ oddCoreOf A₁ ⊓ normalizer (Q : Set X) := by
    intro v hv
    have hvA : v * g * v⁻¹ ∈ A₁ := (Subgroup.mem_normalizer_iff.1 (hVN hv) g).1 hgA
    have hcg : ⁅g⁻¹, v⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
      Sec5Two.comm_mem_of_ne hT.hA₁ hT.hA₂ hT.h12 g⁻¹ (A₁.inv_mem hgA) v (hT.hVA hv)
    have e : g⁻¹ * (v * g * v⁻¹) = ⁅g⁻¹, v⁆ := by simp only [commutatorElement_def]; group
    refine ⟨?_, ?_⟩
    · have hmem : ⁅g⁻¹, v⁆ ∈ A₁ ⊓ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
        ⟨by rw [← e]; exact A₁.mul_mem (A₁.inv_mem hgA) hvA, hcg⟩
      rw [Sec5Two.inf_core_eq hT.hA₁] at hmem
      rw [e]
      exact hmem
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hVQ hv) hg) (Subgroup.inv_mem _ (hVQ hv)))
  obtain ⟨p, hp, hgp⟩ := exists_fixed_mem_coset_of_isPGroup hRodd (isPGroup_two_of_sq hV2) hVR hy
  exact ⟨g * p, A₁.mul_mem hgA (oddCoreOf_le A₁ hp.1), hgp, Subgroup.mul_mem _ hg hp.2, p⁻¹,
    (oddCoreOf A₁).inv_mem hp.1, by group⟩

private theorem isElemAbelian_subgroupOf {K U : Subgroup X} (hU : Open.IsElemAbelian 2 U) :
    Open.IsElemAbelian 2 (U.subgroupOf K) := by
  rw [CoreAux.isElemAbelian_iff] at hU ⊢
  refine ⟨fun x hx y hy => Subtype.ext (hU.1 x hx y hy), fun x hx => Subtype.ext (hU.2 x hx)⟩

private theorem mem_normalizer_of_mem_gamma (h : Sec5Data X n z (zpowers z) S)
    {A₁ A₂ V P : Subgroup X} (hT : TwoCompData X n z A₁ A₂ V) (hzV : z ∈ V)
    (hP : IsSylowTwoIn A₁ P) (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P)
    {E : Subgroup X} (hE : AhatData.RankThreeVertex P E) :
    ∀ β ∈ Open.properTwoGenCoreGamma (P.subgroupOf A₁) 2,
      ((β : ↥A₁) : X) ∈ normalizer ((W1V V E : Subgroup X) : Set X) := by
  have hΓ : Open.properTwoGenCoreGamma (P.subgroupOf A₁) 2 ≤
      (normalizer ((W1V V E : Subgroup X) : Set X)).comap A₁.subtype := by
    rw [CFSG.ProperTwoGeneratedCore.gamma_le_iff]
    intro Q hQP hQ g hg
    obtain ⟨U₁, hU₁Q, hU₁ab, hU₁4⟩ := CoreAux.exists_fourSub_of_two_le_pRank hQ
    have hQXP : Q.map A₁.subtype ≤ P := by
      refine (Subgroup.map_mono hQP).trans ?_
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    have hgQ : (g : X) ∈ normalizer ((Q.map A₁.subtype : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g * q * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg q).1 hq, rfl⟩
      · rintro ⟨q, hq, hqx⟩
        refine ⟨g⁻¹ * q * g, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) q).1 hq
          simpa using this
        · change (g : X)⁻¹ * (q : X) * (g : X) = x
          have h3 : (q : X) = (g : X) * x * (g : X)⁻¹ := hqx
          rw [h3]
          group
    let H₁ : FourSub P := ⟨U₁.map A₁.subtype, (Subgroup.map_mono hU₁Q).trans hQXP,
      CFSG.SectionRank.isElemAbelian_map hU₁ab _, by
        rw [Subgroup.card_map_of_injective A₁.subtype_injective, hU₁4]⟩
    obtain ⟨m, hmA, hmC, hmQ, o, hoO, hgmo⟩ :=
      exists_decomp_of_normalizer hT hPV hQXP g.2 hgQ
    obtain ⟨hc1, hc2, hc3⟩ := CoreAux.fourSub_conj (Subgroup.map_mono hU₁Q) H₁.2.2.1 H₁.2.2.2 hmQ
    let H₂ : FourSub P := ⟨H₁.1.map (MulAut.conj m).toMonoidHom, hc1.trans hQXP, hc2, hc3⟩
    have hW₁ := W1V_eq_of_fourSub_vertex h hT hP hPV hR hE H₁
    have hW₂ := W1V_eq_of_fourSub_vertex h hT hP hPV hR hE H₂
    have hmW : m ∈ normalizer ((W1V V E : Subgroup X) : Set X) := by
      apply mem_normalizer_of_map_conj_eq
      calc (W1V V E).map (MulAut.conj m).toMonoidHom
          = (W1V V H₁.1).map (MulAut.conj m).toMonoidHom := by rw [hW₁]
        _ = W1V V (H₁.1.map (MulAut.conj m).toMonoidHom) := W1V_map_conj hmC _
        _ = W1V V E := hW₂
    have hoW := oddCoreOf_A₁_le_normalizer h hT hzV hP hPV hR hE hoO
    show (g : X) ∈ normalizer ((W1V V E : Subgroup X) : Set X)
    rw [hgmo]
    exact Subgroup.mul_mem _ hmW hoW
  exact fun β hβ => hΓ hβ

private theorem exists_conj_mem_sylow {A₁ P : Subgroup X} (hP : IsSylowTwoIn A₁ P)
    {Γ : Subgroup ↥A₁} (hPΓ : P.subgroupOf A₁ ≤ Γ) {b : X} (hb : b ∈ Γ.map A₁.subtype)
    (hb2 : orderOf b = 2) : ∃ y ∈ Γ.map A₁.subtype, y⁻¹ * b * y ∈ P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWA : Γ.map A₁.subtype ≤ A₁ := Subgroup.map_subtype_le Γ
  have hPW : P ≤ Γ.map A₁.subtype := fun p hp => ⟨⟨p, hP.1 hp⟩, hPΓ hp, rfl⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 P (Γ.map A₁.subtype) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPW, hP.2.1, fun hdvd => hP.2.2 ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P (Γ.map A₁.subtype) A₁ hPW hWA]
    exact hdvd.mul_right _
  set W : Subgroup X := Γ.map A₁.subtype with hW
  let bW : ↥W := ⟨b, hb⟩
  have hbW2 : orderOf bW = 2 := (Subgroup.orderOf_mk b hb).trans hb2
  have hzp : IsPGroup 2 (Subgroup.zpowers bW) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbW2]; norm_num)
  obtain ⟨Qs, hQs⟩ := hzp.exists_le_sylow
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 ((Qs : Subgroup ↥W).map W.subtype) W := ⟨Qs, rfl⟩
  obtain ⟨k, hkW, hk⟩ := hS.exists_mem_conj hQ
  have hbQ : b ∈ (Qs : Subgroup ↥W).map W.subtype :=
    ⟨bW, hQs (Subgroup.mem_zpowers bW), rfl⟩
  exact ⟨k, hkW, (hk b).1 hbQ⟩

theorem oddCore_le_normalizer_W1V (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V P : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hV : Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (hVA : V ≤ A₂) (hzV : z ∈ V)
    (hP : IsSylowTwoIn A₁ P) (hPV : P ≤ centralizer (V : Set X)) (hR : FourInE8 P)
    (U : FourSub P) {b : X}
    (hb : b ∈ (Open.properTwoGenCoreGamma (P.subgroupOf A₁) 2).map A₁.subtype)
    (hb2 : orderOf b = 2) :
    oddCoreOf (centralizer ({b} : Set X)) ≤ normalizer ((W1V V U.1 : Subgroup X) : Set X) := by
  have hT : TwoCompData X n z A₁ A₂ V := ⟨hA₁, hA₂, h12, hV, hV4, hVA⟩
  obtain ⟨E, hEP, hEab, hE8, hUE⟩ := hR U.1 U.2.1 U.2.2.1 U.2.2.2
  have hE : AhatData.RankThreeVertex P E := ⟨hEP, hEab, hE8⟩
  have hUE' : W1V V U.1 = W1V V E :=
    W1V_eq_of_le h hT hEab hE8 (hEP.trans hP.1) (hEP.trans hPV) hUE U.2.2.2
  rw [hUE']
  have hPΓ : P.subgroupOf A₁ ≤ Open.properTwoGenCoreGamma (P.subgroupOf A₁) 2 := by
    have hrank : 2 ≤ Open.pRank 2 (P.subgroupOf A₁) := by
      refine CFSG.ComponentClassification.HarrisLit.T1.S74.L38.le_pRank_of_le
        (E := U.1.subgroupOf A₁) (Subgroup.comap_mono U.2.1) (isElemAbelian_subgroupOf U.2.2.1)
        (k := 2) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U.2.1.trans hP.1)).toEquiv, U.2.2.2]
      norm_num
    exact Subgroup.le_normalizer.trans (AhatData.normalizer_le_gamma le_rfl hrank)
  obtain ⟨y, hyΓ, hyP⟩ := exists_conj_mem_sylow hP hPΓ hb hb2
  have hyW : y ∈ normalizer ((W1V V E : Subgroup X) : Set X) := by
    obtain ⟨β, hβ, rfl⟩ := hyΓ
    exact mem_normalizer_of_mem_gamma h hT hzV hP hPV hR hE β hβ
  have hp2 : orderOf (y⁻¹ * b * y) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y⁻¹) b
    simpa [MulAut.conj_apply, hb2] using this
  have hOp := oddCoreOf_cen_le_normalizer h hT hzV hP hPV hR hE hyP hp2
  intro x hx
  have hx' : y⁻¹ * x * y ∈ oddCoreOf (centralizer ({y⁻¹ * b * y} : Set X)) := by
    have h1 := CoreAux.oddCoreOf_map_equiv (MulAut.conj y⁻¹) (cen b)
    have h2 := CoreAux.cen_conj y⁻¹ b
    have h3 : y⁻¹ * x * y⁻¹⁻¹ ∈ oddCoreOf (cen (y⁻¹ * b * y⁻¹⁻¹)) := by
      rw [h2, h1]
      exact Subgroup.mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom hx
    simpa using h3
  have hxy : y⁻¹ * x * y ∈ normalizer ((W1V V E : Subgroup X) : Set X) := hOp hx'
  have e : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyW hxy) (Subgroup.inv_mem _ hyW)

end SW7

end CFSG.OddStandard.Solomon75
