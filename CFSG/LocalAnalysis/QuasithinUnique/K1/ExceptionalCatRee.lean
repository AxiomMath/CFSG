module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatCommon
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatWeyl
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeSylowCenter
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeFaithful
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog
open scoped commutatorElement

@[expose] def ree4Root (i : ℕ) : Fin F4.tag.rank → ℤ :=
  orbitCertRoot .F4 i

@[expose] def ree4I0 : Fin F4.tag.rank := ⟨0, by decide⟩

@[expose] def ree4I1 : Fin F4.tag.rank := ⟨1, by decide⟩

theorem ree4Root_mem_posUnipotent
    {K : Type} [Field K] {i : ℕ} (hi : 24 ≤ i ∧ i ≤ 47) (c : K) :
    pinnedX F4.tag K (ree4Root i) c ∈ posUnipotent F4.tag K :=
  f4x_mem_posUnipotent hi c

theorem ree_weyl_witnesses
    :
    ∃ WA WB : WeylGroup F4.tag, WA ∈ F4.relWeylRee ∧ WB ∈ F4.relWeylRee ∧
      WA • ree4Root 44 = ree4Root 28 ∧ WA • ree4Root 47 = ree4Root 30 ∧
      WB • ree4Root 44 = ree4Root 36 ∧ WB • ree4Root 47 = ree4Root 39 := by
  refine ⟨(coxeterSystem F4.tag).wordProd
      (reeOrbitWord F4 ree4I0 ++ reeOrbitWord F4 ree4I1 ++ reeOrbitWord F4 ree4I0),
    (coxeterSystem F4.tag).wordProd (reeOrbitWord F4 ree4I1 ++ reeOrbitWord F4 ree4I0),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
    exact mul_mem (mul_mem (reeOrbitWord_mem F4 ree4I0) (reeOrbitWord_mem F4 ree4I1))
      (reeOrbitWord_mem F4 ree4I0)
  · rw [CoxeterSystem.wordProd_append]
    exact mul_mem (reeOrbitWord_mem F4 ree4I1) (reeOrbitWord_mem F4 ree4I0)
  all_goals
    rw [CFSG.LieType.Chevalley.wordProd_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem canonicalRep_conj_pair
    {K : Type} [Field K] [CharP K 2] {w : WeylGroup F4.tag} {i j : ℕ}
    (hi : w • ree4Root 44 = ree4Root i) (hj : w • ree4Root 47 = ree4Root j) (c d : K) :
    canonicalRep (coxeterSystem F4.tag) K w *
        (pinnedX F4.tag K (ree4Root 44) c * pinnedX F4.tag K (ree4Root 47) d) *
        (canonicalRep (coxeterSystem F4.tag) K w)⁻¹ =
      pinnedX F4.tag K (ree4Root i) c * pinnedX F4.tag K (ree4Root j) d := by
  have h44 : IsRoot F4.tag (ree4Root 44) :=
    (f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩).1
  have h47 : IsRoot F4.tag (ree4Root 47) :=
    (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  have e : ∀ n u v : ModGL F4.tag K, n * (u * v) * n⁻¹ = n * u * n⁻¹ * (n * v * n⁻¹) :=
    fun n u v => by group
  rw [e, canonicalRep_conj_charTwo w h44 c, canonicalRep_conj_charTwo w h47 d, hi, hj]

theorem f4_commutator_28_36
    {K : Type} [Field K] [Finite K] [CharP K 2] {x y x' y' : K}
    (h : ⁅pinnedX F4.tag K (ree4Root 28) x * pinnedX F4.tag K (ree4Root 30) y,
      pinnedX F4.tag K (ree4Root 36) x' * pinnedX F4.tag K (ree4Root 39) y'⁆ = 1) :
    x * x' = 0 := by
  have h' : ⁅f4x K 28 x * f4x K 30 y, f4x K 36 x' * f4x K 39 y'⁆ = 1 := h
  have hok : f4RowOK 41 [28, 30] [36, 39] = true := by decide +kernel
  have hE : f4Contribs 41 [28, 30] [36, 39] = [(28, 1, 36, 1)] := by decide +kernel
  have hrow := f4_row hok (fun i => if i = 28 then x else y) (fun p => if p = 36 then x' else y')
    (by simpa using h')
  rw [hE] at hrow
  simpa using hrow

theorem noStronglyClosedElemAbelian_ree
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    NoStronglyClosedElemAbelian (F4.reeGamma K a) := by
  classical
  have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨⟨S, hS⟩, hcenter, -, -⟩ := large_Ree_Sylow_center a ha K hK
  have hQ : IsSylowTwoOf ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
    rw [← hS]
    exact isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  obtain ⟨WA, WB, hWA, hWB, hA44, hA47, hB44, hB47⟩ := ree_weyl_witnesses
  have hnA : (canonicalRep (coxeterSystem F4.tag) K WA : ModGL F4.tag K) ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a hWA).2
  have hnB : (canonicalRep (coxeterSystem F4.tag) K WB : ModGL F4.tag K) ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a hWB).2
  refine noStronglyClosedElemAbelian_of_witnesses _ hQ ?_
  intro z hz hz1 hzc
  have hzP : (z : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := hz
  have hmem : (z : ModGL F4.tag K) ∈ ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) := by
    refine ⟨⟨z, hzP⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    have h := congrArg Subtype.val (hzc ⟨g, (Subgroup.mem_inf.1 g.2).2⟩ g.2)
    exact Subtype.ext h
  obtain ⟨c, hc⟩ := hcenter.subset hmem
  have r44 : ree4Root 44 = largeReeAlpha44 := orbitCertRoot_largeRee.2.2.2.2.2.1
  have r47 : ree4Root 47 = largeReeAlpha47 := orbitCertRoot_largeRee.2.2.2.2.2.2
  have hc' : pinnedX F4.tag K (ree4Root 44) c *
      pinnedX F4.tag K (ree4Root 47) (c ^ (2 * 2 ^ a)) = (z : ModGL F4.tag K) := by
    rw [r44, r47]
    exact hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    have h0 : (0 : K) ^ (2 * 2 ^ a) = 0 := zero_pow (by positivity)
    have h1 : (z : ModGL F4.tag K) = 1 := by
      rw [← hc', h0, pinnedX_zero, pinnedX_zero, mul_one]
    exact h1
  let gA : F4.reeGamma K a := (⟨_, hnA⟩ : F4.reeGamma K a)⁻¹
  let gB : F4.reeGamma K a := (⟨_, hnB⟩ : F4.reeGamma K a)⁻¹
  have eA : ((gA⁻¹ * z * gA : F4.reeGamma K a) : ModGL F4.tag K) =
      pinnedX F4.tag K (ree4Root 28) c * pinnedX F4.tag K (ree4Root 30) (c ^ (2 * 2 ^ a)) := by
    have e : ((gA⁻¹ * z * gA : F4.reeGamma K a) : ModGL F4.tag K) =
        canonicalRep (coxeterSystem F4.tag) K WA * (z : ModGL F4.tag K) *
          (canonicalRep (coxeterSystem F4.tag) K WA)⁻¹ := by
      simp only [gA, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [e, ← hc']
    exact canonicalRep_conj_pair hA44 hA47 c _
  have eB : ((gB⁻¹ * z * gB : F4.reeGamma K a) : ModGL F4.tag K) =
      pinnedX F4.tag K (ree4Root 36) c * pinnedX F4.tag K (ree4Root 39) (c ^ (2 * 2 ^ a)) := by
    have e : ((gB⁻¹ * z * gB : F4.reeGamma K a) : ModGL F4.tag K) =
        canonicalRep (coxeterSystem F4.tag) K WB * (z : ModGL F4.tag K) *
          (canonicalRep (coxeterSystem F4.tag) K WB)⁻¹ := by
      simp only [gB, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [e, ← hc']
    exact canonicalRep_conj_pair hB44 hB47 c _
  have hmA : gA⁻¹ * z * gA ∈ (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := by
    have hΓ := (gA⁻¹ * z * gA).2
    show ((gA⁻¹ * z * gA : F4.reeGamma K a) : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a
    rw [eA] at hΓ ⊢
    exact Subgroup.mem_inf.2
      ⟨mul_mem (ree4Root_mem_posUnipotent (i := 28) ⟨by norm_num, by norm_num⟩ _)
        (ree4Root_mem_posUnipotent (i := 30) ⟨by norm_num, by norm_num⟩ _), hΓ⟩
  have hmB : gB⁻¹ * z * gB ∈ (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := by
    have hΓ := (gB⁻¹ * z * gB).2
    show ((gB⁻¹ * z * gB : F4.reeGamma K a) : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a
    rw [eB] at hΓ ⊢
    exact Subgroup.mem_inf.2
      ⟨mul_mem (ree4Root_mem_posUnipotent (i := 36) ⟨by norm_num, by norm_num⟩ _)
        (ree4Root_mem_posUnipotent (i := 39) ⟨by norm_num, by norm_num⟩ _), hΓ⟩
  refine ⟨gA, gB, hmA, hmB, fun hcomm => ?_⟩
  have h1 : ((gA⁻¹ * z * gA : F4.reeGamma K a) : ModGL F4.tag K) *
      ((gB⁻¹ * z * gB : F4.reeGamma K a) : ModGL F4.tag K) =
      ((gB⁻¹ * z * gB : F4.reeGamma K a) : ModGL F4.tag K) *
        ((gA⁻¹ * z * gA : F4.reeGamma K a) : ModGL F4.tag K) := congrArg Subtype.val hcomm
  rw [eA, eB] at h1
  have h2 : ⁅pinnedX F4.tag K (ree4Root 28) c * pinnedX F4.tag K (ree4Root 30) (c ^ (2 * 2 ^ a)),
      pinnedX F4.tag K (ree4Root 36) c * pinnedX F4.tag K (ree4Root 39) (c ^ (2 * 2 ^ a))⁆ =
      1 := commutatorElement_eq_one_iff_mul_comm.mpr h1
  exact hc0 (mul_self_eq_zero.mp (f4_commutator_28_36 h2))

theorem fix_of_odd_pow {X : Type*} [Group X] {UC : Subgroup X} (hUC : IsPGroup 2 UC)
    {δ : MulAut X} {m : ℕ} (hm : Odd m) (hδm : δ ^ m = 1) {w : X} (hw : w ∈ UC)
    (hconj : ∀ x ∈ UC, δ x = w * x * w⁻¹) : ∀ x ∈ UC, δ x = x := by
  have hpow : ∀ k : ℕ, ∀ x ∈ UC, (δ ^ k) x = w ^ k * x * (w ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hx' : w * x * w⁻¹ ∈ UC := UC.mul_mem (UC.mul_mem hw hx) (UC.inv_mem hw)
      rw [pow_succ, MulAut.mul_apply, hconj x hx, ih _ hx', pow_succ]
      group
  have hcomm : ∀ x ∈ UC, Commute (w ^ m) x := by
    intro x hx
    have h := hpow m x hx
    rw [hδm, MulAut.one_apply] at h
    have h' : x * w ^ m = w ^ m * x := by
      calc x * w ^ m = (w ^ m * x * (w ^ m)⁻¹) * w ^ m := by rw [← h]
        _ = w ^ m * x := by group
    exact h'.symm
  obtain ⟨n, hn⟩ := hUC ⟨w, hw⟩
  have hwn : w ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hord : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hwn
  have hcop : Nat.Coprime m (orderOf w) :=
    Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hm))
  obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
  intro x hx
  rw [hconj x hx]
  have hc : Commute w x := by
    rw [← hm']
    exact (hcomm x hx).pow_left m'
  rw [hc.eq]
  group

section Aut

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem sylowCentralizingAutInner_ree
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SylowCentralizingAutInner (F4.reeGamma K a) := by
  classical
  have := finite_modGL (τ := F4.tag) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, hUV, -, hopp, -⟩ := large_Ree_Sylow_opposition F4 a K w₀ hw₀
  obtain ⟨Φ, -, -, -, hodd⟩ := large_Ree_opposite_Sylow_parameters_faithful a ha K hK
  have hU : IsSylowTwoOf ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
    rw [← hPU]
    exact isSylowTwoOf_top_iff.mpr ⟨PU.isPGroup', PU.not_dvd_index⟩
  have hV : IsSylowTwoOf ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
    rw [← hPV]
    exact isSylowTwoOf_top_iff.mpr ⟨PV.isPGroup', PV.not_dvd_index⟩
  have hUV' : (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) ⊓
      (F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a ⊓ F4.reeFixedNegUnipotent K a :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [hUV, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  refine sylowCentralizingAutInner_of_opposite hU hV hUV' ?_ ?_
  · intro S hS hUS
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hS
    have hcoe : ((hp.toSylow hi : Sylow 2 (F4.reeGamma K a)) : Subgroup (F4.reeGamma K a)) = S :=
      IsPGroup.toSylow_coe hp hi
    obtain ⟨u, hu, hSu⟩ := (hopp (hp.toSylow hi)).1 (by rw [hcoe]; exact hUS)
    exact ⟨u, hu, hcoe ▸ hSu⟩
  · rintro δ hUδ hVδ ⟨w, hwU, hw⟩
    have hδA : δ ∈ largeReeOppAut K a := ⟨hUδ, hVδ⟩
    have hfin : Finite (largeReeOppAut K a) := Nat.finite_of_card_ne_zero (Odd.pos hodd).ne'
    have hpow : (⟨δ, hδA⟩ : largeReeOppAut K a) ^ Nat.card (largeReeOppAut K a) = 1 :=
      pow_card_eq_one'
    have hδm : δ ^ Nat.card (largeReeOppAut K a) = 1 := by
      have h := congrArg Subtype.val hpow
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
    have hfix := fix_of_odd_pow (isSylowTwoOf_top_iff.mp hU).1 hodd hδm hwU hw
    have h1 : ∀ c, ((δ ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ : F4.reeGamma K a) :
        ModGL F4.tag K) = largeReeA1X a c := fun c =>
      congrArg Subtype.val (hfix _ (Subgroup.mem_subgroupOf.2
        (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ (largeReeA1X_mem_U1 hK c))))
    have h2 : ∀ g, largeReeRestrictU2 ha hK ⟨δ, hδA⟩ g = g := by
      intro g
      apply Subtype.ext
      rw [coe_largeReeRestrictU2]
      exact congrArg Subtype.val (hfix ⟨(g : ModGL F4.tag K), U2_le_reeGamma g.2⟩
        (Subgroup.mem_subgroupOf.2 (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ g.2)))
    exact congrArg Subtype.val (eq_one_of_forall_fix ha hK ⟨δ, hδA⟩ h1 h2)

end Aut

theorem centralizes_of_ree
    {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {f : ℕ}
    (hmodel : CFSG.Blueprint.ReeTitsModel (L ⧸ Subgroup.center L) .twistedF4 2 f)
    {w : G} (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨-, -, -, -, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := large_Ree_model_Schreier _ 2 f hmodel
  obtain ⟨-, a, hfa, hmodel'⟩ := hmodel
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have ha : 1 ≤ a := by omega
  exact centralizes_of_mulEquiv h E (noStronglyClosedElemAbelian_ree ha hK')
    (sylowCentralizingAutInner_ree ha hK') hwU hwS

end CFSG.QuasithinUnique.K1
