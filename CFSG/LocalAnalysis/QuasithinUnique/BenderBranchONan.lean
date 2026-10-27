module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchTI
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchLinear

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

namespace BenderBranch

variable {G : Type} [Group G] [Finite G] {T M U : Subgroup G} {z : G}

theorem rho_isIrreducible [Fact (IsElemAbelian 2 U)] (hd : UniqueFusionDatum T M U z) :
    ONan.IsIrreducible (rho hd.normal).range := by
  intro W hW
  let Wsub : Subgroup U :=
    { carrier := {x | Additive.ofMul x ∈ W}
      mul_mem' := fun {a b} ha hb => W.add_mem ha hb
      one_mem' := W.zero_mem
      inv_mem' := fun {a} ha => W.neg_mem ha }
  have hmem : ∀ m : M, ∀ x ∈ Wsub.map U.subtype, (m : G) * x * (m : G)⁻¹ ∈ Wsub.map U.subtype := by
    intro m x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' : Additive.ofMul y ∈ W := hy
    have := hW (rho hd.normal m) ⟨m, rfl⟩ _ hy'
    refine Subgroup.mem_map.mpr ⟨Additive.toMul (rho hd.normal m (Additive.ofMul y)), this, ?_⟩
    simp [coe_toMul_rho]
  have hnorm : M ≤ Subgroup.normalizer ((Wsub.map U.subtype : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hmem ⟨m, hm⟩ x hx, fun hx => ?_⟩
    have := hmem ⟨m⁻¹, M.inv_mem hm⟩ _ hx
    simpa [mul_assoc] using this
  rcases hd.irreducible _ (Subgroup.map_subtype_le Wsub) hnorm with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have h1 : ((Additive.toMul v : U) : G) ∈ Wsub.map U.subtype :=
      Subgroup.mem_map.mpr ⟨Additive.toMul v, by simpa [Wsub] using hv, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    apply Additive.toMul.injective
    exact Subtype.ext (by simpa using h1)
  · right
    rw [Submodule.eq_top_iff']
    intro v
    have h1 : ((Additive.toMul v : U) : G) ∈ Wsub.map U.subtype := by
      rw [htop]; exact (Additive.toMul v : U).2
    obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp h1
    have hyv' : y = Additive.toMul v := Subtype.ext hyv
    have hy' : Additive.ofMul y ∈ W := hy
    rw [hyv'] at hy'
    simpa using hy'

theorem rho_not_isTransitiveNonzero [Fact (IsElemAbelian 2 U)] (hd : UniqueFusionDatum T M U z)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) (huM : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    ¬ ONan.IsTransitiveNonzero (rho hd.normal).range := by
  intro ht
  have hz1 : (Additive.ofMul (⟨z, hd.z_mem⟩ : U)) ≠ 0 := fun h =>
    hd.z_ne_one (congrArg Subtype.val (ofMul_eq_zero.mp h))
  have hu1' : (Additive.ofMul (⟨u, hu⟩ : U)) ≠ 0 := fun h =>
    hu1 (congrArg Subtype.val (ofMul_eq_zero.mp h))
  obtain ⟨x, ⟨m, rfl⟩, hx⟩ := ht _ _ hz1 hu1'
  have hmz : (m : G) * z * (m : G)⁻¹ = u := congrArg (fun v => ((Additive.toMul v : U) : G)) hx
  apply huM
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hz : z = (m : G)⁻¹ * u * m := by rw [← hmz]; group
  have hyz : (m : G)⁻¹ * y * m ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hz]
    calc (m : G)⁻¹ * y * m * ((m : G)⁻¹ * u * m) = (m : G)⁻¹ * (y * u) * m := by group
      _ = (m : G)⁻¹ * (u * y) * m := by rw [hy]
      _ = (m : G)⁻¹ * u * m * ((m : G)⁻¹ * y * m) := by group
  have hM1 := hd.centralizer_le hyz
  have hy' : y = (m : G) * ((m : G)⁻¹ * y * m) * (m : G)⁻¹ := by group
  rw [hy']
  exact M.mul_mem (M.mul_mem m.2 hM1) (M.inv_mem m.2)

def rhoNL [Fact (IsElemAbelian 2 U)] (hM : M ≤ Subgroup.normalizer (U : Set G))
    (L : Subgroup G) : Subgroup (Additive U ≃ₗ[ZMod 2] Additive U) :=
  ((L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G)).subgroupOf M).map (rho hM)

omit [Finite G] in
theorem mem_rhoNL [Fact (IsElemAbelian 2 U)] {hM : M ≤ Subgroup.normalizer (U : Set G)}
    {L : Subgroup G} {r : Additive U ≃ₗ[ZMod 2] Additive U} :
    r ∈ rhoNL hM L ↔ ∃ n : M,
      (n : G) ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) ∧ rho hM n = r := by
  unfold rhoNL
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

omit [Finite G] in
theorem rhoNL_le_range [Fact (IsElemAbelian 2 U)] (hM : M ≤ Subgroup.normalizer (U : Set G))
    (L : Subgroup G) : rhoNL hM L ≤ (rho hM).range :=
  Subgroup.map_le_range _ _

omit [Finite G] in
theorem isTransitiveOnSummand_rhoNL [Fact (IsElemAbelian 2 U)]
    (hM : M ≤ Subgroup.normalizer (U : Set G)) {L : Subgroup G} (hr : PairRecognition M U L) :
    ONan.IsTransitiveOnSummand (rhoNL hM L) (ofSub U L)
      (ofSub U (Subgroup.centralizer (L : Set G))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr' a ha
    obtain ⟨n, hn, rfl⟩ := mem_rhoNL.mp hr'
    rw [mem_ofSub] at ha ⊢
    rw [coe_toMul_rho]
    exact L.mul_mem (L.mul_mem hn.1 ha) (L.inv_mem hn.1)
  · intro r hr' c hc
    obtain ⟨n, hn, rfl⟩ := mem_rhoNL.mp hr'
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coe_toMul_rho]
    have := hr.trivial_on ((n : G)⁻¹)
      ((L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G)).inv_mem hn)
      (Additive.toMul c : U) ⟨(Additive.toMul c : U).2, hc⟩
    simpa using this
  · intro a ha b hb ha0 hb0
    have ha1 : ((Additive.toMul a : U) : G) ≠ 1 := fun h => ha0 (by
      apply Additive.toMul.injective
      exact Subtype.ext h)
    have hb1 : ((Additive.toMul b : U) : G) ≠ 1 := fun h => hb0 (by
      apply Additive.toMul.injective
      exact Subtype.ext h)
    obtain ⟨n, hn, hnab⟩ := hr.transitive ((Additive.toMul a : U) : G)
      ⟨(Additive.toMul a : U).2, ha⟩ ((Additive.toMul b : U) : G) ⟨(Additive.toMul b : U).2, hb⟩
      ha1 hb1
    have hnM : (n : G) ∈ M := hr.le_M hn
    have hn' : (n : G)⁻¹ ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) :=
      (L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G)).inv_mem hn
    refine ⟨rho hM ⟨(n : G)⁻¹, M.inv_mem hnM⟩,
      mem_rhoNL.mpr ⟨⟨(n : G)⁻¹, M.inv_mem hnM⟩, hn', rfl⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coe_toMul_rho]
    simpa using hnab

omit [Finite G] in
theorem isCyclic_rhoNL [Fact (IsElemAbelian 2 U)] (hM : M ≤ Subgroup.normalizer (U : Set G))
    {L : Subgroup G} (hr : PairRecognition M U L) : IsCyclic (rhoNL hM L) := by
  obtain ⟨g, hg, hgen⟩ := hr.cyclic
  have hgM : (g : G) ∈ M := hr.le_M hg
  refine ⟨⟨⟨rho hM ⟨g, hgM⟩, mem_rhoNL.mpr ⟨⟨g, hgM⟩, hg, rfl⟩⟩, ?_⟩⟩
  rintro ⟨r, hrR⟩
  obtain ⟨n, hn, rfl⟩ := mem_rhoNL.mp hrR
  obtain ⟨k, hk⟩ := hgen n hn
  refine ⟨(k : ℤ), ?_⟩
  apply Subtype.ext
  rw [SubgroupClass.coe_zpow, zpow_natCast]
  show (rho hM ⟨g, hgM⟩) ^ k = rho hM n
  rw [← map_pow]
  apply LinearEquiv.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_toMul_rho, coe_toMul_rho]
  have hnM : (n : G) ∈ M := hr.le_M hn
  have hy : (n : G) * (Additive.toMul v : U) * (n : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hM hnM) _).mp (Additive.toMul v : U).2
  have := hk _ hy
  push_cast
  have hx : ((Additive.toMul v : U) : G) =
      (g ^ k)⁻¹ * ((n : G) * (Additive.toMul v : U) * (n : G)⁻¹) * g ^ k := by
    calc ((Additive.toMul v : U) : G)
        = (n : G)⁻¹ * ((n : G) * (Additive.toMul v : U) * (n : G)⁻¹) * n := by group
      _ = _ := this
  calc (g ^ k) * ((Additive.toMul v : U) : G) * (g ^ k)⁻¹
      = (g ^ k) * ((g ^ k)⁻¹ * ((n : G) * (Additive.toMul v : U) * (n : G)⁻¹) * g ^ k) *
          (g ^ k)⁻¹ := by rw [← hx]
    _ = (n : G) * (Additive.toMul v : U) * (n : G)⁻¹ := by group

omit [Finite G] in
theorem rhoNL_free [Fact (IsElemAbelian 2 U)] (hM : M ≤ Subgroup.normalizer (U : Set G))
    {L : Subgroup G} (hr : PairRecognition M U L) :
    ∀ r ∈ rhoNL hM L, ∀ a ∈ ofSub U L, a ≠ 0 → r a = a → r = 1 := by
  intro r hr' a ha ha0 hra
  obtain ⟨n, hn, rfl⟩ := mem_rhoNL.mp hr'
  have ha1 : ((Additive.toMul a : U) : G) ≠ 1 := fun h => ha0 (by
    apply Additive.toMul.injective
    exact Subtype.ext h)
  have h1 : (n : G) * (Additive.toMul a : U) * (n : G)⁻¹ = ((Additive.toMul a : U) : G) :=
    congrArg (fun v => ((Additive.toMul v : U) : G)) hra
  have hn' := (L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G)).inv_mem hn
  have key := hr.free ((n : G)⁻¹) hn' ((Additive.toMul a : U) : G)
    ⟨(Additive.toMul a : U).2, ha⟩ ha1 (by simpa using h1)
  apply LinearEquiv.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_toMul_rho]
  simpa using key ((Additive.toMul v : U) : G) (Additive.toMul v : U).2

theorem isCompl_ofSub [Fact (IsElemAbelian 2 U)] (hd : UniqueFusionDatum T M U z)
    {L : Subgroup G} (hr : PairRecognition M U L) :
    IsCompl (ofSub U L) (ofSub U (Subgroup.centralizer (L : Set G))) := by
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    have h1 : ((Additive.toMul x : U) : G) ∈
        (U ⊓ L) ⊓ (U ⊓ Subgroup.centralizer (L : Set G)) :=
      ⟨⟨(Additive.toMul x : U).2, hx.1⟩, ⟨(Additive.toMul x : U).2, hx.2⟩⟩
    rw [hr.inf_eq, Subgroup.mem_bot] at h1
    exact Additive.toMul.injective (Subtype.ext (by simpa using h1))
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : ((Additive.toMul v : U) : G) ∈
        (U ⊓ L) ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hr.sup_eq]
      exact (Additive.toMul v : U).2
    rw [mem_sup_iff_of_commute (H := U ⊓ L) (K := U ⊓ Subgroup.centralizer (L : Set G))
      (fun a ha c hc => mul_comm_of_mem hd ha.1 hc.1)] at hv
    obtain ⟨a, ha, c, hc, hac⟩ := hv
    have hv' : v = Additive.ofMul (⟨a, ha.1⟩ : U) + Additive.ofMul (⟨c, hc.1⟩ : U) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa using hac.symm
    rw [hv']
    exact Submodule.add_mem_sup (show Additive.ofMul (⟨a, ha.1⟩ : U) ∈ ofSub U L from ha.2)
      (show Additive.ofMul (⟨c, hc.1⟩ : U) ∈ ofSub U (Subgroup.centralizer (L : Set G)) from hc.2)

omit [Finite G] in
theorem natCard_ofSub [Fact (IsElemAbelian 2 U)] (H : Subgroup G) :
    Nat.card ↥(ofSub U H) = Nat.card ↥(U ⊓ H) :=
  Nat.card_congr
    { toFun := fun v => ⟨((Additive.toMul v.1 : U) : G), (Additive.toMul v.1 : U).2, v.2⟩
      invFun := fun x => ⟨Additive.ofMul ⟨x, x.2.1⟩, x.2.2⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

theorem two_le_finrank_ofSub [Fact (IsElemAbelian 2 U)] {L : Subgroup G}
    (hr : PairRecognition M U L) : 2 ≤ Module.finrank (ZMod 2) (ofSub U L) := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ofSub U L)
  rw [natCard_ofSub, Nat.card_zmod] at h1
  have h4 := hr.card_ge
  by_contra hlt
  have hle : Module.finrank (ZMod 2) (ofSub U L) ≤ 1 := by omega
  have : 2 ^ Module.finrank (ZMod 2) (ofSub U L) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
  omega

omit [Finite G] in
theorem ofSub_centralizer_ne_bot [Fact (IsElemAbelian 2 U)] {L : Subgroup G}
    (hCne : U ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ofSub U (Subgroup.centralizer (L : Set G)) ≠ ⊥ := by
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
  rw [Ne, Submodule.eq_bot_iff]
  intro h
  have := h (Additive.ofMul (⟨(c : G), c.2.1⟩ : U)) c.2.2
  exact hc (Subtype.ext (by simpa using congrArg (fun v => ((Additive.toMul v : U) : G)) this))

omit [Finite G] in
theorem ofSub_centralizer_ne_top [Fact (IsElemAbelian 2 U)] {L : Subgroup G}
    (hCU : U ⊓ Subgroup.centralizer (L : Set G) ≠ U) :
    ofSub U (Subgroup.centralizer (L : Set G)) ≠ ⊤ := by
  intro h
  apply hCU
  refine le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩
  have : Additive.ofMul (⟨x, hx⟩ : U) ∈ ofSub U (Subgroup.centralizer (L : Set G)) := by
    rw [h]; trivial
  exact this

theorem isTI_rho [Fact (IsElemAbelian 2 U)] (hd : UniqueFusionDatum T M U z) {L : Subgroup G}
    (hTI : ∀ g ∈ M, (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
        CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g ≠ ⊥ →
      CFSG.conjugate L g = L ∧
        CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g =
          U ⊓ Subgroup.centralizer (L : Set G)) :
    ONan.IsTI (rho hd.normal).range (ofSub U (Subgroup.centralizer (L : Set G))) := by
  rintro x ⟨m, rfl⟩ hne
  have hmap := map_ofSub_rho hd.normal m (Subgroup.centralizer (L : Set G))
  show (ofSub U (Subgroup.centralizer (L : Set G))).map
    (rho hd.normal m : Additive U →ₗ[ZMod 2] Additive U) = _
  rw [hmap]
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hv2 : v ∈ ofSub U (CFSG.conjugate (Subgroup.centralizer (L : Set G)) (m : G)⁻¹) := by
    rw [← hmap]
    exact hv.2
  have hV : (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) (m : G)⁻¹ ≠ ⊥ := by
    intro hbot
    have hc : ((Additive.toMul v : U) : G) ∈ (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
        CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) (m : G)⁻¹ := by
      refine ⟨⟨(Additive.toMul v : U).2, hv.1⟩, ?_⟩
      rw [conjugate_inf, conjugate_U_eq hd (M.inv_mem m.2)]
      exact ⟨(Additive.toMul v : U).2, hv2⟩
    rw [hbot, Subgroup.mem_bot] at hc
    exact hv0 (Additive.toMul.injective (Subtype.ext (by simpa using hc)))
  obtain ⟨hL, -⟩ := hTI ((m : G)⁻¹) (M.inv_mem m.2) hV
  rw [conjugate_centralizer, hL]

theorem rhoNL_normalized [Fact (IsElemAbelian 2 U)] (hd : UniqueFusionDatum T M U z)
    {L : Subgroup G}
    (hnorm : ∀ g ∈ M, g ∈ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (L : Set G) :
      Subgroup G) : Set G) → g ∈ Subgroup.normalizer (L : Set G)) :
    ∀ x ∈ (rho hd.normal).range,
      ONan.image x (ofSub U (Subgroup.centralizer (L : Set G))) =
        ofSub U (Subgroup.centralizer (L : Set G)) →
      ∀ r ∈ rhoNL hd.normal L, x * r * x⁻¹ ∈ rhoNL hd.normal L := by
  rintro x ⟨m, rfl⟩ hx r hr
  have hmap := map_ofSub_rho hd.normal m (Subgroup.centralizer (L : Set G))
  have hx' : (ofSub U (Subgroup.centralizer (L : Set G))).map
      (rho hd.normal m : Additive U →ₗ[ZMod 2] Additive U) =
        ofSub U (Subgroup.centralizer (L : Set G)) := hx
  rw [hmap, ofSub_eq_ofSub_iff] at hx'
  have hconjC : CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) (m : G)⁻¹ =
      U ⊓ Subgroup.centralizer (L : Set G) := by
    rw [conjugate_inf, conjugate_U_eq hd (M.inv_mem m.2)]
    exact hx'
  have hmC : (m : G) ∈ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (L : Set G) :
      Subgroup G) : Set G) := by
    have := conjugate_eq_iff_mem_normalizer.mp hconjC
    simpa using (Subgroup.normalizer _).inv_mem this
  have hmL : (m : G) ∈ Subgroup.normalizer (L : Set G) := hnorm m m.2 hmC
  obtain ⟨n, hn, rfl⟩ := mem_rhoNL.mp hr
  have hnM : (n : G) ∈ M := n.2
  refine mem_rhoNL.mpr ⟨m * n * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have hmU : (m : G) ∈ Subgroup.normalizer (U : Set G) := hd.normal m.2
  have hmUL : (m : G) ∈ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hmU hmL ⊢
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hmU x, hmL x]
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp hmL (n : G)).mp hn.1
    simpa using this
  · have h1 : (m : G) * n * (m : G)⁻¹ ∈ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hmUL hn.2)
        ((Subgroup.normalizer _).inv_mem hmUL)
    simpa using h1



end BenderBranch

theorem UniqueFusionDatum.maximal_component_ONan_hypotheses {G : Type} [Group G] [Finite G]
    (hrec : LocalComponentRecognition) (hemb : ComponentEmbeddingUnderInvolution)
    {T M U : Subgroup G} {z : G} (hd : UniqueFusionDatum T M U z) {u : G} {L : Subgroup G}
    (h : IsMaximalEscapingPair M U u L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (e : U ≃* Multiplicative V) (ρ : M →* (V ≃ₗ[ZMod 2] V))
      (R : Subgroup (V ≃ₗ[ZMod 2] V)) (A C : Submodule (ZMod 2) V),
      (∀ (m : M) (w : U),
        ((e.symm (Multiplicative.ofAdd (ρ m (Multiplicative.toAdd (e w)))) : U) : G) =
          (m : G) * w * (m : G)⁻¹) ∧
      (∀ v : V, v ∈ A ↔ ((e.symm (Multiplicative.ofAdd v) : U) : G) ∈ L) ∧
      (∀ v : V, v ∈ C ↔
        ((e.symm (Multiplicative.ofAdd v) : U) : G) ∈ Subgroup.centralizer (L : Set G)) ∧
      (∀ r : V ≃ₗ[ZMod 2] V, r ∈ R ↔ ∃ n : M,
        (n : G) ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) ∧ ρ n = r) ∧
      R ≤ ρ.range ∧ ONan.IsIrreducible ρ.range ∧ ¬ ONan.IsTransitiveNonzero ρ.range ∧
      IsCompl A C ∧ 2 ≤ Module.finrank (ZMod 2) A ∧ C ≠ ⊥ ∧ C ≠ ⊤ ∧
      ONan.IsTransitiveOnSummand R A C ∧ IsCyclic R ∧
      (∀ r ∈ R, ∀ a ∈ A, a ≠ 0 → r a = a → r = 1) ∧
      ONan.IsTI ρ.range C ∧
      (∀ x ∈ ρ.range, ONan.image x C = C → ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      ((M ⊓ Subgroup.normalizer
          ((U ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)).subgroupOf M).index =
        (ONan.orbit ρ.range C).ncard := by
  have : Fact (IsElemAbelian 2 U) := ⟨hd.elem⟩
  have hM := hd.normal
  have hr := BenderBranch.pairRecognition hrec hd h.1 h.2.1 h.2.2.1 h.2.2.2.1
  obtain ⟨hTI1, hTI2⟩ := hd.maximal_component_centralizer_TI hrec hemb h
  let e : U ≃* Multiplicative (Additive U) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
      invFun := fun v => Additive.toMul (Multiplicative.toAdd v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hnorm : ∀ g ∈ M, g ∈ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (L : Set G) :
      Subgroup G) : Set G) → g ∈ Subgroup.normalizer (L : Set G) := fun g hg hgC => by
    have := SetLike.ext_iff.mp hTI2 g
    exact (Subgroup.mem_inf.mp (this.mp (Subgroup.mem_inf.mpr ⟨hg, hgC⟩))).2
  refine ⟨Additive U, inferInstance, inferInstance, inferInstance, e, BenderBranch.rho hM,
    BenderBranch.rhoNL hM L, BenderBranch.ofSub U L,
    BenderBranch.ofSub U (Subgroup.centralizer (L : Set G)), ?_⟩
  refine ⟨fun m w => BenderBranch.coe_toMul_rho hM m (Additive.ofMul w),
    fun v => BenderBranch.mem_ofSub, fun v => BenderBranch.mem_ofSub,
    fun r => BenderBranch.mem_rhoNL,
    BenderBranch.rhoNL_le_range hM L, BenderBranch.rho_isIrreducible hd,
    BenderBranch.rho_not_isTransitiveNonzero hd h.1 h.2.1 h.2.2.1,
    BenderBranch.isCompl_ofSub hd hr, BenderBranch.two_le_finrank_ofSub hr,
    BenderBranch.ofSub_centralizer_ne_bot (BenderBranch.inf_centralizer_ne_bot h),
    BenderBranch.ofSub_centralizer_ne_top (BenderBranch.inf_centralizer_ne_U hr),
    BenderBranch.isTransitiveOnSummand_rhoNL hM hr, BenderBranch.isCyclic_rhoNL hM hr,
    BenderBranch.rhoNL_free hM hr, BenderBranch.isTI_rho hd hTI1,
    BenderBranch.rhoNL_normalized hd hnorm,
    BenderBranch.index_normalizer_eq_ncard_orbit hM (Subgroup.centralizer (L : Set G))⟩

end CFSG.QuasithinUnique
