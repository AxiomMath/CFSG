module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XCaseIIbLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup CFSG.LocalCores

variable {V : Type*} [Group V] {X : Type} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

theorem exists_fixed_of_fixed_center_quotient {K : Type*} [Group K] [Finite K]
    (σ : MulAut K) (hσ : σ * σ = 1) (hZ : Odd (Nat.card (center K))) {k : K}
    (hk : (σ k : K ⧸ center K) = (k : K ⧸ center K)) :
    ∃ k' : K, (k' : K ⧸ center K) = (k : K ⧸ center K) ∧ σ k' = k' := by
  set u := σ k / k with hu_def
  have hu : u ∈ center K := by
    rw [hu_def]
    exact QuotientGroup.eq_iff_div_mem.mp hk
  have hσk : σ k = u * k := by rw [hu_def, div_eq_mul_inv]; group
  have hσu : σ u = u⁻¹ := by
    have h2 : σ (σ k) = k := by
      have h := congrArg (fun f : MulAut K => f k) hσ
      simpa [MulAut.mul_apply] using h
    rw [hσk, map_mul, hσk] at h2
    have h3 : (σ u * u) * k = 1 * k := by
      rw [one_mul]
      simpa [mul_assoc] using h2
    have h4 : σ u * u = 1 := mul_right_cancel h3
    calc σ u = ((σ u)⁻¹)⁻¹ := (inv_inv _).symm
      _ = u⁻¹ := by rw [inv_eq_of_mul_eq_one_right h4]
  obtain ⟨m, hm⟩ := hZ
  have hun : u ^ (2 * m + 1) = 1 := by
    have h := pow_card_eq_one' (x := (⟨u, hu⟩ : center K))
    rw [hm] at h
    simpa using h
  set w := u ^ (m + 1) with hw_def
  have hw : w ∈ center K := by rw [hw_def]; exact Subgroup.pow_mem _ hu _
  have hw2 : w * w = u := by
    rw [hw_def, ← pow_add]
    rw [show m + 1 + (m + 1) = 2 * m + 1 + 1 by omega, pow_succ, hun, one_mul]
  have hσw : σ w = w⁻¹ := by
    rw [hw_def, map_pow, hσu, inv_pow]
  refine ⟨k * w, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff w).mpr hw, mul_one]
  · calc σ (k * w) = σ k * σ w := map_mul σ k w
      _ = (u * k) * w⁻¹ := by rw [hσk, hσw]
      _ = k * (u * w⁻¹) := by
            rw [show u * k = k * u from (Subgroup.mem_center_iff.mp hu k).symm]
            group
      _ = k * w := by rw [← hw2]; group

theorem normal_of_simple_of_index_le_four {C : Type*} [Group C] [Finite C] {H : Subgroup C}
    (hH : IsSimpleGroup ↥H) (hindex : H.index ≤ 4) (hcard : 24 < Nat.card ↥H) :
    H.Normal := by
  haveI := hH
  have hdvd : H.normalCore.index ∣ 24 :=
    (Subgroup.index_normalCore_dvd_factorial_index H).trans (Nat.factorial_dvd_factorial hindex)
  have hle : H.normalCore.index ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.normalCore.subgroupOf H) with h | h
  · have hbot : H.normalCore = ⊥ := by
      have hd := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      rwa [inf_eq_left.mpr H.normalCore_le] at hd
    have hcardC : Nat.card C ≤ 24 := by
      rw [← Subgroup.index_bot (G := C), ← hbot]
      exact hle
    have : Nat.card ↥H ≤ 24 := (Subgroup.card_le_card_group (H := H)).trans hcardC
    omega
  · have htop : H.normalCore = H :=
      le_antisymm H.normalCore_le (Subgroup.subgroupOf_eq_top.mp h)
    simpa [htop] using (inferInstance : H.normalCore.Normal)

private noncomputable def conjSubgroupEquiv (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) : ↥K ≃* ↥K :=
  (MulEquiv.subgroupMap (MulAut.conj g) K).trans (MulEquiv.subgroupCongr hg)

private theorem conjSubgroupEquiv_coe (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) (k : ↥K) :
    (conjSubgroupEquiv g K hg k : X) = g * k * g⁻¹ := by
  unfold conjSubgroupEquiv
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
    MulAut.conj_apply]

private theorem conjSubgroupEquiv_symm_coe (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) (k : ↥K) :
    ((conjSubgroupEquiv g K hg).symm k : X) = g⁻¹ * k * g := by
  have h2 := congrArg Subtype.val ((conjSubgroupEquiv g K hg).apply_symm_apply k)
  rw [conjSubgroupEquiv_coe] at h2
  calc ((conjSubgroupEquiv g K hg).symm k : X)
      = g⁻¹ * (g * ((conjSubgroupEquiv g K hg).symm k : X) * g⁻¹) * g := by group
    _ = g⁻¹ * k * g := by rw [h2]

private theorem conjSubgroupEquiv_mul_self (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) (hgg : g * g = 1) :
    conjSubgroupEquiv g K hg * conjSubgroupEquiv g K hg = 1 := by
  ext k
  simp only [MulAut.mul_apply, MulAut.one_apply]
  rw [conjSubgroupEquiv_coe, conjSubgroupEquiv_coe]
  rw [show g * (g * (k : X) * g⁻¹) * g⁻¹ = (g * g) * (k : X) * (g * g)⁻¹ by group]
  rw [hgg]
  group

private noncomputable def quotCenterConj (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) :
    MulAut (↥K ⧸ center ↥K) :=
  QuotientGroup.congr (center ↥K) (center ↥K) (conjSubgroupEquiv g K hg)
    (Subgroup.map_center_eq (conjSubgroupEquiv g K hg))

private theorem quotCenterConj_mk (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) (k : ↥K) :
    quotCenterConj g K hg (k : ↥K ⧸ center ↥K) =
      ((conjSubgroupEquiv g K hg k : ↥K) : ↥K ⧸ center ↥K) := rfl

private theorem quotCenterConj_mul_self (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) (hgg : g * g = 1) :
    quotCenterConj g K hg * quotCenterConj g K hg = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [MulAut.mul_apply, quotCenterConj_mk, quotCenterConj_mk, MulAut.one_apply]
    have h2 : conjSubgroupEquiv g K hg (conjSubgroupEquiv g K hg k) = k := by
      have h := congrArg (fun f : MulAut ↥K => f k) (conjSubgroupEquiv_mul_self g K hg hgg)
      simpa [MulAut.mul_apply] using h
    rw [h2]

private theorem quotCenterConj_ne_one (g : X) (K : Subgroup X)
    (hg : K.map (MulAut.conj g) = K) (hperf : Group.IsPerfect ↥K)
    (hcent : ¬ K ≤ centralizer ({g} : Set X)) :
    quotCenterConj g K hg ≠ 1 := by
  intro hα
  apply hcent
  intro k hk
  have hquot : ∀ x : ↥K,
      ((conjSubgroupEquiv g K hg x : ↥K) : ↥K ⧸ center ↥K) = (x : ↥K ⧸ center ↥K) := by
    intro x
    have := congrArg (fun f : MulAut (↥K ⧸ center ↥K) => f (x : ↥K ⧸ center ↥K)) hα
    simpa [quotCenterConj_mk] using this
  have hδ : ∀ x : ↥K,
      conjSubgroupEquiv g K hg x * ((1 : MulAut ↥K) x)⁻¹ ∈ center ↥K := by
    intro x
    have := QuotientGroup.eq_iff_div_mem.mp (hquot x)
    simpa [div_eq_mul_inv] using this
  have hcz : conjSubgroupEquiv g K hg = 1 :=
    CFSG.GorensteinWalter.perfect_central_automorphism_eq hperf _ _ hδ
  have hfix : conjSubgroupEquiv g K hg ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [hcz]; rfl
  have hgk : g * k * g⁻¹ = k := by
    have := congrArg Subtype.val hfix
    rwa [conjSubgroupEquiv_coe] at this
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc k * g = (g * k * g⁻¹) * g := by rw [hgk]
    _ = g * k := by group

private theorem center_quotient_center_eq_bot {K : Type*} [Group K]
    (hS : IsSimpleGroup (K ⧸ center K))
    (hnonab : ∃ a b : K ⧸ center K, a * b ≠ b * a) :
    center (K ⧸ center K) = ⊥ := by
  haveI := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ center K)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm

private noncomputable def layerProj (G : Type*) [Group G] [Finite G]
    (K : ComponentIndex G) : ↥(layer G) →* K.1 ⧸ center K.1 :=
  (Pi.evalMonoidHom (fun L : ComponentIndex G => L.1 ⧸ center L.1) K).comp
    ((layerCentralQuotientEquiv G).symm.toMonoidHom.comp
      (QuotientGroup.mk' (center (layer G))))

private theorem layerProj_layerMul (G : Type*) [Group G] [Finite G]
    (K : ComponentIndex G) (x : ∀ L : ComponentIndex G, L.1) :
    layerProj G K (layerMulOnto G x) = (x K : K.1 ⧸ center K.1) := by
  have h := layerCentralQuotientEquiv_apply (G := G) x
  simp only [layerProj, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
    QuotientGroup.mk'_apply]
  rw [← h]
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

private theorem conj_layerMul (G : Type*) [Group G] [Finite G]
    (x : ∀ L : ComponentIndex G, L.1) (K : ComponentIndex G) (k : K.1) :
    layerMul G x * (k : G) * (layerMul G x)⁻¹ =
      (x K : G) * (k : G) * (x K : G)⁻¹ := by
  rw [layerMul_eq_mul_update x K]
  have hc : Commute (k : G) (layerMul G (Function.update x K 1)) :=
    commute_layerMul_update x K k.2
  have hck : layerMul G (Function.update x K 1) * (k : G) *
      (layerMul G (Function.update x K 1))⁻¹ = (k : G) := by
    rw [hc.eq.symm]; group
  calc (x K : G) * layerMul G (Function.update x K 1) * (k : G) *
        ((x K : G) * layerMul G (Function.update x K 1))⁻¹
      = (x K : G) * (layerMul G (Function.update x K 1) * (k : G) *
          (layerMul G (Function.update x K 1))⁻¹) * (x K : G)⁻¹ := by group
    _ = (x K : G) * (k : G) * (x K : G)⁻¹ := by rw [hck]

private theorem layerProj_conj [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (y : ↥(layer X)) (k : ↥K) :
    ((conjSubgroupEquiv (y : X) K
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (layer_le_normalizer hK y.2)) k :
        ↥K) : ↥K ⧸ center ↥K) =
      layerProj X ⟨K, hK⟩ y * (k : ↥K ⧸ center ↥K) *
        (layerProj X ⟨K, hK⟩ y)⁻¹ := by
  obtain ⟨x, hx⟩ := exists_layerMul_eq (G := X) y.2
  have hy : y = layerMulOnto X x := (Subtype.ext hx).symm
  rw [hy, layerProj_layerMul]
  have hconj : conjSubgroupEquiv ((layerMulOnto X x : ↥(layer X)) : X) K
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (layer_le_normalizer hK (layerMulOnto X x).2)) k =
      conjSubgroupEquiv (x ⟨K, hK⟩ : X) K
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (layer_le_normalizer hK (component_le_layer hK (x ⟨K, hK⟩).2))) k := by
    apply Subtype.ext
    rw [conjSubgroupEquiv_coe, conjSubgroupEquiv_coe]
    exact conj_layerMul X x ⟨K, hK⟩ k
  rw [hconj]
  have hL : conjSubgroupEquiv (x ⟨K, hK⟩ : X) K
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (layer_le_normalizer hK (component_le_layer hK (x ⟨K, hK⟩).2))) k =
      (x ⟨K, hK⟩ : ↥K) * k * (x ⟨K, hK⟩ : ↥K)⁻¹ := by
    apply Subtype.ext
    rw [conjSubgroupEquiv_coe]
    rfl
  rw [hL]
  rfl

private theorem layerProj_eq_one_centralizes [Finite X] {K : Subgroup X} (hK : IsComponent K)
    {y : ↥(layer X)} (hy : layerProj X ⟨K, hK⟩ y = 1) (k : ↥K) :
    (y : X) * (k : X) * (y : X)⁻¹ = (k : X) := by
  have hg : K.map (MulAut.conj (y : X)) = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (layer_le_normalizer hK y.2)
  have hquot : ∀ x : ↥K, ((conjSubgroupEquiv (y : X) K hg x : ↥K) :
      ↥K ⧸ center ↥K) = (x : ↥K ⧸ center ↥K) := by
    intro x
    have h1 := layerProj_conj hK y x
    rw [hy] at h1
    rw [one_mul, inv_one, mul_one] at h1
    exact h1
  have hδ : ∀ x : ↥K,
      conjSubgroupEquiv (y : X) K hg x * ((1 : MulAut ↥K) x)⁻¹ ∈ center ↥K := by
    intro x
    have := QuotientGroup.eq_iff_div_mem.mp (hquot x)
    simpa [div_eq_mul_inv] using this
  have hcz : conjSubgroupEquiv (y : X) K hg = 1 :=
    CFSG.GorensteinWalter.perfect_central_automorphism_eq hK.1.1 _ _ hδ
  have hfix : conjSubgroupEquiv (y : X) K hg k = k := by rw [hcz]; rfl
  have := congrArg Subtype.val hfix
  rwa [conjSubgroupEquiv_coe] at this

private theorem odd_card_center_of_component [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (hZ : Odd (Nat.card (center (layer X)))) : Odd (Nat.card (center ↥K)) := by
  have hle := center_component_le_center_layer hK
  have h1 : Nat.card ((center ↥K).map K.subtype) ∣
      Nat.card ((center (layer X)).map (layer X).subtype) := by
    have hmul := Subgroup.card_mul_index
      (H := ((center ↥K).map K.subtype).subgroupOf ((center (layer X)).map (layer X).subtype))
    have hcard : Nat.card (((center ↥K).map K.subtype).subgroupOf
        ((center (layer X)).map (layer X).subtype)) =
        Nat.card ((center ↥K).map K.subtype) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    exact ⟨_, by rw [← hmul, hcard]⟩
  rw [Subgroup.card_map_of_injective (f := K.subtype) K.subtype_injective,
    Subgroup.card_map_of_injective (f := (layer X).subtype) (layer X).subtype_injective] at h1
  exact hZ.of_dvd_nat h1

private theorem card_fixed_le_centralizer [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z) = K) (hZ : Odd (Nat.card (center ↥K))) (hz2 : z * z = 1) :
    Nat.card ↥(TauCeti.fixedSubgroup (quotCenterConj z K hKz).toMonoidHom) ≤
      Nat.card ↥(K ⊓ centralizer ({z} : Set X)) := by
  let α := quotCenterConj z K hKz
  let ψ : ↥(K ⊓ centralizer ({z} : Set X)) → ↥(TauCeti.fixedSubgroup α.toMonoidHom) := fun k =>
    ⟨((⟨k.1, k.2.1⟩ : ↥K) : ↥K ⧸ center ↥K), by
      show α (((⟨k.1, k.2.1⟩ : ↥K)) : ↥K ⧸ center ↥K) = ((⟨k.1, k.2.1⟩ : ↥K) : ↥K ⧸ center ↥K)
      rw [quotCenterConj_mk]
      have hczk : conjSubgroupEquiv z K hKz (⟨k.1, k.2.1⟩ : ↥K) = ⟨k.1, k.2.1⟩ := by
        apply Subtype.ext
        rw [conjSubgroupEquiv_coe]
        have hkz : ((⟨k.1, k.2.1⟩ : ↥K) : X) * z = z * ((⟨k.1, k.2.1⟩ : ↥K) : X) :=
          Subgroup.mem_centralizer_singleton_iff.mp k.2.2
        calc z * ((⟨k.1, k.2.1⟩ : ↥K) : X) * z⁻¹ =
              ((⟨k.1, k.2.1⟩ : ↥K) : X) * z * z⁻¹ := by rw [hkz]
          _ = ((⟨k.1, k.2.1⟩ : ↥K) : X) := by group
      rw [hczk]⟩
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (center ↥K) (y : ↥K ⧸ center ↥K)
    have hyfix : α (k : ↥K ⧸ center ↥K) = (k : ↥K ⧸ center ↥K) := by
      have hk' : ((k : ↥K) : ↥K ⧸ center ↥K) = (y : ↥K ⧸ center ↥K) := by simpa using hk
      rw [hk']
      exact y.2
    have hfix : (conjSubgroupEquiv z K hKz k : ↥K ⧸ center ↥K) = (k : ↥K ⧸ center ↥K) := by
      rwa [quotCenterConj_mk] at hyfix
    obtain ⟨k', hk'coset, hk'fix⟩ :=
      exists_fixed_of_fixed_center_quotient (conjSubgroupEquiv z K hKz)
        (conjSubgroupEquiv_mul_self z K hKz hz2) hZ hfix
    have hk'z : (k' : X) ∈ centralizer ({z} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hval := congrArg Subtype.val hk'fix
      rw [conjSubgroupEquiv_coe] at hval
      calc (k' : X) * z = (z * (k' : X) * z⁻¹) * z := by rw [hval]
        _ = z * (k' : X) := by group
    refine ⟨⟨(k' : X), ⟨k'.2, hk'z⟩⟩, ?_⟩
    apply Subtype.ext
    exact hk'coset.trans hk
  exact Nat.card_le_card_of_surjective ψ hsurj

private theorem quotCenterConj_layerProj [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K) (hKz : K.map (MulAut.conj z) = K)
    (hQE : ⁅Q, Q⁆ ≤ layer X) (g : ↥⁅Q, Q⁆) :
    quotCenterConj z K hKz (layerProj X ⟨K, hK⟩ ⟨(g : X), hQE g.2⟩) =
      layerProj X ⟨K, hK⟩ ⟨(g : X), hQE g.2⟩ := by
  classical
  obtain ⟨x, hx⟩ := exists_layerMul_eq (G := X) (hQE g.2)
  have hπ : layerProj X ⟨K, hK⟩ ⟨(g : X), hQE g.2⟩ = (x ⟨K, hK⟩ : ↥K ⧸ center ↥K) := by
    have hy : (⟨(g : X), hQE g.2⟩ : ↥(layer X)) = layerMulOnto X x := (Subtype.ext hx).symm
    rw [hy, layerProj_layerMul]
  rw [hπ, quotCenterConj_mk]
  have hkey : ∀ k : ↥K, (x ⟨K, hK⟩ : ↥K ⧸ center ↥K) * (k : ↥K ⧸ center ↥K) *
        ((x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹ =
      (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K) * (k : ↥K ⧸ center ↥K) *
        ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K))⁻¹ := by
    intro k
    have hgk : (g : X) * (k : X) * (g : X)⁻¹ ∈ K := by
      have hN : (g : X) ∈ normalizer (K : Set X) := layer_le_normalizer hK (hQE g.2)
      have himg := Subgroup.mem_normalizer_iff_conj_image_eq.mp hN
      have hmem := Set.mem_image_of_mem (MulAut.conj (g : X)) k.2
      rw [himg] at hmem
      simpa [MulAut.conj_apply] using hmem
    have h1 : (x ⟨K, hK⟩ : ↥K ⧸ center ↥K) * (k : ↥K ⧸ center ↥K) *
        ((x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹ =
        ((⟨(g : X) * (k : X) * (g : X)⁻¹, hgk⟩ : ↥K) : ↥K ⧸ center ↥K) := by
      rw [← hπ]
      rw [← layerProj_conj hK ⟨(g : X), hQE g.2⟩ k]
      congr 1
    have h2 : (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K) *
        (k : ↥K ⧸ center ↥K) *
        ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K))⁻¹ =
        ((⟨(g : X) * (k : X) * (g : X)⁻¹, hgk⟩ : ↥K) : ↥K ⧸ center ↥K) := by
      have hcalc : conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) * k *
          (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩))⁻¹ =
          (⟨(g : X) * (k : X) * (g : X)⁻¹, hgk⟩ : ↥K) := by
        apply Subtype.ext
        calc (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : X) * (k : X) *
              (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : X)⁻¹
            = z * ((x ⟨K, hK⟩ : X) * ((conjSubgroupEquiv z K hKz).symm k : X) *
                (x ⟨K, hK⟩ : X)⁻¹) * z⁻¹ := by
                rw [conjSubgroupEquiv_coe, conjSubgroupEquiv_symm_coe]
                group
          _ = z * ((g : X) * ((conjSubgroupEquiv z K hKz).symm k : X) * (g : X)⁻¹) * z⁻¹ := by
                rw [← conj_layerMul X x ⟨K, hK⟩ ((conjSubgroupEquiv z K hKz).symm k), hx]
          _ = (g : X) * (k : X) * (g : X)⁻¹ := by
                rw [conjSubgroupEquiv_symm_coe]
                have hzg : z * (g : X) = (g : X) * z :=
                  (h.mul_comm_of_mem (Subgroup.commutator_le_self Q g.2)).symm
                have hzg' : (g : X)⁻¹ * z⁻¹ = z⁻¹ * (g : X)⁻¹ := by
                  rw [← mul_inv_rev, ← mul_inv_rev, hzg]
                calc z * ((g : X) * (z⁻¹ * (k : X) * z) * (g : X)⁻¹) * z⁻¹
                    = (z * (g : X)) * (z⁻¹ * (k : X) * z) * ((g : X)⁻¹ * z⁻¹) := by group
                  _ = ((g : X) * z) * (z⁻¹ * (k : X) * z) * (z⁻¹ * (g : X)⁻¹) := by
                        rw [hzg, hzg']
                  _ = (g : X) * (k : X) * (g : X)⁻¹ := by group
      rw [← hcalc]
      rfl
    rw [h1, h2]
  have hall : ∀ y : ↥K ⧸ center ↥K,
      (x ⟨K, hK⟩ : ↥K ⧸ center ↥K) * y * ((x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹ =
      (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K) * y *
        ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K))⁻¹ := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center ↥K) y
    exact hkey k
  have hcent : (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
      (x ⟨K, hK⟩ : ↥K ⧸ center ↥K) ∈ center (↥K ⧸ center ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
        (x ⟨K, hK⟩ : ↥K ⧸ center ↥K)) * y *
        ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
          (x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹ = y := by
      calc ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
            (x ⟨K, hK⟩ : ↥K ⧸ center ↥K)) * y *
            ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
              (x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹
          = (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
            ((x ⟨K, hK⟩ : ↥K ⧸ center ↥K) * y *
              ((x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹) *
            (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K) := by group
        _ = (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
            ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K) * y *
              ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K))⁻¹) *
            (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K) := by rw [hall y]
        _ = y := by group
    calc y * ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
          (x ⟨K, hK⟩ : ↥K ⧸ center ↥K))
        = (((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
            (x ⟨K, hK⟩ : ↥K ⧸ center ↥K)) * y *
            ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
              (x ⟨K, hK⟩ : ↥K ⧸ center ↥K))⁻¹) *
            ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
              (x ⟨K, hK⟩ : ↥K ⧸ center ↥K)) := by rw [hx']
      _ = ((conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
            (x ⟨K, hK⟩ : ↥K ⧸ center ↥K)) * y := by group
  have hzF : center (↥K ⧸ center ↥K) = ⊥ :=
    center_quotient_center_eq_bot hK.1.2.1 hK.1.2.2
  rw [hzF] at hcent
  have h1 : (conjSubgroupEquiv z K hKz (x ⟨K, hK⟩) : ↥K ⧸ center ↥K)⁻¹ *
      (x ⟨K, hK⟩ : ↥K ⧸ center ↥K) = 1 := Subgroup.mem_bot.mp hcent
  rw [inv_mul_eq_one] at h1
  exact h1

theorem XHyp.false_of_forall_isComponent [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hX : zpowers z ⊔ Q ≠ ⊤) (hKD : KDM22) (hKg : KCore.KGroupNonab CFSG.Blueprint.Catalog X)
    (hE : layer X ≠ ⊥)
    (hmap : ∀ K : Subgroup X, IsComponent K → K.map (MulAut.conj z).toMonoidHom = K)
    (hnc : ∀ K : Subgroup X, IsComponent K → ¬ K ≤ centralizer ({z} : Set X)) : False := by
  classical
  haveI : IsSimpleGroup ↥⁅Q, Q⁆ := h.isSimpleGroup_commutator
  have hQE : ⁅Q, Q⁆ ≤ layer X := h.commutator_le_layer hE
  have hcomp : ∃ K : Subgroup X, IsComponent K ∧ ⁅K, ⁅Q, Q⁆⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hEcent : layer X ≤ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) := by
      rw [CFSG.layer.eq_sSup]
      exact sSup_le fun K hK => (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (hcon K hK)
    have hQ'cent : ⁅Q, Q⁆ ≤ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) := hQE.trans hEcent
    have hab : IsMulCommutative ↥⁅Q, Q⁆ := by
      rw [← Subgroup.commutator_self_eq_bot_iff]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hQ'cent
    letI : CommGroup ↥⁅Q, Q⁆ :=
      { (inferInstance : Group ↥⁅Q, Q⁆) with mul_comm := fun a b => hab.is_comm.comm a b }
    have hp : (Nat.card ↥⁅Q, Q⁆).Prime := IsSimpleGroup.prime_card
    rw [h.card_commutator] at hp
    norm_num at hp
  obtain ⟨K, hK, hKQ⟩ := hcomp
  haveI : IsSimpleGroup (↥K ⧸ center ↥K) := hK.1.2.1
  have hKz : K.map (MulAut.conj z) = K := by
    simpa using hmap K hK
  let Kidx : ComponentIndex X := ⟨K, hK⟩
  let α : MulAut (↥K ⧸ center ↥K) := quotCenterConj z K hKz
  have hα2 : α * α = 1 := quotCenterConj_mul_self z K hKz h.mul_self
  have hαne : α ≠ 1 := quotCenterConj_ne_one z K hKz hK.1.1 (hnc K hK)
  let π : ↥⁅Q, Q⁆ →* (↥K ⧸ center ↥K) := (layerProj X Kidx).comp ((⁅Q, Q⁆).inclusion hQE)
  have hπinj : Function.Injective π := by
    haveI : (π.ker).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
    · rwa [MonoidHom.ker_eq_bot_iff] at hbot
    · exfalso
      apply hKQ
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hπg : π ⟨g, hg⟩ = 1 := by
        have hmem : (⟨g, hg⟩ : ↥⁅Q, Q⁆) ∈ π.ker := by
          rw [htop]; exact Subgroup.mem_top _
        exact MonoidHom.mem_ker.mp hmem
      have hc := layerProj_eq_one_centralizes hK hπg ⟨k, hk⟩
      have hc' : (g : X) * (k : X) * (g : X)⁻¹ = (k : X) := by simpa using hc
      calc k * g = ((g : X) * k * (g : X)⁻¹) * g := by rw [hc']
        _ = g * k := by group
  haveI hHsimple : IsSimpleGroup ↥π.range :=
    (MonoidHom.ofInjective hπinj).symm.isSimpleGroup
  have hHcard : Nat.card ↥π.range = 443520 := by
    rw [← h.card_commutator]
    exact (Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv).symm
  have hZ : Odd (Nat.card (center ↥K)) :=
    odd_card_center_of_component hK (h.odd_card_center_layer hX)
  have hcard_fixed : Nat.card {x : ↥K ⧸ center ↥K // α x = x} ≤ 4 * 443520 := by
    have h1 : Nat.card ↥(TauCeti.fixedSubgroup α.toMonoidHom) ≤
        Nat.card ↥(K ⊓ centralizer ({z} : Set X)) :=
      card_fixed_le_centralizer hK hKz hZ h.mul_self
    have h2 : Nat.card ↥(K ⊓ centralizer ({z} : Set X)) ≤
        Nat.card ↥(centralizer ({z} : Set X)) := Subgroup.card_le_of_le inf_le_right
    have h3 : Nat.card ↥(centralizer ({z} : Set X)) = 2 * 887040 := h.card_centralizer
    calc Nat.card {x : ↥K ⧸ center ↥K // α x = x} =
        Nat.card ↥(TauCeti.fixedSubgroup α.toMonoidHom) := rfl
      _ ≤ Nat.card ↥(K ⊓ centralizer ({z} : Set X)) := h1
      _ ≤ Nat.card ↥(centralizer ({z} : Set X)) := h2
      _ = 2 * 887040 := h3
      _ = 4 * 443520 := by norm_num
  let C : Subgroup (↥K ⧸ center ↥K) := TauCeti.fixedSubgroup α.toMonoidHom
  have hHle : π.range ≤ C := by
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    exact quotCenterConj_layerProj h hK hKz hQE g
  have hHcardC : Nat.card ↥(π.range.subgroupOf C) = 443520 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv]
    exact hHcard
  haveI hHsimpleC : IsSimpleGroup ↥(π.range.subgroupOf C) :=
    (Subgroup.subgroupOfEquivOfLe hHle).isSimpleGroup
  have hindex : (π.range.subgroupOf C).index ≤ 4 := by
    have hmul : Nat.card ↥(π.range.subgroupOf C) * (π.range.subgroupOf C).index =
        Nat.card ↥C := Subgroup.card_mul_index _
    have h1 : Nat.card ↥C ≤ 443520 * 4 := by
      calc Nat.card ↥C ≤ 4 * 443520 := hcard_fixed
        _ = 443520 * 4 := by norm_num
    rw [← hmul, hHcardC] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
  have hnormal : (π.range.subgroupOf C).Normal :=
    normal_of_simple_of_index_le_four hHsimpleC hindex (by rw [hHcardC]; norm_num)
  have hHfix : ∀ k ∈ π.range, α k = k := by
    intro k hk
    obtain ⟨g, rfl⟩ := hk
    exact quotCenterConj_layerProj h hK hKz hQE g
  have hHnorm : ∀ x : ↥K ⧸ center ↥K, α x = x → ∀ k ∈ π.range, x * k * x⁻¹ ∈ π.range := by
    intro x hx k hk
    have hkC : k ∈ C := hHle hk
    have hmem : (⟨k, hkC⟩ : ↥C) ∈ π.range.subgroupOf C := hk
    have hconj := hnormal.conj_mem ⟨k, hkC⟩ hmem ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf] at hconj
    exact hconj
  have hFcat : CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) :=
    KCore.KGroupNonab.catalogue_of_surjective CFSG.SectionRank.catalog_isoInvariant hKg K
      hK.1.2.2 (QuotientGroup.mk' (center ↥K)) (QuotientGroup.mk'_surjective _)
  exact hKD (↥K ⧸ center ↥K) hK.1.2.1 hFcat α hαne hα2 π.range hHfix hHsimple hHcard hHnorm
    hcard_fixed

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
