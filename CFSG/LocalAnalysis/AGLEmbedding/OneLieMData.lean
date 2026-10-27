module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
import CFSG.LocalAnalysis.AGLEmbedding.TorusIrreducible
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0U3Lift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section MData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_oneLieTorusFacts (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧ OneLieFacts p K T₁ ∧
      ∃ n e : ℕ, OneLieTorusFacts p K T₁ n e := by
  have hp : p.Prime := Fact.out
  obtain ⟨hsimple, hnonab⟩ := hd.isSimpleGroup
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT₁]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  have hcore := hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT₁
  exact ⟨T, hT₁, hK K hsimple hnonab hcat p hp hd.cfg.red.ne_two T hTnc hcore hd.big,
    hT K hsimple hnonab hcat p hd.cfg.red.ne_two T hTnc hcore hd.big⟩

omit [Fact p.Prime] in
theorem D1CompCore.map_d1LiftX_centerOf (hd : D1CompCore p P M H R Rbar K) :
    ((d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      K))).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) := by
  rw [map_d1LiftX, ← hd.rbar]
  exact inf_eq_right.mpr (inf_le_left.trans inf_le_left)

omit [Fact p.Prime] in
theorem D1OneLieData.map_d1LiftX_centerOf (hd : D1OneLieData p P M H R Rbar K) :
    ((d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      K))).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :=
  hd.toCore.map_d1LiftX_centerOf

theorem D1OneLieData.exists_lift_of_ppd (hd : D1OneLieData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) {r : ℕ} [Fact r.Prime]
    {c : K} (hcN : c ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K)) (hcord : orderOf c = r)
    (hcirr : ∀ k : ℕ, ¬ r ∣ k →
      (∃ u ∈ (T₁ : Subgroup K), c ^ k * u * (c ^ k)⁻¹ * u⁻¹ ∉
        (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K)) ∧
      ∀ V : Subgroup K,
        (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K) ≤ V →
        V ≤ T₁ → c ^ k ∈ Subgroup.normalizer (V : Set K) →
        V = (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K) ∨ V = T₁) :
    ∃ t : G, t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (d1LiftX p H R K : Set G) ∧
      IsPGroup r (Subgroup.zpowers t) ∧
      (∀ u ∈ d1LiftX p H R K, t ^ r * u * (t ^ r)⁻¹ = u) ∧
      (∃ u ∈ d1LiftX p H R K, t * u * t⁻¹ * u⁻¹ ∉
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K))) ∧
      ∀ V : Subgroup G,
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ≤
          V → V ≤ d1LiftX p H R K → t ∈ Subgroup.normalizer (V : Set G) →
        V = d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          K)) ∨ V = d1LiftX p H R K := by
  obtain ⟨z₀, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set T : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hTdef
  set U := d1LiftX p H R K with hUdef
  set Z := d1LiftX p H R (centerOf T) with hZdef
  have hUH : U ≤ H := d1LiftX_le_H p H R K
  have hUR : U ≤ R := d1LiftX_le p H R K
  have hUp : IsPGroup p U := hd.cfg.ext.isPGroup.to_le hUR
  have hUmap : (U.subgroupOf H).map π = T := hd.cfg.map_d1LiftX_eq_inf
  have hNHM : GLBPrimeCore p H ≤ H ⊓ M := hd.d1PlusCore_facts.2.2.trans hd.d1PlusCore_facts.1
  have hZX : Z ≤ U := Subgroup.map_mono (inf_le_inf_left _ (Subgroup.comap_mono
    ((inf_le_left : centerOf _ ≤ _).trans inf_le_right)))
  have hZmap : (Z.subgroupOf H).map π = centerOf T := hd.map_d1LiftX_centerOf
  have hZT : centerOf T =
      ((T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K)).map K.subtype := by
    rw [← hT₁]
    exact (map_subtype_centerOf _).symm
  have hT1 : T ≠ ⊥ := fun h => hd.noncyclic (by rw [← hTdef, h]; infer_instance)
  exact exists_lift_of_ppd_of_map hUH hUp hZX hNHM (hUmap.trans hT₁.symm) (hZmap.trans hZT)
    (by rw [hT₁]; exact hN _ le_rfl hT1) hcN hcord hcirr

theorem D1OneLieData.pair_of_torusFacts (hd : D1OneLieData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) {e : ℕ}
    (hTF : OneLieTorusFacts p K T₁ 2 e) {Z : Subgroup G} (hZX : Z ≤ d1LiftX p H R K)
    (hZmap : (Z.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K))
    (hZcard : Nat.card Z = p ^ 2) :
    ∃ U : Subgroup G, Z ≤ U ∧ U ≤ R ∧ ⁅U, U⁆ = Z ∧ Z ≤ Subgroup.centralizer (U : Set G) ∧
      (∀ u ∈ U, u ^ p = 1) ∧ Nat.card U = p ^ 6 ∧
      ∀ r : ℕ, r.Prime → r ∣ p ^ 4 - 1 → (∀ k : ℕ, 0 < k → k < 4 → ¬ r ∣ p ^ k - 1) →
        ∃ t : G, t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (U : Set G) ∧
          IsPGroup r (Subgroup.zpowers t) ∧ (∀ z ∈ Z, t * z * t⁻¹ = z) ∧
          (∀ u ∈ U, t ^ r * u * (t ^ r)⁻¹ = u) ∧ (∃ u ∈ U, t * u * t⁻¹ * u⁻¹ ∉ Z) ∧
          ∀ V : Subgroup G, Z ≤ V → V ≤ U → t ∈ Subgroup.normalizer (V : Set G) →
            V = Z ∨ V = U := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨z₀, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  obtain ⟨hTcard, hTcomm, hTpow, hTppd⟩ := hTF.pair rfl
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set T : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hTdef
  set U := d1LiftX p H R K with hUdef
  have hUH : U ≤ H := d1LiftX_le_H p H R K
  have hUR : U ≤ R := d1LiftX_le p H R K
  have hUp : IsPGroup p U := hd.cfg.ext.isPGroup.to_le hUR
  have hUmap : (U.subgroupOf H).map π = T := hd.cfg.map_d1LiftX_eq_inf
  have hNHM : GLBPrimeCore p H ≤ H ⊓ M := hd.d1PlusCore_facts.2.2.trans hd.d1PlusCore_facts.1
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hUp (glbPrimeCore_coprime p H)
  have hinj : ∀ {A B : Subgroup G}, A ≤ U → B ≤ U →
      (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π → A ≤ B :=
    fun hAU hBU hAB => le_of_map_mk_le_of_isPGroup hUH hUp hAU hBU hAB
  have hZT : centerOf T =
      ((T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K)).map K.subtype := by
    rw [← hT₁]
    exact (map_subtype_centerOf _).symm
  have hCU : ((U ⊓ Subgroup.centralizer (U : Set G)).subgroupOf H).map π = centerOf T := by
    rw [map_inf_centralizer_eq hUH hUp, hUmap]
    rfl
  have hZC : Z = U ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (hinj hZX inf_le_left (by rw [hZmap, hCU]))
      (hinj inf_le_left hZX (by rw [hZmap, hCU]))
  have hcomm : ⁅U, U⁆ = Z := by
    have hmap : ((⁅U, U⁆ : Subgroup G).subgroupOf H).map π = (Z.subgroupOf H).map π := by
      rw [hZmap, hZT, ← hTcomm, Subgroup.map_commutator, hT₁, ← hUmap,
        ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH,
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self U).trans hUH)]
    exact le_antisymm (hinj (Subgroup.commutator_le_self U) hZX hmap.le)
      (hinj hZX (Subgroup.commutator_le_self U) hmap.ge)
  have hcardU : Nat.card U = p ^ 6 := by
    have h1 : Nat.card ((U.subgroupOf H).map π) = Nat.card (U.subgroupOf H) :=
      card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hUp.comap_subtype
    rw [hUmap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv, ← hT₁,
      Subgroup.card_map_of_injective K.subtype_injective, hTcard] at h1
    exact h1.symm
  have hpowU : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    have hπu : π ⟨u, hUH hu⟩ ∈ (U.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
    rw [hUmap, ← hT₁] at hπu
    obtain ⟨v, hv, hvu⟩ := hπu
    have h1 : π ⟨u, hUH hu⟩ ^ p = 1 := by rw [← hvu, ← map_pow, hTpow v hv, map_one]
    have h2 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_pow, h1]
    have h3 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ U ⊓ GLBPrimeCore p H :=
      ⟨by simpa using U.pow_mem hu p, h2⟩
    rw [hUN, Subgroup.mem_bot] at h3
    simpa using h3
  refine ⟨U, hZX, hUR, hcomm, by rw [hZC]; exact inf_le_right, hpowU, hcardU,
    fun r hr hr4 hprim => ?_⟩
  have := Fact.mk hr
  obtain ⟨c, hcN, hcord, hcirr⟩ := hTppd r hr hr4 hprim
  obtain ⟨t, htK, htU, htr, htrU, hnt, hirr⟩ := hd.exists_lift_of_ppd hT₁ hcN hcord hcirr
  have hZ₀X : d1LiftX p H R (centerOf T) ≤ U := Subgroup.map_mono (inf_le_inf_left _
    (Subgroup.comap_mono ((inf_le_left : centerOf _ ≤ _).trans inf_le_right)))
  have hZ₀ : d1LiftX p H R (centerOf T) = Z :=
    le_antisymm (hinj hZ₀X hZX (by rw [hd.map_d1LiftX_centerOf, hZmap]))
      (hinj hZX hZ₀X (by rw [hd.map_d1LiftX_centerOf, hZmap]))
  rw [← hTdef, hZ₀] at hnt hirr
  have htZ : t ∈ Subgroup.normalizer (Z : Set G) := by
    rw [hZC]
    exact mem_normalizer_centerOf htU
  have hrp : r ≠ p := by
    intro hrp
    rw [hrp] at hr4
    have h1 : p ∣ p ^ 4 - (p ^ 4 - 1) := Nat.dvd_sub (dvd_pow_self p (by norm_num)) hr4
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hcZ := mem_centralizer_of_isPGroup_of_card_eq_sq hZcard htZ htr
    (by simpa using hprim 1 (by norm_num) (by norm_num)) (hprim 2 (by norm_num) (by norm_num)) hrp
  exact ⟨t, htK, htU, htr, hcZ, htrU, hnt, hirr⟩

theorem D1OneLieData.exists_torus_lift (hd : D1OneLieData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) {n e : ℕ}
    (hTF : OneLieTorusFacts p K T₁ n e) :
    ∃ φ : Multiplicative (GaloisField p n) ≃*
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)),
      ∀ μ : (GaloisField p n)ˣ, ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p n),
        t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ e * Multiplicative.toAdd a)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set Z := d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
    K)) with hZ
  have hZH : Z ≤ H := d1LiftX_le_H p H R _
  have hZp : IsPGroup p Z := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R _)
  have hNB : GLBPrimeCore p H ≤ H ⊓ M := hd.d1PlusCore_facts.2.2.trans hd.d1PlusCore_facts.1
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hT1 : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≠ ⊥ :=
    fun h => hd.noncyclic (by rw [h]; infer_instance)
  obtain ⟨ψK, hψinj, hψrange, hc⟩ := hTF.torus
  set ψ : Multiplicative (GaloisField p n) →* H ⧸ primeComplementCore (G := H) p :=
    K.subtype.comp ψK with hψdef
  have hψinj' : Function.Injective ψ := K.subtype_injective.comp hψinj
  have hψrange' : ψ.range = (Z.subgroupOf H).map π := by
    rw [hd.map_d1LiftX_centerOf, hψdef, MonoidHom.range_comp, hψrange, ← hT₁]
    exact map_subtype_centerOf _
  have hcY : ∀ μ : (GaloisField p n)ˣ, ∃ c ∈ ((H ⊓ M).subgroupOf H).map π,
      ∀ a : Multiplicative (GaloisField p n),
        c * ψ a * c⁻¹ =
          ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ e * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcN, hcact⟩ := hc μ
    have hcY : (c : H ⧸ primeComplementCore (G := H) p) ∈ K ⊓ Subgroup.normalizer
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) : Set _) := by
      have := coe_mem_normalizer_map hcN
      rwa [hT₁] at this
    refine ⟨c, hN _ le_rfl hT1 hcY, fun a => ?_⟩
    simp only [hψdef, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, hcact a]
  rcases hTF.e_cases with rfl | ⟨rfl, -⟩
  · obtain ⟨φ, hφ⟩ := exists_torus_of_map_subgroupOf_eq' hZH hZp hNB ψ hψinj' hψrange'
      (fun μ => by
        obtain ⟨c, hc, hca⟩ := hcY μ
        exact ⟨c, hc, fun a => by rw [hca, pow_one]⟩)
    exact ⟨φ, fun μ => by
      obtain ⟨t, ht, hta⟩ := hφ μ
      exact ⟨t, ht, fun a => by rw [hta, pow_one]⟩⟩
  · exact exists_torus_of_map_subgroupOf_eq hZH hZp hNB ψ hψinj' hψrange' hcY

omit [Finite G] [Fact p.Prime] in
theorem le_d1PlusCore_of_map_le {Y : Subgroup G} (hYH : Y ≤ H)
    (hY : (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) :
    Y ≤ d1PlusCore p H K := fun y hy =>
  ⟨⟨y, hYH hy⟩, hY ⟨⟨y, hYH hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩

theorem D1CompCore.isCyclic_of_le_d1PlusCore (hd : D1CompCore p P M H R Rbar K)
    {A : Subgroup G} (hAN : A ≤ d1PlusCore p H K) (hA : IsPGroup p A) : IsCyclic A := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hAH : A ≤ H := hAN.trans (Subgroup.map_subtype_le _)
  have hAp : IsPGroup p (A.subgroupOf H) := hA.comap_subtype
  have hAC : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hAN (Subgroup.mem_subgroupOf.mp ha)
    rw [← Subtype.ext hxa]
    exact hx
  have hcyc := hd.red.isCyclic_of_le_centralizer hd.comp hKX₀ (hAp.map _) hAC
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
    (primeComplementCore (G := H) p) (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p))
    _ hAp
  let e := MulEquiv.ofBijective _ ⟨hinj, (QuotientGroup.mk' _).subgroupMap_surjective _⟩
  have : IsCyclic (A.subgroupOf H) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom
    (MulEquiv.surjective _)

theorem D1OneLieData.isCyclic_of_le_d1PlusCore (hd : D1OneLieData p P M H R Rbar K)
    {A : Subgroup G} (hAN : A ≤ d1PlusCore p H K) (hA : IsPGroup p A) : IsCyclic A :=
  hd.toCore.isCyclic_of_le_d1PlusCore hAN hA

theorem D1OneLieData.inf_d1PlusCore_eq_bot (hd : D1OneLieData p P M H R Rbar K) :
    d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ⊓
      d1PlusCore p H K = ⊥ := by
  have hp : p.Prime := Fact.out
  set Z := d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
    K)) with hZ
  have hZH : Z ≤ H := d1LiftX_le_H p H R _
  have hZp : IsPGroup p Z := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R _)
  have hle : Z ⊓ d1PlusCore p H K ≤ Z ⊓ GLBPrimeCore p H := by
    rintro x ⟨hxZ, hxN⟩
    refine ⟨hxZ, (mem_glbPrimeCore_iff_mk_eq_one ⟨x, hZH hxZ⟩).mpr ?_⟩
    have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hZH hxZ⟩ ∈
        (Z.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      ⟨⟨x, hZH hxZ⟩, Subgroup.mem_subgroupOf.mpr hxZ, rfl⟩
    rw [hd.map_d1LiftX_centerOf] at h1
    obtain ⟨y, hyC, hyx⟩ := hxN
    have hyx' : y = ⟨x, hZH hxZ⟩ := Subtype.ext hyx
    rw [hyx'] at hyC
    have hcen : (⟨_, h1.1.2⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC _ k.2)
    rw [hd.center, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  rw [inf_eq_bot_of_isPGroup hp hZp (glbPrimeCore_coprime p H)] at hle
  exact le_bot_iff.mp hle

theorem D1OneLieData.mData (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) :
    ∃ n e : ℕ, D1OneLieMData p n e P M H R (d1PlusCore p H K)
      (d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K))) := by
  have hp : p.Prime := Fact.out
  obtain ⟨T₁, hT₁, hF, n, e, hTF⟩ := hd.exists_oneLieTorusFacts hK hT
  obtain ⟨-, hdich, hperf, hrank⟩ := stmtOneLieBorel Rbar _ K n e hd.cfg.red hd.comp
    hd.noncyclic hd.z hd.center T₁ hT₁ hF hTF
  obtain ⟨hNle, hHN, hcore⟩ := hd.d1PlusCore_facts
  have htor := hd.exists_torus_lift hT₁ hTF
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set Z := d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
    K)) with hZ
  have hZH : Z ≤ H := d1LiftX_le_H p H R _
  have hZp : IsPGroup p Z := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R _)
  have hZmap := hd.map_d1LiftX_centerOf
  refine ⟨n, e, hd.toPhaseThree hK, hd.cfg.indBetaFour, hTF.two_le, hTF.e_cases, d1LiftX_le p H R _,
    htor, hNle, hHN, hcore, fun A hAN hA => hd.isCyclic_of_le_d1PlusCore hAN hA,
    hd.inf_d1PlusCore_eq_bot, fun Y hY hYN => ?_, fun L hL hLL => ?_, fun z hz c hc => ?_,
    pRank_inf_le_of_pRank_top_le hp hrank, fun h2 => ?_⟩
  ·
    rcases hdich ((Y.subgroupOf H).map π) (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY))
      (map_mk_le_normalizer_map_mk hYN) with hle | hle
    · left
      have h1 : Z ≤ Y ⊔ GLBPrimeCore p H :=
        le_sup_glbPrimeCore_of_map_le hZH (by rw [hZmap]; exact hle)
      exact le_of_le_sup_of_isPGroup_of_coprime hZp (glbPrimeCore_coprime p H)
        ((hcore.trans hNle).trans hYN) h1
    · exact Or.inr (le_d1PlusCore_of_map_le (hY.trans inf_le_left) hle)
  ·
    exact le_d1PlusCore_of_map_le (hL.trans inf_le_left)
      (hperf _ (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL))
        (commutator_map_eq_self (hL.trans inf_le_left) hLL))
  ·
    obtain ⟨c', hc'C, rfl⟩ := hc
    have hzH := hZH hz
    have hzK : π ⟨z, hzH⟩ ∈ K := by
      have h1 : π ⟨z, hzH⟩ ∈ (Z.subgroupOf H).map π :=
        ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      rw [hZmap] at h1
      exact h1.1.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hc'C _ hzK
    refine (mem_glbPrimeCore_iff_mk_eq_one (⟨z, hzH⟩ * c' * (⟨z, hzH⟩ : H)⁻¹ * c'⁻¹)).mpr ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm
  ·
    subst h2
    have hZX : Z ≤ d1LiftX p H R K := Subgroup.map_mono (inf_le_inf_left _ (Subgroup.comap_mono
      ((inf_le_left : centerOf _ ≤ _).trans inf_le_right)))
    obtain ⟨φ, -⟩ := htor
    have hZcard : Nat.card Z = p ^ 2 := by
      rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
        GaloisField.card p 2 (by norm_num)]
    exact hd.pair_of_torusFacts hT₁ hTF hZX hZmap hZcard

end MData

theorem stmtOneLieMData : StmtOneLieMData :=
  fun hK hT hd => hd.mData hK hT

end CFSG.AGLEmbedding
