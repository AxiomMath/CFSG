module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

namespace ZCAbs

theorem mem_zpowers_map {N G : Type*} [Group N] [Group G] (f : N ≃* G) {z g : N}
    (hg : g ∈ zpowers z) : f g ∈ zpowers (f z) := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  exact mem_zpowers_iff.mpr ⟨k, (map_zpow f z k).symm⟩

theorem map_zConjClosure {N G : Type*} [Group N] [Group G] (f : N ≃* G) (z u : N) :
    (zConjClosure z u).map f.toMonoidHom = zConjClosure (f z) (f u) := by
  have hz : (zpowers z).map f.toMonoidHom = zpowers (f z) :=
    MonoidHom.map_zpowers f.toMonoidHom z
  unfold zConjClosure
  rw [MonoidHom.map_closure]
  refine congrArg Subgroup.closure (Set.ext fun x => ⟨?_, ?_⟩)
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨f g, mem_zpowers_map f hg, by simp⟩
  · rintro ⟨g', hg', rfl⟩
    rw [← hz] at hg'
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hg'
    exact ⟨g * u * g⁻¹, ⟨g, hg, rfl⟩, by simp⟩

theorem map_le_normalizer_zConjClosure {N G : Type} [Group N] [Group G] (f : N ≃* G) {z u : N}
    {H : Subgroup N} (h : H ≤ normalizer (zConjClosure z u : Set N)) :
    H.map f.toMonoidHom ≤ normalizer (zConjClosure (f z) (f u) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  have hset : (zConjClosure (f z) (f u) : Set G) = f '' (zConjClosure z u : Set N) := by
    rw [← map_zConjClosure f z u]
    rfl
  rw [hset]
  exact mem_normalizer_image_of_mem f (h hx)

theorem zConjClosure_congr {G : Type*} [Group G] {z z' : G} (h : zpowers z = zpowers z')
    (u : G) : zConjClosure z u = zConjClosure z' u := by
  unfold zConjClosure
  rw [h]

theorem conj_mem_zConjClosure {G : Type*} [Group G] {z : G} (u : G) {g : G}
    (hg : g ∈ zpowers z) : g * u * g⁻¹ ∈ zConjClosure z u :=
  subset_closure ⟨g, hg, rfl⟩

theorem zConjClosure_le {G : Type*} [Group G] {z u : G} {X : Subgroup G}
    (h : ∀ g ∈ zpowers z, g * u * g⁻¹ ∈ X) : zConjClosure z u ≤ X :=
  (closure_le X).mpr (by rintro _ ⟨g, hg, rfl⟩; exact h g hg)

theorem mem_normalizer_zConjClosure {G : Type*} [Group G] (z u : G) :
    z ∈ normalizer (zConjClosure z u : Set G) := by
  have hle : zpowers z ≤
      normalizer ((Subgroup.closure {x | ∃ g ∈ zpowers z, x = g * u * g⁻¹} : Subgroup G) :
        Set G) := by
    refine le_normalizer_closure_iff.mpr ?_
    rintro w hw _ ⟨g, hg, rfl⟩
    have h : w * (g * u * g⁻¹) * w⁻¹ = (w * g) * u * (w * g)⁻¹ := by group
    rw [h]
    exact subset_closure ⟨w * g, mul_mem hw hg, rfl⟩
  exact hle (mem_zpowers z)

theorem map_simple_nonabelian {N G : Type} [Group N] [Group G] (f : N ≃* G) {H : Subgroup N}
    (hsimp : IsSimpleGroup H) (hnc : ¬ IsMulCommutative H) :
    IsSimpleGroup (H.map f.toMonoidHom) ∧ ¬ IsMulCommutative (H.map f.toMonoidHom) ∧
      Nat.card (H.map f.toMonoidHom) = Nat.card H := by
  have e := H.equivMapOfInjective f.toMonoidHom f.injective
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mp hsimp, ?_, (Nat.card_congr e.toEquiv).symm⟩
  intro h
  apply hnc
  rw [isMulCommutative_iff] at h ⊢
  intro a b
  apply e.injective
  rw [map_mul, map_mul]
  exact h _ _

theorem kxSection_of_nonabelian_simple {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {K H : Subgroup G} {z : G} (hz : orderOf z = p) (hHK : H ≤ K) (hsimp : IsSimpleGroup H)
    (hnc : ¬ IsMulCommutative H) (hzH : z ∈ H) (h3 : 3 ∣ Nat.card H) : KxSection z K 3 := by
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hcon
    exact hnc (isMulCommutative_iff.mpr fun a b => by_contra fun hab => hcon ⟨a, b, hab⟩)
  have hS : S622IsSimpleSection H (⊥ : Subgroup G) := by
    haveI := hsimp
    have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection.of_surjective
      (MonoidHom.id ↥H) Function.surjective_id hnab
    rwa [(MonoidHom.ker_eq_bot_iff (MonoidHom.id ↥H)).mpr Function.injective_id,
      Subgroup.map_bot] at h
  have hz1 : z ∉ (⊥ : Subgroup G) := by
    intro hmem
    rw [Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz
    have := hp.one_lt
    omega
  have h3' : 3 ∣ (⊥ : Subgroup G).relIndex H := by
    rw [Subgroup.relIndex_bot_left]
    exact h3
  unfold KxSection
  exact ⟨H, ⊥, hHK, hS, hzH, hz1, h3'⟩

end ZCAbs

theorem ZCW.of_mulEquiv {N G : Type} [Group N] [Group G] (f : N ≃* G) {p : ℕ} (h : ZCW N p) :
    ZCW G p := by
  obtain ⟨z₀, hord, hW⟩ := h
  refine ⟨f z₀, (orderOf_injective f.toMonoidHom f.injective z₀).trans hord, ?_⟩
  intro u hu2 hu1
  obtain ⟨v, rfl⟩ := f.surjective u
  have hv2 : v * v = 1 := f.injective (by rw [map_mul, hu2, map_one])
  have hv1 : v ≠ 1 := fun hv => hu1 (by rw [hv, map_one])
  rcases hW v hv2 hv1 with ⟨g, hg, k, hk, hne⟩ | ⟨H, hHle, hsimp, hnc, hz₀H, h3⟩
  · left
    refine ⟨f g, ZCAbs.mem_zpowers_map f hg, f k, ZCAbs.mem_zpowers_map f hk,
      fun heq => hne ?_⟩
    apply f.injective
    simpa only [map_mul, map_inv] using heq
  · right
    obtain ⟨hsimp', hnc', hcard⟩ := ZCAbs.map_simple_nonabelian f hsimp hnc
    refine ⟨H.map f.toMonoidHom, ZCAbs.map_le_normalizer_zConjClosure f hHle, hsimp', hnc',
      mem_map_of_mem _ hz₀H, ?_⟩
    rw [hcard]
    exact h3

namespace ZCAbs

theorem conj_mem_pCoreOf {p : ℕ} {G : Type*} [Group G] {K : Subgroup G} {k o : G} (hk : k ∈ K)
    (ho : o ∈ pCoreOf p K) : k * o * k⁻¹ ∈ pCoreOf p K :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p K hk) o).mp ho

theorem exists_central_involution_pCoreOf {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {y : G} (hyQ : y ∈ pCoreOf 2 K) (hy1 : y ≠ 1) :
    ∃ u ∈ pCoreOf 2 K, u * u = 1 ∧ u ≠ 1 ∧ ∀ q ∈ pCoreOf 2 K, u * q = q * u := by
  have hne : pCoreOf 2 K ≠ ⊥ := fun h => hy1 (by rwa [h, Subgroup.mem_bot] at hyQ)
  obtain ⟨u, hu2, huQ, huc⟩ :=
    CFSG.ComponentClassification.BFailureLocalization.exists_central_involution (pCoreOf 2 K)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hne
  refine ⟨u, huQ, ?_, ?_, huc⟩
  · have h := pow_orderOf_eq_one u
    rwa [hu2, sq] at h
  · intro h
    rw [h, orderOf_one] at hu2
    omega

theorem conj_comm_of_central {G : Type*} [Group G] {K : Subgroup G} {z u : G} (hzK : z ∈ K)
    (huQ : u ∈ pCoreOf 2 K) (huc : ∀ q ∈ pCoreOf 2 K, u * q = q * u) {g h : G}
    (hg : g ∈ zpowers z) (hh : h ∈ zpowers z) :
    g * u * g⁻¹ * (h * u * h⁻¹) = h * u * h⁻¹ * (g * u * g⁻¹) := by
  have hgK : g ∈ K := zpowers_le.mpr hzK hg
  have hhK : h ∈ K := zpowers_le.mpr hzK hh
  have hq : h * u * h⁻¹ ∈ pCoreOf 2 K := conj_mem_pCoreOf hhK huQ
  have hq' : g⁻¹ * (h * u * h⁻¹) * g ∈ pCoreOf 2 K := by
    simpa using conj_mem_pCoreOf (inv_mem hgK) hq
  have h1 := huc _ hq'
  calc g * u * g⁻¹ * (h * u * h⁻¹)
      = g * (u * (g⁻¹ * (h * u * h⁻¹) * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * (h * u * h⁻¹) * g) * u) * g⁻¹ := by rw [h1]
    _ = h * u * h⁻¹ * (g * u * g⁻¹) := by group

theorem normalizer_zConjClosure_le {G : Type} [Group G] [Finite G] {K : Subgroup G} {z u : G}
    (hu1 : u ≠ 1)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K)
    (hQ : ∀ g ∈ zpowers z, g * u * g⁻¹ ∈ pCoreOf 2 K) :
    normalizer (zConjClosure z u : Set G) ≤ K := by
  have hVQ : zConjClosure z u ≤ pCoreOf 2 K := zConjClosure_le hQ
  have hVK : zConjClosure z u ≤ K := hVQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hV2 : IsPGroup 2 (zConjClosure z u) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).of_injective (Subgroup.inclusion hVQ)
      (Subgroup.inclusion_injective hVQ)
  have huV : u ∈ zConjClosure z u := by
    have h := conj_mem_zConjClosure u ((zpowers z).one_mem)
    rwa [one_mul, inv_one, mul_one] at h
  have hVK1 : zConjClosure z u ⊓ K ≠ ⊥ := by
    intro hbot
    have hmem : u ∈ zConjClosure z u ⊓ K := ⟨huV, hVK huV⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  exact hcl _ hV2 (mem_normalizer_zConjClosure z u) hVK1

end ZCAbs

theorem kxSection_of_zcw {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : ZCW G p) {K : Subgroup G} {z : G} (hz : orderOf z = p)
    (hzK : z ∈ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K)
    (hy : ∃ y ∈ pCoreOf 2 K, z * y ≠ y * z) : KxSection z K 3 := by
  obtain ⟨z₀, hord, hW⟩ := hW
  obtain ⟨y, hyQ, hyne⟩ := hy
  have hy1 : y ≠ 1 := fun h => hyne (by rw [h, mul_one, one_mul])
  obtain ⟨u, huQ, hu2, hu1, huc⟩ := ZCAbs.exists_central_involution_pCoreOf hyQ hy1
  have hQ : ∀ g ∈ zpowers z, g * u * g⁻¹ ∈ pCoreOf 2 K := fun g hg =>
    ZCAbs.conj_mem_pCoreOf (zpowers_le.mpr hzK hg) huQ
  have hNK := ZCAbs.normalizer_zConjClosure_le hu1 hcl hQ
  obtain ⟨c, hzc⟩ := exists_mulEquiv_zpowers hp hsyl hz hord
  have hv2 : c.symm u * c.symm u = 1 :=
    c.injective (by rw [map_mul, c.apply_symm_apply, hu2, map_one])
  have hv1 : c.symm u ≠ 1 := fun h => hu1 (by rw [← c.apply_symm_apply u, h, map_one])
  rcases hW (c.symm u) hv2 hv1 with ⟨g, hg, k, hk, hne⟩ | ⟨H, hHle, hsimp, hnc, hz₀H, h3⟩
  · exfalso
    apply hne
    apply c.injective
    have hcg : c g ∈ zpowers z := by
      rw [← hzc]
      exact ZCAbs.mem_zpowers_map c hg
    have hck : c k ∈ zpowers z := by
      rw [← hzc]
      exact ZCAbs.mem_zpowers_map c hk
    have hcomm := ZCAbs.conj_comm_of_central hzK huQ huc hcg hck
    simpa only [map_mul, map_inv, c.apply_symm_apply] using hcomm
  · have hH1 := ZCAbs.map_le_normalizer_zConjClosure c hHle
    rw [c.apply_symm_apply, ZCAbs.zConjClosure_congr hzc] at hH1
    obtain ⟨hsimp', hnc', hcard⟩ := ZCAbs.map_simple_nonabelian c hsimp hnc
    have hzH : z ∈ H.map c.toMonoidHom := by
      have h1 : c z₀ ∈ H.map c.toMonoidHom := mem_map_of_mem _ hz₀H
      refine (zpowers_le.mpr h1) ?_
      rw [hzc]
      exact mem_zpowers z
    refine ZCAbs.kxSection_of_nonabelian_simple hp hz (hH1.trans hNK) hsimp' hnc' hzH ?_
    rw [hcard]
    exact h3

theorem row_of_zcw {s : TauCeti.SporadicName} {p : ℕ} {N : Type} [Group N] [Finite N]
    (e : Nonempty (N ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (hsyl : ¬ p ^ 2 ∣ Nat.card N)
    (hW : ZCW N p) (hs : s ≠ .M11) : KFactSporLocalRow s p := by
  refine row_of_model fun G _ _ hG hp _ K z hz _ hzK _ hcl hy _ => ?_
  let f : N ≃* G := e.some.trans hG.some.symm
  have hsylG : ¬ p ^ 2 ∣ Nat.card G := by
    rwa [← Nat.card_congr f.toEquiv]
  exact ⟨kxSection_of_zcw hp hsylG (ZCW.of_mulEquiv f hW) hz hzK hcl hy, hs⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
