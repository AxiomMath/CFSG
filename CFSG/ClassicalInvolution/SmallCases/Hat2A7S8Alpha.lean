module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Frame
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerDich
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Tri
public import CFSG.ClassicalInvolution.Asc77.AscT8T3
import CFSG.ClassicalInvolution.Asc77.AscT8T12Eng
import CFSG.ClassicalInvolution.Asc77.AscT8T4Eng
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Defs
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Std

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def AlphaConstAll (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z → ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K,
    ∀ t₁ t₂ : G, IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
      alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
        alphaOf (Subgroup.closure ({t₂, z} : Set G))

theorem nbr_symm (hΩ : HypOmegaGen Ω) {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω)
    (h : B ∈ omegaNbr Ω A) : A ∈ omegaNbr Ω B :=
  Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hA hB h

theorem tri_of_adj (hΩ : HypOmegaGen Ω) {V W₁ W₂ : Subgroup G} {v w₁ w₂ : G} (hV : V ∈ Ω)
    (hW₁ : W₁ ∈ omegaNbr Ω V) (hW₂ : W₂ ∈ omegaNbr Ω V) (h12 : W₂ ∈ omegaNbr Ω W₁)
    (hv : IsUniqueInvolution V v) (hw₁ : IsUniqueInvolution W₁ w₁)
    (hw₂ : IsUniqueInvolution W₂ w₂) : Tri Ω ![V, W₁, W₂] ![v, w₁, w₂] where
  mem := by
    intro i
    fin_cases i
    exacts [hV, hW₁.1, hW₂.1]
  inv := by
    intro i
    fin_cases i
    exacts [hv, hw₁, hw₂]
  adj := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hW₁
    · exact hW₂
    · exact nbr_symm hΩ hV hW₁.1 hW₁
    · exact absurd rfl hij
    · exact h12
    · exact nbr_symm hΩ hV hW₂.1 hW₂
    · exact nbr_symm hΩ hW₁.1 hW₂.1 h12
    · exact absurd rfl hij

theorem closure_pair_eq_of_mul {z t₁ t₂ : G} (hz : z * z = 1) (h : t₂ = z * t₁) :
    Subgroup.closure ({t₂, z} : Set G) = Subgroup.closure ({t₁, z} : Set G) := by
  exact CFSG.ClassicalInvolution.Asc77.T8T.closure_pair_eq_of_mulE hz h

theorem centralizer_le_sigmaNorm_of_nbr (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hK' : K' ∈ omegaNbr Ω K) {y : G} (hy : IsUniqueInvolution K' y) :
    Subgroup.centralizer ({y} : Set G) ≤ sigmaNorm Ω K :=
  (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK'.1 (hnt K' hK'.1) hy).trans
    (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK (T8.mem_dComp_of_mem_omegaNbr hK'))

theorem eq_mul_of_mem_closure_pair (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K M K' : Subgroup G} {z s y : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hM : M ∈ omegaNbr Ω K)
    (hs : IsUniqueInvolution M s)
    (hK'K : K' ∈ omegaNbr Ω K) (hK'M : K' ∈ omegaNbr Ω M) (hy : IsUniqueInvolution K' y)
    (hmem : y ∈ Subgroup.closure ({z, s} : Set G)) : y = z * s := by
  have hzs : z * s = s * z := Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hM hs
  rcases T8.mem_closure_pair_involutions hz.sq hs.sq hzs hmem with h | h | h | h
  · exact absurd h hy.ne_one
  · exfalso
    have h1 : IsUniqueInvolution K' z := h ▸ hy
    exact hK'K.2.1 (hnt K hK K' ⟨hK'K.1, z, hz, h1⟩)
  · exfalso
    have h1 : IsUniqueInvolution K' s := h ▸ hy
    exact hK'M.2.1 (hnt M hM.1 K' ⟨hK'M.1, s, hs, h1⟩)
  · exact h

end Basic

section XMem

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem xMem_self {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    T8.XMem Ω z K := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ K)
  exact ⟨hK, Subgroup.le_normalizer hz.mem, R, hR,
    fun r hr => comm_of_mem_isUniqueInvolution hz (hR.1 hr)⟩

theorem xMem_of_mem_omegaNbr (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L) {K J : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) :
    T8.XMem Ω z J := by
  have hJK : K ∈ omegaNbr Ω J := nbr_symm hΩ hK hJ.1 hJ
  obtain ⟨hzN, hzt⟩ := comm_mem_oddCore_of_mem_omegaNbr hΩ (hw J hJ.1) hJK hz
  have hmem : z ∈ centralizerModOdd ⊤ J := mem_centralizerModOdd hzN hzt
  have hle : Subgroup.zpowers z ≤ centralizerModOdd ⊤ J := Subgroup.zpowers_le.mpr hmem
  obtain ⟨R, hR, hRc⟩ := exists_sylow_centralized_of_acts_trivially
    (T8.isPGroup_zpowers_of_sq hz.sq) (fun e he => (hle he).2.1)
    (fun e he k hk => (hle he).2.2.2 k hk)
  exact ⟨hJ.1, hzN, R, hR, fun r hr => (hRc z (Subgroup.mem_zpowers z) r hr).symm⟩

theorem xMem_zt (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution J t) : T8.XMem Ω (z * t) K := by
  obtain ⟨htN, htk⟩ := comm_mem_oddCore_of_mem_omegaNbr hΩ (hw K hK) hJ ht
  have hzm : z ∈ centralizerModOdd ⊤ K := by
    refine mem_centralizerModOdd (Subgroup.le_normalizer hz.mem) fun k hk => ?_
    have h1 : z * k = k * z := (comm_of_mem_isUniqueInvolution hz hk).symm
    have h2 : z * k * z⁻¹ * k⁻¹ = 1 := by
      rw [h1]
      group
    rw [h2]
    exact (oddCoreOf K).one_mem
  have htm : t ∈ centralizerModOdd ⊤ K := mem_centralizerModOdd htN htk
  have hztm : z * t ∈ centralizerModOdd ⊤ K := (centralizerModOdd ⊤ K).mul_mem hzm htm
  have hle : Subgroup.zpowers (z * t) ≤ centralizerModOdd ⊤ K := Subgroup.zpowers_le.mpr hztm
  have hsq : z * t * (z * t) = 1 := Q3.Q3CL.T8.mul_self_zt hΩ hz hJ ht
  obtain ⟨R, hR, hRc⟩ := exists_sylow_centralized_of_acts_trivially
    (T8.isPGroup_zpowers_of_sq hsq) (fun e he => (hle he).2.1)
    (fun e he k hk => (hle he).2.2.2 k hk)
  exact ⟨hK, hztm.2.1, R, hR, fun r hr => (hRc (z * t) (Subgroup.mem_zpowers _) r hr).symm⟩

end XMem

section Vertex


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem alphaOf_eq_of_triangle (hs : Hat2A7S.Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {V W₁ W₂ : Subgroup G} {v w₁ w₂ : G}
    (hV : V ∈ Ω) (hW₁ : W₁ ∈ omegaNbr Ω V) (hW₂ : W₂ ∈ omegaNbr Ω V)
    (h12 : W₂ ∈ omegaNbr Ω W₁) (hv : IsUniqueInvolution V v) (hw₁ : IsUniqueInvolution W₁ w₁)
    (hw₂ : IsUniqueInvolution W₂ w₂) :
    alphaOf (Subgroup.closure ({w₂, v} : Set G)) =
      alphaOf (Subgroup.closure ({w₁, v} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hT := tri_of_adj hΩ hV hW₁ hW₂ h12 hv hw₁ hw₂
  have hvw : v * w₁ = w₁ * v := hT.comm hΩ 0 1
  by_cases hind : w₂ ∈ Subgroup.closure ({v, w₁} : Set G)
  · have hne1 : w₂ ≠ v := (hT.x_ne hnt (i := 2) (j := 0) (by decide))
    have hne2 : w₂ ≠ w₁ := (hT.x_ne hnt (i := 2) (j := 1) (by decide))
    rcases T8.mem_closure_pair_involutions hv.sq hw₁.sq hvw hind with h | h | h | h
    · exact absurd h hw₂.ne_one
    · exact absurd h hne1
    · exact absurd h hne2
    · rw [closure_pair_eq_of_mul hv.sq h]
  · have hH51 := hT.hyp51 hs hnt hind
    have hvw' : w₁ * v = v * w₁ := hvw.symm
    have hDB : Subgroup.closure ({w₁, v} : Set G) ≤ Subgroup.closure ({v, w₁, w₂} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hAB : Subgroup.closure ({w₂, v} : Set G) ≤ Subgroup.closure ({v, w₁, w₂} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({w₁, v} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hw₁.sq hv.sq hw₁.ne_one hv.ne_one
        (hT.x_ne hnt (i := 1) (j := 0) (by decide)) hvw'
    have hA : IsElemAbelian2 (Subgroup.closure ({w₂, v} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hw₂.sq hv.sq hw₂.ne_one hv.ne_one
        (hT.x_ne hnt (i := 2) (j := 0) (by decide)) (hT.comm hΩ 2 0)
    exact (lemma54_odd_and_eq hH51 hDB hD).2 _ hAB hA

theorem odd_card_alphaOf_of_indep (hs : Hat2A7S.Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {V W₁ W₂ : Subgroup G} {v w₁ w₂ : G}
    (hV : V ∈ Ω) (hW₁ : W₁ ∈ omegaNbr Ω V) (hW₂ : W₂ ∈ omegaNbr Ω V)
    (h12 : W₂ ∈ omegaNbr Ω W₁) (hv : IsUniqueInvolution V v) (hw₁ : IsUniqueInvolution W₁ w₁)
    (hw₂ : IsUniqueInvolution W₂ w₂) (hind : w₂ ∉ Subgroup.closure ({v, w₁} : Set G)) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({w₁, v} : Set G)))) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hT := tri_of_adj hΩ hV hW₁ hW₂ h12 hv hw₁ hw₂
  have hH51 := hT.hyp51 hs hnt hind
  have hDB : Subgroup.closure ({w₁, v} : Set G) ≤ Subgroup.closure ({v, w₁, w₂} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({w₁, v} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hw₁.sq hv.sq hw₁.ne_one hv.ne_one
      (hT.x_ne hnt (i := 1) (j := 0) (by decide)) (hT.comm hΩ 1 0)
  exact (lemma54_odd_and_eq hH51 hDB hD).1

@[expose] def IndepTri (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) : Prop :=
  ∃ (A B' : Subgroup G) (tA tB : G), A ∈ omegaNbr Ω K ∧ B' ∈ omegaNbr Ω K ∧ B' ∈ omegaNbr Ω A ∧
    IsUniqueInvolution A tA ∧ IsUniqueInvolution B' tB ∧ tB ∉ Subgroup.closure ({z, tA} : Set G)

theorem exists_indepTri (h261 : Hat2A7S.A7C26_1) (h274 : Hat2A7S.A7C27_4)
    (hs : Hat2A7S.Std2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hedge : ¬ DEdgeless Ω) (hdisc : ¬ DConnected Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : IndepTri Ω K z := by
  by_contra hno
  have hsK : Hat2A7S.Std2A7 Ω K := hs.of_mem hK
  have hdeg : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      Subgroup.centralizer ({z * s} : Set G) ≤ sigmaNorm Ω K := by
    intro M hM s hs'
    obtain ⟨S', R', T', W', hstd⟩ :=
      Hat2A7S.a7C27_setup_proved G Ω K hsK (hnt K hK) hdisc z hz M hM s hs'
    obtain ⟨K', hK'K, hK'M⟩ := exists_triangle hstd hdisc
      (h261 G Ω K M S' R' T' W' z s hstd hdisc)
    obtain ⟨y, hy⟩ := Sec6Gen.exists_uniqueInvolution hs.hyp hK'K.1
    have hmem : y ∈ Subgroup.closure ({z, s} : Set G) := by
      by_contra hn
      exact hno ⟨M, K', s, y, hM, hK'K, hK'M, hs', hy, hn⟩
    have hyzs := eq_mul_of_mem_closure_pair hs.hyp hnt hK hz hM hs' hK'K hK'M hy hmem
    rw [← hyzs]
    exact centralizer_le_sigmaNorm_of_nbr hs.hyp hnt hK hK'K hy
  obtain ⟨J₀, hJ₀, -⟩ := Hat2A7S.a7C27_nbr_proved G Ω K hsK hedge
  obtain ⟨t₀, ht₀⟩ := Sec6Gen.exists_uniqueInvolution hs.hyp hJ₀.1
  obtain ⟨S', R', T', W', hstd⟩ :=
    Hat2A7S.a7C27_setup_proved G Ω K hsK (hnt K hK) hdisc z hz J₀ hJ₀ t₀ ht₀
  have htop := h274 G Ω K J₀ S' R' T' W' z t₀ hstd hdisc
  have hle : sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
      Subgroup.centralizer ({z * s} : Set G)) ≤ sigmaNorm Ω K :=
    sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => hdeg M hM s hs')
  rw [htop] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hK hsK.trans (top_le_iff.mp hle))

theorem oddCoreOf_layerJoin_le_normalizer_alpha (hs : Hat2A7S.Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K A B' : Subgroup G} {z tA tB : G}
    (hK : K ∈ Ω) (hA : A ∈ omegaNbr Ω K) (hB' : B' ∈ omegaNbr Ω K) (hB'A : B' ∈ omegaNbr Ω A)
    (hz : IsUniqueInvolution K z) (htA : IsUniqueInvolution A tA)
    (htB : IsUniqueInvolution B' tB) (hind : tB ∉ Subgroup.closure ({z, tA} : Set G)) :
    oddCoreOf (T8.layerJoin Ω z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hT := tri_of_adj hΩ hK hA hB' hB'A hz htA htB
  have hH51 := hT.hyp51 hs hnt hind
  have hzA : tA * z = z * tA := hT.comm hΩ 1 0
  have hDB : Subgroup.closure ({tA, z} : Set G) ≤ Subgroup.closure ({z, tA, tB} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({tA, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair htA.sq hz.sq htA.ne_one hz.ne_one
      (hT.x_ne hnt (i := 1) (j := 0) (by decide)) hzA
  obtain ⟨-, h3⟩ := lemma54_odd_and_eq hH51 hDB hD
  have hBabel := hT.B_isElemAbelian hΩ
  have hB8 := hT.card_B hΩ hnt hind
  have hzB := hT.mem_B 0
  have hOC : oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G) :=
    T8T.oddCoreOf_centralizer_le_normalizer hBabel hB8 hzB h3
  have hYC : T8.layerJoin Ω z ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ z
  have hn : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c (T8.layerJoin Ω z) = T8.layerJoin Ω z := fun c hc =>
    Asc77.T8.layerJoin_conjSub_eq hΩ (by rw [T8.cenZ_eq_centralizer]; exact hc)
  exact (T8.oddCoreOf_le_oddCoreOf_of_normalized hYC hn).trans hOC

theorem alphaOf_eq_of_layer (hs : Hat2A7S.Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K A J : Subgroup G} {z tA tJ : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hA : A ∈ omegaNbr Ω K)
    (hJ : J ∈ omegaNbr Ω K) (htA : IsUniqueInvolution A tA) (htJ : IsUniqueInvolution J tJ)
    (hOz : oddCoreOf (T8.layerJoin Ω z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G)) :
    alphaOf (Subgroup.closure ({tJ, z} : Set G)) =
      alphaOf (Subgroup.closure ({tA, z} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := witness_of_pre hs
  have hL : Asc77.T8.LayerHyp Ω z := layerHyp_of_pre hs hz.sq hz.ne_one
  have hAx : T8.XMem Ω z A := xMem_of_mem_omegaNbr hΩ hw hK hz hA
  have hJx : T8.XMem Ω z J := xMem_of_mem_omegaNbr hΩ hw hK hz hJ
  have hOcz : ∀ n ∈ oddCoreOf (T8.layerJoin Ω z), n ∈ Subgroup.centralizer ({z} : Set G) := by
    intro n hn
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ z (oddCoreOf_le_self _ hn)
  have hOc : ∀ n ∈ oddCoreOf (T8.layerJoin Ω z), n * z * n⁻¹ = z := by
    intro n hn
    have h1 : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp (hOcz n hn)
    rw [h1]
    group
  by_cases heq : T8.layerImg Ω z A = T8.layerImg Ω z J
  · obtain ⟨n, hn, hnA⟩ := Asc77.T8.exists_oddCore_conj_of_layerImg_eq hL hAx hJx heq
    have htJ' : tJ = n * tA * n⁻¹ := by
      have h1 := htA.conj n
      rw [hnA] at h1
      exact htJ.eq h1
    have e : Subgroup.closure ({tJ, z} : Set G) =
        conjSub n (Subgroup.closure ({tA, z} : Set G)) := by
      rw [T7A.conjSub_closure_pair, htJ', hOc n hn]
    rw [e, alphaOf_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp (hOz hn)
  · have hF := Asc77.T8.LayerFam.layerSet hΩ hAx
    rcases hF.images_eq_or_commute hL ⟨A, hAx, rfl⟩ ⟨J, hJx, rfl⟩ with h | hcomm
    · exact absurd h heq
    · obtain ⟨n, hn, hJn⟩ :=
        Asc77.T8.exists_oddCore_conj_omegaNbr_of_commute hL hAx hJx heq hcomm
      have hnN : n ∈ Subgroup.normalizer (K : Set G) :=
        T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK (hnt K hK) hz (hOcz n hn)
      have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hnN
      have hAn : conjSub n A ∈ omegaNbr Ω K := by
        have := omegaNbr_conj hΩ.conjInvariant hA n
        rwa [hnK] at this
      have hJAn : conjSub n A ∈ omegaNbr Ω J :=
        nbr_symm hΩ (hΩ.conjInvariant n A hA.1) hJ.1 hJn
      have h1 := alphaOf_eq_of_triangle hs hnt hK hJ hAn hJAn hz htJ (htA.conj n)
      have e : Subgroup.closure ({n * tA * n⁻¹, z} : Set G) =
          conjSub n (Subgroup.closure ({tA, z} : Set G)) := by
        rw [T7A.conjSub_closure_pair, hOc n hn]
      rw [e, alphaOf_conjSub, mem_normalizer_iff_conjSub_eq.mp (hOz hn)] at h1
      exact h1.symm

theorem alphaConst_at_vertex (h261 : Hat2A7S.A7C26_1) (h274 : Hat2A7S.A7C27_4)
    (hs : Hat2A7S.Std2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hedge : ¬ DEdgeless Ω) (hdisc : ¬ DConnected Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) {t₁ t₂ : G} (ht₁ : IsUniqueInvolution J₁ t₁)
    (ht₂ : IsUniqueInvolution J₂ t₂) :
    alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
      alphaOf (Subgroup.closure ({t₂, z} : Set G)) := by
  obtain ⟨A, B', tA, tB, hA, hB', hB'A, htA, htB, hind⟩ :=
    exists_indepTri h261 h274 hs hnt hedge hdisc hK hz
  have hOz := oddCoreOf_layerJoin_le_normalizer_alpha hs.toPre2A7 hnt hK hA hB' hB'A hz htA htB
    hind
  rw [alphaOf_eq_of_layer hs.toPre2A7 hnt hK hz hA hJ₁ htA ht₁ hOz,
    alphaOf_eq_of_layer hs.toPre2A7 hnt hK hz hA hJ₂ htA ht₂ hOz]

theorem alphaConstAll (h261 : Hat2A7S.A7C26_1) (h274 : Hat2A7S.A7C27_4)
    (hs : Hat2A7S.Std2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hedge : ¬ DEdgeless Ω) (hdisc : ¬ DConnected Ω) : AlphaConstAll Ω :=
  fun _ hK _ hz _ hJ₁ _ hJ₂ _ _ h1 h2 =>
    alphaConst_at_vertex h261 h274 hs hnt hedge hdisc hK hz hJ₁ hJ₂ h1 h2

end Vertex

section Global

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem alphaOf_eq_of_mem_dComp (hΩ : HypOmegaGen Ω) (hA : AlphaConstAll Ω) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution J t) {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y →
      IsUniqueInvolution L' y' →
        alphaOf (Subgroup.closure ({y', y} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T8T.alphaOf_eq_of_mem_dCompE
    (fun hA' hB' h => nbr_symm hΩ hA' hB' h)
    (fun hA' => Sec6Gen.exists_uniqueInvolution hΩ hA') hA hK hz hJ ht hL

theorem sigmaNorm_le_normalizer_alpha (hΩ : HypOmegaGen Ω) (hA : AlphaConstAll Ω)
    {K J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) :
    sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  intro n hn
  have hKn : conjSub n K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).1 hn
  obtain ⟨-, hP⟩ := alphaOf_eq_of_mem_dComp hΩ hA hK hz hJ ht hKn
  have h := hP (conjSub n J) (omegaNbr_conj hΩ.conjInvariant hJ n) (n * z * n⁻¹)
    (n * t * n⁻¹) (hz.conj n) (ht.conj n)
  rw [← T7A.conjSub_closure_pair, alphaOf_conjSub] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

end Global

section Layer


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem exists_mul_mem_sigmaNorm_of_centralizer {x : G} (hL : Asc77.T8.LayerHyp Ω x)
    {K : Subgroup G} (hK : T8.XMem Ω x K) {c : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    ∃ ν ∈ oddCoreOf (T8.layerJoin Ω x), ν * c ∈ sigmaNorm Ω K := by
  have hcz : c ∈ T8.cenZ x := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hKc : T8.XMem Ω x (conjSub c K) := Asc77.T8.XMem.conj hL.gen hK hcz
  obtain ⟨ν, hν, hνK⟩ := Asc77.T8.exists_oddCore_conj_mem_dComp hL hK hKc
  refine ⟨ν, hν, ?_⟩
  rw [T8.mem_sigmaNorm_iff hL.gen.conjInvariant hK.1, conjSub_mul]
  exact hνK

theorem oddCoreOf_layerJoin_le_oddCoreOf_centralizer (hΩ : HypOmegaGen Ω) (x : G) :
    oddCoreOf (T8.layerJoin Ω x) ≤ oddCoreOf (Subgroup.centralizer ({x} : Set G)) := by
  have hYC : T8.layerJoin Ω x ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ x
  exact T8.oddCoreOf_le_oddCoreOf_of_normalized hYC fun c hc =>
    Asc77.T8.layerJoin_conjSub_eq hΩ (by rw [T8.cenZ_eq_centralizer]; exact hc)

theorem oddCoreOf_layerJoin_le_of_alpha (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K J : Subgroup G} {z t : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) :
    oddCoreOf (T8.layerJoin Ω (z * t)) ≤ sigmaNorm Ω K := by
  have ha1 : z * t ≠ 1 := T8.zt_ne_one (hnt K hK) hJ hz ht
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have haA : z * t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mul_mem _ hzA htA
  intro x hx
  have hxC := oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * t) hx
  have hxz : x * z = z * x := T8.oddCoreOf_centralizer_commutes hα haA ha1 hzA x hxC
  exact T8.normalizer_le_sigmaNorm hΩ.conjInvariant hK
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK (hnt K hK) hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hxz))

theorem centralizer_le_normalizer_alpha_of_nbr (h261 : Hat2A7S.A7C26_1)
    (hs : Hat2A7S.Std2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hdisc : ¬ DConnected Ω) (hA : AlphaConstAll Ω) {K J : Subgroup G} {z t : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := witness_of_pre hs.toPre2A7
  have hsK : Hat2A7S.Std2A7 Ω K := hs.of_mem hK
  obtain ⟨S', R', T', W', hstd⟩ :=
    Hat2A7S.a7C27_setup_proved G Ω K hsK (hnt K hK) hdisc z hz M hM s hs'
  have hαeq : alphaOf (Subgroup.closure ({s, z} : Set G)) =
      alphaOf (Subgroup.closure ({t, z} : Set G)) := hA K hK z hz M hM J hJ s t hs' ht
  by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω M → ∀ z' : G,
      IsUniqueInvolution K' z' → z' ≠ z * s
  · obtain ⟨K'', hK''K, hK''M⟩ := exists_triangle hstd hdisc
      (h261 G Ω K M S' R' T' W' z s hstd hdisc)
    obtain ⟨z'', hz''⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK''K.1
    have hz''ne : z'' ≠ z * s := hE8 K'' hK''K hK''M z'' hz''
    have hind : z'' ∉ Subgroup.closure ({z, s} : Set G) := fun hmem =>
      hz''ne (eq_mul_of_mem_closure_pair hΩ hnt hK hz hM hs' hK''K hK''M hz'' hmem)
    have hT := tri_of_adj hΩ hK hM hK''K hK''M hz hs' hz''
    have hH51 := hT.hyp51 hs.toPre2A7 hnt hind
    have hzs : s * z = z * s := (hT.comm hΩ 0 1).symm
    have hDB : Subgroup.closure ({s, z} : Set G) ≤ Subgroup.closure ({z, s, z''} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hs'.sq hz.sq hs'.ne_one hz.ne_one
        (hT.x_ne hnt (i := 1) (j := 0) (by decide)) hzs
    obtain ⟨-, h3⟩ := lemma54_odd_and_eq hH51 hDB hD
    have hBabel := hT.B_isElemAbelian hΩ
    have hB8 := hT.card_B hΩ hnt hind
    have hzsB := Subgroup.mul_mem _ (hT.mem_B 0) (hT.mem_B 1)
    have hx : z * s * (z * s) = 1 := Q3.Q3CL.T8.mul_self_zt hΩ hz hM hs'
    have hxne : z * s ≠ 1 := T8.zt_ne_one (hnt K hK) hM hz hs'
    have hL : Asc77.T8.LayerHyp Ω (z * s) := layerHyp_of_pre hs.toPre2A7 hx hxne
    have hKx : T8.XMem Ω (z * s) K := xMem_zt hΩ hw hK hz hM hs'
    intro c hc
    obtain ⟨ν, hν, hνc⟩ := exists_mul_mem_sigmaNorm_of_centralizer hL hKx hc
    have hνO : ν ∈ oddCoreOf (Subgroup.centralizer ({z * s} : Set G)) :=
      oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) hν
    have hν' : ν ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({s, z} : Set G)) : Set G) :=
      T8T.oddCoreOf_centralizer_le_normalizer hBabel hB8 hzsB h3 hνO
    rw [hαeq] at hν'
    have hc' : c = ν⁻¹ * (ν * c) := by group
    rw [hc']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hν') (hN hνc)
  · push Not at hE8
    obtain ⟨K', hK', -, z', hz', hzs⟩ := hE8
    have h1 := centralizer_le_sigmaNorm_of_nbr hΩ hnt hK hK' hz'
    rw [hzs] at h1
    exact h1.trans hN

theorem a7C27_8_of_steps (h261 : Hat2A7S.A7C26_1) (h274 : Hat2A7S.A7C27_4) :
    Hat2A7S.A7C27_8 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G,
      IsUniqueInvolution K' z' → z' ≠ z * t
  · obtain ⟨K'', hK''K, hK''J⟩ := exists_triangle hs hdisc
      (h261 G Ω K J S R T W z t hs hdisc)
    obtain ⟨z'', hz''⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK''K.1
    have hz''ne : z'' ≠ z * t := hE8 K'' hK''K hK''J z'' hz''
    have hind : z'' ∉ Subgroup.closure ({z, t} : Set G) := fun hmem =>
      hz''ne (eq_mul_of_mem_closure_pair hΩ hnt hK hs.hz hs.hJ hs.ht hK''K hK''J hz'' hmem)
    have hedge : ¬ DEdgeless Ω := fun h => h K hK J hs.hJ.1 (Or.inl hs.hJ)
    have hAll : AlphaConstAll Ω := alphaConstAll h261 h274 hs.stand hnt hedge hdisc
    have hN := sigmaNorm_le_normalizer_alpha hΩ hAll hK hs.hz hs.hJ hs.ht
    have hH : T8.H274 Ω K z ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
      sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
        centralizer_le_normalizer_alpha_of_nbr h261 hs.stand hnt hdisc hAll hK hs.hz hs.hJ
          hs.ht hN hM hs')
    have htop : T8.H274 Ω K z = ⊤ := h274 G Ω K J S R T W z t hs hdisc
    rw [htop, top_le_iff] at hH
    have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hH
    have hodd := odd_card_alphaOf_of_indep hs.stand.toPre2A7 hnt hK hs.hJ hK''K hK''J hs.hz hs.ht
      hz'' hind
    have hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
      rcases hnorm.eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        have hord : orderOf z = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact hs.hz.sq) hs.hz.ne_one
        have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
        rw [h, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    have hO := oddCoreOf_layerJoin_le_of_alpha hΩ hnt hK hs.hz hs.hJ hs.ht hα
    have hx : z * t * (z * t) = 1 := Q3.Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
    have hxne : z * t ≠ 1 := T8.zt_ne_one (hnt K hK) hs.hJ hs.hz hs.ht
    have hL : Asc77.T8.LayerHyp Ω (z * t) := layerHyp_of_pre hs.stand.toPre2A7 hx hxne
    have hKx : T8.XMem Ω (z * t) K :=
      xMem_zt hΩ (witness_of_pre hs.stand.toPre2A7) hK hs.hz hs.hJ hs.ht
    have hY := Asc77.T8.layerJoin_le_sigmaNorm_of_oddCoreOf_le hL hKx hO
    exact Asc77.T8.centralizer_le_sigmaNorm_of_layerJoin_le hL hKx hY
  · push Not at hE8
    obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
    have h1 := centralizer_le_sigmaNorm_of_nbr hΩ hnt hK hK' hz'
    rw [hzt] at h1
    exact h1

end Layer

end CFSG.ClassicalInvolution.Hat2A7S8
