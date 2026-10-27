module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7T21A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8.T21

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Triangle


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem alphaOf_eq_of_triangle_T (hs : Hat2A7S.Pre2A7 Ω K₀) {V W₁ W₂ : Subgroup G}
    {v w₁ w₂ : G} (hV : V ∈ Ω) (hW₁ : W₁ ∈ omegaNbr Ω V) (hW₂ : W₂ ∈ omegaNbr Ω V)
    (h12 : W₂ ∈ omegaNbr Ω W₁) (hv : IsUniqueInvolution V v) (hw₁ : IsUniqueInvolution W₁ w₁)
    (hw₂ : IsUniqueInvolution W₂ w₂) (hw₁v : w₁ ≠ v) (hw₂v : w₂ ≠ v) :
    alphaOf (Subgroup.closure ({w₂, v} : Set G)) =
      alphaOf (Subgroup.closure ({w₁, v} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := witness_of_pre hs
  have hT := tri_of_adj hΩ hV hW₁ hW₂ h12 hv hw₁ hw₂
  have hvw : v * w₁ = w₁ * v := hT.comm hΩ 0 1
  have hvw₂ : v * w₂ = w₂ * v := hT.comm hΩ 0 2
  have hw₁w₂ : w₁ * w₂ = w₂ * w₁ := hT.comm hΩ 1 2
  by_cases hind : w₂ ∈ Subgroup.closure ({v, w₁} : Set G)
  · rcases T8.mem_closure_pair_involutions hv.sq hw₁.sq hvw hind with h | h | h | h
    · exact absurd h hw₂.ne_one
    · exact absurd h hw₂v
    · rw [h]
    · rw [closure_pair_eq_of_mul hv.sq h]
  · have hBabel : IsElemAbelian 2 (Subgroup.closure ({v, w₁, w₂} : Set G)) :=
      T8T.isElemAbelian_closure_three hv.sq hw₁.sq hw₂.sq hvw hvw₂ hw₁w₂
    have hB8 : Nat.card ↥(Subgroup.closure ({v, w₁, w₂} : Set G)) = 8 :=
      T8T.natCard_closure_three hv.sq hw₁.sq hw₂.sq hvw hvw₂ hw₁w₂ hv.ne_one hw₁.ne_one
        (Ne.symm hw₁v) hw₂.ne_one hind
    have hB2 : IsPGroup 2 ↥(Subgroup.closure ({v, w₁, w₂} : Set G)) :=
      IsPGroup.of_card (n := 3) (by rw [hB8]; norm_num)
    have hleV : Subgroup.closure ({v, w₁, w₂} : Set G) ≤ centralizerModOdd ⊤ V := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy | hy
      · rw [hy]
        exact inv_mem_centralizerModOdd hΩ hw hV hv (Or.inl rfl)
      · rw [hy]
        exact inv_mem_centralizerModOdd hΩ hw hV hw₁ (Or.inr hW₁)
      · rw [hy]
        exact inv_mem_centralizerModOdd hΩ hw hV hw₂ (Or.inr hW₂)
    have hleW : Subgroup.closure ({v, w₁, w₂} : Set G) ≤ centralizerModOdd ⊤ W₁ := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy | hy
      · rw [hy]
        exact inv_mem_centralizerModOdd hΩ hw hW₁.1 hv (Or.inr (nbr_symm hΩ hV hW₁.1 hW₁))
      · rw [hy]
        exact inv_mem_centralizerModOdd hΩ hw hW₁.1 hw₁ (Or.inl rfl)
      · rw [hy]
        exact inv_mem_centralizerModOdd hΩ hw hW₁.1 hw₂ (Or.inr h12)
    have hH51 : Hyp51 (Subgroup.closure ({v, w₁, w₂} : Set G)) := by
      refine hyp51_of_members hs hBabel hB8 fun c hcB hc1 => ?_
      have hc2 : c * c = 1 := by
        have := hBabel.2 c hcB
        rwa [pow_two] at this
      have hcord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
      by_cases hcv : c = v
      · refine ⟨W₁, w₁, hw₁, Subgroup.subset_closure (by simp), ?_, ?_⟩
        · intro hmem
          rcases T7A.eq_one_or_eq_of_mem_zpowers hcord hmem with h1 | h1
          · exact hw₁.ne_one h1
          · exact hw₁v (h1.trans hcv)
        · rw [hcv]
          exact xMem_of_le_centralizerModOdd hW₁.1 hB2 hleW (Subgroup.subset_closure (by simp))
      · refine ⟨V, v, hv, Subgroup.subset_closure (by simp), ?_,
          xMem_of_le_centralizerModOdd hV hB2 hleV hcB⟩
        intro hmem
        rcases T7A.eq_one_or_eq_of_mem_zpowers hcord hmem with h1 | h1
        · exact hv.ne_one h1
        · exact hcv h1.symm
    have hDB : Subgroup.closure ({w₁, v} : Set G) ≤ Subgroup.closure ({v, w₁, w₂} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hAB : Subgroup.closure ({w₂, v} : Set G) ≤ Subgroup.closure ({v, w₁, w₂} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({w₁, v} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hw₁.sq hv.sq hw₁.ne_one hv.ne_one hw₁v hvw.symm
    have hA : IsElemAbelian2 (Subgroup.closure ({w₂, v} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hw₂.sq hv.sq hw₂.ne_one hv.ne_one hw₂v hvw₂.symm
    exact (lemma54_odd_and_eq hH51 hDB hD).2 _ hAB hA

theorem mem_omegaOfSet_of_nbr (hs : Hat2A7S.Pre2A7 Ω K₀) {K P : Subgroup G} {z t : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hP : P ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution P t) (htz : t ≠ z) : P ∈ omegaOfSet Ω (twinSet Ω K) := by
  refine ⟨hP.1, fun L hL => ?_⟩
  have hKL := Hat2A7S.kPerp_eq_of_mem_twinSet hs.hyp hs.classical hK hz hL
  have hPK : P ∈ KPerp Ω K := Or.inr hP
  have hPL : P ∈ KPerp Ω L := by
    rw [← hKL]
    exact hPK
  rcases Set.mem_insert_iff.mp hPL with h | h
  · exfalso
    have h1 : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
    have h2 : IsUniqueInvolution P z := by
      rw [h]
      exact h1
    exact htz (ht.eq h2)
  · exact h

theorem alphaOf_eq_of_layer_T (hs : Hat2A7S.Pre2A7 Ω K₀) {K A J : Subgroup G} {z tA tJ : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hA : A ∈ omegaNbr Ω K)
    (hJ : J ∈ omegaNbr Ω K) (htA : IsUniqueInvolution A tA) (htJ : IsUniqueInvolution J tJ)
    (htAz : tA ≠ z) (htJz : tJ ≠ z)
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
      have hnz : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp (hOcz n hn)
      have hzA : z ∈ Subgroup.normalizer (A : Set G) :=
        Hat2A7S.normalizes_of_mem_omegaNbr_a7 hΩ hs.classical hK hA.1 hA hz htA
      have hzAn : z ∈ Subgroup.normalizer ((conjSub n A : Subgroup G) : Set G) := by
        rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul, ← hnz, conjSub_mul,
          mem_normalizer_iff_conjSub_eq.mp hzA]
      have hAnΩ : conjSub n A ∈ Ω := hΩ.conjInvariant n A hA.1
      have htAn : IsUniqueInvolution (conjSub n A) (n * tA * n⁻¹) := htA.conj n
      have hne : n * tA * n⁻¹ ≠ z := by
        intro h
        apply htAz
        calc tA = n⁻¹ * (n * tA * n⁻¹) * n := by group
          _ = n⁻¹ * z * n := by rw [h]
          _ = z := by
            calc n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [hOc n hn]
              _ = z := by group
      have hAnK : conjSub n A ≠ K := by
        intro h
        apply hne
        have h1 : IsUniqueInvolution K (n * tA * n⁻¹) := by
          rw [← h]
          exact htAn
        exact (hz.eq h1).symm
      have hAn : conjSub n A ∈ omegaNbr Ω K :=
        Hat2A7S.mem_omegaNbr_of_normalizes_a7 hΩ hs.classical hK hAnΩ hAnK hz htAn hzAn
      have hJAn : conjSub n A ∈ omegaNbr Ω J := nbr_symm hΩ hAnΩ hJ.1 hJn
      have h1 := alphaOf_eq_of_triangle_T hs hK hJ hAn hJAn hz htJ htAn htJz hne
      have e : Subgroup.closure ({n * tA * n⁻¹, z} : Set G) =
          conjSub n (Subgroup.closure ({tA, z} : Set G)) := by
        rw [T7A.conjSub_closure_pair, hOc n hn]
      rw [e, alphaOf_conjSub, mem_normalizer_iff_conjSub_eq.mp (hOz hn)] at h1
      exact h1.symm

theorem alphaConst_twin (hs : Hat2A7S.Pre2A7 Ω K₀) {K K' P₁ P₂ : Subgroup G} {z t₁ t₂ : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hP₁ : P₁ ∈ omegaNbr Ω K) (hP₂ : P₂ ∈ omegaNbr Ω K) (ht₁ : IsUniqueInvolution P₁ t₁)
    (ht₂ : IsUniqueInvolution P₂ t₂) (h₁ : t₁ ≠ z) (h₂ : t₂ ≠ z) :
    alphaOf (Subgroup.closure ({t₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({t₁, z} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hP₁' : P₁ ∈ omegaOfSet Ω (twinSet Ω K) := mem_omegaOfSet_of_nbr hs hK hz hP₁ ht₁ h₁
  obtain ⟨u, hfr⟩ := exists_sframe hΩ hK hz hK' hne hP₁' ht₁
  have hN := (sframe_alpha hs hfr).2.2 z (Subgroup.subset_closure (by simp))
  have hOz := (oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ z).trans hN
  exact alphaOf_eq_of_layer_T hs hK hz hP₁ hP₂ ht₁ ht₂ h₁ h₂ hOz

end Triangle

section Component


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem exists_twin_of_mem (hs : Hat2A7S.Pre2A7 Ω K₀) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {M : Subgroup G} (hM : M ∈ Ω) :
    ∃ M' ∈ twinSet Ω M, M' ≠ M := by
  obtain ⟨g₁, hg₁⟩ := hs.trans K hK
  obtain ⟨g₂, hg₂⟩ := hs.trans M hM
  refine ⟨conjSub (g₂ * g₁⁻¹) K', ?_, ?_⟩
  · have := twinSet_conj hs.hyp.conjInvariant hK' (g₂ * g₁⁻¹)
    have e : conjSub (g₂ * g₁⁻¹) K = M := by
      rw [conjSub_mul, ← hg₁, conjSub_inv_conjSub, hg₂]
    rwa [e] at this
  · intro h
    apply hne
    have e : conjSub (g₂ * g₁⁻¹) K = M := by
      rw [conjSub_mul, ← hg₁, conjSub_inv_conjSub, hg₂]
    have h2 : conjSub (g₂ * g₁⁻¹) K' = conjSub (g₂ * g₁⁻¹) K := h.trans e.symm
    calc K' = conjSub (g₂ * g₁⁻¹)⁻¹ (conjSub (g₂ * g₁⁻¹) K') :=
          (conjSub_inv_conjSub _ K').symm
      _ = conjSub (g₂ * g₁⁻¹)⁻¹ (conjSub (g₂ * g₁⁻¹) K) := by rw [h2]
      _ = K := conjSub_inv_conjSub _ K

@[expose] def AlphaConstT (Ω : Set (Subgroup G)) : Prop :=
  ∀ M ∈ Ω, ∀ z : G, IsUniqueInvolution M z → ∀ P₁ ∈ omegaNbr Ω M, ∀ P₂ ∈ omegaNbr Ω M,
    ∀ t₁ t₂ : G, IsUniqueInvolution P₁ t₁ → IsUniqueInvolution P₂ t₂ → t₁ ≠ z → t₂ ≠ z →
      alphaOf (Subgroup.closure ({t₂, z} : Set G)) =
        alphaOf (Subgroup.closure ({t₁, z} : Set G))

theorem alphaConstT (hs : Hat2A7S.Pre2A7 Ω K₀) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) : AlphaConstT Ω := by
  intro M hM z hz P₁ hP₁ P₂ hP₂ t₁ t₂ ht₁ ht₂ h₁ h₂
  obtain ⟨M', hM', hne'⟩ := exists_twin_of_mem hs hK hK' hne hM
  exact alphaConst_twin hs hM hz hM' hne' hP₁ hP₂ ht₁ ht₂ h₁ h₂

theorem alphaOf_eq_of_mem_dComp_T (hs : Hat2A7S.Pre2A7 Ω K₀) (hA : AlphaConstT Ω)
    {K J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) (htz : t ≠ z) {L : Subgroup G}
    (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y →
      IsUniqueInvolution L' y' → y' ≠ y →
        alphaOf (Subgroup.closure ({y', y} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  induction hL with
  | refl =>
    refine ⟨hK, fun L' hL' y y' hy hy' hne => ?_⟩
    have hyz : y = z := hy.eq hz
    rw [hyz] at hne ⊢
    exact hA K hK z hz J hJ L' hL' t y' ht hy' htz hne
  | @tail b c hbk hbc ih =>
    obtain ⟨hbΩ, hPb⟩ := ih
    obtain ⟨hcΩ, hadj⟩ := hbc
    have hcb : c ∈ omegaNbr Ω b ∧ b ∈ omegaNbr Ω c := by
      rcases hadj with h | h
      · exact ⟨h, nbr_symm hΩ hbΩ hcΩ h⟩
      · exact ⟨nbr_symm hΩ hcΩ hbΩ h, h⟩
    refine ⟨hcΩ, fun L'' hL'' y₂ y'' hy₂ hy'' hne => ?_⟩
    obtain ⟨yb, hyb⟩ := Sec6Gen.exists_uniqueInvolution hΩ hbΩ
    by_cases hbc' : yb = y₂
    ·
      have hcT : c ∈ twinSet Ω b := by
        refine ⟨hcΩ, yb, hyb, ?_⟩
        rw [hbc']
        exact hy₂
      have hKP := Hat2A7S.kPerp_eq_of_mem_twinSet hΩ hs.classical hbΩ hyb hcT
      have hL''b : L'' ∈ omegaNbr Ω b := by
        have h1 : L'' ∈ KPerp Ω c := Or.inr hL''
        rw [← hKP] at h1
        rcases Set.mem_insert_iff.mp h1 with h | h
        · exfalso
          have h2 : IsUniqueInvolution b y'' := by
            rw [← h]
            exact hy''
          have h3 := hyb.eq h2
          exact hne (h3.symm.trans hbc')
        · exact h
      have h4 := hPb L'' hL''b yb y'' hyb hy'' (fun h => hne (h.trans hbc'))
      rw [← hbc']
      exact h4
    · have h1 : alphaOf (Subgroup.closure ({y'', y₂} : Set G)) =
          alphaOf (Subgroup.closure ({yb, y₂} : Set G)) :=
        hA c hcΩ y₂ hy₂ b hcb.2 L'' hL'' yb y'' hyb hy'' hbc' hne
      have h2 := hPb c hcb.1 yb y₂ hyb hy₂ (fun h => hbc' h.symm)
      rw [h1, Set.pair_comm]
      exact h2

theorem sigmaNorm_le_normalizer_alpha_T (hs : Hat2A7S.Pre2A7 Ω K₀) (hA : AlphaConstT Ω)
    {K J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) (htz : t ≠ z) :
    sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  intro n hn
  have hKn : conjSub n K ∈ dComp Ω K :=
    (T8.mem_sigmaNorm_iff hs.hyp.conjInvariant hK).1 hn
  obtain ⟨-, hP⟩ := alphaOf_eq_of_mem_dComp_T hs hA hK hz hJ ht htz hKn
  have hne : n * t * n⁻¹ ≠ n * z * n⁻¹ := by
    intro h
    exact htz (mul_left_cancel (mul_right_cancel h))
  have h := hP (conjSub n J) (omegaNbr_conj hs.hyp.conjInvariant hJ n) (n * z * n⁻¹)
    (n * t * n⁻¹) (hz.conj n) (ht.conj n) hne
  rw [← T7A.conjSub_closure_pair, alphaOf_conjSub] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

end Component

end CFSG.ClassicalInvolution.Hat2A7S8.T21
