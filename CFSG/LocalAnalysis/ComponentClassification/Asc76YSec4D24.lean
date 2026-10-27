module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Defs
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D11
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D20

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def rotIn (Δ : Set (Subgroup G)) (W : Subgroup G) : Subgroup G :=
  sSup {V | V ≤ W ∧ ∃ L ∈ Δ, ∃ T : Subgroup G, IsSylowOf 2 T L ∧ IsDihedralRot V T}

@[expose] def blockGrp (Δ : Set (Subgroup G)) (W : Subgroup G) : Subgroup G :=
  rotIn Δ W ⊔ oddCoreIn (sSup Δ)

omit [Finite G] in
theorem rotIn_le (Δ : Set (Subgroup G)) (W : Subgroup G) : rotIn Δ W ≤ W :=
  sSup_le fun _ hV => hV.1

omit [Finite G] in
theorem rotIn_le_sSup (Δ : Set (Subgroup G)) (W : Subgroup G) : rotIn Δ W ≤ sSup Δ :=
  sSup_le fun _ ⟨_, _, hL, _, hT, hV⟩ => (hV.le.trans hT.le).trans (le_sSup hL)

theorem rot_le_blockGrp (hΩ : Assumption41 Ω)
    (hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ omegaD Ω (sec4W Ω S))
    (hΔn : ∀ L ∈ Δ, sSup Δ ≤ normalizer (L : Set G)) {L T V : Subgroup G} (hL : L ∈ Δ)
    (hT : IsSylowOf 2 T L) (hV : IsDihedralRot V T) : V ≤ blockGrp Δ (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLΩ, TL, hTL, hTLW⟩ := hΔ hL
  obtain ⟨VL, hVL⟩ := Assumption41.exists_rot hΩ hLΩ hTL
  have hVLW : VL ≤ sec4W Ω S := rot_le_sec4W hΩ hS hLΩ hTL hVL hTLW
  have hVLY : VL ≤ blockGrp Δ (sec4W Ω S) :=
    (le_sSup (show VL ∈ {V | V ≤ sec4W Ω S ∧ ∃ L ∈ Δ, ∃ T : Subgroup G, IsSylowOf 2 T L ∧
      IsDihedralRot V T} from ⟨hVLW, L, hL, TL, hTL, hVL⟩)).trans le_sup_left
  obtain ⟨o, ho, hTeq⟩ := exists_oddCoreIn_eq_rightConjugate hT hTL (hnil L hLΩ TL hTL)
  have hVL' := hVL.rightConjugate o
  rw [← hTeq] at hVL'
  have hVeq : AschbacherTightEmbedding.rightConjugate VL o = V :=
    hV.eq_of_isCyclic hVL'.le hVL'.isCyclic hVL'.relIndex_eq
  have hLX : L ≤ sSup Δ := le_sSup hL
  have hOX : oddCoreIn L ≤ oddCoreIn (sSup Δ) :=
    oddCoreIn_le_oddCoreIn_of_le hLX (hΔn L hL)
  have hoY : o ∈ blockGrp Δ (sec4W Ω S) := mem_sup_right (hOX ho)
  intro v hv
  rw [← hVeq, mem_rightConjugate_iff] at hv
  have e : v = o⁻¹ * (o * v * o⁻¹) * o := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hoY) (hVLY hv)) hoY

theorem mem_normalizer_blockGrp (hΩ : Assumption41 Ω)
    (hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ omegaD Ω (sec4W Ω S))
    (hΔn : ∀ L ∈ Δ, sSup Δ ≤ normalizer (L : Set G)) {g : G} (hg : g ∈ setStab Δ) :
    g ∈ normalizer (blockGrp Δ (sec4W Ω S) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := blockGrp Δ (sec4W Ω S) with hYdef
  have hgX : g ∈ normalizer ((sSup Δ : Subgroup G) : Set G) := setStab_le_normalizer_sSup Δ hg
  have hO : AschbacherTightEmbedding.rightConjugate (oddCoreIn (sSup Δ)) g =
      oddCoreIn (sSup Δ) := by
    rw [← oddCoreIn_rightConjugate_eq, (rightConjugate_eq_self_iff _ g).mpr hgX]
  have hWg : AschbacherTightEmbedding.rightConjugate (rotIn Δ (sec4W Ω S)) g ≤ Y := by
    rw [rightConjugate_le_iff]
    refine sSup_le fun V ⟨_, L, hL, T, hT, hV⟩ => ?_
    rw [← rightConjugate_le_iff]
    exact rot_le_blockGrp hΩ hnil hS hΔ hΔn ((hg L).mp hL) (isSylowOf_rightConjugate hT g)
      (hV.rightConjugate g)
  have hle : AschbacherTightEmbedding.rightConjugate Y g ≤ Y := by
    have e : AschbacherTightEmbedding.rightConjugate Y g =
        AschbacherTightEmbedding.rightConjugate (rotIn Δ (sec4W Ω S)) g ⊔
          AschbacherTightEmbedding.rightConjugate (oddCoreIn (sSup Δ)) g := Subgroup.map_sup _ _ _
    rw [e, hO]
    exact sup_le hWg le_sup_right
  have heq : AschbacherTightEmbedding.rightConjugate Y g = Y :=
    eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  exact (rightConjugate_eq_self_iff Y g).mp heq

theorem mem_rotIn_of_mem_blockGrp {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {Δ : Set (Subgroup G)} {x : G} (hx : x ∈ blockGrp Δ (sec4W Ω S)) (hxS : x ∈ S) :
    x ∈ rotIn Δ (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  have hR2 : IsPGroup 2 (rotIn Δ W) :=
    hS.isPGroup.to_le ((rotIn_le Δ W).trans (sec4W_le S))
  have hRO : rotIn Δ W ≤ normalizer (oddCoreIn (sSup Δ) : Set G) :=
    (rotIn_le_sSup Δ W).trans (le_normalizer_oddCoreIn _)
  have hsyl : IsSylowOf 2 (rotIn Δ W) (blockGrp Δ W) :=
    isSylowOf_sup_of_odd_of_le_normalizer hR2 (odd_card_oddCoreIn _) hRO
  have hP : IsPGroup 2 (blockGrp Δ W ⊓ S : Subgroup G) := hS.isPGroup.to_le inf_le_right
  have heq := hsyl.eq_of_le (le_inf le_sup_left ((rotIn_le Δ W).trans (sec4W_le S)))
    inf_le_left hP
  rw [← heq]
  exact mem_inf.mpr ⟨hx, hxS⟩

theorem zZero_subset_rotIn (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K)
    (hRW : R ≤ normalizer (sec4W Ω S : Set G)) {z : G} (hz : IsZOf R z) {x : G}
    (hx : x ∈ zZero Ω (sec4W Ω S) R z) : x ∈ rotIn (dComp Ω K) (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, zT, hzT, hc, rfl⟩ := hx
  obtain ⟨⟨L, hL, hTL⟩, hTW⟩ := hT
  have hRD : R ∈ DSet Ω (sec4W Ω S) := ⟨⟨K, hK, hR⟩, hRW⟩
  obtain ⟨r, hr⟩ := IsBarOf.exists_of_mem H.hΩ hRD
  obtain ⟨s, hs⟩ := IsBarOf.exists_of_mem H.hΩ (⟨⟨L, hL, hTL⟩, hTW⟩ : T ∈ DSet Ω _)
  have hLK : L ∈ dComp Ω K := by
    rcases eq_or_dAdj_of_commute H hS hK hL hR hTL hRW hTW hr hs (hc r s hr hs) with h | h
    · rw [← h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h
  obtain ⟨U, hU, hzU, -, -⟩ := hz
  obtain ⟨V, hV, hzTV, -, -⟩ := hzT
  have hUW : U ≤ sec4W Ω S := rot_le_sec4W H.hΩ hS hK hR hU hRW
  have hVW : V ≤ sec4W Ω S := rot_le_sec4W H.hΩ hS hL hTL hV hTW
  have h1 : z ∈ rotIn (dComp Ω K) (sec4W Ω S) :=
    le_sSup (show U ∈ {V | V ≤ sec4W Ω S ∧ ∃ L ∈ dComp Ω K, ∃ T, IsSylowOf 2 T L ∧
      IsDihedralRot V T} from ⟨hUW, K, Relation.ReflTransGen.refl, R, hR, hU⟩) hzU
  have h2 : zT ∈ rotIn (dComp Ω K) (sec4W Ω S) :=
    le_sSup (show V ∈ {V | V ≤ sec4W Ω S ∧ ∃ L ∈ dComp Ω K, ∃ T, IsSylowOf 2 T L ∧
      IsDihedralRot V T} from ⟨hVW, L, hLK, T, hTL, hV⟩) hzTV
  exact mul_mem h1 h2

theorem conj_mem_zZero (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z x : G}
    (hx : x ∈ zZero Ω (sec4W Ω S) R z) (n : normalizer (sec4W Ω S : Set G)) :
    (n : G)⁻¹ * x * n ∈ zZero Ω (sec4W Ω S) (AschbacherTightEmbedding.rightConjugate R n)
      ((n : G)⁻¹ * z * n) := by
  obtain ⟨T, hT, zT, hzT, hc, rfl⟩ := hx
  have hRn := DSet.rightConjugate_mem hΩ hR n.2
  have hTn := DSet.rightConjugate_mem hΩ hT n.2
  refine ⟨_, hTn, (n : G)⁻¹ * zT * n, hzT.rightConjugate n, fun r' s' hr' hs' => ?_, by group⟩
  obtain ⟨r, hr⟩ := IsBarOf.exists_of_mem hΩ hR
  obtain ⟨s, hs⟩ := IsBarOf.exists_of_mem hΩ hT
  have e1 := IsBarOf.unique hΩ hS hRn hr' (hr.rightConjugate n)
  have e2 := IsBarOf.unique hΩ hS hTn hs' (hs.rightConjugate n)
  rw [e1, e2]
  have h := hc r s hr hs
  calc (n : NBar (sec4W Ω S))⁻¹ * r * n * ((n : NBar (sec4W Ω S))⁻¹ * s * n) =
        (n : NBar (sec4W Ω S))⁻¹ * (r * s) * n := by group
    _ = (n : NBar (sec4W Ω S))⁻¹ * (s * r) * n := by rw [h]
    _ = (n : NBar (sec4W Ω S))⁻¹ * s * n * ((n : NBar (sec4W Ω S))⁻¹ * r * n) := by group

omit [Finite G] in
theorem mGrp_le_normalizer (W : Subgroup G) : MGrp Ω W ≤ normalizer (W : Set G) :=
  iSup₂_le fun _ hT => hT.2

omit [Finite G] in
theorem le_mGrp {W T : Subgroup G} (hT : T ∈ DSet Ω W) : T ≤ MGrp Ω W :=
  le_iSup₂ (f := fun T (_ : T ∈ DSet Ω W) => T) T hT

theorem MinCounter.omegaOne_stronglyClosed (h22 : Asc76Lemma22) (hB3 : B3Conclusion)
    {S : Subgroup G} (hM : MinCounter Ω S) (hconn : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∈ dStarComp Ω K)
    (hZ2 : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ →
      ∀ x, IsZInv Ω x → x ∈ normalizer (sec4W Ω S' : Set G) → x ∈ sec4W Ω S')
    {v g : G} (hv : v ∈ omegaOne (sec4W Ω S)) (hvg : g⁻¹ * v * g ∈ S) :
    g⁻¹ * v * g ∈ omegaOne (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  set t := g⁻¹ * v * g with htdef
  obtain ⟨hvW, hvv⟩ := hv
  have htt : t * t = 1 := by
    calc t * t = g⁻¹ * (v * v) * g := by rw [htdef]; group
      _ = 1 := by rw [hvv]; group
  refine ⟨?_, htt⟩
  by_contra htW
  have htN : t ∈ normalizer (W : Set G) := le_normalizer_sec4W hΩ.conj_mem S hvg
  obtain ⟨K₁, hK₁, -⟩ := hM.single
  obtain ⟨K₀, hK₀Ω, R, hR, hRW⟩ := exists_mem_omegaD hΩ hS hK₁
  have hRD : R ∈ DSet Ω W := ⟨⟨K₀, hK₀Ω, hR⟩, hRW⟩
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK₀Ω hR
  obtain ⟨z, hz⟩ := IsZOf.exists_of_rot hU
  have hzZ : IsZInv Ω z := by
    obtain ⟨V, hV, hzV, hz1, hzz⟩ := hz
    exact ⟨K₀, hK₀Ω, R, V, hR, hV, hzV, hz1, hzz⟩
  obtain ⟨htrans, ⟨hZM, hZ₀c⟩, hfix⟩ := hB3 G Ω S h22 hM hconn R hRD z hz
  have hMW := mGrp_le_normalizer (Ω := Ω) W
  have hvZ₀ : v ∈ zZero Ω W R z := by
    by_contra hvZ₀
    have hvM : v ∈ {w | ∃ m ∈ MGrp Ω W, w = m⁻¹ * z * m} := by
      rw [hZM]
      exact ⟨⟨hvW, hvv⟩, hvZ₀⟩
    obtain ⟨m, -, rfl⟩ := hvM
    apply htW
    exact hZ2 S hS t ((hzZ.conj hΩ m).conj hΩ g) htN
  have hvc : ∀ m ∈ MGrp Ω W, m * v = v * m := hZ₀c v hvZ₀
  obtain ⟨m, hmM, htz'⟩ := hfix t htN htt
  set z' := m⁻¹ * z * m with hz'def
  have hzM : z ∈ MGrp Ω W := le_mGrp hRD hz.mem
  have hz'Z : IsZInv Ω z' := hzZ.conj hΩ m
  set z'' := g * z' * g⁻¹ with hz''def
  have hz''v : z'' * v = v * z'' := by
    have e1 : z'' * v = g * (z' * t) * g⁻¹ := by rw [hz''def, htdef]; group
    have e2 : v * z'' = g * (t * z') * g⁻¹ := by rw [hz''def, htdef]; group
    rw [e1, e2, htz']
  set C := centralizer ({v} : Set G) with hCdef
  have hWC : W ≤ C := fun w hw =>
    mem_centralizer_singleton_iff.mpr (sec4W_mul_comm hΩ hS hw hvW)
  obtain ⟨Tv, hTv, hWTv⟩ := exists_isSylowOf_le hW2 hWC
  have hz''z'' : z'' * z'' = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hz'Z
    calc z'' * z'' = g * (z' * z') * g⁻¹ := by rw [hz''def]; group
      _ = 1 := by rw [h]; group
  have hz''P : IsPGroup 2 (zpowers z'') :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hz''z'')
  have hz''C : zpowers z'' ≤ C := (zpowers_le).mpr (mem_centralizer_singleton_iff.mpr hz''v)
  obtain ⟨T₂, hT₂, hz''T₂⟩ := exists_isSylowOf_le hz''P hz''C
  obtain ⟨c₁, hc₁C, hc₁⟩ := L26.IsSylowOf.exists_conj_mem hTv hT₂
  set y := c₁⁻¹ * z'' * c₁ with hydef
  have hyTv : y ∈ Tv := (hc₁ z'').mp (hz''T₂ (mem_zpowers z''))
  obtain ⟨S', hS', hTvS'⟩ := exists_isSylowOf_le hTv.isPGroup (le_top : Tv ≤ ⊤)
  have hWS' : sec4W Ω S' = W := sec4W_eq_of_le hΩ hS hS' (hWTv.trans hTvS')
  have hyZ : IsZInv Ω y := by
    have h1 := hz'Z.conj hΩ (g⁻¹ * c₁)
    have e : (g⁻¹ * c₁)⁻¹ * z' * (g⁻¹ * c₁) = y := by rw [hydef, hz''def]; group
    rwa [e] at h1
  have hyW : y ∈ W := by
    have h1 := hZ2 S' hS' y hyZ (le_normalizer_sec4W hΩ.conj_mem S' (hTvS' hyTv))
    rwa [hWS'] at h1
  obtain ⟨L, hL, TL, VL, hTL, hVL, hyVL, hy1, hyy⟩ := hyZ
  obtain ⟨Ty, Vy, hTy, hVy, hyVy, hTyW, -⟩ :=
    exists_isSylowOf_le_normalizer_of_mem hΩ hS hL hTL hVL hyVL hy1 hyy hyW
  have hTyD : Ty ∈ DSet Ω W := ⟨⟨L, hL, hTy⟩, hTyW⟩
  obtain ⟨m₁, hm₁M, hTyeq⟩ := htrans R hRD Ty hTyD
  have hyz : y = m₁⁻¹ * z * m₁ := by
    have h1 : IsZOf Ty (m₁⁻¹ * z * m₁) := hTyeq ▸ hz.rightConjugate m₁
    exact IsZOf.unique ⟨Vy, hVy, hyVy, hy1, hyy⟩ h1
  set n := m⁻¹ * m₁ with hndef
  have hnM : n ∈ MGrp Ω W := mul_mem (inv_mem hmM) hm₁M
  set c := n * c₁⁻¹ with hcdef
  have hc₁v : c₁ * v = v * c₁ := mem_centralizer_singleton_iff.mp hc₁C
  have hcv : c * v = v * c := by
    have h1 : c₁⁻¹ * v = v * c₁⁻¹ := by
      calc c₁⁻¹ * v = c₁⁻¹ * (v * c₁) * c₁⁻¹ := by group
        _ = c₁⁻¹ * (c₁ * v) * c₁⁻¹ := by rw [hc₁v]
        _ = v * c₁⁻¹ := by group
    calc c * v = n * (c₁⁻¹ * v) := by rw [hcdef]; group
      _ = n * v * c₁⁻¹ := by rw [h1]; group
      _ = v * n * c₁⁻¹ := by rw [hvc n hnM]
      _ = v * c := by rw [hcdef]; group
  have hcz : c⁻¹ * z' * c = z'' := by
    have h1 : z'' = c₁ * y * c₁⁻¹ := by rw [hydef]; group
    rw [h1, hyz, hcdef, hndef, hz'def]
    group
  set h := c * g with hhdef
  have hhz' : h⁻¹ * z' * h = z' := by
    calc h⁻¹ * z' * h = g⁻¹ * (c⁻¹ * z' * c) * g := by rw [hhdef]; group
      _ = z' := by rw [hcz, hz''def]; group
  have hht : h⁻¹ * v * h = t := by
    calc h⁻¹ * v * h = g⁻¹ * (c⁻¹ * (v * c)) * g := by rw [hhdef]; group
      _ = g⁻¹ * (c⁻¹ * (c * v)) * g := by rw [hcv]
      _ = t := by rw [htdef]; group
  have hmW : m ∈ normalizer (W : Set G) := hMW hmM
  set K' := AschbacherTightEmbedding.rightConjugate K₀ m with hK'def
  set R' := AschbacherTightEmbedding.rightConjugate R m with hR'def
  have hK' : K' ∈ Ω := hΩ.conj_mem K₀ hK₀Ω m
  have hR' : IsSylowOf 2 R' K' := isSylowOf_rightConjugate hR m
  have hR'W : R' ≤ normalizer (W : Set G) := rightConjugate_le_normalizer hRW hmW
  have hz'R' : IsZOf R' z' := hz.rightConjugate m
  have hK'D : K' ∈ omegaD Ω W := ⟨hK', R', hR', hR'W⟩
  have hhK' : h ∈ normalizer (K' : Set G) := by
    apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK')
      (hR'.le hz'R'.mem) hz'R'.ne_one hz'R'.mul_self
    rw [mem_centralizer_singleton_iff]
    calc h * z' = h * (h⁻¹ * z' * h) := by rw [hhz']
      _ = z' * h := by group
  set Δ' := dComp Ω K' with hΔ'def
  have hdis := hM.not_connected_commGraph h22 hconn
  have hΔ' : Δ' ⊆ omegaD Ω W := fun L hL => hM.mem_omegaD_of_reflTransGen hK'D hL
  have hΔ'n : ∀ L ∈ Δ', sSup Δ' ≤ normalizer (L : Set G) := by
    intro L hL
    refine sSup_le fun L' hL' => ?_
    rcases hM.eq_or_dAdj_of_mem_dComp h22 hdis hK' hR' hR'W hL hL' with h1 | h1
    · rw [← h1]
      exact le_normalizer
    · exact h1.2.2.1
  have hhstab : h ∈ setStab Δ' := by
    apply mem_setStab_dComp hΩ
    rw [(rightConjugate_eq_self_iff K' h).mpr hhK']
    exact Relation.ReflTransGen.refl
  have hhY := mem_normalizer_blockGrp hΩ hM.twoNil hS hΔ' hΔ'n hhstab
  have hvZ₀' : v ∈ zZero Ω W R' z' := by
    have h1 := conj_mem_zZero hΩ hS hRD hvZ₀ ⟨m, hmW⟩
    have e : m⁻¹ * v * m = v := by
      calc m⁻¹ * v * m = m⁻¹ * (m * v) := by rw [hvc m hmM]; group
        _ = v := by group
    rwa [e] at h1
  have hvY : v ∈ blockGrp Δ' W :=
    mem_sup_left (zZero_subset_rotIn H hS hK' hR' hR'W hz'R' hvZ₀')
  have htY : t ∈ blockGrp Δ' W := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hhY) v).mp hvY
    rw [inv_inv, hht] at h1
    exact h1
  exact htW (rotIn_le Δ' W (mem_rotIn_of_mem_blockGrp hS htY hvg))

end CFSG.ComponentClassification.Asc76.Sec4
