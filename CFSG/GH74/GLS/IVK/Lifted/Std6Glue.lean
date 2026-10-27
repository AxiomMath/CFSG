module

public import CFSG.GH74.GLS.IVK.Lifted.FProps
public import CFSG.GH74.GLS.IVK.Lifted.TwoGroups
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed3
public import CFSG.Walter.J1.HStruct
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section Std6r1Lemmas

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

omit [Finite G] in
theorem hatImg_eq_map (K S : Subgroup G) : hatImg K S = (S.subgroupOf K).map (hatMk K) := by
  ext x
  rw [mem_hatImg, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem std6r1_comp_rigid (h : Std6r1 G z S K) : IsRigidRankOneComp z K := by
  have : K ∈ {K' | IsRigidRankOneComp z K'} := by rw [h.comps]; exact Set.mem_singleton K
  exact this

theorem std6r1_comp_isPCompIn (h : Std6r1 G z S K) : IsPCompIn 2 (centralizer ({z} : Set G)) K :=
  (std6r1_comp_rigid h).1.1.2.2

theorem std6r1_comp_pRank (h : Std6r1 G z S K) : pRank 2 ↥K = 1 := (std6r1_comp_rigid h).2

theorem std6r1_orderOf_z (h : Std6r1 G z S K) : orderOf z = 2 := h.classical.1

theorem std6r1_rigidProduct_eq (h : Std6r1 G z S K) : rigidProduct z = K := by
  unfold rigidProduct; rw [h.comps, sSup_singleton]

theorem std6r1_Pz_eq (h : Std6r1 G z S K) : Pz S z = S ⊓ K := by
  unfold Pz; rw [std6r1_rigidProduct_eq h]

theorem std6r1_Qz_eq (h : Std6r1 G z S K) : Qz S z = S ⊓ cSec K := by
  unfold Qz rigidSectionCentralizer; rw [std6r1_rigidProduct_eq h]; rfl

theorem std6r1_Rz_eq (h : Std6r1 G z S K) : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := by
  unfold Rz; rw [std6r1_Pz_eq h, std6r1_Qz_eq h]

theorem std6r1_S_le_C (h : Std6r1 G z S K) : S ≤ centralizer ({z} : Set G) := h.sylow.le

theorem std6r1_S_pgroup (h : Std6r1 G z S K) : IsPGroup 2 ↥S := h.sylow.isPGroup

theorem std6r1_cmap_eq (h : Std6r1 G z S K) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    cmap c K = K := by
  have h1 : IsRigidRankOneComp z (cmap c K) := isRigidRankOneComp_cmap (std6r1_comp_rigid h) hc
  have h2 : cmap c K ∈ {K' | IsRigidRankOneComp z K'} := h1
  rw [h.comps] at h2
  exact h2

theorem std6r1_S_normalizes (h : Std6r1 G z S K) {s : G} (hs : s ∈ S) : s ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := std6r1_cmap_eq h (std6r1_S_le_C h (S.inv_mem hs))
  have h2 : x ∈ cmap s⁻¹ K ↔ s⁻¹⁻¹ * x * s⁻¹ ∈ K := mem_cmap
  rw [h1, inv_inv] at h2
  exact h2

theorem std6r1_P_norm (h : Std6r1 G z S K) {s : G} (hs : s ∈ S) {p : G} (hp : p ∈ S ⊓ K) :
    s * p * s⁻¹ ∈ S ⊓ K :=
  ⟨S.mul_mem (S.mul_mem hs hp.1) (S.inv_mem hs),
    (mem_normalizer_iff.1 (std6r1_S_normalizes h hs) p).1 hp.2⟩

theorem std6r1_exists_sylow_P (h : Std6r1 G z S K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K := by
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 h.sylow
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := (std6r1_comp_isPCompIn h).2
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS (std6r1_comp_isPCompIn h).1 hsub
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1 hSK

theorem std6r1_lift_inner (h : Std6r1 G z S K) (hZ : ∀ x ∈ Subgroup.center (Hat K), x * x = 1)
    {s : G} (hs : s ∈ S) (hin : InducesInner s K) :
    ∃ k₀ ∈ S ⊓ K, s * k₀⁻¹ ∈ S ⊓ cSec K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := std6r1_exists_sylow_P h
  let Pbar : Sylow 2 (Hat K) := P.mapSurjective (hatMk_surjective K)
  have hPbar : (Pbar : Subgroup (Hat K)) = (P : Subgroup ↥K).map (hatMk K) :=
    Sylow.coe_mapSurjective (hatMk_surjective K) P
  have hPsub : (S ⊓ K).subgroupOf K = (P : Subgroup ↥K) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hPimg : (Pbar : Subgroup (Hat K)) = hatImg K (S ⊓ K) := by
    rw [hPbar, hatImg_eq_map, hPsub]
  have hsN := std6r1_S_normalizes h hs
  have phi_one : ∀ hh : (1 : G) ∈ normalizer (K : Set G), phi K (1 : G) hh = 1 := by
    intro hh
    have h1K : hatMk K (⟨1, one_mem K⟩ : ↥K) = 1 := by
      have : (⟨1, one_mem K⟩ : ↥K) = 1 := rfl
      rw [this, map_one]
    rw [show phi K (1 : G) hh = phi K (1 : G) (le_normalizer (one_mem K)) from rfl,
      phi_of_mem K (one_mem K), h1K, map_one]
  obtain ⟨k, hk, hkc⟩ := hin
  have hsk : s * k⁻¹ ∈ normalizer (K : Set G) := hkc.1
  have h1 : phi K (s * k⁻¹) hsk = 1 := (phi_eq_one_iff K hsk).mpr hkc
  have hφ : phi K s hsN = MulAut.conj (hatMk K ⟨k, hk⟩) := by
    have h2 : phi K s hsN = phi K (s * k⁻¹) hsk * phi K k (le_normalizer hk) := by
      rw [← phi_mul K hsk (le_normalizer hk)]
      exact phi_congr K (by group) hsN _
    rw [h2, h1, one_mul, phi_of_mem K hk]
  set kb : Hat K := hatMk K ⟨k, hk⟩ with hkb
  have hsinv : s⁻¹ ∈ S := S.inv_mem hs
  have hsinvN := std6r1_S_normalizes h hsinv
  have hφinv : phi K s⁻¹ hsinvN = (phi K s hsN)⁻¹ := by
    have h3 : phi K s hsN * phi K s⁻¹ hsinvN = 1 := by
      rw [← phi_mul K hsN hsinvN]
      have : phi K (s * s⁻¹) (mul_mem hsN hsinvN) = phi K 1 (one_mem _) :=
        phi_congr K (by group) _ _
      rw [this]
      exact phi_one _
    exact eq_inv_of_mul_eq_one_right h3
  have hnorm : kb ∈ normalizer ((Pbar : Subgroup (Hat K)) : Set (Hat K)) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hPimg]
    have hSs : ∀ a ∈ S ⊓ K, s * a * s⁻¹ ∈ S ⊓ K := fun a ha => std6r1_P_norm h hs ha
    have hSs' : ∀ a ∈ S ⊓ K, s⁻¹ * a * s⁻¹⁻¹ ∈ S ⊓ K := fun a ha => std6r1_P_norm h hsinv ha
    constructor
    · intro hx
      have := phi_mem_hatImg hsN hSs hx
      rwa [hφ, MulAut.conj_apply] at this
    · intro hx
      have h4 : phi K s hsN x ∈ hatImg K (S ⊓ K) := by
        rw [hφ, MulAut.conj_apply]
        exact hx
      have h5 := phi_mem_hatImg hsinvN hSs' h4
      rwa [hφinv, MulAut.inv_apply_self] at h5
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 (std6r1_S_pgroup h)) ⟨s, hs⟩
  have hs2 : s ^ (2 ^ m) = 1 := by
    have h6 := pow_orderOf_eq_one (⟨s, hs⟩ : ↥S)
    rw [hm] at h6
    simpa using congrArg Subtype.val h6
  have hφpow : ∀ n : ℕ, (phi K s hsN) ^ n = phi K (s ^ n) (pow_mem hsN n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      have : phi K (s ^ 0) (pow_mem hsN 0) = phi K (1 : G) (one_mem _) := phi_congr K (pow_zero s) _ _
      rw [this, phi_one]
    | succ n ih =>
      rw [pow_succ, ih, ← phi_mul K (pow_mem hsN n) hsN]
      exact phi_congr K (by rw [pow_succ]) _ _
  have hkb2 : kb ^ (2 ^ (m + 1)) = 1 := by
    have h7 : (MulAut.conj kb) ^ (2 ^ m) = 1 := by
      rw [← hφ, hφpow]
      have : phi K (s ^ 2 ^ m) (pow_mem hsN _) = phi K 1 (one_mem _) := phi_congr K hs2 _ _
      rw [this, phi_one]
    have h8 : kb ^ (2 ^ m) ∈ Subgroup.center (Hat K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h9 : MulAut.conj (kb ^ 2 ^ m) x = x := by
        rw [map_pow, h7]
        rfl
      rw [MulAut.conj_apply] at h9
      calc x * kb ^ 2 ^ m = (kb ^ 2 ^ m * x * (kb ^ 2 ^ m)⁻¹) * kb ^ 2 ^ m := by rw [h9]
        _ = kb ^ 2 ^ m * x := by group
    have h10 := hZ _ h8
    rw [pow_succ, pow_mul, sq]
    exact h10
  have hmem : kb ∈ (Pbar : Subgroup (Hat K)) :=
    CFSG.Walter.J1.JankoHyp.mem_sylow_of_mem_normalizer Pbar hnorm hkb2
  rw [hPbar] at hmem
  obtain ⟨k₀, hk₀P, hk₀⟩ := Subgroup.mem_map.1 hmem
  have hk₀S : (k₀ : G) ∈ S ⊓ K := by
    rw [← hP]
    exact ⟨k₀, hk₀P, rfl⟩
  refine ⟨(k₀ : G), hk₀S, ?_⟩
  have hk0N : (k₀ : G) ∈ normalizer (K : Set G) := le_normalizer k₀.2
  have hsk0 : s * (k₀ : G)⁻¹ ∈ normalizer (K : Set G) := mul_mem hsN (inv_mem hk0N)
  refine ⟨S.mul_mem hs (S.inv_mem hk₀S.1), ?_⟩
  refine (phi_eq_one_iff K hsk0).mp ?_
  rw [phi_mul K hsN (inv_mem hk0N), hφ]
  have h11 : phi K (k₀ : G)⁻¹ (inv_mem hk0N) = MulAut.conj (hatMk K ⟨(k₀ : G)⁻¹, inv_mem k₀.2⟩) :=
    phi_of_mem K (inv_mem k₀.2)
  rw [h11]
  have h12 : (hatMk K ⟨(k₀ : G)⁻¹, inv_mem k₀.2⟩) = (hatMk K k₀)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h12, hk₀]
  show MulAut.conj kb * MulAut.conj kb⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

end Std6r1Lemmas


section Std6Props

open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 II4_Aut IsSL2Or2A7 innOf)

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

omit [Finite G] in
theorem rigid_isPCompIn {K : Subgroup G} (hK : IsRigidRankOneComp z K) :
    IsPCompIn 2 (centralizer ({z} : Set G)) K := hK.1.1.2.2

theorem std6_hatOK (h44 : II4_44) (h : Std6 G z S) {K : Subgroup G} (hK : IsRigidRankOneComp z K) :
    HatOK (Hat K) := by
  have hz : orderOf z = 2 := h.classical.1
  have hKc := rigid_isPCompIn hK
  exact ⟨TwoThin.isQuasisimple_hat hKc, isKGroupNative_hat h.simple hz hKc.1,
    (pRank_hat K).trans hK.2, h44 G h.simple z hz K hKc hK.2⟩

theorem sq_eq_one_of_card_center {Q : Type} [Group Q] (hc : Nat.card (Subgroup.center Q) = 2) :
    ∀ x ∈ Subgroup.center Q, x * x = 1 := by
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥(Subgroup.center Q)) ^ Nat.card (Subgroup.center Q) = 1 := pow_card_eq_one'
  rw [hc, sq] at h1
  simpa using congrArg Subtype.val h1

theorem normalizes_of_centralizes {K : Subgroup G} (hK : IsRigidRankOneComp z K) {t : G}
    (ht : t ∈ centralizer ({z} : Set G)) {W : Subgroup G} (hWK : W ≤ K) (hW2 : IsPGroup 2 ↥W)
    (hWnc : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWt : ∀ w ∈ W, t * w = w * t) :
    t ∈ normalizer (K : Set G) := by
  by_contra hn
  have hK' : IsRigidRankOneComp z (cmap t⁻¹ K) := isRigidRankOneComp_cmap hK (inv_mem ht)
  have hne : K ≠ cmap t⁻¹ K := by
    intro h
    apply hn
    rw [mem_normalizer_iff]
    intro x
    have h1 : x ∈ cmap t⁻¹ K ↔ t⁻¹⁻¹ * x * t⁻¹ ∈ K := mem_cmap
    rw [← h, inv_inv] at h1
    exact h1
  have hle : K ≤ cSec (cmap t⁻¹ K) :=
    le_cSec_of_ne (rigid_isPCompIn hK) (rigid_isPCompIn hK') hne
  have hWK' : W ≤ cmap t⁻¹ K := by
    intro w hw
    rw [mem_cmap, inv_inv]
    have : t * w * t⁻¹ = w := by rw [hWt w hw]; group
    rw [this]
    exact hWK hw
  apply hWnc
  intro a ha b hb
  have hcent : ∀ w (hw : w ∈ W), hatMk (cmap t⁻¹ K) ⟨w, hWK' hw⟩ ∈
      Subgroup.center (Hat (cmap t⁻¹ K)) := by
    intro w hw
    have hwK' : w ∈ cmap t⁻¹ K := hWK' hw
    have hwc : w ∈ cSec (cmap t⁻¹ K) := hle (hWK hw)
    have h1 : phi (cmap t⁻¹ K) w (le_normalizer hwK') = 1 := (phi_eq_one_iff _ _).2 hwc
    rw [phi_of_mem (cmap t⁻¹ K) hwK'] at h1
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun ρ : MulAut (Hat (cmap t⁻¹ K)) => ρ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * hatMk (cmap t⁻¹ K) ⟨w, hwK'⟩
        = (hatMk (cmap t⁻¹ K) ⟨w, hwK'⟩ * g * (hatMk (cmap t⁻¹ K) ⟨w, hwK'⟩)⁻¹) *
            hatMk (cmap t⁻¹ K) ⟨w, hwK'⟩ := by rw [h2]
      _ = hatMk (cmap t⁻¹ K) ⟨w, hwK'⟩ * g := by group
  have hab : hatMk (cmap t⁻¹ K) ⟨a * b, hWK' (W.mul_mem ha hb)⟩ =
      hatMk (cmap t⁻¹ K) ⟨b * a, hWK' (W.mul_mem hb ha)⟩ := by
    have e1 : (⟨a * b, hWK' (W.mul_mem ha hb)⟩ : ↥(cmap t⁻¹ K)) =
        ⟨a, hWK' ha⟩ * ⟨b, hWK' hb⟩ := rfl
    have e2 : (⟨b * a, hWK' (W.mul_mem hb ha)⟩ : ↥(cmap t⁻¹ K)) =
        ⟨b, hWK' hb⟩ * ⟨a, hWK' ha⟩ := rfl
    rw [e1, e2, map_mul, map_mul]
    exact ((Subgroup.mem_center_iff.1 (hcent a ha)) _).symm
  exact eq_of_hatMk_eq hWK' hW2 (W.mul_mem ha hb) (W.mul_mem hb ha) hab

theorem ivk_triv_fAut_of_std : CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_triv_fAut := by
  intro G _ _ z S h K hK a ha
  exact inducesFAut_of_mem_cSec h.simple h.classical.1 (rigid_isPCompIn hK) hK.2 ha

theorem ivk_f_pow_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_f_pow := by
  intro G _ _ z S h K hK s hs hsF hsc
  obtain ⟨hsN, hF⟩ := hsF
  have hOK := std6_hatOK h44 h hK
  have hφ1 : phi K s hsN ≠ 1 := fun h1 => hsc ((phi_eq_one_iff K hsN).1 h1)
  obtain ⟨m, hm1, hm2, hmF⟩ := dict_pow h2A7 hOK _ hF hφ1
  have hφpow : ∀ n : ℕ, (phi K s hsN) ^ n = phi K (s ^ n) (pow_mem hsN n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      have : phi K (s ^ 0) (pow_mem hsN 0) = phi K (1 : G) (one_mem _) := phi_congr K (pow_zero s) _ _
      rw [this, phi_one_aux]
    | succ n ih =>
      rw [pow_succ, ih, ← phi_mul K (pow_mem hsN n) hsN]
      exact phi_congr K (by rw [pow_succ]) _ _
  have hbN : s ^ m ∈ normalizer (K : Set G) := pow_mem hsN m
  refine ⟨s ^ m, pow_mem hs m, ⟨hbN, ?_⟩, ?_, ?_⟩
  · show IsFAutomorphism (Hat K) (phi K (s ^ m) hbN)
    rw [← hφpow m]
    exact hmF
  · intro hc
    apply hm1
    rw [hφpow m]
    exact (phi_eq_one_iff K hbN).2 hc
  · refine (phi_eq_one_iff K (mul_mem hbN hbN)).1 ?_
    rw [phi_mul K hbN hbN, ← hφpow m]
    exact hm2

theorem ivk_diag_unique_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_diag_unique := by
  intro G _ _ z S K h s hs y hy hss hyy hsR hyR hsF hyF
  have hOK := std6_hatOK h44 h.toStd6 (std6r1_comp_rigid h)
  have hZ := sq_eq_one_of_card_center hOK.sl2.2
  have hsN := std6r1_S_normalizes h hs
  have hyN := std6r1_S_normalizes h hy
  have hφs2 : phi K s hsN * phi K s hsN = 1 := phi_mul_self K hsN hss
  have hφy2 : phi K y hyN * phi K y hyN = 1 := phi_mul_self K hyN hyy
  have hRz := std6r1_Rz_eq h
  have notInner : ∀ {x : G} (hx : x ∈ S) (hxN : x ∈ normalizer (K : Set G)), x ∉ Rz S z →
      phi K x hxN ∉ innOf (Hat K) := by
    intro x hx hxN hxR hin
    apply hxR
    obtain ⟨k₀, hk₀, hk⟩ := std6r1_lift_inner h hZ hx ((phi_mem_inn_iff K hxN).1 hin)
    rw [hRz]
    have e : x = (x * k₀⁻¹) * k₀ := by group
    rw [e]
    exact mul_mem (mem_sup_right hk) (mem_sup_left hk₀)
  have hin := dict_diag h2A7 hOK _ _ hφs2 hφy2 (notInner hs hsN hsR) (notInner hy hyN hyR)
    (fun hf => hsF ⟨hsN, hf⟩) (fun hf => hyF ⟨hyN, hf⟩)
  have hyiN : y⁻¹ ∈ normalizer (K : Set G) := inv_mem hyN
  have hsyN : s * y⁻¹ ∈ normalizer (K : Set G) := mul_mem hsN hyiN
  have hin' : phi K (s * y⁻¹) hsyN ∈ innOf (Hat K) := by
    rw [phi_mul K hsN hyiN, phi_inv_aux K hyN hyiN]
    exact hin
  obtain ⟨k₀, hk₀, hk⟩ := std6r1_lift_inner h hZ (S.mul_mem hs (S.inv_mem hy))
    ((phi_mem_inn_iff K hsyN).1 hin')
  rw [hRz]
  have e : s * y⁻¹ = (s * y⁻¹ * k₀⁻¹) * k₀ := by group
  rw [e]
  exact mul_mem (mem_sup_right hk) (mem_sup_left hk₀)

theorem ivk_1_19_lift_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_1_19_lift := by
  intro G _ _ z S h K hK t ht ht2 W hWSK hWq hWt
  have hz := h.classical.1
  have hKc := rigid_isPCompIn hK
  have hWK : W ≤ K := fun w hw => (hWSK hw).2
  have hW2 : IsPGroup 2 ↥W := h.sylow.isPGroup.to_le (fun w hw => (hWSK hw).1)
  have hWnc := quatGroup_not_comm W hWq
  have htC : t ∈ centralizer ({z} : Set G) := h.sylow.le ht
  have htN := normalizes_of_centralizes hK htC hWK hW2 hWnc hWt
  have hOK := std6_hatOK h44 h hK
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, sq] at this
  have hφ2 : phi K t htN * phi K t htN = 1 := phi_mul_self K htN htt
  have hWbar2 : IsPGroup 2 ↥(hatImg K W) := by
    rw [hatImg_eq_map]
    exact (hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm).map (hatMk K)
  have hWbarnc : ¬ ∀ a ∈ hatImg K W, ∀ b ∈ hatImg K W, a * b = b * a := by
    intro hcomm
    apply hWnc
    intro a ha b hb
    have h1 := hcomm _ (hatMk_mem_hatImg hWK ha) _ (hatMk_mem_hatImg hWK hb)
    have h2 : hatMk K ⟨a * b, hWK (W.mul_mem ha hb)⟩ = hatMk K ⟨b * a, hWK (W.mul_mem hb ha)⟩ := by
      have e1 : (⟨a * b, hWK (W.mul_mem ha hb)⟩ : ↥K) = ⟨a, hWK ha⟩ * ⟨b, hWK hb⟩ := rfl
      have e2 : (⟨b * a, hWK (W.mul_mem hb ha)⟩ : ↥K) = ⟨b, hWK hb⟩ * ⟨a, hWK ha⟩ := rfl
      rw [e1, e2, map_mul, map_mul]
      exact h1
    exact eq_of_hatMk_eq hWK hW2 (W.mul_mem ha hb) (W.mul_mem hb ha) h2
  have hWφ : ∀ w ∈ hatImg K W, phi K t htN w = w := by
    intro x hx
    obtain ⟨a, haW, rfl⟩ := mem_hatImg.1 hx
    rw [phi_mk]
    congr 1
    apply Subtype.ext
    have : t * (a : G) * t⁻¹ = a := by rw [hWt a haW]; group
    exact this
  rcases dict_involution h2A7 hOK _ hφ2 (hatImg K W) hWbar2 hWbarnc hWφ with h1 | hF
  · exact inducesFAut_of_mem_cSec h.simple hz hKc hK.2 ((phi_eq_one_iff K htN).1 h1)
  · exact ⟨htN, hF⟩

end Std6Props

end CFSG.GH74.GLS.IVK.Lifted
