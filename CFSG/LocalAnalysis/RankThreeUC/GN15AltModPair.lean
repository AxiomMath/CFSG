module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModData
public import CFSG.LocalAnalysis.RankThreeUC.GN15Sym
public import CFSG.LocalAnalysis.RankThreeUC.GN15ParaSharp
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
open Equiv Equiv.Perm
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
  {g : ↥L →* alternatingGroup (Fin n)}

namespace GNAltModData

variable (S : GNAltModData T L g)

omit [Finite X] in
theorem fixed_ne {a b c₀ : Fin n} (hab : a ≠ b) (hc₀ : ∀ q ∈ S.Q, q c₀ = c₀)
    (hs : swap a b ∈ S.J) : c₀ ≠ a ∧ c₀ ≠ b := by
  have hfix := hc₀ _ (S.J_le_Q hs)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, swap_apply_left] at hfix
    exact hab hfix.symm
  · rw [h, swap_apply_right] at hfix
    exact hab hfix

omit [Finite X] in
theorem ρ_eq_one_iff (hn : 4 ≤ n) (x : ↥(Subgroup.normalizer (gnPre T L : Set X))) :
    S.ρ x = 1 ↔ toStar T x ∈ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
  have hxn : toStar T x ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
    mem_normalizer_gnPre_iff.1 x.2
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hxl : toStar T x * l * (toStar T x)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hxn l).1 hl
    have h2 := S.g_conj x ⟨l, hl⟩ hxl
    rw [h1, one_mul, inv_one, mul_one] at h2
    have h3 : (⟨toStar T x * l * (toStar T x)⁻¹, hxl⟩ : ↥L) = ⟨l, hl⟩ :=
      S.g_bij.1 (Subtype.ext h2)
    have h4 : toStar T x * l * (toStar T x)⁻¹ = l := congrArg Subtype.val h3
    exact (mul_inv_eq_iff_eq_mul.1 h4).symm
  · intro hc
    refine CFSG.CGT.PushingUpLit.BHS.eq_one_of_commute_alt hn fun σ hσ => ?_
    obtain ⟨l, hl⟩ := S.g_bij.2 ⟨σ, hσ⟩
    have hlσ : (g l : Perm (Fin n)) = σ := congrArg Subtype.val hl
    have hxl : toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hxn l).1 l.2
    have h2 := S.g_conj x l hxl
    have h3 : toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹ = (l : X ⧸ gnC T) := by
      have := Subgroup.mem_centralizer_iff.1 hc l l.2
      exact mul_inv_eq_iff_eq_mul.2 this.symm
    have h4 : (⟨toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹, hxl⟩ : ↥L) = l := Subtype.ext h3
    rw [h4, hlσ] at h2
    have h5 : σ = S.ρ x * σ * (S.ρ x)⁻¹ := h2
    calc S.ρ x * σ = (S.ρ x * σ * (S.ρ x)⁻¹) * S.ρ x := by group
      _ = σ * S.ρ x := by rw [← h5]

theorem R_spec (hX : GNSetting X T) {a b : Fin n} (hab : a ≠ b) (hs : swap a b ∈ S.J) :
    baum T ≤ S.R a b ∧ S.R a b ≤ T ∧ pCoreOf 2 (⊤ : Subgroup X) ≤ S.R a b ∧
      T ⊓ gnC T ≤ S.R a b := by
  have hBR : baum T ≤ S.R a b := by
    intro x hx
    refine (S.mem_R_iff).2 ⟨hx.1, S.baum_le hx, ?_⟩
    exact mem_swapPairStab_of_commute hab (S.J_comm _ (S.baum_map_mem_J hx) _ hs)
  have hCR : T ⊓ gnC T ≤ S.R a b := by
    rintro x ⟨hxT, hxC⟩
    have hx1 : toStar T x = 1 := (QuotientGroup.eq_one_iff x).2 hxC
    have hxN : x ∈ Subgroup.normalizer (gnPre T L : Set X) :=
      mem_normalizer_gnPre_iff.2 (by rw [hx1]; exact Subgroup.one_mem _)
    refine (S.mem_R_iff).2 ⟨hxT, hxN, ?_⟩
    rw [S.ρ_C ⟨x, hxN⟩ hxC]
    exact Subgroup.one_mem _
  have hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ S.R a b :=
    (le_inf (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow) (pCoreOf_le_gnC hX)).trans hCR
  exact ⟨hBR, inf_le_left, hQR, hCR⟩

omit [Finite X] in
theorem threeElement_spec {a b c₀ : Fin n} (hab : a ≠ b) (hc₀ : ∀ q ∈ S.Q, q c₀ = c₀)
    (hs : swap a b ∈ S.J) {ℓ : ↥L} (hgℓ : (g ℓ : Perm (Fin n)) = swap a b * swap b c₀) :
    orderOf (ℓ : X ⧸ gnC T) = 3 ∧
      gnImg T (S.R a b) ≤ Subgroup.normalizer (Subgroup.zpowers (ℓ : X ⧸ gnC T) : Set (X ⧸ gnC T)) ∧
      ¬ Subgroup.zpowers (ℓ : X ⧸ gnC T) ≤
        Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) := by
  classical
  obtain ⟨hca, hcb⟩ := S.fixed_ne hab hc₀ hs
  have hbc : b ≠ c₀ := hcb.symm
  have hac : a ≠ c₀ := hca.symm
  have h3 : (swap a b * swap b c₀).IsThreeCycle := by
    rw [swap_comm a b]
    exact isThreeCycle_swap_mul_swap_same hab.symm hbc hac
  have hord : orderOf (ℓ : X ⧸ gnC T) = 3 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective g S.g_bij.1 ℓ, ← Subgroup.orderOf_coe, hgℓ,
      h3.orderOf]
  have hnorm0 : ∀ r ∈ S.R a b,
      toStar T r * (ℓ : X ⧸ gnC T) * (toStar T r)⁻¹ ∈ Subgroup.zpowers (ℓ : X ⧸ gnC T) := by
    intro r hr
    obtain ⟨hrT, hrN, hρσ⟩ := (S.mem_R_iff).1 hr
    have hrQ : S.ρ ⟨r, hrN⟩ ∈ S.Q :=
      ⟨⟨r, hrN⟩, Subgroup.mem_subgroupOf.2 ⟨hrT, hrN⟩, rfl⟩
    have hσc := hc₀ _ hrQ
    have htN : toStar T r ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
      mem_normalizer_gnPre_iff.1 hrN
    have hyL : toStar T r * (ℓ : X ⧸ gnC T) * (toStar T r)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 htN ℓ).1 ℓ.2
    have hg1 := S.g_conj ⟨r, hrN⟩ ℓ hyL
    rw [hgℓ] at hg1
    rcases swapMulSwap_conj_mem hab hbc hac hρσ hσc with h | h
    · have h1 : (⟨_, hyL⟩ : ↥L) = ℓ :=
        S.g_bij.1 (Subtype.ext (by rw [hg1, h, hgℓ]))
      have h2 : toStar T r * (ℓ : X ⧸ gnC T) * (toStar T r)⁻¹ = (ℓ : X ⧸ gnC T) :=
        congrArg Subtype.val h1
      rw [h2]
      exact Subgroup.mem_zpowers _
    · have h1 : (⟨_, hyL⟩ : ↥L) = ℓ⁻¹ :=
        S.g_bij.1 (Subtype.ext (by rw [hg1, h, map_inv, Subgroup.coe_inv, hgℓ]))
      have h2 : toStar T r * (ℓ : X ⧸ gnC T) * (toStar T r)⁻¹ = (ℓ : X ⧸ gnC T)⁻¹ :=
        congrArg Subtype.val h1
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hnorm : gnImg T (S.R a b) ≤
      Subgroup.normalizer (Subgroup.zpowers (ℓ : X ⧸ gnC T) : Set (X ⧸ gnC T)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      have := Subgroup.zpow_mem _ (hnorm0 r hr) i
      rwa [conj_zpow] at this
    · intro hh
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hh
      have h4 : h = (toStar T r⁻¹ * (ℓ : X ⧸ gnC T) * (toStar T r⁻¹)⁻¹) ^ i := by
        rw [map_inv, conj_zpow, hi]
        group
      rw [h4]
      exact Subgroup.zpow_mem _ (hnorm0 r⁻¹ ((S.R a b).inv_mem hr)) i
  have hnotB : ¬ Subgroup.zpowers (ℓ : X ⧸ gnC T) ≤
      Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) := by
    intro hcB
    have hcN := hcB (Subgroup.mem_zpowers _)
    obtain ⟨x, hxJ, hxs⟩ := hs
    have hxB : (x : X) ∈ baum T := B6.thompsonJ_le_baum T (Subgroup.mem_subgroupOf.1 hxJ)
    have h1 : (ℓ : X ⧸ gnC T) * toStar T x * (ℓ : X ⧸ gnC T)⁻¹ ∈ gnImg T (baum T) :=
      (Subgroup.mem_normalizer_iff.1 hcN (toStar T x)).1 (Subgroup.mem_map_of_mem _ hxB)
    obtain ⟨z, hzB, hz⟩ := Subgroup.mem_map.1 h1
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (ℓ : X ⧸ gnC T)
    have hkK : k ∈ gnPre T L := by
      show toStar T k ∈ L
      rw [show toStar T k = (ℓ : X ⧸ gnC T) from hk]
      exact ℓ.2
    have hkN : k ∈ Subgroup.normalizer (gnPre T L : Set X) := Subgroup.le_normalizer hkK
    have hzN : z ∈ Subgroup.normalizer (gnPre T L : Set X) := S.baum_le hzB
    have hyN : k * (x : X) * k⁻¹ ∈ Subgroup.normalizer (gnPre T L : Set X) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN x.2) (Subgroup.inv_mem _ hkN)
    have hzy : toStar T (z⁻¹ * (k * (x : X) * k⁻¹)) = 1 := by
      have hz' : toStar T z = (ℓ : X ⧸ gnC T) * toStar T x * (ℓ : X ⧸ gnC T)⁻¹ := hz
      rw [map_mul, map_inv, hz', map_mul, map_mul, map_inv, show toStar T k = (ℓ : X ⧸ gnC T) from hk]
      group
    have hzyC : z⁻¹ * (k * (x : X) * k⁻¹) ∈ gnC T := (QuotientGroup.eq_one_iff _).1 hzy
    have hzyN : z⁻¹ * (k * (x : X) * k⁻¹) ∈ Subgroup.normalizer (gnPre T L : Set X) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hzN) hyN
    have hρ1 := S.ρ_C ⟨_, hzyN⟩ hzyC
    have hρz : S.ρ ⟨z, hzN⟩ = S.ρ ⟨k * (x : X) * k⁻¹, hyN⟩ := by
      have : (⟨z⁻¹ * (k * (x : X) * k⁻¹), hzyN⟩ :
          ↥(Subgroup.normalizer (gnPre T L : Set X))) = ⟨z, hzN⟩⁻¹ * ⟨k * (x : X) * k⁻¹, hyN⟩ := rfl
      rw [this, map_mul, map_inv] at hρ1
      exact (inv_mul_eq_one.1 hρ1)
    have hρk : S.ρ ⟨k, hkN⟩ = swap a b * swap b c₀ := by
      have := S.ρ_pre ⟨k, hkK⟩ (show toStar T k ∈ L from hkK)
      have h6 : (⟨toStar T k, show toStar T k ∈ L from hkK⟩ : ↥L) = ℓ := Subtype.ext hk
      rw [h6, hgℓ] at this
      exact this
    have hρy : S.ρ ⟨k * (x : X) * k⁻¹, hyN⟩ = swap b c₀ := by
      have : (⟨k * (x : X) * k⁻¹, hyN⟩ : ↥(Subgroup.normalizer (gnPre T L : Set X))) =
          ⟨k, hkN⟩ * x * ⟨k, hkN⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hρk, hxs, ← swap_apply_apply]
      have ha : (swap a b * swap b c₀) a = b := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hac, swap_apply_left]
      have hb : (swap a b * swap b c₀) b = c₀ := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hca hcb]
      rw [ha, hb]
    have hzJ : S.ρ ⟨z, hzN⟩ ∈ S.J := S.baum_map_mem_J hzB
    have hfix2 := hc₀ _ (S.J_le_Q hzJ)
    rw [hρz, hρy, swap_apply_right] at hfix2
    exact hbc hfix2
  exact ⟨hord, hnorm, hnotB⟩

theorem threeElement_not_normalizes (hX : GNSetting X T) {a b c₀ : Fin n} (hab : a ≠ b)
    (hc₀ : ∀ q ∈ S.Q, q c₀ = c₀) (hs : swap a b ∈ S.J) {ℓ : ↥L}
    (hgℓ : (g ℓ : Perm (Fin n)) = swap a b * swap b c₀) :
    ¬ Subgroup.zpowers (ℓ : X ⧸ gnC T) ≤
      Subgroup.normalizer (gnImg T (S.R a b) : Set (X ⧸ gnC T)) := by
  obtain ⟨hord, hnorm, hnotB⟩ := S.threeElement_spec hab hc₀ hs hgℓ
  obtain ⟨hB, hT, -, -⟩ := S.R_spec hX hab hs
  have hRsp : IsPGroup 2 (gnImg T (S.R a b)) :=
    (hX.sylow.2.1.to_le hT).map (QuotientGroup.mk' (gnC T))
  exact not_zpowers_le_normalizer_of_le hRsp hord hnorm (Subgroup.map_mono hB) hnotB

theorem outcome_of_swap (hX : GNSetting X T) {T₁ T₂ : Subgroup X} (hP : IsC118Pair T T₁ T₂)
    {a b c₀ : Fin n} (hab : a ≠ b) (hc₀ : ∀ q ∈ S.Q, q c₀ = c₀) (hs : swap a b ∈ S.J)
    {ℓ : ↥L} (hgℓ : (g ℓ : Perm (Fin n)) = swap a b * swap b c₀) :
    (ℓ : X ⧸ gnC T) ∈ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      (ℓ : X ⧸ gnC T) ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ∨
      ∃ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H ∧ IsBlock2 H Kb ∧ IsAltType Kb 3 ∧
        ¬ Kb ≤ gnC T ∧ gnImg T Kb = Subgroup.zpowers (ℓ : X ⧸ gnC T) := by
  obtain ⟨hord, hnorm, -⟩ := S.threeElement_spec hab hc₀ hs hgℓ
  obtain ⟨hB, hT, hQ, hC⟩ := S.R_spec hX hab hs
  exact threeElement_dichotomy hX hP hB hT hQ hC hord hnorm
    (S.threeElement_not_normalizes hX hab hc₀ hs hgℓ)

theorem outcome_of_swap_sharp (hX : GNSetting X T) {T₁ T₂ : Subgroup X}
    (hP : IsC118Pair T T₁ T₂) :
    ∃ C : Subgroup X, C ≤ baum T ∧ (C.subgroupOf (baum T)).Characteristic ∧
      C ≤ omegaOneCenterOf (baum T) ∧ T₁ ≤ C ⊓ gnV T ∧
      ∀ {a b c₀ : Fin n}, a ≠ b → (∀ q ∈ S.Q, q c₀ = c₀) → swap a b ∈ S.J → ∀ {ℓ : ↥L},
        (g ℓ : Perm (Fin n)) = swap a b * swap b c₀ →
        (ℓ : X ⧸ gnC T) ∈ gnImg T (Subgroup.centralizer ((C ⊓ gnV T : Subgroup X) : Set X)) ∨
          (ℓ : X ⧸ gnC T) ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ∨
          ∃ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H ∧ IsBlock2 H Kb ∧ IsAltType Kb 3 ∧
            ¬ Kb ≤ gnC T ∧ gnImg T Kb = Subgroup.zpowers (ℓ : X ⧸ gnC T) := by
  obtain ⟨C, hCB, hCc, hCΩ, -, hT₁D, hmain⟩ := exists_threeElement_dichotomy_sharp hX hP
  refine ⟨C, hCB, hCc, hCΩ, hT₁D, fun {a b c₀} hab hc₀ hs {ℓ} hgℓ => ?_⟩
  obtain ⟨hord, hnorm, hnotB⟩ := S.threeElement_spec hab hc₀ hs hgℓ
  obtain ⟨hB, hT, -, hC⟩ := S.R_spec hX hab hs
  exact hmain hB hT hC hord hnorm hnotB

omit [Finite X] in
theorem existsUnique_fixed (hodd : Odd n) : ∃! c : Fin n, ∀ q ∈ S.Q, q c = c :=
  existsUnique_fixed_of_sylowTwo hodd S.sylow.1 S.sylow.2

omit [Finite X] in
theorem conj_mem_J {q s : Perm (Fin n)} (hq : q ∈ S.Q) (hs : s ∈ S.J) : q * s * q⁻¹ ∈ S.J := by
  obtain ⟨x, hx, rfl⟩ := hq
  obtain ⟨j, hj, rfl⟩ := hs
  have hxT : (x : X) ∈ T := (Subgroup.mem_subgroupOf.1 hx).1
  have hxJ : (x : X) ∈ Subgroup.normalizer (thompsonJ T : Set X) :=
    normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer hxT)
  have hxjJ : (x : X) * (j : X) * (x : X)⁻¹ ∈ thompsonJ T :=
    (Subgroup.mem_normalizer_iff.1 hxJ (j : X)).1 (Subgroup.mem_subgroupOf.1 hj)
  exact ⟨x * j * x⁻¹, Subgroup.mem_subgroupOf.2 hxjJ, by rw [map_mul, map_mul, map_inv]⟩

@[expose] def JAllSwaps : Prop := ∀ s ∈ S.Q, s.IsSwap → s ∈ S.J

omit [Finite X] in
theorem jAllSwaps_of_two_pow_succ {m : ℕ} (hm : 1 ≤ m) (hn : n = 2 ^ m + 1) : S.JAllSwaps := by
  subst hn
  intro s hsQ hsw
  obtain ⟨T', ⟨s₀, hs₀⟩, hT's, -, hT'J⟩ := S.J_swaps
  have hs₀J : s₀ ∈ S.J := by
    have hJ : S.J = Subgroup.closure T' := hT'J
    rw [hJ]
    exact Subgroup.subset_closure hs₀
  obtain ⟨a, b, hab, rfl⟩ := hT's s₀ hs₀
  obtain ⟨a', b', hab', rfl⟩ := hsw
  obtain ⟨t, htQ, hconj⟩ := exists_conj_swap_eq_of_sylowTwo_two_pow_succ hm S.sylow.1 S.sylow.2
    hab hab' (S.J_le_Q hs₀J) hsQ
  have := S.conj_mem_J htQ hs₀J
  rwa [hconj] at this

omit [Finite X] in
theorem le_of_threeElements (hn : 5 ≤ n) (hall : S.JAllSwaps) {c₀ : Fin n}
    (hc₀ : ∀ q ∈ S.Q, q c₀ = c₀) {H : Subgroup (X ⧸ gnC T)}
    (hH : ∀ (a b : Fin n), a ≠ b → swap a b ∈ S.J → ∀ ℓ : ↥L,
      (g ℓ : Perm (Fin n)) = swap a b * swap b c₀ → (ℓ : X ⧸ gnC T) ∈ H) : L ≤ H := by
  classical
  let f₀ : ↥L →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp g
  have hf₀ : Function.Injective f₀ := (alternatingGroup (Fin n)).subtype_injective.comp S.g_bij.1
  have hcl := closure_swap_mul_swap_eq_alternating_of_sylowTwo hn S.sylow.1 S.sylow.2 hc₀
  let C₃ : Set ↥L := {ℓ | ∃ a b : Fin n, a ≠ b ∧ swap a b ∈ S.Q ∧
    (g ℓ : Perm (Fin n)) = swap a b * swap b c₀}
  have himg : f₀ '' C₃ = {σ | ∃ a b : Fin n, a ≠ b ∧ swap a b ∈ S.Q ∧ σ = swap a b * swap b c₀} := by
    ext σ
    constructor
    · rintro ⟨ℓ, ⟨a, b, hab, hQ, h⟩, rfl⟩
      exact ⟨a, b, hab, hQ, h⟩
    · rintro ⟨a, b, hab, hQ, rfl⟩
      have hfix := hc₀ _ hQ
      have hca : c₀ ≠ a := fun h => by
        rw [h, swap_apply_left] at hfix
        exact hab hfix.symm
      have hcb : c₀ ≠ b := fun h => by
        rw [h, swap_apply_right] at hfix
        exact hab hfix
      have hτ : swap a b * swap b c₀ ∈ alternatingGroup (Fin n) := by
        rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcb.symm]
        decide
      obtain ⟨ℓ, hℓ⟩ := S.g_bij.2 ⟨swap a b * swap b c₀, hτ⟩
      exact ⟨ℓ, ⟨a, b, hab, hQ, congrArg Subtype.val hℓ⟩, congrArg Subtype.val hℓ⟩
  have hrange : Subgroup.map f₀ ⊤ = alternatingGroup (Fin n) := by
    ext σ
    constructor
    · rintro ⟨l, -, rfl⟩
      exact (g l).2
    · intro hσ
      obtain ⟨l, hl⟩ := S.g_bij.2 ⟨σ, hσ⟩
      exact ⟨l, Subgroup.mem_top _, by simp [f₀, hl]⟩
  have hclos : Subgroup.closure C₃ = ⊤ := by
    apply Subgroup.map_injective hf₀
    rw [MonoidHom.map_closure, himg, hrange]
    exact hcl
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ Subgroup.closure C₃ := by rw [hclos]; exact Subgroup.mem_top _
  have hle : Subgroup.closure C₃ ≤ H.comap L.subtype := by
    rw [Subgroup.closure_le]
    rintro ℓ ⟨a, b, hab, hQ, h⟩
    exact hH a b hab (hall _ hQ ⟨a, b, hab, rfl⟩) ℓ h
  exact hle hy'

omit [Finite X] in
theorem conj_threeElement {a b a' b' c₀ : Fin n} {x : ↥(Subgroup.normalizer (gnPre T L : Set X))}
    (hx : S.ρ x c₀ = c₀) (ha : S.ρ x a = a') (hb : S.ρ x b = b') {ℓ ℓ' : ↥L}
    (hgℓ : (g ℓ : Perm (Fin n)) = swap a b * swap b c₀)
    (hgℓ' : (g ℓ' : Perm (Fin n)) = swap a' b' * swap b' c₀)
    (hxl : toStar T x * (ℓ : X ⧸ gnC T) * (toStar T x)⁻¹ ∈ L) :
    toStar T x * (ℓ : X ⧸ gnC T) * (toStar T x)⁻¹ = (ℓ' : X ⧸ gnC T) := by
  have h1 := S.g_conj x ℓ hxl
  have h2 : (g ⟨toStar T x * (ℓ : X ⧸ gnC T) * (toStar T x)⁻¹, hxl⟩ : Perm (Fin n)) =
      swap a' b' * swap b' c₀ := by
    rw [h1, hgℓ]
    have e : S.ρ x * (swap a b * swap b c₀) * (S.ρ x)⁻¹ =
        swap (S.ρ x a) (S.ρ x b) * swap (S.ρ x b) (S.ρ x c₀) := by
      rw [swap_apply_apply, swap_apply_apply]
      group
    rw [e, ha, hb, hx]
  have h3 : (⟨toStar T x * (ℓ : X ⧸ gnC T) * (toStar T x)⁻¹, hxl⟩ : ↥L) = ℓ' :=
    S.g_bij.1 (Subtype.ext (h2.trans hgℓ'.symm))
  exact congrArg Subtype.val h3

end GNAltModData

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
