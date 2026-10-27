module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneProjectiveEightLayer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageChain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageZero

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
  CFSG.Blueprint
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 goldschmidt1974_of_milestone)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Chain

variable {G : Type} [Group G]

theorem LinearPushChain.le_of_le {t d : G} {T A : Subgroup G} {f m : ℕ} {C : ℕ → Subgroup G}
    (h : LinearPushChain t d T A f m C) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m + 1) :
    C a ≤ C b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (h.mono b (by omega))

variable [Finite G]

theorem LinearPushChain.exists_conj_eq_mul {t d : G} {T A : Subgroup G} {f m : ℕ}
    {C : ℕ → Subgroup G} (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m) :
    ∀ c ∈ C m, ∃ g : G, g⁻¹ * t * g = t * c := by
  classical
  set J : Set G := (fun s => s * t * s⁻¹) '' (C (m + 1) : Set G) with hJ
  set I : Set G := (fun c => c * t) '' (C m : Set G) with hI
  have hJI : J ⊆ I := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s * t * s⁻¹ * t⁻¹, h.comm_t m hm le_rfl s hs, by group⟩
  have hcount := card_le_mul_card_inf_centralizer_of_conj_mem (C (m + 1)) t J
    (fun s hs => ⟨s, hs, rfl⟩)
  rw [h.centralizer_t, ← h.base, h.card 1 (by omega), h.card (m + 1) le_rfl, mul_one] at hcount
  have hIc : I.ncard ≤ 2 ^ (f * m) := by
    calc I.ncard ≤ (C m : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 2 ^ (f * m) := by rw [← Nat.card_coe_set_eq]; exact h.card m (by omega)
  have hJc : 2 ^ (f * m) ≤ J.ncard := by
    rw [← Nat.card_coe_set_eq]
    have e : 2 ^ (f * (m + 1)) = 2 ^ (f * m) * 2 ^ f := by rw [← pow_add]; ring_nf
    rw [e] at hcount
    exact Nat.le_of_mul_le_mul_right hcount (by positivity)
  have hJeq : J = I := Set.eq_of_subset_of_ncard_le hJI (hIc.trans hJc)
  intro c hc
  have htc : t * c ∈ I :=
    ⟨t * c * t⁻¹, (mem_normalizer_iff.mp (h.t_norm m (by omega)) c).mp hc, by group⟩
  rw [← hJeq] at htc
  obtain ⟨s, -, hst⟩ := htc
  exact ⟨s⁻¹, by simpa using hst⟩

omit [Finite G] in
theorem LinearPushChain.mem_iff_pow_two_pow_eq_one {t d : G} {T A : Subgroup G} {f m : ℕ}
    {C : ℕ → Subgroup G} (h : LinearPushChain t d T A f m C)
    (hinv : ∀ u ∈ C (m + 1), t * u * t⁻¹ = u⁻¹) :
    ∀ j ≤ m + 1, ∀ x ∈ C (m + 1), x ∈ C j ↔ x ^ 2 ^ j = 1 := by
  have hcomm : ∀ x ∈ C (m + 1), x * t * x⁻¹ * t⁻¹ = x * x := by
    intro x hx
    have h1 : x * t * x⁻¹ * t⁻¹ = x * (t * x * t⁻¹)⁻¹ := by group
    rw [h1, hinv x hx, inv_inv]
  intro j
  induction j with
  | zero =>
    intro _ x _
    rw [h.zero, mem_bot, pow_zero, pow_one]
  | succ j ih =>
    intro hj x hx
    constructor
    · intro hxj
      have h1 := (ih (by omega) (x * x) (mul_mem hx hx)).mp (h.layer_sq j (by omega) x hxj)
      rw [← sq, ← pow_mul] at h1
      rw [pow_succ, mul_comm]
      exact h1
    · intro hx1
      have hxx : x * x ∈ C j := (ih (by omega) (x * x) (mul_mem hx hx)).mpr (by
        rw [← sq, ← pow_mul, mul_comm, ← pow_succ]
        exact hx1)
      have hdown : ∀ e : ℕ, j + 1 + e ≤ m + 1 → x ∈ C (j + 1 + e) → x ∈ C (j + 1) := by
        intro e
        induction e with
        | zero => exact fun _ hx' => hx'
        | succ e ihe =>
          intro he hxe
          apply ihe (by omega)
          have h2 := h.comm_t_ker (j + 1 + e) (by omega) (by omega) x hxe (by
            rw [hcomm x hx]
            exact h.le_of_le (show j ≤ j + 1 + e - 1 by omega) (by omega) hxx)
          exact h2
      have h3 := hdown (m - j) (by omega) (by rwa [show j + 1 + (m - j) = m + 1 by omega])
      exact h3

omit [Finite G] in
theorem LinearPushChain.normalizer_le_pushNormalizer {t d : G} {T A : Subgroup G} {f m : ℕ}
    {C : ℕ → Subgroup G} (h : LinearPushChain t d T A f m C)
    (hinv : ∀ u ∈ C (m + 1), t * u * t⁻¹ = u⁻¹) :
    normalizer (C (m + 1) : Set G) ≤ pushNormalizer C (m + 2) := by
  intro g hg
  rw [mem_pushNormalizer_iff]
  intro j hj
  have hΩ := h.mem_iff_pow_two_pow_eq_one hinv j (by omega)
  have hle : C j ≤ C (m + 1) := h.le_of_le (by omega) le_rfl
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hgx : g * x * g⁻¹ ∈ C (m + 1) := (mem_normalizer_iff.mp hg x).mp (hle hx)
    rw [hΩ _ hgx, conj_pow, (hΩ x (hle hx)).mp hx]
    group
  · intro hx
    have hx' : x ∈ C (m + 1) := (mem_normalizer_iff.mp hg x).mpr (hle hx)
    rw [hΩ x hx']
    have h1 := (hΩ _ (hle hx)).mp hx
    rw [conj_pow] at h1
    calc x ^ 2 ^ j = g⁻¹ * (g * x ^ 2 ^ j * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

end Chain

theorem SmallRootStage.sq_eq_one_of_commute_of_degree_eight {D : Type} [Group D] [Finite D]
    {R X U P : Subgroup D} (h : SmallRootStage R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) {t : D} (htR : t ∈ R) (ht1 : t ≠ 1)
    {x : D} (hxt : x * t = t * x) (hx2 : ∃ j : ℕ, x ^ 2 ^ j = 1) : x * x = 1 := by
  have hodd : Odd (Nat.card (gmsPermStabilizer U R)) := by
    obtain ⟨-, -, hd, -⟩ := gms_normal_root_degree_eight_completion h.1 h3
    rw [card_gmsPermStabilizer h.1 h3]
    rcases hd with h1 | h1 <;> rw [h1] <;> decide
  exact sq_eq_one_of_commute_of_odd_card_gmsPermStabilizer (h.setup h3 htR ht1)
    h.normalizer_inf_centralizer hodd hxt hx2

section State

variable {G : Type} [Group G] [Finite G]

theorem PushState.exists_normal_index_two_of_projectiveEight {t : G} {T A X : Subgroup G}
    {k : ℕ} {d : G} {C : ℕ → Subgroup G} (ht : orderOf t = 2) (h : PushState t T A 3 k d C X)
    (hproj : ∀ [((C k).subgroupOf (pushNormalizer C (k + 1))).Normal],
      GMSProjectiveEight
        (((C (k + 1)).subgroupOf (pushNormalizer C (k + 1))).map
          (QuotientGroup.mk' ((C k).subgroupOf (pushNormalizer C (k + 1)))))
        (((C k ⊔ zpowers t).subgroupOf (pushNormalizer C (k + 1))).map
          (QuotientGroup.mk' ((C k).subgroupOf (pushNormalizer C (k + 1))))))
    (hCt : 1 ≤ k → ∀ x : G, x * t = t * x → (∃ j : ℕ, x ^ 2 ^ j = 1) → x * x = 1) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = 2 := by
  obtain ⟨hch, -, hst⟩ := h
  have : ((C k).subgroupOf (pushNormalizer C (k + 1))).Normal := hst.1
  have hproj' : GMSProjectiveEight (relImg (pushNormalizer C (k + 1)) (C k) (C (k + 1)))
      (relImg (pushNormalizer C (k + 1)) (C k) (C k ⊔ zpowers t)) := hproj
  have h3 := ncard_eq_eight_of_projectiveEight hproj'
  have htt : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  rcases Nat.eq_zero_or_pos k with rfl | hk
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, hS⟩ := id hst
    have hS := @hS inferInstance
    obtain ⟨M, hMn, hMi⟩ :=
      hS.exists_normal_index_two_of_projectiveEight (by rw [h3]; norm_num) hproj'
    have hN1 : pushNormalizer C (0 + 1) = ⊤ := pushNormalizer_one hch.zero
    let ι : G →* ↥(pushNormalizer C (0 + 1)) :=
      (MonoidHom.id G).codRestrict _ fun g => by rw [hN1]; exact mem_top g
    let ψ := (QuotientGroup.mk' ((C 0).subgroupOf (pushNormalizer C (0 + 1)))).comp ι
    have hψ : Function.Surjective ψ := fun z => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
      exact ⟨x, rfl⟩
    exact ⟨M.comap ψ, hMn.comap ψ, (index_comap_of_surjective (H := M) hψ).trans hMi⟩
  ·
    have hW2 : IsPGroup 2 (C k) := IsPGroup.of_card (hch.card k (by omega))
    have hW := hch.exists_conj_eq_mul hk
    have htW : t ∉ C k := fun h1 => hch.t_not_mem (hch.mono k le_rfl h1)
    have hconj := hst.exists_conj_eq_mul (by rw [h3]; norm_num) (mem_sup_right (mem_zpowers t))
      htW hW
    have hinv := inv_of_forall_conj_eq_mul htt hconj
    have hN : normalizer (C (k + 1) : Set G) ≤ pushNormalizer C (k + 1) :=
      (hch.normalizer_le_pushNormalizer hinv).trans (pushNormalizer_antitone C (by omega))
    have hUt : ∀ u ∈ C (k + 1), u * t = t * u → u ∈ C k := by
      intro u hu hut
      have h1 : u ∈ C (k + 1) ⊓ centralizer ({t} : Set G) :=
        mem_inf.mpr ⟨hu, mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]; exact hut.symm⟩
      rw [hch.centralizer_t, ← hch.base] at h1
      exact hch.le_of_le hk (by omega) h1
    exact exists_normal_index_two_of_relSmallRootStage_projectiveEight hst hproj' htt hW2 hW hN
      hUt (hCt hk)

theorem PushState.false_of_projectiveEight [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {t : G} {T A X : Subgroup G} {k : ℕ} {d : G} {C : ℕ → Subgroup G} (ht : orderOf t = 2)
    (h : PushState t T A 3 k d C X)
    (hproj : ∀ [((C k).subgroupOf (pushNormalizer C (k + 1))).Normal],
      GMSProjectiveEight
        (((C (k + 1)).subgroupOf (pushNormalizer C (k + 1))).map
          (QuotientGroup.mk' ((C k).subgroupOf (pushNormalizer C (k + 1)))))
        (((C k ⊔ zpowers t).subgroupOf (pushNormalizer C (k + 1))).map
          (QuotientGroup.mk' ((C k).subgroupOf (pushNormalizer C (k + 1))))))
    (hCt : 1 ≤ k → ∀ x : G, x * t = t * x → (∃ j : ℕ, x ^ 2 ^ j = 1) → x * x = 1) : False :=
  Endings.not_exists_normal_index_two hnab
    (h.exists_normal_index_two_of_projectiveEight ht hproj hCt)

end State

section Loop

variable {G : Type} [Group G] [Finite G]

theorem PushState.terminates_state [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hHKS : SmallRootRegularNormalInput)
    {t : G} (ht : orderOf t = 2) {T A : Subgroup G} {f : ℕ} (hf : 1 ≤ f) {d : G}
    (hT2 : IsPGroup 2 T) (hT0 : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) (hAT : A ≤ T) :
    ∀ (s k : ℕ) (C : ℕ → Subgroup G) (X : Subgroup G), Nat.card G ≤ k + s →
      PushState t T A f k d C X →
      ∃ (C' : ℕ → Subgroup G) (m : ℕ) (X' : Subgroup G), PushState t T A f m d C' X' ∧
        ((1 ≤ m ∧ ABGLocalTools.IsSylowOf 2 (C' (m + 1) ⊔ T) (pushNormalizer C' (m + 1))) ∨
          (f = 3 ∧ ∀ [((C' m).subgroupOf (pushNormalizer C' (m + 1))).Normal],
            GMSProjectiveEight
              (((C' (m + 1)).subgroupOf (pushNormalizer C' (m + 1))).map
                (QuotientGroup.mk' ((C' m).subgroupOf (pushNormalizer C' (m + 1)))))
              (((C' m ⊔ zpowers t).subgroupOf (pushNormalizer C' (m + 1))).map
                (QuotientGroup.mk' ((C' m).subgroupOf (pushNormalizer C' (m + 1))))))) := by
  intro s
  induction s with
  | zero =>
    intro k C X hk h
    exfalso
    have h1 : Nat.card (C (k + 1)) ≤ Nat.card G := Subgroup.card_le_card_group _
    rw [h.chain.card (k + 1) le_rfl] at h1
    have h2 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (k + 1) ≤ 2 ^ (f * (k + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hf)
    omega
  | succ s ih =>
    intro k C X hk h
    rcases h.next hnab hK hHKS ht hT2 hT0 hAT with hstop | ⟨C', X', h'⟩
    · exact ⟨C, k, X, h, hstop⟩
    · exact ih (k + 1) C' X' (by omega) h'

end Loop

section Main

variable {G : Type} [Group G] [Finite G]

theorem psl2_pushing_up_sylow_of_stage {L : Subgroup G} (h : SeitzSetting G L) {f : ℕ}
    (hf : 3 ≤ f) {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    {T : Subgroup G} (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G)))
    (h0 : SmallRootStage (zpowers t) L (T ⊓ L) T f) (hT0 : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T)
    (hHKS : SmallRootRegularNormalInput) :
    ∃ d : G, d ∈ L ∧ (∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1) ∧
      ∃ C : ℕ → Subgroup G, ∃ m : ℕ, LinearPushChain t d T (T ⊓ L) f m C ∧
        1 ≤ m ∧ ABGLocalTools.IsSylowOf 2 (C (m + 1) ⊔ T) (pushNormalizer C (m + 1)) := by
  obtain ⟨hsimple, hnab, hK, -⟩ := h
  have hT2 : IsPGroup 2 T := by
    obtain ⟨P, hP⟩ := hT
    have h1 : IsPGroup 2 (T.subgroupOf (normalizer (zpowers t : Set G))) := hP ▸ P.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hTN)
  obtain ⟨d, C, hst, hdfix⟩ := pushState_zero ht htC h0
  have hdL : d ∈ L := hst.d_mem
  obtain ⟨C', m, X', hst', hout⟩ := PushState.terminates_state hnab hK hHKS ht (by omega) hT2 hT0
    inf_le_left (Nat.card G) 0 C L (by omega) hst
  refine ⟨d, hdL, hdfix, C', m, hst'.chain, ?_⟩
  rcases hout with hstop | ⟨hf3, hproj⟩
  · exact hstop
  · exfalso
    subst hf3
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; exact absurd ht (by norm_num)
    have h3 : 3 ≤ (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t)).ncard :=
      ((smallRoot_sylow_alternative h0).2.resolve_left fun h1 => hT0 h1.1).2
    have hCt : ∀ x : G, x * t = t * x → (∃ j : ℕ, x ^ 2 ^ j = 1) → x * x = 1 :=
      fun x hxt hx2 => h0.sq_eq_one_of_commute_of_degree_eight h3 (mem_zpowers t) ht1 hxt hx2
    exact hst'.false_of_projectiveEight hnab ht hproj fun _ => hCt

theorem psl2_pushing_up_sylow_of_goldschmidt
    (hGold : Goldschmidt1974) {L : Subgroup G}
    (h : SeitzSetting G L) {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {T : Subgroup G}
    (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G)))
    (hHKS : SmallRootRegularNormalInput) :
    ∃ d : G, d ∈ L ∧ (∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1) ∧
      ∃ C : ℕ → Subgroup G, ∃ m : ℕ, LinearPushChain t d T (T ⊓ L) f m C ∧
        1 ≤ m ∧ ABGLocalTools.IsSylowOf 2 (C (m + 1) ⊔ T) (pushNormalizer C (m + 1)) :=
  psl2_pushing_up_sylow_of_stage h hf ht htC hTN hT (psl2_smallRootStage h hf hL ht htC hTN hT)
    (psl2_stage_zero_full_of_goldschmidt hGold h hf hL ht htC hTN hT).2.1 hHKS

end Main

end CFSG.SeitzReduction.RankOne
