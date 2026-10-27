module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinBasic

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Components

variable {G : Type} [Group G]

theorem isComponentIn_conjugate_pair {A H : Subgroup G} (hA : IsComponentIn A H) (g : G) :
    IsComponentIn (CFSG.conjugate A g) (CFSG.conjugate H g) :=
  BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) hA

variable [Finite G]

theorem not_isComponentIn_of_charTwo' {X : Subgroup G} (hX : CharTwo X) (K : Subgroup G) :
    ¬ IsComponentIn K X := by
  intro hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CFSG.IsCharacteristicP 2 ↥X := EscapingLocal.isCharacteristicP_of_charTwo hX
  have hlayer := CFSG.layer_eq_bot_of_isCharacteristicP ↥X 2 hchar
  have hle0 : K.subgroupOf X ≤ CFSG.layer ↥X := le_sSup hK.2
  have hle : K.subgroupOf X ≤ ⊥ := by rw [← hlayer]; exact hle0
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h3 : (⟨g, hK.1 hg⟩ : X) ∈ (⊥ : Subgroup X) := hle hg
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h3))
  have hq : CFSG.IsQuasisimple K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact ((Subgroup.nontrivial_iff_ne_bot K).mp hnt) hKbot

end Components

section Sylow

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G}

theorem Gt_le_normalizer_K (h : Lv2518 N t zK) (hK0 : N.K0 = N.K) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G) := by
  rw [h.concl2518.2.1]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hK0]; exact Subgroup.le_normalizer
  · intro x hx
    have := N.H_le_normalizer_K0 (N.S_le_H hx)
    rwa [hK0] at this
  · intro x hx
    have hx2 : x ∈ Subgroup.centralizer (N.K : Set G) := by
      have := hx.2
      rwa [hK0] at this
    exact Subgroup.centralizer_le_normalizer _ hx2

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {K : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) : m⁻¹ * k * m ∈ K := by
  have := (Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * k * m)).mpr (by
    have e : m * (m⁻¹ * k * m) * m⁻¹ = k := by group
    rw [e]; exact hk)
  exact this

theorem card_le_four (h : Lv2518 N t zK) (hK0 : N.K0 = N.K)
    (hR : ∀ i' : G, Hyp2519 N i' → Rgrp2519 N i' = Subgroup.closure ({t, i'} : Set G))
    {i : G} (hi : Hyp2519 N i) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPt : P ≤ Subgroup.centralizer ({t} : Set G)) (hPK : P ≤ Subgroup.centralizer (N.K : Set G))
    (hPi : P ≤ Subgroup.centralizer ({i} : Set G)) : Nat.card P ≤ 4 := by
  have hf := h.facts2511
  have hi2 : i * i = 1 := hi.mul_self
  have hiord : orderOf i = 2 := orderOf_eq_prime hi.sq_eq_one hi.ne_one
  have hpi : IsPGroup 2 (Subgroup.zpowers i) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hiord]; norm_num)
  have hP' : IsPGroup 2 (P ⊔ Subgroup.zpowers i : Subgroup G) :=
    hP.to_sup_of_normal_right' hpi (by rw [normalizer_zpowers_eq_centralizer hi2]; exact hPi)
  have hiCt : i ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (N.t_comm_of_mem_S hf hi.mem_S).symm
  have hP'le : P ⊔ Subgroup.zpowers i ≤ Subgroup.centralizer ({t} : Set G) :=
    sup_le hPt (Subgroup.zpowers_le.mpr hiCt)
  obtain ⟨m, hm, hms⟩ := EscapingLocal.exists_conj_mem_of_isPGroup (M := Subgroup.centralizer ({t} : Set G))
    (T := N.S) hf.sylow.1 hf.sylow.2.1 hf.sylow.2.2 hP'le hP'
  have hmK : m ∈ Subgroup.normalizer (N.K : Set G) := Gt_le_normalizer_K h hK0 hm
  have hconj := fun {k : G} (hk : k ∈ N.K) => conj_mem_of_mem_normalizer hmK hk
  have hi'S : m * i * m⁻¹ ∈ N.S := hms i (Subgroup.mem_sup_right (Subgroup.mem_zpowers i))
  have hi'K : m * i * m⁻¹ ∈ Subgroup.centralizer (N.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := Subgroup.mem_centralizer_iff.mp hi.mem_centralizer_K _ (hconj hk)
    calc k * (m * i * m⁻¹) = m * ((m⁻¹ * k * m) * i) * m⁻¹ := by group
      _ = m * (i * (m⁻¹ * k * m)) * m⁻¹ := by rw [h1]
      _ = (m * i * m⁻¹) * k := by group
  have hi'1 : m * i * m⁻¹ ≠ 1 := by
    intro h1
    apply hi.ne_one
    calc i = m⁻¹ * (m * i * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  have hi'2 : (m * i * m⁻¹) ^ 2 = 1 := by
    rw [sq]
    calc (m * i * m⁻¹) * (m * i * m⁻¹) = m * (i * i) * m⁻¹ := by group
      _ = 1 := by rw [hi2]; group
  have hnc : ¬ IsComponentIn N.K (Subgroup.centralizer ({m * i * m⁻¹} : Set G)) := by
    intro hcomp
    apply hi.not_comp
    have h1 := isComponentIn_conjugate_pair hcomp m
    have hKm : CFSG.conjugate N.K m = N.K := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hmK
    have hCm : CFSG.conjugate (Subgroup.centralizer ({m * i * m⁻¹} : Set G)) m =
        Subgroup.centralizer ({i} : Set G) := by
      rw [BenderBranch.conjugate_centralizer_singleton]
      congr 2
      group
    rw [hKm, hCm] at h1
    exact h1
  have hi' : Hyp2519 N (m * i * m⁻¹) := ⟨⟨hi'S, hi'K⟩, hi'1, hi'2, hnc⟩
  have hsub : P.map (MulAut.conj m).toMonoidHom ≤ Rgrp2519 N (m * i * m⁻¹) := by
    rintro x ⟨p, hp, hx⟩
    have hxe : x = m * p * m⁻¹ := by rw [← hx]; rfl
    rw [hxe]
    have hpS : m * p * m⁻¹ ∈ N.S := hms p (Subgroup.mem_sup_left hp)
    have hC1 : m * p * m⁻¹ ∈ Subgroup.centralizer ({m * i * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPi hp)
      calc (m * p * m⁻¹) * (m * i * m⁻¹) = m * (p * i) * m⁻¹ := by group
        _ = m * (i * p) * m⁻¹ := by rw [h1]
        _ = (m * i * m⁻¹) * (m * p * m⁻¹) := by group
    have hC2 : m * p * m⁻¹ ∈ Subgroup.centralizer (N.K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := Subgroup.mem_centralizer_iff.mp (hPK hp) _ (hconj hk)
      calc k * (m * p * m⁻¹) = m * ((m⁻¹ * k * m) * p) * m⁻¹ := by group
        _ = m * (p * (m⁻¹ * k * m)) * m⁻¹ := by rw [h1]
        _ = (m * p * m⁻¹) * k := by group
    exact ⟨⟨hpS, hC1⟩, hpS, hC2⟩
  have hcard := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hR _ hi'] at hcard
  exact hcard.trans (hi'.card_closure h).le

theorem exists_swap (h : Lv2518 N t zK) (hK0 : N.K0 = N.K)
    (hR : Rgrp2519 N i = Subgroup.closure ({t, i} : Set G)) (hi : Hyp2519 N i) :
    ∃ s ∈ N.S, s * i * s⁻¹ = t * i := by
  have hf := h.facts2511
  have hti : t * i = i * t := N.t_comm_of_mem_S hf hi.mem_S
  have hne : N.S ⊓ Subgroup.centralizer ({i} : Set G) ≠ N.S := by
    intro heq
    apply hi.not_mem_centerOf_S h
    refine ⟨hi.mem_S, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : s ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G) := by rw [heq]; exact hs
    exact Subgroup.mem_centralizer_singleton_iff.mp hs'.2
  obtain ⟨s, hs, hsn⟩ := EscapingLocal.exists_mem_inf_normalizer_not_mem
    (U := N.S ⊓ Subgroup.centralizer ({i} : Set G)) (V := N.S) N.tuple.sylow.isPGroup inf_le_left hne
  have hsS : s ∈ N.S := hs.1
  have hsni : ¬ s * i = i * s := fun hc =>
    hsn ⟨hsS, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  have hiU : i ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G) :=
    ⟨hi.mem_S, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hsiU : s * i * s⁻¹ ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hs.2 i).mp hiU
  have hsiS : s * i * s⁻¹ ∈ N.S := hsiU.1
  have hsK : s ∈ Subgroup.normalizer (N.K : Set G) := by
    have := N.H_le_normalizer_K0 (N.S_le_H hsS)
    rwa [hK0] at this
  have hsiK : s * i * s⁻¹ ∈ Subgroup.centralizer (N.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : s⁻¹ * k * s ∈ N.K := conj_mem_of_mem_normalizer hsK hk
    have h1 := Subgroup.mem_centralizer_iff.mp hi.mem_centralizer_K _ hk'
    calc k * (s * i * s⁻¹) = s * ((s⁻¹ * k * s) * i) * s⁻¹ := by group
      _ = s * (i * (s⁻¹ * k * s)) * s⁻¹ := by rw [h1]
      _ = (s * i * s⁻¹) * k := by group
  have hmem : s * i * s⁻¹ ∈ Rgrp2519 N i := ⟨⟨hsiS, hsiU.2⟩, hsiS, hsiK⟩
  rw [hR] at hmem
  refine ⟨s, hsS, ?_⟩
  rcases mem_closure_pair_of_involutions (N.t_mul_self' hf) hi.mul_self hti hmem with
    h1 | h1 | h1 | h1
  · exfalso
    apply hi.ne_one
    calc i = s⁻¹ * (s * i * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  · exfalso
    apply hi.ne_t h
    have hts : t * s = s * t := N.t_comm_of_mem_S hf hsS
    calc i = s⁻¹ * (s * i * s⁻¹) * s := by group
      _ = s⁻¹ * t * s := by rw [h1]
      _ = t := by rw [mul_assoc, hts]; group
  · exact absurd (by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1) hsni
  · exact h1

theorem not_conj_t_i (h : Lv2518 N t zK) (hK0 : N.K0 = N.K) {Ki : Subgroup G}
    (hKi : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))) (hKKi : N.K ≤ Ki)
    (hne : N.K ≠ Ki) (g : G) : g⁻¹ * t * g ≠ i := by
  intro hg
  have hCt : CFSG.conjugate (Subgroup.centralizer ({t} : Set G)) g =
      Subgroup.centralizer ({i} : Set G) := by
    rw [BenderBranch.conjugate_centralizer_singleton, hg]
  have hKg : IsComponentIn (CFSG.conjugate N.K g) (Subgroup.centralizer ({i} : Set G)) := by
    have := isComponentIn_conjugate_pair h.concl2518.1 g
    rwa [hCt] at this
  rcases BenderBranch.eq_or_commute_of_isComponentIn hKg hKi with heq | hcomm
  · apply hne
    refine Subgroup.eq_of_le_of_card_ge hKKi ?_
    rw [← heq, BenderBranch.card_conjugate]
  · have hCi : CFSG.conjugate (Subgroup.centralizer ({i} : Set G)) g⁻¹ =
        Subgroup.centralizer ({t} : Set G) := by
      rw [BenderBranch.conjugate_centralizer_singleton]
      have : (g⁻¹)⁻¹ * i * g⁻¹ = t := by rw [← hg]; group
      rw [this]
    have hJ : IsComponentIn (CFSG.conjugate Ki g⁻¹) (Subgroup.centralizer ({t} : Set G)) := by
      have := isComponentIn_conjugate_pair hKi g⁻¹
      rwa [hCi] at this
    have hJK : ⁅CFSG.conjugate Ki g⁻¹, N.K⁆ = ⊥ := by
      have h1 := conjugate_commutator (CFSG.conjugate N.K g) Ki g⁻¹
      rw [hcomm, BenderBranch.conjugate_conjugate, mul_inv_cancel,
        BenderBranch.conjugate_one] at h1
      have h2 : CFSG.conjugate (⊥ : Subgroup G) g⁻¹ = ⊥ := Subgroup.map_bot _
      rw [h2] at h1
      rw [Subgroup.commutator_comm]
      exact h1
    have hJle : CFSG.conjugate Ki g⁻¹ ≤ Subgroup.centralizer (N.K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJK
    have hJY : IsComponentIn (CFSG.conjugate Ki g⁻¹)
        (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) :=
      BenderBranch.isComponentIn_of_le hJ (le_inf hJ.1 hJle) inf_le_left
    have hchar : CharTwo (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) := by
      have := h.concl2518.2.2.2.1
      rwa [hK0] at this
    exact not_isComponentIn_of_charTwo' hchar _ hJY

theorem not_conj_t_ti (h : Lv2518 N t zK) (hK0 : N.K0 = N.K) {Ki : Subgroup G}
    (hKi : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))) (hKKi : N.K ≤ Ki)
    (hne : N.K ≠ Ki) (hswap : ∃ s ∈ N.S, s * i * s⁻¹ = t * i) (g : G) :
    g⁻¹ * t * g ≠ t * i := by
  intro hg
  obtain ⟨s, -, hs⟩ := hswap
  apply not_conj_t_i h hK0 hKi hKKi hne (g * s)
  calc (g * s)⁻¹ * t * (g * s) = s⁻¹ * (g⁻¹ * t * g) * s := by group
    _ = s⁻¹ * (t * i) * s := by rw [hg]
    _ = i := by rw [← hs]; group

end Sylow

end CFSG.QuasithinUnique.Id2519
