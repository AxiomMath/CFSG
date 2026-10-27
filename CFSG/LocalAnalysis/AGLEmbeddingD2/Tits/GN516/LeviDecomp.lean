module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviResidual
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

theorem leviAlt_sup_of_normalizes_of_or {K : Type} [Group K] [Finite K] {Lr U' : Subgroup K}
    (hLN : Lr ≤ Subgroup.normalizer (U' : Set K)) (hU2 : IsPGroup 2 ↥U')
    (hnode : Group.IsSolvable ↥Lr ∨ Open.IsQuasisimple ↥Lr) : LeviAlt ↥(Lr ⊔ U') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Λ : Subgroup K := Lr ⊔ U' with hΛ
  have hUΛ : U' ≤ Λ := le_sup_right
  have hLΛ : Lr ≤ Λ := le_sup_left
  have hUN : Λ ≤ Subgroup.normalizer (U' : Set K) := sup_le hLN Subgroup.le_normalizer
  have hN' : (U'.subgroupOf Λ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUΛ).2 hUN
  have hN'2 : IsPGroup 2 ↥(U'.subgroupOf Λ) := hU2.comap_subtype
  have hmul : ∀ g ∈ Λ, ∃ u ∈ U', ∃ l ∈ Lr, g = u * l := by
    intro g hg
    have : g ∈ ((U' : Set K) * (Lr : Set K)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left U' Lr hLN, sup_comm]
      exact hg
    obtain ⟨u, hu, l, hl, rfl⟩ := this
    exact ⟨u, hu, l, hl, rfl⟩
  let ι : ↥Lr →* ↥Λ ⧸ U'.subgroupOf Λ :=
    (QuotientGroup.mk' (U'.subgroupOf Λ)).comp (Subgroup.inclusion hLΛ)
  have hι : Function.Surjective ι := by
    intro s
    induction s using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨u, hu, l, hl, hg⟩ := hmul g.1 g.2
      refine ⟨⟨l, hl⟩, ?_⟩
      have hg' : g = ⟨u, hUΛ hu⟩ * ⟨l, hLΛ hl⟩ := Subtype.ext hg
      show QuotientGroup.mk (⟨l, hLΛ hl⟩ : ↥Λ) = QuotientGroup.mk g
      rw [hg', QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (⟨u, hUΛ hu⟩ : ↥Λ)).2 (Subgroup.mem_subgroupOf.2 hu), one_mul]
  rcases hnode with hs | hq
  · left
    have h1 : Group.IsSolvable ↥(U'.subgroupOf Λ) := by
      have : Group.IsNilpotent ↥(U'.subgroupOf Λ) := hN'2.isNilpotent
      infer_instance
    have h2 : Group.IsSolvable (↥Λ ⧸ U'.subgroupOf Λ) := Group.isSolvable_of_surjective hι
    exact Group.isSolvable_of_ker_le_range (U'.subgroupOf Λ).subtype
      (QuotientGroup.mk' (U'.subgroupOf Λ))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  right
  have hinf : Lr ⊓ U' ≤ Lr := inf_le_left
  have hnorm : ((Lr ⊓ U').subgroupOf Lr).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hinf).2 fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hLN hx⟩
  rcases normal_le_center_or_eq_top hq ((Lr ⊓ U').subgroupOf Lr) with hc | ht
  · have hker : ∀ x ∈ ι.ker, x ∈ Subgroup.center ↥Lr := by
      intro x hx
      have h1 : (Subgroup.inclusion hLΛ x : ↥Λ) ∈ U'.subgroupOf Λ :=
        (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
      exact hc (Subgroup.mem_subgroupOf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 h1⟩)
    have hS : Open.IsQuasisimple (↥Λ ⧸ U'.subgroupOf Λ) :=
      isQuasisimple_of_central_quotient hq ι hι hker
    exact isQuasisimple_quot_pCore_of_normal_two (U'.subgroupOf Λ) hN'2 hS
  · exfalso
    have hLU : Lr ≤ U' := fun x hx =>
      (Subgroup.mem_subgroupOf.1 (ht ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥Lr)) : x ∈ Lr ⊓ U').2
    exact not_isPGroup_of_isQuasisimple hq (hU2.to_le hLU)

theorem leviAlt_sup_of_normalizes {K : Type} [Group K] [Finite K] {Lr U' : Subgroup K}
    (hLN : Lr ≤ Subgroup.normalizer (U' : Set K)) (hU2 : IsPGroup 2 ↥U')
    (hq : Open.IsQuasisimple ↥Lr) : LeviAlt ↥(Lr ⊔ U') :=
  leviAlt_sup_of_normalizes_of_or hLN hU2 (Or.inr hq)

theorem le_pElementSubgroup_of_simple {G : Type} [Group G] [Finite G] {N V : Subgroup G}
    (hs : IsSimpleGroup ↥N) (hVN : V ≤ N) (hV2 : IsPGroup 2 ↥V) (hV : V ≠ ⊥) :
    N ≤ pElementSubgroup 2 N := by
  have := normal_pElementSubgroup_top ↥N
  have hne : pElementSubgroup 2 (⊤ : Subgroup ↥N) ≠ ⊥ := by
    intro hbot
    apply hV
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hVN hx⟩ : ↥N) ∈ pElementSubgroup 2 (⊤ : Subgroup ↥N) :=
      le_pElementSubgroup_of_isPGroup (le_top : V.subgroupOf N ≤ ⊤)
        (hV2.comap_subtype) (Subgroup.mem_subgroupOf.2 hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  have htop : pElementSubgroup 2 (⊤ : Subgroup ↥N) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  have h2 := pElementSubgroup_map_injective N.subtype N.subtype_injective (⊤ : Subgroup ↥N)
  rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2.symm.le

theorem leviAlt_pElement_of_levi_decomp {G : Type} [Group G] [Finite G] {P V N H : Subgroup G}
    (hP : P = V ⊔ N ⊔ H) (hVn : P ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 ↥V)
    (hNs : IsSimpleGroup ↥N) (hna : ∃ a b : ↥N, a * b ≠ b * a)
    (hN2 : N ≤ pElementSubgroup 2 N)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hH : Odd (Nat.card ↥H)) :
    LeviAlt ↥(pElementSubgroup 2 P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := pElementSubgroup 2 P with hW
  have hVP : V ≤ P := hP ▸ le_sup_left.trans le_sup_left
  have hNP : N ≤ P := hP ▸ le_sup_right.trans le_sup_left
  have hHP : H ≤ P := hP ▸ le_sup_right
  set M := V ⊔ N with hM
  have hMP : M ≤ P := sup_le hVP hNP
  have hMH : M ⊔ H = P := hP.symm
  have hPM : P ≤ Subgroup.normalizer (M : Set G) := by
    rw [hP]
    exact sup_le Subgroup.le_normalizer
      (fun x hx => mem_normalizer_sup (hVn (hHP hx)) (hHN hx))
  have hMpn : (M.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMP).2 hPM
  let q : ↥P →* ↥P ⧸ M.subgroupOf P := QuotientGroup.mk' (M.subgroupOf P)
  have hsup : M.subgroupOf P ⊔ H.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMP hHP, hMH, Subgroup.subgroupOf_self]
  have hmapH : (H.subgroupOf P).map q = ⊤ := by
    have h1 : (H.subgroupOf P).map q = ((H.subgroupOf P).map q) := rfl
    have hc : ((H.subgroupOf P).map q).comap q = ⊤ := by
      rw [Subgroup.comap_map_eq, show q.ker = M.subgroupOf P from QuotientGroup.ker_mk' _,
        sup_comm, hsup]
    have := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (M.subgroupOf P))
      ((H.subgroupOf P).map q)
    rw [hc, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    exact this.symm
  let g : ↥(H.subgroupOf P) →* ↥P ⧸ M.subgroupOf P := q.comp (H.subgroupOf P).subtype
  have hg : Function.Surjective g := by
    intro y
    have : y ∈ (H.subgroupOf P).map q := hmapH ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcardH : Nat.card ↥(H.subgroupOf P) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv
  have hodd : Odd (Nat.card (↥P ⧸ M.subgroupOf P)) := by
    have hd : Nat.card (↥P ⧸ M.subgroupOf P) ∣ Nat.card ↥(H.subgroupOf P) :=
      Subgroup.card_dvd_of_surjective hg
    rw [hcardH] at hd
    exact Odd.of_dvd_nat hH hd
  have hWM : W ≤ M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxP, k, hk⟩
    have hx1 : q ⟨x, hxP⟩ = 1 := by
      have hdvd1 : orderOf (q ⟨x, hxP⟩) ∣ 2 ^ k := by
        have := orderOf_map_dvd q (⟨x, hxP⟩ : ↥P)
        rwa [show orderOf (⟨x, hxP⟩ : ↥P) = 2 ^ k by rw [← hk]; exact Subgroup.orderOf_mk x hxP]
          at this
      have hdvd2 : orderOf (q ⟨x, hxP⟩) ∣ Nat.card (↥P ⧸ M.subgroupOf P) := orderOf_dvd_natCard _
      have hodd' : Odd (orderOf (q ⟨x, hxP⟩)) := Odd.of_dvd_nat hodd hdvd2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
      rw [hj] at hodd'
      have : j = 0 := by
        by_contra hj0
        exact (Nat.not_even_iff_odd.2 hodd') (Nat.even_pow.2 ⟨even_two, hj0⟩)
      rw [this, pow_zero] at hj
      exact orderOf_eq_one_iff.1 hj
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hx1)
  have hNW : N ≤ W := hN2.trans (pElementSubgroup_mono' hNP)
  have hWeq : N ⊔ (V ⊓ W) = W := by
    refine le_antisymm (sup_le hNW inf_le_right) fun w hw => ?_
    have hwM : w ∈ ((V : Set G) * (N : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left V N (fun x hx => hVn (hNP hx))]
      exact hWM hw
    obtain ⟨v, hv, n, hn, rfl⟩ := hwM
    have hvW : v ∈ W := by
      have := Subgroup.mul_mem W hw (Subgroup.inv_mem W (hNW hn))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hv, hvW⟩) (Subgroup.mem_sup_left hn)
  have hNn : N ≤ Subgroup.normalizer ((V ⊓ W : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hVn (hNP hx),
      (Subgroup.le_normalizer.trans (CFSG.AGLEmbeddingD2.GN.normalizer_le_normalizer_pElementSubgroup 2 P))
        |>.trans le_rfl (hNP hx)⟩
  have h1 := leviAlt_sup_of_normalizes hNn (hV2.to_le inf_le_left) (isQuasisimple_of_simple hNs hna)
  rw [hWeq] at h1
  exact h1

end CFSG.AGLEmbeddingD2.Tits.GN516
