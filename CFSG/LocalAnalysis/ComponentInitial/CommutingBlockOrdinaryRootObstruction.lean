module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddLinear
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

theorem commutatorElement_mul_mem_center {M : Type*} [Group M] {z₁ z₂ : M}
    (h₁ : z₁ ∈ center M) (h₂ : z₂ ∈ center M) (a b : M) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have c₁ := mem_center_iff.1 h₁
  have c₂ := mem_center_iff.1 h₂
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * ((b * z₂) * z₁) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [← c₁ (b * z₂)]
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z₂) * z₂⁻¹ * b⁻¹ := by rw [← c₂ a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_bot_of_le_center_of_coprime_of_perfect {M : Type*} [Group M] [Finite M]
    (hM : commutator M = ⊤) {P : Subgroup M} (hP : P ≤ center M)
    (hcop : Nat.Coprime (Nat.card P) P.index) : P = ⊥ := by
  obtain ⟨K, -, hsup, hinf, -, -, -⟩ :=
    CFSG.LyonsUnitaryFour.central_hall_direct_complement P hP hcop
  have : P.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.1 (hP hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hK : commutator M ≤ K := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    have ha : a ∈ ((K ⊔ P : Subgroup M) : Set M) := by
      rw [sup_comm, hsup]
      exact mem_top a
    have hb : b ∈ ((K ⊔ P : Subgroup M) : Set M) := by
      rw [sup_comm, hsup]
      exact mem_top b
    rw [mul_normal] at ha hb
    obtain ⟨k₁, hk₁, p₁, hp₁, rfl⟩ := ha
    obtain ⟨k₂, hk₂, p₂, hp₂, rfl⟩ := hb
    rw [commutatorElement_mul_mem_center (hP hp₁) (hP hp₂), commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  rw [hM] at hK
  rw [eq_bot_iff, ← hinf]
  exact fun p hp => mem_inf.2 ⟨hp, hK (mem_top p)⟩

theorem le_of_map_mk'_center_eq_top {G : Type*} [Group G] {L H : Subgroup G}
    (hL : commutator L = ⊤) (h : (H.subgroupOf L).map (QuotientGroup.mk' (center L)) = ⊤) :
    L ≤ H := by
  have hdec : ∀ l : L, ∃ x ∈ H.subgroupOf L, x⁻¹ * l ∈ center L := fun l => by
    have hl : QuotientGroup.mk' (center L) l ∈
        (H.subgroupOf L).map (QuotientGroup.mk' (center L)) :=
      h ▸ mem_top _
    obtain ⟨x, hx, hxl⟩ := mem_map.1 hl
    exact ⟨x, hx, QuotientGroup.eq.1 hxl⟩
  have hcomm : commutator L ≤ H.subgroupOf L := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    obtain ⟨x, hx, hxa⟩ := hdec a
    obtain ⟨y, hy, hyb⟩ := hdec b
    have e : ⁅a, b⁆ = ⁅x * (x⁻¹ * a), y * (y⁻¹ * b)⁆ := by
      rw [mul_inv_cancel_left, mul_inv_cancel_left]
    rw [e, commutatorElement_mul_mem_center hxa hyb, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  rw [hL] at hcomm
  intro l hl
  exact mem_subgroupOf.1 (hcomm (mem_top (⟨l, hl⟩ : L)))

variable {G : Type*} [Group G] [Finite G]

theorem dvd_card_centerQuotientImage {J L : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (hJL : J ≤ L) {r : ℕ} [Fact r.Prime] (hr : r ∣ Nat.card J) :
    r ∣ Nat.card (centerQuotientImage L J) := by
  by_contra hnot
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r J))
  let ψ : J →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp (inclusion hJL)
  have hPψ : (P : Subgroup J).map ψ ≤ centerQuotientImage L J := by
    rintro _ ⟨j, -, rfl⟩
    exact ⟨inclusion hJL j, mem_subgroupOf.2 j.2, rfl⟩
  have hbot : (P : Subgroup J).map ψ = ⊥ := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (P.isPGroup'.map ψ)
    have hdvd := Subgroup.card_dvd_of_le hPψ
    rcases m with _ | m
    · rw [pow_zero] at hm
      exact eq_bot_of_card_eq _ hm
    · exact absurd ((dvd_pow_self r (Nat.succ_ne_zero m)).trans (hm ▸ hdvd)) hnot
  have hPZ : (P : Subgroup J) ≤ center J := by
    intro j hj
    have hj1 : ψ j = 1 := by
      have h1 : ψ j ∈ (P : Subgroup J).map ψ := mem_map_of_mem ψ hj
      rw [hbot] at h1
      exact h1
    have hjZ : inclusion hJL j ∈ center L := (QuotientGroup.eq_one_iff _).1 hj1
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (show ((g * j : J) : G) = ((j * g : J) : G) from
      congrArg (fun z : L => (z : G)) (mem_center_iff.1 hjZ (inclusion hJL g)))
  have hcop : Nat.Coprime (Nat.card (P : Subgroup J)) (P : Subgroup J).index := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup'
    rw [hn]
    exact Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (Sylow.not_dvd_index P))
  exact Sylow.ne_bot_of_dvd_card P hr (eq_bot_of_le_center_of_coprime_of_perfect hq.1 hPZ hcop)

theorem not_dvd_card_of_centralizer_generation {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) {X : Type*} [Group X] {C : Subgroup X}
    (e : L ⧸ center L ≃* C) {r : ℕ} [Fact r.Prime]
    (hgen : ∀ (A : Subgroup X), A ≤ C → CFSG.IsElementaryAbelian 2 A → 2 ^ 2 ≤ Nat.card A →
      ∀ R : Subgroup X, R ≤ C → IsPGroup r R → R ≠ ⊥ →
        A ≤ normalizer (R : Set X) →
        (⨆ a ∈ A, ⨆ (_ : a ≠ 1), C ⊓ centralizer ({a} : Set X)) = C) :
    ¬ r ∣ Nat.card J := by
  intro hrJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, -, hcomm, -, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K, hK, hKJ⟩ := hΔ.exists_ne J
  have hJΔ : J ∈ block J := mem_block_self
  have hKL : K ≤ L := (le_blockGroup hK).trans hML
  have hJL : J ≤ L := (le_blockGroup hJΔ).trans hML
  let ι : L ⧸ center L →* X := C.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιC : ∀ y, ι y ∈ C := fun y => (e y).2
  obtain ⟨V, hVK, hVe, hVc⟩ := exists_four_group_centerQuotientImage hV hK.1 hKL hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L J) r
    (dvd_card_centerQuotientImage hq hJL hrJ)
  have hAC : V.map ι ≤ C := by
    rintro _ ⟨v, -, rfl⟩
    exact hιC v
  have hAcard : 2 ^ 2 ≤ Nat.card (V.map ι) := by
    rw [card_map_of_injective hι, hVc]
    norm_num
  have hRC : (zpowers (x : L ⧸ center L)).map ι ≤ C := by
    rintro _ ⟨v, -, rfl⟩
    exact hιC v
  have hRr : IsPGroup r ((zpowers (x : L ⧸ center L)).map ι) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_coe, hx, pow_one])).map ι
  have hR1 : (zpowers (x : L ⧸ center L)).map ι ≠ ⊥ := by
    intro h
    have hmem : ι x ∈ (zpowers (x : L ⧸ center L)).map ι := mem_map_of_mem ι (mem_zpowers _)
    rw [h, mem_bot, ← map_one ι] at hmem
    have hx1 : (x : L ⧸ center L) = 1 := hι hmem
    have := orderOf_coe x
    rw [hx1, orderOf_one, hx] at this
    exact (Fact.out : r.Prime).one_lt.ne' this.symm
  have hAR : V.map ι ≤
      normalizer (((zpowers (x : L ⧸ center L)).map ι : Subgroup X) : Set X) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hwJ : w ∈ centerQuotientImage L J := zpowers_le.2 x.2 hw
    have hvc := (commutator_eq_bot_iff_le_centralizer.1 (hcomm K hK J hJΔ hKJ).2) (hVK hv)
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hvc w hwJ]
  have hgenA := hgen (V.map ι) hAC (CFSG.IsElementaryAbelian.map ι) hAcard _ hRC hRr hR1 hAR
  have hcent : ∀ a ∈ V.map ι, a ≠ 1 → C ⊓ centralizer ({a} : Set X) ≤
      (((normalizer (blockGroup J : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (center L))).map ι := by
    rintro _ ⟨v, hv, rfl⟩ ha c hc
    obtain ⟨hcC, hcc⟩ := mem_inf.1 hc
    have : CFSG.IsElementaryAbelian 2 V := hVe
    have hv1 : v ≠ 1 := fun h => ha (by rw [h, map_one])
    have hv2 : orderOf v = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian v hv) hv1
    obtain ⟨t, htK, ht2, htv⟩ := exists_involution_lift_of_odd_center hodd (hVK hv) hv2
    obtain ⟨y, rfl⟩ : ∃ y, ι y = c := by
      refine ⟨e.symm ⟨c, hcC⟩, ?_⟩
      simp only [ι, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, Subgroup.coe_subtype]
    have hy : y ∈ centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L)) := by
      rw [htv, mem_centralizer_singleton_iff]
      apply hι
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hcc
    have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    rw [← map_centralizer_center_quotient hodd ht2'] at hy
    obtain ⟨l, hl, rfl⟩ := mem_map.1 hy
    have hlG : (l : G) ∈ centralizer ({(t : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hl)
    have hlH := centralizer_le_normalizer_blockGroup_of_mem hJ heven hΔ hK htK
      (by rw [orderOf_coe, ht2]) hlG
    exact mem_map_of_mem ι (mem_map_of_mem _ (mem_subgroupOf.2 hlH))
  have hle : C ≤ (((normalizer (blockGroup J : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (center L))).map ι := by
    rw [← hgenA]
    exact iSup₂_le fun a ha => iSup_le fun ha1 => hcent a ha ha1
  have htop : ((normalizer (blockGroup J : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (center L)) = ⊤ := eq_top_iff.2 fun y _ => by
    obtain ⟨y', hy', hyy'⟩ := mem_map.1 (hle (hιC y))
    rwa [hι hyy'] at hy'
  exact hLH (le_of_map_mk'_center_eq_top hL.1 htop)

theorem commuting_block_ordinary_root_quotient_prime_divisor_obstruction {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (r : ℕ) [Fact r.Prime] (hr : Odd r)
    (k : Type) [Field k] [Finite k] [CharP k r] (τ : CFSG.Blueprint.Chevalley.Tag)
    (he : Nonempty (L ⧸ center L ≃* CFSG.Blueprint.Chevalley.adjointGroup τ k)) :
    ¬ r ∣ Nat.card J := by
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ center L) := hL.2
  have : IsSimpleGroup (CFSG.Blueprint.Chevalley.adjointGroup τ k) :=
    MulEquiv.isSimpleGroup e.symm
  have hr2 : r ≠ 2 := fun h => by rw [h] at hr; exact (Nat.not_even_iff_odd.2 hr) even_two
  exact not_dvd_card_of_centralizer_generation hq heven hV hJ hΔ hL hML hLH e
    fun A hAC hAe hAcard R hRC hRr hR hAR =>
      have : CFSG.IsElementaryAbelian 2 A := hAe
      CFSG.LieType.Chevalley.ordinary_root_invariant_prime_subgroup_centralizer_generation τ k r 2
        hr2 A hAC hAcard R hRC hRr hR hAR

end CFSG.LocalAnalysis.ComponentInitial
