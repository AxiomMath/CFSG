module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Planes
public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Comp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section TwoComponents

variable {X : Type} [Group X] [Finite X] {p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

theorem isSylowOf_inf_of_le_normalizer [Fact p.Prime] (P : Sylow p X) {K : Subgroup X}
    (hn : (P : Subgroup X) ≤ normalizer (K : Set X)) :
    CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup X) ⊓ K) K := by
  have hP : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup X) ((P : Subgroup X) ⊔ K) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, P.isPGroup', ?_⟩
    intro hdvd
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : (P : Subgroup X) ≤ (P : Subgroup X) ⊔ K)
    apply P.not_dvd_index
    rw [← h1]
    exact Dvd.dvd.mul_right hdvd _
  exact hP.inf_of_le_normalizer le_sup_right (sup_le hn le_normalizer)

theorem not_isMulCommutative_inf [Fact p.Prime] (hodd : p ≠ 2) (P : Sylow p X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hn : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hdvd : p ∣ Nat.card (center K)) : ¬ IsMulCommutative ↥((P : Subgroup X) ⊓ K) := by
  intro hc
  obtain ⟨Q, hQ⟩ := (isSylowOf_inf_of_le_normalizer P hn).exists_sylow_eq_subgroupOf
  have hnab := (GL83.I_6_10_1_proved K hK.2.2 p Fact.out hodd hdvd Q).1
  apply hnab
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : ((a : K) : X) ∈ (P : Subgroup X) ⊓ K :=
    Subgroup.mem_subgroupOf.1 ((SetLike.ext_iff.1 hQ (a : K)).1 a.2)
  have hb : ((b : K) : X) ∈ (P : Subgroup X) ⊓ K :=
    Subgroup.mem_subgroupOf.1 ((SetLike.ext_iff.1 hQ (b : K)).1 b.2)
  have h1 := hc.is_comm.comm ⟨((a : K) : X), ha⟩ ⟨((b : K) : X), hb⟩
  have h2 : ((a : K) : X) * ((b : K) : X) = ((b : K) : X) * ((a : K) : X) :=
    congrArg Subtype.val h1
  apply Subtype.ext
  apply Subtype.ext
  exact h2

theorem RedConfig.mem_of_mem_inf_centralizer (h : RedConfig p P z D) {x : X}
    (hxP : x ∈ (P : Subgroup X)) (hxC : x ∈ centralizer (D : Set X)) : x ∈ D := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hQP : D ⊔ zpowers x ≤ (P : Subgroup X) := sup_le h.le (zpowers_le.2 hxP)
  have hQD : D ⊔ zpowers x ≤ centralizer (D : Set X) :=
    sup_le (le_centralizer_iff_isMulCommutative.mpr h.elem.1) (zpowers_le.2 hxC)
  have heq : D ⊔ zpowers x = D := h.sylow.eq_of_le le_sup_left hQD (P.isPGroup'.to_le hQP)
  rw [← heq]
  exact Subgroup.mem_sup_right (mem_zpowers x)

theorem RedConfig.exists_normal_plane (h : RedConfig p P z D) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hn : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hdvd : p ∣ Nat.card (center K)) :
    ∃ U : Subgroup X, U ≤ (P : Subgroup X) ⊓ K ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
      z ∈ U ∧ (P : Subgroup X) ≤ normalizer (U : Set X) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set S : Subgroup X := (P : Subgroup X) ⊓ K with hS
  have hSP : S ≤ (P : Subgroup X) := inf_le_left
  have hnormS : (P : Subgroup X) ≤ normalizer (S : Set X) :=
    (le_inf le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  haveI : (S.subgroupOf (P : Subgroup X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).2 hnormS
  have hnc : ¬ IsCyclic (S.subgroupOf (P : Subgroup X)) := by
    intro hcyc
    have e : S.subgroupOf (P : Subgroup X) ≃* S := Subgroup.subgroupOfEquivOfLe hSP
    have : IsCyclic S := (MulEquiv.isCyclic e).1 hcyc
    exact not_isMulCommutative_inf h.ne_two P hK hn hdvd inferInstance
  obtain ⟨U, hUC, hUn, hUcard, hUexp, hUcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le h.ne_two P.isPGroup'
      (S.subgroupOf (P : Subgroup X)) hnc
  set U' : Subgroup X := U.map (P : Subgroup X).subtype with hU'
  have hUel : IsElemAbelian p U :=
    ⟨⟨⟨fun a b => Subtype.ext (hUcomm (a : ↥(P : Subgroup X)) a.2 (b : ↥(P : Subgroup X)) b.2)⟩⟩,
      fun x hx => hUexp x hx⟩
  have hU'el : IsElemAbelian p U' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hUel _
  have hU'card : Nat.card U' = p ^ 2 := by
    rw [hU', Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective, hUcard]
  have hU'S : U' ≤ S := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hUC hu)
  have hU'P : U' ≤ (P : Subgroup X) := hU'S.trans hSP
  have hsub : U'.subgroupOf (P : Subgroup X) = U :=
    Subgroup.comap_map_eq_self_of_injective (P : Subgroup X).subtype_injective U
  have hU'n : (P : Subgroup X) ≤ normalizer (U' : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU'P).1 (by rw [hsub]; exact hUn)
  have hU'ne : U' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hU'card
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  exact ⟨U', hU'S, hU'el, hU'card,
    mem_of_normalizing_ne_bot hp P.isPGroup' hU'ne hU'P hU'n h.ord h.unique, hU'n⟩

theorem RedConfig.false_of_two_components (h : RedConfig p P z D) (hz : z ∈ CFSG.pCore p X)
    {K₁ K₂ : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤) (hK₂ : IsComponentOf K₂ ⊤) (hne : K₁ ≠ K₂) :
    False := by
  classical
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn₁ := h.le_normalizer_component hz hK₁
  have hn₂ := h.le_normalizer_component hz hK₂
  have hd₁ := h.dvd_card_center_component hz hK₁ hn₁
  have hd₂ := h.dvd_card_center_component hz hK₂ hn₂
  obtain ⟨U₁, hU₁S, hU₁e, hU₁c, hzU₁, hU₁n⟩ := h.exists_normal_plane hK₁ hn₁ hd₁
  obtain ⟨U₂, hU₂S, hU₂e, hU₂c, hzU₂, hU₂n⟩ := h.exists_normal_plane hK₂ hn₂ hd₂
  have hK₁₂ : K₁ ≤ centralizer (K₂ : Set X) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne K₁ K₂ hK₁ hK₂ hne)
  have hK₂₁ : K₂ ≤ centralizer (K₁ : Set X) := le_centralizer_iff.mp hK₁₂
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a := by
    intro a ha b hb
    exact (mem_centralizer_iff.1 (hK₁₂ (hU₁S ha).2) b (hU₂S hb).2).symm
  have hint : ∀ u ∈ U₁, u ∈ U₂ → u ∈ zpowers z := by
    intro u hu₁ hu₂
    by_contra hnu
    have hu1 : u ≠ 1 := fun h1 => hnu (h1 ▸ one_mem _)
    have hup : u ^ p = 1 := hU₁e.2 u hu₁
    have huord : orderOf u = p := orderOf_eq_prime hup hu1
    have hzp : z ^ p = 1 := h.ord ▸ pow_orderOf_eq_one z
    have hzuP : u ∈ centralizer ((zpowers z : Subgroup X) : Set X) := by
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      have hzu : Commute z u := (mem_centralizer_iff.1 h.central u (hU₁S hu₁).1).symm
      exact ((hzu.zpow_left k).eq)
    have hAcard : Nat.card (zpowers z) = p ^ 1 := by rw [Nat.card_zpowers, h.ord, pow_one]
    obtain ⟨hAel, hAc⟩ := isElemAbelian_sup_zpowers hp
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hzp) hAcard huord hzuP hnu
    have hAle : zpowers z ⊔ zpowers u ≤ U₁ ⊓ U₂ :=
      sup_le (le_inf (zpowers_le.2 hzU₁) (zpowers_le.2 hzU₂))
        (zpowers_le.2 (mem_inf.2 ⟨hu₁, hu₂⟩))
    have hAK₁ : zpowers z ⊔ zpowers u ≤ K₁ := fun x hx => (hU₁S (hAle hx).1).2
    have hAK₂ : zpowers z ⊔ zpowers u ≤ K₂ := fun x hx => (hU₂S (hAle hx).2).2
    have hS : ∀ K ∈ ({K₁, K₂} : Finset (Subgroup X)), IsComponentOf K ⊤ := by
      intro K hK
      rcases Finset.mem_insert.1 hK with rfl | hK
      · exact hK₁
      · rw [Finset.mem_singleton.1 hK]; exact hK₂
    have hAC : ∀ K ∈ ({K₁, K₂} : Finset (Subgroup X)),
        zpowers z ⊔ zpowers u ≤ centralizer (K : Set X) := by
      intro K hK
      rcases Finset.mem_insert.1 hK with rfl | hK
      · exact hAK₂.trans hK₂₁
      · rw [Finset.mem_singleton.1 hK]; exact hAK₁.trans hK₁₂
    have := card_add_le_pRank_of_components h.prime h.ne_two h.core {K₁, K₂} hS hAel hAc hAC
    rw [Finset.card_pair hne, h.pRank_top] at this
    omega
  have hcen := centralizes_of_two_planes hp h.ne_two P.isPGroup' h.ord (h.le h.mem) h.central
    h.le h.elem h.card h.mem (fun x hxP hxC => h.mem_of_mem_inf_centralizer hxP hxC)
    (hU₁S.trans inf_le_left) hU₁e hU₁c hzU₁ hU₁n (hU₂S.trans inf_le_left) hU₂e hU₂c hzU₂ hU₂n
    hcomm hint
  have hU₁D : U₁ ≤ D := by
    intro u hu
    refine h.mem_of_mem_inf_centralizer (hU₁S hu).1 ?_
    rw [mem_centralizer_iff]
    intro d hd
    exact hcen d hd u hu
  have hDU₁ : D = U₁ := (eq_of_le_of_card_ge hU₁D (by rw [hU₁c, h.card])).symm
  have hDK₁ : D ≤ K₁ := hDU₁ ▸ (hU₁S.trans inf_le_right)
  have hS₂D : (P : Subgroup X) ⊓ K₂ ≤ D := by
    rintro x ⟨hxP, hxK⟩
    refine h.mem_of_mem_inf_centralizer hxP ?_
    rw [mem_centralizer_iff]
    intro d hd
    exact (mem_centralizer_iff.1 (hK₂₁ hxK) d (hDK₁ hd))
  have hcomm₂ : IsMulCommutative ↥((P : Subgroup X) ⊓ K₂) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 := h.elem.1.is_comm.comm (⟨(a : X), hS₂D a.2⟩ : D) ⟨(b : X), hS₂D b.2⟩
    have h2 : (a : X) * (b : X) = (b : X) * (a : X) := congrArg Subtype.val h1
    exact Subtype.ext h2
  exact not_isMulCommutative_inf h.ne_two P hK₂ hn₂ hd₂ hcomm₂

end TwoComponents

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
