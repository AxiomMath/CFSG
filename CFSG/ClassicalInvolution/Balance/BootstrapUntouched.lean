module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayers
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsRankFour
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

section Lift

theorem exists_involution_lift_centralizer {a : G} {E : Subgroup G}
    (hE : E ≤ Subgroup.centralizer ({a} : Set G)) (hE2 : ∀ e ∈ E, e * e = 1) {z : OddQuot a}
    (hz2 : z * z = 1)
    (hcomm : ∀ (e : G) (he : e ∈ E), oddQuotMk a ⟨e, hE he⟩ * z = z * oddQuotMk a ⟨e, hE he⟩) :
    ∃ (g : G) (hg : g ∈ Subgroup.centralizer ({a} : Set G)),
      g ∈ Subgroup.centralizer (E : Set G) ∧ g * g = 1 ∧ oddQuotMk a ⟨g, hg⟩ = z := by
  classical
  by_cases hz1 : z = 1
  · refine ⟨1, one_mem _, one_mem _, mul_one 1, ?_⟩
    rw [hz1]
    exact map_one (oddQuotMk a)
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hker : Odd (Nat.card (oddQuotMk a).ker) := by
    rw [show (oddQuotMk a).ker = componentClassificationOddCore ↥C from QuotientGroup.ker_mk' _]
    exact OddCore.odd_card _
  have key := map_inf_centralizer_eq (oddQuotMk a) hker (E.subgroupOf C) ⊤
    (isPGroup_two_of_sq_eq_one fun x hx => Subtype.ext (hE2 _ (Subgroup.mem_subgroupOf.mp hx)))
    (fun x _ => by rw [Subgroup.mem_normalizer_iff]; simp)
  have hmem : z ∈ (⊤ : Subgroup ↥C).map (oddQuotMk a) ⊓
      Subgroup.centralizer ((E.subgroupOf C).map (oddQuotMk a) : Set (OddQuot a)) := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
        (componentClassificationOddCore ↥C) z
      exact ⟨c, Subgroup.mem_top c, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      exact hcomm e (Subgroup.mem_subgroupOf.mp he)
  rw [← key] at hmem
  obtain ⟨g, ⟨-, hgE⟩, hgz⟩ := hmem
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hord : orderOf z = 2 := orderOf_eq_prime hz2' hz1
  have hg2 : g ^ 2 ∈ (oddQuotMk a).ker := by
    rw [MonoidHom.mem_ker, map_pow, hgz]
    exact hz2'
  have hodd : Odd (orderOf (g ^ 2)) :=
    hker.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hg2)
  have hdvd : 2 ∣ orderOf g := by
    have := orderOf_map_dvd (oddQuotMk a) g
    rw [hgz, hord] at this
    exact this
  obtain ⟨m, hm⟩ := hdvd
  have hgm : orderOf (g ^ 2) = m := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  rw [hgm] at hodd
  refine ⟨((g ^ m : ↥C) : G), (g ^ m).2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hge : g ^ m ∈ Subgroup.centralizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C) :=
      Subgroup.pow_mem _ hgE m
    have := Subgroup.mem_centralizer_iff.mp hge ⟨e, hE he⟩ (Subgroup.mem_subgroupOf.mpr he)
    exact congrArg Subtype.val this
  · have : g ^ m * g ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← hm]
      exact pow_orderOf_eq_one g
    exact congrArg Subtype.val this
  · obtain ⟨k, hk⟩ := hodd
    show oddQuotMk a (g ^ m) = z
    rw [map_pow, hgz, hk, pow_succ, pow_mul, hz2', one_pow, one_mul]

end Lift

section Closure

structure FrameSideH (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (A : Subgroup G) : Prop where
  elem : IsElemAbelian 2 A
  card : 8 ≤ Nat.card A
  nonempty : ∃ K ∈ Ω, ∃ z ∈ A, IsClassicalMember p f K z
  generation : ∀ a ∈ A, a ≠ 1 → CentralizerGenerationModOTwo Ω A a
  link : ∀ a ∈ A, a ≠ 1 → ∀ M ∈ centralizingMembers Ω {a}, ∀ z : G, IsClassicalMember p f M z →
    ∃ z' ∈ A, ∃ h ∈ rankTwoSpan A, z = h * z' * h⁻¹

@[expose] def omegaStarH (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ rankTwoSpan A, ∃ z ∈ A, IsClassicalMember p f L (h * z * h⁻¹)}

omit [Finite G] in
theorem mem_omegaStarH_of_commutes (hΩ : InClass p f Ω) (hF : FrameSideH p f Ω A)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarH p f Ω A) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarH p f Ω A := by
  obtain ⟨hLΩ, h₀, hh₀, a, haA, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨z', hz'A, h₁, hh₁, hz₀h₁⟩ :=
    hF.link a haA hLa'.ne_one M ⟨hMΩ, hMa⟩ z₀ hz₀
  have hz₀' : IsClassicalMember p f M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember p f L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ hh₁, z', hz'A, ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem le_rankTwoSpan_of_mem_omegaStarH (hΩ : InClass p f Ω) (hF : FrameSideH p f Ω A)
    {L : Subgroup G} (hLs : L ∈ omegaStarH p f Ω A) : L ≤ rankTwoSpan A := by
  obtain ⟨hLΩ, h, hh, a, haA, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} := ⟨hconj _ _ hLΩ, le_centralizer hLa'⟩
  have hY : conjSub h⁻¹ L ≤ rankTwoSpan A :=
    (le_centralizingLayer hmem).trans (centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
      (hF.generation a haA hLa'.ne_one))
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

omit [Finite G] in
theorem mem_omegaStarH_of_omegaConnected (hΩ : InClass p f Ω) (hF : FrameSideH p f Ω A)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStarH p f Ω A := by
  obtain ⟨K₀, hK₀, z, hzA, hz⟩ := hF.nonempty
  have hK₀s : K₀ ∈ omegaStarH p f Ω A :=
    ⟨hK₀, 1, one_mem _, z, hzA, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarH p f Ω A := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarH_of_commutes hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ hK₀ L hLΩ)

theorem rankTwoSpan_eq_top_of_frameSideH (hΩ : InClass p f Ω) (hF : FrameSideH p f Ω A)
    (hconn : OmegaConnected Ω) : rankTwoSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankTwoSpan_of_mem_omegaStarH hΩ hF
    (mem_omegaStarH_of_omegaConnected hΩ hF hconn hLΩ)

end Closure

section Link

theorem oddCoreIn_centralizer_le_rankTwoSpan (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) {a : G}
    (ha : a ∈ A) : oddCoreIn (Subgroup.centralizer ({a} : Set G)) ≤ rankTwoSpan A := by
  have hAC : ∀ x ∈ A, x ∈ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hA hx ha)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (oddCoreIn (Subgroup.centralizer ({a} : Set G))) hA (by simpa using h8)
    (fun x hx => normalizer_oddCoreIn _ (hAC x hx))
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem exists_conj_of_inCommonComponent (hL : LocalHypotheses p f Ω A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) {M K : Subgroup G} (hM : M ∈ centralizingMembers Ω {a})
    (hK : K ∈ centralizingMembers Ω {a}) (hcc : InCommonComponent a M K) {z z' : G}
    (hz : IsClassicalMember p f M z) (hz' : IsClassicalMember p f K z') :
    ∃ h ∈ centralizingLayer Ω {a}, z = h * z' * h⁻¹ := by
  have hΩ := hL.inClass.conjInvariant
  have hodd := odd_card_galoisField hL.odd hL.five
  obtain ⟨D⟩ := hL.lie {a} (fun h => hL.noncentral a haA ha1 (h rfl))
  obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn_of_inCommonComponent hL.inClass hL.odd hL.five D
    (hL.single a haA ha1 D) hM hK hcc
  have hK'' : IsClassicalMember p f (conjSub w M) (w * z * w⁻¹) := hz.conj w
  have hwC : w ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hwY
  have hK''Y : conjSub w M ≤ centralizingLayer Ω {a} :=
    le_centralizingLayer (conjSub_mem_centralizingMembers hΩ hwC hM)
  have hU := mul_mem_oddCoreIn_of_modOddIn_eq hodd hz' hK'' (le_centralizingLayer hK) hK''Y hmod
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem (sq_eq_one hK'') (sq_eq_one hz')
    (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

theorem exists_fixed_involution_of_untouched (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) {a : G}
    (ha : a ∈ A) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) {K : Subgroup G}
    (hK : K ∈ centMembers Ω a) (hKL : ∀ L ∈ frameFamily p f Ω A, ¬ InCommonComponent a K L)
    {z : G} (hz : IsClassicalMember p f K z) :
    ∃ n ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)),
      ∀ x ∈ A, x * (n * z * n⁻¹) * x⁻¹ = n * z * n⁻¹ := by
  classical
  obtain ⟨Q, hQ, hi, hgen⟩ :=
    exists_centralized_component_of_not_inCommonComponent hp2 hΩ hIH hM ha hnc hK hKL
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {x : G}, x ∈ A → x ∈ Subgroup.centralizer ({a} : Set G) := fun hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hx ha)
  have hApg : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hM.card]; norm_num)
  have hcommN : ∀ x ∈ A, ∀ k ∈ K,
      x * k * x⁻¹ * k⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx k hk
    have hkC : k ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hkC).mp
      (hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC)))
  have hzC : z ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hz.mem
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (sq_eq_one hz)
  obtain ⟨n, hnN, hfix⟩ := exists_conj_fixed_of_isPGroup (A := A)
    (N := oddCoreIn (Subgroup.centralizer ({a} : Set G))) hApg
    (odd_card_oddCoreIn _) (fun x hx m hm => conj_mem_oddCoreIn (hAC hx) hm) (sq_eq_one hz)
    (fun m hm => conj_mem_oddCoreIn hzC hm) (by
      intro x hx
      have h1 := (oddCoreIn _).inv_mem (hcommN x hx z hz.mem)
      have e : z * (x * z * x⁻¹) = (x * z * x⁻¹ * z⁻¹)⁻¹ := by
        have h2 : (x * z * x⁻¹ * z⁻¹)⁻¹ = z * x * z⁻¹ * x⁻¹ := by group
        rw [h2, hzinv]
        group
      rw [e]
      exact h1)
  exact ⟨n, hnN, hfix⟩

@[expose] def InvSaturated (A : Subgroup G) : Prop :=
  ∀ z : G, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) → z ∈ A

omit [Finite G] in
theorem frameSaturated_of_invSaturated (hA : InvSaturated A) : FrameSaturated p f Ω A :=
  fun _ _ hMA _ hz => hA _ (sq_eq_one hz) (hMA hz.mem)

theorem link_of_invSaturated (hL : LocalHypotheses p f Ω A)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) (hsat : InvSaturated A)
    (hgen : ∀ a ∈ A, a ≠ 1 → CentralizerGenerationModOTwo Ω A a) :
    ∀ a ∈ A, a ≠ 1 → ∀ M ∈ centralizingMembers Ω {a}, ∀ z : G, IsClassicalMember p f M z →
      ∃ z' ∈ A, ∃ h ∈ rankTwoSpan A, z = h * z' * h⁻¹ := by
  intro a haA ha1 M hMmem z hz
  have hΩ := hL.inClass.conjInvariant
  have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G := fun h => hL.noncentral a haA ha1 (h rfl)
  by_cases htouch : ∃ K ∈ frameFamily p f Ω A, InCommonComponent a M K
  · obtain ⟨K, hK, hcc⟩ := htouch
    obtain ⟨hKΩ, hKA, z', hz'A, hz'⟩ := hK
    have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
      hKA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
    obtain ⟨h, hh, hzh⟩ := exists_conj_of_inCommonComponent hL haA ha1 hMmem ⟨hKΩ, hKa⟩ hcc hz hz'
    exact ⟨z', hz'A, h, centralizingLayer_le_rankTwoSpan hΩ hM.elem hM.card.ge haA
      (hgen a haA ha1) hh, hzh⟩
  · push Not at htouch
    obtain ⟨n, hn, hfix⟩ := exists_fixed_involution_of_untouched hL.odd hL.inClass hL.lie hM haA
      hnc hMmem htouch hz
    have hz2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
      calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [sq_eq_one hz]; group
    have hcent : n * z * n⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hfix x hx
      calc x * (n * z * n⁻¹) = x * (n * z * n⁻¹) * x⁻¹ * x := by group
        _ = n * z * n⁻¹ * x := by rw [h1]
    refine ⟨n * z * n⁻¹, hsat _ hz2 hcent, n⁻¹,
      oddCoreIn_centralizer_le_rankTwoSpan hM.elem hM.card.ge haA ((oddCoreIn _).inv_mem hn), ?_⟩
    group

end Link

section Stage2

theorem stage2_of_memberFamily_of_invSaturated [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a) (hconn : OmegaConnected Ω)
    (hgen : ∀ a ∈ A, a ≠ 1 → CentralizerGenerationModOTwo Ω A a) (hsat : InvSaturated A) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧ ExactMembers Ω ∧
      ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hL : LocalHypotheses p f Ω A :=
    { inClass := hΩ
      odd := hp2
      five := hq
      noncentral := fun a _ ha1 hc =>
        not_subset_center_of_ne_one hnab ha1 (Set.singleton_subset_iff.mpr hc)
      lie := hIH
      single := hMF1 }
  have hFH : FrameSideH p f Ω A :=
    { elem := hM.elem
      card := hM.card.ge
      nonempty := by
        obtain ⟨K, hK⟩ := hM.nonempty
        obtain ⟨z, hzA, hz, -⟩ := hM.involution K hK
        exact ⟨K, hM.subset hK, z, hzA, hz⟩
      generation := hgen
      link := link_of_invSaturated hL hM hsat hgen }
  obtain ⟨hΔ, hex, hP1⟩ := stage2_of_rankThreeBalance hnab hp2 hq h9 ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hsingle hIH
    ⟨hM.elem, hM.card, weakBalanced_of_memberFamily hnab hp2 hq ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hIH hM, twoBalancedWrt_of_memberFamily_of_layers hM hloc⟩
    (rankTwoSpan_eq_top_of_frameSideH hΩ hFH hconn)
    (fun K hK => ⟨hM.subset hK, by
      obtain ⟨z, hzA, hz, hKA⟩ := hM.involution K hK
      exact ⟨z, hzA, hz, hKA⟩⟩) hM.nonempty
  refine ⟨hΔ, hex, ?_⟩
  obtain ⟨K₀, hK₀⟩ := hM.nonempty
  obtain ⟨z₀, hz₀A, hz₀, -⟩ := hM.involution K₀ hK₀
  have hnc : ¬ ({z₀} : Set G) ⊆ Subgroup.center G := fun h => hL.noncentral z₀ hz₀A hz₀.ne_one
    (h rfl)
  exact localOddCentral_of_classicalMember hp2 hf hΩ hsingle (hM.subset hK₀) hz₀
    (hP1 z₀ hz₀A hz₀.ne_one (familyMeetsAt_of_saturated hp2 hq hΩ hIH hex hM
      (frameSaturated_of_invSaturated hsat) hz₀A hnc))

theorem exactMembers_and_localOddCentral_of_frameFamily_saturated [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hI : ∀ a ∈ A, a ≠ 1 → CommutingInputs p f Ω a) (hsat : InvSaturated A) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have h0 := ModelFacts.modelClauseZero
  obtain ⟨-, hex, hP1⟩ := stage2_of_memberFamily_of_invSaturated hnab hp2 hq h9 hΩ hsingle hIH hM
    (fun a ha ha1 D => (hI a ha ha1).single D)
    (fun a ha ha1 => componentLayersAt_of_commutingFundamental hp2 hq h0 hΩ hIH hM ha ha1
      (not_subset_center_of_ne_one hnab ha1) (hI a ha ha1))
    hconn
    (fun a ha ha1 => centralizerGenerationModOTwo_of_commutingFundamental hp2 hq h0 hΩ hIH hM ha
      (not_subset_center_of_ne_one hnab ha1) (hI a ha ha1))
    hsat
  exact ⟨hex, hP1⟩

end Stage2

end CFSG.ClassicalInvolution.Balance.Bootstrap
