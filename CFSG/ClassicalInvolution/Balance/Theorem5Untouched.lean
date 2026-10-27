module

public import CFSG.ClassicalInvolution.Balance.Theorem5Boot
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsRankFour
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Lifting

theorem exact_inf_oddCoreIn_eq_bot (hex : ExactMembers Ω) {a : G} {X : Subgroup G} (hX : X ∈ Ω)
    (hXC : X ≤ Subgroup.centralizer ({a} : Set G)) :
    X ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) = ⊥ := by
  have hle : X ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) ≤ oddCoreIn X := by
    refine le_oddCoreIn_of_normalizes inf_le_left ?_
      ((odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hkinv : k⁻¹ ∈ X := Subgroup.inv_mem _ hk
    have hkC := hXC hk
    have hkinvC := hXC hkinv
    constructor
    · rintro ⟨hs1, hs2⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hs1) hkinv, conj_mem_oddCoreIn hkC hs2⟩
    · rintro ⟨hs1, hs2⟩
      have e : s = k⁻¹ * (k * s * k⁻¹) * k := by group
      rw [e]
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hkinv hs1) hk, ?_⟩
      have := conj_mem_oddCoreIn hkinvC hs2
      simpa [mul_assoc] using this
  have hOX : oddCoreIn X = ⊥ := by
    have h' : componentClassificationOddCore X = ⊥ := hex _ hX
    show (componentClassificationOddCore X).map X.subtype = ⊥
    rw [h']
    exact Subgroup.map_bot _
  exact le_bot_iff.mp (hle.trans hOX.le)

theorem centralizes_of_exact_of_comm_mem_oddCoreIn (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {a : G} {X : Subgroup G} (hX : X ∈ Ω)
    (hXC : X ≤ Subgroup.centralizer ({a} : Set G)) {zX : G} (hzX : IsClassicalMember p f X zX)
    {g : G} (hgz : g * zX * g⁻¹ = zX)
    (hcomm : ∀ y ∈ X, g * y * g⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G))) :
    ∀ y ∈ X, g * y = y * g := by
  intro y hy
  have hbot := exact_inf_oddCoreIn_eq_bot hex hX hXC
  have hgXΩ : conjSub g X ∈ Ω := hΩ.conjInvariant g X hX
  have hz'' : IsClassicalMember p f (conjSub g X) zX := by
    have := hzX.conj g
    rwa [hgz] at this
  rcases members_eq_or_commute hz'' hzX (isQuasisimple_of_mem_exactMembers hq hΩ hex hgXΩ)
      (isQuasisimple_of_mem_exactMembers hq hΩ hex hX) with heq | hc
  · have h1 : g * y * g⁻¹ ∈ X := heq ▸ conj_mem_conjSub hy
    have h2 : g * y * g⁻¹ * y⁻¹ ∈ X ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
      ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy), hcomm y hy⟩
    rw [hbot, Subgroup.mem_bot] at h2
    calc g * y = g * y * g⁻¹ * y⁻¹ * y * g := by group
      _ = y * g := by rw [h2]; group
  · exfalso
    have hperf : ⁅X, X⁆ = X := by
      have := hzX.perfect
      exact Subgroup.commutator_eq_self
    have hle : X ≤ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
      rw [← hperf]
      refine Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => ?_
      have hcm := hcomm k₁ hk₁
      have hconj := conj_mem_oddCoreIn (hXC hk₂) hcm
      have h2 := hc _ (conj_mem_conjSub hk₁) k₂ hk₂
      have h3 : (g * k₁ * g⁻¹)⁻¹ * k₂ * (g * k₁ * g⁻¹) = k₂ := by
        calc _ = (g * k₁ * g⁻¹)⁻¹ * (k₂ * (g * k₁ * g⁻¹)) := by group
          _ = (g * k₁ * g⁻¹)⁻¹ * ((g * k₁ * g⁻¹) * k₂) := by rw [h2]
          _ = k₂ := by group
      have e : ⁅k₁, k₂⁆ = (g * k₁ * g⁻¹ * k₁⁻¹)⁻¹ * (k₂ * (g * k₁ * g⁻¹ * k₁⁻¹) * k₂⁻¹) := by
        calc ⁅k₁, k₂⁆ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := rfl
          _ = k₁ * ((g * k₁ * g⁻¹)⁻¹ * k₂ * (g * k₁ * g⁻¹)) * k₁⁻¹ * k₂⁻¹ := by rw [h3]
          _ = _ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcm) hconj
    exact hzX.ne_one (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn _) (hle hzX.mem)
      (sq_eq_one hzX))

theorem comm_mem_oddCoreIn_of_not_inCommonComponent (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {a : G} (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    {K L : Subgroup G} (hK : K ∈ centMembers Ω a) (hL : L ∈ centMembers Ω a)
    (hKL : ¬ InCommonComponent a K L) :
    ∀ k ∈ K, ∀ l ∈ L,
      k * l * k⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
  classical
  have hnorm : (memberJoin Ω a).Normal := memberJoin_normal hΩ.conjInvariant
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hIH hnc
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨K, hK, rfl⟩ : modOdd a K ∈ memberImages Ω a)
  obtain ⟨j, hj⟩ := D.exists_le _ (⟨L, hL, rfl⟩ : modOdd a L ∈ memberImages Ω a)
  have hQi : CFSG.IsComponent (D.Q i) := (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i)
  have hne : i ≠ j := by
    rintro rfl
    exact hKL ⟨D.Q i, hQi, hi, hj⟩
  intro k hk l hl
  have hkC : k ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
  have hlC : l ∈ Subgroup.centralizer ({a} : Set G) := hL.2 hl
  exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hkC hlC).mp
    (D.commute i j hne _ (hi (oddQuotMk_mem_modOdd hk hkC)) _
      (hj (oddQuotMk_mem_modOdd hl hlC)))

end Lifting

section Extension

theorem exists_extension_of_untouched (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) {K : Subgroup G} (hK : K ∈ centMembers Ω a)
    (hKL : ∀ L ∈ frameFamily p f Ω A, ¬ InCommonComponent a K L) :
    ∃ M ∈ Ω, M ≤ Subgroup.centralizer (A : Set G) ∧
      (∃ z : G, IsClassicalMember p f M z ∧ z ∉ A) ∧ InCommonComponent a K M ∧
        ∀ L ∈ frameFamily p f Ω A, Commutes L M := by
  classical
  obtain ⟨Q, hQ, hi, hgen⟩ :=
    exists_centralized_component_of_not_inCommonComponent hp2 hΩ hIH hM ha hnc hK hKL
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {x : G}, x ∈ A → x ∈ Subgroup.centralizer ({a} : Set G) := fun hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hx ha)
  have hFC : ∀ {L : Subgroup G}, L ∈ frameFamily p f Ω A →
      L ≤ Subgroup.centralizer ({a} : Set G) := fun hL =>
    hL.2.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hApg : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hM.card]; norm_num)
  have hcommN : ∀ x ∈ A, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx k hk
    have hkC : k ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hkC).mp
      (hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC)))
  obtain ⟨z, hz⟩ := hΩ.classical K hK.1
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
  have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hnN
  have hn1 : oddQuotMk a ⟨n, hnC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn hnN hnC
  have hK'Ω : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK.1
  have hK'C : conjSub n K ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    have h1 : n⁻¹ * y * n ∈ K := mem_conjSub_iff.mp hy
    have e : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC (hK.2 h1)) (Subgroup.inv_mem _ hnC)
  have hz' : IsClassicalMember p f (conjSub n K) (n * z * n⁻¹) := hz.conj n
  have himg : ∀ (y : G) (hy : y ∈ conjSub n K) (hyC : y ∈ Subgroup.centralizer ({a} : Set G)),
      ∃ k ∈ K, ∃ hkC : k ∈ Subgroup.centralizer ({a} : Set G),
        oddQuotMk a ⟨y, hyC⟩ = oddQuotMk a ⟨k, hkC⟩ := by
    intro y hy hyC
    have hk : n⁻¹ * y * n ∈ K := mem_conjSub_iff.mp hy
    have hkC : n⁻¹ * y * n ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    refine ⟨n⁻¹ * y * n, hk, hkC, ?_⟩
    have e : (⟨y, hyC⟩ : Subgroup.centralizer ({a} : Set G)) =
        ⟨n, hnC⟩ * ⟨n⁻¹ * y * n, hkC⟩ * ⟨n, hnC⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [e, map_mul, map_mul, map_inv, hn1]
    simp
  have hcommN' : ∀ x ∈ A, ∀ y ∈ conjSub n K,
      x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx y hy
    have hyC := hK'C hy
    obtain ⟨k, hk, hkC, hyk⟩ := himg y hy hyC
    refine (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hyC).mp ?_
    have h1 := hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC))
    rw [← hyk] at h1
    exact h1
  have hKcent : conjSub n K ≤ Subgroup.centralizer (A : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hxA
    exact centralizes_of_exact_of_comm_mem_oddCoreIn hq hΩ hex hK'Ω hK'C hz' (hfix x hxA)
      (fun y' hy' => hcommN' x hxA y' hy') y hy
  have hMQ : modOdd a (conjSub n K) ≤ Q := by
    rintro _ ⟨y', hy', rfl⟩
    obtain ⟨k, hk, hkC, hyk⟩ := himg (y' : G) hy' y'.2
    show oddQuotMk a ⟨(y' : G), y'.2⟩ ∈ Q
    rw [hyk]
    exact hi (oddQuotMk_mem_modOdd hk hkC)
  refine ⟨conjSub n K, hK'Ω, hKcent, ⟨n * z * n⁻¹, hz', fun hzA => ?_⟩, ⟨Q, hQ, hi, hMQ⟩, ?_⟩
  ·
    exact hKL (conjSub n K) ⟨hK'Ω, hKcent, _, hzA, hz'⟩ ⟨Q, hQ, hi, hMQ⟩
  ·
    intro L hL l hl g hg
    have hLΩ : L ∈ Ω := hL.1
    obtain ⟨zL, hzLA, hzL⟩ := hL.2.2
    have hgC := hK'C hg
    obtain ⟨k, hk, hkC, hgk⟩ := himg g hg hgC
    have hcomm' : ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
      intro y hy
      have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := hFC hL hy
      have hky := comm_mem_oddCoreIn_of_not_inCommonComponent hp2 hΩ hIH hnc hK
        ⟨hLΩ, hFC hL⟩ (hKL L hL) k hk y hy
      have h1 : oddQuotMk a ⟨k, hkC⟩ * oddQuotMk a ⟨y, hyC⟩ =
          oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a ⟨k, hkC⟩ :=
        (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hkC hyC).mpr hky
      rw [← hgk] at h1
      exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hgC hyC).mp h1
    have hgz : g * zL * g⁻¹ = zL :=
      (Subgroup.mem_centralizer_iff.mp (hKcent hg) zL hzLA).symm ▸ by group
    exact (centralizes_of_exact_of_comm_mem_oddCoreIn hq hΩ hex hLΩ (hFC hL) hzL hgz hcomm' l
      hl).symm

end Extension

section Triples

theorem card_closure_insert_le {S : Set G} {c : G} (hc : c * c = 1)
    (hcS : ∀ s ∈ S, c * s = s * c) :
    Nat.card (Subgroup.closure (insert c S)) ≤ 2 * Nat.card (Subgroup.closure S) := by
  set F : Subgroup G := Subgroup.closure S with hF
  have hFc : F ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hF, Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hcS s hs).symm
  have hcF : ∀ x ∈ F, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hFc hx)).symm
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hmem : ∀ x ∈ Subgroup.closure (insert c S), x ∈ F ∨ ∃ g ∈ F, x = g * c := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Or.inr ⟨1, F.one_mem, by simp⟩
      · exact Or.inl (Subgroup.subset_closure hy)
    | one => exact Or.inl F.one_mem
    | mul y z _ _ hy hz =>
      rcases hy with hy | ⟨g, hg, rfl⟩ <;> rcases hz with hz | ⟨g', hg', rfl⟩
      · exact Or.inl (F.mul_mem hy hz)
      · exact Or.inr ⟨y * g', F.mul_mem hy hg', by group⟩
      · refine Or.inr ⟨g * z, F.mul_mem hg hz, ?_⟩
        calc g * c * z = g * (c * z) := by group
          _ = g * (z * c) := by rw [hcF z hz]
          _ = g * z * c := by group
      · refine Or.inl ?_
        have e : g * c * (g' * c) = g * g' := by
          calc g * c * (g' * c) = g * (c * g') * c := by group
            _ = g * (g' * c) * c := by rw [hcF g' hg']
            _ = g * g' * (c * c) := by group
            _ = g * g' := by rw [hc]; group
        rw [e]
        exact F.mul_mem hg hg'
    | inv y _ hy =>
      rcases hy with hy | ⟨g, hg, rfl⟩
      · exact Or.inl (F.inv_mem hy)
      · refine Or.inr ⟨g⁻¹, F.inv_mem hg, ?_⟩
        have h1 : c * g⁻¹ = g⁻¹ * c := hcF g⁻¹ (F.inv_mem hg)
        calc (g * c)⁻¹ = c⁻¹ * g⁻¹ := by group
          _ = c * g⁻¹ := by rw [hcinv]
          _ = g⁻¹ * c := h1
  have hsub : ((Subgroup.closure (insert c S) : Subgroup G) : Set G) ⊆
      (F : Set G) ∪ (fun g => g * c) '' (F : Set G) := by
    intro x hx
    rcases hmem x hx with h | ⟨g, hg, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨g, hg, rfl⟩
  calc Nat.card (Subgroup.closure (insert c S))
      = Set.ncard ((Subgroup.closure (insert c S) : Subgroup G) : Set G) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard ((F : Set G) ∪ (fun g => g * c) '' (F : Set G)) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Set.ncard (F : Set G) + Set.ncard ((fun g => g * c) '' (F : Set G)) :=
        Set.ncard_union_le _ _
    _ ≤ Set.ncard (F : Set G) + Set.ncard (F : Set G) :=
        Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
    _ = 2 * Nat.card F := by rw [two_mul, ← Nat.card_coe_set_eq]; rfl

theorem card_closure_singleton_le_two {a : G} (ha : a * a = 1) :
    Nat.card (Subgroup.closure ({a} : Set G)) ≤ 2 := by
  have h := card_closure_insert_le (S := (∅ : Set G)) ha
    (fun s hs => absurd hs (Set.notMem_empty s))
  rw [← Set.singleton_def, Subgroup.closure_empty, Subgroup.card_bot] at h
  simpa using h

theorem card_closure_pair_le_four {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 4 := by
  have h := card_closure_insert_le (S := ({b} : Set G)) (c := a) ha (by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact hab)
  have h2 := card_closure_singleton_le_two hb
  omega

omit [Finite G] in
theorem isElemAbelian_closure_of_commuting_involutions {S : Set G}
    (hS2 : ∀ s ∈ S, s * s = 1) (hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    IsElemAbelian 2 (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hSc x hx y hy)
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => rw [sq]; exact hS2 y hy
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure S) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [(Commute.mul_pow (show Commute y z from hc)), hy, hz, one_mul]
  | inv y _ hy => rw [inv_pow, hy, inv_one]

theorem indepTripleOn_exchange {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) {i j : Fin 3} (hij : i ≠ j) {M : Subgroup G} {zM : G} (hM : M ∈ Ω)
    (hzM : IsClassicalMember p f M zM) (hMA : M ≤ Subgroup.centralizer (A : Set G))
    (hzMA : zM ∉ A) (hMi : ∀ x ∈ K i, ∀ y ∈ M, x * y = y * x)
    (hMj : ∀ x ∈ K j, ∀ y ∈ M, x * y = y * x) :
    IndepTripleOn p f Ω (Subgroup.closure ({z i, z j, zM} : Set G)) ∧
      Nat.card (Subgroup.closure ({z i, z j} : Set G)) = 4 ∧
      M ≤ Subgroup.centralizer
        ((Subgroup.closure ({z i, z j, zM} : Set G) : Subgroup G) : Set G) := by
  classical
  have hsq : ∀ m, z m * z m = 1 := fun m => sq_eq_one (hK m).2
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hAc : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hzMsq : zM * zM = 1 := sq_eq_one hzM
  have hzMc : ∀ x ∈ A, x * zM = zM * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hMA hzM.mem) x hx
  have hab : z i * z j = z j * z i := hAc (hzA i) (hzA j)
  obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j :=
    (by decide : ∀ i j : Fin 3, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j) i j hij
  have hrange : Set.range z ⊆ insert (z k) ({z i, z j} : Set G) := by
    rintro _ ⟨m, rfl⟩
    by_cases hmi : m = i
    · subst hmi
      simp
    by_cases hmj : m = j
    · subst hmj
      simp
    have hmk : m = k :=
      (by decide : ∀ i j k m : Fin 3, i ≠ j → k ≠ i → k ≠ j → m ≠ i → m ≠ j → m = k)
        i j k m hij hki hkj hmi hmj
    subst hmk
    simp
  have hF4le : Nat.card (Subgroup.closure ({z i, z j} : Set G)) ≤ 4 :=
    card_closure_pair_le_four (hsq i) (hsq j) hab
  have hAle : Nat.card A ≤ Nat.card (Subgroup.closure (insert (z k) ({z i, z j} : Set G))) :=
    Subgroup.card_le_of_le (by
      rw [hAdef, Subgroup.closure_le]
      exact fun x hx => Subgroup.subset_closure (hrange hx))
  have hAle2 := card_closure_insert_le (S := ({z i, z j} : Set G)) (c := z k) (hsq k) (by
    rintro s (rfl | hs)
    · exact hAc (hzA k) (hzA i)
    · rw [Set.mem_singleton_iff.mp hs]
      exact hAc (hzA k) (hzA j))
  have hF4 : Nat.card (Subgroup.closure ({z i, z j} : Set G)) = 4 := by omega
  have hA'ins : ({z i, z j, zM} : Set G) = insert zM {z i, z j} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hA'le : Nat.card (Subgroup.closure ({z i, z j, zM} : Set G)) ≤ 8 := by
    have h := card_closure_insert_le (S := ({z i, z j} : Set G)) (c := zM) hzMsq (by
      rintro s (rfl | hs)
      · exact (hzMc _ (hzA i)).symm
      · rw [Set.mem_singleton_iff.mp hs]
        exact (hzMc _ (hzA j)).symm)
    rw [hA'ins]
    omega
  have hFA' : Subgroup.closure ({z i, z j} : Set G) ≤
      Subgroup.closure ({z i, z j, zM} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    apply Subgroup.subset_closure
    rcases hx with rfl | hx
    · simp
    · rw [Set.mem_singleton_iff.mp hx]
      simp
  have hFA : Subgroup.closure ({z i, z j} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hzA i
    · rw [Set.mem_singleton_iff.mp hx]
      exact hzA j
  have hA'card : Nat.card (Subgroup.closure ({z i, z j, zM} : Set G)) = 8 := by
    by_contra hne
    have hdvd : 4 ∣ Nat.card (Subgroup.closure ({z i, z j, zM} : Set G)) :=
      hF4 ▸ Subgroup.card_dvd_of_le hFA'
    have hpos : 0 < Nat.card (Subgroup.closure ({z i, z j, zM} : Set G)) := Nat.card_pos
    have h4 : Nat.card (Subgroup.closure ({z i, z j, zM} : Set G)) = 4 := by omega
    have hFeq : Subgroup.closure ({z i, z j} : Set G) =
        Subgroup.closure ({z i, z j, zM} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hFA' (by rw [h4, hF4])
    have hzMF : zM ∈ Subgroup.closure ({z i, z j} : Set G) :=
      hFeq ▸ Subgroup.subset_closure (by simp)
    exact hzMA (hFA hzMF)
  have hA'el : IsElemAbelian 2 (Subgroup.closure ({z i, z j, zM} : Set G)) := by
    refine isElemAbelian_closure_of_commuting_involutions ?_ ?_
    · rintro s (rfl | rfl | rfl)
      · exact hsq i
      · exact hsq j
      · exact hzMsq
    · rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl)
      · rfl
      · exact hab
      · exact hzMc _ (hzA i)
      · exact hab.symm
      · rfl
      · exact hzMc _ (hzA j)
      · exact (hzMc _ (hzA i)).symm
      · exact (hzMc _ (hzA j)).symm
      · rfl
  have hrange3 : Set.range ![z i, z j, zM] = ({z i, z j, zM} : Set G) := by
    ext x
    simp
    tauto
  refine ⟨⟨![K i, K j, M], ![z i, z j, zM], ?_, ?_, ?_, hA'el, hA'card⟩, hF4, ?_⟩
  · intro m
    fin_cases m
    exacts [hK i, hK j, ⟨hM, hzM⟩]
  · intro m n hmn x hx y hy
    fin_cases m <;> fin_cases n
    · exact absurd rfl hmn
    · exact hcomm i j hij x hx y hy
    · exact hMi x hx y hy
    · exact hcomm j i hij.symm x hx y hy
    · exact absurd rfl hmn
    · exact hMj x hx y hy
    · exact (hMi y hy x hx).symm
    · exact (hMj y hy x hx).symm
    · exact absurd rfl hmn
  · rw [hrange3]
  · intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : Subgroup.closure ({z i, z j, zM} : Set G) ≤ Subgroup.centralizer ({m} : Set G) := by
      rw [Subgroup.closure_le]
      rintro s (rfl | rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hMA hm) _ (hzA i)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hMA hm) _ (hzA j)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hzM.isCentralInvolution.central m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

end Triples

section P1Triangle

theorem localOddCentral_of_indepTriple_pair [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) {F₀ : Subgroup G} (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A)
    (hα : alphaCore F₀ = ⊥) {i j : Fin 3} (hij : i ≠ j) {x : G}
    (hx : x ∈ Subgroup.closure ({z i, z j} : Set G)) (hx1 : x ≠ 1) :
    LocalOddCentral Ω {x} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hA : IndepTripleOn p f Ω A := ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩
  have hMF := memberFamily_of_indepTripleOn hp2 hf hA
  have hB : RankThreeBalance A :=
    rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH hA (hlay A hA)
  have hΔA : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ :=
    deltaCore_eq_bot_of_alphaCore_eq_bot hB hF₀ hα
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hxA : x ∈ A := by
    refine (Subgroup.closure_le A).mpr ?_ hx
    rintro _ (rfl | hy)
    · exact hzA i
    · rw [Set.mem_singleton_iff.mp hy]
      exact hzA j
  have hKfam : ∀ m, K m ∈ frameFamily p f Ω A := fun m =>
    ⟨(hK m).1, by rw [hAdef]; exact triple_centralizes hK hcomm m, z m, hzA m, (hK m).2⟩
  refine localOddCentral_of_framesMeet hnab hp2 hq ModelFacts.modelClauseZero fundamentalWholeA1
    hΩ hIH hx1 fun K' hK' => ?_
  by_cases hcc : ∃ L ∈ frameFamily p f Ω A, InCommonComponent x K' L
  · obtain ⟨L, ⟨hLΩ, hLA, zL, hzLA, hzL⟩, hcc⟩ := hcc
    exact ⟨A, hel, hcard, hΔA, hxA, L, hLΩ, zL, hzLA, hzL, hLA, hcc⟩
  · push Not at hcc
    obtain ⟨M, hMΩ, hMA, ⟨zM, hzM, hzMA⟩, hKM, hMcomm⟩ := exists_extension_of_untouched hp2 hq hΩ
      hIH hex hMF hxA (not_subset_center_of_ne_one hnab hx1) hK' hcc
    obtain ⟨hA', hF4, hMA'⟩ := indepTripleOn_exchange hK hcomm hAdef hel hcard hij hMΩ hzM hMA
      hzMA (hMcomm (K i) (hKfam i)) (hMcomm (K j) (hKfam j))
    set A' : Subgroup G := Subgroup.closure ({z i, z j, zM} : Set G) with hA'def
    have hB' : RankThreeBalance A' :=
      rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH hA' (hlay A' hA')
    set F : Subgroup G := Subgroup.closure ({z i, z j} : Set G) with hFdef
    have hFA : F ≤ A := by
      rw [hFdef, Subgroup.closure_le]
      rintro _ (rfl | hy)
      · exact hzA i
      · rw [Set.mem_singleton_iff.mp hy]
        exact hzA j
    have hFA' : F ≤ A' := by
      rw [hFdef, Subgroup.closure_le]
      rintro _ (rfl | hy)
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff.mp hy]
        exact Subgroup.subset_closure (by simp)
    have hFE : F ∈ signalizerFunctorEk 2 2 A := ⟨hFA, by rw [hF4]; norm_num⟩
    have hFE' : F ∈ signalizerFunctorEk 2 2 A' := ⟨hFA', by rw [hF4]; norm_num⟩
    have hαF : alphaCore F = ⊥ :=
      (alphaFrame_eq_alphaCore hB hFE).symm.trans ((alphaFrame_eq_alphaCore hB hF₀).trans hα)
    have hxA' : x ∈ A' := hFA' hx
    exact ⟨A', hB'.elem, hB'.card, deltaCore_eq_bot_of_alphaCore_eq_bot hB' hFE' hαF, hxA', M, hMΩ,
      zM, Subgroup.subset_closure (by simp), hzM, hMA', hKM⟩

end P1Triangle

section Assembly

theorem exactMembers_and_localOddCentral_of_connectedTriangles [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {𝒯 : Set (Subgroup G)} (hsub : 𝒯 ⊆ triangleFrames p f Ω)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A')
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ 𝒯) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hbal : ∀ A ∈ 𝒯, RankThreeBalance A := fun A hA =>
    rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH (hsub hA) (hlay A (hsub hA))
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hα := alphaCore_eq_bot_of_connected_frames hO hinv hbal hcon
  have hΔ := deltaCore_eq_bot_of_connected_frames hO hinv hbal hcon
  obtain ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩ := hsub hA₀
  obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal A₀ hA₀)
  have hzA : ∀ m, z m ∈ A₀ := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hK0A : K 0 ≤ Subgroup.centralizer (A₀ : Set G) := by
    rw [hAdef]
    exact triple_centralizes hK hcomm 0
  have hex : ExactMembers Ω :=
    exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hsingle hIH (hK 0).1 (hK 0).2
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hel hF₀.1)
      (hK0A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ A₀ hA₀ F₀ hF₀)
  have hP1 : LocalOddCentral Ω {z 0} :=
    localOddCentral_of_indepTriple_pair hnab hp2 hq hΩ hIH hex hlay hK hcomm hAdef hel hcard hF₀
      (hα A₀ hA₀ F₀ hF₀) (i := 0) (j := 1) (by decide) (x := z 0)
      (Subgroup.subset_closure (by simp)) (hK 0).2.ne_one
  exact ⟨hex, localOddCentral_of_classicalMember hp2 hf hΩ hsingle (hK 0).1 (hK 0).2 hP1⟩

@[expose] def ConnectedTrianglesExist (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∃ 𝒯 : Set (Subgroup G), 𝒯 ⊆ triangleFrames p f (CoreAssembly.conjClass K) ∧
          (∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯) ∧
          (∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
            Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') ∧ 𝒯.Nonempty

theorem bootTriple_of_triangleLayers_noCover (hlay : TriangleLayers p f)
    (htri : ConnectedTrianglesExist p f) (hcov9 : p ^ f = 9 → ConnectedFramesExist p f)
    (hexotic : ExoticLeviBlock p f) : CoreAssembly.BootTriple p f := by
  by_cases h9 : p ^ f = 9
  · exact bootTriple_of_triangleLayers hlay (hcov9 h9) hexotic
  · intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
    have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
    have hIH := localLieSystems_of_citBelowU hΩ hBelow
    obtain ⟨𝒯, hsub, hinv, hcon, A₀, hA₀⟩ := htri G hnab hp2 hq K z hz hBelow hconn hind
    obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_connectedTriangles hnab hp2 hq h9 hΩ
      (CoreAssembly.exists_single_class K) hIH
      (fun A' hA' => hlay G hnab hp2 hq K z hz hBelow hconn A' hA') hsub hinv hcon hA₀
    exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem connectedTrianglesExist_of_triangleConnected (htri : TriangleConnectedAll p f) :
    ConnectedTrianglesExist p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
  exact ⟨triangleFrames p f (CoreAssembly.conjClass K), fun _ h => h,
    fun _ hA g => indepTripleOn_map hΩ.conjInvariant hA g, htri G hnab hp2 hq K z hz hBelow hconn,
    Subgroup.closure (Set.range z'), K', z', hK', hcomm, rfl, hel, hcard⟩

theorem bootTriple_of_model_noCover (hmodel : LayerGenerationModel)
    (htri : ConnectedTrianglesExist p f) (hcov9 : p ^ f = 9 → ConnectedFramesExist p f)
    (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_triangleLayers_noCover
    (triangleLayers_of_triple (layerGenerationTriple_of_model hmodel) hF3) htri hcov9 hexotic

theorem bootTriple_of_model_triangle_noCover (hmodel : LayerGenerationModel)
    (htri : TriangleConnectedAll p f) (hcov9 : p ^ f = 9 → CoveredTriangleExists p f)
    (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_model_noCover hmodel (connectedTrianglesExist_of_triangleConnected htri)
    (fun h9 => connectedFramesExist_of_triangle htri (hcov9 h9)) hexotic hF3

end Assembly

end CFSG.ClassicalInvolution.Balance.Theorem5
