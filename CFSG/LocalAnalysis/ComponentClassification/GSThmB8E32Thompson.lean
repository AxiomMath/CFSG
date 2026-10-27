module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Step12
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Tr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Step12Input

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Eight

namespace S6M

theorem Vlist_evenfix_pair : (Vlist.all fun s => Vlist.all fun t =>
    s == 1 || t == 1 || s == t || decide (evenfixlen [s, t] ≤ 4)) = true := by
  decide +kernel

theorem swap_pair_fix : ([s01, s23, s45].all fun s => [s01, s23, s45].all fun t =>
    s == t || (allV.all fun v => allV.all fun w =>
      !(veq (v + act t v) (w + act s w)) || veq (act t v) v)) = true := by
  decide +kernel

theorem swaps_fix_K : (allV.all fun v => !(veq (act s01 v) v && veq (act s23 v) v &&
    veq (act s45 v) v) || Klist.contains v) = true := by
  decide +kernel

theorem zmod2_add_swap : ∀ a b c d : ZMod 2, a + b = c + d → a + d = c + b := by decide

theorem zmod2_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide

end S6M

open S6M

theorem exists_conj_le_of_relIndex {G : Type*} [Group G] [Finite G] {K T A : Subgroup G}
    (hTK : T ≤ K) (hT : IsPGroup 2 T) (hidx : ¬ 2 ∣ T.relIndex K) (hAK : A ≤ K)
    (hA : IsPGroup 2 A) : ∃ c ∈ K, conjugate A c ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf K) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  let S' : Sylow 2 K := hT'.toSylow hidx
  have hA' : IsPGroup 2 (A.subgroupOf K) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  obtain ⟨P, hP⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S'
  refine ⟨(g : G)⁻¹, inv_mem g.property, fun x hx => ?_⟩
  rw [mem_conjugate_iff, inv_inv] at hx
  have hxK : x ∈ K := by
    have h1 := hAK hx
    have h2 := mul_mem (mul_mem g.property h1) (inv_mem g.property)
    rwa [show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at h2
  have haP : (⟨(g : G)⁻¹ * x * g, hAK hx⟩ : K) ∈ (P : Subgroup K) := hP hx
  have hmem : MulAut.conj g (⟨(g : G)⁻¹ * x * g, hAK hx⟩ : K) ∈ ((g • P : Sylow 2 K) :
      Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ haP
  rw [hg] at hmem
  have hconj : MulAut.conj g (⟨(g : G)⁻¹ * x * g, hAK hx⟩ : K) = ⟨x, hxK⟩ := by
    apply Subtype.ext
    show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x
    group
  rw [hconj] at hmem
  have : (⟨x, hxK⟩ : K) ∈ T.subgroupOf K := by
    rw [← IsPGroup.toSylow_coe hT' hidx]
    exact hmem
  exact this

theorem exists_two_ne_one {G : Type*} [Group G] {S : Subgroup G} [Finite S]
    (hS : 2 < Nat.card S) : ∃ σ ∈ S, σ ≠ 1 ∧ ∃ σ' ∈ S, σ' ≠ 1 ∧ σ' ≠ σ := by
  have hfin : (S : Set G).Finite := Set.toFinite _
  have hcard : 2 < (S : Set G).ncard := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    exact hS
  by_contra hcon
  push Not at hcon
  by_cases hex : ∃ σ ∈ S, σ ≠ 1
  · obtain ⟨σ, hσ, hσ1⟩ := hex
    have hsub : (S : Set G) ⊆ {1, σ} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon σ hσ hσ1 x hx hx1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, σ} : Set G).ncard ≤ 2 := by
      calc ({1, σ} : Set G).ncard ≤ ({σ} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  · push Not at hex
    have hsub : (S : Set G) ⊆ {1} := fun x hx => hex x hx
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

theorem mem_E0_of_mem_conj_E0 {h x : X} (hx : x ∈ conjugate C.E0 h) (hxE : x ∈ C.E) :
    x ∈ C.E0 := by
  rw [mem_conjugate_iff] at hx
  have h1 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  have := C.fus_sc _ hx h (by rw [h1]; exact hxE)
  rwa [h1] at this

theorem mem_conj_E0_of_mem_E0 {h x : X} (hx : x ∈ conjugate C.E h) (hx0 : x ∈ C.E0) :
    x ∈ conjugate C.E0 h := by
  rw [mem_conjugate_iff] at hx ⊢
  have h1 : h⁻¹⁻¹ * x * h⁻¹ = h * x * h⁻¹ := by group
  have := C.fus_sc x hx0 h⁻¹ (by rw [h1]; exact hx)
  rwa [h1] at this

theorem mem_conj_E0_of_mem_conj_E0 {h y x : X} (hx : x ∈ conjugate C.E h)
    (hx0 : x ∈ conjugate C.E0 y) : x ∈ conjugate C.E0 h := by
  rw [mem_conjugate_iff] at hx hx0 ⊢
  have h1 : (y * h⁻¹)⁻¹ * (y * x * y⁻¹) * (y * h⁻¹) = h * x * h⁻¹ := by group
  have := C.fus_sc _ hx0 (y * h⁻¹) (by rw [h1]; exact hx)
  rwa [h1] at this

theorem not_swap_of_mem_conj_E0 {h x : X} (hx : x ∈ conjugate C.E0 h) (hxW : x ∈ C.W) :
    C.π ⟨x, hxW.2⟩ ∉ [s01, s23, s45] := by
  intro hs
  by_cases hx1 : x = 1
  · subst hx1
    apply one_not_mem_swaps
    have : (⟨1, hxW.2⟩ : ↥C.N) = 1 := rfl
    rwa [this, map_one] at hs
  · rw [mem_conjugate_iff] at hx
    refine C.fus_z (h * x * h⁻¹) hx (fun h1 => hx1 ?_) h ⟨x, hxW.2⟩ (by group) hxW.1
      (isSwap_of_mem hs)
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group

section Thompson

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
include hyU hyN hyW

omit hyU hyW in
theorem mul_coord {v v' : V5} {g g' : X} (hg : g ∈ conjugate C.E y) :
    C.θ v * g * (C.θ v' * g') =
      C.θ (v + act (C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩) v') * (g * g') := by
  rw [C.θ_add, ← C.θ_conj ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩ v']
  show C.θ v * g * (C.θ v' * g') = C.θ v * (g * C.θ v' * g⁻¹) * (g * g')
  group

omit hyU hyW in
theorem coord_of_comm {v v' : V5} {g g' : X} (hg : g ∈ conjugate C.E y)
    (hg' : g' ∈ conjugate C.E y) (hc : C.θ v * g * (C.θ v' * g') = C.θ v' * g' * (C.θ v * g)) :
    v + act (C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩) v' =
      v' + act (C.π ⟨g', (C.conj_le_W le_rfl hyN hg').2⟩) v := by
  rw [C.mul_coord hyN hg, C.mul_coord hyN hg', C.conj_E_comm hg hg'] at hc
  exact C.θ_injective (mul_right_cancel hc)

omit hyU hyW in
theorem fix_of_sq {v : V5} {g : X} (hg : g ∈ conjugate C.E y)
    (hsq : C.θ v * g * (C.θ v * g) = 1) :
    act (C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩) v = v := by
  rw [C.mul_coord hyN hg, C.conj_E_sq hg, mul_one, C.θ_eq_one_iff] at hsq
  funext i
  exact zmod2_add_eq_zero _ _ (congrFun hsq i)

omit hyU hyW in
theorem π_coord {v : V5} {g : X} (hg : g ∈ conjugate C.E y) (hN : C.θ v * g ∈ C.N) :
    C.π ⟨C.θ v * g, hN⟩ = C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩ := by
  have hθN : C.θ v ∈ C.N := (C.E_le_W (C.θ_mem v)).2
  rw [show (⟨C.θ v * g, hN⟩ : ↥C.N) = ⟨C.θ v, hθN⟩ * ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩ from rfl,
    map_mul, C.π_E (e := ⟨C.θ v, hθN⟩) (C.θ_mem v), one_mul]

theorem conj_E_eq_Ey_of_range {h : X} (hFQ : conjugate C.E h ≤ C.Q y)
    (hS : (C.ψW (hFQ.trans (C.Q_le_W hyN))).range = Vsub) :
    conjugate C.E h = conjugate C.E y := by
  have hFW : conjugate C.E h ≤ C.W := hFQ.trans (C.Q_le_W hyN)
  have hF2 : ∀ x ∈ conjugate C.E h, x * x = 1 := fun x hx => by
    rw [mem_conjugate_iff] at hx
    have := C.E_sq hx
    calc x * x = h⁻¹ * ((h * x * h⁻¹) * (h * x * h⁻¹)) * h := by group
      _ = 1 := by rw [this]; group
  have hFc : ∀ x ∈ conjugate C.E h, ∀ x' ∈ conjugate C.E h, x * x' = x' * x :=
    fun x hx x' hx' => Eight.comm_of_mul_self hF2 hx hx'
  have hcoord : ∀ f ∈ conjugate C.E h, ∃ v : V5, ∃ g ∈ conjugate C.E y, f = C.θ v * g := by
    intro f hf
    obtain ⟨e, he, g, hg, rfl⟩ := C.exists_mul_of_mem_Q hyN (hFQ hf)
    obtain ⟨v, rfl⟩ := C.mem_E_iff.mp he
    exact ⟨v, g, hg, rfl⟩
  have hπV : ∀ (v : V5) (g : X) (hg : g ∈ conjugate C.E y), C.θ v * g ∈ conjugate C.E h →
      C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩ ∈ Vsub := by
    intro v g hg hf
    rw [← hS, ← C.π_coord hyN hg (hFW hf).2]
    exact (C.mem_range_ψW hFW).mpr ⟨_, hf, rfl⟩
  have hget : ∀ t ∈ Vsub, ∃ v : V5, ∃ g, ∃ hg : g ∈ conjugate C.E y,
      C.θ v * g ∈ conjugate C.E h ∧ C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩ = t := by
    intro t ht
    rw [← hS] at ht
    obtain ⟨f, hf, hft⟩ := (C.mem_range_ψW hFW).mp ht
    obtain ⟨v, g, hg, rfl⟩ := hcoord f hf
    exact ⟨v, g, hg, hf, by rw [← hft, C.π_coord hyN hg]⟩
  have hpair : ∀ (v v' : V5) (g g' : X) (hg : g ∈ conjugate C.E y)
      (hg' : g' ∈ conjugate C.E y), C.θ v * g ∈ conjugate C.E h →
      C.θ v' * g' ∈ conjugate C.E h → ∀ s ∈ [s01, s23, s45], ∀ t ∈ [s01, s23, s45], s ≠ t →
      C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩ = s →
      C.π ⟨g', (C.conj_le_W le_rfl hyN hg').2⟩ = t → act t v = v := by
    intro v v' g g' hg hg' hf hf' s hs t ht hst hgs hgt
    have hc := C.coord_of_comm hyN hg hg' (hFc _ hf _ hf')
    rw [hgs, hgt] at hc
    have hB : v + act t v = v' + act s v' :=
      funext fun i => zmod2_add_swap _ _ _ _ (congrFun hc i)
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp swap_pair_fix s hs) t ht
    simp only [Bool.or_eq_true, beq_iff_eq, hst, false_or] at h1
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1 v (mem_allV v)) v' (mem_allV v')
    have h3 : veq (v + act t v) (v' + act s v') = true := veq_iff.mpr hB
    simp only [h3, Bool.not_true, Bool.false_or] at h2
    exact veq_iff.mp h2
  have hK : ∀ v : V5, act s01 v = v → act s23 v = v → act s45 v = v → v ∈ Klist := by
    intro v h01 h23 h45
    have h1 := List.all_eq_true.mp swaps_fix_K v (mem_allV v)
    simp only [veq_iff.mpr h01, veq_iff.mpr h23, veq_iff.mpr h45, Bool.and_self, Bool.not_true,
      Bool.false_or, List.contains_iff_mem] at h1
    exact h1
  have h01 : s01 ∈ Vsub := mem_listSub.mpr (by decide)
  have h23 : s23 ∈ Vsub := mem_listSub.mpr (by decide)
  have h45 : s45 ∈ Vsub := mem_listSub.mpr (by decide)
  obtain ⟨v₁, g₁, hg₁, hf₁, hπ₁⟩ := hget s01 h01
  obtain ⟨v₂, g₂, hg₂, hf₂, hπ₂⟩ := hget s23 h23
  obtain ⟨v₃, g₃, hg₃, hf₃, hπ₃⟩ := hget s45 h45
  have hsq : ∀ (v : V5) (g : X) (hg : g ∈ conjugate C.E y), C.θ v * g ∈ conjugate C.E h →
      act (C.π ⟨g, (C.conj_le_W le_rfl hyN hg).2⟩) v = v := fun v g hg hf =>
    C.fix_of_sq hyN hg (hF2 _ hf)
  have hv₁ : v₁ ∈ Klist := hK v₁ (hπ₁ ▸ hsq v₁ g₁ hg₁ hf₁)
    (hpair v₁ v₂ g₁ g₂ hg₁ hg₂ hf₁ hf₂ s01 (by simp) s23 (by simp) (by decide) hπ₁ hπ₂)
    (hpair v₁ v₃ g₁ g₃ hg₁ hg₃ hf₁ hf₃ s01 (by simp) s45 (by simp) (by decide) hπ₁ hπ₃)
  have hv₂ : v₂ ∈ Klist := hK v₂
    (hpair v₂ v₁ g₂ g₁ hg₂ hg₁ hf₂ hf₁ s23 (by simp) s01 (by simp) (by decide) hπ₂ hπ₁)
    (hπ₂ ▸ hsq v₂ g₂ hg₂ hf₂)
    (hpair v₂ v₃ g₂ g₃ hg₂ hg₃ hf₂ hf₃ s23 (by simp) s45 (by simp) (by decide) hπ₂ hπ₃)
  have hv₃ : v₃ ∈ Klist := hK v₃
    (hpair v₃ v₁ g₃ g₁ hg₃ hg₁ hf₃ hf₁ s45 (by simp) s01 (by simp) (by decide) hπ₃ hπ₁)
    (hpair v₃ v₂ g₃ g₂ hg₃ hg₂ hf₃ hf₂ s45 (by simp) s23 (by simp) (by decide) hπ₃ hπ₂)
    (hπ₃ ▸ hsq v₃ g₃ hg₃ hf₃)
  have hKfix : ∀ w ∈ Klist, ∀ t ∈ Vsub, act t w = w := by
    intro w hw t ht
    have h1 := List.all_eq_true.mp Vlist_fix.2 w hw
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    exact veq_iff.mp (h1.2 t (mem_listSub.mp ht))
  have hle : conjugate C.E h ≤ conjugate C.E y := by
    intro f hf
    obtain ⟨v, g, hg, rfl⟩ := hcoord f hf
    have hσ := hπV v g hg hf
    have hfix : ∀ (vi : V5) (gi : X) (hgi : gi ∈ conjugate C.E y), C.θ vi * gi ∈ conjugate C.E h →
        vi ∈ Klist → act (C.π ⟨gi, (C.conj_le_W le_rfl hyN hgi).2⟩) v = v := by
      intro vi gi hgi hfi hvi
      have hc := C.coord_of_comm hyN hg hgi (hFc _ hf _ hfi)
      rw [hKfix vi hvi _ hσ, add_comm v vi] at hc
      exact (add_left_cancel hc).symm
    have hvK : v ∈ Klist := hK v (hπ₁ ▸ hfix v₁ g₁ hg₁ hf₁ hv₁) (hπ₂ ▸ hfix v₂ g₂ hg₂ hf₂ hv₂)
      (hπ₃ ▸ hfix v₃ g₃ hg₃ hf₃ hv₃)
    have hθ : C.θ v ∈ conjugate C.E y ⊓ C.E := (C.mem_inf_iff hyU hyN hyW).mpr ⟨v, hvK, rfl⟩
    exact mul_mem (Subgroup.mem_inf.mp hθ).1 hg
  exact eq_of_le_of_card_ge hle (by rw [Eight.card_conjugate_eq, Eight.card_conjugate_eq])


theorem conj_E_eq_or {h : X} (hFQ : conjugate C.E h ≤ C.Q y) :
    conjugate C.E h = C.E ∨ conjugate C.E h = conjugate C.E y := by
  classical
  have hFW : conjugate C.E h ≤ C.W := hFQ.trans (C.Q_le_W hyN)
  have hF₀F : conjugate C.E0 h ≤ conjugate C.E h := C.conj_E0_le h
  have hF₀W : conjugate C.E0 h ≤ C.W := hF₀F.trans hFW
  have hF32 : Nat.card (conjugate C.E h) = 32 := by rw [Eight.card_conjugate_eq, C.card_E]
  have hF₀16 : Nat.card (conjugate C.E0 h) = 16 := by rw [Eight.card_conjugate_eq, C.card_E0]
  have hF2 : ∀ x ∈ conjugate C.E h, x * x = 1 := fun x hx => by
    rw [mem_conjugate_iff] at hx
    have := C.E_sq hx
    calc x * x = h⁻¹ * ((h * x * h⁻¹) * (h * x * h⁻¹)) * h := by group
      _ = 1 := by rw [this]; group
  have hFc : ∀ x ∈ conjugate C.E h, ∀ x' ∈ conjugate C.E h, x * x' = x' * x :=
    fun x hx x' hx' => Eight.comm_of_mul_self hF2 hx hx'
  have hc := C.card_eq_mul_of_le_W hFW
  have hc₀ := C.card_eq_mul_of_le_W hF₀W
  set S := (C.ψW hFW).range with hSdef
  set S₀ := (C.ψW hF₀W).range with hS₀def
  have hS₀S : S₀ ≤ S := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hF₀W).mp ht
    exact (C.mem_range_ψW hFW).mpr ⟨f, hF₀F hf, rfl⟩
  have hSV : S ≤ Vsub := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hFW).mp ht
    exact C.π_mem_V_of_mem_Q hyU hyN hyW (hFQ hf)
  have hns : ∀ t ∈ S₀, t ∉ [s01, s23, s45] := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψW hF₀W).mp ht
    exact C.not_swap_of_mem_conj_E0 hf (hF₀W hf)
  have hinf : conjugate C.E0 h ⊓ C.E = conjugate C.E h ⊓ C.E0 := by
    ext x
    constructor
    · rintro ⟨hx0, hxE⟩
      exact ⟨hF₀F hx0, C.mem_E0_of_mem_conj_E0 hx0 hxE⟩
    · rintro ⟨hxF, hx0⟩
      exact ⟨C.mem_conj_E0_of_mem_E0 hxF hx0, C.E0_le_E hx0⟩
  have hle2 : Nat.card ↥(conjugate C.E h ⊓ C.E) ≤ 2 * Nat.card ↥(conjugate C.E h ⊓ C.E0) := by
    have h1 := Eight.card_le_two_mul_card_inf (A := conjugate C.E h ⊓ C.E) (K := C.E0)
      fun x hx x' hx' h0 h0' => by
        rw [inv_eq_of_mul_eq_one_right (C.E_sq (Subgroup.mem_inf.mp hx).2)]
        exact C.mul_mem_E0 (Subgroup.mem_inf.mp hx).2 (Subgroup.mem_inf.mp hx').2 h0 h0'
    have h2 : conjugate C.E h ⊓ C.E ⊓ C.E0 = conjugate C.E h ⊓ C.E0 := by
      rw [inf_assoc, inf_eq_right.mpr C.E0_le_E]
    rwa [h2] at h1
  have hdvd : Nat.card ↥(conjugate C.E h ⊓ C.E0) ∣ Nat.card ↥(conjugate C.E h ⊓ C.E) :=
    Subgroup.card_dvd_of_le (inf_le_inf_left _ C.E0_le_E)
  have hSdvd : Nat.card S₀ ∣ Nat.card S := Subgroup.card_dvd_of_le hS₀S
  have hS8 : Nat.card S ≤ 8 := by rw [← card_Vsub]; exact Subgroup.card_le_of_le hSV
  have hSdvd8 : Nat.card S ∣ 8 := by rw [← card_Vsub]; exact Subgroup.card_dvd_of_le hSV
  have ha0 : 0 < Nat.card ↥(conjugate C.E h ⊓ C.E0) := Nat.card_pos
  rw [hF32] at hc
  rw [hF₀16, hinf] at hc₀
  have hfixF : ∀ a ∈ conjugate C.E h ⊓ C.E, ∃ v ∈ fixSet (S : Set (Equiv.Perm (Fin 6))),
      C.θ v = a := by
    intro a ha
    obtain ⟨v, rfl⟩ := C.mem_E_iff.mp (Subgroup.mem_inf.mp ha).2
    exact ⟨v, C.fix_of_le_W hFW hFc (Subgroup.mem_inf.mp ha).1, rfl⟩
  have hS₀cases : Nat.card S₀ = 1 ∨ Nat.card S₀ = 2 ∨ (Nat.card S₀ = 4 ∧ S₀ = V0sub) := by
    have hpos : 0 < Nat.card S₀ := Nat.card_pos
    rcases noswap_cases S₀ (hS₀S.trans hSV) hns with hS₀V0 | hS₀t
    · have hd : Nat.card S₀ ∣ 4 := by rw [← card_V0sub]; exact Subgroup.card_dvd_of_le hS₀V0
      have h4 : Nat.card S₀ ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      interval_cases hs : Nat.card S₀
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hd (by norm_num)
      · exact Or.inr (Or.inr ⟨rfl, eq_of_le_of_card_ge hS₀V0 (by rw [card_V0sub, hs])⟩)
    · have h2 : Nat.card S₀ ≤ 2 := by
        have hsub : (S₀ : Set (Equiv.Perm (Fin 6))) ⊆ {1, t135} := fun t ht => by
          rcases hS₀t t ht with h | h
          · exact Or.inl h
          · exact Or.inr h
        calc Nat.card S₀ = (S₀ : Set (Equiv.Perm (Fin 6))).ncard := (Nat.card_coe_set_eq _).symm
          _ ≤ ({1, t135} : Set (Equiv.Perm (Fin 6))).ncard := Set.ncard_le_ncard hsub
          _ ≤ 2 := ncard_pair_le _ _
      interval_cases hs : Nat.card S₀
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hk : Nat.card ↥(conjugate C.E h ⊓ C.E) = Nat.card ↥(conjugate C.E h ⊓ C.E0) ∨
      Nat.card ↥(conjugate C.E h ⊓ C.E) = 2 * Nat.card ↥(conjugate C.E h ⊓ C.E0) := by
    obtain ⟨k, hkd⟩ := hdvd
    have hk2 : k ≤ 2 := by
      refine Nat.le_of_mul_le_mul_left ?_ ha0
      rw [← hkd]
      omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hkd
        exact absurd hkd (Nat.card_pos (α := ↥(conjugate C.E h ⊓ C.E))).ne'
      · exact h0
    interval_cases k
    · left; rw [hkd, mul_one]
    · right; rw [hkd, mul_comm]
  have hfixL : ∀ L : List (Equiv.Perm (Fin 6)), (∀ t ∈ L, t ∈ S) →
      Nat.card ↥(conjugate C.E h ⊓ C.E) ≤ fixlen L := fun L hL =>
    (C.card_le_ncard _ hfixF).trans (fixSet_ncard_le hL)
  rcases hS₀cases with h1 | h2 | ⟨h4, hS₀eq⟩
  ·
    left
    have ha₀ : Nat.card ↥(conjugate C.E h ⊓ C.E0) = 16 := by rw [h1, mul_one] at hc₀; omega
    have hE0F : C.E0 ≤ conjugate C.E h := by
      have heq : conjugate C.E h ⊓ C.E0 = C.E0 :=
        eq_of_le_of_card_ge inf_le_right (by rw [C.card_E0, ha₀])
      rw [← heq]
      exact inf_le_left
    have hFE : conjugate C.E h ≤ C.E := fun x hx =>
      C.mem_E_of_comm_E0 hyU hyN hyW (hFQ hx) fun e he => hFc x hx e (hE0F he)
    exact eq_of_le_of_card_ge hFE (by rw [C.card_E, hF32])
  ·
    exfalso
    have ha₀ : Nat.card ↥(conjugate C.E h ⊓ C.E0) = 8 := by rw [h2] at hc₀; omega
    rcases hk with hk | hk
    ·
      have ha : Nat.card ↥(conjugate C.E h ⊓ C.E) = 8 := by omega
      have hs4 : Nat.card S = 4 := by rw [ha] at hc; omega
      have hEE0 : conjugate C.E h ⊓ C.E ≤ C.E0 := by
        have heq : conjugate C.E h ⊓ C.E0 = conjugate C.E h ⊓ C.E :=
          eq_of_le_of_card_ge (inf_le_inf_left _ C.E0_le_E) (by rw [ha, ha₀])
        rw [← heq]
        exact inf_le_right
      obtain ⟨σ, hσ, hσ1, σ', hσ', hσ'1, hσσ'⟩ := exists_two_ne_one (by omega : 2 < Nat.card S)
      have hlen : Nat.card ↥(conjugate C.E h ⊓ C.E) ≤ evenfixlen [σ, σ'] := by
        refine C.card_le_length _ fun x hx => ?_
        obtain ⟨v, hv, rfl⟩ := hfixF x hx
        refine ⟨v, ?_, rfl⟩
        obtain ⟨w, hw, hwv⟩ := C.mem_E0_iff.mp (hEE0 hx)
        rw [C.θ_inj_iff] at hwv
        subst hwv
        simp only [Bool.and_eq_true, isEvenB_iff.mpr hw, true_and, List.all_eq_true]
        intro t ht
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl
        · exact veq_iff.mpr (hv _ hσ)
        · exact veq_iff.mpr (hv _ hσ')
      have hev := List.all_eq_true.mp (List.all_eq_true.mp Vlist_evenfix_pair σ
        (mem_listSub.mp (hSV hσ))) σ' (mem_listSub.mp (hSV hσ'))
      simp only [Bool.or_eq_true, beq_iff_eq, hσ1, hσ'1, (Ne.symm hσσ'), decide_eq_true_eq,
        false_or] at hev
      omega
    ·
      have ha : Nat.card ↥(conjugate C.E h ⊓ C.E) = 16 := by omega
      have hs2 : Nat.card S = 2 := by rw [ha] at hc; omega
      have hSS₀ : S₀ = S := eq_of_le_of_card_ge hS₀S (by rw [hs2, h2])
      obtain ⟨⟨t, ht⟩, ht1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
        ((Subgroup.one_lt_card_iff_ne_bot S₀).mp (by omega))
      have ht1 : t ≠ 1 := fun h1 => ht1' (Subtype.ext h1)
      have htV : t ∈ Vlist := mem_listSub.mp (hSV (hS₀S ht))
      have htW : t ∈ Wlist := by
        have := List.all_eq_true.mp Vlist_sub t htV
        simpa using this
      have h8 := List.all_eq_true.mp Wlist_fix8 t htW
      simp only [Bool.or_eq_true, beq_iff_eq, ht1, false_or, List.contains_iff_mem,
        decide_eq_true_eq] at h8
      have h8' : fixlen [t] ≤ 8 := h8.resolve_left (hns t ht)
      have := hfixL [t] (by
        intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rw [hu, ← hSS₀]
        exact ht)
      omega
  ·
    have ha₀ : Nat.card ↥(conjugate C.E h ⊓ C.E0) = 4 := by rw [h4] at hc₀; omega
    rcases hk with hk | hk
    ·
      right
      have ha : Nat.card ↥(conjugate C.E h ⊓ C.E) = 4 := by omega
      have hs8 : Nat.card S = 8 := by rw [ha] at hc; omega
      have hSeq : S = Vsub := eq_of_le_of_card_ge hSV (by rw [card_Vsub, hs8])
      exact C.conj_E_eq_Ey_of_range hyU hyN hyW hFQ hSeq
    ·
      exfalso
      have ha : Nat.card ↥(conjugate C.E h ⊓ C.E) = 8 := by omega
      have hs4 : Nat.card S = 4 := by rw [ha] at hc; omega
      have hSS₀ : S₀ = S := eq_of_le_of_card_ge hS₀S (by rw [hs4, h4])
      have := hfixL V0list (by
        intro u hu
        rw [← hSS₀, hS₀eq]
        exact mem_listSub.mpr hu)
      rw [t135_facts.2] at this
      omega

theorem χ_eq_neg_one_of_mem_E (m : ↥(C.M1 y)) (hmE : (m : X) ∈ C.E) (hm0 : (m : X) ∉ C.E0) :
    C.χ hyU hyN hyW m = -1 := by
  have hf : y * (m : X) * y⁻¹ ∈ conjugate C.E y := by
    rw [← C.conj_inv_eq hyU hyN hyW C.W_le_normalizer_E, mem_conjugate_iff, inv_inv]
    rwa [show y⁻¹ * (y * (m : X) * y⁻¹) * y = m by group]
  have hπV : C.π ⟨y * m * y⁻¹, C.conj_y_mem_N hyU hyN hyW m.2⟩ ∈ Vsub := by
    rw [← C.range_ψ_eq hyU hyN hyW]
    exact (C.mem_range_ψ le_rfl hyN).mpr ⟨_, hf, rfl⟩
  have hπ0 : C.π ⟨y * m * y⁻¹, C.conj_y_mem_N hyU hyN hyW m.2⟩ ∉ V0list := by
    intro h0
    have hfW := C.conj_le_W le_rfl hyN hf
    obtain ⟨e, he, g₀, hg₀, hfe⟩ := C.exists_mul_of_π0 hyU hyN hyW hfW h0
    have heK : e ∈ conjugate C.E y ⊓ C.E := by
      refine Subgroup.mem_inf.mpr ⟨?_, he⟩
      rw [show e = (y * (m : X) * y⁻¹) * g₀⁻¹ by rw [hfe]; group]
      exact mul_mem hf (inv_mem (C.conj_E0_le y hg₀))
    obtain ⟨v, hv, rfl⟩ := (C.mem_inf_iff hyU hyN hyW).mp heK
    have hf0 : y * (m : X) * y⁻¹ ∈ conjugate C.E0 y :=
      hfe ▸ mul_mem (C.K_le_E0y hyU hyN hyW hv) hg₀
    rw [mem_conjugate_iff] at hf0
    have h1 := C.conj_E0_mem ⟨(y * y)⁻¹, inv_mem (C.sq_mem_W hyU hyN hyW).2⟩ hf0
    rw [show (y * y)⁻¹ * (y * (y * (m : X) * y⁻¹) * y⁻¹) * (y * y)⁻¹⁻¹ = m by group] at h1
    exact hm0 h1
  have hodd : C.π ⟨y * m * y⁻¹, C.conj_y_mem_N hyU hyN hyW m.2⟩ ∈ [s01, s23, s45, t135] := by
    have h1 := List.all_eq_true.mp Vlist_split _ (mem_listSub.mp hπV)
    simp only [Bool.or_eq_true, List.contains_iff_mem] at h1
    exact h1.resolve_left hπ0
  simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [C.π_E (e := ⟨(m : X), m.2.2⟩) hmE, map_one, one_mul, sign_odd hodd]

theorem χ_eq_neg_one_of_mem_Ey (m : ↥(C.M1 y)) (hmE : (m : X) ∈ conjugate C.E y)
    (hm0 : (m : X) ∉ conjugate C.E0 y) : C.χ hyU hyN hyW m = -1 := by
  have hyE : y * (m : X) * y⁻¹ ∈ C.E := by rwa [mem_conjugate_iff] at hmE
  have hmW : (m : X) ∈ C.W := C.conj_le_W le_rfl hyN hmE
  have hπV : C.π ⟨m, hmW.2⟩ ∈ Vsub := by
    rw [← C.range_ψ_eq hyU hyN hyW]
    exact (C.mem_range_ψ le_rfl hyN).mpr ⟨_, hmE, rfl⟩
  have hπ0 : C.π ⟨m, hmW.2⟩ ∉ V0list := by
    intro h0
    obtain ⟨e, he, g₀, hg₀, hme⟩ := C.exists_mul_of_π0 hyU hyN hyW hmW (mem_listSub.mpr h0)
    have heK : e ∈ conjugate C.E y ⊓ C.E := by
      refine Subgroup.mem_inf.mpr ⟨?_, he⟩
      rw [show e = (m : X) * g₀⁻¹ by rw [hme]; group]
      exact mul_mem hmE (inv_mem (C.conj_E0_le y hg₀))
    obtain ⟨v, hv, rfl⟩ := (C.mem_inf_iff hyU hyN hyW).mp heK
    exact hm0 (hme ▸ mul_mem (C.K_le_E0y hyU hyN hyW hv) hg₀)
  have hodd : C.π ⟨m, hmW.2⟩ ∈ [s01, s23, s45, t135] := by
    have h1 := List.all_eq_true.mp Vlist_split _ (mem_listSub.mp hπV)
    simp only [Bool.or_eq_true, List.contains_iff_mem] at h1
    exact h1.resolve_left hπ0
  simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [C.π_E (e := ⟨y * (m : X) * y⁻¹, C.conj_y_mem_N hyU hyN hyW m.2⟩) hyE, map_one, mul_one]
  exact sign_odd hodd

omit hyU hyW in
theorem W_le_M1 : C.W ≤ C.M1 y := le_inf (C.W_le_normalizer_Q hyN) C.W_le_normalizer_E

theorem mul_inv_y_mem_W {u : X} (hu : u ∈ C.U) (huW : u ∉ C.W) : u * y⁻¹ ∈ C.W := by
  have hu' : u ∈ C.NUW := by rw [C.NUW_eq hyU hyN hyW]; exact hu
  exact (C.mem_W_or hyU hyN hyW u hu').resolve_left huW

theorem χ_conj_y {w : X} (hw : w ∈ C.W) (hw' : y * w * y⁻¹ ∈ C.W) :
    C.χ hyU hyN hyW ⟨y * w * y⁻¹, C.W_le_M1 hyN hw'⟩ =
      C.χ hyU hyN hyW ⟨w, C.W_le_M1 hyN hw⟩ := by
  rw [← C.χ_conj hyU hyN hyW ⟨y * w * y⁻¹, C.W_le_M1 hyN hw'⟩]
  congr 1
  apply Subtype.ext
  show y⁻¹ * (y * w * y⁻¹) * y = w
  group

open scoped Classical in
@[expose] noncomputable def χUfun (u : X) : ℤˣ :=
  if hu : u ∈ C.W then C.χ hyU hyN hyW ⟨u, C.W_le_M1 hyN hu⟩
  else if hu' : u * y⁻¹ ∈ C.W then C.χ hyU hyN hyW ⟨u * y⁻¹, C.W_le_M1 hyN hu'⟩
  else 1

theorem χUfun_of_mem {w : X} (hw : w ∈ C.W) :
    C.χUfun hyU hyN hyW w = C.χ hyU hyN hyW ⟨w, C.W_le_M1 hyN hw⟩ := by
  rw [χUfun, dite_eq_left hw]

theorem χUfun_of_not_mem {u : X} (huW : u ∉ C.W) (hu' : u * y⁻¹ ∈ C.W) :
    C.χUfun hyU hyN hyW u = C.χ hyU hyN hyW ⟨u * y⁻¹, C.W_le_M1 hyN hu'⟩ := by
  rw [χUfun, dite_eq_right huW, dite_eq_left hu']

theorem χ_mul_of_eq {m m₁ m₂ : ↥(C.M1 y)} (h : (m : X) = m₁ * m₂) :
    C.χ hyU hyN hyW m = C.χ hyU hyN hyW m₁ * C.χ hyU hyN hyW m₂ := by
  rw [show m = m₁ * m₂ from Subtype.ext h, map_mul]

@[expose] noncomputable def χU : ↥C.U →* ℤˣ where
  toFun u := C.χUfun hyU hyN hyW u
  map_one' := by
    show C.χUfun hyU hyN hyW 1 = 1
    rw [C.χUfun_of_mem hyU hyN hyW (one_mem _)]
    exact map_one _
  map_mul' u u' := by
    have hyW2 := C.sq_mem_W hyU hyN hyW
    by_cases hu : (u : X) ∈ C.W <;> by_cases hu' : (u' : X) ∈ C.W
    · have huu' : (u : X) * u' ∈ C.W := mul_mem hu hu'
      show C.χUfun hyU hyN hyW ((u : X) * u') = _
      rw [C.χUfun_of_mem hyU hyN hyW huu', C.χUfun_of_mem hyU hyN hyW hu,
        C.χUfun_of_mem hyU hyN hyW hu']
      exact C.χ_mul_of_eq hyU hyN hyW rfl
    · have hv' := C.mul_inv_y_mem_W hyU hyN hyW u'.2 hu'
      have huu' : (u : X) * u' ∉ C.W := fun h => hu' (by
        rw [show (u' : X) = (u : X)⁻¹ * (u * u') by group]
        exact mul_mem (inv_mem hu) h)
      have hv : (u : X) * u' * y⁻¹ ∈ C.W := by
        rw [show (u : X) * u' * y⁻¹ = u * (u' * y⁻¹) by group]
        exact mul_mem hu hv'
      show C.χUfun hyU hyN hyW ((u : X) * u') = _
      rw [C.χUfun_of_not_mem hyU hyN hyW huu' hv, C.χUfun_of_mem hyU hyN hyW hu,
        C.χUfun_of_not_mem hyU hyN hyW hu' hv']
      exact C.χ_mul_of_eq hyU hyN hyW (by show (u : X) * u' * y⁻¹ = u * (u' * y⁻¹); group)
    · have hv := C.mul_inv_y_mem_W hyU hyN hyW u.2 hu
      have hyu' : y * (u' : X) * y⁻¹ ∈ C.W := (mem_normalizer_iff.mp hyN _).mp hu'
      have huu' : (u : X) * u' ∉ C.W := fun h => hu (by
        rw [show (u : X) = (u * u') * (u' : X)⁻¹ by group]
        exact mul_mem h (inv_mem hu'))
      have hw : (u : X) * u' * y⁻¹ ∈ C.W := by
        rw [show (u : X) * u' * y⁻¹ = (u * y⁻¹) * (y * u' * y⁻¹) by group]
        exact mul_mem hv hyu'
      show C.χUfun hyU hyN hyW ((u : X) * u') = _
      rw [C.χUfun_of_not_mem hyU hyN hyW huu' hw, C.χUfun_of_not_mem hyU hyN hyW hu hv,
        C.χUfun_of_mem hyU hyN hyW hu', ← C.χ_conj_y hyU hyN hyW hu' hyu']
      exact C.χ_mul_of_eq hyU hyN hyW
        (by show (u : X) * u' * y⁻¹ = (u * y⁻¹) * (y * u' * y⁻¹); group)
    · have hv := C.mul_inv_y_mem_W hyU hyN hyW u.2 hu
      have hv' := C.mul_inv_y_mem_W hyU hyN hyW u'.2 hu'
      have hyv' : y * ((u' : X) * y⁻¹) * y⁻¹ ∈ C.W := (mem_normalizer_iff.mp hyN _).mp hv'
      have huu' : (u : X) * u' ∈ C.W := by
        rw [show (u : X) * u' = (u * y⁻¹) * (y * (u' * y⁻¹) * y⁻¹) * (y * y) by group]
        exact mul_mem (mul_mem hv hyv') hyW2
      show C.χUfun hyU hyN hyW ((u : X) * u') = _
      rw [C.χUfun_of_mem hyU hyN hyW huu', C.χUfun_of_not_mem hyU hyN hyW hu hv,
        C.χUfun_of_not_mem hyU hyN hyW hu' hv']
      have h1 : C.χ hyU hyN hyW ⟨(u : X) * u', C.W_le_M1 hyN huu'⟩ =
          C.χ hyU hyN hyW ⟨(u : X) * y⁻¹, C.W_le_M1 hyN hv⟩ *
            C.χ hyU hyN hyW ⟨y * ((u' : X) * y⁻¹) * y⁻¹, C.W_le_M1 hyN hyv'⟩ *
            C.χ hyU hyN hyW ⟨y * y, C.W_le_M1 hyN hyW2⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show (u : X) * u' = (u * y⁻¹) * (y * (u' * y⁻¹) * y⁻¹) * (y * y)
        group
      rw [h1, C.χ_conj_y hyU hyN hyW hv' hyv']
      have h2 : C.χ hyU hyN hyW ⟨y * y, C.W_le_M1 hyN hyW2⟩ = 1 :=
        C.χ_sq_y hyU hyN hyW
      rw [h2, mul_one]

theorem χU_of_mem (w : ↥C.U) (hw : (w : X) ∈ C.W) :
    C.χU hyU hyN hyW w = C.χ hyU hyN hyW ⟨w, C.W_le_M1 hyN hw⟩ :=
  C.χUfun_of_mem hyU hyN hyW hw

end Thompson

include C in
theorem false_of_simple [IsSimpleGroup X] (hnab : ∃ u v : X, u * v ≠ v * u) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := C.U_sylow
  have hU2 : IsPGroup 2 C.U := hT ▸ T.isPGroup'
  have hUidx : ¬ 2 ∣ C.U.index := hT ▸ T.not_dvd_index
  obtain ⟨y, hyU, hyW, hyn⟩ :=
    Eight.exists_mem_normalizer_not_mem hU2 (inf_le_left : C.W ≤ C.U) C.W_ne
  have hyN : y ∈ normalizer (C.W : Set X) := by
    have := Eight.mem_normalizer_of_conj_mem (C := C.W) (s := y⁻¹) fun c hc => by
      rw [inv_inv]
      exact hyn c hc
    simpa using inv_mem this
  have hNUW := C.NUW_eq hyU hyN hyW
  let σ₂ : ℤˣ ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) (by rw [Nat.card_eq_fintype_card]; rfl)
      (by rw [Nat.card_eq_fintype_card]; rfl)
  let χ₂ : ↥C.U →* Multiplicative (ZMod 2) := σ₂.toMonoidHom.comp (C.χU hyU hyN hyW)
  have hσ₂ : σ₂ (-1) ≠ 1 := fun h => by
    have : (-1 : ℤˣ) = 1 := σ₂.injective (h.trans σ₂.map_one.symm)
    exact absurd this (by decide)
  have hodd : ∀ (v : X) (hvU : v ∈ C.U) (hvW : v ∈ C.W),
      C.χ hyU hyN hyW ⟨v, C.W_le_M1 hyN hvW⟩ = -1 → χ₂ ⟨v, hvU⟩ ≠ 1 := by
    intro v hvU hvW hv
    show σ₂ (C.χU hyU hyN hyW ⟨v, hvU⟩) ≠ 1
    rw [C.χU_of_mem hyU hyN hyW ⟨v, hvU⟩ hvW, hv]
    exact hσ₂
  have hc4E : C.c 4 ∈ C.E := C.c_mem_E 4
  have hc4W : C.c 4 ∈ C.W := C.E_le_W hc4E
  have hu : χ₂ ⟨C.c 4, C.c_mem 4⟩ ≠ 1 :=
    hodd _ _ hc4W (C.χ_eq_neg_one_of_mem_E hyU hyN hyW _ hc4E (C.c4_not_mem_E0))
  have hext : ∀ (g : X) (hg : g⁻¹ * C.c 4 * g ∈ C.U),
      GH74.GLS.Bg.Thompson.IsExtremalIn 2 C.U (g⁻¹ * C.c 4 * g) →
        χ₂ ⟨g⁻¹ * C.c 4 * g, hg⟩ ≠ 1 := by
    intro g hg hex
    set v := g⁻¹ * C.c 4 * g with hvdef
    have hvF : v ∈ conjugate C.E g := by
      rw [mem_conjugate_iff, hvdef, show g * (g⁻¹ * C.c 4 * g) * g⁻¹ = C.c 4 by group]
      exact hc4E
    have hF2 : ∀ x ∈ conjugate C.E g, x * x = 1 := fun x hx => by
      rw [mem_conjugate_iff] at hx
      have := C.E_sq hx
      calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = 1 := by rw [this]; group
    have hFC : conjugate C.E g ≤ centralizer ({v} : Set X) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (Eight.comm_of_mul_self hF2 hx hvF)
    have hFp : IsPGroup 2 (conjugate C.E g) :=
      IsPGroup.of_card (n := 5) (by rw [Eight.card_conjugate_eq, C.card_E]; norm_num)
    obtain ⟨hle, hp, hidx⟩ := hex
    obtain ⟨c, hc, hcF⟩ := exists_conj_le_of_relIndex hle hp hidx hFC hFp
    have hFU : conjugate C.E (g * c) ≤ C.NUW := by
      rw [hNUW, ← conjugate_conjugate]
      exact hcF.trans inf_le_left
    have hFQ := C.conj_E_le_Q hyU hyN hyW hFU
    have hvc : (g * c)⁻¹ * C.c 4 * (g * c) = v := by
      have hcv : v * c = c * v := (mem_centralizer_singleton_iff.mp hc).symm
      calc (g * c)⁻¹ * C.c 4 * (g * c) = c⁻¹ * v * c := by rw [hvdef]; group
        _ = v := by rw [mul_assoc, hcv, ← mul_assoc, inv_mul_cancel, one_mul]
    have hvF' : v ∈ conjugate C.E (g * c) := by
      rw [mem_conjugate_iff, ← hvc, show g * c * ((g * c)⁻¹ * C.c 4 * (g * c)) * (g * c)⁻¹ =
        C.c 4 by group]
      exact hc4E
    have hvnot : v ∉ conjugate C.E0 (g * c) := by
      rw [mem_conjugate_iff, ← hvc, show g * c * ((g * c)⁻¹ * C.c 4 * (g * c)) * (g * c)⁻¹ =
        C.c 4 by group]
      exact C.c4_not_mem_E0
    have hvW : v ∈ C.W := C.Q_le_W hyN (hFQ hvF')
    refine hodd v hg hvW ?_
    rcases C.conj_E_eq_or hyU hyN hyW hFQ with hE | hEy
    · have hvE : v ∈ C.E := hE ▸ hvF'
      refine C.χ_eq_neg_one_of_mem_E hyU hyN hyW _ hvE fun h0 => hvnot ?_
      exact C.mem_conj_E0_of_mem_E0 hvF' h0
    · have hvE : v ∈ conjugate C.E y := hEy ▸ hvF'
      refine C.χ_eq_neg_one_of_mem_Ey hyU hyN hyW _ hvE fun h0 => hvnot ?_
      exact C.mem_conj_E0_of_mem_conj_E0 hvF' h0
  obtain ⟨N, hN, hcyc, -, hc4N⟩ :=
    X11.exists_normal_of_character hU2 hUidx χ₂ (C.c_mem 4) hu (C.c_sq 4) hext
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨u, w, huw⟩ := hnab
      apply huw
      have : ⁅u, w⁆ ∈ commutator X := commutator_mem_commutator (mem_top u) (mem_top w)
      rw [h, mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    · exact h
  exact X11.not_mem_commutator_of_normal hcyc hc4N (hcomm ▸ mem_top _)

end E32Conf

theorem gs83Step12Input : GS83Step12Input := by
  intro X _ _ h H _ C
  have : IsSimpleGroup X := H.setting.1
  exact C.false_of_simple H.setting.2.1

end Eight

end CFSG.ComponentClassification.GSThmB
