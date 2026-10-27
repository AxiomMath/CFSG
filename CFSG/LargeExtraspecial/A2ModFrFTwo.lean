module

public import CFSG.LargeExtraspecial.A2ModFrFGen

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS

abbrev negRoots : List (Fin 4 → ℤ) :=
  [![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1], ![-1, -1, 0, 0],
    ![0, -1, -1, 0], ![0, 0, -1, -1], ![-1, -1, -1, 0], ![0, -1, -2, 0], ![0, -1, -1, -1],
    ![-1, -1, -2, 0], ![-1, -1, -1, -1], ![0, -1, -2, -1], ![-1, -2, -2, 0], ![-1, -1, -2, -1],
    ![0, -1, -2, -2], ![-1, -2, -2, -1], ![-1, -1, -2, -2], ![-1, -2, -3, -1], ![-1, -2, -2, -2],
    ![-1, -2, -3, -2], ![-1, -2, -4, -2], ![-1, -3, -4, -2], ![-2, -3, -4, -2]]

section Roots

variable (hA : TauCeti.IsFiniteType f4M)

theorem roots_subset_f4Roots : roots hA ∅ ⊆ (f4Roots : Set (Fin 4 → ℤ)) :=
  roots_subset_of_closed hA _ (by decide)
    (fun v hv k => by rw [reflection_eq_reflF]; exact f4Roots_closed v hv k)

theorem negSingle_mem (i : Fin 4) {v : Fin 4 → ℤ} (h : -(Pi.single i 1 : Fin 4 → ℤ) = v) :
    v ∈ roots hA ∅ :=
  h ▸ (RootSystem.ofCartan hA ∅).neg_mem _ ((RootSystem.ofCartan hA ∅).single_mem i)

theorem mem_roots_of_reflF {v w : Fin 4 → ℤ} (hv : v ∈ roots hA ∅) (k : Fin 4)
    (h : reflF f4M k v = w) : w ∈ roots hA ∅ := by
  rw [← h, ← weylAction_simple_eq hA]
  exact weylAction_mem_roots _ _ hv

theorem mem_roots_of_mem_negRoots {γ : Fin 4 → ℤ} (hγ : γ ∈ negRoots) : γ ∈ roots hA ∅ := by
  have h0 : (![-1, 0, 0, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := negSingle_mem hA 0 (by decide)
  have h1 : (![0, -1, 0, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := negSingle_mem hA 1 (by decide)
  have h2 : (![0, 0, -1, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := negSingle_mem hA 2 (by decide)
  have h3 : (![0, 0, 0, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := negSingle_mem hA 3 (by decide)
  have h4 : (![-1, -1, 0, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h0 1 (by decide)
  have h5 : (![0, -1, -2, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h1 2 (by decide)
  have h6 : (![0, -1, -1, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h2 1 (by decide)
  have h7 : (![0, 0, -1, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h2 3 (by decide)
  have h8 : (![-1, -1, -2, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h4 2 (by decide)
  have h9 : (![0, -1, -2, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h5 3 (by decide)
  have h10 : (![-1, -1, -1, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h6 0 (by decide)
  have h11 : (![0, -1, -1, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h6 3 (by decide)
  have h12 : (![-1, -2, -2, 0] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h8 1 (by decide)
  have h13 : (![-1, -1, -2, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h8 3 (by decide)
  have h14 : (![-1, -1, -1, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h10 3 (by decide)
  have h15 : (![0, -1, -2, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h11 2 (by decide)
  have h16 : (![-1, -2, -2, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h12 3 (by decide)
  have h17 : (![-1, -1, -2, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h14 2 (by decide)
  have h18 : (![-1, -2, -4, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h16 2 (by decide)
  have h19 : (![-1, -2, -2, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h17 1 (by decide)
  have h20 : (![-1, -3, -4, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h18 1 (by decide)
  have h21 : (![-1, -2, -3, -1] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h19 2 (by decide)
  have h22 : (![-2, -3, -4, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h20 0 (by decide)
  have h23 : (![-1, -2, -3, -2] : Fin 4 → ℤ) ∈ roots hA ∅ := mem_roots_of_reflF hA h21 3 (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem mem_negRoots_iff (γ : Fin 4 → ℤ) :
    γ ∈ negRoots ↔ γ ∈ roots hA ∅ ∧ ht γ < 0 ∧ ∀ δ ∈ roots hA ∅, γ ≠ 2 • δ := by
  constructor
  · intro hγ
    refine ⟨mem_roots_of_mem_negRoots hA hγ,
      (by decide : ∀ v ∈ negRoots, ht v < 0) γ hγ, fun δ hδ e => ?_⟩
    have hδ' := roots_subset_f4Roots hA hδ
    exact (by decide : ∀ v ∈ f4Roots, 2 • v ∉ negRoots) δ hδ' (e ▸ hγ)
  · rintro ⟨hγ, hneg, -⟩
    exact (by decide : ∀ v ∈ f4Roots, ht v < 0 → v ∈ negRoots) γ (roots_subset_f4Roots hA hγ)
      hneg

theorem negRoots_nodup : negRoots.Nodup := by decide

theorem negRoots_sorted : negRoots.Pairwise (fun γ δ => ht δ ≤ ht γ) := by decide

end Roots

namespace F4Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : F4Frame G R}

theorem isLong_of_form {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) (h : (form F.hA).Q γ γ = 4) :
    F.IsLong γ := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single (D := F.D) rfl hγ
  rw [form_weylAction_single] at h
  change Fin 4 at i
  fin_cases i
  · exact isLong_single_zero.weylAction w
  · exact isLong_single_one.weylAction w
  · exact absurd h (by decide)
  · exact absurd h (by decide)

omit [Group G] in
theorem card_conjSub {K : Type} [Group K] (H : Subgroup K) (g : K) :
    Nat.card (conjSub H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_rootGroup_short {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅)
    (h : (form F.hA).Q γ γ = 2) : Nat.card (F.X γ) = Nat.card (F.X a2v) := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single (D := F.D) rfl hγ
  rw [form_weylAction_single] at h
  rw [rootGroup_weylAction w ((RootSystem.ofCartan F.hA ∅).single_mem i), card_conjSub]
  change Fin 4 at i
  fin_cases i
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · show Nat.card (F.X (Pi.single 2 1)) = _
    rw [show (Pi.single 2 1 : Fin 4 → ℤ) = a2v by decide]
  · have e := actsAs_mw (F := F) a2v (a2v_mem_roots F.hA)
    rw [weylAction_mul_apply, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
      show reflF f4M 2 (reflF f4M 3 a2v) = Pi.single 3 1 by decide] at e
    change (F.X a2v).map (MulAut.conj (F.n 2 * F.n 3)).toMonoidHom = F.X (Pi.single 3 1) at e
    show Nat.card (F.X (Pi.single 3 1)) = _
    rw [← e]
    exact card_conjSub _ _

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
include hR hRD

theorem card_rootGroup_long {γ : Fin 4 → ℤ} (h : F.IsLong γ) : Nat.card (F.X γ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rootGroup_eq_zpowers hR hRD h, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq]; exact xL_mul_self hR hRD h) (xL_ne_one h.mem_roots)

omit hR hRD in
theorem prodInjective_negRoots : ProdInjectiveFor F.X negRoots :=
  F.hext.prodInjective_neg negRoots negRoots_nodup (mem_negRoots_iff F.hA) negRoots_sorted

omit hR hRD in
theorem injective_negUnipotent : Function.Injective (F.Ψ.comp (negUnipotent F.D).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h1 : (x : F.K) = 1 :=
    eq_one_of_mem_negUnipotent_of_mem_center F.hct F.hext x.2 (F.ker hx)
  exact (Subgroup.mem_bot).2 (Subtype.ext h1)

omit hR hRD in
theorem prod_card_le_card_negUnipotent [Finite G] :
    ∏ γ ∈ negRoots.toFinset, Nat.card (F.X γ) ≤ Nat.card (negUnipotent F.D) := by
  classical
  have : Finite (negUnipotent F.D) := Finite.of_injective _ injective_negUnipotent
  have hfin : ∀ γ : negRoots.toFinset, Finite (F.X γ) := fun γ =>
    finite_rootGroup (mem_roots_of_mem_negRoots F.hA (List.mem_toFinset.1 γ.2))
  let ext : (∀ γ : negRoots.toFinset, F.X γ) → (Fin 4 → ℤ) → F.K := fun t γ =>
    if h : γ ∈ negRoots.toFinset then (t ⟨γ, h⟩ : F.K) else 1
  have hext : ∀ t, ∀ γ ∈ negRoots, ext t γ ∈ F.X γ := fun t γ hγ => by
    have h := List.mem_toFinset.2 hγ
    simp only [ext, h, dite_true]
    exact (t ⟨γ, h⟩).2
  have hU : ∀ t, (negRoots.map (ext t)).prod ∈ negUnipotent F.D := fun t => by
    refine (negUnipotent F.D).list_prod_mem fun x hx => ?_
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
    exact rootGroup_le_negUnipotent (mem_roots_of_mem_negRoots F.hA hγ)
      ((mem_negRoots_iff F.hA γ).1 hγ).2.1 (hext t γ hγ)
  let Φ : (∀ γ : negRoots.toFinset, F.X γ) → negUnipotent F.D := fun t =>
    ⟨(negRoots.map (ext t)).prod, hU t⟩
  have hΦ : Function.Injective Φ := by
    intro t t' htt
    have h := prodInjective_negRoots (F := F) (ext t) (ext t') (hext t) (hext t')
      (congrArg Subtype.val htt)
    funext ⟨γ, hγ⟩
    have h1 := h γ (List.mem_toFinset.1 hγ)
    simp only [ext, hγ, dite_true] at h1
    exact Subtype.ext h1
  have h := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_pi, Finset.prod_coe_sort negRoots.toFinset (fun γ => Nat.card (F.X γ))] at h

theorem prod_card_negRoots :
    ∏ γ ∈ negRoots.toFinset, Nat.card (F.X γ) = 2 ^ 12 * Nat.card (F.X a2v) ^ 12 := by
  classical
  rw [Finset.prod_congr rfl (g := fun γ => if formF γ γ = 4 then 2 else Nat.card (F.X a2v))
    fun γ hγ => ?_]
  · have h1 : (negRoots.toFinset.filter fun γ => formF γ γ = 4).card = 12 := by decide
    have h2 : (negRoots.toFinset.filter fun γ => ¬ formF γ γ = 4).card = 12 := by decide
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, h1, h2]
  · have hγ' := mem_roots_of_mem_negRoots F.hA (List.mem_toFinset.1 hγ)
    split_ifs with h
    · exact card_rootGroup_long hR hRD (isLong_of_form hγ' (by rw [form_apply]; exact h))
    · refine card_rootGroup_short hγ' ?_
      rw [form_apply]
      exact (by decide : ∀ v ∈ negRoots, formF v v ≠ 4 → formF v v = 2) γ
        (List.mem_toFinset.1 hγ) h

variable (F) in
theorem exists_two_pow_dvd_card [Finite G] :
    ∃ a, 2 ^ 12 * Nat.card (F.X a2v) ^ 12 ≤ 2 ^ a ∧ 2 ^ a ∣ Nat.card G := by
  have : Finite (negUnipotent F.D) := Finite.of_injective _ injective_negUnipotent
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 (isPGroup_negUnipotent F.hext F.pgroup))
  refine ⟨a, ?_, ?_⟩
  · rw [← ha, ← prod_card_negRoots hR hRD]
    exact prod_card_le_card_negUnipotent
  · rw [← ha, Nat.card_congr (MonoidHom.ofInjective injective_negUnipotent).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _

variable (F) in
theorem card_a2v_le_of_card [Finite G] {N m k : ℕ} (hG : Nat.card G = 2 ^ N * m) (hm : Odd m)
    (hk : N ≤ 12 + 12 * k) : Nat.card (F.X a2v) ≤ 2 ^ k := by
  obtain ⟨a, hle, hdvd⟩ := F.exists_two_pow_dvd_card hR hRD
  rw [hG] at hdvd
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.coprime_two_left).2 hm)
  have ha : a ≤ N := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hdvd)
  have h1 : 2 ^ 12 * Nat.card (F.X a2v) ^ 12 ≤ 2 ^ 12 * (2 ^ k) ^ 12 := by
    calc 2 ^ 12 * Nat.card (F.X a2v) ^ 12 ≤ 2 ^ a := hle
      _ ≤ 2 ^ (12 + 12 * k) := Nat.pow_le_pow_right (by norm_num) (ha.trans hk)
      _ = 2 ^ 12 * (2 ^ k) ^ 12 := by rw [pow_add, ← pow_mul, mul_comm k 12]
  have h2 : Nat.card (F.X a2v) ^ 12 ≤ (2 ^ k) ^ 12 := Nat.le_of_mul_le_mul_left h1 (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2

end F4Frame

end CFSG.LargeExtraspecial.A2Mod.FrF
