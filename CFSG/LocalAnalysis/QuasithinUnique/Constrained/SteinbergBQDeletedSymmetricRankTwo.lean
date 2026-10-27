module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQDeletedSelfNormalizing
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.QuasithinUnique

open Module

namespace SteinbergBQ.DeletedModule

variable {m : ℕ}

theorem perm_pairVec {ρ : Equiv.Perm (Fin m) → (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hρ : ∀ σ x i, ρ σ x i = x (σ⁻¹ i)) (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    ρ σ (pairVec i j) = pairVec (σ i) (σ j) := by
  funext p
  rw [hρ]
  simp only [pairVec_apply, Equiv.Perm.inv_eq_iff_eq]

theorem orbit_three {b : Equiv.Perm (Fin m)} (hb : orderOf b = 3) {x : Fin m} (hx : b x ≠ x) :
    b (b (b x)) = x ∧ x ≠ b x ∧ x ≠ b (b x) ∧ b x ≠ b (b x) := by
  have h3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb3 : b (b (b x)) = x := by
    have h1 := congrArg (fun σ : Equiv.Perm (Fin m) => σ x) h3
    simpa [pow_succ, Equiv.Perm.mul_apply] using h1
  refine ⟨hb3, fun h => hx h.symm, fun h => hx ?_, fun h => hx (b.injective h).symm⟩
  have h1 : b (b (b x)) = b x := by rw [← h]
  rw [hb3] at h1
  exact h1.symm

theorem sub_pairVec_orbit {ρ : Equiv.Perm (Fin m) → (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hρ : ∀ σ x i, ρ σ x i = x (σ⁻¹ i)) {b : Equiv.Perm (Fin m)} (hb : orderOf b = 3) {x : Fin m}
    (hx : b x ≠ x) :
    (ρ b - 1) (pairVec x (b x)) = pairVec x (b (b x)) ∧
      (ρ b - 1) (pairVec (b x) (b (b x))) = pairVec x (b x) := by
  obtain ⟨hb3, h12, h13, h23⟩ := orbit_three hb hx
  constructor
  · funext p
    rw [LinearMap.sub_apply, Module.End.one_apply, perm_pairVec hρ, Pi.sub_apply]
    simp only [pairVec_apply]
    by_cases h1 : p = x
    · subst h1
      simp only [h12, h13, ite_true, ite_false]
      simp [CharTwo.sub_eq_add]
    by_cases h2 : p = b x
    · subst h2
      simp only [h1, h23, ite_true, ite_false]
      simp
    by_cases h3 : p = b (b x)
    · subst h3
      simp only [h1, h2, ite_true, ite_false]
      simp [CharTwo.sub_eq_add]
    · simp only [h1, h2, h3, ite_false]
      simp
  · funext p
    rw [LinearMap.sub_apply, Module.End.one_apply, perm_pairVec hρ, Pi.sub_apply, hb3]
    simp only [pairVec_apply]
    by_cases h1 : p = x
    · subst h1
      simp only [h12, h13, ite_true, ite_false]
      simp [CharTwo.sub_eq_add]
    by_cases h2 : p = b x
    · subst h2
      simp only [h1, h23, ite_true, ite_false]
      simp [CharTwo.sub_eq_add]
    by_cases h3 : p = b (b x)
    · subst h3
      simp only [h1, h2, ite_true, ite_false]
      simp
    · simp only [h1, h2, h3, ite_false]
      simp

theorem linearIndependent_mkQ {x₁ x₂ x₃ y₁ y₂ y₃ : Fin m}
    (h : [x₁, x₂, x₃, y₁, y₂, y₃].Nodup) {Z : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hZ : Z = Submodule.span (ZMod 2) {fun _ => 1}) :
    LinearIndependent (ZMod 2) (Z.mkQ ∘ ![pairVec x₁ x₃, pairVec x₁ x₂, pairVec y₁ y₃,
      pairVec y₁ y₂]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ :=
    h
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_four] at hc
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Submodule.mkQ_apply] at hc
  have hc' : c 0 • pairVec x₁ x₃ + c 1 • pairVec x₁ x₂ + c 2 • pairVec y₁ y₃ +
      c 3 • pairVec y₁ y₂ ∈ Z := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    exact hc
  rw [hZ, Submodule.mem_span_singleton] at hc'
  obtain ⟨l, hl⟩ := hc'
  have hev : ∀ p, l = c 0 * pairVec x₁ x₃ p + c 1 * pairVec x₁ x₂ p + c 2 * pairVec y₁ y₃ p +
      c 3 * pairVec y₁ y₂ p := fun p => by
    have h1 := congrFun hl p
    simpa using h1
  have e1 := hev x₃
  have e2 := hev x₂
  have e3 := hev x₁
  have e4 := hev y₃
  have e5 := hev y₂
  have e6 := hev y₁
  have hne := And.intro h12 (And.intro h13 (And.intro h14 (And.intro h15 (And.intro h16
    (And.intro h23 (And.intro h24 (And.intro h25 (And.intro h26 (And.intro h34 (And.intro h35
    (And.intro h36 (And.intro h45 (And.intro h46 h56)))))))))))))
  simp only [pairVec_apply, hne, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16,
    Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h34, Ne.symm h35, Ne.symm h36,
    Ne.symm h45, Ne.symm h46, Ne.symm h56, ite_true, ite_false, mul_one, mul_zero, add_zero,
    zero_add] at e1 e2 e3 e4 e5 e6
  have hl0 : l = 0 := by
    have h := e3
    rw [← e1, ← e2, CharTwo.add_self_eq_zero] at h
    exact h
  intro i
  fin_cases i
  · exact e1.symm.trans hl0
  · exact e2.symm.trans hl0
  · exact e4.symm.trans hl0
  · exact e5.symm.trans hl0

theorem rank_ge_four {ρ : Equiv.Perm (Fin m) → (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hρ : ∀ σ x i, ρ σ x i = x (σ⁻¹ i)) {Δ : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) {Z : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hZ : Z = Submodule.span (ZMod 2) {fun _ => 1}) {b : Equiv.Perm (Fin m)}
    (hb : orderOf b = 3) {x y : Fin m} (hx : b x ≠ x) (hy : b y ≠ y)
    (hxy : y ≠ x ∧ y ≠ b x ∧ y ≠ b (b x)) :
    4 ≤ finrank (ZMod 2) (Δ.map (ρ b - 1)) ∧
      4 ≤ finrank (ZMod 2) ((Δ.map (ρ b - 1)).map Z.mkQ) := by
  obtain ⟨hb3x, hx12, hx13, hx23⟩ := orbit_three hb hx
  obtain ⟨hb3y, hy12, hy13, hy23⟩ := orbit_three hb hy
  obtain ⟨hyx1, hyx2, hyx3⟩ := hxy
  have h4 : b y ≠ x := fun h => hyx3 (by rw [← hb3y, h])
  have h5 : b y ≠ b x := fun h => hyx1 (b.injective h)
  have h6 : b y ≠ b (b x) := fun h => hyx2 (b.injective h)
  have h7 : b (b y) ≠ x := fun h => hyx2 (by rw [← hb3y, h])
  have h8 : b (b y) ≠ b x := fun h => h4 (b.injective h)
  have h9 : b (b y) ≠ b (b x) := fun h => hyx1 (b.injective (b.injective h))
  have hd : [x, b x, b (b x), y, b y, b (b y)].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hx12, hx13, Ne.symm hyx1, Ne.symm h4, Ne.symm h7⟩, ⟨hx23, Ne.symm hyx2, Ne.symm h5,
      Ne.symm h8⟩, ⟨Ne.symm hyx3, Ne.symm h6, Ne.symm h9⟩, ⟨hy12, hy13⟩, hy23, not_false⟩
  have hli := linearIndependent_mkQ hd hZ
  set v : Fin 4 → (Fin m → ZMod 2) := ![pairVec x (b (b x)), pairVec x (b x),
    pairVec y (b (b y)), pairVec y (b y)] with hv
  have hmem : ∀ i, v i ∈ Δ.map (ρ b - 1) := by
    intro i
    fin_cases i
    · exact ⟨_, pairVec_mem hΔ _ _, (sub_pairVec_orbit hρ hb hx).1⟩
    · exact ⟨_, pairVec_mem hΔ _ _, (sub_pairVec_orbit hρ hb hx).2⟩
    · exact ⟨_, pairVec_mem hΔ _ _, (sub_pairVec_orbit hρ hb hy).1⟩
    · exact ⟨_, pairVec_mem hΔ _ _, (sub_pairVec_orbit hρ hb hy).2⟩
  constructor
  · have hli' : LinearIndependent (ZMod 2) v := LinearIndependent.of_comp Z.mkQ hli
    have h1 : Submodule.span (ZMod 2) (Set.range v) ≤ Δ.map (ρ b - 1) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hmem)
    have h2 := finrank_span_eq_card hli'
    rw [Fintype.card_fin] at h2
    exact h2.symm.le.trans (Submodule.finrank_mono h1)
  · have h1 : Submodule.span (ZMod 2) (Set.range (Z.mkQ ∘ v)) ≤ (Δ.map (ρ b - 1)).map Z.mkQ :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun i => Submodule.mem_map_of_mem (hmem i))
    have h2 := finrank_span_eq_card hli
    rw [Fintype.card_fin] at h2
    exact h2.symm.le.trans (Submodule.finrank_mono h1)

theorem isThreeCycle_of_rank {ρ : Equiv.Perm (Fin m) → (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hρ : ∀ σ x i, ρ σ x i = x (σ⁻¹ i)) {Δ : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) {Z : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hZ : Z = Submodule.span (ZMod 2) {fun _ => 1}) {b : Equiv.Perm (Fin m)}
    (hb : orderOf b = 3)
    (hrank : finrank (ZMod 2) (Δ.map (ρ b - 1)) < 4 ∨
      finrank (ZMod 2) ((Δ.map (ρ b - 1)).map Z.mkQ) < 4) :
    b.IsThreeCycle := by
  classical
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    exact absurd hb (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, b x ≠ x := by
    by_contra h
    push Not at h
    exact hb1 (Equiv.ext h)
  obtain ⟨hb3, h12, h13, h23⟩ := orbit_three hb hx
  have hsupp : b.support = {x, b x, b (b x)} := by
    ext y
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hy
      by_contra hny
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hny
      obtain ⟨h1, h2⟩ := rank_ge_four hρ hΔ hZ hb hx hy ⟨hny.1, hny.2.1, hny.2.2⟩
      rcases hrank with h | h <;> omega
    · intro hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hx
      · exact fun h => hx (b.injective h)
      · rw [hb3]
        exact h13
  rw [← card_support_eq_three_iff, hsupp, Finset.card_insert_of_notMem, Finset.card_pair h23]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h12, h13⟩

theorem orderOf_conj' {G : Type*} [Group G] (x b : G) : orderOf (x * b * x⁻¹) = orderOf b := by
  have h := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective b
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem card_normalizer_zpowers {b : Equiv.Perm (Fin m)} (hb : b.IsThreeCycle) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m)))) =
      6 * (m - 3).factorial := by
  classical
  set N := Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m))) with hNdef
  set C := Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin m))) with hCdef
  have hb3 : orderOf b = 3 := hb.orderOf
  have hbpow : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hbinv : b ≠ b⁻¹ := by
    intro h
    have h1 : b ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel b
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hb3] at h2
    exact absurd h2 (by norm_num)
  have hconj : ∀ x ∈ N, x * b * x⁻¹ = b ∨ x * b * x⁻¹ = b⁻¹ := by
    intro x hx
    have h1 : x * b * x⁻¹ ∈ Subgroup.zpowers b :=
      (Subgroup.mem_normalizer_iff.1 hx b).1 (Subgroup.mem_zpowers b)
    have h2 : orderOf (x * b * x⁻¹) = 3 := by rw [orderOf_conj', hb3]
    rw [mem_zpowers_iff_mem_range_orderOf, hb3] at h1
    simp only [Finset.mem_image, Finset.mem_range] at h1
    obtain ⟨k, hk, hkx⟩ := h1
    interval_cases k
    · rw [pow_zero] at hkx
      rw [← hkx, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · left
      rw [← hkx, pow_one]
    · right
      rw [← hkx, eq_inv_iff_mul_eq_one, ← pow_succ, hbpow]
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin m), τ * b * τ⁻¹ = b⁻¹ :=
    isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (Equiv.Perm.cycleType_inv b).symm)
  have hmemN : ∀ x : Equiv.Perm (Fin m), (x * b * x⁻¹ = b ∨ x * b * x⁻¹ = b⁻¹) → x ∈ N := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers, MonoidHom.coe_ofClass,
      MulAut.conj_apply]
    rcases hx with hx | hx
    · rw [hx]
    · rw [hx, Subgroup.zpowers_inv]
  have hτN : τ ∈ N := hmemN τ (Or.inr hτ)
  have hCN : C ≤ N := fun x hx => hmemN x (Or.inl (by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [hx, mul_inv_cancel_right]))
  have hmemC : ∀ x : Equiv.Perm (Fin m), x ∈ C ↔ x * b * x⁻¹ = b := fun x => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc x * b = x * b * x⁻¹ * x := by group
        _ = b * x := by rw [h]
  have hindex : (C.subgroupOf N).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨τ, hτN⟩, fun y => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmemC, hmemC]
    have h1 : (y : Equiv.Perm (Fin m)) * τ * b * ((y : Equiv.Perm (Fin m)) * τ)⁻¹ =
        ((y : Equiv.Perm (Fin m)) * b * (y : Equiv.Perm (Fin m))⁻¹)⁻¹ := by
      calc (y : Equiv.Perm (Fin m)) * τ * b * ((y : Equiv.Perm (Fin m)) * τ)⁻¹ =
          (y : Equiv.Perm (Fin m)) * (τ * b * τ⁻¹) * (y : Equiv.Perm (Fin m))⁻¹ := by group
        _ = _ := by rw [hτ]; group
    rw [h1, inv_eq_iff_eq_inv]
    rcases hconj y y.2 with h2 | h2
    · rw [h2]
      exact Or.inr ⟨rfl, hbinv⟩
    · rw [h2]
      exact Or.inl ⟨rfl, fun h3 => hbinv h3.symm⟩
  have hC : Nat.card C = (m - 3).factorial * 3 := by
    rw [hCdef, Equiv.Perm.nat_card_centralizer, hb.cycleType, Fintype.card_fin]
    simp
  have h1 := Subgroup.card_mul_index (C.subgroupOf N)
  rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, hC] at h1
  rw [← h1]
  ring

theorem exists_sylow_le_iff {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) : (∃ T : Sylow p G, (T : Subgroup G) ≤ K) ↔ ¬ p ∣ K.index := by
  constructor
  · rintro ⟨T, hT⟩ hpK
    have h1 := Subgroup.relIndex_mul_index hT
    exact T.not_dvd_index (h1 ▸ dvd_mul_of_dvd_right hpK _)
  · intro hpK
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p K))
    have hP' : IsPGroup p ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
    have hidx : ¬ p ∣ ((P : Subgroup K).map K.subtype).index := by
      rw [Subgroup.index_map_subtype]
      intro h
      rcases (Nat.Prime.dvd_mul Fact.out).1 h with h1 | h1
      · exact P.not_dvd_index h1
      · exact hpK h1
    exact ⟨hP'.toSylow hidx, Subgroup.map_subtype_le _⟩

theorem odd_index_iff {m idx : ℕ} (hm : 3 ≤ m) (h : 6 * idx = m * (m - 1) * (m - 2)) :
    ¬ 2 ∣ idx ↔ m % 4 = 3 := by
  have hmod : m * (m - 1) * (m - 2) % 4 = m % 4 * ((m - 1) % 4) % 4 * ((m - 2) % 4) % 4 := by
    rw [Nat.mul_mod, Nat.mul_mod m]
  generalize hP : m * (m - 1) * (m - 2) = P at h hmod
  have hr : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr
  · have h1 : (m - 1) % 4 = 3 := by omega
    have h2 : (m - 2) % 4 = 2 := by omega
    rw [hr, h1, h2] at hmod
    norm_num at hmod
    constructor <;> intro h3 <;> omega
  · have h1 : (m - 1) % 4 = 0 := by omega
    have h2 : (m - 2) % 4 = 3 := by omega
    rw [hr, h1, h2] at hmod
    norm_num at hmod
    constructor <;> intro h3 <;> omega
  · have h1 : (m - 1) % 4 = 1 := by omega
    have h2 : (m - 2) % 4 = 0 := by omega
    rw [hr, h1, h2] at hmod
    norm_num at hmod
    constructor <;> intro h3 <;> omega
  · have h1 : (m - 1) % 4 = 2 := by omega
    have h2 : (m - 2) % 4 = 1 := by omega
    rw [hr, h1, h2] at hmod
    norm_num at hmod
    constructor <;> intro h3 <;> omega

theorem exists_elementaryAbelian_27 (hm : 9 ≤ m) :
    ∃ E : Subgroup (Equiv.Perm (Fin m)), IsElementaryAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  let t : Multiplicative (ZMod 3) →* Equiv.Perm (ZMod 3) :=
    { toFun := fun a => Equiv.addLeft (Multiplicative.toAdd a)
      map_one' := by
        ext x
        simp
      map_mul' := fun a b => by
        ext x
        simp }
  have ht : Function.Injective t := fun a b h => by
    have h1 := congrArg (fun σ : Equiv.Perm (ZMod 3) => σ 0) h
    simpa [t] using h1
  let f₁ : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →*
      Equiv.Perm (ZMod 3 ⊕ ZMod 3 ⊕ ZMod 3) :=
    (Equiv.Perm.sumCongrHom _ _).comp
      (t.prodMap ((Equiv.Perm.sumCongrHom _ _).comp (t.prodMap t)))
  have hf₁ : Function.Injective f₁ :=
    Equiv.Perm.sumCongrHom_injective.comp
      (ht.prodMap (Equiv.Perm.sumCongrHom_injective.comp (ht.prodMap ht)))
  have hX : Fintype.card (ZMod 3 ⊕ ZMod 3 ⊕ ZMod 3) = 9 := by simp
  let e : ZMod 3 ⊕ ZMod 3 ⊕ ZMod 3 ≃ {i : Fin m // i ∈ Set.range (Fin.castLE hm)} :=
    (Fintype.equivFinOfCardEq hX).trans
      (Equiv.ofInjective (Fin.castLE hm) (Fin.castLE_injective hm))
  let f := (Equiv.Perm.extendDomainHom e).comp f₁
  have hf : Function.Injective f := (Equiv.Perm.extendDomainHom_injective e).comp hf₁
  refine ⟨f.range, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← map_mul, mul_comm a b]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
      have ha : a ^ 3 = 1 := by
        obtain ⟨a₁, a₂, a₃⟩ := a
        ext
        · change Multiplicative.toAdd (a₁ ^ 3) = 0
          rw [toAdd_pow]
          decide +revert
        · change Multiplicative.toAdd (a₂ ^ 3) = 0
          rw [toAdd_pow]
          decide +revert
        · change Multiplicative.toAdd (a₃ ^ 3) = 0
          rw [toAdd_pow]
          decide +revert
      rw [ha, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    simp

end SteinbergBQ.DeletedModule

open SteinbergBQ.DeletedModule

theorem deleted_symmetric_rank_two_three_normalizer_degrees {m : ℕ} (hm : 3 ≤ m)
    (ρ : Equiv.Perm (Fin m) → (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hρ : ∀ σ x i, ρ σ x i = x (σ⁻¹ i)) {Δ : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) {Z : Submodule (ZMod 2) (Fin m → ZMod 2)}
    (hZ : Z = Submodule.span (ZMod 2) {fun _ => 1}) {b : Equiv.Perm (Fin m)}
    (hb : orderOf b = 3) (hWodd : Odd m → finrank (ZMod 2) (Δ.map (ρ b - 1)) = 2)
    (hWeven : Even m → finrank (ZMod 2) ((Δ.map (ρ b - 1)).map Z.mkQ) = 2) :
    b.IsThreeCycle ∧
      Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m)))) =
        6 * (m - 3).factorial ∧
      ((∃ T : Sylow 2 (Equiv.Perm (Fin m)), (T : Subgroup (Equiv.Perm (Fin m))) ≤
          Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m)))) ↔ m % 4 = 3) ∧
      ∀ T : Sylow 2 (Equiv.Perm (Fin m)), (T : Subgroup (Equiv.Perm (Fin m))) ≤
          Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m))) →
        (∀ E : Subgroup (Equiv.Perm (Fin m)), IsElementaryAbelian 3 E → Nat.card E ≤ 9) →
          m = 3 ∨ m = 7 := by
  classical
  have h3 : b.IsThreeCycle := isThreeCycle_of_rank hρ hΔ hZ hb (by
    rcases Nat.even_or_odd m with h | h
    · right
      rw [hWeven h]
      norm_num
    · left
      rw [hWodd h]
      norm_num)
  have hN := card_normalizer_zpowers h3
  have hidx : 6 * (Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m)))).index =
      m * (m - 1) * (m - 2) := by
    have h1 := Subgroup.card_mul_index
      (Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m))))
    rw [hN, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h1
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    rw [show k + 3 - 3 = k by omega, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ] at h1
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    have hk := Nat.factorial_pos k
    apply Nat.eq_of_mul_eq_mul_right hk
    linarith [h1]
  have hsyl := exists_sylow_le_iff (p := 2)
    (Subgroup.normalizer (Subgroup.zpowers b : Set (Equiv.Perm (Fin m))))
  have hpar := odd_index_iff hm hidx
  refine ⟨h3, hN, hsyl.trans hpar, fun T hT h9 => ?_⟩
  have hm4 : m % 4 = 3 := (hsyl.trans hpar).1 ⟨T, hT⟩
  have hm8 : m ≤ 8 := by
    by_contra h
    push Not at h
    obtain ⟨E, hE, hEcard⟩ := exists_elementaryAbelian_27 (show 9 ≤ m by omega)
    have h1 := h9 E hE
    omega
  omega

end CFSG.QuasithinUnique
