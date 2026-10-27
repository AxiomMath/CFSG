module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Perm
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1Perm

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

theorem exists_central_involution {α : Type*} [Group α] {T : Subgroup α}
    (hT : IsPGroup 2 ↥T) [Finite ↥T]
    {N : Subgroup α} (hNT : N ≤ T) (hNn : ∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) : ∃ g ∈ N, orderOf g = 2 ∧ ∀ t ∈ T, t * g = g * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil := hT.isNilpotent
  let N' : Subgroup ↥T := N.subgroupOf T
  have hN'n : N'.Normal := ⟨fun x hx t => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hNn t.1 t.2 x.1 hx
    simpa using this⟩
  have hN' : N' ≠ ⊥ := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    intro h
    have : (⟨x.1, hNT x.2⟩ : ↥T) ∈ N' := Subgroup.mem_subgroupOf.mpr x.2
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (Subtype.ext (congrArg (fun y : ↥T => (y : α)) this))
  have hW : N' ⊓ Subgroup.center ↥T ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'
  have hWp : IsPGroup 2 ↥(N' ⊓ Subgroup.center ↥T) := hT.to_subgroup _
  have hcard : Nat.card ↥(N' ⊓ Subgroup.center ↥T) ≠ 1 := fun h =>
    hW (Subgroup.card_eq_one.mp h)
  have hdvd : 2 ∣ Nat.card ↥(N' ⊓ Subgroup.center ↥T) :=
    (hWp.card_eq_or_dvd).resolve_left hcard
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N' ⊓ Subgroup.center ↥T)) 2 hdvd
  have hw1 : (w : ↥T) ∈ N' := (Subgroup.mem_inf.mp w.2).1
  have hw2 : (w : ↥T) ∈ Subgroup.center ↥T := (Subgroup.mem_inf.mp w.2).2
  refine ⟨((w : ↥T) : α), Subgroup.mem_subgroupOf.mp hw1, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw2 ⟨t, ht⟩)

theorem support_invariant {T : Subgroup (Perm (Fin 11))} {g : Perm (Fin 11)}
    (hgc : ∀ t ∈ T, t * g = g * t) {t : Perm (Fin 11)} (ht : t ∈ T) {x : Fin 11}
    (hx : g x ≠ x) : g (t x) ≠ t x := by
  intro hcon
  apply hx
  have h1 : t (g x) = g (t x) := by
    have := congrArg (fun f : Perm (Fin 11) => f x) (hgc t ht)
    simpa using this
  exact t.injective (h1.trans hcon)

theorem card_support_cases {T : Subgroup (Perm (Fin 11))} (hT : SylData T)
    {g : Perm (Fin 11)} (hgT : g ∈ T) (hgc : ∀ t ∈ T, t * g = g * t) :
    g.support.card = 0 ∨ g.support.card = 2 ∨ g.support.card = 8 ∨ g.support.card = 10 := by
  classical
  have h10 : g 10 = 10 := hT.fix10 g hgT
  have hlow : ∀ x : Fin 11, x.val < 8 → (g x ≠ x ↔ g 0 ≠ 0) := by
    intro x hx
    constructor
    · intro h
      obtain ⟨t, ht, htx⟩ := hT.trans8 x 0 hx (by decide)
      have := support_invariant hgc ht h
      rwa [htx] at this
    · intro h
      obtain ⟨t, ht, htx⟩ := hT.trans8 0 x (by decide) hx
      have := support_invariant hgc ht h
      rwa [htx] at this
  have hmid : g 9 ≠ 9 ↔ g 8 ≠ 8 := by
    obtain ⟨t, ht, ht8⟩ := hT.swap89
    constructor
    · intro h
      have := support_invariant hgc (T.inv_mem ht) h
      have h9 : t⁻¹ 9 = 8 := by rw [← ht8]; simp
      rwa [h9] at this
    · intro h
      have := support_invariant hgc ht h
      rwa [ht8] at this
  have hs : g.support = Finset.univ.filter (fun x : Fin 11 =>
      (x.val < 8 ∧ g 0 ≠ 0) ∨ (8 ≤ x.val ∧ x.val < 10 ∧ g 8 ≠ 8)) := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx8 : x.val < 8
    · rw [hlow x hx8]; omega
    · by_cases hx10 : x.val < 10
      · have : x = 8 ∨ x = 9 := by
          rcases (by omega : x.val = 8 ∨ x.val = 9) with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        rcases this with rfl | rfl
        · simp
        · rw [hmid]; simp
      · have : x = 10 := Fin.ext (by omega)
        subst this
        simp [h10]
  rw [hs]
  by_cases hP : g 0 = 0 <;> by_cases hQ : g 8 = 8
  · left; simp [hP, hQ]
  · right; left
    simp only [hP, hQ, ne_eq, not_true_eq_false, and_false, false_or, not_false_eq_true,
      and_true]
    decide
  · right; right; left
    simp only [hP, hQ, ne_eq, not_true_eq_false, and_false, or_false, not_false_eq_true,
      and_true]
    decide
  · right; right; right
    simp only [hP, hQ, ne_eq, not_false_eq_true, and_true]
    decide

theorem central_involution_cycleType {T : Subgroup (Perm (Fin 11))} (hT : SylData T)
    {g : Perm (Fin 11)} (hgT : g ∈ T) (hg2 : orderOf g = 2)
    (hgc : ∀ t ∈ T, t * g = g * t) : g.cycleType = {2, 2, 2, 2} := by
  classical
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hg2]; exact Nat.prime_two)
  rw [hg2] at hn
  have hsign : Perm.sign g = 1 := hT.even g hgT
  have hsg := Equiv.Perm.sign_of_cycleType g
  rw [hn, hsign] at hsg
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsg
  have heven := (neg_one_pow_eq_one_iff_even (by decide)).mp hsg.symm
  obtain ⟨r, hr⟩ := heven
  have hc := Equiv.Perm.sum_cycleType g
  rw [hn] at hc
  simp only [Multiset.sum_replicate, smul_eq_mul] at hc
  have hcases := card_support_cases hT hgT hgc
  have h4 : n + 1 = 4 := by omega
  rw [hn, h4]
  rfl

theorem exists_type2222_of_sylData {T : Subgroup (Perm (Fin 11))} (hT : SylData T)
    {N : Subgroup (Perm (Fin 11))} (hNT : N ≤ T) (hNn : ∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) : ∃ g ∈ N, g.cycleType = {2, 2, 2, 2} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥T := IsPGroup.of_card hT.card
  obtain ⟨g, hgN, hg2, hgc⟩ := exists_central_involution hP hNT hNn hN1
  exact ⟨g, hgN, central_involution_cycleType hT (hNT hgN) hg2 hgc⟩

theorem exists_type2222_of_card {T : Subgroup (Perm (Fin 11))}
    (hTA : T ≤ alternatingGroup (Fin 11)) (hT : Nat.card ↥T = 2 ^ 7)
    {N : Subgroup (Perm (Fin 11))} (hNT : N ≤ T) (hNn : ∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) : ∃ g ∈ N, g.cycleType = {2, 2, 2, 2} := by
  obtain ⟨T₀, hT₀⟩ := exists_sylData
  have hT₀A : T₀ ≤ alternatingGroup (Fin 11) := fun t ht =>
    Equiv.Perm.mem_alternatingGroup.2 (hT₀.even t ht)
  obtain ⟨c, hc⟩ := exists_conj_of_card hT₀A hTA hT₀.card hT
  let N₀ : Subgroup (Perm (Fin 11)) := N.comap (MulAut.conj c).toMonoidHom
  have hmem : ∀ y, y ∈ N₀ ↔ c * y * c⁻¹ ∈ N := fun y => by
    simp [N₀, MulAut.conj_apply]
  have h1 : N₀ ≤ T₀ := fun y hy => by
    have h := (hc _).1 (hNT ((hmem y).1 hy))
    simpa [mul_assoc] using h
  have h2 : ∀ t ∈ T₀, ∀ x ∈ N₀, t * x * t⁻¹ ∈ N₀ := by
    intro t ht x hx
    rw [hmem]
    have htT : c * t * c⁻¹ ∈ T := (hc _).2 (by simp [mul_assoc, ht])
    have h := hNn _ htT _ ((hmem x).1 hx)
    have e : c * (t * x * t⁻¹) * c⁻¹ = c * t * c⁻¹ * (c * x * c⁻¹) * (c * t * c⁻¹)⁻¹ := by
      group
    rw [e]
    exact h
  have h3 : N₀ ≠ ⊥ := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    intro h
    have : c⁻¹ * (x : Perm (Fin 11)) * c ∈ N₀ := by
      rw [hmem]; simp [mul_assoc]
    rw [h, Subgroup.mem_bot] at this
    apply hx1
    apply Subtype.ext
    have h' : (x : Perm (Fin 11)) = c * (c⁻¹ * (x : Perm (Fin 11)) * c) * c⁻¹ := by group
    rw [h', this]
    simp
  obtain ⟨g₀, hg₀, hcyc⟩ := exists_type2222_of_sylData hT₀ h1 h2 h3
  refine ⟨c * g₀ * c⁻¹, (hmem g₀).1 hg₀, ?_⟩
  rw [Equiv.Perm.cycleType_conj]
  exact hcyc

private def e10 : Fin 10 ≃ {x : Fin 11 // x.val < 10} where
  toFun a := ⟨⟨a.val, by omega⟩, a.isLt⟩
  invFun y := ⟨y.1.val, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def ι : Perm (Fin 10) →* Perm (Fin 11) := Equiv.Perm.extendDomainHom e10

private theorem ι_injective : Function.Injective ι := Equiv.Perm.extendDomainHom_injective e10

private theorem sign_ι (σ : Perm (Fin 10)) : Perm.sign (ι σ) = Perm.sign σ :=
  Equiv.Perm.sign_extendDomain σ e10

private theorem cycleType_ι (σ : Perm (Fin 10)) : (ι σ).cycleType = σ.cycleType :=
  Equiv.Perm.cycleType_extendDomain e10

theorem exists_type2222_of_card10 {T : Subgroup (Perm (Fin 10))}
    (hTA : T ≤ alternatingGroup (Fin 10)) (hT : Nat.card ↥T = 2 ^ 7)
    {N : Subgroup (Perm (Fin 10))} (hNT : N ≤ T) (hNn : ∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) : ∃ g ∈ N, g.cycleType = {2, 2, 2, 2} := by
  have hTA' : T.map ι ≤ alternatingGroup (Fin 11) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, sign_ι]
    exact Equiv.Perm.mem_alternatingGroup.1 (hTA ht)
  have hT' : Nat.card ↥(T.map ι) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective ι_injective, hT]
  have hNT' : N.map ι ≤ T.map ι := Subgroup.map_mono hNT
  have hNn' : ∀ t ∈ T.map ι, ∀ x ∈ N.map ι, t * x * t⁻¹ ∈ N.map ι := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨t * x * t⁻¹, hNn t ht x hx, by simp⟩
  have hN1' : N.map ι ≠ ⊥ := by
    intro h
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : ι x ∈ N.map ι := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ι] at this
    exact Subgroup.mem_bot.mpr (ι_injective this)
  obtain ⟨g', ⟨g, hg, rfl⟩, hcyc⟩ := exists_type2222_of_card hTA' hT' hNT' hNn' hN1'
  exact ⟨g, hg, by rw [← cycleType_ι]; exact hcyc⟩

private def a₁ : Perm (Fin 11) := swap 0 1 * swap 2 3
private def a₂ : Perm (Fin 11) := swap 0 2 * swap 1 3
private def b₁ : Perm (Fin 11) := swap 4 5 * swap 6 7
private def b₂ : Perm (Fin 11) := swap 4 6 * swap 5 7

private def E₀ : Subgroup (Perm (Fin 11)) := Subgroup.closure {a₁, a₂, b₁, b₂}

private theorem gens_commute : ({a₁, a₂, b₁, b₂} : Set (Perm (Fin 11))).Pairwise Commute := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | (show _ * _ = _ * _; decide)

private theorem gens_sq : ∀ x ∈ ({a₁, a₂, b₁, b₂} : Set (Perm (Fin 11))), x * x = 1 := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

private theorem E₀_comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
  intro x hx y hy
  have : IsMulCommutative ↥E₀ := Subgroup.isMulCommutative_closure gens_commute
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E₀) ⟨y, hy⟩)

private theorem E₀_sq : ∀ x ∈ E₀, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact gens_sq x hx
  | one => simp
  | mul x y hx hy hx1 hy1 =>
    have hxy : y * x = x * y := (E₀_comm x hx y hy).symm
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx1, hy1, mul_one]
  | inv x hx hx1 =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hx1, inv_one]

private theorem E₀_le_alt : E₀ ≤ alternatingGroup (Fin 11) := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    (rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide)

private theorem E₀_card : 16 ≤ Nat.card ↥E₀ := by
  let f : Fin 2 × Fin 2 × Fin 2 × Fin 2 → Perm (Fin 11) := fun x =>
    a₁ ^ x.1.val * a₂ ^ x.2.1.val * b₁ ^ x.2.2.1.val * b₂ ^ x.2.2.2.val
  have hmem : ∀ x, f x ∈ E₀ := by
    intro x
    have h1 : a₁ ∈ E₀ := Subgroup.subset_closure (by simp)
    have h2 : a₂ ∈ E₀ := Subgroup.subset_closure (by simp)
    have h3 : b₁ ∈ E₀ := Subgroup.subset_closure (by simp)
    have h4 : b₂ ∈ E₀ := Subgroup.subset_closure (by simp)
    exact E₀.mul_mem (E₀.mul_mem (E₀.mul_mem (E₀.pow_mem h1 _) (E₀.pow_mem h2 _))
      (E₀.pow_mem h3 _)) (E₀.pow_mem h4 _)
  have hinj : Function.Injective f := by
    intro x y h
    revert h
    revert x y
    decide
  have := Nat.card_le_card_of_injective (fun x => (⟨f x, hmem x⟩ : ↥E₀))
    (fun x y h => hinj (congrArg Subtype.val h))
  simpa [Nat.card_eq_fintype_card] using this

private theorem exists_sylow_ge_E₀ : ∃ T'' : Subgroup (Perm (Fin 11)),
    T'' ≤ alternatingGroup (Fin 11) ∧ Nat.card ↥T'' = 2 ^ 7 ∧ E₀ ≤ T'' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := alternatingGroup (Fin 11)
  let Q : Subgroup ↥A := E₀.subgroupOf A
  have hQ : IsPGroup 2 ↥Q := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := E₀_sq g.1.1 (Subgroup.mem_subgroupOf.mp g.2)
    simpa [pow_two] using this
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  refine ⟨(P : Subgroup ↥A).map A.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity,
      factorization_card_alternatingGroup_eleven]
  · intro x hx
    exact ⟨⟨x, E₀_le_alt hx⟩, hP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem exists_elemAbelian_of_card {T : Subgroup (Perm (Fin 11))}
    (hTA : T ≤ alternatingGroup (Fin 11)) (hT : Nat.card ↥T = 2 ^ 7) :
    ∃ E : Subgroup (Perm (Fin 11)), E ≤ T ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x * x = 1) ∧ 16 ≤ Nat.card ↥E := by
  obtain ⟨T'', hT''A, hT''c, hE⟩ := exists_sylow_ge_E₀
  obtain ⟨c, hc⟩ := exists_conj_of_card hT''A hTA hT''c hT
  refine ⟨E₀.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [hc]
    have : c⁻¹ * ((MulAut.conj c).toMonoidHom y) * c = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hE hy
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, E₀_comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, E₀_sq x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact E₀_card

theorem exists_elemAbelian_of_card10 {T : Subgroup (Perm (Fin 10))}
    (hTA : T ≤ alternatingGroup (Fin 10)) (hT : Nat.card ↥T = 2 ^ 7) :
    ∃ E : Subgroup (Perm (Fin 10)), E ≤ T ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x * x = 1) ∧ 16 ≤ Nat.card ↥E := by
  have hTA' : T.map ι ≤ alternatingGroup (Fin 11) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, sign_ι]
    exact Equiv.Perm.mem_alternatingGroup.1 (hTA ht)
  have hT' : Nat.card ↥(T.map ι) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective ι_injective, hT]
  obtain ⟨E', hE'T, hc, hs, hcard⟩ := exists_elemAbelian_of_card hTA' hT'
  have hrange : E' ≤ ι.range := fun x hx => by
    obtain ⟨t, -, rfl⟩ := hE'T hx
    exact ⟨t, rfl⟩
  refine ⟨E'.comap ι, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, hte⟩ := hE'T hx
    rw [← ι_injective hte]
    exact ht
  · intro x hx y hy
    apply ι_injective
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  · intro x hx
    apply ι_injective
    rw [map_mul, map_one]
    exact hs _ hx
  · have h : Nat.card ↥((E'.comap ι).map ι) = Nat.card ↥(E'.comap ι) :=
      Subgroup.card_map_of_injective ι_injective
    rw [Subgroup.map_comap_eq_self hrange] at h
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1Perm
