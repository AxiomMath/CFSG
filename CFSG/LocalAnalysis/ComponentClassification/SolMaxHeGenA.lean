module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

theorem conj_smul_eq_map {G : Type*} [Group G] (σ : G) (R : Subgroup G) :
    MulAut.conj σ • R = R.map (MulAut.conj σ).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem apply_eq_or_of_pow {g w : Perm (Fin 7)} (hg3 : ∀ y, (g ^ 3) y = y)
    (hww : ∀ y, w (w y) = y) (hcw : ∀ k : ℕ, ∀ y, w ((g ^ k) y) = (g ^ k) (w y)) {x : Fin 7}
    {j : ℕ} (hj : j < 3) (hi : (g ^ j) x = w x) : w x = x ∨ g x = x := by
  obtain h | h | h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · subst h
    left
    simpa using hi.symm
  · subst h
    right
    rw [pow_one] at hi
    have e := hcw 1 x
    rw [pow_one, hi] at e
    have h1 : g (g x) = x := by rw [hi, ← e, hww]
    calc g x = g (g (g x)) := by rw [h1]
      _ = (g ^ 3) x := by rw [pow_three]; rfl
      _ = x := hg3 x
  · subst h
    right
    have e := hcw 2 x
    rw [hi] at e
    have h1 : (g ^ 2) ((g ^ 2) x) = x := by rw [hi, ← e, hww]
    calc g x = (g ^ 3) (g x) := (hg3 _).symm
      _ = (g ^ 2) ((g ^ 2) x) := by simp only [pow_three, pow_two, Perm.mul_apply]
      _ = x := h1

theorem exists_range_ofSubtype_of_commute {V : Subgroup (alternatingGroup (Fin 7))}
    (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) {γ : alternatingGroup (Fin 7)}
    (hγ : orderOf γ = 3) (hγV : ∀ v ∈ V, γ * v = v * γ) :
    ∃ S : Finset (Fin 7), S.card = 4 ∧ V ≤ (alternatingGroup.ofSubtype S).range := by
  classical
  set g : Perm (Fin 7) := (γ : Perm (Fin 7)) with hg
  have hg3 : orderOf g = 3 := by rw [hg, Subgroup.orderOf_coe, hγ]
  have hcomm : ∀ v ∈ V, Commute g (v : Perm (Fin 7)) := fun v hv => by
    change g * (v : Perm (Fin 7)) = (v : Perm (Fin 7)) * g
    rw [hg, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hγV v hv]
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := g) (by rw [hg3]; exact Nat.prime_three)
  rw [hg3] at hn
  have hsupp : g.support.card = 3 * (n + 1) := by
    rw [← sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : g.support.card ≤ 7 := by
    simpa using Finset.card_le_univ g.support
  have hn0 : n = 0 := by
    by_contra hne
    have hn1 : n = 1 := by omega
    subst hn1
    have hcard : Nat.card (centralizer ({g} : Set (Perm (Fin 7)))) = 18 := by
      rw [nat_card_centralizer, hn]
      decide
    have hmap : V.map (alternatingGroup (Fin 7)).subtype ≤
        centralizer ({g} : Set (Perm (Fin 7))) := by
      rintro _ ⟨v, hv, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact (hcomm v hv).eq.symm
    have hdvd := Subgroup.card_dvd_of_le hmap
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective, hV,
      hcard] at hdvd
    norm_num at hdvd
  subst hn0
  have hcyc : g.IsCycle := by
    rw [← card_cycleType_eq_one, hn]
    simp
  have hg3' : ∀ y, (g ^ 3) y = y := fun y => by
    rw [← hg3, pow_orderOf_eq_one, Perm.one_apply]
  refine ⟨g.supportᶜ, by simp [Finset.card_compl, hsupp], fun v hv => ?_⟩
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  intro x hx
  rw [Finset.mem_compl]
  intro hxg
  rw [Equiv.Perm.mem_support] at hx hxg
  apply hx
  have hww : ∀ y, (v : Perm (Fin 7)) ((v : Perm (Fin 7)) y) = y := fun y => by
    have h2 : (v : Perm (Fin 7)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hV2 v hv, Subgroup.coe_one]
    rw [← Perm.mul_apply, ← pow_two, h2, Perm.one_apply]
  have hcw : ∀ k : ℕ, ∀ y, (v : Perm (Fin 7)) ((g ^ k) y) = (g ^ k) ((v : Perm (Fin 7)) y) :=
    fun k y => by
      rw [← Perm.mul_apply, ← Perm.mul_apply, ((hcomm v hv).pow_left k).eq]
  have hwx : g ((v : Perm (Fin 7)) x) ≠ (v : Perm (Fin 7)) x := by
    intro h
    apply hxg
    apply (v : Perm (Fin 7)).injective
    have e := hcw 1 x
    rw [pow_one] at e
    rw [e, h]
  obtain ⟨i, hi⟩ := hcyc.exists_pow_eq hxg hwx
  rw [← pow_mod_orderOf, hg3] at hi
  exact (apply_eq_or_of_pow hg3' hww hcw (Nat.mod_lt _ (by norm_num)) hi).resolve_right hxg

theorem exists_smul_eq_of_card_four {S₀ S : Finset (Fin 7)} (h₀ : S₀.card = 4) (h : S.card = 4) :
    ∃ σ : alternatingGroup (Fin 7), σ • S₀ = S := by
  classical
  have h5 := alternatingGroup.isMultiplyPretransitive (Fin 7)
  have : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7) 4 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 7) - 2) (by simp) (by simp)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7))
    (S₀.orderEmbOfFin h₀).toEmbedding (S.orderEmbOfFin h).toEmbedding
  have hσi : ∀ i, σ • (S₀.orderEmbOfFin h₀) i = (S.orderEmbOfFin h) i := fun i => by
    have := congrArg (fun e : Fin 4 ↪ Fin 7 => e i) hσ
    simpa only [Function.Embedding.smul_apply, RelEmbedding.coe_toEmbedding] using this
  refine ⟨σ, Finset.coe_injective ?_⟩
  rw [Finset.coe_smul_finset, ← Finset.range_orderEmbOfFin S₀ h₀,
    ← Finset.range_orderEmbOfFin S h]
  ext y
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hσi i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(S₀.orderEmbOfFin h₀) i, ⟨i, rfl⟩, hσi i⟩

theorem eq_of_le_range_ofSubtype {S : Finset (Fin 7)} (hS : S.card = 4)
    {V W : Subgroup (alternatingGroup (Fin 7))} (hV : Nat.card V = 4) (hW : Nat.card W = 4)
    (hVS : V ≤ (alternatingGroup.ofSubtype S).range)
    (hWS : W ≤ (alternatingGroup.ofSubtype S).range) : V = W := by
  classical
  have hι : Function.Injective (alternatingGroup.ofSubtype S) :=
    alternatingGroup.ofSubtype_injective
  have hS4 : Nat.card S = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS]
  have hA : Nat.card (alternatingGroup S) = 12 := alternatingGroup.card_of_card_eq_four hS4
  have key : ∀ U : Subgroup (alternatingGroup (Fin 7)), Nat.card U = 4 →
      U ≤ (alternatingGroup.ofSubtype S).range → ∃ P : Sylow 2 (alternatingGroup S),
        (P : Subgroup (alternatingGroup S)).map (alternatingGroup.ofSubtype S) = U := by
    intro U hU hUS
    have hc : Nat.card (U.comap (alternatingGroup.ofSubtype S)) = 4 := by
      rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hUS, hU]
    have hp : IsPGroup 2 (U.comap (alternatingGroup.ofSubtype S)) :=
      IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)
    have hidx : (U.comap (alternatingGroup.ofSubtype S)).index = 3 := by
      have := (U.comap (alternatingGroup.ofSubtype S)).card_mul_index
      rw [hc, hA] at this
      omega
    refine ⟨hp.toSylow (by rw [hidx]; norm_num), ?_⟩
    rw [IsPGroup.toSylow_coe, Subgroup.map_comap_eq_self hUS]
  obtain ⟨P, hP⟩ := key V hV hVS
  obtain ⟨Q, hQ⟩ := key W hW hWS
  have := alternatingGroup.subsingleton_two_sylow hS4
  rw [← hP, ← hQ, Subsingleton.elim P Q]

theorem exists_map_conj_eq {V V₀ : Subgroup (alternatingGroup (Fin 7))} (hV : Nat.card V = 4)
    (hV₀ : Nat.card V₀ = 4) (hV₀2 : ∀ v ∈ V₀, v ^ 2 = 1) {γ : alternatingGroup (Fin 7)}
    (hγ : orderOf γ = 3) (hγV : ∀ v ∈ V₀, γ * v = v * γ) {S : Finset (Fin 7)} (hS : S.card = 4)
    (hVS : V ≤ (alternatingGroup.ofSubtype S).range) :
    ∃ σ : alternatingGroup (Fin 7), V₀.map (MulAut.conj σ).toMonoidHom = V := by
  obtain ⟨S₀, hS₀, hV₀S⟩ := exists_range_ofSubtype_of_commute hV₀ hV₀2 hγ hγV
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_card_four hS₀ hS
  refine ⟨σ, eq_of_le_range_ofSubtype hS ?_ hV ?_ hVS⟩
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj σ).toMonoidHom)
      (MulAut.conj σ).injective, hV₀]
  · have h := alternatingGroup.conj_smul_range_ofSubtype S₀ σ
    rw [hσ, conj_smul_eq_map] at h
    rw [← h]
    exact Subgroup.map_mono hV₀S

theorem eq_one_of_sq_of_cube {Q : Type*} [Group Q] {z : Q} (h3 : z ^ 3 = 1) (h2 : z ^ 2 = 1) :
    z = 1 := by
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem exists_conj_of_tripleCover {Q : Type*} [Group Q] [Finite Q]
    (f : Q →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) (hkerZ : f.ker ≤ center Q) {F F₀ : Subgroup Q}
    (hF : Nat.card F = 4) (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF₀ : Nat.card F₀ = 4)
    (hF₀2 : ∀ x ∈ F₀, x ^ 2 = 1) {c : Q} (hc3 : c ^ 3 = 1) (hc : f c ≠ 1)
    (hcF₀ : ∀ x ∈ F₀, c * x = x * c) {S : Finset (Fin 7)} (hS : S.card = 4)
    (hFS : ∀ x ∈ F, ∀ ω ∉ S, ((f x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ω = ω) :
    ∃ a : Q, F₀.map (MulAut.conj a).toMonoidHom = F := by
  classical
  have hcard : ∀ H : Subgroup Q, (∀ x ∈ H, x ^ 2 = 1) → Nat.card (H.map f) = Nat.card H := by
    intro H hH
    have hinj : Function.Injective (f.comp H.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      apply Subtype.ext
      exact eq_one_of_sq_of_cube (hker3 x (MonoidHom.mem_ker.2 hx)) (hH x x.2)
    have h1 : H.map f = (f.comp H.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hV₀2 : ∀ v ∈ F₀.map f, v ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF₀2 x hx, map_one]
  have hγ : orderOf (f c) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [← map_pow, hc3, map_one]) hc
  have hγV : ∀ v ∈ F₀.map f, f c * v = v * f c := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hcF₀ x hx]
  have hVS : F.map f ≤ (alternatingGroup.ofSubtype S).range := by
    rintro _ ⟨x, hx, rfl⟩
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro ω hω
    by_contra hωS
    exact (Equiv.Perm.mem_support.1 hω) (hFS x hx ω hωS)
  obtain ⟨σ, hσ⟩ := exists_map_conj_eq (by rw [hcard F hF2, hF]) (by rw [hcard F₀ hF₀2, hF₀])
    hV₀2 hγ hγV hS hVS
  obtain ⟨a, rfl⟩ := hf σ
  have hmap : (F₀.map (MulAut.conj a).toMonoidHom).map f = F.map f := by
    rw [← hσ, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hF₁2 : ∀ x ∈ F₀.map (MulAut.conj a).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF₀2 x hx, map_one]
  have hle : F ≤ F₀.map (MulAut.conj a).toMonoidHom ⊔ f.ker :=
    Subgroup.map_le_map_iff.1 hmap.ge
  have hle' : F ≤ F₀.map (MulAut.conj a).toMonoidHom := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hle hx)
    have hyz : Commute y z := Subgroup.mem_center_iff.1 (hkerZ hz) y
    have hz2 : z ^ 2 = 1 := by
      have h1 := hF2 _ hx
      rw [hyz.mul_pow, hF₁2 y hy, one_mul] at h1
      exact h1
    rw [eq_one_of_sq_of_cube (hker3 z hz) hz2, mul_one]
    exact hy
  refine ⟨a, (Subgroup.eq_of_le_of_card_ge hle' (le_of_eq ?_)).symm⟩
  rw [hF, Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
    (MulAut.conj a).injective, hF₀]

theorem closure_pair_four {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (closure ({a, b} : Set G)) = 4 ∧ ∀ x ∈ closure ({a, b} : Set G), x ^ 2 = 1 := by
  classical
  have h1 : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have h3 : ∀ x, b * (a * x) = a * (b * x) := fun x => by rw [← mul_assoc, ← hab, mul_assoc]
  have h4 : b * a = a * b := hab.symm
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  let T : Subgroup G :=
    { carrier := {1, a, b, a * b}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> subst x y <;>
          simp [mul_assoc, ha, hb, h1, h3, h4]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with hx | hx | hx | hx <;> subst x <;> simp [hai, hbi, mul_inv_rev, h4] }
  have hT : closure ({a, b} : Set G) = T := by
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      show x ∈ ({1, a, b, a * b} : Set G)
      rcases hx with hx | hx <;> subst x <;> simp
    · intro x hx
      change x ∈ ({1, a, b, a * b} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have ha' : a ∈ closure ({a, b} : Set G) := subset_closure (by simp)
      have hb' : b ∈ closure ({a, b} : Set G) := subset_closure (by simp)
      rcases hx with hx | hx | hx | hx <;> subst x
      · exact one_mem _
      · exact ha'
      · exact hb'
      · exact mul_mem ha' hb'
  rw [hT]
  refine ⟨?_, fun x hx => ?_⟩
  · change Nat.card ({1, a, b, a * b} : Set G) = 4
    have hab1 : a * b ≠ 1 := fun h => hne (by rw [← mul_one a, ← hb, ← mul_assoc, h, one_mul])
    have hba : a ≠ a * b := fun h => hb1 (by
      calc b = a * (a * b) := (h1 b).symm
        _ = a * a := by rw [← h]
        _ = 1 := ha)
    have hbb : b ≠ a * b := fun h => ha1 (by
      calc a = a * (b * b) := by rw [hb, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b * b := by rw [← h]
        _ = 1 := hb)
    have n1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => hab1 h.symm⟩
    have n2 : a ∉ ({b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hba⟩
    have e1 := Set.ncard_insert_of_notMem n1
    have e2 := Set.ncard_insert_of_notMem n2
    have e3 := Set.ncard_pair hbb
    rw [Nat.card_coe_set_eq]
    omega
  · change x ∈ ({1, a, b, a * b} : Set G) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx <;> subst x <;> simp [pow_two, mul_assoc, ha, hb, h3]

theorem mem_normalizer_closure_pair {G : Type*} [Group G] [Finite G] {a b t : G}
    (ha : t * a * t⁻¹ ∈ closure ({a, b} : Set G)) (hb : t * b * t⁻¹ ∈ closure ({a, b} : Set G)) :
    t ∈ normalizer (closure ({a, b} : Set G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> subst x
    · exact ha
    · exact hb
  · exact (Subgroup.card_map_of_injective (f := ((MulAut.conj t : MulAut G) : G →* G))
      (MulAut.conj t).injective).ge

end CFSG.ComponentClassification.SolMax.HeGen
