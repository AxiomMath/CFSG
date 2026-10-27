module

import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExt
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open

namespace AltCentralExtOne

theorem le_pRank_of_cube_ker_of_le {J A : Type*} [Group J] [Finite J] [Group A] {p : ℕ}
    [Fact p.Prime] (ψ : J →* A) {C H : Subgroup J} [IsMulCommutative C] (hCH : C ≤ H)
    (hC : ∀ c ∈ C, ψ c ^ p = 1) {k : ℕ} (hcard : p ^ k ≤ Nat.card (ψ.comp C.subtype).range) :
    k ≤ pRank p H := by
  have hrange : ((ψ.comp H.subtype).comp (C.subgroupOf H).subtype).range =
      (ψ.comp C.subtype).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.1.1, x.2⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨⟨x.1, hCH x.2⟩, x.2⟩, rfl⟩
  have h := AltCentralExt.le_pRank_of_cube_ker (ψ.comp H.subtype) (C.subgroupOf H)
    (fun c hc => hC c.1 hc) (k := k) (by rw [hrange]; exact hcard)
  refine h.trans ((SectionRank.pRank_le_map (Fact.out : p.Prime).one_lt H.subtype
    H.subtype_injective ⊤).trans ?_)
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem le_pRank_comap_of_commutation_data {J A : Type*} [Group J] [Finite J] [Group A]
    (ψ : J →* A) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (h3 : IsPGroup 3 ψ.ker) {T : Set A} (hT3 : ∀ x ∈ T, x ^ 3 = 1) (hTc : T.Pairwise Commute)
    (hTi : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ g : A, g * x * g⁻¹ = x ∧ g * y * g⁻¹ = y⁻¹) {k : ℕ}
    (hk : 3 ^ k ≤ Nat.card (Subgroup.closure T)) :
    k ≤ pRank 3 ((Subgroup.closure T).comap ψ) := by
  obtain ⟨s, hs⟩ : ∃ s : A → J, ∀ x, ψ (s x) = x :=
    ⟨Function.surjInv hψ, Function.surjInv_eq hψ⟩
  have hlift : ∀ x ∈ T, ∀ y ∈ T, s x * s y = s y * s x := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy]
    obtain ⟨g, hgx, hgy⟩ := hTi x hx y hy hxy
    exact AltCentralExt.commute_of_inverted ψ hψ hker h3 (by simpa only [hs] using hgx)
      (by simpa only [hs] using hgy) (by simpa only [hs] using (hTc hx hy hxy).eq)
  let S : Set J := s '' T ∪ ψ.ker
  have hS : S.Pairwise Commute := by
    rintro _ (⟨x, hx, rfl⟩ | hx) _ (⟨y, hy, rfl⟩ | hy) -
    · exact hlift x hx y hy
    · exact Subgroup.mem_center_iff.1 (hker hy) _
    · exact (Subgroup.mem_center_iff.1 (hker hx) _).symm
    · exact (Subgroup.mem_center_iff.1 (hker hx) _).symm
  have hCcomm : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  have hgen : ∀ x ∈ S, ψ x ^ 3 = 1 := by
    rintro _ (⟨x, hx, rfl⟩ | hx)
    · rw [hs]
      exact hT3 x hx
    · simp [MonoidHom.mem_ker.1 hx]
  have hC : ∀ c ∈ Subgroup.closure S, ψ c ^ 3 = 1 := by
    intro c hc
    refine Subgroup.closure_induction (p := fun c _ => ψ c ^ 3 = 1) hgen (by simp)
      (fun x y hx hy ihx ihy => ?_) (fun x hx ih => by rw [map_inv, inv_pow, ih, inv_one]) hc
    have hxy : ψ x * ψ y = ψ y * ψ x := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩))
    rw [map_mul, Commute.mul_pow hxy, ihx, ihy, one_mul]
  have hCH : Subgroup.closure S ≤ (Subgroup.closure T).comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨x, hx, rfl⟩ | hx)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hs]
      exact Subgroup.subset_closure hx
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
      exact one_mem _
  have hrange : Subgroup.closure T ≤ (ψ.comp (Subgroup.closure S).subtype).range := by
    rw [Subgroup.closure_le]
    intro x hx
    exact ⟨⟨s x, Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)⟩, hs x⟩
  have : Finite (ψ.comp (Subgroup.closure S).subtype).range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  exact le_pRank_of_cube_ker_of_le ψ hCH hC (hk.trans (Subgroup.card_le_of_le hrange))

section Perm

open Equiv

variable {α : Type*}

theorem eq_of_mul_eq_mul_of_perm_disjoint {σ τ σ' τ' : Perm α} (h : σ * τ = σ' * τ')
    (h1 : Perm.Disjoint σ τ) (h2 : Perm.Disjoint σ τ') (h3 : Perm.Disjoint σ' τ)
    (h4 : Perm.Disjoint σ' τ') : σ = σ' ∧ τ = τ' := by
  have hρ : σ'⁻¹ * σ = τ' * τ⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
  have hd : Perm.Disjoint (σ'⁻¹ * σ) (τ' * τ⁻¹) :=
    (h4.inv_left.mul_right h3.inv_left.inv_right).mul_left (h2.mul_right h1.inv_right)
  rw [hρ] at hd
  have h5 : τ' * τ⁻¹ = 1 := Perm.disjoint_refl_iff.1 hd
  exact ⟨(inv_mul_eq_one.1 (hρ.trans h5)).symm, (mul_inv_eq_one.1 h5).symm⟩

variable [DecidableEq α]

theorem swap_mul_mul_swap_eq_inv {y : Perm α} {a b d : α} (h : y = swap a b * swap b d) :
    swap a b * y * (swap a b)⁻¹ = y⁻¹ := by
  subst h
  simp

variable [Fintype α]

theorem exists_swap_inv_of_isThreeCycle {y : Perm α} (hy : y.IsThreeCycle) :
    ∃ a b : α, a ∈ y.support ∧ b ∈ y.support ∧ a ≠ b ∧ swap a b * y * (swap a b)⁻¹ = y⁻¹ := by
  obtain ⟨a, ha⟩ : y.support.Nonempty :=
    Finset.card_pos.1 (by rw [hy.card_support]; norm_num)
  exact ⟨a, y a, ha, Perm.apply_mem_support.2 ha, fun h => Perm.mem_support.1 ha h.symm,
    swap_mul_mul_swap_eq_inv (hy.eq_swap_mul_swap_iff_mem_support.2 ha)⟩

theorem commute_swap_of_notMem_support {p q : α} {f : Perm α} (hpq : p ≠ q)
    (hp : p ∉ f.support) (hq : q ∉ f.support) : Commute (swap p q) f := by
  refine Perm.Disjoint.commute (Perm.disjoint_iff_disjoint_support.2 ?_)
  rw [Perm.support_swap hpq, Finset.disjoint_left]
  intro e he
  rcases Finset.mem_insert.1 he with rfl | he
  · exact hp
  · rw [Finset.mem_singleton.1 he]
    exact hq

theorem exists_even_centralizing_inverting {x y z : Perm α} (hy : y.IsThreeCycle)
    (hz : z.IsThreeCycle) (hxy : Disjoint x.support y.support) (hxz : Disjoint x.support z.support)
    (hyz : Disjoint y.support z.support) :
    ∃ t : Perm α, Perm.sign t = 1 ∧ t * x * t⁻¹ = x ∧ t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨a, b, ha, hb, hab, hinv⟩ := exists_swap_inv_of_isThreeCycle hy
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ z.support, ∃ v ∈ z.support, u ≠ v :=
    Finset.one_lt_card.1 (by rw [hz.card_support]; norm_num)
  have hx1 : Commute (swap a b) x := commute_swap_of_notMem_support hab
    (Finset.disjoint_right.1 hxy ha) (Finset.disjoint_right.1 hxy hb)
  have hx2 : Commute (swap u v) x := commute_swap_of_notMem_support huv
    (Finset.disjoint_right.1 hxz hu) (Finset.disjoint_right.1 hxz hv)
  have hy2 : Commute (swap u v) y := commute_swap_of_notMem_support huv
    (Finset.disjoint_right.1 hyz hu) (Finset.disjoint_right.1 hyz hv)
  refine ⟨swap a b * swap u v, ?_, ?_, ?_⟩
  · rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap huv]
    decide
  · exact mul_inv_eq_iff_eq_mul.2 (hx1.mul_left hx2).eq
  · calc swap a b * swap u v * y * (swap a b * swap u v)⁻¹
        = swap a b * (swap u v * y * (swap u v)⁻¹) * (swap a b)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = y⁻¹ := by rw [mul_inv_eq_iff_eq_mul.2 hy2.eq]; exact hinv

theorem exists_inverting_alt {x y z : alternatingGroup α} (hy : (y : Perm α).IsThreeCycle)
    (hz : (z : Perm α).IsThreeCycle) (hxy : Disjoint (x : Perm α).support (y : Perm α).support)
    (hxz : Disjoint (x : Perm α).support (z : Perm α).support)
    (hyz : Disjoint (y : Perm α).support (z : Perm α).support) :
    ∃ g : alternatingGroup α, g * x * g⁻¹ = x ∧ g * y * g⁻¹ = y⁻¹ := by
  obtain ⟨t, ht, h1, h2⟩ := exists_even_centralizing_inverting hy hz hxy hxz hyz
  exact ⟨⟨t, Perm.mem_alternatingGroup.2 ht⟩, Subtype.ext h1, Subtype.ext h2⟩

theorem injective_prod_pow {c : Fin 4 → Perm α} (hc : ∀ i, (c i).IsThreeCycle)
    (hd : ∀ i j, i ≠ j → Perm.Disjoint (c i) (c j)) :
    Function.Injective fun q : Fin 3 × Fin 3 × Fin 3 × Fin 3 =>
      c 0 ^ (q.1 : ℕ) * c 1 ^ (q.2.1 : ℕ) * c 2 ^ (q.2.2.1 : ℕ) * c 3 ^ (q.2.2.2 : ℕ) := by
  have hD : ∀ a b : Fin 4, a ≠ b → ∀ m n : ℕ, Perm.Disjoint (c a ^ m) (c b ^ n) :=
    fun a b hab m n => (hd a b hab).pow_disjoint_pow m n
  have hpow : ∀ (m : Fin 4) (a b : Fin 3), c m ^ (a : ℕ) = c m ^ (b : ℕ) → a = b := by
    intro m a b hab
    have := pow_eq_pow_iff_modEq.1 hab
    rw [(hc m).orderOf] at this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt this a.2 b.2)
  have d3 : ∀ a b d e : ℕ, Perm.Disjoint (c 0 ^ a * c 1 ^ b * c 2 ^ d) (c 3 ^ e) := fun a b d e =>
    ((hD 0 3 (by decide) a e).mul_left (hD 1 3 (by decide) b e)).mul_left
      (hD 2 3 (by decide) d e)
  have d2 : ∀ a b d : ℕ, Perm.Disjoint (c 0 ^ a * c 1 ^ b) (c 2 ^ d) := fun a b d =>
    (hD 0 2 (by decide) a d).mul_left (hD 1 2 (by decide) b d)
  have d1 : ∀ a b : ℕ, Perm.Disjoint (c 0 ^ a) (c 1 ^ b) := fun a b => hD 0 1 (by decide) a b
  rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
  obtain ⟨h012, hl⟩ := eq_of_mul_eq_mul_of_perm_disjoint h (d3 _ _ _ _) (d3 _ _ _ _) (d3 _ _ _ _)
    (d3 _ _ _ _)
  obtain ⟨h01, hk⟩ := eq_of_mul_eq_mul_of_perm_disjoint h012 (d2 _ _ _) (d2 _ _ _) (d2 _ _ _)
    (d2 _ _ _)
  obtain ⟨hi, hj⟩ := eq_of_mul_eq_mul_of_perm_disjoint h01 (d1 _ _) (d1 _ _) (d1 _ _) (d1 _ _)
  exact Prod.ext (hpow 0 _ _ hi) (Prod.ext (hpow 1 _ _ hj) (Prod.ext (hpow 2 _ _ hk)
    (hpow 3 _ _ hl)))

end Perm

end AltCentralExtOne

theorem four_le_pRank_comap_of_central_three {J : Type*} [Group J] [Finite J] {n : ℕ}
    (ψ : J →* alternatingGroup (Fin n)) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center J) (h3 : IsPGroup 3 ψ.ker)
    (c : Fin 4 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    4 ≤ Open.pRank 3 ((Subgroup.closure (Set.range c)).comap ψ) := by
  have hpow3 : ∀ i, (c i : Equiv.Perm (Fin n)) ^ 3 = 1 := fun i => by
    have := pow_orderOf_eq_one (c i : Equiv.Perm (Fin n))
    rwa [(hc i).orderOf] at this
  have hne : ∀ i j, c i ≠ c j → i ≠ j := fun i j h hij => h (hij ▸ rfl)
  have hk3 : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  have hdisj' : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i : Equiv.Perm (Fin n)) (c j) :=
    fun i j hij => Equiv.Perm.disjoint_iff_disjoint_support.2 (hdisj i j hij)
  refine AltCentralExtOne.le_pRank_comap_of_commutation_data ψ hψ hker h3 (T := Set.range c)
    ?_ ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact Subtype.ext (hpow3 i)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact Subtype.ext (hdisj' i j (hne i j hij)).commute.eq
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    obtain ⟨k, hki, hkj⟩ := hk3 i j
    exact AltCentralExtOne.exists_inverting_alt (hc j) (hc k) (hdisj i j (hne i j hij))
      (hdisj i k hki.symm) (hdisj j k hkj.symm)
  · have hinj := AltCentralExtOne.injective_prod_pow
      (c := fun i => (c i : Equiv.Perm (Fin n))) hc hdisj'
    have hgen : ∀ (m : Fin 4) (e : ℕ), c m ^ e ∈ Subgroup.closure (Set.range c) := fun m e =>
      Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self m)) e
    let ν : Fin 3 × Fin 3 × Fin 3 × Fin 3 → Subgroup.closure (Set.range c) := fun q =>
      ⟨c 0 ^ (q.1 : ℕ) * c 1 ^ (q.2.1 : ℕ) * c 2 ^ (q.2.2.1 : ℕ) * c 3 ^ (q.2.2.2 : ℕ),
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgen 0 _) (hgen 1 _))
          (hgen 2 _)) (hgen 3 _)⟩
    calc 3 ^ 4 = Nat.card (Fin 3 × Fin 3 × Fin 3 × Fin 3) := by simp
      _ ≤ _ := Nat.card_le_card_of_injective ν fun q q' h => hinj (congrArg (fun x => x.1.1) h)

end CFSG.AGLEmbeddingD2
