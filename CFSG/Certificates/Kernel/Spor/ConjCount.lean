module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.KS.ConjCount

variable {G : Type*} [Group G] {ι : Type*} {b : ι → G}

theorem mem_centralizer_iff_conj {L : Subgroup G} (hL : L = Subgroup.closure (Set.range b))
    (g : G) : g ∈ Subgroup.centralizer (L : Set G) ↔ ∀ i, g * b i * g⁻¹ = b i := by
  constructor
  · intro hg i
    have hb : b i ∈ L := hL ▸ Subgroup.subset_closure ⟨i, rfl⟩
    rw [← Subgroup.mem_centralizer_iff.1 hg (b i) hb, mul_inv_cancel_right]
  · intro h
    rw [hL, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    calc b i * g = (g * b i * g⁻¹) * g := by rw [h i]
      _ = g * b i := by group

theorem mem_normalizer_of_finite {S : Set G} {g : G} (hfin : S.Finite)
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : G ↪ G := ⟨fun y => g * y * g⁻¹, fun a c hac => by
    have := congrArg (fun z => g⁻¹ * z * g) hac
    simpa [mul_assoc] using this⟩
  have hsub : (f '' S) ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : f '' S = S := Set.map_eq_of_subset hsub hfin
  have hx' : f x ∈ f '' S := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := hx'
  have : y = x := f.injective hyx
  rwa [this] at hy

theorem mem_normalizer_iff_conj {L : Subgroup G} (hL : L = Subgroup.closure (Set.range b))
    (hfin : (L : Set G).Finite) (g : G) :
    g ∈ Subgroup.normalizer (L : Set G) ↔ ∀ i, g * b i * g⁻¹ ∈ L := by
  constructor
  · intro hg i
    have hb : b i ∈ L := hL ▸ Subgroup.subset_closure ⟨i, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg (b i)).1 hb
  · intro h
    refine mem_normalizer_of_finite hfin fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    rw [hL] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact h i
    | one => simpa using Subgroup.one_mem _
    | mul a c _ _ ha hc =>
      have e : g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hc
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha

@[expose] noncomputable def sumConj (L : Subgroup G) [Fintype L] (kp : G → ℕ) (g : G) : ℕ :=
  ∑ h : L, kp (g * (h : G) * g⁻¹)

@[expose] noncomputable def conjEquiv (L : Subgroup G) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) : L ≃ L where
  toFun h := ⟨a * h * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha h).1 h.2⟩
  invFun h := ⟨a⁻¹ * h * a, by
    have h1 := (Subgroup.mem_normalizer_iff.1 ha (a⁻¹ * h * a)).2
    have e : a * (a⁻¹ * (h : G) * a) * a⁻¹ = h := by group
    exact h1 (by rw [e]; exact h.2)⟩
  left_inv h := Subtype.ext (by simp only; group)
  right_inv h := Subtype.ext (by simp only; group)

theorem sumConj_mul (L : Subgroup G) [Fintype L] (kp : G → ℕ) (g : G) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) : sumConj L kp (g * a) = sumConj L kp g := by
  unfold sumConj
  refine Fintype.sum_equiv (conjEquiv L ha) _ _ fun h => ?_
  change kp (g * a * h * (g * a)⁻¹) = kp (g * (a * h * a⁻¹) * g⁻¹)
  congr 1
  group

theorem card_orbit_mul_le [Finite G] [Finite ι] {A L : Subgroup G}
    (hL : L = Subgroup.closure (Set.range b)) :
    Nat.card {x : ι → G | ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹} *
      Nat.card ↥(Subgroup.centralizer (L : Set G) ⊓ A) ≤ Nat.card A := by
  let O := {x : ι → G | ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹}
  let C := Subgroup.centralizer (L : Set G) ⊓ A
  have hO : ∀ x ∈ O, ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹ := fun x hx => hx
  choose! gx hgxA hgx using hO
  let f : O × C → A := fun p => ⟨gx p.1.1 * p.2.1, Subgroup.mul_mem _ (hgxA _ p.1.2)
    (Subgroup.mem_inf.1 p.2.2).2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, z⟩ ⟨⟨y, hy⟩, z'⟩ e
    have e1 : gx x * z = gx y * z' := congrArg Subtype.val e
    have hz : ∀ {z : C} i, (z : G) * b i * (z : G)⁻¹ = b i := fun {z} i =>
      (mem_centralizer_iff_conj hL _).1 (Subgroup.mem_inf.1 z.2).1 i
    have hxy : x = y := funext fun i => by
      rw [hgx x hx i, hgx y hy i]
      calc gx x * b i * (gx x)⁻¹ = (gx x * z) * b i * (gx x * z)⁻¹ := by
            rw [mul_inv_rev]
            calc gx x * b i * (gx x)⁻¹ = gx x * ((z : G) * b i * (z : G)⁻¹) * (gx x)⁻¹ := by
                  rw [hz i]
              _ = _ := by group
        _ = (gx y * z') * b i * (gx y * z')⁻¹ := by rw [e1]
        _ = gx y * ((z' : G) * b i * (z' : G)⁻¹) * (gx y)⁻¹ := by group
        _ = gx y * b i * (gx y)⁻¹ := by rw [hz i]
    subst hxy
    have e2 : (z : G) = z' := by simpa using e1
    rw [Subtype.ext e2]
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h1

variable {A L CL : Subgroup G} [Fintype L] {kp : G → ℕ} {q r c : ℕ} {gk : Fin q → G}
  {nn : Fin r → G}

theorem conj_count [Finite G] [Finite ι] (hL : L = Subgroup.closure (Set.range b))
    (hA : Nat.card A = q * r * c) (hgA : ∀ k, gk k ∈ A)
    (hS : ∀ k k', sumConj L kp (gk k) = sumConj L kp (gk k') → k = k')
    (hnA : ∀ l, nn l ∈ A) (hnN : ∀ l, nn l ∈ Subgroup.normalizer (L : Set G))
    (hny : ∀ l l', (∀ i, nn l * b i * (nn l)⁻¹ = nn l' * b i * (nn l')⁻¹) → l = l')
    (hCL : CL ≤ Subgroup.centralizer (L : Set G) ⊓ A) (hcl : Nat.card CL = c) :
    Subgroup.centralizer (L : Set G) ⊓ A = CL ∧
      Nat.card {x : ι → G | ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹} = q * r ∧
      Nat.card {x : ι → G | (∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹) ∧ ∀ i, x i ∈ L} = r := by
  set C := Subgroup.centralizer (L : Set G) ⊓ A with hCdef
  have hfin : (L : Set G).Finite := Set.toFinite _
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hqr : 0 < q * r := by
    rcases Nat.eq_zero_or_pos (q * r) with h | h
    · rw [h, zero_mul] at hA
      omega
    · exact h
  have hcent : ∀ {g}, g ∈ C → ∀ i, g * b i * g⁻¹ = b i := fun hg =>
    (mem_centralizer_iff_conj hL _).1 (Subgroup.mem_inf.1 hg).1
  have hCN : ∀ {g}, g ∈ C → g ∈ Subgroup.normalizer (L : Set G) := fun hg =>
    (mem_normalizer_iff_conj hL hfin _).2 fun i => by
      rw [hcent hg i, hL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  have hsep : ∀ k k', (gk k')⁻¹ * gk k ∈ Subgroup.normalizer (L : Set G) → k = k' :=
    fun k k' h => hS k k' (by
      have e : gk k = gk k' * ((gk k')⁻¹ * gk k) := by group
      rw [e, sumConj_mul L kp _ h])
  have hcmem : ∀ {g g'}, g ∈ A → g' ∈ A → (∀ i, g * b i * g⁻¹ = g' * b i * g'⁻¹) →
      g'⁻¹ * g ∈ C := by
    intro g g' hg hg' he
    refine Subgroup.mem_inf.2 ⟨(mem_centralizer_iff_conj hL _).2 fun i => ?_,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hg⟩
    have e : g'⁻¹ * g * b i * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * b i * g⁻¹) * g' := by group
    rw [e, he i]
    group
  have hCle : Nat.card C ≤ c := by
    let f : Fin q × Fin r × C → A := fun x =>
      ⟨gk x.1 * nn x.2.1 * x.2.2, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgA _) (hnA _))
        (Subgroup.mem_inf.1 x.2.2.2).2⟩
    have hf : Function.Injective f := by
      rintro ⟨k, l, x⟩ ⟨k', l', x'⟩ e
      have e1 : gk k * nn l * x = gk k' * nn l' * x' := congrArg Subtype.val e
      have hk : k = k' := hsep k k' (by
        have e2 : (gk k')⁻¹ * gk k = nn l' * x' * (x : G)⁻¹ * (nn l)⁻¹ := by
          calc (gk k')⁻¹ * gk k = (gk k')⁻¹ * (gk k * nn l * x) * (x : G)⁻¹ * (nn l)⁻¹ := by
                group
            _ = _ := by rw [e1]; group
        rw [e2]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnN l') (hCN x'.2))
          (Subgroup.inv_mem _ (hCN x.2))) (Subgroup.inv_mem _ (hnN l)))
      subst hk
      have e3 : nn l * x = nn l' * x' := by
        have := congrArg (fun y => (gk k)⁻¹ * y) e1
        simpa [mul_assoc] using this
      have hl : l = l' := hny l l' (by
        have hm : (nn l')⁻¹ * nn l ∈ C := by
          have e4 : (nn l')⁻¹ * nn l = (x' : G) * (x : G)⁻¹ := by
            calc (nn l')⁻¹ * nn l = (nn l')⁻¹ * (nn l * x) * (x : G)⁻¹ := by group
              _ = _ := by rw [e3]; group
          rw [e4]
          exact Subgroup.mul_mem _ x'.2 (Subgroup.inv_mem _ x.2)
        intro i
        have h1 := hcent hm i
        calc nn l * b i * (nn l)⁻¹
            = nn l' * (((nn l')⁻¹ * nn l) * b i * ((nn l')⁻¹ * nn l)⁻¹) * (nn l')⁻¹ := by group
          _ = nn l' * b i * (nn l')⁻¹ := by rw [h1])
      subst hl
      have e5 : (x : G) = x' := by simpa using e3
      rw [Subtype.ext e5]
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin q),
      Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, Fintype.card_fin, hA,
      ← Nat.mul_assoc] at h1
    exact Nat.le_of_mul_le_mul_left h1 hqr
  have hCeq : C = CL := (Subgroup.eq_of_le_of_card_ge hCL (by rw [hcl]; exact hCle)).symm
  have hcC : Nat.card C = c := by rw [hCeq, hcl]
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hA
      omega
    · exact h
  have hO : Nat.card {x : ι → G | ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹} = q * r := by
    refine le_antisymm ?_ ?_
    · have h1 := card_orbit_mul_le (ι := ι) (A := A) hL
      rw [hcC, hA] at h1
      exact Nat.le_of_mul_le_mul_right h1 hcpos
    · let f : Fin q × Fin r → {x : ι → G | ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹} := fun p =>
        ⟨fun i => (gk p.1 * nn p.2) * b i * (gk p.1 * nn p.2)⁻¹,
          gk p.1 * nn p.2, Subgroup.mul_mem _ (hgA _) (hnA _), fun _ => rfl⟩
      have hf : Function.Injective f := by
        rintro ⟨k, l⟩ ⟨k', l'⟩ e
        have hm := hcmem (Subgroup.mul_mem _ (hgA k) (hnA l)) (Subgroup.mul_mem _ (hgA k') (hnA l'))
          fun i => congrFun (congrArg Subtype.val e) i
        have hk : k = k' := hsep k k' (by
          have e2 : (gk k')⁻¹ * gk k =
              nn l' * ((gk k' * nn l')⁻¹ * (gk k * nn l)) * (nn l)⁻¹ := by group
          rw [e2]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnN l') (hCN hm))
            (Subgroup.inv_mem _ (hnN l)))
        subst hk
        have hm' : (nn l')⁻¹ * nn l ∈ C := by
          have e3 : (nn l')⁻¹ * nn l = (gk k * nn l')⁻¹ * (gk k * nn l) := by group
          rw [e3]
          exact hm
        have hl : l = l' := hny l l' fun i => by
          have h1 := hcent hm' i
          calc nn l * b i * (nn l)⁻¹
              = nn l' * (((nn l')⁻¹ * nn l) * b i * ((nn l')⁻¹ * nn l)⁻¹) * (nn l')⁻¹ := by
                group
            _ = nn l' * b i * (nn l')⁻¹ := by rw [h1]
        rw [hl]
      have h1 := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin q),
        Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, Fintype.card_fin] at h1
  refine ⟨hCeq, hO, le_antisymm ?_ ?_⟩
  ·
    let S := {x : ι → G | (∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹) ∧ ∀ i, x i ∈ L}
    let O := {x : ι → G | ∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹}
    have hSN : ∀ x ∈ S, ∃ g ∈ A, g ∈ Subgroup.normalizer (L : Set G) ∧
        ∀ i, x i = g * b i * g⁻¹ := by
      rintro x ⟨⟨g, hg, hx⟩, hL'⟩
      exact ⟨g, hg, (mem_normalizer_iff_conj hL hfin g).2 fun i => hx i ▸ hL' i, hx⟩
    choose! gs hgsA hgsN hgsx using hSN
    let f : Fin q × S → O := fun p => ⟨fun i => gk p.1 * p.2.1 i * (gk p.1)⁻¹,
      gk p.1 * gs p.2.1, Subgroup.mul_mem _ (hgA _) (hgsA _ p.2.2), fun i => by
        change gk p.1 * p.2.1 i * (gk p.1)⁻¹ = _
        rw [hgsx _ p.2.2 i]
        group⟩
    have hf : Function.Injective f := by
      rintro ⟨k, x, hx⟩ ⟨k', x', hx'⟩ e
      have e1 : ∀ i, gk k * x i * (gk k)⁻¹ = gk k' * x' i * (gk k')⁻¹ := fun i =>
        congrFun (congrArg Subtype.val e) i
      have hm := hcmem (Subgroup.mul_mem _ (hgA k) (hgsA x hx))
        (Subgroup.mul_mem _ (hgA k') (hgsA x' hx')) fun i => by
          have := e1 i
          rw [hgsx x hx i, hgsx x' hx' i] at this
          calc gk k * gs x * b i * (gk k * gs x)⁻¹ = gk k * (gs x * b i * (gs x)⁻¹) * (gk k)⁻¹ := by
                group
            _ = gk k' * (gs x' * b i * (gs x')⁻¹) * (gk k')⁻¹ := this
            _ = _ := by group
      have hk : k = k' := hsep k k' (by
        have e2 : (gk k')⁻¹ * gk k =
            gs x' * ((gk k' * gs x')⁻¹ * (gk k * gs x)) * (gs x)⁻¹ := by group
        rw [e2]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgsN x' hx') (hCN hm))
          (Subgroup.inv_mem _ (hgsN x hx)))
      subst hk
      have e3 : x = x' := funext fun i => by
        have := congrArg (fun y => (gk k)⁻¹ * y * gk k) (e1 i)
        simpa [mul_assoc] using this
      subst e3
      rfl
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin q), Fintype.card_fin] at h1
    change q * Nat.card S ≤ Nat.card O at h1
    rw [hO] at h1
    have hq : 0 < q := Nat.pos_of_mul_pos_right hqr
    exact Nat.le_of_mul_le_mul_left h1 hq
  ·
    let f : Fin r → {x : ι → G | (∃ g ∈ A, ∀ i, x i = g * b i * g⁻¹) ∧ ∀ i, x i ∈ L} :=
      fun l => ⟨fun i => nn l * b i * (nn l)⁻¹, ⟨nn l, hnA l, fun _ => rfl⟩,
        fun i => (mem_normalizer_iff_conj hL hfin _).1 (hnN l) i⟩
    have hf : Function.Injective f := fun l l' e =>
      hny l l' fun i => congrFun (congrArg Subtype.val e) i
    have h1 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin] at h1

end CFSG.KS.ConjCount

end
