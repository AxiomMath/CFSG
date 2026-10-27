module

public import CFSG.CGT.A8S.Interfaces
public import CFSG.CGT.A8S.TopData

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 Perm8

variable {G : Type} [Group G] {T : Subgroup G}

theorem evalA8_genTupleA8_relsN0 (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G)))
    (g : G) : ∀ r ∈ relsN0A8, evalA8 (genTupleA8 ψ g) (liftW5 r) = 1 := by
  intro r hr
  rw [evalA8_liftW5]
  have h1 : (PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ relsN0A8.map FreeGroup.mk}
      (FreeGroup.mk r)) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem hr)
  have h2 : (FreeGroup.lift (fun i : Fin 5 => genTupleA8 ψ g (Fin.castSucc i)) :
      FreeGroup (Fin 5) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 5) |
          r ∈ relsN0A8.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [genTupleA8, PresentedGroup.mk]
    rfl
  rw [h2]
  simp [h1]

theorem sup_le_closure_genTupleA8 (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G)))
    (g : G) : Subgroup.normalizer (T : Set G) ⊔ conjSubgroup g T ≤
      Subgroup.closure (Set.range (genTupleA8 ψ g)) := by
  set X := Subgroup.closure (Set.range (genTupleA8 ψ g)) with hXdef
  have hN : ∀ n : ↥(Subgroup.normalizer (T : Set G)), (n : G) ∈ X := by
    intro n
    have hw : ψ.symm n ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 5 → PG 5 relsN0A8)) := by
      rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top _
    have key : ∀ w : PG 5 relsN0A8, w ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 5 → PG 5 relsN0A8)) →
        ((ψ w : ↥(Subgroup.normalizer (T : Set G))) : G) ∈ X := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨Fin.castSucc i, ?_⟩
        simp [genTupleA8]
      | one => simp
      | mul x y _ _ hx hy => simpa using X.mul_mem hx hy
      | inv x _ hx => simpa using X.inv_mem hx
    simpa using key _ hw
  have hg : g ∈ X := Subgroup.subset_closure ⟨5, by simp [genTupleA8]⟩
  have hT1 : conjSubgroup g T ≤ X := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h3 := X.mul_mem (X.mul_mem hg (hN ⟨_, Subgroup.le_normalizer hx⟩)) (X.inv_mem hg)
    simpa [mul_assoc] using h3
  exact sup_le (fun x hx => hN ⟨x, hx⟩) hT1

theorem genTupleA8_t (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G)
    (j : Fin 3) :
    genTupleA8 ψ g ⟨2 + j.val, by omega⟩ =
      ((ψ (tGenA8 j) : ↥(Subgroup.normalizer (T : Set G))) : G) := by
  have hj : 2 + j.val < 5 := by omega
  simp only [genTupleA8, hj, ↓reduceDIte, tGenA8]

theorem eq_closure_genTupleA8_t (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G)))
    (g : G) (hmap : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGenA8)) =
      T.subgroupOf (Subgroup.normalizer (T : Set G))) :
    T = Subgroup.closure (Set.range fun j : Fin 3 => genTupleA8 ψ g ⟨2 + j.val, by omega⟩) := by
  have hT : T = (T.subgroupOf (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr Subgroup.le_normalizer]
  rw [← hmap, Subgroup.map_map, MonoidHom.map_closure, ← Set.range_comp] at hT
  refine hT.trans (congrArg Subgroup.closure (congrArg Set.range (funext fun j => ?_)))
  exact (genTupleA8_t ψ g j).symm

theorem T1ConfigA8.sup_le_closure_gens {T₁ : Subgroup G} (c : T1ConfigA8 T T₁) :
    Subgroup.normalizer (T : Set G) ⊔ T₁ ≤ Subgroup.closure (Set.range c.gens) := by
  have h := sup_le_closure_genTupleA8 c.ψ c.g
  rwa [c.conj_g] at h

theorem T1ConfigA8.eq_closure_t {T₁ : Subgroup G} (c : T1ConfigA8 T T₁) :
    T = Subgroup.closure (Set.range fun j : Fin 3 => c.gens ⟨2 + j.val, by omega⟩) :=
  eq_closure_genTupleA8_t c.ψ c.g c.map_t

theorem T1ConfigA8.rels {T₁ : Subgroup G} [Finite G] (hR3 : R3StatementA8)
    (hyp : A8CtxHyp T T₁) (c : T1ConfigA8 T T₁) : ∀ r ∈ a8Rels, evalA8 c.gens r = 1 := by
  intro r hr
  simp only [a8Rels, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    exact evalA8_genTupleA8_relsN0 c.ψ c.g r0 hr0
  · exact c.rel r hr
  · exact hR3 G T T₁ hyp c r hr

theorem exists_mulEquiv_a8_of_parts (hN0 : N0StatementA8) (hL2 : N0StatementA8 → L2StatementA8)
    (hR3 : R3StatementA8) (hR5 : R5StatementA8) [Finite G] {T₁ : Subgroup G}
    (hyp : A8CtxHyp T T₁) :
    ∃ c : T1ConfigA8 T T₁,
      Subgroup.normalizer (T : Set G) ⊔ T₁ ≤ Subgroup.closure (Set.range c.gens) ∧
      ∃ φ : ↥(Subgroup.closure (Set.range c.gens)) ≃* alternatingGroup (Fin 8),
        ∀ i, ((φ ⟨c.gens i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : alternatingGroup (Fin 8)) :
          Equiv.Perm (Fin 8)) = a8Perm i := by
  obtain ⟨c⟩ := hL2 hN0 G T T₁ hyp
  have hle := c.sup_le_closure_gens
  have hne : Subgroup.closure (Set.range c.gens) ≠ ⊥ := by
    intro h
    have hTle : T ≤ Subgroup.closure (Set.range c.gens) :=
      (Subgroup.le_normalizer.trans le_sup_left).trans hle
    rw [h, le_bot_iff] at hTle
    have h1 := hyp.card8
    rw [hTle, Subgroup.card_bot] at h1
    omega
  obtain ⟨φ, hφ⟩ := hR5 G c.gens (c.rels hR3 hyp) hne
  exact ⟨c, hle, φ, hφ⟩

theorem mem_iff_exists_transl {X : Subgroup G} (φ : ↥X ≃* alternatingGroup (Fin 8))
    (e : Fin 6 → G) (heX : ∀ i, e i ∈ X)
    (hφe : ∀ i, ((φ ⟨e i, heX i⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) = a8Perm i)
    (hT : T = Subgroup.closure (Set.range fun j : Fin 3 => e ⟨2 + j.val, by omega⟩)) :
    ∀ x : ↥X, (x : G) ∈ T ↔
      ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) = transl c := by
  have hcX : Subgroup.closure (Set.range fun j : Fin 3 => e ⟨2 + j.val, by omega⟩) ≤ X := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact heX _
  have he : ∀ j : Fin 3, e ⟨2 + j.val, by omega⟩ ∈ T := fun j =>
    hT ▸ Subgroup.subset_closure ⟨j, rfl⟩
  have key : ∀ y (hy : y ∈ Subgroup.closure (Set.range fun j : Fin 3 =>
      e ⟨2 + j.val, by omega⟩)), ∃ c : Fin 8,
      ((φ ⟨y, hcX hy⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) = transl c := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨2 ^ j.val, ?_⟩
      rw [hφe]
      fin_cases j
      · exact a8Perm_two
      · exact a8Perm_three
      · exact a8Perm_four
    | one =>
      refine ⟨0, ?_⟩
      rw [transl_zero, show (⟨1, hcX (Subgroup.one_mem _)⟩ : ↥X) = 1 from rfl, map_one]
      rfl
    | mul y w hy hw ihy ihw =>
      obtain ⟨c₁, hc₁⟩ := ihy
      obtain ⟨c₂, hc₂⟩ := ihw
      obtain ⟨c₃, hc₃⟩ := exists_transl_mul c₁ c₂
      refine ⟨c₃, ?_⟩
      rw [show (⟨y * w, hcX (Subgroup.mul_mem _ hy hw)⟩ : ↥X) =
        ⟨y, hcX hy⟩ * ⟨w, hcX hw⟩ from rfl, map_mul, Subgroup.coe_mul, hc₁, hc₂, hc₃]
    | inv y hy ihy =>
      obtain ⟨c₁, hc₁⟩ := ihy
      refine ⟨c₁, ?_⟩
      rw [show (⟨y⁻¹, hcX (Subgroup.inv_mem _ hy)⟩ : ↥X) = (⟨y, hcX hy⟩ : ↥X)⁻¹ from rfl,
        map_inv, Subgroup.coe_inv, hc₁, inv_eq_of_mul_eq_one_right (transl_mul_self c₁)]
  intro x
  constructor
  · intro hx
    rw [hT] at hx
    exact key _ hx
  · rintro ⟨c, hc⟩
    set y : ↥X := ⟨e 2, heX 2⟩ ^ (c.val % 2) * ⟨e 3, heX 3⟩ ^ (c.val / 2 % 2) *
      ⟨e 4, heX 4⟩ ^ (c.val / 4) with hy
    have hxy : x = y := φ.injective (Subtype.ext (by
      rw [hc, transl_eq_prod, hy, map_mul, map_mul, map_pow, map_pow, map_pow, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_pow, hφe, hφe, hφe]))
    rw [hxy, hy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      Subgroup.coe_pow]
    exact T.mul_mem (T.mul_mem (T.pow_mem (he 0) _) (T.pow_mem (he 1) _)) (T.pow_mem (he 2) _)

theorem jankoA8CtxInput_of_parts (hN0 : N0StatementA8) (hL2 : N0StatementA8 → L2StatementA8)
    (hR3 : R3StatementA8) (hR5 : R5StatementA8) :
    ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), A8CtxHyp T T₁ →
      ∃ X : Subgroup G, Subgroup.normalizer (T : Set G) ≤ X ∧ T₁ ≤ X ∧
        ∃ φ : ↥X ≃* alternatingGroup (Fin 8), ∀ x : ↥X, (x : G) ∈ T ↔
          ∃ c : Fin 8, ((φ x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) = transl c := by
  intro G _ _ T T₁ hyp
  obtain ⟨c, hle, φ, hφ⟩ := exists_mulEquiv_a8_of_parts hN0 hL2 hR3 hR5 hyp
  exact ⟨_, le_sup_left.trans hle, le_sup_right.trans hle, φ,
    mem_iff_exists_transl φ c.gens (fun i => Subgroup.subset_closure ⟨i, rfl⟩) hφ c.eq_closure_t⟩

end CFSG.CGT.A8S
