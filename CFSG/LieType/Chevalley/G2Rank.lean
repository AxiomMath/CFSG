module

public import CFSG.LieType.Chevalley.RootProduct
public import CFSG.LieType.Chevalley.RootRank

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank

theorem val_inv_smul_simpleRoot
    {τ : Tag} (ω : List (Fin τ.rank)) (i : Fin τ.rank) :
    (((coxeterSystem τ).wordProd ω)⁻¹ • simpleRoot τ i).1 =
      ω.reverse.foldr (reflect τ) (Pi.single i 1) := by
  rw [coe_smul_root, ← CoxeterSystem.wordProd_reverse, wordProd_smul]
  rfl

@[expose] def g2LongWord : List (Fin Tag.G2.rank) := ([0, 1, 0, 1, 0, 1] : List (Fin 2))

noncomputable abbrev g2Root
    (ω : List (Fin 2)) (i : Fin 2) : Root .G2 :=
  ((coxeterSystem .G2).wordProd ω)⁻¹ • simpleRoot .G2 i

theorem wordRoots_g2LongWord
    : wordRoots g2LongWord =
    [g2Root [1, 0, 1, 0, 1] 0, g2Root [0, 1, 0, 1] 1, g2Root [1, 0, 1] 0, g2Root [0, 1] 1,
      g2Root [1] 0, g2Root [] 1] := rfl

abbrev g2Vec (ω : List (Fin 2)) (i : Fin 2) : Fin Tag.G2.rank → ℤ :=
  ω.reverse.foldr (reflect .G2) (Pi.single i 1)

theorem pairCheck_g2 :
    pairCheck .G2 (g2Vec [1, 0, 1] 0) (g2Vec [0, 1] 1) = true ∧
      pairCheck .G2 (g2Vec [1, 0, 1] 0) (g2Vec [1] 0) = true ∧
      pairCheck .G2 (g2Vec [0, 1] 1) (g2Vec [1] 0) = true := by
  decide +kernel

noncomputable abbrev g2r12
    : Root .G2 := g2Root [0, 1] 1

noncomputable abbrev g2r13
    : Root .G2 := g2Root [1] 0

noncomputable abbrev g2r23
    : Root .G2 := g2Root [1, 0, 1] 0

variable {K : Type} [Field K]

theorem commute_g2r23_g2r12
    (x y : Multiplicative K) :
    Commute (rootHom g2r23 x) (rootHom g2r12 y) :=
  commute_rootHom_of_pairCheck pairCheck_g2.1 x y

theorem commute_g2r23_g2r13
    (x y : Multiplicative K) :
    Commute (rootHom g2r23 x) (rootHom g2r13 y) :=
  commute_rootHom_of_pairCheck pairCheck_g2.2.1 x y

theorem commute_g2r12_g2r13
    (x y : Multiplicative K) :
    Commute (rootHom g2r12 x) (rootHom g2r13 y) :=
  commute_rootHom_of_pairCheck pairCheck_g2.2.2 x y

@[expose] noncomputable def g2RootProd :
    Multiplicative K × (Multiplicative K × Multiplicative K) →* adjointGroup .G2 K :=
  (rootHom g2r13).noncommCoprod
    ((rootHom g2r12).noncommCoprod (rootHom g2r23) fun x y => (commute_g2r23_g2r12 y x).symm)
    fun x yz => by
      change Commute _ (rootHom g2r12 yz.1 * rootHom g2r23 yz.2)
      exact ((commute_g2r12_g2r13 yz.1 x).symm).mul_right (commute_g2r23_g2r13 yz.2 x).symm

theorem g2RootProd_apply
    (a b c : Multiplicative K) :
    g2RootProd (a, b, c) = rootHom g2r13 a * (rootHom g2r12 b * rootHom g2r23 c) := rfl

variable [Finite K]

theorem g2RootProd_injective :
    Function.Injective (g2RootProd (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a, b, c⟩ h
  rw [MonoidHom.mem_ker, g2RootProd_apply] at h
  have hy := eq_of_reverse_prod_eq (K := K) g2LongWord isReduced_G2_alternating
    [1, 1, rootHom g2r23 c, rootHom g2r12 b, rootHom g2r13 a, 1] [1, 1, 1, 1, 1, 1]
    (by
      rw [wordRoots_g2LongWord]
      refine .cons (one_mem _) (.cons (one_mem _) (.cons ?_ (.cons ?_ (.cons ?_
        (.cons (one_mem _) .nil)))))
      all_goals exact (rootOperatorFamily _).eltElement_mem_rootSubgroup _ _)
    (by
      rw [wordRoots_g2LongWord]
      exact .cons (one_mem _) (.cons (one_mem _) (.cons (one_mem _) (.cons (one_mem _)
        (.cons (one_mem _) (.cons (one_mem _) .nil))))))
    (by simpa [mul_assoc] using h)
  simp only [List.cons.injEq] at hy
  obtain ⟨-, -, hc, hb, ha, -⟩ := hy
  have key : ∀ (β : Root .G2) (x : Multiplicative K), rootHom β x = 1 → x = 1 :=
    fun β x hx => rootHom_injective β (hx.trans (map_one _).symm)
  rw [Subgroup.mem_bot, Prod.mk_eq_one, Prod.mk_eq_one]
  exact ⟨key _ _ ha, key _ _ hb, key _ _ hc⟩

theorem three_mul_le_pRank_G2
    {p f : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) : 3 * f ≤ pRank p (⊤ : Subgroup (adjointGroup .G2 K)) := by
  refine le_pRank_of_injective hp.out.one_lt (fun x y => mul_comm x y) (fun x => ?_) ?_
    g2RootProd g2RootProd_injective le_top
  · have hx : ∀ z : Multiplicative K, z ^ p = 1 := fun z => by
      change Multiplicative.ofAdd (p • Multiplicative.toAdd z) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    exact Prod.ext (hx _) (Prod.ext (hx _) (hx _))
  · rw [Nat.card_prod, Nat.card_prod,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK]
    ring

end CFSG.LieType.Chevalley
