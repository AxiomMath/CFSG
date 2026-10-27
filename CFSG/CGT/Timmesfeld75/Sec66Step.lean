module

public import CFSG.CGT.Timmesfeld75.Sec66Build
public import CFSG.CGT.Timmesfeld75.Sec66Plane

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec66A6Free : Prop :=
  Lemma215Stmt → Lemma26Input → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → SimpleCaseUpTo (Nat.card G) →
    ∀ (U Tb P : Subgroup G) (y y' : G) (q : ℕ), Sec66Cfg U Tb P y y' q →
      ¬ Nonempty (jQuot ↥(U ⊔ Tb ⊔ P) ⧸ Subgroup.center (jQuot ↥(U ⊔ Tb ⊔ P)) ≃*
        alternatingGroup (Fin 6))

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {m : ℕ}

theorem Sec6Ctx.sec66_three_step (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hA6 : Sec66A6Free)
    (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m)
    {x y g : G} (hx : x ∈ T) (hx1 : x ≠ 1) (hyD : y ∈ classD T) (h4 : orderOf (x * y) = 4)
    (hyy : y * y = 1) (hT' : conjSubgroup y T ≠ T) (hg : g ∈ T ⊔ conjSubgroup y T)
    (hfix : conjSubgroup y (conjSubgroup g T) = conjSubgroup g T)
    (hyS : y ∉ conjSubgroup g T) : (x * y) ^ 2 ∈ classD T := by
  rcases hc.sec66_build h62 h63 hx hx1 hyD h4 hyy hT' hg hfix hyS with h | ⟨Tb, P, y', cfg, hxy⟩
  · exact h
  · have := hc.hy.simple
    obtain ⟨j, -, hj⟩ := cfg.exists_conj_mem h215 h26 hc.hy.nonab hc.hy.ind
      (hA6 h215 h26 G hc.hy.nonab hc.hy.ind _ _ _ _ _ _ cfg)
    rw [hxy]
    rw [conjSubgroup_conjSubgroup] at hj
    exact mem_classD_of_mem_conjSubgroup hj cfg.mul_ne_one

end CFSG.CGT.Timmesfeld75
