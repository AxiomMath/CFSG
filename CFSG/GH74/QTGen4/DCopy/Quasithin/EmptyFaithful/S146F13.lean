module

public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

@[expose] def Input14614Sol_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 →
      conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H → Group.IsSolvable ↥(mcOf T)

@[expose] def Input14614Shape_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H → Stage14614At T H p

theorem stage14614_of_named_inputs_F4 (i0 : Input14614Solv) (i1 : Input14614Sol_F4)
    (i2 : Input14614Shape_F4) : Stage14614_F4 := by
  intro G _ _ T M S H PQ p hred hmax
  by_cases hKz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H
  · left
    refine ⟨hKz, fun hp3 r hr hdvd => ?_⟩
    have hsolv := i1 G T M S H PQ p hred hmax hp3 hKz
    exact (i0 G T M S H PQ p hred hmax (mcOf T) (S.le_mcOf hred.isHTM) le_rfl hsolv).1 hp3 r hr hdvd
  · exact i2 G T M S H PQ p hred hmax hKz

end CFSG.Quasithin
