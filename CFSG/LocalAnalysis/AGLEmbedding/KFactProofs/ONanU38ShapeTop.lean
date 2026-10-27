module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Model
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38GenSound

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open scoped Matrix

theorem range_le_weakCore_of_repSys_top {X : Type*} [Group X] [Finite X] (R : RepSys X)
    (ι : SU →* X) (d : CheckData) (gd : GenData) (hE : checkE R.sc R.valid d = true)
    (hG : ∀ k < 2, checkG R.sc R.valid d k = true) (htop : Subgroup.closure (genSet gd) = ⊤)
    (hsz : gd.gens.size = 2) (hcorr : ∀ k < 2, d.g.getD k oneP3 = (gd.gens.getD k #[], 0))
    (hrep : ∀ k < 2, ∀ g : SU,
      ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = toMat3 (gd.gens.getD k #[]) →
        R.Rep (gd.gens.getD k #[], 0) (ι g)) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      ι.range ≤ CFSG.Open.GLBWeakCore 3 E := by
  obtain ⟨E, hEab, hEc, hEk⟩ := weakCore_of_check R d hE hG
  refine ⟨E, hEab, hEc, ?_⟩
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨k, hk, hgk⟩, rfl⟩
  have hk2 : k < 2 := hsz ▸ hk
  exact hEk k hk2 (ι g) (by rw [hcorr k hk2]; exact hrep k hk2 g hgk)

theorem range_le_weakCore_top {X : Type*} [Group X] [Finite X] (M : Model X) (d : CheckData)
    (gd : GenData) (hE : checkE M.repSys.sc M.repSys.valid d = true)
    (hG : ∀ k < 2, checkG M.repSys.sc M.repSys.valid d k = true)
    (htop : Subgroup.closure (genSet gd) = ⊤) (hsz : gd.gens.size = 2)
    (hsz9 : ∀ k < 2, (gd.gens.getD k #[]).size = 9)
    (hcorr : ∀ k < 2, d.g.getD k oneP3 = (gd.gens.getD k #[], 0)) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      M.ι.range ≤ CFSG.Open.GLBWeakCore 3 E := by
  refine range_le_weakCore_of_repSys_top M.repSys M.ι d gd hE hG htop hsz hcorr ?_
  intro k hk g hgk
  have hrep : M.Rep (gd.gens.getD k #[], 0) (M.ι g * M.x ^ 0) :=
    ⟨hsz9 k hk, by norm_num, g, hgk.symm, rfl⟩
  rw [pow_zero, mul_one] at hrep
  exact hrep

end CFSG.AGLEmbedding.ChevOuter.U38
