module

public import CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
import all CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.RootIrreducible
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSylow

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.SylowNormalizerIrreducible

open scoped MatrixGroups
open CFSG.LinearAlgebra.ProjectiveRootSpaces.RootIrreducible
open CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSylow

theorem isIrreducibleUnder_normalizer_map {G : Type} [Group G] (e : G ≃* G) {P : Subgroup G}
    (h : CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder (Subgroup.normalizer (P : Set G)) P) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
      (Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G) : Set G))
      (P.map e.toMonoidHom) := by
  unfold CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder at *
  obtain ⟨hne, hirr⟩ := h
  refine ⟨?_, ?_⟩
  · intro hb
    exact hne ((Subgroup.map_eq_bot_iff_of_injective P e.injective).mp hb)
  · intro W hW hN
    have hle : W.comap e.toMonoidHom ≤ P := by
      intro w hw
      obtain ⟨q, hq, hqw⟩ := hW hw
      have : q = w := e.injective hqw
      exact this ▸ hq
    have hN' : Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer ((W.comap e.toMonoidHom : Subgroup G) : Set G) := by
      intro x hx
      have h1 : e.toMonoidHom x ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map e.toMonoidHom ⟨x, hx, rfl⟩
      have h2 := hN h1
      exact Subgroup.le_normalizer_comap e.toMonoidHom h2
    have hW' : W = (W.comap e.toMonoidHom).map e.toMonoidHom :=
      (Subgroup.map_comap_eq_self_of_surjective e.surjective W).symm
    rcases hirr _ hle hN' with h0 | h0
    · left; rw [hW', h0]; exact Subgroup.map_bot _
    · right; rw [hW', h0]

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

theorem isIrreducibleUnder_normalizer_sylow (hp : 5 ≤ p) (hn : 1 < n)
    (S : Sylow p PSL(2, GaloisField p n)) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
      (Subgroup.normalizer ((S : Subgroup PSL(2, GaloisField p n)) : Set _))
      (S : Subgroup PSL(2, GaloisField p n)) := by
  obtain ⟨P, hP⟩ := upperSubgroup_isSylow p n hp hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, GaloisField p n) P S
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).mp (by simpa using h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hirr := isIrreducibleUnder_normalizer_map (MulAut.conj g) (P := (P : Subgroup _))
    (by rw [hP]; exact isIrreducibleUnder_normalizer h2)
  have hS : (S : Subgroup PSL(2, GaloisField p n)) =
      (P : Subgroup PSL(2, GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  rw [hS]
  exact hirr

end CFSG.LinearAlgebra.ProjectiveRootSpaces.SylowNormalizerIrreducible
