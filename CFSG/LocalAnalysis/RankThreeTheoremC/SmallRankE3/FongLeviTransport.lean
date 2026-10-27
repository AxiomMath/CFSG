module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviPrime

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup

theorem LeviSurj.of_mulEquiv {X : Type} [Group X] {p : ℕ} {P : Subgroup X} {z : X} {L L' : Type}
    [Group L] [Group L'] (h : LeviSurj p P z L) (e : L ≃* L') : LeviSurj p P z L' := by
  obtain ⟨hz, φ, hφs, hφk, hL, hn, hpL⟩ := h
  obtain ⟨a, b, hab⟩ := hn
  refine ⟨hz, e.toMonoidHom.comp φ, e.surjective.comp hφs, ?_,
    (MulEquiv.isSimpleGroup_congr e).mp hL, ⟨e a, e b, ?_⟩, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective φ e.toMonoidHom e.injective]
    exact hφk
  · intro h'
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact h'
  · rw [← Nat.card_congr e.toEquiv]
    exact hpL

theorem LeviSurj.map {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X'] {p : ℕ}
    {P : Subgroup X} {z : X} {L : Type} [Group L] (f : X →* X') (hf : Function.Injective f)
    (h : LeviSurj p P z L) : LeviSurj p (P.map f) (f z) L := by
  obtain ⟨hz, φ, hφs, hφk, hL, hn, hpL⟩ := h
  have hzmem : f z ∈ leviY (P.map f) := by
    rw [leviY_map f P]
    exact Subgroup.mem_map_of_mem f hz
  let ε : ↥(leviY (P.map f)) ≃* ↥(leviY P) :=
    (MulEquiv.subgroupCongr (leviY_map f P)).trans ((leviY P).equivMapOfInjective f hf).symm
  refine ⟨hzmem, φ.comp ε.toMonoidHom, hφs.comp ε.surjective, ?_, hL, hn, hpL⟩
  have hk : (φ.comp ε.toMonoidHom).ker = φ.ker.map ε.symm.toMonoidHom :=
    MonoidHom.ker_comp_mulEquiv φ ε
  have hεi : Function.Injective ε.symm.toMonoidHom := ε.symm.injective
  rw [hk, Subgroup.card_map_of_injective hεi]
  exact hφk

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
