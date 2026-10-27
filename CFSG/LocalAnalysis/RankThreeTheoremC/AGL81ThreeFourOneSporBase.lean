module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PlaneKill
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.HardMathSupport.Dickson.I271 (NoSig)

private theorem coprime_card_of_isPGroup_three {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {W : Subgroup G} (hW : IsPGroup 3 W) :
    Nat.Coprime p (Nat.card W) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_three).2 hp3)

theorem signalizerThreeAt_of_model_noSig {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {X : Type*}
    [Group X] {M : Type} [Group M] [Finite M] (hM : Nonempty (M ≃* X)) {B₀ : Subgroup M}
    (hB₀ : IsPGroup p B₀) (h : NoSig p (B₀.map (MulAut.conj : M →* MulAut M))) :
    SignalizerThreeAt p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro K _ _ ⟨e⟩ T W hW hTW
  obtain ⟨eM⟩ := hM
  obtain ⟨T₀, hBT₀⟩ := hB₀.exists_le_sylow
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (e.trans eM.symm) T₀.isPGroup'
    T₀.not_dvd_index T
  set ψ : MulAut K ≃* MulAut M := MulAut.congr Φ.symm with hψ
  have hψc : ∀ r : M, ψ (MulAut.conj (Φ r)) = MulAut.conj r := by
    intro r
    ext a
    simp [hψ, MulAut.conj_apply]
  refine (Subgroup.map_eq_bot_iff_of_injective (f := ψ.toMonoidHom) W ψ.injective).1
    (h _ (coprime_card_of_isPGroup_three hp hp3 (hW.map _)) ?_)
  rintro _ ⟨r, hr, rfl⟩
  have hrT : Φ r ∈ (T : Subgroup K) := by
    rw [hΦ]
    exact ⟨r, hBT₀ hr, rfl⟩
  have hN : MulAut.conj (Φ r) ∈ Subgroup.normalizer (W : Set (MulAut K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hTW _ hrT w, fun hw => ?_⟩
    have := hTW _ (inv_mem hrT) _ hw
    simpa [map_inv, mul_assoc] using this
  rw [← Subgroup.map_equiv_normalizer_eq, ← hψc r]
  exact ⟨_, hN, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
