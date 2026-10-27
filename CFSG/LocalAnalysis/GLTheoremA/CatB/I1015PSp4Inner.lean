module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Out
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Core
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Inner

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Core
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin

theorem conj_injective_of_center {G : Type} [Group G] (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hcen : k ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut G => φ g) hk
    simp only [MulAut.conj_apply, map_one, MulAut.one_apply] at hg
    exact ((mul_inv_eq_iff_eq_mul).1 hg).symm
  rw [h, Subgroup.mem_bot] at hcen
  exact hcen

theorem center_eq_bot_of_sp4 {G : Type} [Group G] (f : G ≃* StatedSp 2 (GaloisField 2 3)) :
    Subgroup.center G = ⊥ := by
  have hc : Subgroup.center (StatedSp 2 (GaloisField 2 3)) = ⊥ :=
    CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two 2
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_center_iff] at hk
  have hfk : f k ∈ Subgroup.center (StatedSp 2 (GaloisField 2 3)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := f.surjective h
    rw [← map_mul, ← map_mul, hk g]
  rw [hc, Subgroup.mem_bot] at hfk
  exact Subgroup.mem_bot.2 (f.injective (hfk.trans (map_one f).symm))

theorem i1015oneSp4Inner_holds : I1015oneSp4Inner := by
  intro K _ _ hK A hA hinn T hT2 hT0 hinv
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Out.sp4eight_equiv hK
  let f : K ≃* StatedSp 2 (GaloisField 2 3) :=
    e.trans (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.projSpEquiv (GaloisField 2 3)).symm
  have hcK : Subgroup.center K = ⊥ := center_eq_bot_of_sp4 f
  have hconj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_center hcK
  obtain ⟨Ã, hÃdef⟩ : ∃ Ã : Subgroup K, Ã = A.comap (MulAut.conj : K →* MulAut K) := ⟨_, rfl⟩
  have hAle : A ≤ (MulAut.conj : K →* MulAut K).range := fun α hα => hinn α hα
  have hÃmap : Ã.map (MulAut.conj : K →* MulAut K) = A := by
    rw [hÃdef]; exact Subgroup.map_comap_eq_self hAle
  have hÃab : IsElemAbelian 3 Ã := by
    apply isElemAbelian_of_map_injective (MulAut.conj : K →* MulAut K) hconj
    rw [hÃmap]; exact hA
  have hcardÃ : Nat.card A ≤ Nat.card Ã := by
    rw [← hÃmap]
    exact (Subgroup.card_map_of_injective hconj).le
  have hf : Function.Injective f.toMonoidHom := f.injective
  have hEtab : IsElemAbelian 3 (Ã.map f.toMonoidHom) := isElemAbelian_map _ hÃab
  have hEtcard : Nat.card (Ã.map f.toMonoidHom) = Nat.card Ã :=
    Subgroup.card_map_of_injective hf
  have hTt0 : T.map f.toMonoidHom ≠ ⊥ := by
    intro h
    apply hT0
    rw [eq_bot_iff]
    intro t ht
    have hmem : f.toMonoidHom t ∈ T.map f.toMonoidHom := Subgroup.mem_map_of_mem _ ht
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (hf (hmem.trans (map_one _).symm))
  have hTt2 : IsPGroup 2 (T.map f.toMonoidHom) := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    refine ⟨n, Subtype.ext ?_⟩
    show f.toMonoidHom t ^ 2 ^ n = 1
    have hn' : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
    rw [← map_pow, hn', map_one]
  have hNt : ∀ g ∈ Ã.map f.toMonoidHom, ∀ t ∈ T.map f.toMonoidHom,
      g * t * g⁻¹ ∈ T.map f.toMonoidHom := by
    intro g hg t ht
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨t0, ht0, rfl⟩ := Subgroup.mem_map.1 ht
    have hkA : MulAut.conj k ∈ A := by
      rw [hÃdef] at hk
      exact hk
    have hmem := hinv (MulAut.conj k) hkA t0 ht0
    refine Subgroup.mem_map.2 ⟨MulAut.conj k t0, hmem, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hcore := card_le_three_of_normalizes hcard hEtab hTt2 hTt0 hNt
  omega

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Inner
