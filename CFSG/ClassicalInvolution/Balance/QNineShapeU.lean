module

public import CFSG.ClassicalInvolution.Balance.QNineLocal

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Phan (Su)
open scoped MatrixGroups commutatorElement

section Unitary

variable {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ} [Fact p.Prime] [CharP K₀ p]

theorem exists_unitaryBlockStandardPair_rootSU2_map (hK₀ : Nat.card K₀ = (p ^ f) ^ 2) {n : ℕ}
    (hn : 3 ≤ n) {X : Type} [Group X] (ψ : Su K₀ p f n →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Su K₀ p f n)) :
    ∃ V W : Subgroup X, Phan.UnitaryBlockStandardPair K₀ p f W
      ((rootSU2 K₀ p f (by omega : 2 ≤ n)).map ψ) V := by
  obtain ⟨θ, hker, hθ⟩ : ∃ θ : Su K₀ p f 3 →* X, θ.ker ≤ Subgroup.center (Su K₀ p f 3) ∧
      (Phan.B12 K₀ p f).map θ = (rootSU2 K₀ p f (by omega : 2 ≤ n)).map ψ := by
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · refine ⟨ψ, hψ, ?_⟩
      rw [Phan.B12, rootSU2, Phan.embSUid_two_eq_blockEmb]
    · have h3 : 0 + 3 ≤ n := by omega
      refine ⟨ψ.comp (Phan.blockEmb K₀ p f n 3 0 h3), fun x hx => ?_, ?_⟩
      · rw [Phan.eq_one_of_blockEmb_mem_center hK₀ h3 hlt hn (hψ hx)]
        exact one_mem _
      · have e : (Phan.blockEmb K₀ p f n 3 0 h3).comp (Phan.blockEmb K₀ p f 3 2 0 (by omega)) =
            Phan.blockEmb K₀ p f n 2 0 (by omega) := Phan.blockEmb_comp h3 (by omega)
        rw [Phan.B12, Phan.embSUid_two_eq_blockEmb, rootSU2, ← Subgroup.map_map,
          MonoidHom.map_range, e]
  refine ⟨(Phan.B23 K₀ p f).map θ, θ.range, θ, 1, rfl, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [SymplecticPairs.map_conj_one, hθ]
  · rw [SymplecticPairs.map_conj_one]

end Unitary

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_member_leviBlockImage_of_psu (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card)
    (ht : D.tag i = .PSU) {n : ℕ} (hr : D.rank i = n) (hn : 3 ≤ n) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨ψ, hker, -, hfund⟩ := exists_psu_hom hp2 D i ht hr (by omega : 2 ≤ n)
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hRΦ
  refine ⟨L, hL, ?_⟩
  obtain ⟨R', hR', hRR'⟩ := (hfund (R.map (D.hom i))).mp ⟨R, hR, rfl⟩
  obtain ⟨g, rfl⟩ := (mem_longRootSetU_iff (by omega : 2 ≤ n)).mp hR'
  rw [hLR, hRR', Subgroup.map_map]
  have hf := ne_zero_of_five_le_pow hq
  obtain ⟨V, W, hVW⟩ := exists_unitaryBlockStandardPair_rootSU2_map
    (CFSG.LieType.Universal.card_galoisField_two_mul p f (Nat.one_le_iff_ne_zero.mpr hf)) hn
    (ψ.comp (MulAut.conj g).toMonoidHom) (WeakCT.ker_comp_mulEquiv_le_center hker _)
  exact Or.inr (Or.inl ⟨V, W, hVW⟩)

end Component

end CFSG.ClassicalInvolution.Balance
