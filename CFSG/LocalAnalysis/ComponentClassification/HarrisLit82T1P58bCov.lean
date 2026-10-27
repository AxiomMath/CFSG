module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCl
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClBasic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

theorem mulAut_congr_conj {S T : Type*} [Group S] [Group T] (θ : S ≃* T) (y : T) :
    MulAut.congr θ (MulAut.conj (θ.symm y)) = MulAut.conj y := by
  ext x
  change θ (θ.symm y * θ.symm x * (θ.symm y)⁻¹) = y * x * y⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

variable {X : Type} [Group X] [Finite X]

theorem false_of_noL2At (hX : IsQuasisimple X) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c t : X} {Q : Subgroup X} (hcfg : Lemma58bConfig X p k c t Q)
    (h : Burgoyne.Cl.NoL2At (MulAut.conj (QuotientGroup.mk' (center X) t))) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at h5
    · exact h
  obtain ⟨-, -, hRv, hRc, N, hN, hNodd, ⟨eN⟩⟩ := exists_psl2_component hX
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hp2 hcfg
  have hfix := autFixed_conj (QuotientGroup.mk' (center X) t)
  exact h (Q.map (QuotientGroup.mk' (center X))) (by rw [hfix]; exact hRv)
    (by rw [hfix]; exact hRc) p k hp2 hk N hNodd ⟨eN⟩

theorem false_of_cover (hX : IsQuasisimple X) (hO : pPrimeCore 2 X = ⊥) {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {c t : X} {Q : Subgroup X} (hcfg : Lemma58bConfig X p k c t Q)
    {G : Type} [Group G] [Finite G]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : G →* E, ∀ x, π (s x) = x)
    (β : G →* X ⧸ center X) (hβ : Function.Surjective β)
    (hlift : ∀ α : G →* X, Function.Surjective α →
      (∀ s, QuotientGroup.mk' (center X) (α s) = β s) → center X = β.ker.map α →
        ∀ g : G, α g = t → Burgoyne.Cl.NoL2At (MulAut.conj (β g))) : False := by
  have : Group.IsPerfect X := hX.1
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  obtain ⟨g, hg⟩ := hαs t
  have h := hlift α hαs hαβ (by rw [← hker, hη]) g hg
  rw [← hαβ, hg] at h
  exact false_of_noL2At hX hp hp2 hcfg h

theorem propBHypII_of_config {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c t : X}
    {Q : Subgroup X} (hcfg : Lemma58bConfig X p k c t Q) : Burgoyne.PropBHypII X c := by
  obtain ⟨hc2, hcZ, ht2, htZ, hQ, hcQ, h5, hSL⟩ := hcfg
  have hpF : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  obtain ⟨e⟩ := nonempty_equiv_galoisField hk hSL
  have hfix := autFixed_conj t
  have hv : orderOf (MulAut.conj t) = 2 := by
    have h2 : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ht2] at h
    apply orderOf_eq_prime
    · rw [← map_pow, h2, map_one]
    · intro h1
      apply htZ
      rw [mem_center_iff]
      intro g
      have h3 : t * g * t⁻¹ = g := by
        have h4 := DFunLike.congr_fun h1 g
        rwa [MulAut.conj_apply, MulAut.one_apply] at h4
      calc g * t = t * g * t⁻¹ * t := by rw [h3]
        _ = t * g := by group
  exact ⟨MulAut.conj t, hv, Q, by rw [hfix]; exact hQ.1,
    by rw [hfix]; exact (isTwoComponentIn_iff hQ.1).mp hQ,
    ⟨p, k, hpF, hp2, Nat.pos_of_ne_zero hk, ⟨e⟩⟩, hcZ, hcQ, hc2⟩

end CFSG.ComponentClassification.HarrisLit.T1.P58b
