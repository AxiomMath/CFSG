module

public import CFSG.GroupTheory.GroupAction.PerfectCommuting
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.RepresentationTheory.SL2SplitTorusSpan

public section

namespace CFSG

open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

universe u v

variable {F : Type v} [Field F]

theorem orderOf_sl2Diag_eq (lam : Fˣ) : orderOf (sl2Diag F lam) = orderOf lam := by
  let f : Fˣ →* SL(2, F) :=
    { toFun := sl2Diag F
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_mul' := fun a b => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm] }
  have hf : Function.Injective f := fun a b h => Units.ext (by
    simpa [f] using congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h)
  exact orderOf_injective f hf lam

theorem closure_translates_fixedPoints_sl2Diag_eq_top [Fintype F] [CharP F 2] (lam : Fˣ)
    (V : Type u) [Group V] [Finite V] [MulDistribMulAction SL(2, F) V] (r : ℕ) (hr : r.Prime)
    (hV : IsElementaryAbelian r V) (hVo : Odd (Nat.card V))
    (hVc : Nat.Coprime (Nat.card (Subgroup.zpowers (sl2Diag F lam))) (Nat.card V)) :
    Subgroup.closure (⋃ g : SL(2, F), (fun v => g • v) ''
      {v : V | ∀ t ∈ Subgroup.zpowers (sl2Diag F lam), (t : SL(2, F)) • v = v}) = ⊤ := by
  refine closure_translates_fixedPoints_eq_top_of_zmod _
    (fun ℓ _ hℓ2 hTℓ W _ _ _ _ => ?_) V r hr hV hVo hVc
  have : SMulCommClass SL(2, F) (ZMod ℓ) W :=
    ⟨fun g c w => ZMod.map_smul (DistribSMul.toAddMonoidHom W g) c w⟩
  have hℓ : ℓ.Prime := Fact.out
  have hk2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod ℓ) ℓ] at h2
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
  have hkn : (orderOf lam : ZMod ℓ) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ]
    intro hdvd
    rw [Nat.card_zpowers, orderOf_sl2Diag_eq] at hTℓ
    exact hℓ.ne_one (Nat.Coprime.eq_one_of_dvd hTℓ.symm hdvd)
  have hset : ∀ g : SL(2, F), (fun w : W => g • w) ''
      {w : W | ∀ t ∈ Subgroup.zpowers (sl2Diag F lam), (t : SL(2, F)) • w = w} =
      Representation.ofDistribMulAction (ZMod ℓ) SL(2, F) W g ''
        {v | Representation.ofDistribMulAction (ZMod ℓ) SL(2, F) W (sl2Diag F lam) v = v} := by
    intro g
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq, Representation.ofDistribMulAction_apply_apply]
    refine exists_congr fun v => and_congr_left fun _ =>
      ⟨fun hv => hv _ (Subgroup.mem_zpowers _), fun hv t ht => ?_⟩
    exact MulAction.mem_stabilizer_iff.mp
      (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hv) ht)
  rw [Set.iUnion_congr hset]
  exact RepresentationTheory.SL2SplitTorus.span_translates_fixed_eq_top hk2
    (Representation.ofDistribMulAction (ZMod ℓ) SL(2, F) W) hkn

theorem commute_of_perfect_or_pGroup_of_sl2Diag {G : Type u} [Group G] [Fintype F] [CharP F 2]
    (ψ : SL(2, F) →* G) (lam : Fˣ) {N S : Subgroup G} [Finite N]
    (hQN : ψ.range ≤ Subgroup.normalizer (N : Set G)) (hSN : S ≤ Subgroup.normalizer (N : Set G))
    (hQS : ∀ x ∈ ψ.range, ∀ y ∈ S, x * y = y * x)
    (hS : Group.IsPerfect S ∨ ∃ p : ℕ, p.Prime ∧ IsPGroup p S ∧ ¬ p ∣ Nat.card N)
    (hN : Group.IsSolvable N) (hNc : Nat.Coprime (Nat.card N) (2 * orderOf lam))
    (hfix : ∀ s ∈ S, ∀ n ∈ N ⊓ Subgroup.centralizer {ψ (sl2Diag F lam)}, s * n = n * s) :
    ∀ s ∈ S, ∀ n ∈ N, s * n = n * s := by
  classical
  let : MulDistribMulAction ψ.range N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer ψ.range N hQN
  let : MulDistribMulAction SL(2, F) N := MulDistribMulAction.compHom N ψ.rangeRestrict
  let : MulDistribMulAction S N := Subgroup.conjMulDistribMulActionOfLeNormalizer S N hSN
  have hQs : ∀ (g : SL(2, F)) (m : N), ((g • m : N) : G) = ψ g * m * (ψ g)⁻¹ := fun _ _ => rfl
  have hSs : ∀ (x : S) (m : N), ((x • m : N) : G) = x * m * (x : G)⁻¹ := fun _ _ => rfl
  have : SMulCommClass SL(2, F) S N := ⟨fun g x m => by
    apply Subtype.ext
    rw [hQs, hSs, hSs, hQs]
    have hgx : ψ g * x = x * ψ g := hQS (ψ g) ⟨g, rfl⟩ x x.2
    have hgx' : (x : G)⁻¹ * (ψ g)⁻¹ = (ψ g)⁻¹ * (x : G)⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hgx]
    calc ψ g * (x * m * (x : G)⁻¹) * (ψ g)⁻¹ = (ψ g * x) * m * ((x : G)⁻¹ * (ψ g)⁻¹) := by
          group
      _ = (x * ψ g) * m * ((ψ g)⁻¹ * (x : G)⁻¹) := by rw [hgx, hgx']
      _ = (x : G) * (ψ g * m * (ψ g)⁻¹) * (x : G)⁻¹ := by group⟩
  have hT : Nat.card (Subgroup.zpowers (sl2Diag F lam)) = orderOf lam := by
    rw [Nat.card_zpowers, orderOf_sl2Diag_eq]
  have hmain := smul_eq_self_of_perfect_or_pGroup_of_fixedPoints (N := N) (Q := SL(2, F)) (S := S) hS hN
    (Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hNc))
    (Subgroup.zpowers (sl2Diag F lam))
    (by rw [hT]; exact (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ 2) hNc).symm)
    (fun V _ _ _ r hr hV hVo hVc =>
      closure_translates_fixedPoints_sl2Diag_eq_top lam V r hr hV hVo hVc)
    (fun m hm x => by
      apply Subtype.ext
      rw [hSs]
      have hc : ψ (sl2Diag F lam) * m * (ψ (sl2Diag F lam))⁻¹ = m := by
        rw [← hQs]
        exact congrArg Subtype.val (hm _ (Subgroup.mem_zpowers _))
      have hmc : (m : G) ∈ N ⊓ Subgroup.centralizer {ψ (sl2Diag F lam)} :=
        ⟨m.2, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc).symm⟩
      rw [hfix x x.2 m hmc, mul_inv_cancel_right])
  intro s hs n hn
  have h := congrArg Subtype.val (hmain ⟨s, hs⟩ ⟨n, hn⟩)
  rw [hSs] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem commute_of_perfect_or_pGroup_of_sl2Diag_of_le {G : Type u} [Group G] [Finite G]
    [Fintype F] [CharP F 2] {p : ℕ} {J Q₁ Q₂ : Subgroup G} {e₁ : G} (ψ : SL(2, F) →* G)
    (hψ : ψ.range ≤ Q₁) (lam : Fˣ) (hlam : orderOf lam = p) (t : SL(2, F))
    (ht : IsConj t (sl2Diag F lam)) (he₁ : ψ t = e₁) (hQ₁J : Q₁ ≤ J) (hQ₂J : Q₂ ≤ J)
    (hQ₁₂ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x)
    (hQ₂ : Group.IsPerfect Q₂ ∨ p.Prime ∧ IsPGroup p Q₂) :
    ∀ N : Subgroup G, Group.IsSolvable ↥N → Nat.Coprime (Nat.card N) (2 * p) →
      J ≤ Subgroup.normalizer (N : Set G) →
      (∀ s ∈ Q₂, ∀ n ∈ N ⊓ Subgroup.centralizer {e₁}, s * n = n * s) →
      ∀ s ∈ Q₂, ∀ n ∈ N, s * n = n * s := by
  intro N hN hNc hJN hfix
  obtain ⟨c, hc⟩ := isConj_iff.mp ht
  set ψ' : SL(2, F) →* G := ψ.comp (MulAut.conj c⁻¹).toMonoidHom with hψ'
  have hψ'e : ψ' (sl2Diag F lam) = e₁ := by
    rw [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hc, ← he₁]
    congr 1
    group
  have hψ'Q : ψ'.range ≤ Q₁ := by
    rw [hψ', MonoidHom.range_comp]
    exact (Subgroup.map_le_range _ _).trans hψ
  subst hlam
  rw [← hψ'e] at hfix
  refine commute_of_perfect_or_pGroup_of_sl2Diag ψ' lam ((hψ'Q.trans hQ₁J).trans hJN)
    (hQ₂J.trans hJN) (fun x hx y hy => hQ₁₂ x (hψ'Q hx) y hy) ?_ hN hNc hfix
  rcases hQ₂ with hQ₂ | ⟨hp, hQ₂p⟩
  · exact Or.inl hQ₂
  · refine Or.inr ⟨orderOf lam, hp, hQ₂p, fun hdvd => hp.one_lt.ne' ?_⟩
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ 2) hNc).symm hdvd

theorem commute_of_perfect_of_sl2Diag_of_le {G : Type u} [Group G] [Finite G] [Fintype F]
    [CharP F 2] {p : ℕ} {J Q₁ Q₂ : Subgroup G} {e₁ : G} (ψ : SL(2, F) →* G)
    (hψ : ψ.range ≤ Q₁) (lam : Fˣ) (hlam : orderOf lam = p) (t : SL(2, F))
    (ht : IsConj t (sl2Diag F lam)) (he₁ : ψ t = e₁) (hQ₁J : Q₁ ≤ J) (hQ₂J : Q₂ ≤ J)
    (hQ₁₂ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) (hQ₂ : Group.IsPerfect Q₂) :
    ∀ N : Subgroup G, Group.IsSolvable ↥N → Nat.Coprime (Nat.card N) (2 * p) →
      J ≤ Subgroup.normalizer (N : Set G) →
      (∀ s ∈ Q₂, ∀ n ∈ N ⊓ Subgroup.centralizer {e₁}, s * n = n * s) →
      ∀ s ∈ Q₂, ∀ n ∈ N, s * n = n * s :=
  commute_of_perfect_or_pGroup_of_sl2Diag_of_le ψ hψ lam hlam t ht he₁ hQ₁J hQ₂J hQ₁₂ (Or.inl hQ₂)

end CFSG

end
