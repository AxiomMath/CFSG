module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Out
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Exit
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3U3
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic Matrix
open QuaternionGroup CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem exitIdent_l3Ne3 : ExitIdent TA3.SmallL3Ne3 := by
  intro Y _ _ _ hnab hPF R S t hD hc
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hPF
  have hL : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSL 3 p f := Or.inl ⟨by decide, hm⟩
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC := Nobq.centralizer_genFittingFStar_eq_bot hnab
  set N := genFittingFStar Y with hN
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  let e : ↥N ≃* projectiveSL 3 K :=
    (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  have hoddK : Odd (Nat.card K) := hK ▸ hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  set ι : Y →* MulAut (projectiveSL 3 K) := transConj N e with hι
  have hιapp : ∀ (y : Y) (n : ↥N), ι y (e n) = e (MulAut.conjNormal y n) := fun y n => by
    rw [hι, transConj_apply, MulEquiv.symm_apply_apply]
  have hιN : ∀ y, ι y ∈ inner (projectiveSL 3 K) ↔ y ∈ N := transConj_mem_inner_iff e hC
  obtain ⟨φ, -, hφR, hφt⟩ := datum_exists_q8 hD
  have htN : t ∈ N := by
    have hq : (a 1 : QuaternionGroup 2) * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ = a 1 ^ 2 := by decide
    have ht' : t = φ (a 1) * φ (xa 0) * (φ (a 1))⁻¹ * (φ (xa 0))⁻¹ := by
      rw [← hφt, ← map_pow, ← hq, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hD' : ι t ∈ linearAutGroup 3 K := by
      rw [ht', map_mul ι, map_mul ι, map_mul ι, map_inv ι, map_inv ι]
      exact commutator_mem_linearAutGroup le_rfl _ _
    have ht2 : t ^ 2 = 1 := by rw [← hD.order, pow_orderOf_eq_one]
    have h2 : ι t ^ 2 ^ 1 = 1 := by rw [← map_pow, pow_one, ht2, map_one]
    exact (hιN t).mp (mem_inner_of_pow hD' h2)
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ := Q5L3.exists_frame hoddK e htN hD.order
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hoddK (by omega) slPartTopEquiv
  have hfix : ∀ g ∈ R, ∀ B : SL(2, K),
      ι g (proj 3 K ((blkP Q).comp SpecialLinearGroup.toGL B)) =
        proj 3 K ((blkP Q).comp SpecialLinearGroup.toGL B) := by
    intro g hg B
    let x : ↥N := e.symm (proj 3 K (blkP Q (SpecialLinearGroup.toGL B)))
    have hxJ : (x : Y) ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π :=
      ⟨⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩,
        mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B), hπ _⟩
    have hgx : (x : Y) * g = g * x := Subgroup.mem_centralizer_iff.mp (hRJ hg) _ hxJ
    have hconj : MulAut.conjNormal g x = x := Subtype.ext (by
      rw [MulAut.conjNormal_apply, ← hgx, mul_inv_cancel_right])
    have hex : proj 3 K (blkP Q (SpecialLinearGroup.toGL B)) = e x :=
      (MulEquiv.apply_symm_apply e _).symm
    show ι g (proj 3 K (blkP Q (SpecialLinearGroup.toGL B))) =
      proj 3 K (blkP Q (SpecialLinearGroup.toGL B))
    rw [hex, hιapp, hconj]
  have hDof : ∀ g ∈ R, ι g ∈ semilinearAutGroup 3 K → ι g ∈ linearAutGroup 3 K :=
    fun g hg hgE => mem_linearAutGroup_of_fix (by omega) ((blkP Q).comp SpecialLinearGroup.toGL)
      (trace_blkP Q) hgE (hfix g hg)
  obtain ⟨eS⟩ := hc.1
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  let eQ : S₀ ≃* QuaternionGroup 2 :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans eS
  have hS₀R : S₀ ≤ R := Subgroup.map_subtype_le _
  have hsq : ∀ s ∈ S₀, s ^ 2 ∈ N := by
    intro s hs
    have hq : ∀ q : QuaternionGroup 2, q ^ 2 = 1 ∨ q ^ 2 = a 2 := by decide
    have h2 : orderOf ((eQ.symm (a 2) : S₀) : Y) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by decide) (by decide)
    have hta : ((eQ.symm (a 2) : S₀) : Y) = t :=
      hD.eq_of_orderOf_eq_two (hS₀R (eQ.symm (a 2)).2) h2
    have hs' : s ^ 2 = ((eQ.symm ((eQ ⟨s, hs⟩) ^ 2) : S₀) : Y) := by
      rw [map_pow, MulEquiv.symm_apply_apply]
      rfl
    rcases hq (eQ ⟨s, hs⟩) with h | h
    · rw [hs', h, map_one]
      exact N.one_mem
    · rw [hs', h, hta]
      exact htN
  have : Finite (projectiveSL 3 K) := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut (projectiveSL 3 K)) :=
    Finite.of_injective (fun α : MulAut (projectiveSL 3 K) => (α : projectiveSL 3 K → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  set Ω : Y →* Outer (projectiveSL 3 K) := (QuotientGroup.mk' (inner (projectiveSL 3 K))).comp ι
    with hΩ
  set Dbar := ((QuotientGroup.mk' (inner (projectiveSL 3 K))).comp (conjAut 3 K)).range
    with hDbar
  have hker : Ω.ker = N := by
    ext y
    rw [MonoidHom.mem_ker, hΩ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hιN y
  have hDin : ∀ y, ι y ∈ linearAutGroup 3 K → Ω y ∈ Dbar := fun y hy => by
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hy
    exact ⟨A, by rw [MonoidHom.comp_apply, hA]; rfl⟩
  have hD3 : Nat.card Dbar ∣ 3 :=
    (OuterDerived.linear_diagonal_outer (K := K) (n := 3) (by norm_num)).2.trans
      (Nat.gcd_dvd_left 3 _)
  have hcomm : ∀ x y : Outer (projectiveSL 3 K), x * y * x⁻¹ * y⁻¹ ∈ Dbar := by
    intro x y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp (commutator_mem_linearAutGroup le_rfl α β)
    exact ⟨A, by rw [MonoidHom.comp_apply, hA]; rfl⟩
  have hS : ∀ s₁ ∈ S₀, ∀ s₂ ∈ S₀, Ω s₁ ∉ Dbar → Ω s₂ ∉ Dbar → Ω (s₁⁻¹ * s₂) ∈ Dbar := by
    intro s₁ h₁ s₂ h₂ hn₁ hn₂
    have hE₁ : ι s₁ ∉ semilinearAutGroup 3 K := fun h => hn₁ (hDin _ (hDof _ (hS₀R h₁) h))
    have hE₂ : ι s₂ ∉ semilinearAutGroup 3 K := fun h => hn₂ (hDin _ (hDof _ (hS₀R h₂) h))
    have hE₁' : (ι s₁)⁻¹ ∉ semilinearAutGroup 3 K := fun h =>
      hE₁ (by simpa using (semilinearAutGroup 3 K).inv_mem h)
    have h12 := mul_mem_semilinearAutGroup hE₁' hE₂
    rw [← map_inv, ← map_mul] at h12
    exact hDin _ (hDof _ (R.mul_mem (R.inv_mem (hS₀R h₁)) (hS₀R h₂)) h12)
  have hS2 : ∀ s ∈ S₀, Ω (s ^ 2) ∈ Dbar := fun s hs => by
    have h := hsq s hs
    rw [← hker, MonoidHom.mem_ker] at h
    rw [h]
    exact Dbar.one_mem
  have hidx := index_dvd_six_of_hom Ω hker Dbar hD3 hcomm
    (fun M h => hD.eq_top_of_conj hc.2.1 h) hS hS2
  exact Or.inl ⟨p, f, hp, hp2, Or.inr ⟨Or.inl (lieModel_fstarQuot hnab (Or.inl rfl) hL), hidx⟩⟩

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
