module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentrePerm
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA1
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs (kac_facts
  orbit_ne_of_rank_one_quasisimple)
open CFSG.Timmesfeld (card_statedClassicalModel_two)


theorem card_centerQuot_twE6Line_of_dim28 {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ}
    (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) (hdim : twE6MatFixDim K σ h = 28)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 13685760 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have hq2 : D.S.D.q = 2 := D.hSq.trans D.hqe.symm
  have he : D.e = 1 := by
    have h1 := D.hqe
    rw [hchar] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans (pow_one 2).symm)
  have h22 : (kernelRoots (rootCharHom D.a)).ncard = 22 := by
    have := D.hker
    omega
  have hfin : (kernelRoots (rootCharHom D.a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  obtain ⟨i, hqi, hJi⟩ := D.exists_rationalComponent hJ
  have hJR : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card
      (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
        Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) :=
    let e := (J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi)
    Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv
  obtain ⟨m, hm, v, ψ₀, σ₀, hψ₀, hn₀, hΨ₀, -, hS1⟩ :=
    KSConn.conn_class_data D.hL3 D.hap (Or.inl h22) i
  have hψ := hψ₀.transport v
  have hnorm : ∀ x y, x ≠ y → iform (v • σ₀ x y) (v • σ₀ x y) = 2 := fun x y hxy => by
    rw [CFSG.LieType.Chevalley.iform_smul]
    exact hn₀ x y hxy
  have hΨ : componentRoots (rootCharHom D.a) i = frameRoots (fun x y => v • σ₀ x y) := by
    rw [hΨ₀, IsSLFrame.frameRoots_smul]
  have hle := Set.ncard_le_ncard (fun γ hγ => hγ.1 : componentRoots (rootCharHom D.a) i ⊆
    kernelRoots (rootCharHom D.a)) hfin
  rcases hm with rfl | rfl | rfl
  ·
    have h2 := (hS1 rfl).2.1
    have F := kac_facts D.hL3 D.hap
    obtain ⟨k', hk'⟩ := outer_exists_image_component D.S D.hT i
    have hn : (componentRoots (rootCharHom D.a) k').ncard =
        (componentRoots (rootCharHom D.a) i).ncard := by
      rw [← hk', Set.ncard_image_of_injective _ D.S.ρ.injective]
    have hstab : (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom D.a) i =
        componentRoots (rootCharHom D.a) i := by
      rw [hk', F.one k' i (hn.trans h2) h2]
    exact absurd hstab
      (orbit_ne_of_rank_one_quasisimple D.S hq2 D.hT i (F.rank_one i h2) h2 hqi)
  ·
    obtain ⟨t, ht, Fr, hFr, hΦ0⟩ := D.hS
    obtain rfl : t = .E6 := by
      cases t
      · rfl
      · exact absurd ht (by decide)
    have hΦ : D.S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr :=
      MonoidHom.ext fun g => (hΦ0 g).trans rfl
    have h3q : 3 ∣ D.S.D.q + 1 := by rw [hq2]
    obtain ⟨u, hu, hρ⟩ := KSConn.exists_rho_neg_weyl_of_conn D.S hFr hΦ D.hT D.hap h3q
      (by rw [h22]; simp)
    obtain ⟨π, hπ1⟩ := KSConn.exists_unitary_perm_of_rho_eq_neg i hψ hnorm hΨ D.S.ρ hu hρ
    have hstab : ∀ γ ∈ componentRoots (rootCharHom D.a) i,
        D.S.ρ γ ∈ componentRoots (rootCharHom D.a) i := by
      intro γ hγ
      rw [hΨ] at hγ ⊢
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      exact ⟨π y, π x, fun hyx => hxy (π.injective hyx).symm, hπ1 x y hxy⟩
    have hfini : (componentRoots (rootCharHom D.a) i).Finite :=
      (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
    have hs1 := componentOrbitLength_eq_one hfini hstab
    have hπ : ∀ x y, x ≠ y → (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength D.S.ρ
        (componentRoots (rootCharHom D.a) i)] (v • σ₀ x y) = v • σ₀ (π y) (π x) :=
      fun x y hxy => by
        rw [hs1, Function.iterate_one]
        exact hπ1 x y hxy
    have hmodel := KSExact.rationalComponent_suN_model D.S D.hT i (ν := 4 + 1) (by norm_num) hψ
      hΨ π hπ D.hℓ D.hchar D.he D.hSq (by simp)
    rw [hs1, Nat.mul_one, hchar, he] at hmodel
    exact hJR.trans (((card_statedClassicalModel_two hmodel).2.1 rfl).trans (by decide))
  ·
    have hc := kd147c_frameRoots_ncard hψ one_ne_zero
      fun x y hxy => (hnorm x y hxy).trans (mul_one 2).symm
    rw [← hΨ] at hc
    omega

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
