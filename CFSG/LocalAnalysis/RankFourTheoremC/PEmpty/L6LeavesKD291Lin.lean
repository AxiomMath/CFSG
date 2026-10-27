module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Core
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Cyc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniFam
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_linear l212in_projectiveSLEquivStated
  exists_cover_linear l212in_descend l212in_descend_apply odC l212in_scalar_comm)

section Linear

variable {n : ℕ} {K : Type} [Field K]

theorem linear_compat {Y : Type} [Group Y] (L : Subgroup Y) [L.Normal] {x : Y}
    (e : ↥L ⧸ center ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL n K))
    (B ŷ : GL (Fin n) K) (hŷ : ∀ M : GL (Fin n) K, ŷ * M * ŷ⁻¹ = B * M * B⁻¹)
    (hB : conjAut n K B =
      l212in_descend (e.trans (l212in_projectiveSLEquivStated n K).symm) (odC L x)) :
    ∀ (g h : ↥L) (A B₀ : ↥(CFSG.Open.StatedSL n K)), x * (g : Y) * x⁻¹ = (h : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B₀ : GL (Fin n) K) = ŷ * (A : GL (Fin n) K) * ŷ⁻¹ →
      e (QuotientGroup.mk h) = QuotientGroup.mk B₀ := by
  intro g h A B₀ hxg heA hB₀
  set e' := e.trans (l212in_projectiveSLEquivStated n K).symm with he'
  have hh : odC L x g = h := Subtype.ext (by rw [odC, MulAut.conjNormal_apply]; exact hxg)
  obtain ⟨s, rfl⟩ :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).surjective A
  have h1 : e' (QuotientGroup.mk g) = proj n K s := by
    show (l212in_projectiveSLEquivStated n K).symm (e (QuotientGroup.mk g)) = _
    rw [heA, MulEquiv.symm_apply_eq]
    rfl
  have h2 : e' (QuotientGroup.mk h) = proj n K (slConjugation n K B s) := by
    rw [← hh, ← l212in_descend_apply e' (odC L x) g, ← hB, h1, conjAut_proj]
  have h3 : e (QuotientGroup.mk h) = QuotientGroup.mk
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K (slConjugation n K B s)) := by
    have h4 := congrArg (l212in_projectiveSLEquivStated n K) h2
    rw [he'] at h4
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h4
    exact h4.trans (by rfl)
  rw [h3]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  have h5 : (B₀ : GL (Fin n) K) = B *
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K s :
        ↥(CFSG.Open.StatedSL n K)) : GL (Fin n) K) * B⁻¹ := by
    rw [hB₀, hŷ]
  rw [h5]
  simp only [Units.val_mul, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
    coe_slConjugation]

theorem scalar_mul_conj (d : Kˣ) (B M : GL (Fin n) K) :
    (GeneralLinearGroup.scalar (Fin n) d * B) * M * (GeneralLinearGroup.scalar (Fin n) d * B)⁻¹ =
      B * M * B⁻¹ := by
  have h := l212in_scalar_comm (B * M * B⁻¹) d
  calc (GeneralLinearGroup.scalar (Fin n) d * B) * M *
        (GeneralLinearGroup.scalar (Fin n) d * B)⁻¹
      = GeneralLinearGroup.scalar (Fin n) d * (B * M * B⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) d)⁻¹ := by group
    _ = B * M * B⁻¹ := by rw [← h, mul_inv_cancel_right]

variable [Finite K]

theorem linear_model (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} [hpp : Fact p.Prime]
    (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZp : IsPGroup p (center ↥L))
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hpn : p ∣ n) (hpK : p ∣ Nat.card K - 1)
    (e : ↥L ⧸ center ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL n K)) :
    LinUniModelLin p x L := by
  have hp : p.Prime := hpp.out
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  let e' : ↥L ⧸ center ↥L ≃* projectiveSL n K :=
    e.trans (l212in_projectiveSLEquivStated n K).symm
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_linear hp hp5 hGA hq hZp (by omega) e'
  have hF := odFamily_linear hp hp5 hpn hn0 hpK
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hcZ : ∀ w ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range,
      ∀ B : GL (Fin n) K,
      (fun B => (slConjugation n K B).toMonoidHom) (w * B) =
        (fun B => (slConjugation n K B).toMonoidHom) B := by
    intro w hw B
    obtain ⟨u, rfl⟩ := hw
    refine MonoidHom.ext fun g => ?_
    show slConjugation n K (GeneralLinearGroup.scalar (Fin n) u * B) g = slConjugation n K B g
    rw [map_mul, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar,
      one_mul]
  have htorus : ∀ B : GL (Fin n) K, B ^ p = 1 →
      ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* SpecialLinearGroup (Fin n) K,
        Function.Injective ((proj n K).comp f) ∧ ∀ a, slConjugation n K B (f a) = f a :=
    fun B hB => I291LinUni.linear_torus hp hn5 hpK B hB
  have hnp : n = p :=
    I291LinUni.n_eq_p_of_cover (p := p) hp5 hpn hn0 L hperf hx hx2 hperfSL (proj n K)
      (fun B => (slConjugation n K B).toMonoidHom) (conjAut n K)
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range hF.central hF.comm_mem
      (fun B h => (hF.ker_eq B).1 h) e' φ hφπ (fun B s => (conjAut_proj B s).symm) hcZ htorus
      (fun hn B hBZ hnp => I291LinUni.linear_mono hp hpK hn B hBZ hnp)
  obtain ⟨B, hB, hBZ, hBnp⟩ := exists_B_of_cover hp5 L hperf hx hx2 hperfSL (proj n K)
    (fun B => (slConjugation n K B).toMonoidHom) (conjAut n K)
    (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range hF.central hF.comm_mem
    (fun B h => (hF.ker_eq B).1 h) e' φ hφπ (fun B s => (conjAut_proj B s).symm) hcZ htorus
  obtain ⟨c, hc⟩ := hBZ
  have hcnp : ∀ b : Kˣ, b ^ p ≠ c := by
    intro b hb
    refine hBnp (GeneralLinearGroup.scalar (Fin n) b) ⟨b, rfl⟩ ?_
    rw [← hc, ← map_pow, hb]
  have hfac : (orderOf c).factorization p = (Nat.card K - 1).factorization p := by
    rw [factorization_orderOf_eq_of_not_pow hp hcnp, Nat.card_units]
  obtain ⟨d, -, hd⟩ := exists_pow_mul_orderOf_eq hp c
  subst hnp
  refine ⟨K, inferInstance, inferInstance, e, GeneralLinearGroup.scalar (Fin n) d * B,
    d ^ n * c, hpK, ?_, ?_, ?_⟩
  · rw [(Commute.symm (l212in_scalar_comm B d)).mul_pow, ← hc, ← map_pow, ← map_mul]
  · rw [hd, hfac]
  · exact linear_compat L e B _ (scalar_mul_conj d B) hB

end Linear

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
