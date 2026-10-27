module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section Matrix

variable {K : Type} [Field K] [Finite K] {n p : ℕ} [hp : Fact p.Prime]

theorem isMulCommutative_of_isPGroup_GL_matrix (hp2 : Odd p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (hne : n / e < p)
    {P : Subgroup (GL (Fin n) K)} (hP : IsPGroup p P) : IsMulCommutative P := by
  let ψ : GL (Fin n) K ≃* (Module.End K (Fin n → K))ˣ := Matrix.GeneralLinearGroup.toLin
  have h1 : IsPGroup p (P.map ψ.toMonoidHom) := hP.map ψ.toMonoidHom
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  exact isMulCommutative_of_map_injective ψ.toMonoidHom ψ.injective
    (isMulCommutative_of_isPGroup_GL (V := Fin n → K) hp2 hpK he hpe (by rw [hfr]; exact hne) h1)

theorem le_pRank_centralizer_GL_matrix (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) {c : ℕ} (hc : c < p)
    (hcn : c * e ≤ n) {Y : GL (Fin n) K} (hY : Y ^ p = 1) :
    c ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (GL (Fin n) K))) := by
  let ψ : GL (Fin n) K ≃* (Module.End K (Fin n → K))ˣ := Matrix.GeneralLinearGroup.toLin
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have h1 := le_pRank_centralizer_GL (V := Fin n → K) hp5 hpK he hpe hc (by rw [hfr]; exact hcn)
    (u := ψ Y) (by rw [← map_pow, hY, map_one])
  exact h1.trans (pRank_centralizer_of_mulEquiv ψ Y)

end Matrix

section Stated

variable {K : Type} [Field K] [Finite K] {n p : ℕ} [hp : Fact p.Prime]

theorem not_dvd_card_scalars (hn : 0 < n) (hg : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨c, hc⟩ : ((z : StatedSL n K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K := z.2
  have hdet : (Matrix.GeneralLinearGroup.det ((z : StatedSL n K) : GL (Fin n) K) : K) = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL (z : StatedSL n K).2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hcn : c ^ n = 1 := Units.ext (by simpa using hdet)
  have hscal : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) (R := K)) := by
    intro a b hab
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hab
    exact Units.ext (by simpa [Matrix.GeneralLinearGroup.scalar] using this)
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hcp : c ^ p = 1 := by
    apply hscal
    rw [map_pow, map_one, hc]
    exact congrArg (fun w : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) =>
      ((w : StatedSL n K) : GL (Fin n) K)) hzp
  have hc1 : c ≠ 1 := by
    intro h
    apply (hz ▸ (hp.out.one_lt.ne' : p ≠ 1) : orderOf z ≠ 1)
    have : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← hc, h, map_one]
      rfl
    rw [this, orderOf_one]
  have hord : orderOf c = p := orderOf_eq_prime hcp hc1
  apply hg
  refine Nat.dvd_gcd ?_ ?_
  · rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hcn
  · rw [← hord, ← Nat.card_units]
    exact orderOf_dvd_natCard c

theorem isMulCommutative_sylow_statedProj {r : ℕ} [Fact r.Prime]
    (hGL : ∀ P : Subgroup (GL (Fin n) K), IsPGroup r P → IsMulCommutative P)
    (H : Subgroup (GL (Fin n) K)) (R : Sylow r (StatedProj H)) :
    IsMulCommutative (R : Subgroup (StatedProj H)) := by
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective
    (f := QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf H))
    (QuotientGroup.mk'_surjective _) r R
  rw [Sylow.coe_mapSurjective]
  have h1 : IsMulCommutative ((S : Subgroup H).map H.subtype) := hGL _ (S.isPGroup'.map _)
  have h2 : IsMulCommutative (S : Subgroup H) :=
    .of_setLike_mul_comm fun a ha b hb => Subtype.ext
      (setLike_mul_comm (s := (S : Subgroup H).map H.subtype) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  infer_instance

theorem three_le_pRank_centralizer_statedProj_large (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hg : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) {e : ℕ} (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (hlarge : p ≤ n / e)
    (y : StatedProj (StatedSL n K)) (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedSL n K)))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hn5 : 5 * e ≤ n := (Nat.le_div_iff_mul_le he).1 (le_trans hp5 hlarge)
  have hn : 0 < n := by
    have := Nat.mul_pos (by omega : 0 < 5) he
    omega
  have hN := not_dvd_card_scalars hn hg
  obtain ⟨ŷ, hŷp, rfl⟩ := exists_pow_eq_one_lift
    ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) hN y hy
  set Y : GL (Fin n) K := ((ŷ : StatedSL n K) : GL (Fin n) K) with hY
  have hYp : Y ^ p = 1 := by
    have := congrArg (fun w : StatedSL n K => (w : GL (Fin n) K)) hŷp
    simpa using this
  have h4 : 4 ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (GL (Fin n) K))) :=
    le_pRank_centralizer_GL_matrix hp5 hpK he hpe (by omega) (by omega) hYp
  have h3 := pRank_le_pRank_inf_ker_add_one (p := p) (Matrix.GeneralLinearGroup.det :
    GL (Fin n) K →* Kˣ) (centralizer ({Y} : Set (GL (Fin n) K)))
  rw [← CFSG.Open.StatedAPI.statedSL_eq_ker_det] at h3
  obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1
    (centralizer ({Y} : Set (GL (Fin n) K)) ⊓ StatedSL n K)
  set m := CFSG.Open.pRank p (centralizer ({Y} : Set (GL (Fin n) K)) ⊓ StatedSL n K) with hm
  obtain ⟨F, hF, hFcard, hFmem⟩ := exists_isElemAbelian_subgroupOf hE (StatedSL n K)
  have hEH : E ≤ StatedSL n K := hEle.trans inf_le_right
  have hFm : Nat.card F = p ^ m := by
    rw [hFcard, inf_eq_left.2 hEH, hEcard]
  have hFy : ∀ f ∈ F, f * ŷ = ŷ * f := by
    intro f hf
    have h1 : (f : GL (Fin n) K) ∈ centralizer ({Y} : Set (GL (Fin n) K)) :=
      (hEle ((hFmem f).1 hf)).1
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact Subtype.ext h1
  have := le_pRank_centralizer_quotient
    ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) hN hF hFm hFy
  omega

theorem abelian_statedProj_sl (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hg : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) {e : ℕ} (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (h2 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))) = 2)
    (R : Sylow p (StatedProj (StatedSL n K))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedSL n K))) := by
  by_cases hsmall : n / e < p
  · exact isMulCommutative_sylow_statedProj
      (fun P hP => isMulCommutative_of_isPGroup_GL_matrix
        (hp.out.odd_of_ne_two (by omega)) hpK he hpe hsmall hP) (StatedSL n K) R
  · exfalso
    have h3 := three_le_pRank_centralizer_statedProj_large hp5 hpK hg he hpe (not_lt.1 hsmall)
      1 (one_pow p)
    have hc : centralizer ({1} : Set (StatedProj (StatedSL n K))) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.2 (by simp)
    rw [hc, h2] at h3
    omega

theorem rank_statedProj_sl (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hg : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) {e : ℕ} (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))))
    (y : StatedProj (StatedSL n K)) (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedSL n K)))) := by
  by_cases hsmall : n / e < p
  · exact three_le_pRank_centralizer_of_sylow_abelian
      (fun R => isMulCommutative_sylow_statedProj
        (fun P hP => isMulCommutative_of_isPGroup_GL_matrix
          (hp.out.odd_of_ne_two (by omega)) hpK he hpe hsmall hP) (StatedSL n K) R) h3 hy
  · exact three_le_pRank_centralizer_statedProj_large hp5 hpK hg he hpe (not_lt.1 hsmall) y hy

end Stated

section Catalog

theorem crossAbelianAt_linear {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) : CrossAbelianAt ⟨.A m q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ hn h2 P
  haveI : Fact p.Prime := ⟨hp⟩
  have hmodel := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hg := not_dvd_gcd_psl_of_not_isLinearOrUnitaryAt hn hmodel
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmodel
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  rw [← hK] at hg
  obtain ⟨e₀, he, hpe⟩ := exists_order_data (K := K) (p := p) hpK
  have h2' : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL (m + 1) K))) = 2 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e').symm.trans h2
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => abelian_statedProj_sl hp5 hpK hg he hpe h2' R) P

theorem crossRankAt_linear {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) : CrossRankAt ⟨.A m q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ hn h3 y hy
  haveI : Fact p.Prime := ⟨hp⟩
  have hmodel := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hg := not_dvd_gcd_psl_of_not_isLinearOrUnitaryAt hn hmodel
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmodel
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  rw [← hK] at hg
  obtain ⟨e₀, he, hpe⟩ := exists_order_data (K := K) (p := p) hpK
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL (m + 1) K))) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e') ▸ h3
  have hyp : (e' y) ^ p = 1 := by
    rw [← map_pow, (hy ▸ pow_orderOf_eq_one y : y ^ p = 1), map_one]
  exact (rank_statedProj_sl hp5 hpK hg he hpe h3' (e' y) hyp).trans
    (pRank_centralizer_of_mulEquiv e' y)

theorem crossAt_linear {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) : CrossAt ⟨.A m q, hv⟩ :=
  ⟨crossAbelianAt_linear hv, crossRankAt_linear hv⟩

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
