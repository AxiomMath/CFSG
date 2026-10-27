module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankFusion
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem SmallRankPlane.of_situation (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) : SmallRankPlane p (P : Subgroup G) x z :=
  smallRankPlane_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
    hsit.largeObstruction_empty hx.mem hx.ne_one hx.pow_eq_one hx.not_centralizer_le hz.mem
    hz.centralizes hz.ne_one hz.pow_eq_one

theorem exists_mem_normalizer_conj_zpowers (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {y : G} (hyB : y ∈ zpowers x ⊔ zpowers z)
    (hyZ : y ∉ zpowers z) :
    ∃ g ∈ (P : Subgroup G) ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers y := by
  classical
  have hprime := sigmaA_prime p hsit.mem_sigmaA
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  have hA : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ 3 := by
    obtain ⟨A, hAP, hAe, hAc⟩ := pRank_attained p (P : Subgroup G) (by omega)
    exact ⟨A, hAP, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hAe,
      by rwa [hP3] at hAc⟩
  obtain ⟨hcomm, h, hh, hne⟩ := hB.exists_transvection hprime P.isPGroup' hz.centralizes
    hz.ne_one hz.pow_eq_one hA
  obtain ⟨d, hdeq⟩ : ∃ d, d = h * x * h⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hd : d ∈ zpowers z := by rw [hdeq]; exact hcomm h hh
  have hd1 : d ≠ 1 := by rw [hdeq]; exact hne
  have hdp : d ^ p = 1 := hB.isElemAbelian.2 d (mem_sup_right hd)
  have hdz : zpowers d = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hd) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hdp hd1,
      orderOf_eq_prime hz.pow_eq_one hz.ne_one]
  have hdc : ∀ q ∈ (P : Subgroup G), q * d = d * q := fun q hq =>
    mem_centralizer_iff.mp ((zpowers_le.mpr hz.centralizes) hd) q hq
  have hhx : h * x * h⁻¹ = d * x := by rw [hdeq]; group
  have hconjk : ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ = d ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hhd : h * d ^ k = d ^ k * h := (Commute.pow_right (hdc h hh.1) k).eq
      calc h ^ (k + 1) * x * (h ^ (k + 1))⁻¹
          = h * (h ^ k * x * (h ^ k)⁻¹) * h⁻¹ := by group
        _ = (h * d ^ k) * x * h⁻¹ := by rw [ih]; group
        _ = d ^ k * (h * x * h⁻¹) := by rw [hhd]; group
        _ = d ^ k * (d * x) := by rw [hhx]
        _ = d ^ (k + 1) * x := by rw [pow_succ, mul_assoc]
  have hxn : zpowers x ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    zpowers_le.mpr (le_normalizer_zpowers_of_le_centralizer hz.centralizes hx.mem)
  have hyB' : y ∈ ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := hyB
  rw [coe_mul_of_left_le_normalizer_right _ _ hxn] at hyB'
  obtain ⟨a, ha, c, hc, rfl⟩ := hyB'
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hyZ (by simpa using hc)
  have hap : a ^ p = 1 := hB.isElemAbelian.2 a (mem_sup_left ha)
  have haz : zpowers a = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hap ha1,
      orderOf_eq_prime hx.pow_eq_one hx.ne_one]
  obtain ⟨u, hu⟩ : ∃ u : ℕ, a ^ u = x := by
    have hxa : x ∈ zpowers a := by rw [haz]; exact mem_zpowers x
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxa)
  have hac : Commute a c := congrArg Subtype.val
    (hB.isElemAbelian.1.is_comm.comm ⟨a, mem_sup_left ha⟩ ⟨c, mem_sup_right hc⟩)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d ^ k = c ^ u := by
    have hcu : c ^ u ∈ zpowers d := by rw [hdz]; exact pow_mem hc u
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hcu)
  have hgx : h ^ k * x * (h ^ k)⁻¹ = (a * c) ^ u := by
    rw [hconjk, hk, hac.mul_pow, hu]
    exact (hu ▸ (hac.pow_pow u u).symm).eq
  have hmap : (zpowers x).map (MulAut.conj (h ^ k)).toMonoidHom =
      zpowers (h ^ k * x * (h ^ k)⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hle : (zpowers x).map (MulAut.conj (h ^ k)).toMonoidHom ≤ zpowers (a * c) := by
    rw [hmap, zpowers_le, hgx]
    exact pow_mem (mem_zpowers _) u
  have hyp : (a * c) ^ p = 1 := hB.isElemAbelian.2 _ hyB
  have hy1 : a * c ≠ 1 := by
    intro h1
    apply hyZ
    show a * c ∈ zpowers z
    rw [h1]
    exact one_mem _
  refine ⟨h ^ k, pow_mem hh k, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1,
    card_map_of_injective (MulAut.conj (h ^ k)).injective, Nat.card_zpowers,
    orderOf_eq_prime hx.pow_eq_one hx.ne_one]

theorem normalizer_plane_le_normalizer_zpowers (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤
      normalizer ((zpowers z : Subgroup G) : Set G) := by
  classical
  have hprime := sigmaA_prime p hsit.mem_sigmaA
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hB.isIsolatedPlane.1
  intro g hg
  have hz'B : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z :=
    (mem_normalizer_iff.mp hg z).mp (mem_sup_right (mem_zpowers z))
  by_cases hz' : g * z * g⁻¹ ∈ zpowers z
  ·
    refine mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge ?_
      (card_map_of_injective (MulAut.conj g).injective).ge)
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact hz'
  ·
    exfalso
    obtain ⟨h, hh, hconj⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx hz hz'B hz'
    have hcz : ∀ w : G,
        centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
      rw [zpowers_eq_closure, centralizer_closure]
    have hC : centralizer ({g * z * g⁻¹} : Set G) =
        (centralizer ({x} : Set G)).map (MulAut.conj h).toMonoidHom := by
      calc centralizer ({g * z * g⁻¹} : Set G)
          = centralizer ((zpowers (g * z * g⁻¹) : Subgroup G) : Set G) := hcz _
        _ = centralizer (((zpowers x).map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
          rw [hconj]
        _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj h).toMonoidHom :=
          (centralizer_map_automorphism _ _).symm
        _ = (centralizer ({x} : Set G)).map (MulAut.conj h).toMonoidHom := by rw [hcz x]
    refine hsit.largeObstruction_empty (g * z * g⁻¹) ⟨hPM (hBP hz'B), ?_, ?_, ?_, ?_⟩
    · exact fun h1 => hz.ne_one (conj_eq_one_iff.mp h1)
    · rw [conj_pow, hz.pow_eq_one, mul_one, mul_inv_cancel]
    ·
      have hPz' : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
          centralizer ({g * z * g⁻¹} : Set G) := by
        rintro _ ⟨q, hq, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have hqz : q * z = z * q := mem_centralizer_iff.mp hz.centralizes q hq
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
          _ = g * (z * q) * g⁻¹ := by rw [hqz]
          _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
      have h3 := pRank_mono p hprime.one_lt hPz'
      rwa [pRank_map_automorphism p hprime.one_lt, hP3] at h3
    ·
      intro hle
      apply hx.not_centralizer_le
      intro c hc
      have hcM : h * c * h⁻¹ ∈ M := hle (by rw [hC]; exact ⟨c, hc, rfl⟩)
      have hhM : h ∈ M := hPM hh.1
      have hc' := M.mul_mem (M.mul_mem (M.inv_mem hhM) hcM) hhM
      simpa [mul_assoc] using hc'

theorem normalizer_plane_le (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M := by
  have hprime := sigmaA_prime p hsit.mem_sigmaA
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  have hPM := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hB.isIsolatedPlane.1
  refine normalizer_le_of_le_of_two_le_pRank hS hU0 hsit.mem_sigmaA hsit.isCoreMaxLocal
    (P.isPGroup'.to_le hBP) (hBP.trans hPM) ?_
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, le_rfl, hB.isElemAbelian, hB.card_eq⟩

set_option linter.unusedVariables false in
theorem centralizer_plane_le (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M := by
  have hzB : ({z} : Set G) ⊆ ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) :=
    Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers z))
  exact (centralizer_le hzB).trans ((centralizer_singleton_le_normalizer_zpowers z).trans
    (normalizer_zpowers_le_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
      hsit.largeObstruction_empty hz.mem hz.centralizes hz.ne_one hz.pow_eq_one))

end CFSG.LocalAnalysis.RankThreeTheoremC
