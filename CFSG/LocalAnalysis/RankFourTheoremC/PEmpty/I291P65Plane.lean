module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankFusion
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {x z : G}

theorem exists_elemAbelian_cube (hp : p.Prime) (h4 : 4 ≤ Open.pRank p (P : Subgroup G)) :
    ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ 3 := by
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (P : Subgroup G)
  have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p (by omega)
  obtain ⟨A, hAc, -, hAE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨A, hAE.trans hEP,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2
      (CFSG.Open.IsElemAbelian.mono hE hAE), hAc⟩

theorem plane_facts (hp : p.Prime) (hB : SmallRankPlane p (P : Subgroup G) x z) :
    x ∈ (P : Subgroup G) ∧ z ∈ (P : Subgroup G) ∧ x ^ p = 1 ∧ z ^ p = 1 ∧ x ≠ 1 ∧ z ≠ 1 := by
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hB.isIsolatedPlane.1
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hzB : z ∈ zpowers x ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hxp : x ^ p = 1 := hB.isElemAbelian.2 x hxB
  have hzp : z ^ p = 1 := hB.isElemAbelian.2 z hzB
  have hc := hB.card_eq
  have hp2 : p < p ^ 2 := by
    have := hp.one_lt
    nlinarith
  refine ⟨hBP hxB, hBP hzB, hxp, hzp, ?_, ?_⟩
  · rintro rfl
    rw [zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers] at hc
    have : orderOf z ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hzp)
    omega
  · rintro rfl
    rw [zpowers_one_eq_bot, sup_bot_eq, Nat.card_zpowers] at hc
    have : orderOf x ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
    omega

theorem exists_conj_line (hp : p.Prime) (hB : SmallRankPlane p (P : Subgroup G) x z)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (h4 : 4 ≤ Open.pRank p (P : Subgroup G)) {y : G} (hyB : y ∈ zpowers x ⊔ zpowers z)
    (hyZ : y ∉ zpowers z) :
    ∃ g ∈ (P : Subgroup G) ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers y := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨hxP, hzP, hxp, hzp, hx1, hz1⟩ := plane_facts hp hB
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  obtain ⟨hcomm, h, hh, hne⟩ := hB.exists_transvection hp P.isPGroup' hzc hz1 hzp
    (exists_elemAbelian_cube hp h4)
  obtain ⟨d, hdeq⟩ : ∃ d, d = h * x * h⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hd : d ∈ zpowers z := by rw [hdeq]; exact hcomm h hh
  have hd1 : d ≠ 1 := by rw [hdeq]; exact hne
  have hdp : d ^ p = 1 := hB.isElemAbelian.2 d (mem_sup_right hd)
  have hdz : zpowers d = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hd) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hdp hd1, hzo]
  have hdc : ∀ q ∈ (P : Subgroup G), q * d = d * q := fun q hq =>
    mem_centralizer_iff.mp ((zpowers_le.mpr hzc) hd) q hq
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
    zpowers_le.mpr
      (CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_zpowers_of_le_centralizer hzc hxP)
  have hyB' : y ∈ ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := hyB
  rw [coe_mul_of_left_le_normalizer_right _ _ hxn] at hyB'
  obtain ⟨a, ha, c, hc, rfl⟩ := hyB'
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hyZ (by simpa using hc)
  have hap : a ^ p = 1 := hB.isElemAbelian.2 a (mem_sup_left ha)
  have haz : zpowers a = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hap ha1, hxo]
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
    card_map_of_injective (MulAut.conj (h ^ k)).injective, Nat.card_zpowers, hxo]

theorem exists_line_rep (hp : p.Prime) (hB : SmallRankPlane p (P : Subgroup G) x z)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) {b : G}
    (hbB : b ∈ zpowers x ⊔ zpowers z) (hbZ : b ∉ zpowers z) :
    ∃ j : Fin p, x * z ^ (j : ℕ) ∈ zpowers b := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨hxP, hzP, hxp, hzp, hx1, hz1⟩ := plane_facts hp hB
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxz : Commute x z := (mem_centralizer_iff.mp hzc x hxP)
  have hcomm : ∀ a ∈ zpowers x, ∀ c ∈ zpowers z, a * c = c * a := by
    intro a ha c hc
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (hxz.zpow_zpow m k).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers x) (zpowers z) hcomm).2
  have hbB' : b ∈ ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := hbB
  rw [hset] at hbB'
  obtain ⟨a, ha, c, hc, rfl⟩ := hbB'
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hbZ (by simpa using hc)
  have hap : a ^ p = 1 := hB.isElemAbelian.2 a (mem_sup_left ha)
  have haz : zpowers a = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hap ha1, hxo]
  obtain ⟨u, hu⟩ : ∃ u : ℕ, a ^ u = x := by
    have hxa : x ∈ zpowers a := by rw [haz]; exact mem_zpowers x
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxa)
  have hac : Commute a c := hcomm a ha c hc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, z ^ k = c ^ u := by
    have hcu : c ^ u ∈ zpowers z := pow_mem hc u
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hcu)
  refine ⟨⟨k % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
  have hzk : z ^ (k % p) = z ^ k := by
    conv_rhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hzp, one_pow, mul_one]
  show x * z ^ (k % p) ∈ zpowers (a * c)
  rw [hzk, hk, ← hu, ← hac.mul_pow]
  exact pow_mem (mem_zpowers _) u

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
