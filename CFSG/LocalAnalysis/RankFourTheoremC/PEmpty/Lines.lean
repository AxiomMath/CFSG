module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Plane
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankFusion

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem Situation.exists_elemAbelian_cube (hS : Situation G p P M) :
    ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ 3 := by
  have hprime := hS.prime
  have h4 := hS.four_le_pRank
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hprime.one_lt (P : Subgroup G)
  have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p (by omega)
  obtain ⟨A, hAc, -, hAE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hprime (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨A, hAE.trans hEP,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2
      (CFSG.Open.IsElemAbelian.mono hE hAE), hAc⟩

theorem exists_mem_normalizer_conj_zpowers (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {y : G} (hyB : y ∈ zpowers x ⊔ zpowers z) (hyZ : y ∉ zpowers z) :
    ∃ g ∈ (P : Subgroup G) ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers y := by
  classical
  have hprime := hS.prime
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hB := plane_of_central hS hx hz
  have hx1 : x ≠ 1 := hx.ne_one hprime
  have hxp : x ^ p = 1 := hx.pow_eq_one
  obtain ⟨hcomm, h, hh, hne⟩ := hB.exists_transvection hprime P.isPGroup' hz.centralizes
    hz.ne_one hz.pow_eq_one hS.exists_elemAbelian_cube
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
    zpowers_le.mpr
      (CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_zpowers_of_le_centralizer
        hz.centralizes hx.mem)
  have hyB' : y ∈ ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := hyB
  rw [coe_mul_of_left_le_normalizer_right _ _ hxn] at hyB'
  obtain ⟨a, ha, c, hc, rfl⟩ := hyB'
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hyZ (by simpa using hc)
  have hap : a ^ p = 1 := hB.isElemAbelian.2 a (mem_sup_left ha)
  have haz : zpowers a = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hap ha1, hx.order]
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
    card_map_of_injective (MulAut.conj (h ^ k)).injective, Nat.card_zpowers, hx.order]

theorem pRank_centralizer_le_of_mem_plane (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {y : G} (hyB : y ∈ zpowers x ⊔ zpowers z) (hyZ : y ∉ zpowers z) :
    Open.pRank p (centralizer ({y} : Set G)) ≤ 2 := by
  have hprime := hS.prime
  obtain ⟨g, -, hconj⟩ := exists_mem_normalizer_conj_zpowers hS hx hz hyB hyZ
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({y} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    calc centralizer ({y} : Set G)
        = centralizer ((zpowers y : Subgroup G) : Set G) := hcz _
      _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [hconj]
      _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        (centralizer_map_automorphism _ _).symm
      _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]
  rw [hC, pRank_map_automorphism p hprime.one_lt]
  exact hx.pRank_centralizer_le hS

theorem mem_zpowers_of_conj_mem_plane (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  have hprime := hS.prime
  by_contra hgz
  have h2 := pRank_centralizer_le_of_mem_plane hS hx hz hg hgz
  have hPz' : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqz : q * z = z * q := mem_centralizer_iff.mp hz.centralizes q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  have h4 := CFSG.SectionRank.pRank_mono hprime.one_lt hPz'
  rw [pRank_map_automorphism p hprime.one_lt] at h4
  have := hS.four_le_pRank
  omega

theorem normalizer_plane_le_normalizer_zpowers (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) :
    normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤
      normalizer ((zpowers z : Subgroup G) : Set G) := by
  intro g hg
  have hz'B : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z :=
    (mem_normalizer_iff.mp hg z).mp (mem_sup_right (mem_zpowers z))
  have hz' := mem_zpowers_of_conj_mem_plane hS hx hz hz'B
  refine mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge ?_
    (card_map_of_injective (MulAut.conj g).injective).ge)
  rw [MonoidHom.map_zpowers, zpowers_le]
  exact hz'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
