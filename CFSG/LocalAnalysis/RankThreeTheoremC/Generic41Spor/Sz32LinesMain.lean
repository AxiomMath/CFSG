module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Qdecomp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedLemma33
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32FocalAlperin
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32LinesTorus
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NormalizerJ
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32OuterY
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.LinesCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41Aux
import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 U3Lemma33 u3f_false_of_lines
  fusion_P_le_C_of_fix u3K0_conj_gen)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_comm_pow5 {X : Type*} [Group X] {y a : X} {n : ℤ} (hao : orderOf a = 25)
    (hn : y * a * y⁻¹ = a ^ n) (hn5 : n % 5 = 1) : y * a ^ 5 = a ^ 5 * y := by
  obtain ⟨r, hr⟩ : ∃ r : ℤ, n = 5 * r + 1 := ⟨n / 5, by omega⟩
  have h25 : a ^ (25 : ℤ) = 1 := by
    have : a ^ 25 = 1 := hao ▸ pow_orderOf_eq_one a
    simpa using this
  have h1 : y * a ^ 5 * y⁻¹ = a ^ 5 := by
    rw [← conj_pow, hn, ← zpow_natCast, ← zpow_mul, hr]
    have : a ^ ((5 * r + 1) * ((5 : ℕ) : ℤ)) = (a ^ (25 : ℤ)) ^ r * a ^ ((5 : ℕ) : ℤ) := by
      rw [← zpow_mul, ← zpow_add]
      congr 1
      push_cast
      ring
    rw [this, h25, one_zpow, one_mul]
    simp
  calc y * a ^ 5 = (y * a ^ 5 * y⁻¹) * y := by group
    _ = a ^ 5 * y := by rw [h1]

theorem sz32_C_e_central {a c y : G} (hA : Sz32QDecomp P x J a c y) :
    ∀ s ∈ u3S P x, s * a ^ 5 = a ^ 5 * s := by
  have hpres := hA.pres
  obtain ⟨n, hn, hn5, -⟩ := hpres.ya
  have hy : y * a ^ 5 = a ^ 5 * y := sz32_comm_pow5 hpres.ord_a hn hn5
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer ({a ^ 5} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        ((Commute.refl a).pow_right 5).eq)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        ((show Commute c a from hpres.ac.symm).pow_right 5).eq)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hy)
  intro s hs
  have hs' : s ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y := hpres.gen ▸ hs
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs')

theorem sz32_C_act (hdata : Sz32DataFacts) (hc : PointConfig IsSz32Type G 5 P M x J)
    {a c y : G} (hA : Sz32QDecomp P x J a c y) {d : G} (hdS : d ∈ u3S P x) (hd5 : d ^ 5 = 1)
    (hdQ : d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c) :
    ∃ n : ℤ, d * a * d⁻¹ = a ^ n ∧ n % 5 = 1 ∧ n % 25 ≠ 1 := by
  have hpres := hA.pres
  have hao := hpres.ord_a
  have hout := sz32_A_out hdata hc hA.T_eq hA.QC
  have haS : a ∈ u3S P x := hpres.a_mem
  have hdC : d ∈ Subgroup.centralizer ({x} : Set G) := hdS.2
  have hdaS : d * a * d⁻¹ ∈ u3S P x :=
    (u3S P x).mul_mem ((u3S P x).mul_mem hdS haS) ((u3S P x).inv_mem hdS)
  have hdaJ : d * a * d⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hc.cent_le hdC) a).mp hA.a_J
  have hda' : d * a * d⁻¹ ∈ Subgroup.zpowers a :=
    hA.T_eq ▸ (⟨hdaS, hdaJ⟩ : d * a * d⁻¹ ∈ u3S P x ⊓ J)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hda'
  have hn5 : n % 5 = 1 := sz32_conj_mod5 (k := 2) (by norm_num) (by rw [hao]; norm_num) hd5 hn.symm
  refine ⟨n, hn.symm, hn5, ?_⟩
  intro h
  have h1 : a ^ n = a := by
    have h2 := zpow_mod_orderOf a n
    rw [hao] at h2
    simp only [Nat.cast_ofNat] at h2
    rw [h, zpow_one] at h2
    exact h2.symm
  rw [h1] at hn
  have hcomm : d * a = a * d := by
    calc d * a = (d * a * d⁻¹) * d := by group
      _ = a * d := by rw [← hn]
  exact hdQ (hout d hdS hcomm)

theorem sz32_C_not_out (hdata : Sz32DataFacts) (hc : PointConfig IsSz32Type G 5 P M x J)
    {a c y : G} (hA : Sz32QDecomp P x J a c y) (hL33 : U3Lemma33 5 x) {d : G}
    (hdS : d ∈ u3S P x) (hd5 : d ^ 5 = 1) (hdQ : d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    (hconj : ∃ g : G, Subgroup.zpowers d = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpres := hA.pres
  have hao := hpres.ord_a
  have haS : a ∈ u3S P x := hpres.a_mem
  obtain ⟨n, hn, hn5, hn25⟩ := sz32_C_act hdata hc hA hdS hd5 hdQ
  obtain ⟨r, hr⟩ : ∃ r : ℤ, n = 5 * r + 1 := ⟨n / 5, by omega⟩
  have hd1 : d ≠ 1 := fun h => hdQ (h ▸ Subgroup.one_mem _)
  have h25 : a ^ 25 = 1 := hao ▸ pow_orderOf_eq_one a
  have he5 : (a ^ 5) ^ 5 = 1 := by rw [← pow_mul]; exact h25
  have heo : orderOf (a ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hao]; norm_num), hao]
  set t : G := a ^ (1 - n) with ht
  have hte : t ∈ Subgroup.zpowers (a ^ 5) := by
    refine Subgroup.mem_zpowers_iff.mpr ⟨-r, ?_⟩
    rw [ht, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    omega
  have ht1 : t ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_iff_zpow_eq_one.mpr h
    rw [hao] at h1
    have : (25 : ℤ) ∣ 1 - n := by exact_mod_cast h1
    omega
  have hdia : a * d * a⁻¹ = t * d := by
    have h1 : d * a⁻¹ * d⁻¹ = a ^ (-n) := by
      rw [zpow_neg, ← hn]
      group
    calc a * d * a⁻¹ = a * (d * a⁻¹ * d⁻¹) * d := by group
      _ = a * a ^ (-n) * d := by rw [h1]
      _ = t * d := by rw [ht, ← zpow_one_add]; rfl
  have hat : ∀ i : ℕ, a * t ^ i * a⁻¹ = t ^ i := by
    intro i
    have : Commute a (t ^ i) := ((Commute.refl a).zpow_right (1 - n)).pow_right i
    calc a * t ^ i * a⁻¹ = (t ^ i * a) * a⁻¹ := by rw [this.eq]
      _ = t ^ i := by group
  have hind : ∀ i : ℕ, a ^ i * d * (a ^ i)⁻¹ = t ^ i * d := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc a ^ (i + 1) * d * (a ^ (i + 1))⁻¹
          = a * (a ^ i * d * (a ^ i)⁻¹) * a⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = a * (t ^ i * d) * a⁻¹ := by rw [ih]
        _ = (a * t ^ i * a⁻¹) * (a * d * a⁻¹) := by group
        _ = t ^ i * (t * d) := by rw [hat i, hdia]
        _ = t ^ (i + 1) * d := by rw [pow_succ]; group
  have hde : d * a ^ 5 = a ^ 5 * d := sz32_comm_pow5 hao hn hn5
  have hdnot : d ∉ Subgroup.zpowers (a ^ 5) := fun h =>
    hdQ (Subgroup.mem_sup_left ((Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5)) h))
  have hel_e : IsElemAbelian 5 (Subgroup.zpowers (a ^ 5)) := CFSG.Open.isElemAbelian_zpowers he5
  have hel_d : IsElemAbelian 5 (Subgroup.zpowers d) := CFSG.Open.isElemAbelian_zpowers hd5
  have hcomm_ed : ∀ u ∈ Subgroup.zpowers (a ^ 5), u * d = d * u := by
    intro u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((show Commute (a ^ 5) d from hde.symm).zpow_left i).eq
  have hEel : IsElemAbelian 5 (Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers d) := by
    refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 5 hel_e hel_d ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute d u from (hcomm_ed u hu).symm).zpow_left k).eq
  have hEcard : Nat.card ↥(Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers d) = 5 ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_five (Subgroup.zpowers (a ^ 5)) hd5 hdnot
      hcomm_ed, Nat.card_zpowers, heo]
    norm_num
  have hEC : Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr hdS.2)
    exact ((u3S P x).pow_mem haS 5).2
  have hdt : d ∉ Subgroup.zpowers t := fun h =>
    hdnot ((Subgroup.zpowers_le.mpr hte) h)
  obtain ⟨g₀, hg₀⟩ := hconj
  refine u3f_false_of_lines hL33 hEC hEel hEcard (a := d) (b := t)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) (Subgroup.mem_sup_left hte) ht1 hdt ?_
  intro i _
  refine ⟨a ^ i * g₀, ?_⟩
  rw [← map_conj_map_conj, ← hg₀, map_conj_zpowers, ← hind i]

theorem sz32_arith_two_pow (i s : ℕ) (hi : ¬ 5 ∣ i) (hs : ¬ 5 ∣ s) :
    ∃ m : ℕ, m < 4 ∧ (2 ^ m * i) % 5 = s % 5 := by
  have key : ∀ a : ℕ, a < 5 → ∀ b : ℕ, b < 5 → 0 < a → 0 < b →
      ∃ m : ℕ, m < 4 ∧ (2 ^ m * a) % 5 = b := by decide
  have hi5 : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hs5 : s % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hi0 : 0 < i % 5 := Nat.pos_of_ne_zero (fun h => hi (Nat.dvd_of_mod_eq_zero h))
  have hs0 : 0 < s % 5 := Nat.pos_of_ne_zero (fun h => hs (Nat.dvd_of_mod_eq_zero h))
  obtain ⟨m, hm, h⟩ := key (i % 5) hi5 (s % 5) hs5 hi0 hs0
  refine ⟨m, hm, ?_⟩
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod] at h
  exact h

theorem sz32_C_W {a c y : G} (hA : Sz32QDecomp P x J a c y) (hx1 : x ≠ 1) (hxp : x ^ 5 = 1) :
    IsElemAbelian 5 (Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x) ∧
      Nat.card ↥(Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x) = 5 ^ 2 := by
  have hpres := hA.pres
  have hao := hpres.ord_a
  have h25 : a ^ 25 = 1 := hao ▸ pow_orderOf_eq_one a
  have he5 : (a ^ 5) ^ 5 = 1 := by rw [← pow_mul]; exact h25
  have hcomm : ∀ u ∈ Subgroup.zpowers (a ^ 5), u * x = x * u := by
    intro u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hpres.x_mem
    have : Commute (a ^ 5) c := (show Commute a c from hpres.ac).pow_left 5
    exact (this.zpow_zpow i j).eq
  refine ⟨?_, ?_⟩
  · refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 5
      (CFSG.Open.isElemAbelian_zpowers he5) (CFSG.Open.isElemAbelian_zpowers hxp) ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute x u from (hcomm u hu).symm).zpow_left k).eq
  · have hxa : x ∉ Subgroup.zpowers (a ^ 5) := by
      intro hx
      have h1 : x ∈ Subgroup.zpowers a :=
        (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5)) hx
      have h2 : x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c := ⟨h1, hpres.x_mem⟩
      rw [hpres.inf, Subgroup.mem_bot] at h2
      exact hx1 h2
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_five (Subgroup.zpowers (a ^ 5)) hxp hxa
      hcomm, Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hao]; norm_num), hao]
    norm_num

theorem sz32_C_W_lines (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hA : Sz32QDecomp P x J a c y) (hL33 : U3Lemma33 5 x)
    (hn : ∃ n ∈ J, n * a ^ 5 * n⁻¹ = (a ^ 5) ^ 2) {d : G}
    (hdW : d ∈ Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x) (hd1 : d ≠ 1)
    (hconj : ∃ g : G, Subgroup.zpowers d = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) :
    Subgroup.zpowers d = Subgroup.zpowers x ∨ Subgroup.zpowers d = Subgroup.zpowers (a ^ 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5 : Nat.Prime 5 := by norm_num
  have hpres := hA.pres
  have hao := hpres.ord_a
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hxo : orderOf x = 5 := orderOf_eq_prime hxp hx1
  have h25 : a ^ 25 = 1 := hao ▸ pow_orderOf_eq_one a
  have he5 : (a ^ 5) ^ 5 = 1 := by rw [← pow_mul]; exact h25
  have heo : orderOf (a ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hao]; norm_num), hao]
  have he1 : a ^ 5 ≠ 1 := by
    intro h; rw [h, orderOf_one] at heo; omega
  obtain ⟨hWel, hWcard⟩ := sz32_C_W hA hx1 hxp
  have hex : Commute (a ^ 5) x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpres.x_mem
    rw [← hk]
    exact ((show Commute a c from hpres.ac).pow_left 5).zpow_right k
  have hcomm : ∀ u ∈ Subgroup.zpowers (a ^ 5), ∀ v ∈ Subgroup.zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (hex.zpow_zpow i j).eq
  obtain ⟨u, hu, v, hv, huv⟩ := sps_mem_sup_of_commute hcomm hdW
  by_cases hu1 : u = 1
  · left
    have hdv : d = v := by rw [huv, hu1, one_mul]
    rw [hdv] at hd1 ⊢
    exact eg41_zpowers_eq_of_mem hp5 hxo hv hd1
  by_cases hv1 : v = 1
  · right
    have hdu : d = u := by rw [huv, hv1, mul_one]
    rw [hdu] at hd1 ⊢
    exact eg41_zpowers_eq_of_mem hp5 heo hu hd1
  exfalso
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hu)
  have hi5 : ¬ 5 ∣ i := by
    intro h
    obtain ⟨k, rfl⟩ := h
    apply hu1
    rw [← hi, pow_mul, he5, one_pow]
  obtain ⟨n, hnJ, hne⟩ := hn
  have hnx : n * x = x * n := Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hnJ)
  have hnv : n * v = v * n := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (((show Commute n x from hnx).zpow_right k)).eq
  have hnpow : ∀ m : ℕ, n ^ m * a ^ 5 * (n ^ m)⁻¹ = (a ^ 5) ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc n ^ (m + 1) * a ^ 5 * (n ^ (m + 1))⁻¹
          = n * (n ^ m * a ^ 5 * (n ^ m)⁻¹) * n⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = n * (a ^ 5) ^ (2 ^ m) * n⁻¹ := by rw [ih]
        _ = (n * a ^ 5 * n⁻¹) ^ (2 ^ m) := conj_pow.symm
        _ = ((a ^ 5) ^ 2) ^ (2 ^ m) := by rw [hne]
        _ = (a ^ 5) ^ (2 ^ (m + 1)) := by rw [← pow_mul, pow_succ]; ring_nf
  obtain ⟨g₀, hg₀⟩ := hconj
  have hvW : v ∈ Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right hv
  have heW : a ^ 5 ∈ Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hve : v ∉ Subgroup.zpowers (a ^ 5) := by
    intro hve
    have h1 : v ∈ Subgroup.zpowers a :=
      (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5)) hve
    have h2 : v ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c :=
      ⟨h1, (Subgroup.zpowers_le.mpr hpres.x_mem) hv⟩
    rw [hpres.inf, Subgroup.mem_bot] at h2
    exact hv1 h2
  have hWC : Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact ((u3S P x).pow_mem hpres.a_mem 5).2
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine u3f_false_of_lines hL33 hWC hWel hWcard (a := v) (b := a ^ 5) hvW heW he1 hve ?_
  intro s hs
  by_cases hs0 : s = 0
  · refine ⟨1, ?_⟩
    rw [hs0, pow_zero, one_mul, map_conj_one]
    exact eg41_zpowers_eq_of_mem hp5 hxo hv hv1
  · have hs5 : ¬ 5 ∣ s := fun h => hs0 (by omega)
    obtain ⟨m, -, hm⟩ := sz32_arith_two_pow i s hi5 hs5
    refine ⟨n ^ m * g₀, ?_⟩
    rw [← map_conj_map_conj, ← hg₀, map_conj_zpowers]
    congr 1
    have hdd : d = (a ^ 5) ^ i * v := by rw [huv, ← hi]
    have hnd : n ^ m * d * (n ^ m)⁻¹ = (a ^ 5) ^ (2 ^ m * i) * v := by
      calc n ^ m * d * (n ^ m)⁻¹ = (n ^ m * (a ^ 5) ^ i * (n ^ m)⁻¹) * (n ^ m * v * (n ^ m)⁻¹) := by
            rw [hdd]; group
        _ = ((n ^ m * a ^ 5 * (n ^ m)⁻¹) ^ i) * v := by
            rw [conj_pow, ((show Commute (n ^ m) v from ((show Commute n v from hnv).pow_left m)).eq)]
            group
        _ = (a ^ 5) ^ (2 ^ m * i) * v := by rw [hnpow m, ← pow_mul]
    rw [hnd]
    have hes : (a ^ 5) ^ (2 ^ m * i) = (a ^ 5) ^ s := by
      rw [pow_eq_pow_iff_modEq, heo]
      exact hm
    rw [hes]

theorem sz32_five_elt_line_swap {u : G} (hu : ∃ k : ℕ, u ^ (5 ^ k) = 1) {A B : Subgroup G}
    (hAB : A ≠ B) (hAu : A.map (MulAut.conj u).toMonoidHom = B)
    (h2 : A.map (MulAut.conj (u ^ 2)).toMonoidHom = A ∨
      A.map (MulAut.conj (u ^ 2)).toMonoidHom = B) : False := by
  obtain ⟨k, hk⟩ := hu
  have hinj : Function.Injective (MulAut.conj u).toMonoidHom := (MulAut.conj u).injective
  have hBu : B.map (MulAut.conj u).toMonoidHom = A.map (MulAut.conj (u ^ 2)).toMonoidHom := by
    rw [← hAu, map_conj_map_conj, pow_two]
  have hA2 : A.map (MulAut.conj (u ^ 2)).toMonoidHom = A := by
    rcases h2 with h | h
    · exact h
    · exfalso
      apply hAB
      refine Subgroup.map_injective hinj ?_
      rw [hAu, hBu, h]
  have hind : ∀ m : ℕ, A.map (MulAut.conj (u ^ (2 * m))).toMonoidHom = A := by
    intro m
    induction m with
    | zero => rw [Nat.mul_zero, pow_zero]; exact map_conj_one A
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 + 2 * m by ring, pow_add, ← map_conj_map_conj, ih, hA2]
  have hodd : Odd (5 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have hu1 : u ^ (2 * (m + 1)) = u := by
    have : 2 * (m + 1) = 5 ^ k + 1 := by omega
    rw [this, pow_succ, hk, one_mul]
  have := hind (m + 1)
  rw [hu1, hAu] at this
  exact hAB this.symm

theorem sz32_C_lines_S (hdata : Sz32DataFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hA : Sz32QDecomp P x J a c y) (hL33 : U3Lemma33 5 x)
    (hn : ∃ n ∈ J, n * a ^ 5 * n⁻¹ = (a ^ 5) ^ 2) :
    ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ u3S P x →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x ∨
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5) := by
  have hpres := hA.pres
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  intro g hg
  rw [map_conj_zpowers] at hg ⊢
  have hdS : g * x * g⁻¹ ∈ u3S P x := hg (Subgroup.mem_zpowers _)
  have hd5 : (g * x * g⁻¹) ^ 5 = 1 := by rw [conj_pow, hxp]; group
  have hd1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [h] at this
    simpa using this
  have hconj : ∃ g' : G, Subgroup.zpowers (g * x * g⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj g').toMonoidHom := ⟨g, by rw [map_conj_zpowers]⟩
  by_cases hdQ : g * x * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c
  · have hdW := sz32_A_omega hpres.ac hpres.ord_a hpres.inf hpres.x_mem hx1 hxp _ hdQ hd5
    exact sz32_C_W_lines hc hA hL33 hn hdW hd1 hconj
  · exact (sz32_C_not_out hdata hc hA hL33 hdS hd5 hdQ hconj).elim

theorem sz32_x_ne_e {a c y : G} (hA : Sz32QDecomp P x J a c y) (hx1 : x ≠ 1) :
    Subgroup.zpowers x ≠ Subgroup.zpowers (a ^ 5) := by
  intro h
  have hpres := hA.pres
  have h1 : x ∈ Subgroup.zpowers (a ^ 5) := h ▸ Subgroup.mem_zpowers x
  have h2 : x ∈ Subgroup.zpowers a :=
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5)) h1
  have h3 : x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c := ⟨h2, hpres.x_mem⟩
  rw [hpres.inf, Subgroup.mem_bot] at h3
  exact hx1 h3

theorem sz32_C_le_cent (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hA : Sz32QDecomp P x J a c y)
    (hlines : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ u3S P x →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x ∨
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5)) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hxe := sz32_x_ne_e hA hx1
  refine fusion_P_le_C_of_fix hc fun u huP huN => ?_
  have hle : ∀ m : ℕ, (Subgroup.zpowers x).map (MulAut.conj (u ^ m)).toMonoidHom ≤ u3S P x := by
    intro m
    have hum : u ^ m ∈ Subgroup.normalizer ((u3S P x : Subgroup G) : Set G) :=
      Subgroup.pow_mem _ huN m
    rintro _ ⟨s, hs, rfl⟩
    have hsS : s ∈ u3S P x := (Subgroup.zpowers_le.mpr hxS) hs
    exact (Subgroup.mem_normalizer_iff.mp hum s).mp hsS
  have h1 := hlines u (by simpa using hle 1)
  rcases h1 with h1 | h1
  · have hmem : u * x * u⁻¹ ∈ (Subgroup.zpowers x).map (MulAut.conj u).toMonoidHom :=
      ⟨x, Subgroup.mem_zpowers x, rfl⟩
    rw [h1] at hmem
    exact hmem
  · exfalso
    have hu5 : ∃ k : ℕ, u ^ (5 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, huP⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    refine sz32_five_elt_line_swap hu5 hxe h1 ?_
    exact hlines (u ^ 2) (hle 2)

theorem sz32_lines_fusion_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hA : Sz32QDecomp P x J a c y)
    (hL33 : U3Lemma33 5 x) : Sz32Lines P x (a ^ 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := hS.simple
  have hpres := hA.pres
  have hn := sz32_torus_elt hS hD1 hU0 hSz' hdata hc hA
  have hlinesS := sz32_C_lines_S hdata hc hA hL33 hn
  have hPC := sz32_C_le_cent hc hA hlinesS
  have hSP : u3S P x = (P : Subgroup G) := u3S_eq_of_le_cent hPC
  have hlines : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x ∨
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5) :=
    fun g hg => hlinesS g (hSP ▸ hg)
  have hexists : ∃ h : G, (Subgroup.zpowers x).map (MulAut.conj h).toMonoidHom =
      Subgroup.zpowers (a ^ 5) := by
    by_contra hnone
    push Not at hnone
    have hwc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x :=
      fun g hg => (hlines g hg).resolve_right (hnone g)
    have hcent : ∀ g ∈ (P : Subgroup G), g * x = x * g := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp (hPC hg)
    have hfoc := sylow_le_commutator_normalizer_of_simple hS.nonab P hc.generic.1 hcent hwc
    have hy : y ∈ (P : Subgroup G) := hSP ▸ hpres.y_mem
    exact sz32_y_not_mem_commutator hS hD1 hU0 hSz hc hA
      (sz32_normalizer_le_normalizer_J hS hD1 hU0 hSz hc) (hfoc hy)
  obtain ⟨h, hh⟩ := hexists
  have hPe : (P : Subgroup G) ≤ Subgroup.centralizer ({a ^ 5} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (sz32_C_e_central hA s (hSP ▸ hs))
  obtain ⟨g, hgP, hgswap⟩ := exists_mem_normalizer_swap P hPC hPe hh
  exact ⟨hPC, hlines, ⟨g, hgP, hgswap⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
