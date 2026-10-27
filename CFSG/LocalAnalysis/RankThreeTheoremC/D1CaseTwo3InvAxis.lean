module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CenterAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_cyclic_of_orderOf_eq_three {T : Type*} [Group T] [Finite T] [IsCyclic T]
    {a b : T} (ha : orderOf a = 3) (hb : b ^ 3 = 1) : b ∈ Subgroup.zpowers a := by
  classical
  have := Fintype.ofFinite T
  by_contra hnb
  have hS := IsCyclic.card_pow_eq_one_le (α := T) (n := 3) (by norm_num)
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hzp : ∀ x ∈ Subgroup.zpowers a, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hsub : insert b (Finset.univ.filter fun x : T => x ∈ Subgroup.zpowers a) ⊆
      Finset.univ.filter fun x : T => x ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | hx
    · exact hb
    · exact hzp x hx
  have hcard3 : (Finset.univ.filter fun x : T => x ∈ Subgroup.zpowers a).card = 3 := by
    have h3 : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
    exact h3
  have h4 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hnb), hcard3] at h4
  omega

theorem mk_primeComplementCore_injOn_of_isPGroup_three {R H : Subgroup G} (hR3 : IsPGroup 3 R)
    {a b : H} (ha : (a : G) ∈ R) (hb : (b : G) ∈ R)
    (hab : QuotientGroup.mk' (primeComplementCore (G := H) 3) a =
      QuotientGroup.mk' (primeComplementCore (G := H) 3) b) : a = b :=
  eq_of_mk_eq_of_isPGroup Nat.prime_three (primeComplementCore (G := H) 3)
    (primeComplementCore_coprime (G := H) 3) (T := R.subgroupOf H) hR3.comap_subtype ha hb hab

theorem D1CaseTwoData3.conj_axis_eq_inv
    {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData3 3 P M H R Rbar) {Kb : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hKb : IsComponentOf Kb ⊤)
    {z : H} (hzR : (z : G) ∈ R) (hzKb : QuotientGroup.mk' (primeComplementCore (G := H) 3) z ∈
      Subgroup.centralizer (Kb : Set (H ⧸ primeComplementCore (G := H) 3)))
    {w : G} (hwR : w ∈ R) (hwo : orderOf w = 3) (hwz : w ∉ Subgroup.zpowers (z : G))
    (hwc : ∀ g ∈ R, Commute w g)
    (hΩR : ∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G))
    {t : H} (htK : QuotientGroup.mk' (primeComplementCore (G := H) 3) t ∈ Kb)
    (htinv : ∀ y ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ Kb,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) t * y *
        (QuotientGroup.mk' (primeComplementCore (G := H) 3) t)⁻¹ = y⁻¹)
    (hwt : (t : G) * w * (t : G)⁻¹ ∈ Subgroup.zpowers w) :
    (t : G) * w * (t : G)⁻¹ = w⁻¹ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hred := hd.cfg.red
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hRH : R ≤ H := hd.cfg.ext.le_H
  have hR3 : IsPGroup 3 R := hd.cfg.ext.isPGroup
  have hinj := fun {a b : H} (ha : (a : G) ∈ R) (hb : (b : G) ∈ R) (hab : π a = π b) =>
    mk_primeComplementCore_injOn_of_isPGroup_three hR3 ha hb hab
  obtain ⟨e, he, heo, heC⟩ :=
    exists_mem_sylow_inf_component hp hred.ne_two hred.core_eq_bot Rbar hKb
  have he3 : e ^ 3 = 1 := by
    have := pow_orderOf_eq_one e
    rwa [heo] at this
  have he1 : e ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at heo
    omega
  have hKbN : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤
      Subgroup.normalizer (Kb : Set (H ⧸ primeComplementCore (G := H) 3)) :=
    hred.sylow_le_normalizer_component hKb
  have hTcyc : IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ Kb :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) := hd.cyclic Kb hKb
  have hec : ∀ r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)), r * e * r⁻¹ = e := by
    intro r hr
    have hr' : r * e * r⁻¹ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ Kb :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hr (Subgroup.mem_inf.mp he).1)
        (Subgroup.inv_mem _ hr), (Subgroup.mem_normalizer_iff.mp (hKbN hr) e).mp
          (Subgroup.mem_inf.mp he).2⟩
    have hmem : r * e * r⁻¹ ∈ Subgroup.zpowers e := by
      have h1 := mem_zpowers_of_cyclic_of_orderOf_eq_three (a := (⟨e, he⟩ : ↥((Rbar : Subgroup
        (H ⧸ primeComplementCore (G := H) 3)) ⊓ Kb))) (b := ⟨r * e * r⁻¹, hr'⟩)
        (by rw [Subgroup.orderOf_mk]; exact heo)
        (Subtype.ext (by simp [conj_pow, he3]))
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨r, hr⟩
    have hrk : r ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact conj_eq_of_mem_zpowers_of_three_pow hrk he3 he1 hmem
  have heR : e ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :=
    (Subgroup.mem_inf.mp he).1
  have hgR : ∀ g : H, (g : G) ∈ R →
      π g ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    intro g hg
    rw [hd.cfg.rbar]
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  rw [hd.cfg.rbar] at heR
  obtain ⟨e₀, he₀R, he₀⟩ := Subgroup.mem_map.mp heR
  have he₀R' : (e₀ : G) ∈ R := he₀R
  have hcomm₀ : ∀ g : H, (g : G) ∈ R → e₀ * g = g * e₀ := by
    intro g hg
    have h1 : π g * e = e * π g := by
      have := hec (π g) (hgR g hg)
      calc π g * e = (π g * e * (π g)⁻¹) * π g := by group
        _ = e * π g := by rw [this]
    refine hinj (b := g * e₀) (R.mul_mem he₀R' hg) (R.mul_mem hg he₀R') ?_
    rw [map_mul, map_mul, he₀]
    exact h1.symm
  have he₀3 : (e₀ : G) ^ 3 = 1 := by
    have h1 : e₀ ^ 3 = 1 := by
      refine hinj (a := e₀ ^ 3) (b := 1) (R.pow_mem he₀R' 3) R.one_mem ?_
      rw [map_pow, he₀, map_one]
      exact he3
    simpa using congrArg Subtype.val h1
  have hΩe := hΩR (e₀ : G) he₀R' (fun h hh => by
      have := hcomm₀ ⟨h, hRH hh⟩ hh
      exact congrArg Subtype.val this) he₀3
  have hwzc : Commute w (z : G) := hwc (z : G) hzR
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hwzc).mp hΩe
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  set wH : H := ⟨w, hRH hwR⟩ with hwH
  have hee : e₀ = wH ^ a * z ^ b := Subtype.ext (by simpa [hwH] using huv.symm)
  have he_eq : e = π wH ^ a * π z ^ b := by
    rw [← he₀, hee, map_mul, map_zpow, map_zpow]
  set τ := π t with hτ
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hwt
  have hcH : t * wH * t⁻¹ = wH ^ c := Subtype.ext (by simpa [hwH] using hc.symm)
  have hτw : τ * π wH * τ⁻¹ = π wH ^ c := by
    rw [hτ, ← map_inv, ← map_mul, ← map_mul, hcH, map_zpow]
  have hτz : τ * π z * τ⁻¹ = π z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.mp hzKb τ htK
  have hwzH : Commute wH z := Subtype.ext (by simpa [hwH] using hwzc.eq)
  have hcomm : Commute (π wH) (π z) := hwzH.map π
  have hconj : τ * e * τ⁻¹ = π wH ^ (c * a) * π z ^ b := by
    have h1 : τ * e * τ⁻¹ = (τ * π wH ^ a * τ⁻¹) * (τ * π z ^ b * τ⁻¹) := by
      rw [he_eq]; group
    rw [h1, ← conj_zpow, ← conj_zpow, hτw, hτz, ← zpow_mul]
  have hinv := htinv e he
  rw [hconj] at hinv
  have hY : π (wH ^ (a + c * a) * z ^ (b + b)) = 1 := by
    rw [map_mul, map_zpow, map_zpow, zpow_add, zpow_add]
    have h1 : e * e⁻¹ = 1 := mul_inv_cancel e
    rw [← hinv] at h1
    have h2 : (π wH ^ a * π z ^ b) * (π wH ^ (c * a) * π z ^ b) =
        (π wH ^ a * π wH ^ (c * a)) * (π z ^ b * π z ^ b) := by
      have hc2 : Commute (π z ^ b) (π wH ^ (c * a)) := (hcomm.symm.zpow_zpow b (c * a))
      calc (π wH ^ a * π z ^ b) * (π wH ^ (c * a) * π z ^ b)
          = π wH ^ a * (π z ^ b * π wH ^ (c * a)) * π z ^ b := by group
        _ = π wH ^ a * (π wH ^ (c * a) * π z ^ b) * π z ^ b := by rw [hc2.eq]
        _ = (π wH ^ a * π wH ^ (c * a)) * (π z ^ b * π z ^ b) := by group
    rw [← h2, ← he_eq]
    exact h1
  have hY' : wH ^ (a + c * a) * z ^ (b + b) = 1 := by
    refine hinj (b := 1) ?_ R.one_mem (by rw [hY, map_one])
    exact R.mul_mem (R.zpow_mem hwR _) (R.zpow_mem hzR _)
  have hY'' : w ^ (a + c * a) * (z : G) ^ (b + b) = 1 := by
    simpa [hwH] using congrArg Subtype.val hY'
  have hbot : Subgroup.zpowers w ⊓ Subgroup.zpowers (z : G) = ⊥ :=
    zpowers_inf_eq_bot_of_not_mem' hp hwo hwz
  have hwpow : w ^ (a + c * a) = 1 := by
    have h1 : w ^ (a + c * a) = ((z : G) ^ (b + b))⁻¹ := eq_inv_of_mul_eq_one_left hY''
    have h2 : w ^ (a + c * a) ∈ Subgroup.zpowers w ⊓ Subgroup.zpowers (z : G) :=
      ⟨Subgroup.zpow_mem_zpowers _ _, by
        rw [h1]; exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _)⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact h2
  have h3dvd : (3 : ℤ) ∣ a + c * a := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := w) (i := a + c * a)).mpr hwpow
    rwa [hwo] at this
  have h3a : ¬ (3 : ℤ) ∣ a := by
    intro h3
    apply heC
    have hwa : w ^ a = 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := w) (i := a)).mp (by rw [hwo]; exact_mod_cast h3)
      exact this
    have he₀z : e₀ = z ^ b := by
      refine Subtype.ext ?_
      have := huv
      rw [hwa, one_mul] at this
      simpa using this.symm
    have : e = π z ^ b := by rw [← he₀, he₀z, map_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ hzKb b
  have h3c : (3 : ℤ) ∣ c + 1 := by
    have h1 : (3 : ℤ) ∣ (c + 1) * a := by
      have : a + c * a = (c + 1) * a := by ring
      rwa [this] at h3dvd
    rcases (Int.prime_three.dvd_mul).mp h1 with h | h
    · exact h
    · exact absurd h h3a
  have hwc1 : w ^ (c + 1) = 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := w) (i := c + 1)).mp (by rw [hwo]; exact_mod_cast h3c)
    exact this
  rw [← hc]
  rw [zpow_add_one] at hwc1
  exact eq_inv_of_mul_eq_one_left hwc1


end CFSG.LocalAnalysis.RankThreeTheoremC
