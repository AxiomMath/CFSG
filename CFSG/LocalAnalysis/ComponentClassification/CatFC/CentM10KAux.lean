module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Unpack
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedReduction

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint

theorem mem_sup_zpowers_of_commute {G : Type*} [Group G] (D : Subgroup G) (z : G)
    (hc : ∀ d ∈ D, d * z = z * d) {x : G} (hx : x ∈ D ⊔ zpowers z) :
    ∃ d ∈ D, ∃ n : ℤ, x = d * z ^ n := by
  have hcomm : ∀ d ∈ D, ∀ n : ℤ, z ^ n * d = d * z ^ n := fun d hd n =>
    ((show Commute d z from hc d hd).zpow_right n).symm.eq
  let S₀ : Subgroup G :=
    { carrier := {x | ∃ d ∈ D, ∃ n : ℤ, x = d * z ^ n}
      mul_mem' := by
        rintro _ _ ⟨d₁, hd₁, n, rfl⟩ ⟨d₂, hd₂, m, rfl⟩
        refine ⟨d₁ * d₂, D.mul_mem hd₁ hd₂, n + m, ?_⟩
        calc d₁ * z ^ n * (d₂ * z ^ m) = d₁ * (z ^ n * d₂) * z ^ m := by simp only [mul_assoc]
          _ = d₁ * (d₂ * z ^ n) * z ^ m := by rw [hcomm d₂ hd₂ n]
          _ = d₁ * d₂ * z ^ (n + m) := by rw [zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨1, D.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨d, hd, n, rfl⟩
        refine ⟨d⁻¹, D.inv_mem hd, -n, ?_⟩
        rw [mul_inv_rev, ← zpow_neg]
        exact hcomm d⁻¹ (D.inv_mem hd) (-n) }
  have hle : D ⊔ zpowers z ≤ S₀ := by
    refine sup_le ?_ ?_
    · intro d hd
      exact ⟨d, hd, 0, by simp⟩
    · rw [zpowers_le]
      exact ⟨1, D.one_mem, 1, by simp⟩
  obtain ⟨d, hd, n, rfl⟩ := hle hx
  exact ⟨d, hd, n, rfl⟩

theorem M10Cfg.inv_mem_D {K : Type} [Group K] [Finite K] {S D : Subgroup K} {z : K}
    (cfg : M10Cfg S D z) (hzS : z ∉ S) {k : K} (hkS : k ∈ S)
    (hkC : k ∈ centralizer ({z} : Set K)) (hk2 : k * k = 1) : k ∈ D := by
  have hcD : ∀ d ∈ D, d * z = z * d := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mp (cfg.hDC hd)
  have hkk : k * k ∈ zpowers z := by
    rw [hk2]
    exact one_mem _
  obtain ⟨d, hd, n, hkdn⟩ := mem_sup_zpowers_of_commute D z hcD (cfg.hinv k hkC hkk)
  have hzn : z ^ n ∈ S := by
    have h : z ^ n = d⁻¹ * k := by
      rw [hkdn, inv_mul_cancel_left]
    rw [h]
    exact S.mul_mem (S.inv_mem (cfg.hDS hd)) hkS
  have hz2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    have h := pow_orderOf_eq_one z
    rwa [cfg.hz] at h
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  ·
    rw [hkdn, zpow_mul, hz2, one_zpow, mul_one]
    exact hd
  ·
    exfalso
    have hzz : z ^ (2 * m + 1) = z := by
      rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]
    rw [hzz] at hzn
    exact hzS hzn

theorem M10Cfg.no_order_six {K : Type} [Group K] [Finite K] {S D : Subgroup K} {z : K}
    (cfg : M10Cfg S D z) (hzS : z ∉ S) : ∀ g ∈ S, g * z = z * g → orderOf g ≠ 6 := by
  obtain ⟨F, hF⟩ : ∃ F : Subgroup K, F = S ⊓ centralizer ({z} : Set K) := ⟨_, rfl⟩
  have hFmem : ∀ x : K, x ∈ F ↔ x ∈ S ∧ x ∈ centralizer ({z} : Set K) := by
    intro x
    rw [hF, Subgroup.mem_inf]
  have hFS : F ≤ S := by
    intro x hx
    exact ((hFmem x).mp hx).1
  have hFC : F ≤ centralizer ({z} : Set K) := by
    intro x hx
    exact ((hFmem x).mp hx).2
  have hDF : D ≤ F := by
    intro x hx
    exact (hFmem x).mpr ⟨cfg.hDS hx, cfg.hDC hx⟩
  have hzC : z ∈ centralizer ({z} : Set K) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hFne : Nat.card F ≠ 1440 := by
    intro h
    have heq : F = centralizer ({z} : Set K) :=
      Subgroup.eq_of_le_of_card_ge hFC (le_of_eq (cfg.hcard.trans h.symm))
    have hzF : z ∈ F := by
      rw [heq]
      exact hzC
    exact hzS ((hFmem z).mp hzF).1
  have hdvd : Nat.card F ∣ 1440 := by
    rw [← cfg.hcard]
    exact Subgroup.card_dvd_of_le hFC
  have hFcard : Nat.card F ≤ 720 := by
    obtain ⟨q, hq⟩ := hdvd
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · interval_cases q <;> omega
    · nlinarith [Nat.mul_le_mul (le_refl (Nat.card F)) hq2]
  have hDnorm : (D.subgroupOf F).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := cfg.hDn (g : K) (hFC g.2) _ hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hDA' : Nonempty (↥(D.subgroupOf F) ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨φ⟩ := cfg.hDA
    exact ⟨(Subgroup.subgroupOfEquivOfLe hDF).trans φ⟩
  have hinvF : ∀ x : ↥F, orderOf x = 2 → x ∈ D.subgroupOf F := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx2 : x * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx, pow_two] at h
      exact h
    have hK : (x : K) * (x : K) = 1 := by
      have h := congrArg Subtype.val hx2
      simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h
    exact cfg.inv_mem_D hzS (hFS x.2) (hFC x.2) hK
  have hno := CFSG.ComponentClassification.CatFC.no_order_six (D.subgroupOf F) hDA' hFcard hinvF
  intro g hgS hgz hg6
  have hgF : g ∈ F := (hFmem g).mpr ⟨hgS, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
  exact hno ⟨g, hgF⟩ ((Subgroup.orderOf_mk g hgF).trans hg6)

theorem noInnerZ2_of_cat {A : Type} [Group A]
    (hZ : CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 A) : NoInnerZ2 A := by
  intro S _ _ _ hnab hcat z hz
  have hsimpleTop : IsSimpleGroup ↥(⊤ : Subgroup S) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  have hcatTop : CFSG.Blueprint.Catalog ↥(⊤ : Subgroup S) :=
    CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv hcat
  have hcent : Subgroup.centralizer ((⊤ : Subgroup S) : Set S) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center S := by
        rw [hc]
        exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  exact hZ S ⊤ inferInstance hsimpleTop hcatTop hcent z hz

end CFSG.ComponentClassification.CatFC
