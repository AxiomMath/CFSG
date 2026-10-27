module

public import CFSG.LocalAnalysis.Mason73.Fusion34b
public import CFSG.LocalAnalysis.Mason73.NotIsolated
public import CFSG.LocalAnalysis.Mason73.Powers
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_conj_of_isConj {ι : L4Model n →* G} {a b c : L4Model n} (hab : IsConj a b)
    {g : G} (hg : g * ι b * g⁻¹ = ι c) : ∃ g' : G, g' * ι a * g'⁻¹ = ι c := by
  obtain ⟨x, rfl⟩ := isConj_iff.1 hab
  refine ⟨g * ι x, ?_⟩
  rw [← hg, map_mul, map_mul, map_inv]
  group

theorem zT_mem_centralizer (hn : 2 ≤ n) (l : L4Model n) :
    zT (n := n) (by omega) ∈ centralizer {l} :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 (zT_mem_center hn) l).symm

theorem zT_mul_x1T (hn : 2 ≤ n) : zT (n := n) (by omega) * x1T (by omega) = y1T (by omega) := by
  rw [zT_eq, x1T_eq, y1T_eq, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem zT_mul_y1T (hn : 2 ≤ n) : zT (n := n) (by omega) * y1T (by omega) = x1T (by omega) := by
  rw [zT_eq, x1T_eq, y1T_eq, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem exists_conj_zT_of_conj (hn : 3 ≤ n) {ι : L4Model n →* G} (hS : IsSylowOf 2 ι.range ⊤)
    {l : L4Model n} {g : G} (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ k : G, k⁻¹ * ι l * k = ι (zT (by omega)) ∧
      ∀ c ∈ centralizer {l}, ∃ d : L4Model n, ι d = k⁻¹ * ι c * k := by
  obtain ⟨k, hkl, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup
    (isSylowOf_zT hn hS) (u := ι l) (h := g) (by rw [← hg]; group)
  refine ⟨k, hkl, fun c hc => ?_⟩
  have hcl : ι c ∈ (ι.range ⊓ centralizer {ι l} : Subgroup G) := by
    refine Subgroup.mem_inf.2 ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hc]
  obtain ⟨⟨d, hd⟩, -⟩ := Subgroup.mem_inf.1 (hk _ hcl)
  exact ⟨d, hd⟩

theorem conj_x1T_of_conj_zT_mem_A (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {l : L4Model n} (hl : l ∉ A n) {k : G}
    (hkl : k⁻¹ * ι l * k = ι (zT (by omega))) {e : L4Model n}
    (he : ι e = k⁻¹ * ι (zT (by omega)) * k) (heA : e ∈ A n) :
    ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)) := by
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  have hke : k * ι e * k⁻¹ = ι (zT (by omega)) := by rw [he]; group
  refine conj_x1T_of_conj_mem_A hn hι hS heA
    (mul_self_of_conj_eq hι hz2 (g := k⁻¹) (by rw [inv_inv, he])) ?_ ?_ hke
  · rintro rfl
    have h1 := orderOf_zT (n := n) (by omega)
    rw [← orderOf_injective ι hι, ← hke, map_one, mul_one, mul_inv_cancel, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  · rintro rfl
    apply hl
    have : ι l = ι (zT (n := n) (by omega)) := by
      rw [← hke, ← hkl]
      group
    rw [hι this]
    exact zT_mem_A _

theorem conj_x1T_of_conj_piT_s23 (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {l : L4Model n} (hπ : piT l = s23 ∨ piT l = s01) {g : G}
    (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ g' : G, g' * ι (x1T (by omega)) * g'⁻¹ = ι (zT (by omega)) := by
  obtain ⟨c, hc, hc4⟩ := exists_pow_four_eq_zT_of_piT_s23 hn hπ
  exact conj_x1T_of_fourth_power hn hι hS
    (not_mem_A_of_piT_ne (by rcases hπ with h | h <;> rw [h] <;> decide)) hc hc4 hg

theorem conj_x1T_of_conj_piT_zP (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hc0 : ∀ μ : L4Model n, piT μ = zP →
      ∃ c ∈ A n, c ∈ centralizer {μ} ∧ c * c = zT (by omega))
    (hM3 : ∀ b e : L4Model n, b * b ∉ A n → e ∈ centralizer {b} → e * e = 1 → e ≠ 1 →
      e = zT (by omega) ∨ e = b * b ∨ e = b * b * zT (by omega))
    {l : L4Model n} (hπ : piT l = zP) {g : G} (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ g' : G, g' * ι (x1T (by omega)) * g'⁻¹ = ι (zT (by omega)) := by
  have hlA : l ∉ A n := not_mem_A_of_piT_ne (by rw [hπ]; decide)
  obtain ⟨k, hkl, hk⟩ := exists_conj_zT_of_conj hn hS hg
  obtain ⟨e, he⟩ := hk _ (zT_mem_centralizer (by omega) l)
  by_cases heA : e ∈ A n
  · exact conj_x1T_of_conj_zT_mem_A hn hι hS hlA hkl he heA
  obtain ⟨c, hcA, hcl, hc2⟩ := hc0 l hπ
  obtain ⟨b, hb⟩ := hk c hcl
  have hbe : b * b = e := hι (by rw [map_mul, hb, he, ← hc2, map_mul]; group)
  have hxl : x1T (n := n) (by omega) ∈ centralizer {l} := by
    rw [Subgroup.mem_centralizer_singleton_iff, x1T_eq_omegaEl hn]
    refine ((comm_omegaEl_iff hn).2 ?_).symm
    rw [hπ]
    decide
  obtain ⟨f, hf⟩ := hk _ hxl
  have hx2 : x1T (n := n) (by omega) * x1T (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T (by omega)]
  have hf2 : f * f = 1 := mul_self_of_conj_eq hι hx2 (g := k⁻¹) (by rw [inv_inv, hf])
  have hf1 : f ≠ 1 := by
    rintro rfl
    have h1 := orderOf_x1T (n := n) (by omega)
    rw [← orderOf_injective ι hι, show ι (x1T (n := n) (by omega)) = 1 by
      rw [show ι (x1T (n := n) (by omega)) = k * (k⁻¹ * ι (x1T (by omega)) * k) * k⁻¹ by group,
        ← hf, map_one]; group, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hfb : f ∈ centralizer {b} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    have hxc : ι (x1T (n := n) (by omega)) * ι c = ι c * ι (x1T (by omega)) := by
      rw [← map_mul, ← map_mul, A_comm (x1T_mem_A _) hcA]
    rw [map_mul, map_mul, hf, hb]
    calc k⁻¹ * ι (x1T (by omega)) * k * (k⁻¹ * ι c * k) =
        k⁻¹ * (ι (x1T (by omega)) * ι c) * k := by group
      _ = k⁻¹ * (ι c * ι (x1T (by omega))) * k := by rw [hxc]
      _ = k⁻¹ * ι c * k * (k⁻¹ * ι (x1T (by omega)) * k) := by group
  rcases hM3 b f (hbe ▸ heA) hfb hf2 hf1 with h | h | h
  ·
    exact ⟨k⁻¹, by rw [inv_inv, ← hf, h]⟩
  ·
    exfalso
    apply x1T_ne_zT (n := n) (by omega)
    apply hι
    have : k⁻¹ * ι (x1T (n := n) (by omega)) * k = k⁻¹ * ι (zT (by omega)) * k := by
      rw [← hf, h, hbe, he]
    simpa using this
  ·
    exfalso
    apply hlA
    have h1 : k⁻¹ * ι (x1T (n := n) (by omega)) * k =
        k⁻¹ * ι (zT (by omega)) * k * (k⁻¹ * ι l * k) := by
      rw [← hf, h, hbe, map_mul, he, hkl]
    have h2 : ι (x1T (n := n) (by omega)) = ι (zT (by omega) * l) := by
      calc ι (x1T (n := n) (by omega)) = k * (k⁻¹ * ι (x1T (by omega)) * k) * k⁻¹ := by group
        _ = ι (zT (by omega) * l) := by rw [h1, map_mul]; group
    have hl' : l = (zT (n := n) (by omega))⁻¹ * x1T (by omega) := by
      rw [hι h2]
      group
    rw [hl']
    exact mul_mem (inv_mem (zT_mem_A _)) (x1T_mem_A _)

theorem conj_x1T_eq_of_mem_commutator (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) {l : L4Model n}
    (hx1 : x1T (by omega) ∈ ⁅centralizer {l}, centralizer {l}⁆) {k : G}
    (hk : ∀ c ∈ centralizer {l}, ∃ d : L4Model n, ι d = k⁻¹ * ι c * k) {e : L4Model n}
    (he : ι e = k⁻¹ * ι (zT (by omega)) * k) (hπe : piT e = tP) :
    k⁻¹ * ι (x1T (by omega)) * k = ι (x1T (by omega)) := by
  set φ : G →* G := (MulAut.conj k⁻¹).toMonoidHom with hφdef
  have hφ : ∀ x, φ x = k⁻¹ * x * k := fun x => by simp [φ]
  have hle : ((centralizer {l}).map ι).map φ ≤ (centralizer {e}).map ι := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := hk c hc
    refine ⟨d, ?_, by rw [hd, hφ]⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply hι
    have hcz : ι c * ι (zT (n := n) (by omega)) = ι (zT (by omega)) * ι c := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (zT_mem_center (by omega)) c]
    rw [map_mul, map_mul, hd, he]
    calc k⁻¹ * ι c * k * (k⁻¹ * ι (zT (by omega)) * k) =
        k⁻¹ * (ι c * ι (zT (by omega))) * k := by group
      _ = k⁻¹ * (ι (zT (by omega)) * ι c) * k := by rw [hcz]
      _ = k⁻¹ * ι (zT (by omega)) * k * (k⁻¹ * ι c * k) := by group
  have hmem : k⁻¹ * ι (x1T (n := n) (by omega)) * k ∈
      (⁅centralizer {e}, centralizer {e}⁆).map ι := by
    rw [Subgroup.map_commutator]
    have h1 : ι (x1T (n := n) (by omega)) ∈
        ⁅(centralizer {l}).map ι, (centralizer {l}).map ι⁆ := by
      rw [← Subgroup.map_commutator]
      exact ⟨_, hx1, rfl⟩
    have h2 : φ (ι (x1T (n := n) (by omega))) ∈
        (⁅(centralizer {l}).map ι, (centralizer {l}).map ι⁆).map φ := ⟨_, h1, rfl⟩
    rw [Subgroup.map_commutator, hφ] at h2
    exact Subgroup.commutator_mono hle hle h2
  obtain ⟨f, hf, hfx⟩ := hmem
  have hx2 : x1T (n := n) (by omega) * x1T (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T (by omega)]
  have hf2 : f * f = 1 := mul_self_of_conj_eq hι hx2 (g := k⁻¹) (by rw [inv_inv, hfx])
  have hf1 : f ≠ 1 := by
    rintro rfl
    have h1 := orderOf_x1T (n := n) (by omega)
    rw [← orderOf_injective ι hι, show ι (x1T (n := n) (by omega)) = 1 by
      rw [show ι (x1T (n := n) (by omega)) = k * (k⁻¹ * ι (x1T (by omega)) * k) * k⁻¹ by group,
        ← hfx, map_one]; group, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨m, π, hm, rfl⟩ := exists_eq_el e
  rw [piT_el] at hπe
  subst hπe
  rw [← hfx, eq_x1T_of_mem_commutator_centralizer hn hm hf hf1 hf2]

theorem conj_x1T_of_conj_piT_tP (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hc0 : ∀ μ : L4Model n, piT μ = zP →
      ∃ c ∈ A n, c ∈ centralizer {μ} ∧ c * c = zT (by omega))
    (hM3 : ∀ b e : L4Model n, b * b ∉ A n → e ∈ centralizer {b} → e * e = 1 → e ≠ 1 →
      e = zT (by omega) ∨ e = b * b ∨ e = b * b * zT (by omega))
    {l : L4Model n} (hπ : piT l = tP)
    (hx1 : x1T (by omega) ∈ ⁅centralizer {l}, centralizer {l}⁆)
    (hlx : IsConj (l * x1T (by omega)) l) {g : G} (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ g' : G, g' * ι (x1T (by omega)) * g'⁻¹ = ι (zT (by omega)) := by
  have hlA : l ∉ A n := not_mem_A_of_piT_ne (by rw [hπ]; decide)
  obtain ⟨k, hkl, hk⟩ := exists_conj_zT_of_conj hn hS hg
  obtain ⟨e, he⟩ := hk _ (zT_mem_centralizer (by omega) l)
  by_cases heA : e ∈ A n
  · exact conj_x1T_of_conj_zT_mem_A hn hι hS hlA hkl he heA
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  have hke : k * ι e * k⁻¹ = ι (zT (by omega)) := by rw [he]; group
  have he2 : e * e = 1 := mul_self_of_conj_eq hι hz2 (g := k⁻¹) (by rw [inv_inv, he])
  obtain ⟨g₁, hg₁⟩ := exists_conj_of_isConj hlx hg
  have key : ∀ y : L4Model n, k⁻¹ * ι (x1T (by omega)) * k = ι y →
      ∃ g' : G, g' * ι (zT (by omega) * y) * g'⁻¹ = ι (zT (by omega)) := by
    intro y hy
    refine ⟨g₁ * k, ?_⟩
    rw [← hg₁, map_mul, map_mul, ← hkl, ← hy]
    group
  rcases piT_eq_of_mul_self he2 with h | h | h | h | h | h
  · exact absurd (mem_A_iff.2 h) heA
  · exact conj_x1T_of_conj_piT_s23 hn hι hS (Or.inl h) hke
  · exact conj_x1T_of_conj_piT_s23 hn hι hS (Or.inr h) hke
  · exact conj_x1T_of_conj_piT_zP hn hι hS hc0 hM3 h hke
  ·
    obtain ⟨g₂, hg₂⟩ := key _ (conj_x1T_eq_of_mem_commutator hn hι hx1 hk he h)
    rw [zT_mul_x1T (by omega)] at hg₂
    exact exists_conj_of_isConj (isConj_y1T_x1T (by omega)).symm hg₂
  ·
    have hu : (uT (n := n) (by omega))⁻¹ = uT (by omega) :=
      inv_eq_of_mul_eq_one_right (uT_mul_self (by omega))
    have hιu : (ι (uT (n := n) (by omega)))⁻¹ = ι (uT (by omega)) := by rw [← map_inv, hu]
    have hk' : ∀ c ∈ centralizer {l}, ∃ d : L4Model n,
        ι d = (k * ι (uT (by omega)))⁻¹ * ι c * (k * ι (uT (by omega))) := by
      intro c hc
      obtain ⟨d, hd⟩ := hk c hc
      refine ⟨uT (by omega) * d * uT (by omega), ?_⟩
      rw [map_mul, map_mul, hd, mul_inv_rev, hιu]
      group
    have he' : ι (uT (by omega) * e * uT (by omega)) =
        (k * ι (uT (by omega)))⁻¹ * ι (zT (by omega)) * (k * ι (uT (by omega))) := by
      rw [map_mul, map_mul, he, mul_inv_rev, hιu]
      group
    have hπ' : piT (uT (n := n) (by omega) * e * uT (by omega)) = tP := by
      rw [map_mul, map_mul, h, piT_uT]
      decide
    have h1 := conj_x1T_eq_of_mem_commutator hn hι hx1 hk' he' hπ'
    have hu2 : ι (uT (n := n) (by omega)) * ι (uT (by omega)) = 1 := by
      rw [← map_mul, uT_mul_self (by omega), map_one]
    have h1' : ι (x1T (n := n) (by omega)) =
        ι (uT (by omega)) * (k⁻¹ * ι (x1T (by omega)) * k) * ι (uT (by omega)) := by
      calc ι (x1T (n := n) (by omega)) =
          (k * ι (uT (by omega)))⁻¹ * ι (x1T (by omega)) * (k * ι (uT (by omega))) := h1.symm
        _ = ι (uT (by omega)) * (k⁻¹ * ι (x1T (by omega)) * k) * ι (uT (by omega)) := by
          rw [mul_inv_rev, hιu]
          group
    have h2 : k⁻¹ * ι (x1T (by omega)) * k = ι (y1T (by omega)) := by
      calc k⁻¹ * ι (x1T (by omega)) * k = (ι (uT (by omega)) * ι (uT (by omega))) *
            (k⁻¹ * ι (x1T (by omega)) * k) * (ι (uT (by omega)) * ι (uT (by omega))) := by
            rw [hu2, one_mul, mul_one]
        _ = ι (uT (by omega)) *
            (ι (uT (by omega)) * (k⁻¹ * ι (x1T (by omega)) * k) * ι (uT (by omega))) *
              ι (uT (by omega)) := by group
        _ = ι (uT (by omega)) * ι (x1T (by omega)) * ι (uT (by omega)) := by rw [← h1']
        _ = ι (uT (by omega) * x1T (by omega) * (uT (by omega))⁻¹) := by
          rw [map_mul, map_mul, map_inv, hιu]
        _ = ι (y1T (by omega)) := by rw [uT_conj_x1T (by omega)]
    obtain ⟨g₂, hg₂⟩ := key _ h2
    rw [zT_mul_y1T (by omega)] at hg₂
    exact ⟨g₂, hg₂⟩

theorem conj_x1T_of_not_isolated (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hc0 : ∀ μ : L4Model n, piT μ = zP →
      ∃ c ∈ A n, c ∈ centralizer {μ} ∧ c * c = zT (by omega))
    (hM3 : ∀ b e : L4Model n, b * b ∉ A n → e ∈ centralizer {b} → e * e = 1 → e ≠ 1 →
      e = zT (by omega) ∨ e = b * b ∨ e = b * b * zT (by omega))
    (hx1t : x1T (by omega) ∈
      ⁅centralizer {tT (n := n) (by omega)}, centralizer {tT (n := n) (by omega)}⁆)
    (hx1tx : x1T (by omega) ∈ ⁅centralizer {txT n}, centralizer {txT n}⁆)
    (hz : ∃ g : G, g⁻¹ * ι (zT (by omega)) * g ∈ ι.range ∧
      g⁻¹ * ι (zT (by omega)) * g ≠ ι (zT (by omega))) :
    ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)) := by
  obtain ⟨g, ⟨l, hl⟩, hne⟩ := hz
  have hgl : g * ι l * g⁻¹ = ι (zT (by omega)) := by rw [hl]; group
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  have hl2 : l * l = 1 := mul_self_of_conj_eq hι hz2 (g := g⁻¹) (by rw [inv_inv, hl])
  have hl1 : l ≠ 1 := by
    rintro rfl
    have h1 := orderOf_zT (n := n) (by omega)
    rw [← orderOf_injective ι hι, ← hgl, map_one, mul_one, mul_inv_cancel, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  rcases isConj_rep hn hl1 hl2 with h | h | h | h | h | h | h | h | h
  ·
    exfalso
    apply hne
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hzc := Subgroup.mem_center_iff.1 (zT_mem_center (n := n) (by omega)) c
    have hlz : l = zT (by omega) := by
      calc l = c⁻¹ * (c * l * c⁻¹) * c := by group
        _ = c⁻¹ * (c * zT (by omega)) := by rw [hc, mul_assoc, hzc]
        _ = zT (by omega) := by group
    rw [← hl, hlz]
  · exact exists_conj_of_isConj h.symm hgl
  · exfalso
    obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact not_conj_w1T_zT hn hι hS g' hg'
  · obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact conj_x1T_of_conj_piT_s23 hn hι hS (Or.inl (piT_uT _)) hg'
  · obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact conj_x1T_of_conj_piT_s23 hn hι hS (Or.inl rfl) hg'
  · obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact conj_x1T_of_conj_piT_zP hn hι hS hc0 hM3 (piT_uvT _) hg'
  · obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact conj_x1T_of_conj_piT_zP hn hι hS hc0 hM3 rfl hg'
  · obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact conj_x1T_of_conj_piT_tP hn hι hS hc0 hM3 (piT_tT _) hx1t (isConj_tT_mul_x1T hn) hg'
  · obtain ⟨g', hg'⟩ := exists_conj_of_isConj h.symm hgl
    exact conj_x1T_of_conj_piT_tP hn hι hS hc0 hM3 rfl hx1tx (isConj_txT_mul_x1T hn) hg'

theorem conj_x1T_zT [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hc0 : ∀ μ : L4Model n, piT μ = zP →
      ∃ c ∈ A n, c ∈ centralizer {μ} ∧ c * c = zT (by omega))
    (hM3 : ∀ b e : L4Model n, b * b ∉ A n → e ∈ centralizer {b} → e * e = 1 → e ≠ 1 →
      e = zT (by omega) ∨ e = b * b ∨ e = b * b * zT (by omega))
    (hx1t : x1T (by omega) ∈
      ⁅centralizer {tT (n := n) (by omega)}, centralizer {tT (n := n) (by omega)}⁆)
    (hx1tx : x1T (by omega) ∈ ⁅centralizer {txT n}, centralizer {txT n}⁆) :
    ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)) :=
  conj_x1T_of_not_isolated hn hι (by rw [hS]; exact GHarris.isSylowOf_top S) hc0 hM3 hx1t hx1tx
    (exists_conj_zT_ne hn hι S hS)

end CFSG.LocalAnalysis.Mason73
