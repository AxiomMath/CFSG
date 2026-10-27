module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Action

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem barM_le_normalizer {M L P E : Subgroup G} (hEP : E ≤ P) (hPM : P ≤ M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    barM M E ≤ Subgroup.normalizer ((barM M L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rintro _ ⟨m, hm, rfl⟩
  exact mk_mem_normalizer_barM (hPM (hEP (Subgroup.mem_subgroupOf.mp hm)))
    (hPL (hEP (Subgroup.mem_subgroupOf.mp hm)))

theorem barM_inf_centralizer_eq_bot {M L P E : Subgroup G} (hEP : E ≤ P)
    (hfaith : P ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥) :
    barM M E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨m, hm, rfl⟩, hmC⟩
  have hmem : (m : G) ∈ P ⊓ ((Subgroup.centralizer (barM M L :
      Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map
      M.subtype := ⟨hEP (Subgroup.mem_subgroupOf.mp hm), ⟨m, hmC, rfl⟩⟩
  rw [hfaith] at hmem
  have : m = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem pow_eq_one_of_mem_barM {p : ℕ} {M E : Subgroup G} (hE : ∀ x ∈ E, x ^ p = 1) :
    ∀ y ∈ barM M E, y ^ p = 1 := by
  rintro _ ⟨m, hm, rfl⟩
  rw [← map_pow]
  have h : (m : G) ^ p = 1 := hE (m : G) (Subgroup.mem_subgroupOf.mp hm)
  have : m ^ p = 1 := Subtype.ext h
  rw [this, map_one]

theorem exists_noncomm_barM {M L P E : Subgroup G} (hEP : E ≤ P) (hPM : P ≤ M)
    (hfaith : P ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥)
    (hab : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) :
    ∃ a ∈ barM M E, ∃ b ∈ barM M E, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hne⟩ := hab
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have haM : a ∈ M := hPM (hEP ha)
  have hbM : b ∈ M := hPM (hEP hb)
  refine ⟨mk ⟨a, haM⟩, ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩,
    mk ⟨b, hbM⟩, ⟨⟨b, hbM⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, fun h => hne ?_⟩
  set c : ↥M := ⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹ with hc
  have hmk1 : mk c = 1 := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcE : (c : G) ∈ E := by
    have : (c : G) = a * b * a⁻¹ * b⁻¹ := rfl
    rw [this]
    exact E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
  have hmem : (c : G) ∈ P ⊓ ((Subgroup.centralizer (barM M L :
      Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap mk).map M.subtype :=
    ⟨hEP hcE, ⟨c, Subgroup.mem_comap.mpr (by rw [hmk1]; exact Subgroup.one_mem _), rfl⟩⟩
  rw [hfaith] at hmem
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h2, one_mul]

theorem exists_noncomm_of_center {p : ℕ} (hp : 2 ≤ p) {E : Subgroup G} {z : G}
    (hz : orderOf z = p) (hEcard : Nat.card E = p ^ 3)
    (hEZ : (Subgroup.center ↥E).map E.subtype = Subgroup.zpowers z) :
    ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center ↥E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon g g.2 x x.2)
  have h1 : Nat.card ↥((Subgroup.center ↥E).map E.subtype) = Nat.card ↥(Subgroup.center ↥E) :=
    Subgroup.card_map_of_injective E.subtype_injective
  rw [hEZ, Nat.card_zpowers, hz, htop, Subgroup.card_top, hEcard] at h1
  have h3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [pow_one] at h3
  omega

theorem not_dvd_index_barM_of_not_dvd {p : ℕ} {M L Y : Subgroup G} (hLM : L ≤ M)
    (h : ¬ p ∣ (Y.subgroupOf L).index) :
    ¬ p ∣ ((barM M Y).subgroupOf (barM M L)).index := by
  let f : ↥L →* ↥(barM M L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)).codRestrict (barM M L)
      (fun x => ⟨⟨x, hLM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  have hle : Y.subgroupOf L ≤ ((barM M Y).subgroupOf (barM M L)).comap f := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨⟨x, hLM x.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ hf] at hdvd
  exact fun h3 => h (h3.trans hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC
