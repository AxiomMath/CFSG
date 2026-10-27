module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AOdd2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AOdd1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_conj_mem {X N : Subgroup G} (hXN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    X ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hXN g hg h, fun hh => ?_⟩
  have := hXN g⁻¹ (X.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem mem_sup_cover {N : Subgroup G} (Y : Subgroup G) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    {y : G} : y ∈ Y ⊔ N ↔ ∃ c ∈ Y, ∃ u ∈ N, c * u = y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Y N hYN]
  exact Set.mem_mul

theorem cover_normal [Fact (Nat.Prime 2)] {X N : Subgroup G}
    (hNX : N ≤ X) (hXN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (P : Sylow 2 ↥N) :
    ∀ g ∈ X, ∀ y ∈ (X ⊓ Subgroup.centralizer (((P : Subgroup ↥N).map N.subtype : Subgroup G) :
        Set G)) ⊔ N,
      g * y * g⁻¹ ∈ (X ⊓ Subgroup.centralizer (((P : Subgroup ↥N).map N.subtype : Subgroup G) :
        Set G)) ⊔ N := by
  set Ts : Subgroup G := (P : Subgroup ↥N).map N.subtype with hTs
  set Y : Subgroup G := X ⊓ Subgroup.centralizer (Ts : Set G) with hY
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) :=
    fun y hy => le_normalizer_of_conj_mem hXN hy.1
  intro g hg y hy
  obtain ⟨n, hn, hmn⟩ := exists_mul_mem_normalizer hXN P hg
  set m : G := n * g with hm
  have hmX : m ∈ X := X.mul_mem (hNX hn) hg
  have hmy : ∀ y ∈ Y ⊔ N, m * y * m⁻¹ ∈ Y ⊔ N := by
    intro y hy
    obtain ⟨c, hc, u, hu, rfl⟩ := (mem_sup_cover Y hYN).1 hy
    have hmc : m * c * m⁻¹ ∈ Y := by
      refine Subgroup.mem_inf.2 ⟨X.mul_mem (X.mul_mem hmX hc.1) (X.inv_mem hmX), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hmi : m⁻¹ ∈ Subgroup.normalizer (Ts : Set G) := Subgroup.inv_mem _ hmn
      have ht' : m⁻¹ * t * m ∈ Ts := by
        have := (Subgroup.mem_normalizer_iff.1 hmi t).1 ht
        simpa using this
      have h1 : (m⁻¹ * t * m) * c = c * (m⁻¹ * t * m) :=
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 _ ht'
      calc t * (m * c * m⁻¹) = m * ((m⁻¹ * t * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * t * m)) * m⁻¹ := by rw [h1]
        _ = (m * c * m⁻¹) * t := by group
    have hmu : m * u * m⁻¹ ∈ N := hXN m hmX u hu
    have : m * (c * u) * m⁻¹ = (m * c * m⁻¹) * (m * u * m⁻¹) := by group
    rw [this]
    exact (Y ⊔ N).mul_mem (Subgroup.mem_sup_left hmc) (Subgroup.mem_sup_right hmu)
  have h1 := hmy y hy
  have e : g * y * g⁻¹ = n⁻¹ * (m * y * m⁻¹) * n := by rw [hm]; group
  rw [e]
  have hnS : n ∈ Y ⊔ N := Subgroup.mem_sup_right hn
  exact (Y ⊔ N).mul_mem ((Y ⊔ N).mul_mem ((Y ⊔ N).inv_mem hnS) h1) hnS

theorem L_le_of_normal {L : Subgroup G} (hsimple : IsSimpleGroup (PQuot 3 L)) {Yh : Subgroup G}
    (hLY : ∀ l ∈ L, ∀ y ∈ Yh, l * y * l⁻¹ ∈ Yh) (hOL : GLAPPrimeCoreOf 3 L ≤ Yh)
    (hl₀ : ∃ l₀ : ↥L, (l₀ : G) ∈ Yh ∧ (QuotientGroup.mk l₀ : PQuot 3 L) ≠ 1) : L ≤ Yh := by
  set Wq : Subgroup (PQuot 3 L) :=
    (Yh.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hWq
  haveI : Wq.Normal := by
    refine ⟨fun q hq q' => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hq
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q'
    refine ⟨l' * w * l'⁻¹, ?_, ?_⟩
    · exact hLY l' l'.2 (w : G) hw
    · simp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Wq with h | h
  · exfalso
    obtain ⟨l₀, hl₀Y, hl₀1⟩ := hl₀
    have : (QuotientGroup.mk l₀ : PQuot 3 L) ∈ Wq := ⟨l₀, hl₀Y, rfl⟩
    rw [h] at this
    exact hl₀1 this
  · intro l hl
    have : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : PQuot 3 L) ∈ Wq := by rw [h]; trivial
    obtain ⟨w, hw, hwl⟩ := this
    have h1 := (mk_eq_iff L _ _).1 hwl
    have h2 : (w : G)⁻¹ * l ∈ Yh := hOL h1
    have : l = (w : G) * ((w : G)⁻¹ * l) := by group
    rw [this]
    exact Yh.mul_mem hw h2

namespace Ctx

variable {B : Subgroup G} {x : G} {L : Subgroup G}

theorem B_le_cover (hc : Ctx B x L) (F : TD4Rank (PQuot 3 L)) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hnon : ¬ InducesInnerMod 3 L b₀) {Yh : Subgroup G}
    (hN : GLAPPrimeCoreOf 3 (cx x) ≤ Yh) (hL : L ≤ Yh) (hx : x ∈ Yh) (hb₀Y : b₀ ∈ Yh) :
    B ≤ Yh := by
  intro b hb
  obtain ⟨l, j, hlj⟩ := hc.coset_dec F hb₀ hnon b hb
  set b' : G := b * b₀ ^ (-j) with hb'
  have hb'B : b' ∈ B := B.mul_mem hb (Subgroup.zpow_mem _ hb₀ _)
  have hb'N : b' ∈ Subgroup.normalizer (L : Set G) := hc.hBL hb'B
  have hρb' : rho L ⟨b', hb'N⟩ = rho L ⟨(l : G), Subgroup.le_normalizer l.2⟩ := by
    have e : (⟨b', hb'N⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨b, hc.hBL hb⟩ * ⟨b₀, hc.hBL hb₀⟩ ^ (-j) := Subtype.ext (by simp [hb'])
    rw [e, map_mul, map_zpow, hlj, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hlX : (l : G) ∈ cx x := hc.hLX l.2
  set w : G := (l : G)⁻¹ * b' with hw
  have hwN : w ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer l.2)) hb'N
  have hρw : rho L ⟨w, hwN⟩ = 1 := by
    have e : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨(l : G), Subgroup.le_normalizer l.2⟩⁻¹ * ⟨b', hb'N⟩ := rfl
    rw [e, map_mul, map_inv, hρb', inv_mul_cancel]
  have hwk : w ∈ centModSubgroup 3 L := (rho_eq_one_iff L hwN).1 hρw
  have hwX : w ∈ cx x := (cx x).mul_mem ((cx x).inv_mem hlX) (hc.hBcx hb'B)
  have hlb : (l : G) * w = b' := mul_inv_cancel_left _ _
  have hb'3 : b' ^ 3 = 1 := hc.hBel.2 b' hb'B
  have hl3 : (l : G) ^ 3 ∈ GLAPPrimeCoreOf 3 (cx x) := by
    have h1 : rho L ⟨b', hb'N⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨b', hb'N⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hb'3
      rw [this, map_one]
    rw [hρb', rho_inner, ← map_pow] at h1
    have h2 := mem_center_of_conj_eq_one h1
    rw [hc.hZ, Subgroup.mem_bot, ← QuotientGroup.mk_pow] at h2
    have h3 := (mk_eq_iff L (l ^ 3) 1).1 (by rw [QuotientGroup.mk_one]; exact h2)
    have h4 : ((l : G) ^ 3) ∈ GLAPPrimeCoreOf 3 L := by simpa using Subgroup.inv_mem _ h3
    exact hc.hOL h4
  have hw3 : w ^ 3 ∈ GLAPPrimeCoreOf 3 (cx x) := by
    set a : ↥(cx x) := ⟨(l : G), hlX⟩ with ha
    set w' : ↥(cx x) := ⟨w, hwX⟩ with hw'
    have hcomm : a * w' * a⁻¹ * w'⁻¹ ∈ GLAPPrimeCore 3 ↥(cx x) := by
      rw [← mem_core_iff]
      show (l : G) * w * (l : G)⁻¹ * w⁻¹ ∈ _
      have h := hwk.2 (l : G) l.2
      rw [commutatorElement_def] at h
      exact hc.hOL h
    have h1 : (a * w') ^ 3 ∈ GLAPPrimeCore 3 ↥(cx x) := by
      rw [← mem_core_iff]
      show ((l : G) * w) ^ 3 ∈ _
      rw [hlb, hb'3]
      exact Subgroup.one_mem _
    have h2 : a ^ 3 ∈ GLAPPrimeCore 3 ↥(cx x) := by
      rw [← mem_core_iff]
      exact hl3
    have := cube_mem_of_comm (GLAPPrimeCore 3 ↥(cx x)) hcomm h1 h2
    rw [← mem_core_iff] at this
    exact this
  obtain ⟨i, n, hn, hwin⟩ := hc.lemmaW hwX hwk hw3
  have hb'Y : b' ∈ Yh := by
    rw [← hlb, hwin]
    exact Yh.mul_mem (hL l.2) (Yh.mul_mem (Subgroup.zpow_mem _ hx i) (hN hn))
  have e : b = b' * b₀ ^ j := by rw [hb']; group
  rw [e]
  exact Yh.mul_mem hb'Y (Subgroup.zpow_mem _ hb₀Y j)

end Ctx

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
