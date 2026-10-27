module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylowBasic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

section General

variable {G : Type*} [Group G]

theorem ncyc_exists_mul_of_mem_sup {H K : Subgroup G} (hH : H ≤ normalizer (K : Set G)) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right H K hH] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem ncyc_mem_zpowers_of_orderOf_dvd {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (h : orderOf x ∣ orderOf y) : x ∈ zpowers y := by
  have hle : zpowers x ≤ zpowers y := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
    exact h
  exact hle (mem_zpowers x)

theorem ncyc_mem_zpowers_or_mem_zpowers {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hC : IsPGroup 2 C) (x y : C) : x ∈ zpowers y ∨ y ∈ zpowers x := by
  obtain ⟨α, hα⟩ := IsPGroup.iff_orderOf.mp hC x
  obtain ⟨β, hβ⟩ := IsPGroup.iff_orderOf.mp hC y
  rcases le_total α β with h | h
  · left
    exact ncyc_mem_zpowers_of_orderOf_dvd (by rw [hα, hβ]; exact Nat.pow_dvd_pow 2 h)
  · right
    exact ncyc_mem_zpowers_of_orderOf_dvd (by rw [hα, hβ]; exact Nat.pow_dvd_pow 2 h)

theorem ncyc_card_inf_centralizer_mul_le [Finite G] {T₁ U A₁ W : Subgroup G} {x : G}
    (hcomm : ∀ y ∈ T₁, ∀ u ∈ U, y * u = u * y) (hinf : T₁ ⊓ U ≤ A₁) (hA₁W : A₁ ≤ W)
    (hWT : W ≤ T₁) (hA₁U : A₁ ≤ U) (hxT : ∀ y ∈ T₁, x * y * x⁻¹ ∈ T₁)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hW : ∀ y ∈ T₁, y⁻¹ * (x * y * x⁻¹) ∈ A₁ → y ∈ W) :
    Nat.card ((T₁ ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card A₁ ≤
      Nat.card W * Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  set C := (T₁ ⊔ U) ⊓ centralizer ({x} : Set G) with hCdef
  have hT₁N : T₁ ≤ normalizer (U : Set G) := fun y hy =>
    mem_normalizer_iff.mpr fun u => by
      constructor
      · intro hu
        rw [hcomm y hy u hu, mul_inv_cancel_right]
        exact hu
      · intro hu
        have h1 := hcomm y hy _ hu
        have e : u = y * u * y⁻¹ := by
          calc u = y⁻¹ * ((y * u * y⁻¹) * y) := by group
            _ = y⁻¹ * (y * (y * u * y⁻¹)) := by rw [h1]
            _ = y * u * y⁻¹ := by group
        rw [e]
        exact hu
  have hWN : W ≤ normalizer (U : Set G) := hWT.trans hT₁N
  have hUnn : U ≤ normalizer (U : Set G) := le_normalizer
  have hCle : C ≤ W ⊔ U := by
    intro c hc
    obtain ⟨hcTU, hcx⟩ := mem_inf.mp hc
    obtain ⟨y, hy, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hT₁N hcTU
    have hxc : x * (y * u) * x⁻¹ = y * u := by
      have := mem_centralizer_singleton_iff.mp hcx
      calc x * (y * u) * x⁻¹ = (y * u) * x * x⁻¹ := by rw [this]
        _ = y * u := by group
    have hmem : y⁻¹ * (x * y * x⁻¹) ∈ A₁ := by
      apply hinf
      refine mem_inf.mpr ⟨mul_mem (inv_mem hy) (hxT y hy), ?_⟩
      have e : y⁻¹ * (x * y * x⁻¹) = u * (x * u * x⁻¹)⁻¹ := by
        have h1 : (x * y * x⁻¹) * (x * u * x⁻¹) = y * u := by
          rw [← hxc]; group
        calc y⁻¹ * (x * y * x⁻¹) = y⁻¹ * ((x * y * x⁻¹) * (x * u * x⁻¹)) * (x * u * x⁻¹)⁻¹ := by
              group
          _ = u * (x * u * x⁻¹)⁻¹ := by rw [h1]; group
      rw [e]
      exact mul_mem hu (inv_mem (hxU u hu))
    exact mul_mem (mem_sup_left (hW y hy hmem)) (mem_sup_right hu)
  have hCU : C ⊓ U = U ⊓ centralizer ({x} : Set G) := by
    ext z
    simp only [mem_inf, hCdef]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨mem_sup_right h1, h2⟩, h1⟩⟩
  have hCN : C ≤ normalizer (U : Set G) := by
    intro c hc
    exact (sup_le hT₁N hUnn) (mem_inf.mp hc).1
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hCN
  have h2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hWN
  have hWU : W ⊓ U = A₁ := le_antisymm
    (fun z hz => hinf (mem_inf.mpr ⟨hWT (mem_inf.mp hz).1, (mem_inf.mp hz).2⟩))
    (le_inf hA₁W hA₁U)
  rw [hWU] at h2
  have h3 : Nat.card (C ⊔ U : Subgroup G) ≤ Nat.card (W ⊔ U : Subgroup G) :=
    card_le_of_le (sup_le hCle le_sup_right)
  rw [hCU] at h1
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have key : Nat.card C * Nat.card A₁ * Nat.card U ≤
      Nat.card W * Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card U := by
    calc Nat.card C * Nat.card A₁ * Nat.card U
        = (Nat.card (C ⊔ U : Subgroup G) *
            Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G)) * Nat.card A₁ := by
          rw [h1]; ring
      _ ≤ (Nat.card (W ⊔ U : Subgroup G) *
            Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G)) * Nat.card A₁ := by
          gcongr
      _ = (Nat.card (W ⊔ U : Subgroup G) * Nat.card A₁) *
            Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) := by ring
      _ = Nat.card W * Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card U := by
          rw [h2]; ring
  exact Nat.le_of_mul_le_mul_right key hUpos

end General

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem pow_four_eq_one_of_mem_sup (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G}
    (hx : x ∈ szT₁ L T ⊔ zpowers t) : x ^ 4 = 1 := by
  obtain ⟨-, -, -, hsq, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hx
  have hyz : Commute y z :=
    commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy)
  have hy4 : y ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hA₁sq _ (hsq y hy)]
  have hz4 : z ^ 4 = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
    · exact one_pow 4
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h.sq_eq_one, one_pow]
  rw [hyz.mul_pow, hy4, hz4, one_mul]

theorem exists_pow_four_eq_one (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) : ∃ k : ℤ, (a ^ k * b) ^ 4 = 1 ∨ (b ^ k * a) ^ 4 = 1 := by
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨φ, hker, hcyc⟩ := h.exists_outHom_of_card_sylow hS2
  have hp : IsPGroup 2 φ.range :=
    h.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hcyc' : IsCyclic φ.range := hcyc
  rcases ncyc_mem_zpowers_or_mem_zpowers hp (φ.rangeRestrict ⟨a, ha⟩)
      (φ.rangeRestrict ⟨b, hb⟩) with hab | hba
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hab
    have hk' : φ ⟨b, hb⟩ ^ k = φ ⟨a, ha⟩ := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨-k, Or.inr (h.pow_four_eq_one_of_mem_sup hS2 ?_)⟩
    have h1 : φ ((⟨b, hb⟩ : T) ^ (-k) * ⟨a, ha⟩) = 1 := by
      rw [map_mul, map_zpow, ← hk', ← zpow_add, neg_add_cancel, zpow_zero]
    have := (hker _).mp h1
    simpa using this
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hba
    have hk' : φ ⟨a, ha⟩ ^ k = φ ⟨b, hb⟩ := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨-k, Or.inl (h.pow_four_eq_one_of_mem_sup hS2 ?_)⟩
    have h1 : φ ((⟨a, ha⟩ : T) ^ (-k) * ⟨b, hb⟩) = 1 := by
      rw [map_mul, map_zpow, ← hk', ← zpow_add, neg_add_cancel, zpow_zero]
    have := (hker _).mp h1
    simpa using this

theorem false_of_conj_of_pow_four (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {g : G} {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizer ({g⁻¹ * t * g} : Set G)) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) (hab : ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := h.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  set P' := P.map (MulAut.conj g).toMonoidHom with hP'
  have hP'C : P' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hpc := mem_centralizer_singleton_iff.mp (hPC hp)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * p * g⁻¹ * t = g * (p * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * p) * g⁻¹ := by rw [hpc]
      _ = t * (g * p * g⁻¹) := by group
  have hP'p : IsPGroup 2 P' := hP.map _
  obtain ⟨c, -, hc⟩ := exists_conj_mem_of_isSylowOf hTsyl hP'C hP'p
  set ψ := MulAut.conj (c⁻¹ * g) with hψdef
  have hψ : ∀ x : G, c⁻¹ * ((MulAut.conj g).toMonoidHom x) * c = ψ x := by
    intro x
    simp only [hψdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have haT := hc _ ⟨a, ha, rfl⟩
  have hbT := hc _ ⟨b, hb, rfl⟩
  rw [hψ] at haT hbT
  obtain ⟨k, hk⟩ := h.exists_pow_four_eq_one hS2 haT hbT
  rcases hk with hk | hk
  · apply (hab k).1
    rw [← map_zpow, ← map_mul, ← map_pow] at hk
    exact (MulEquiv.map_eq_one_iff ψ).mp hk
  · apply (hab k).2
    rw [← map_zpow, ← map_mul, ← map_pow] at hk
    exact (MulEquiv.map_eq_one_iff ψ).mp hk

theorem exists_W_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) :
    ∃ W : Subgroup G, W ≤ szT₁ L T ∧ szA₁ (szT₁ L T) ≤ W ∧ Nat.card W = (2 ^ f) ^ 2 ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ (∀ y ∈ W, w * y * w⁻¹ = y⁻¹) ∧
      (∀ z ∈ szA₁ (szT₁ L T), ∃ y ∈ W, y * y = z) ∧
      ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  have hout := (h.outer_facts_of_card_sylow hS2 hwT hw2 hwS).1
  set σ := L.normalizerMonoidHom ⟨w, h.le_normalizer hwT⟩ with hσdef
  have hσ : ∀ y : L, ((σ y : L) : G) = w * y * w⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hww : w * w = 1 := by rw [← sq, hw2]
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hσ, hσ]
    calc w * (w * (y : G) * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
      _ = y := by rw [hww]; group
  have hσout : ¬ ∃ g : L, ∀ y : L, σ y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hσ] at this
    simpa using this
  have hσQ : ∀ y ∈ (Q : Subgroup L), σ y ∈ (Q : Subgroup L) := by
    intro y hy
    rw [hmemQ, hσ]
    exact (mem_normalizer_iff.mp (hTN₁ hwT) y).mp ((hmemQ y).mp hy)
  obtain ⟨hWQ, hZW, hWcard, hWc, hWinv, -, -, hWsq, hiff⟩ :=
    hB.lemma_3_4_d5_unitary Q σ hσσ hσout hσQ
  refine ⟨(commutatorAut (Q : Subgroup L) σ).map L.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hmemQ y).mp (hWQ hy)
  · intro a ha
    have haL : a ∈ L := szT₁_le_right L T (szA₁_le _ ha)
    exact ⟨⟨a, haL⟩, hZW ((hmemZ ⟨a, haL⟩).mpr ha), rfl⟩
  · rw [card_map_of_injective L.subtype_injective, hWcard]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hWc x hx y hy)
  · rintro _ ⟨y, hy, rfl⟩
    have := congrArg Subtype.val (hWinv y hy)
    rw [hσ] at this
    simpa using this
  · intro z hz
    have hzL : z ∈ L := szT₁_le_right L T (szA₁_le _ hz)
    obtain ⟨y, hy, hyz⟩ := hWsq ⟨z, hzL⟩ ((hmemZ ⟨z, hzL⟩).mpr hz)
    exact ⟨y, ⟨y, hy, rfl⟩, by simpa using congrArg Subtype.val hyz⟩
  · intro y hy
    have hyL : y ∈ L := szT₁_le_right L T hy
    have e : y⁻¹ * (w * y * w⁻¹) = ((⟨y, hyL⟩ : L)⁻¹ * σ ⟨y, hyL⟩ : L) := by
      rw [coe_mul, hσ]
      rfl
    rw [e, ← hmemZ, hiff ⟨y, hyL⟩ ((hmemQ _).mpr hy)]
    constructor
    · intro hm
      exact ⟨⟨y, hyL⟩, hm, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      have : y' = ⟨y, hyL⟩ := Subtype.ext hyy'
      rw [← this]
      exact hy'

end U3Start

end CFSG.SeitzReduction.RankOne
