module

public import CFSG.ClassicalInvolution.SmallCases.NDBTA2
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.Asc77.AscAETCyc
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.ClassicalInvolution.Asc77.AscT7K11
public import CFSG.ClassicalInvolution.Asc77.AscT7L1
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model

public section

namespace CFSG.ClassicalInvolution.NDB.TA

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mul_comm_of_isCyclic {C : Subgroup G} (hC : IsCyclic ↥C) {a b : G} (ha : a ∈ C)
    (hb : b ∈ C) : a * b = b * a := by
  have := hC
  exact congrArg Subtype.val (IsCyclic.commGroup.mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)

omit [Finite G] in
theorem comm_of_conj_comm {x y e : G} (hx : x * e = e * x)
    (h : (x * y * x⁻¹) * e = e * (x * y * x⁻¹)) : y * e = e * y := by
  have hx' : x⁻¹ * e = e * x⁻¹ := by
    calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * e) * x⁻¹ := by rw [hx]
      _ = e * x⁻¹ := by group
  calc y * e = x⁻¹ * (x * y * x⁻¹) * (x * e) := by group
    _ = x⁻¹ * (x * y * x⁻¹) * (e * x) := by rw [hx]
    _ = x⁻¹ * ((x * y * x⁻¹) * e) * x := by group
    _ = x⁻¹ * (e * (x * y * x⁻¹)) * x := by rw [h]
    _ = (x⁻¹ * e) * (x * y * x⁻¹) * x := by group
    _ = (e * x⁻¹) * (x * y * x⁻¹) * x := by rw [hx']
    _ = e * y := by group

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {J : Subgroup G} {l x : G}
    (hxJ : x ∈ Subgroup.normalizer (J : Set G)) (hxl : x * l = l * x) :
    x ∈ Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({l} : Set G) : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hxJ, Subgroup.le_normalizer
    (Subgroup.mem_centralizer_singleton_iff.mpr hxl)⟩

theorem mem_trivialOnQuot_of_centralizes_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) {x : G}
    (hx2 : x * x = 1) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxR : ∀ r ∈ R, r * x = x * r) : x ∈ trivialOnQuot L := by
  have hV2 : IsPGroup 2 (Subgroup.zpowers x) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hx2
  have hVL : ∀ y ∈ Subgroup.zpowers x, conjSub y L = L := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr hxL hy)
  have hVR : ∀ r ∈ R, ∀ v ∈ Subgroup.zpowers x, r * v = v * r := by
    intro r hr v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_right (hxR r hr) k)).eq
  have h := centSylow hp hq hΩ hL hR hV2 hVL hVR
  exact ⟨hxL, fun k hk => h k hk x (Subgroup.mem_zpowers x)⟩

theorem comm_of_index_two {R C : Subgroup G} (hCR : C ≤ R) (hcard : Nat.card R = 2 * Nat.card C)
    {w x : G} (hwR : w ∈ R) (hwC : w ∉ C) (hxw : w * x = x * w)
    (hxC : ∀ c ∈ C, c * x = x * c) : ∀ r ∈ R, r * x = x * r := by
  intro r hr
  by_cases hrC : r ∈ C
  · exact hxC r hrC
  · have hc := inv_mul_mem_of_index_two hCR hcard hwR hr hwC hrC
    have e : r = w * (w⁻¹ * r) := by group
    rw [e]
    calc w * (w⁻¹ * r) * x = w * ((w⁻¹ * r) * x) := by group
      _ = w * (x * (w⁻¹ * r)) := by rw [hxC _ hc]
      _ = (w * x) * (w⁻¹ * r) := by group
      _ = (x * w) * (w⁻¹ * r) := by rw [hxw]
      _ = x * (w * (w⁻¹ * r)) := by group

theorem torus_pin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {L J : Subgroup G}
    {l e₀ e₁ : G} (hL : L ∈ Ω) (hJ : J ∈ Ω) (hl : IsUniqueInvolution L l)
    (he₀ : IsUniqueInvolution J e₀) (hne : l ≠ e₀) (he₀l : e₀ * l = l * e₀)
    (he₁l : e₁ * l = l * e₁) (he₁e₀ : e₁ * e₀ = e₀ * e₁) (he₁2 : e₁ * e₁ = 1)
    (he₁J : e₁ ∈ trivialOnQuot J)
    (hCl : Subgroup.centralizer ({l} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hCe₀ : Subgroup.centralizer ({e₀} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {W : Subgroup G} (hWL : W ≤ L) (hW2 : IsPGroup 2 W) (hlW : l ∈ W)
    (hWc : W ≤ Subgroup.centralizer ({e₀} : Set G)) (hW4 : 4 ≤ Nat.card W) :
    e₀ ∈ trivialOnQuot L ∨ e₁ ∈ trivialOnQuot L ∨ e₀ * e₁ ∈ trivialOnQuot L := by
  classical
  have hPair : Pair Ω L J l e₀ := ⟨hL, hJ, hl, he₀, hne⟩
  have he₀N : e₀ ∈ Subgroup.normalizer (L : Set G) :=
    hCl (Subgroup.mem_centralizer_singleton_iff.mpr he₀l)
  have he₁N : e₁ ∈ Subgroup.normalizer (L : Set G) :=
    hCl (Subgroup.mem_centralizer_singleton_iff.mpr he₁l)
  obtain ⟨-, RJ, hRJ, -, hU4J, -, -, hdichJ⟩ := hPair.bootstrap hp hq hΩ hWL hW2 hlW hWc hW4
  have he₁NJ : Subgroup.zpowers e₁ ≤
      Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({l} : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_inf_centralizer he₁J.1 he₁l)
  obtain ⟨V₀, hV₀, hV₀inv⟩ :=
    AscL62.exists_sylow_normalized (ExactLayer.isPGroup_zpowers_of_sq_eq_one he₁2) he₁NJ
  have hV₀J : V₀ ≤ J := hV₀.1.trans inf_le_left
  have hV₀c : V₀ ≤ Subgroup.centralizer ({l} : Set G) := hV₀.1.trans inf_le_right
  have hV₀2 : IsPGroup 2 V₀ := hV₀.2.1
  have hV₀4 : 4 ≤ Nat.card V₀ :=
    le_trans hU4J (hV₀.natCard_le hRJ.2.1.to_inf_left (inf_le_inf_right _ hRJ.1))
  have he₀V₀ : e₀ ∈ V₀ := mem_of_uniqueInvolution_of_pGroup he₀ hV₀J hV₀2 (by omega)
  have he₁V₀ : ∀ v ∈ V₀, e₁ * v = v * e₁ := by
    have h := AscAET.le_centralizer_of_conjSub_eq he₁J hV₀J hV₀2
      (hV₀inv e₁ (Subgroup.mem_zpowers e₁))
    intro v hv
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h hv)).symm
  have hA2 : IsPGroup 2 ↥(V₀ ⊔ Subgroup.zpowers e₁) := by
    refine Lift.isPGroup_sup_of_commute hV₀2 (ExactLayer.isPGroup_zpowers_of_sq_eq_one he₁2) ?_
    intro v hv y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (he₁V₀ v hv).symm k)).eq
  have hAN : V₀ ⊔ Subgroup.zpowers e₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun v hv => hCl (hV₀c hv)) (Subgroup.zpowers_le.mpr he₁N)
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hA2 hAN
  have hRV₀ : ∀ y ∈ V₀, conjSub y R = R := fun y hy =>
    hRinv y ((le_sup_left : V₀ ≤ V₀ ⊔ Subgroup.zpowers e₁) hy)
  have hRe₁ : conjSub e₁ R = R :=
    hRinv e₁ ((le_sup_right : Subgroup.zpowers e₁ ≤ V₀ ⊔ Subgroup.zpowers e₁)
      (Subgroup.mem_zpowers e₁))
  have hcfg : CoreCfg R V₀ l e₀ := hPair.coreCfg hp hΩ hR hV₀2 hV₀J he₀V₀ hRV₀
  have hV₀ne : V₀ ≠ Subgroup.zpowers e₀ := by
    intro h
    have h2 : Nat.card (Subgroup.zpowers e₀) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact he₀.sq) he₀.ne_one
    rw [h, h2] at hV₀4
    omega
  have hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({e₀} : Set G), ∀ v ∈ V₀, u * v = v * u :=
    fun u hu v hv => hPair.comm_of_normalizes hR.1 hR.2.1 hV₀J hRV₀ hu.1 (hCe₀ hu.2) hv
  have hRRJ : Nat.card R = Nat.card RJ := hPair.natCard_sylow_eq hΩ hR hRJ
  rcases hcfg.core_dichotomy hV₀ne hcomm with hUR | ⟨C, hUC, hCR, hCc, hCcard, hCinv, -, hVC,
    -, -⟩
  ·
    left
    refine mem_trivialOnQuot_of_centralizes_sylow hp hq hΩ hL hR he₀.sq he₀N fun r hr => ?_
    have h := (SetLike.ext_iff.mp hUR r).mpr hr
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hVCeq : Nat.card V₀ = Nat.card C := by
    have h0 : 0 < Nat.card C := Nat.card_pos
    rcases hdichJ with hUJR | ⟨CJ, hUCJ, -, -, hCJcard, -⟩
    · exfalso
      have hRJc : RJ ≤ Subgroup.centralizer ({l} : Set G) := fun r hr =>
        ((SetLike.ext_iff.mp hUJR r).mpr hr).2
      have h1 : Nat.card RJ ≤ Nat.card V₀ := hV₀.natCard_le hRJ.2.1 (le_inf hRJ.1 hRJc)
      omega
    · have hCJle : CJ ≤ J ⊓ Subgroup.centralizer ({l} : Set G) := by
        rw [← hUCJ]
        exact inf_le_inf_right _ hRJ.1
      have hCJ2 : IsPGroup 2 CJ := by
        rw [← hUCJ]
        exact hRJ.2.1.to_inf_left
      have h1 : Nat.card CJ ≤ Nat.card V₀ := hV₀.natCard_le hCJ2 hCJle
      omega
  have hCmem : ∀ c ∈ C, c ∈ R ⊓ Subgroup.centralizer ({e₀} : Set G) := fun c hc => by
    rw [hUC]
    exact hc
  obtain ⟨w, hwR, hwC⟩ : ∃ w ∈ R, w ∉ C := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show R ≤ C from hcon)
    have h0 : 0 < Nat.card C := Nat.card_pos
    omega
  have hcommC : ∀ c ∈ C, ∀ v ∈ V₀, c * v = v * c := fun c hc v hv =>
    hcomm c (hCmem c hc) v hv
  obtain ⟨φ, hφ⟩ := hcfg.exists_phi hCR hCcard hCinv hcommC hwR hwC
  have hinj := hcfg.phi_injective hCR hCcard hcommC hUC hwR hwC φ hφ
  have hsurj : Function.Surjective φ := (hinj.bijective_of_nat_card_le hVCeq.symm.le).2
  have hCe₀ : ∀ c ∈ C, c * e₀ = e₀ * c := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mp (hCmem c hc).2
  have e1 : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁2
  have he₁w : e₁ * w * e₁⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := e₁) hwR
    rwa [hRe₁] at this
  have he₁wC : e₁ * w * e₁⁻¹ ∉ C := by
    intro hc
    apply hwC
    rw [← hUC]
    exact ⟨hwR, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_conj_comm he₁e₀ (hCe₀ _ hc))⟩
  set u₁ : G := w⁻¹ * (e₁ * w * e₁⁻¹) with hu₁def
  have hu₁C : u₁ ∈ C := inv_mul_mem_of_index_two hCR hCcard hwR he₁w hwC he₁wC
  have hw₁ : e₁ * w * e₁⁻¹ = w * u₁ := by rw [hu₁def]; group
  have he₁φ : ∀ v : ↥V₀, e₁ * (φ v : G) = (φ v : G) * e₁ := by
    intro v
    set φv : G := (φ v : G) with hφvdef
    have hφv : φv = w⁻¹ * ((v : G) * w * (v : G)⁻¹) := hφ v
    have hv : e₁ * (v : G) * e₁⁻¹ = v := by rw [he₁V₀ v v.2]; group
    have hcu : u₁ * (v : G)⁻¹ = (v : G)⁻¹ * u₁ := by
      have h1 := hcommC u₁ hu₁C v v.2
      calc u₁ * (v : G)⁻¹ = (v : G)⁻¹ * ((v : G) * u₁) * (v : G)⁻¹ := by group
        _ = (v : G)⁻¹ * (u₁ * (v : G)) * (v : G)⁻¹ := by rw [h1]
        _ = (v : G)⁻¹ * u₁ := by group
    have hab : φv * u₁ = u₁ * φv := mul_comm_of_isCyclic hCc (φ v).2 hu₁C
    have key : e₁ * φv * e₁⁻¹ = φv := by
      have step1 : e₁ * φv * e₁⁻¹ = (e₁ * w * e₁⁻¹)⁻¹ * (e₁ * (v : G) * e₁⁻¹) *
          (e₁ * w * e₁⁻¹) * (e₁ * (v : G) * e₁⁻¹)⁻¹ := by
        rw [hφv]
        group
      have step2 : (w * u₁)⁻¹ * (v : G) * (w * u₁) * (v : G)⁻¹ = u₁⁻¹ * φv * u₁ := by
        rw [hφv]
        calc (w * u₁)⁻¹ * (v : G) * (w * u₁) * (v : G)⁻¹ =
            u₁⁻¹ * w⁻¹ * (v : G) * w * (u₁ * (v : G)⁻¹) := by group
          _ = u₁⁻¹ * w⁻¹ * (v : G) * w * ((v : G)⁻¹ * u₁) := by rw [hcu]
          _ = u₁⁻¹ * (w⁻¹ * ((v : G) * w * (v : G)⁻¹)) * u₁ := by group
      rw [step1, hw₁, hv, step2]
      calc u₁⁻¹ * φv * u₁ = u₁⁻¹ * (φv * u₁) := by group
        _ = u₁⁻¹ * (u₁ * φv) := by rw [hab]
        _ = φv := by group
    calc e₁ * φv = (e₁ * φv * e₁⁻¹) * e₁ := by group
      _ = φv * e₁ := by rw [key]
  have he₁C : ∀ c ∈ C, c * e₁ = e₁ * c := by
    intro c hc
    obtain ⟨v, hv⟩ := hsurj ⟨c, hc⟩
    have h1 := he₁φ v
    rw [hv] at h1
    exact h1.symm
  have hu₁2 : u₁ * u₁ = 1 := by
    have h3 : e₁ * u₁ * e₁⁻¹ = u₁ := by rw [← he₁C u₁ hu₁C]; group
    have h1 : w * (u₁ * u₁) = w := by
      calc w * (u₁ * u₁) = (w * u₁) * u₁ := by group
        _ = (e₁ * w * e₁⁻¹) * (e₁ * u₁ * e₁⁻¹) := by rw [hw₁, h3]
        _ = e₁ * (w * u₁) * e₁⁻¹ := by group
        _ = e₁ * (e₁ * w * e₁⁻¹) * e₁⁻¹ := by rw [hw₁]
        _ = (e₁ * e₁) * w * (e₁ * e₁)⁻¹ := by group
        _ = w := by rw [he₁2]; group
    exact mul_left_cancel (h1.trans (mul_one w).symm)
  set u₀ : G := w⁻¹ * (e₀ * w * e₀⁻¹) with hu₀def
  have hu₀φ : (φ ⟨e₀, he₀V₀⟩ : G) = u₀ := hφ _
  have hu₀C : u₀ ∈ C := by
    rw [← hu₀φ]
    exact (φ ⟨e₀, he₀V₀⟩).2
  have hu₀2 : u₀ * u₀ = 1 := by
    have h1 : (⟨e₀, he₀V₀⟩ : ↥V₀) * ⟨e₀, he₀V₀⟩ = 1 := Subtype.ext he₀.sq
    have h2 := congrArg (fun y => (φ y : G)) h1
    simp only [map_mul, Subgroup.coe_mul, map_one, OneMemClass.coe_one] at h2
    rwa [hu₀φ] at h2
  have hCL : ∀ c ∈ C, c * c = 1 → c = 1 ∨ c = l := fun c hc hc2 =>
    hl.unique c (hR.1 (hCR hc)) hc2
  have hw₀ : e₀ * w * e₀⁻¹ = w * u₀ := by rw [hu₀def]; group
  rcases hCL u₁ hu₁C hu₁2 with hu₁1 | hu₁l
  ·
    right; left
    refine mem_trivialOnQuot_of_centralizes_sylow hp hq hΩ hL hR he₁2 he₁N ?_
    refine comm_of_index_two hCR hCcard hwR hwC ?_ he₁C
    have h1 : e₁ * w * e₁⁻¹ = w := by rw [hw₁, hu₁1, mul_one]
    calc w * e₁ = (e₁ * w * e₁⁻¹) * e₁ := by rw [h1]
      _ = e₁ * w := by group
  rcases hCL u₀ hu₀C hu₀2 with hu₀1 | hu₀l
  ·
    left
    refine mem_trivialOnQuot_of_centralizes_sylow hp hq hΩ hL hR he₀.sq he₀N ?_
    refine comm_of_index_two hCR hCcard hwR hwC ?_ hCe₀
    have h1 : e₀ * w * e₀⁻¹ = w := by rw [hw₀, hu₀1, mul_one]
    calc w * e₀ = (e₀ * w * e₀⁻¹) * e₀ := by rw [h1]
      _ = e₀ * w := by group
  ·
    right; right
    have hx2 : e₀ * e₁ * (e₀ * e₁) = 1 := by
      calc e₀ * e₁ * (e₀ * e₁) = e₀ * (e₁ * e₀) * e₁ := by group
        _ = e₀ * (e₀ * e₁) * e₁ := by rw [he₁e₀]
        _ = (e₀ * e₀) * (e₁ * e₁) := by group
        _ = 1 := by rw [he₀.sq, he₁2, one_mul]
    refine mem_trivialOnQuot_of_centralizes_sylow hp hq hΩ hL hR hx2 (mul_mem he₀N he₁N) ?_
    refine comm_of_index_two hCR hCcard hwR hwC ?_ ?_
    · have hle : e₀ * l * e₀⁻¹ = l := by rw [he₀l]; group
      have hl2 : l * l = 1 := hl.sq
      have h1 : (e₀ * e₁) * w * (e₀ * e₁)⁻¹ = w := by
        calc (e₀ * e₁) * w * (e₀ * e₁)⁻¹ = e₀ * (e₁ * w * e₁⁻¹) * e₀⁻¹ := by group
          _ = e₀ * (w * l) * e₀⁻¹ := by rw [hw₁, hu₁l]
          _ = (e₀ * w * e₀⁻¹) * (e₀ * l * e₀⁻¹) := by group
          _ = w * l * l := by rw [hw₀, hu₀l, hle]
          _ = w := by rw [mul_assoc, hl2, mul_one]
      calc w * (e₀ * e₁) = ((e₀ * e₁) * w * (e₀ * e₁)⁻¹) * (e₀ * e₁) := by rw [h1]
        _ = (e₀ * e₁) * w := by group
    · intro c hc
      calc c * (e₀ * e₁) = (c * e₀) * e₁ := by group
        _ = (e₀ * c) * e₁ := by rw [hCe₀ c hc]
        _ = e₀ * (c * e₁) := by group
        _ = e₀ * (e₁ * c) := by rw [he₁C c hc]
        _ = e₀ * e₁ * c := by group

end CFSG.ClassicalInvolution.NDB.TA
