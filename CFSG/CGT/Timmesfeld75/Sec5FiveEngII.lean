module

public import CFSG.CGT.Timmesfeld75.Sec5FiveFix
public import CFSG.CGT.Timmesfeld75.Sec3Eleven
public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_of_le_elemAbelian {M H K : Subgroup G} (hM : IsElemAbelian 2 M)
    (hH : H ≤ M) (hK : K ≤ M) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hmem : h ∈ M := hH hh
  constructor
  · intro hk
    rw [elemAbelian_mul_comm hM hmem (hK hk), mul_inv_cancel_right]
    exact hk
  · intro hk
    have h1 : h * k * h⁻¹ ∈ M := hK hk
    have h2 : h⁻¹ * (h * k * h⁻¹) * h = h * k * h⁻¹ :=
      (elemAbelian_mul_comm hM (M.inv_mem hmem) h1).symm ▸ by group
    have h3 : k = h⁻¹ * (h * k * h⁻¹) * h := by group
    rw [h3, h2]
    exact hk

section Fixed

variable [Finite G]

theorem exists_fixed_of_swap_inner {S S' : Subgroup G} (hS : Sec3 S S') (hSiso : Sec3Iso S S')
    {x : G} (hxx : x * x = 1) (hx : conjSubgroup x S = S') {B : Subgroup G}
    (hBL : B ≤ normIn S S') (hB1 : B ≠ ⊥)
    (hBN : ∀ n ∈ Subgroup.normalizer (S : Set G), conjSubgroup n B = B) {h : G}
    (hh : h ∈ S ⊔ S') {t : G} (ht : t ∈ conjSubgroup h S)
    (hxt : ∀ y ∈ S ⊔ S', y⁻¹ * ((x * t) * y * (x * t)⁻¹) ∈ cfgM S S') :
    ∃ b ∈ B, b ≠ 1 ∧ (x * t) * b * (x * t)⁻¹ = b := by
  obtain ⟨hN, f, hf, hiso⟩ := hSiso
  have := hN
  have hcfg := hS.cfg
  have hM : IsElemAbelian 2 (cfgM S S') := hcfg.isElemAbelian_cfgM
  have hSS' : conjSubgroup x S' = S := by
    rw [← hx, conjSubgroup_conjSubgroup, hxx, conjSubgroup_one]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxM : x ∈ Subgroup.normalizer ((cfgM S S' : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj, hx, hSS']
    show normIn S' S ⊔ normIn S S' = normIn S S' ⊔ normIn S' S
    exact sup_comm _ _
  have htX : t ∈ S ⊔ S' := conjSubgroup_le_of_le_of_mem le_sup_left hh ht
  have htt : t * t = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hcfg.wc.1 h) ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hBM : B ≤ cfgM S S' := hBL.trans (Cfg.normIn_le_cfgM_left S S')
  have hB'L : conjSubgroup x B ≤ normIn S' S := by
    have h1 : normIn (conjSubgroup x S) (conjSubgroup x S') = conjSubgroup x (normIn S S') :=
      normIn_conj x S S'
    rw [hx, hSS'] at h1
    rw [h1]
    exact conjSubgroup_mono hBL
  have hB'M : conjSubgroup x B ≤ cfgM S S' := hB'L.trans (Cfg.normIn_le_cfgM_right S S')
  set W : Subgroup G := B ⊔ conjSubgroup x B with hWdef
  have hWM : W ≤ cfgM S S' := sup_le hBM hB'M
  have hWX : ∀ y ∈ S ⊔ S', conjSubgroup y W = W :=
    hS.conjSubgroup_sup_conj_eq hf hiso hx hBL fun n hn =>
      mem_normalizer_of_conjSubgroup_eq (hBN n hn)
  have hxW : conjSubgroup x W = W := by
    rw [hWdef, conjSubgroup_sup_eq_sup, conjSubgroup_conjSubgroup, hxx, conjSubgroup_one,
      sup_comm]
  obtain ⟨u, hu⟩ : ∃ u : G, u = x * t := ⟨_, rfl⟩
  rw [← hu] at hxt ⊢
  have huW : conjSubgroup u W = W := by
    rw [hu, ← conjSubgroup_conjSubgroup, hWX t htX, hxW]
  have hu2 : u * u ∈ cfgM S S' := by
    have h1 := hxt t htX
    have e : x * (t⁻¹ * (u * t * u⁻¹)) * x⁻¹ = u * u := by
      rw [hu]
      calc x * (t⁻¹ * ((x * t) * t * (x * t)⁻¹)) * x⁻¹
          = (x * t * x * t) * (t * t) * (x * x) := by
            simp only [mul_inv_rev, hti, hxi]
            group
        _ = (x * t) * (x * t) := by rw [htt, hxx]; group
    rw [← e]
    exact (Subgroup.mem_normalizer_iff.1 hxM _).1 h1
  have hu4 : u ^ 4 = 1 := by
    have := elemAbelian_mul_self hM hu2
    calc u ^ 4 = (u * u) * (u * u) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hWp : IsPGroup 2 W :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_subgroup_of_le hM hWM)
  have hW1 : W ≠ ⊥ := fun h' => hB1 (le_bot_iff.1 (by rw [← h']; exact le_sup_left))
  obtain ⟨w, hwW, hw1, hwu⟩ := exists_fixed_of_isPGroup
    (isPGroup_two_zpowers_of_pow_four hu4)
    (Subgroup.zpowers_le.2 (mem_normalizer_of_conjSubgroup_eq huW)) hWp hW1
  have hC1 : (W ⊓ Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
    intro h'
    have hmem : w ∈ W ⊓ Subgroup.centralizer ({u} : Set G) := by
      refine ⟨hwW, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hwu u (Subgroup.mem_zpowers u)
      calc w * u = (u * w * u⁻¹) * u := by rw [h1]
        _ = u * w := by group
    rw [h', Subgroup.mem_bot] at hmem
    exact hw1 hmem
  have hSC : S ≤ Subgroup.normalizer ((W ⊓ Subgroup.centralizer ({u} : Set G) :
      Subgroup G) : Set G) := by
    intro s hs
    have hsX : s ∈ S ⊔ S' := Subgroup.mem_sup_left hs
    refine mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le fun c hc => ?_)
    rw [mem_conjSubgroup] at hc
    obtain ⟨hw₀W, hw₀u⟩ := hc
    have hw₀u' : u * (s⁻¹ * c * s) * u⁻¹ = s⁻¹ * c * s := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hw₀u
      calc u * (s⁻¹ * c * s) * u⁻¹ = ((s⁻¹ * c * s) * u) * u⁻¹ := by rw [← this]
        _ = s⁻¹ * c * s := by group
    have hcW : c ∈ W := by
      have h1 := conj_mem_conjSubgroup s hw₀W
      rw [hWX s hsX] at h1
      simpa [mul_assoc] using h1
    refine ⟨hcW, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    obtain ⟨m, hmdef⟩ : ∃ m, m = s⁻¹ * (u * s * u⁻¹) := ⟨_, rfl⟩
    have hm : m ∈ cfgM S S' := by rw [hmdef]; exact hxt s hsX
    have hum : u * s * u⁻¹ = s * m := by rw [hmdef]; group
    have hmw : m * (s⁻¹ * c * s) = (s⁻¹ * c * s) * m :=
      elemAbelian_mul_comm hM hm (hWM hw₀W)
    have hcu : u * c * u⁻¹ = c := by
      calc u * c * u⁻¹ = u * (s * (s⁻¹ * c * s) * s⁻¹) * u⁻¹ := by group
        _ = (u * s * u⁻¹) * (u * (s⁻¹ * c * s) * u⁻¹) * (u * s * u⁻¹)⁻¹ := by group
        _ = (s * m) * (s⁻¹ * c * s) * (s * m)⁻¹ := by rw [hum, hw₀u']
        _ = s * (m * (s⁻¹ * c * s) * m⁻¹) * s⁻¹ := by group
        _ = c := by rw [hmw]; group
    calc c * u = (u * c * u⁻¹) * u := by rw [hcu]
      _ = u * c := by group
  obtain ⟨c, hcC, hc1, hcS⟩ := exists_fixed_of_isPGroup
    (isPGroup_two_of_isElemAbelian hcfg.wc.1) hSC (hWp.to_le inf_le_left) hC1
  have hBn : B ≤ Subgroup.normalizer (conjSubgroup x B : Set G) :=
    le_normalizer_of_le_elemAbelian hM hBM hB'M
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right B (conjSubgroup x B) hBn
  have hcW : c ∈ ((B : Set G) * (conjSubgroup x B : Set G)) := by
    rw [← hmul]
    exact hcC.1
  obtain ⟨b, hb, b', hb', hcbb⟩ := hcW
  have hcbb' : b * b' = c := hcbb
  have hb'eq : b' = b⁻¹ * c := by rw [← hcbb']; group
  have hbS : b ∈ S := normIn_le _ _ (hBL hb)
  have hb'1 : b' = 1 := by
    by_contra hb'1
    have hb'S' : b' ∈ S' := by
      have : b' ∈ conjSubgroup x S := conjSubgroup_mono (hBL.trans (normIn_le S S')) hb'
      rwa [hx] at this
    have hSle : S ≤ Subgroup.normalizer (S' : Set G) := by
      refine fun s hs => hcfg.wc₁.centralizer_le_normalizer hb'S' hb'1 ?_
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have hsb : s * b⁻¹ = b⁻¹ * s := elemAbelian_mul_comm hcfg.wc.1 hs (S.inv_mem hbS)
      have hsc : s * c = c * s := by
        have := hcS s hs
        calc s * c = (s * c * s⁻¹) * s := by group
          _ = c * s := by rw [this]
      rw [hb'eq]
      calc s * (b⁻¹ * c) = (s * b⁻¹) * c := by rw [mul_assoc]
        _ = (b⁻¹ * s) * c := by rw [hsb]
        _ = b⁻¹ * (s * c) := by rw [mul_assoc]
        _ = b⁻¹ * (c * s) := by rw [hsc]
        _ = (b⁻¹ * c) * s := by rw [mul_assoc]
    have hlt := hcfg.normIn_lt (⟨x, hx.symm⟩ : ∃ y : G, S' = conjSubgroup y S)
    have heq : normIn S S' = S := inf_eq_left.2 hSle
    exact absurd heq (ne_of_lt hlt)
  have hcb : c = b := by rw [← hcbb', hb'1, mul_one]
  refine ⟨b, hb, fun hb1 => hc1 (hcb.trans hb1), ?_⟩
  rw [← hcb]
  have := Subgroup.mem_centralizer_singleton_iff.1 hcC.2
  calc u * c * u⁻¹ = (c * u) * u⁻¹ := by rw [← this]
    _ = c := by group

omit [Finite G] in
theorem commutator_swap_facts {S S' : Subgroup G} (hS : Sec3 S S') {x : G} (hxx : x * x = 1)
    (hx : conjSubgroup x S = S') {B : Subgroup G} (hBL : B ≤ normIn S S') {h : G}
    (hh : h ∈ S ⊔ S') {t : G} (ht : t ∈ conjSubgroup h S) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hub : (x * t) * b * (x * t)⁻¹ = b) :
    ⁅b, x⁆ ≠ 1 ∧ ⁅b, x⁆ = ⁅b, t⁆ ∧ ⁅b, t⁆ ∈ conjSubgroup h S := by
  have hcfg := hS.cfg
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hbS : b ∈ S := normIn_le _ _ (hBL hb)
  refine ⟨fun h1 => hb1 ?_, ?_, ?_⟩
  · have h2 : b * x = x * b := commutatorElement_eq_one_iff_mul_comm.1 h1
    have h3 : x * b * x⁻¹ = b := by rw [← h2]; group
    have h4 : b ∈ S' := by
      have h5 : x * b * x⁻¹ ∈ conjSubgroup x S := conj_mem_conjSubgroup x hbS
      rwa [h3, hx] at h5
    have h6 : b ∈ S ⊓ S' := ⟨hbS, h4⟩
    rwa [hcfg.inf, Subgroup.mem_bot] at h6
  · have h1 : t * b * t⁻¹ = x⁻¹ * b * x := by
      calc t * b * t⁻¹ = x⁻¹ * ((x * t) * b * (x * t)⁻¹) * x := by group
        _ = x⁻¹ * b * x := by rw [hub]
    have h2 : x * b * x⁻¹ = t * b * t⁻¹ := by rw [h1, hxi]
    calc ⁅b, x⁆ = b * (x * b * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      _ = b * (t * b * t⁻¹)⁻¹ := by rw [h2]
      _ = ⁅b, t⁆ := by simp only [commutatorElement_def]; group
  · have hbM : b ∈ cfgM S S' := Cfg.normIn_le_cfgM_left S S' (hBL hb)
    obtain ⟨⟨l₀, hl₀⟩, hl₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne
    have hl₀1' : l₀ ≠ 1 := fun h' => hl₀1 (Subtype.ext h')
    have hlh : h * l₀ * h⁻¹ ∈ conjSubgroup h S := conj_mem_conjSubgroup h (normIn_le _ _ hl₀)
    have hl1 : h * l₀ * h⁻¹ ≠ 1 := fun h' => hl₀1' (by
      calc l₀ = h⁻¹ * (h * l₀ * h⁻¹) * h := by group
        _ = 1 := by rw [h']; group)
    have hlM : h * l₀ * h⁻¹ ∈ cfgM S S' :=
      hcfg.conj_mem_cfgM hh (Cfg.normIn_le_cfgM_left S S' hl₀)
    have hbl : b * (h * l₀ * h⁻¹) = (h * l₀ * h⁻¹) * b :=
      elemAbelian_mul_comm hcfg.isElemAbelian_cfgM hbM hlM
    have hbN : b ∈ Subgroup.normalizer ((conjSubgroup h S : Subgroup G) : Set G) :=
      (hcfg.wc.conj h).centralizer_le_normalizer hlh hl1
        (Subgroup.mem_centralizer_singleton_iff.2 hbl)
    have e : ⁅b, t⁆ = (b * t * b⁻¹) * t⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (conjSubgroup h S).mul_mem (conj_mem_of_mem_normalizer hbN ht)
      ((conjSubgroup h S).inv_mem ht)

end Fixed

end CFSG.CGT.Timmesfeld75
