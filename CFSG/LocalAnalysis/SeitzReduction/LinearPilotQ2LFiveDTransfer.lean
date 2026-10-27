module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransfer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt_of_isPGroup_two {P R : Subgroup G}
    (hP : IsPGroup 2 P) (hRP : R < P) :
    ∃ x ∈ P, x ∉ R ∧ x ∈ normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : R.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hRP.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ R.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyR⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt)
  refine ⟨y, y.2, fun h => hyR (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (R : Set G)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hRP.le]
    exact hyN
  exact mem_subgroupOf.mp hy

@[expose] noncomputable def sylowOfCardMax {C Q₀ : Subgroup G} (hQ₀C : Q₀ ≤ C) (hQ₀ : IsPGroup 2 Q₀)
    {k : ℕ} (hcard : Nat.card Q₀ = k)
    (hmax : ∀ P : Subgroup C, IsPGroup 2 P → Nat.card P ≤ k) : Sylow 2 C where
  toSubgroup := Q₀.subgroupOf C
  isPGroup' := hQ₀.comap_of_injective C.subtype C.subtype_injective
  is_maximal' := by
    intro P hP hle
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀C).toEquiv, hcard]
    exact hmax P hP

theorem mem_of_mem_normalizer_of_fusion_control {M T Q : Subgroup G} {t : G}
    (hTM : T ≤ M) (hQT : Q ≤ T) (htQ : t ∈ Q) (hQ : IsPGroup 2 Q)
    (hQt : Q ≤ centralizer ({t} : Set G))
    (hQmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ Nat.card Q)
    (hfus : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹)
    (hNQ : ∀ y ∈ centralizer ({t} : Set G), y ∈ normalizer (Q : Set G) → y ∈ M)
    {d : G} (hd : d ∈ normalizer (T : Set G)) : d ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht'T : d * t * d⁻¹ ∈ T := (mem_normalizer_iff.1 hd t).1 (hQT htQ)
  obtain ⟨n, hnM, hn⟩ := hfus d (hTM ht'T)
  set C' : Subgroup G := centralizer ({d * t * d⁻¹} : Set G) ⊓ M with hC'
  have hcomm : ∀ g : G, ∀ q ∈ Q, g * q * g⁻¹ ∈ centralizer ({g * t * g⁻¹} : Set G) := by
    intro g q hq
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 (hQt hq)
    calc g * q * g⁻¹ * (g * t * g⁻¹) = g * (q * t) * g⁻¹ := by group
      _ = g * (t * q) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * (g * q * g⁻¹) := by group
  have hQ₁C : Q.map (MulAut.conj d).toMonoidHom ≤ C' := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_inf.2 ⟨hcomm d q hq, hTM ((mem_normalizer_iff.1 hd q).1 (hQT hq))⟩
  have hQ₂C : Q.map (MulAut.conj n).toMonoidHom ≤ C' := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_inf.2 ⟨?_, M.mul_mem (M.mul_mem hnM (hTM (hQT hq))) (M.inv_mem hnM)⟩
    rw [hn]
    exact hcomm n q hq
  have hcard₁ : Nat.card (Q.map (MulAut.conj d).toMonoidHom) = Nat.card Q :=
    card_map_of_injective (MulAut.conj d).injective
  have hcard₂ : Nat.card (Q.map (MulAut.conj n).toMonoidHom) = Nat.card Q :=
    card_map_of_injective (MulAut.conj n).injective
  have hmax : ∀ P : Subgroup C', IsPGroup 2 P → Nat.card P ≤ Nat.card Q := by
    intro P hP
    have hle : (P.map C'.subtype).map (MulAut.conj d⁻¹).toMonoidHom ≤
        centralizer ({t} : Set G) := by
      rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      have hx1 := mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).1
      rw [mem_centralizer_singleton_iff]
      change d⁻¹ * (x : G) * d⁻¹⁻¹ * t = t * (d⁻¹ * (x : G) * d⁻¹⁻¹)
      calc d⁻¹ * (x : G) * d⁻¹⁻¹ * t = d⁻¹ * ((x : G) * (d * t * d⁻¹)) * d := by group
        _ = d⁻¹ * ((d * t * d⁻¹) * (x : G)) * d := by rw [hx1]
        _ = t * (d⁻¹ * (x : G) * d⁻¹⁻¹) := by group
    have h1 := hQmax _ ((hP.map C'.subtype).map _) hle
    rwa [card_map_of_injective (MulAut.conj d⁻¹).injective,
      card_map_of_injective C'.subtype_injective] at h1
  let S₁ := sylowOfCardMax hQ₁C (hQ.map _) hcard₁ hmax
  let S₂ := sylowOfCardMax hQ₂C (hQ.map _) hcard₂ hmax
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C' S₂ S₁
  have hconj : ∀ q ∈ Q, (d⁻¹ * c * n) * q * (d⁻¹ * c * n)⁻¹ ∈ Q := by
    intro q hq
    have hx : (⟨n * q * n⁻¹, hQ₂C ⟨q, hq, rfl⟩⟩ : C') ∈ (S₂ : Subgroup C') :=
      mem_subgroupOf.2 ⟨q, hq, rfl⟩
    have h1 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) (S₂ : Subgroup C') hx
    rw [← Sylow.coe_subgroup_smul, hc] at h1
    obtain ⟨q', hq', hq'eq⟩ := mem_subgroupOf.1 h1
    have hq'' : d * q' * d⁻¹ = (c : G) * (n * q * n⁻¹) * (c : G)⁻¹ := hq'eq
    have heq : (d⁻¹ * c * n) * q * (d⁻¹ * c * n)⁻¹ = q' := by
      calc (d⁻¹ * c * n) * q * (d⁻¹ * c * n)⁻¹ =
            d⁻¹ * ((c : G) * (n * q * n⁻¹) * (c : G)⁻¹) * d := by group
        _ = d⁻¹ * (d * q' * d⁻¹) * d := by rw [hq'']
        _ = q' := by group
    rw [heq]
    exact hq'
  have hyN : d⁻¹ * c * n ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact hconj q hq
    · rw [card_map_of_injective (MulAut.conj (d⁻¹ * c * n)).injective]
  have hyC : d⁻¹ * c * n ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hct : (c : G) * (d * t * d⁻¹) = (d * t * d⁻¹) * c :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).1
    calc d⁻¹ * c * n * t = d⁻¹ * c * (n * t * n⁻¹) * n := by group
      _ = d⁻¹ * c * (d * t * d⁻¹) * n := by rw [← hn]
      _ = d⁻¹ * ((c : G) * (d * t * d⁻¹)) * n := by group
      _ = d⁻¹ * ((d * t * d⁻¹) * c) * n := by rw [hct]
      _ = t * (d⁻¹ * c * n) := by group
  have hyM := hNQ _ hyC hyN
  have hcM : (c : G) ∈ M := (mem_inf.1 c.2).2
  have hdeq : d = c * n * (d⁻¹ * c * n)⁻¹ := by group
  rw [hdeq]
  exact M.mul_mem (M.mul_mem hcM hnM) (M.inv_mem hyM)

theorem not_two_dvd_index_of_fusion_control {M Q : Subgroup G} {t : G} (htQ : t ∈ Q)
    (hQ : IsPGroup 2 Q) (hQt : Q ≤ centralizer ({t} : Set G)) (hQM : Q ≤ M)
    (hQmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ Nat.card Q)
    (hfus : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹)
    (hNQ : ∀ y ∈ centralizer ({t} : Set G), y ∈ normalizer (Q : Set G) → y ∈ M) :
    ¬ 2 ∣ M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := (hQ.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  set T : Subgroup G := (T₀ : Subgroup M).map M.subtype with hTdef
  have hTM : T ≤ M := map_subtype_le _
  have hQT : Q ≤ T := fun q hq => ⟨⟨q, hQM hq⟩, hT₀ hq, rfl⟩
  have hTp : IsPGroup 2 T := T₀.isPGroup'.map M.subtype
  have hTmax : ∀ {P : Subgroup G}, IsPGroup 2 P → T ≤ P → P = T := by
    intro P hP hTP
    by_contra hne
    obtain ⟨d, hdP, hdT, hdN⟩ :=
      exists_mem_normalizer_not_mem_of_lt_of_isPGroup_two hP (lt_of_le_of_ne hTP (Ne.symm hne))
    have hdM : d ∈ M :=
      mem_of_mem_normalizer_of_fusion_control hTM hQT htQ hQ hQt hQmax hfus hNQ hdN
    have hRp : IsPGroup 2 ((T ⊔ zpowers d).comap M.subtype) :=
      (hP.to_le (sup_le hTP (zpowers_le.2 hdP))).comap_of_injective _ M.subtype_injective
    have hle : (T₀ : Subgroup M) ≤ (T ⊔ zpowers d).comap M.subtype := fun x hx =>
      mem_comap.2 (mem_sup_left ⟨x, hx, rfl⟩)
    have heq := T₀.is_maximal' hRp hle
    apply hdT
    have hmem : (⟨d, hdM⟩ : M) ∈ (T ⊔ zpowers d).comap M.subtype :=
      mem_comap.2 (mem_sup_right (mem_zpowers d))
    rw [heq] at hmem
    exact ⟨⟨d, hdM⟩, hmem, rfl⟩
  let S : Sylow 2 G := { toSubgroup := T, isPGroup' := hTp, is_maximal' := hTmax }
  intro h2
  exact S.not_dvd_index (h2.trans (index_dvd_of_le hTM))

theorem exists_normal_index_two_of_fusion_control {M U Q : Subgroup G} {t : G}
    (hU : U.relIndex M = 2) (htM : t ∈ M) (htU : t ∉ U) (ht : orderOf t = 2)
    (hconj : ∀ g : G, g⁻¹ * t * g ∉ U) (htQ : t ∈ Q) (hQ : IsPGroup 2 Q)
    (hQt : Q ≤ centralizer ({t} : Set G)) (hQM : Q ≤ M)
    (hQmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ Nat.card Q)
    (hfus : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹)
    (hNQ : ∀ y ∈ centralizer ({t} : Set G), y ∈ normalizer (Q : Set G) → y ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  refine F4Pilot.exists_normal_index_two_of_not_fused_of_relIndex_eq_two hU
    (not_two_dvd_index_of_fusion_control htQ hQ hQt hQM hQmax hfus hNQ) htM htU (a := 1)
    (by rw [pow_one]; exact ht) (fun y _ hyU _ => ?_) hconj
  have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
  have hpos := orderOf_pos y
  have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  rw [ht]
  omega

theorem card_le_card_inf_centralizer_mul_card_of_exponent_two {N : Type*} [Group N] [Finite N]
    {W : Subgroup N} (hW2 : ∀ w ∈ W, w * w = 1) {x : N} (hx : x * x = 1) {P : Subgroup N}
    (hP : ∀ y ∈ P, y * x * y⁻¹ * x⁻¹ ∈ W) :
    Nat.card P ≤ Nat.card (P ⊓ centralizer ({x} : Set N) : Subgroup N) *
      Nat.card (W ⊓ centralizer ({x} : Set N) : Subgroup N) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hmem : ∀ y : P, (y : N) * x * (y : N)⁻¹ * x⁻¹ ∈ W ⊓ centralizer ({x} : Set N) := by
    intro y
    have hw := hP y y.2
    refine mem_inf.2 ⟨hw, ?_⟩
    set w := (y : N) * x * (y : N)⁻¹ * x⁻¹ with hwdef
    have hw2 : w * w = 1 := hW2 w hw
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have h1 : w * x * w * x = 1 := by
      rw [hwdef]
      calc (y : N) * x * (y : N)⁻¹ * x⁻¹ * x * ((y : N) * x * (y : N)⁻¹ * x⁻¹) * x =
            (y : N) * (x * x) * (y : N)⁻¹ := by group
        _ = 1 := by rw [hx]; group
    rw [mem_centralizer_singleton_iff]
    have h2 : (w * x) * (w * x) = 1 := by rw [← h1]; group
    calc w * x = (w * x)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
      _ = x⁻¹ * w⁻¹ := mul_inv_rev w x
      _ = x * w := by rw [hxi, hwi]
  let F : P → (W ⊓ centralizer ({x} : Set N) : Subgroup N) := fun y => ⟨_, hmem y⟩
  set H : Subgroup P := (centralizer ({x} : Set N)).subgroupOf P with hH
  have hF : ∀ a b : P, F a = F b ↔ a⁻¹ * b ∈ H := by
    intro a b
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, Subtype.ext_iff]
    change (a : N) * x * (a : N)⁻¹ * x⁻¹ = (b : N) * x * (b : N)⁻¹ * x⁻¹ ↔
      ((a : N)⁻¹ * b) * x = x * ((a : N)⁻¹ * b)
    constructor
    · intro h
      have h' : (a : N) * x * (a : N)⁻¹ = (b : N) * x * (b : N)⁻¹ := mul_right_cancel h
      calc ((a : N)⁻¹ * b) * x = (a : N)⁻¹ * ((b : N) * x * (b : N)⁻¹) * b := by group
        _ = (a : N)⁻¹ * ((a : N) * x * (a : N)⁻¹) * b := by rw [h']
        _ = x * ((a : N)⁻¹ * b) := by group
    · intro h
      calc (a : N) * x * (a : N)⁻¹ * x⁻¹ =
            (a : N) * (x * ((a : N)⁻¹ * b)) * (b : N)⁻¹ * x⁻¹ := by group
        _ = (a : N) * (((a : N)⁻¹ * b) * x) * (b : N)⁻¹ * x⁻¹ := by rw [h]
        _ = (b : N) * x * (b : N)⁻¹ * x⁻¹ := by group
  let F' : P ⧸ H → (W ⊓ centralizer ({x} : Set N) : Subgroup N) :=
    Quotient.lift F fun a b hab => (hF a b).2 (QuotientGroup.leftRel_apply.1 hab)
  have hF'inj : Function.Injective F' := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H a =>
      induction q using QuotientGroup.induction_on with
      | H b =>
        have hpq' : F a = F b := hpq
        exact QuotientGroup.eq.2 ((hF a b).1 hpq')
  have h1 := Nat.card_le_card_of_injective F' hF'inj
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
  have h3 : Nat.card H = Nat.card (P ⊓ centralizer ({x} : Set N) : Subgroup N) := by
    have h4 := card_map_of_injective (K := H) P.subtype_injective
    rw [← h4, hH, subgroupOf_map_subtype, inf_comm]
  rw [h2, h3, mul_comm]
  exact Nat.mul_le_mul_left _ h1

theorem false_of_simple_of_fusion_control [IsSimpleGroup G] (hG : 2 < Nat.card G)
    {M U Q : Subgroup G} {t : G}
    (hU : U.relIndex M = 2) (htM : t ∈ M) (htU : t ∉ U) (ht : orderOf t = 2)
    (hconj : ∀ g : G, g⁻¹ * t * g ∉ U) (htQ : t ∈ Q) (hQ : IsPGroup 2 Q)
    (hQt : Q ≤ centralizer ({t} : Set G)) (hQM : Q ≤ M)
    (hQmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ Nat.card Q)
    (hfus : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹)
    (hNQ : ∀ y ∈ centralizer ({t} : Set G), y ∈ normalizer (Q : Set G) → y ∈ M) : False :=
  CFSG.SeitzReduction.not_exists_normal_index_two_of_simple hG
    (exists_normal_index_two_of_fusion_control hU htM htU ht hconj htQ hQ hQt hQM hQmax hfus hNQ)

end CFSG.SeitzReduction.LinearPilot
