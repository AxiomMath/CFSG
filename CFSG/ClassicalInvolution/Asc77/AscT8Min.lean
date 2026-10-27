module

public import CFSG.ClassicalInvolution.Asc77.AscT8Fuse
import CFSG.StronglyEmbedded.UniqueCosetFixedEng
import CFSG.ClassicalInvolution.Asc77.AscT8FourGen

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8

section Min

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mul_comm_of_mem_omegaNbr {K J : Subgroup G} {z t : G} (hp : p ≠ 2)
    (hΩ : HypOmegaMod p f Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution J t) : z * t = t * z := by
  obtain ⟨hJΩ, -, T', hT', hT'J, hT'N⟩ := hJ
  have hsyl := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hT' hT'J
  have h8 := hΩ.eight_le_of_mem_RSet hp hT'
  have htT : t ∈ T' := T3.mem_of_isPGroup ht hT'J hsyl.2.1 (by omega)
  have hN : conjSub t K = K := mem_normalizer_iff_conjSub_eq.mp (hT'N htT)
  have h := hz.conj_eq hN
  calc z * t = (t * z * t⁻¹) * t := by rw [h]
    _ = t * z := by group

theorem mul_self_zt {K J : Subgroup G} {z t : G} (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) :
    z * t * (z * t) = 1 := by
  have hc := mul_comm_of_mem_omegaNbr hp hΩ hz hJ ht
  calc z * t * (z * t) = z * (t * z) * t := by group
    _ = z * (z * t) * t := by rw [hc]
    _ = (z * z) * (t * t) := by group
    _ = 1 := by rw [hz.sq, ht.sq]; group

theorem le_centralizer_mul {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) :
    R ≤ Subgroup.centralizer ({z * t} : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRne : R ≠ T := by
    intro hRT
    have hRsyl := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
    have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
    have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
    have hzJ : z ∈ J := hTJ (hRT ▸ hzR)
    rcases hs.ht.unique z hzJ hs.hz.sq with h | h
    · exact hs.hz.ne_one h
    · have hJtw : J ∈ twinSet Ω K := ⟨hs.hJ.1, z, hs.hz, h ▸ hs.ht⟩
      exact hs.hJ.2.1 (hs.noTwins J hJtw)
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : r * z = z * r := by
    have := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hRK hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [this]
  have h2 : r * t = t * r := by
    have hRsyl := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hTΩ hTJ
    have h8 := hΩ.eight_le_of_mem_RSet hp hTΩ
    have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hRsyl.2.1 (by omega)
    exact l6_7_proved p f hp hq G Ω hΩ S R hRΩ T hTΩ hRS hTS hRne r hr t htT
  calc r * (z * t) = (r * z) * t := by group
    _ = (z * r) * t := by rw [h1]
    _ = z * (r * t) := by group
    _ = z * (t * r) := by rw [h2]
    _ = (z * t) * r := by group

theorem exists_sylow_centralizer {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) :
    ∃ S' : Sylow 2 G, R ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G))
        (Subgroup.centralizer ({z * t} : Set G)) := by
  have hR2 : IsPGroup 2 R := S.isPGroup'.to_le hs.hR.2.2
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_centralizer_mul hs)
  obtain ⟨S', hVS'⟩ := IsPGroup.exists_le_sylow hV.2.1
  refine ⟨S', hRV.trans hVS', ?_⟩
  have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G)) :=
    S'.isPGroup'.to_le inf_le_left
  have heq := hV.eq_of_le hp2 inf_le_right (le_inf hVS' hV.1)
  rw [heq]
  exact hV

theorem sylow_le_H274_of_ge {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) {S' : Sylow 2 G} (hRS' : R ≤ (S' : Subgroup G)) :
    (S' : Subgroup G) ≤ H274 Ω K z :=
  (sylow_le_sigmaNorm hs.stand.odd hs.stand.five hs.stand.hyp hs.stand.mem hs.hR.1 hs.hR.2.1
    hRS' hs.hz).trans (sigmaNorm_le_H274 K z)

theorem not_commute_of_not_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g w : G}
    (hg : g ∉ H274 Ω K z) (hw : IsConj z w) (hwH : w ∈ H274 Ω K z) :
    g⁻¹ * (z * t) * g * w ≠ w * (g⁻¹ * (z * t) * g) := by
  intro hcom
  obtain ⟨c, rfl⟩ := isConj_iff.1 hw
  have hcH : c ∈ H274 Ω K z := by
    have h := mem_H274_of_conj_mem_H274 hs hcomp (g := c⁻¹) (by simpa using hwH)
    simpa using (H274 Ω K z).inv_mem h
  have ha' : (g * c)⁻¹ * (z * t) * (g * c) * z = z * ((g * c)⁻¹ * (z * t) * (g * c)) := by
    have e1 : (g * c)⁻¹ * (z * t) * (g * c) * z
        = c⁻¹ * (g⁻¹ * (z * t) * g * (c * z * c⁻¹)) * c := by group
    have e2 : z * ((g * c)⁻¹ * (z * t) * (g * c))
        = c⁻¹ * ((c * z * c⁻¹) * (g⁻¹ * (z * t) * g)) * c := by group
    rw [e1, e2, hcom]
  have hy : (g * c) * z * (g * c)⁻¹ ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * c) * z * (g * c)⁻¹ * (z * t)
        = (g * c) * (z * ((g * c)⁻¹ * (z * t) * (g * c))) * (g * c)⁻¹ := by group
      _ = (g * c) * (((g * c)⁻¹ * (z * t) * (g * c)) * z) * (g * c)⁻¹ := by rw [ha']
      _ = (z * t) * ((g * c) * z * (g * c)⁻¹) := by group
  have hyH : (g * c) * z * (g * c)⁻¹ ∈ H274 Ω K z := centralizer_mul_le_H274 hs.hJ hs.ht hy
  have hgc : g * c ∈ H274 Ω K z := by
    have h := mem_H274_of_conj_mem_H274 hs hcomp (g := (g * c)⁻¹) (by simpa using hyH)
    simpa using (H274 Ω K z).inv_mem h
  apply hg
  have : g = (g * c) * c⁻¹ := by group
  rw [this]
  exact (H274 Ω K z).mul_mem hgc ((H274 Ω K z).inv_mem hcH)

theorem frame_facts {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) {S' : Sylow 2 G}
    (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {X M : Subgroup G} {x : G} (hXS : X ≤ (S' : Subgroup G))
    (hM : M ∈ Ω) (hXM : IsSylow2In X M) (hXΩ : X ∈ RSet Ω) (hx : IsUniqueInvolution M x) :
    x ∈ X ∧ x ∈ H274 Ω K z ∧ IsConj z x ∧ (∀ y ∈ X, x * y = y * x) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have h8 := hΩ.eight_le_of_mem_RSet hp hXΩ
  have hxX : x ∈ X := T3.mem_of_isPGroup hx hXM.1 hXM.2.1 (by omega)
  refine ⟨hxX, hS'H (hXS hxX), ?_, fun y hy => ?_⟩
  · obtain ⟨c, hc⟩ := hs.stand.trans M hM
    have h1 : IsUniqueInvolution M (c * z * c⁻¹) := hc ▸ hs.hz.conj c
    exact isConj_iff.2 ⟨c, (hx.eq h1).symm⟩
  · have h := hx.conj_eq (n := y) (conjSub_eq_self_of_mem (hXM.1 hy))
    calc x * y = (y * x * y⁻¹) * y := by rw [h]
      _ = y * x := by group

theorem conjSub_ne_of_not_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S' : Sylow 2 G} (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G} (hg : g ∉ H274 Ω K z)
    {X M : Subgroup G} {x : G} (hXS : X ≤ (S' : Subgroup G)) (hM : M ∈ Ω)
    (hXM : IsSylow2In X M) (hXΩ : X ∈ RSet Ω) (hx : IsUniqueInvolution M x) :
    conjSub (g⁻¹ * (z * t) * g) X ≠ X := by
  intro h
  obtain ⟨-, hxH, hxc, -⟩ := frame_facts hs hS'H hXS hM hXM hXΩ hx
  have hdx : (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ = x := by
    have hmem : (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ ∈ conjSub (g⁻¹ * (z * t) * g) X :=
      conj_mem_conjSub (frame_facts hs hS'H hXS hM hXM hXΩ hx).1
    rw [h] at hmem
    have hsq : (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ *
        ((g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹) = 1 := by
      calc (g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹ *
          ((g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹)
          = (g⁻¹ * (z * t) * g) * (x * x) * (g⁻¹ * (z * t) * g)⁻¹ := by group
        _ = 1 := by rw [hx.sq]; group
    rcases hx.unique _ (hXM.1 hmem) hsq with h1 | h1
    · exfalso
      apply hx.ne_one
      calc x = (g⁻¹ * (z * t) * g)⁻¹ * ((g⁻¹ * (z * t) * g) * x * (g⁻¹ * (z * t) * g)⁻¹) *
            (g⁻¹ * (z * t) * g) := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  apply not_commute_of_not_mem_H274 hs hcomp hg hxc hxH
  calc g⁻¹ * (z * t) * g * x = (g⁻¹ * (z * t) * g * x * (g⁻¹ * (z * t) * g)⁻¹) *
        (g⁻¹ * (z * t) * g) := by group
    _ = x * (g⁻¹ * (z * t) * g) := by rw [hdx]

omit [Finite G] in
theorem isPGroup_zpowers_of_sq {x : G} (hx : x * x = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  have h := isPGroup_closure_pair hx hx rfl
  have e : Subgroup.closure ({x, x} : Set G) = Subgroup.zpowers x := by
    rw [Subgroup.zpowers_eq_closure, Set.pair_eq_singleton]
  rw [e] at h
  exact h

theorem exists_normalized_conj {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) {S' : Sylow 2 G}
    (hS'a : IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G))
      (Subgroup.centralizer ({z * t} : Set G)))
    (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G} (hg : g ∉ H274 Ω K z)
    (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) :
    ∃ g' : G, g' ∉ H274 Ω K z ∧ g'⁻¹ * (z * t) * g' ∈ (S' : Subgroup G) ∧
      ∀ s ∈ (S' : Subgroup G), (g'⁻¹ * (z * t) * g') * s = s * (g'⁻¹ * (z * t) * g') →
        g' * s * g'⁻¹ ∈ (S' : Subgroup G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have ha2 : z * t * (z * t) = 1 := mul_self_zt hp hs.stand.hyp hs.hz hs.hJ hs.ht
  have haC : Subgroup.centralizer ({z * t} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hs.hJ hs.ht
  have hd₀2 : (g⁻¹ * (z * t) * g) * (g⁻¹ * (z * t) * g) = 1 := by
    calc (g⁻¹ * (z * t) * g) * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨y, hyH, hyS⟩ := exists_conj_into_sylow S' hS'H hgH (isPGroup_zpowers_of_sq hd₀2)
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = g * y⁻¹ := ⟨_, rfl⟩
  have hd₁ : g₁⁻¹ * (z * t) * g₁ = y * (g⁻¹ * (z * t) * g) * y⁻¹ := by rw [hg₁]; group
  have hd₁S : g₁⁻¹ * (z * t) * g₁ ∈ (S' : Subgroup G) := hd₁ ▸ hyS
  have hg₁H : g₁ ∉ H274 Ω K z := by
    intro h
    apply hg
    have : g = g₁ * y := by rw [hg₁]; group
    rw [this]
    exact (H274 Ω K z).mul_mem h hyH
  obtain ⟨d₁, hd₁def⟩ : ∃ d₁, d₁ = g₁⁻¹ * (z * t) * g₁ := ⟨_, rfl⟩
  rw [← hd₁def] at hd₁S
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G,
      D = conjSub g₁ ((S' : Subgroup G) ⊓ Subgroup.centralizer ({d₁} : Set G)) := ⟨_, rfl⟩
  have hD2 : IsPGroup 2 ↥D := by
    rw [hD]
    exact (S'.isPGroup'.to_le inf_le_left).map _
  have hDC : D ≤ Subgroup.centralizer ({z * t} : Set G) := by
    rw [hD]
    rintro x ⟨s, hs', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsc := Subgroup.mem_centralizer_singleton_iff.1 hs'.2
    have ha_eq : z * t = g₁ * d₁ * g₁⁻¹ := by rw [hd₁def]; group
    show g₁ * s * g₁⁻¹ * (z * t) = (z * t) * (g₁ * s * g₁⁻¹)
    rw [ha_eq]
    calc g₁ * s * g₁⁻¹ * (g₁ * d₁ * g₁⁻¹) = g₁ * (s * d₁) * g₁⁻¹ := by group
      _ = g₁ * (d₁ * s) * g₁⁻¹ := by rw [hsc]
      _ = g₁ * d₁ * g₁⁻¹ * (g₁ * s * g₁⁻¹) := by group
  obtain ⟨V, hV, hDV⟩ := IsSylow2In.exists_ge hD2 hDC
  obtain ⟨c, hcC, hcV⟩ := exists_conj_of_isSylow2In hS'a hV
  have hca : c * (z * t) = (z * t) * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hd₂ : (c⁻¹ * g₁)⁻¹ * (z * t) * (c⁻¹ * g₁) = d₁ := by
    calc (c⁻¹ * g₁)⁻¹ * (z * t) * (c⁻¹ * g₁) = g₁⁻¹ * (c * (z * t) * c⁻¹) * g₁ := by group
      _ = g₁⁻¹ * (z * t) * g₁ := by rw [hca]; group
      _ = d₁ := hd₁def.symm
  refine ⟨c⁻¹ * g₁, ?_, by rw [hd₂]; exact hd₁S, ?_⟩
  · intro h
    apply hg₁H
    have : g₁ = c * (c⁻¹ * g₁) := by group
    rw [this]
    exact (H274 Ω K z).mul_mem (haC hcC) h
  · intro s hsS hsd
    rw [hd₂] at hsd
    have hsc : s ∈ Subgroup.centralizer ({d₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hsd.symm
    have h1 : g₁ * s * g₁⁻¹ ∈ D := by
      rw [hD]
      exact conj_mem_conjSub ⟨hsS, hsc⟩
    have h2 : g₁ * s * g₁⁻¹ ∈ conjSub c ((S' : Subgroup G) ⊓
        Subgroup.centralizer ({z * t} : Set G)) := hcV ▸ hDV h1
    have h3 := (mem_conjSub_iff.1 h2).1
    have : (c⁻¹ * g₁) * s * (c⁻¹ * g₁)⁻¹ = c⁻¹ * (g₁ * s * g₁⁻¹) * c := by group
    rw [this]
    exact h3

omit [Finite G] in
theorem conj_eq_of_conjSub_eq {M X : Subgroup G} {x n : G} (hx : IsUniqueInvolution M x)
    (hXM : X ≤ M) (hxX : x ∈ X) (hn : conjSub n X = X) : n * x * n⁻¹ = x := by
  have hmem : n * x * n⁻¹ ∈ conjSub n X := conj_mem_conjSub hxX
  rw [hn] at hmem
  have hsq : n * x * n⁻¹ * (n * x * n⁻¹) = 1 := by
    calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
      _ = 1 := by rw [hx.sq]; group
  rcases hx.unique _ (hXM hmem) hsq with h | h
  · exfalso
    apply hx.ne_one
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exact h

omit [Finite G] in
theorem commute_mul_conj {d r : G} (hd : d * d = 1)
    (hr : r * (d * r * d⁻¹) = (d * r * d⁻¹) * r) :
    d * (r * (d * r * d⁻¹)) = (r * (d * r * d⁻¹)) * d := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [hdi] at hr ⊢
  calc d * (r * (d * r * d)) = d * ((d * r * d) * r) := by rw [hr]
    _ = (d * d) * r * (d * r) := by group
    _ = r * (d * r) := by rw [hd, one_mul]
    _ = r * (d * r * (d * d)) := by rw [hd, mul_one]
    _ = (r * (d * r * d)) * d := by group

theorem eight_le_card_RSet {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S' : Sylow 2 G}
    (hRS' : R ≤ (S' : Subgroup G)) (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G}
    (hg : g ∉ H274 Ω K z) (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hCS : ∀ s ∈ (S' : Subgroup G), (g⁻¹ * (z * t) * g) * s = s * (g⁻¹ * (z * t) * g) →
      g * s * g⁻¹ ∈ (S' : Subgroup G)) :
    8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)} := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  obtain ⟨d, hd⟩ : ∃ d, d = g⁻¹ * (z * t) * g := ⟨_, rfl⟩
  have hfree : conjSub d R ≠ R := by
    rw [hd]
    exact conjSub_ne_of_not_mem_H274 hs hcomp hS'H hg hRS' hK hRsyl hRΩ hs.hz
  rw [← hd] at hdS hCS
  have hdd : d * d = 1 := by
    rw [hd]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [mul_self_zt hp hΩ hs.hz hs.hJ hs.ht]; group
  have hR'Ω : conjSub d R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ d
  have hR'S : conjSub d R ≤ (S' : Subgroup G) := by
    have := conjSub_mono (n := d) hRS'
    rwa [conjSub_eq_self_of_mem hdS] at this
  have hcomm : Commutes R (conjSub d R) :=
    l6_7_proved p f hp hq G Ω hΩ S' R hRΩ _ hR'Ω hRS' hR'S (Ne.symm hfree)
  have hM : conjSub d K ∈ omegaNbr Ω K :=
    conjSub_mem_omegaNbr hp hq hΩ hK hRΩ hRK hRS' hs.hz hdS hfree
  have hCe : Subgroup.centralizer ({z * (d * z * d⁻¹)} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hM (hs.hz.conj d)
  have hq₀ : ∀ r : ↥R, g * ((r : G) * (d * r * d⁻¹)) * g⁻¹ ∈ (S' : Subgroup G) := by
    intro r
    have hrS : (r : G) ∈ (S' : Subgroup G) := hRS' r.2
    have hr'S : d * r * d⁻¹ ∈ (S' : Subgroup G) :=
      S'.mul_mem (S'.mul_mem hdS hrS) (S'.inv_mem hdS)
    exact hCS _ (S'.mul_mem hrS hr'S)
      (commute_mul_conj hdd (hcomm r r.2 _ (conj_mem_conjSub r.2)))
  let F : ↥R → {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)} := fun r =>
    ⟨conjSub (g * ((r : G) * (d * r * d⁻¹)) * g⁻¹) R, RSet.conj hΩ.conjInvariant hRΩ _, by
      have := conjSub_mono (n := g * ((r : G) * (d * r * d⁻¹)) * g⁻¹) hRS'
      rwa [conjSub_eq_self_of_mem (hq₀ r)] at this⟩
  have hinj : Function.Injective F := by
    intro r r' hrr
    have h1 : conjSub (g * ((r : G) * (d * r * d⁻¹)) * g⁻¹) R =
        conjSub (g * ((r' : G) * (d * r' * d⁻¹)) * g⁻¹) R := congrArg Subtype.val hrr
    by_contra hne
    have hρR : (r : G)⁻¹ * r' ∈ R := R.mul_mem (R.inv_mem r.2) r'.2
    have hρ1 : (r : G)⁻¹ * r' ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.mp h))
    have h2 : conjSub ((g * ((r : G) * (d * r * d⁻¹)) * g⁻¹)⁻¹ *
        (g * ((r' : G) * (d * r' * d⁻¹)) * g⁻¹)) R = R := by
      rw [conjSub_mul, ← h1, conjSub_inv_conjSub]
    have hc : ((r : G)⁻¹ * r') * (d * r * d⁻¹)⁻¹ = (d * r * d⁻¹)⁻¹ * ((r : G)⁻¹ * r') :=
      hcomm _ hρR _ ((conjSub d R).inv_mem (conj_mem_conjSub r.2))
    have hκ : (g * ((r : G) * (d * r * d⁻¹)) * g⁻¹)⁻¹ * (g * ((r' : G) * (d * r' * d⁻¹)) * g⁻¹)
        = g * (((r : G)⁻¹ * r') * (d * ((r : G)⁻¹ * r') * d⁻¹)) * g⁻¹ := by
      calc _ = g * ((d * r * d⁻¹)⁻¹ * ((r : G)⁻¹ * r') * (d * r' * d⁻¹)) * g⁻¹ := by group
        _ = g * (((r : G)⁻¹ * r') * (d * r * d⁻¹)⁻¹ * (d * r' * d⁻¹)) * g⁻¹ := by rw [← hc]
        _ = _ := by group
    rw [hκ] at h2
    have hρ'R : d * ((r : G)⁻¹ * r') * d⁻¹ ∈ conjSub d R := conj_mem_conjSub hρR
    obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hRsyl.2.1
      (x := (⟨(r : G)⁻¹ * r', hρR⟩ : ↥R)) (fun h => hρ1 (congrArg Subtype.val h))
    have hn' : orderOf (((r : G)⁻¹ * r') ^ n) = 2 := by
      rw [← hn, ← Subgroup.orderOf_coe]
      rfl
    have hρn : ((r : G)⁻¹ * r') ^ n = z := by
      have hsq : ((r : G)⁻¹ * r') ^ n * ((r : G)⁻¹ * r') ^ n = 1 := by
        rw [← pow_two]
        have := pow_orderOf_eq_one (((r : G)⁻¹ * r') ^ n)
        rwa [hn'] at this
      rcases hs.hz.unique _ (hRK (R.pow_mem hρR n)) hsq with h | h
      · rw [h, orderOf_one] at hn'
        omega
      · exact h
    have hκn : (((r : G)⁻¹ * r') * (d * ((r : G)⁻¹ * r') * d⁻¹)) ^ n = z * (d * z * d⁻¹) := by
      rw [Commute.mul_pow (hcomm _ hρR _ hρ'R), conj_pow, hρn]
    have hN : g * (z * (d * z * d⁻¹)) * g⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
      have h3 : g * (((r : G)⁻¹ * r') * (d * ((r : G)⁻¹ * r') * d⁻¹)) * g⁻¹ ∈
          Subgroup.normalizer (R : Set G) := mem_normalizer_iff_conjSub_eq.mpr h2
      have h4 := Subgroup.pow_mem _ h3 n
      rwa [conj_pow, hκn] at h4
    have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
    have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
    have hzc := conj_eq_of_conjSub_eq hs.hz hRK hzR (mem_normalizer_iff_conjSub_eq.mp hN)
    have hzc' : (g * (z * (d * z * d⁻¹)) * g⁻¹) * z = z * (g * (z * (d * z * d⁻¹)) * g⁻¹) := by
      calc (g * (z * (d * z * d⁻¹)) * g⁻¹) * z
          = ((g * (z * (d * z * d⁻¹)) * g⁻¹) * z * (g * (z * (d * z * d⁻¹)) * g⁻¹)⁻¹) *
            (g * (z * (d * z * d⁻¹)) * g⁻¹) := by group
        _ = z * (g * (z * (d * z * d⁻¹)) * g⁻¹) := by rw [hzc]
    have hyC : g⁻¹ * z * g ∈ Subgroup.centralizer ({z * (d * z * d⁻¹)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * z * g * (z * (d * z * d⁻¹))
          = g⁻¹ * (z * (g * (z * (d * z * d⁻¹)) * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * (z * (d * z * d⁻¹)) * g⁻¹) * z) * g := by rw [hzc']
        _ = (z * (d * z * d⁻¹)) * (g⁻¹ * z * g) := by group
    exact hg (mem_H274_of_conj_mem_H274 hs hcomp (hCe hyC))
  have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
  have := Nat.card_le_card_of_injective F hinj
  omega

omit [Finite G] in
theorem mul_self_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy]; group

omit [Finite G] in
theorem mul_ne_one_of_ne {x y : G} (hx : x * x = 1) (hxy : x ≠ y) : x * y ≠ 1 := by
  intro h
  apply hxy
  calc x = x * 1 := (mul_one x).symm
    _ = x * (x * y) := by rw [h]
    _ = y := by rw [← mul_assoc, hx, one_mul]

@[expose] def IsFrameInv (Ω : Set (Subgroup G)) (X : Subgroup G) (x : G) : Prop :=
  ∃ M ∈ Ω, IsSylow2In X M ∧ IsUniqueInvolution M x

omit [Finite G] in
theorem IsFrameInv.conj (hΩ : ConjInvariant Ω) {X : Subgroup G} {x : G} (h : IsFrameInv Ω X x)
    (n : G) : IsFrameInv Ω (conjSub n X) (n * x * n⁻¹) := by
  obtain ⟨M, hM, hXM, hx⟩ := h
  exact ⟨conjSub n M, hΩ n M hM, hXM.conj n, hx.conj n⟩

theorem IsFrameInv.mem (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {X : Subgroup G} {x : G}
    (hX : X ∈ RSet Ω) (h : IsFrameInv Ω X x) : x ∈ X := by
  obtain ⟨M, hM, hXM, hx⟩ := h
  have h8 := hΩ.eight_le_of_mem_RSet hp hX
  exact T3.mem_of_isPGroup hx hXM.1 hXM.2.1 (by omega)

omit [Finite G] in
theorem IsFrameInv.central {X : Subgroup G} {x : G} (h : IsFrameInv Ω X x) {y : G} (hy : y ∈ X) :
    x * y = y * x := by
  obtain ⟨M, hM, hXM, hx⟩ := h
  have h1 := hx.conj_eq (n := y) (conjSub_eq_self_of_mem (hXM.1 hy))
  calc x * y = (y * x * y⁻¹) * y := by rw [h1]
    _ = y * x := by group

theorem IsFrameInv.isConj {K : Subgroup G} {z : G} (hs : AscStand p f Ω K)
    (hz : IsUniqueInvolution K z) {X : Subgroup G} {x : G} (h : IsFrameInv Ω X x) :
    IsConj z x := by
  obtain ⟨M, hM, -, hx⟩ := h
  obtain ⟨c, hc⟩ := hs.trans M hM
  have h1 : IsUniqueInvolution M (c * z * c⁻¹) := hc ▸ hz.conj c
  exact isConj_iff.2 ⟨c, (hx.eq h1).symm⟩

theorem IsFrameInv.ne {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) {X Y : Subgroup G} {x y : G} (hx : IsFrameInv Ω X x)
    (hy : IsFrameInv Ω Y y) (hXY : X ≠ Y) (hc : Commutes X Y) : x ≠ y := by
  intro hxy
  obtain ⟨M, hM, hXM, hxM⟩ := hx
  obtain ⟨N, hN, hYN, hyN⟩ := hy
  have hNM : N ∈ twinSet Ω M := ⟨hN, x, hxM, hxy ▸ hyN⟩
  have hNM' : N = M := noTwins_of_mem hs.stand.hyp.conjInvariant hs.stand.trans hs.noTwins hM N hNM
  rw [hNM'] at hYN
  exact hXY (eq_of_commutes_isSylow2In hXM hYN hc).symm

theorem exists_four_group {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S' : Sylow 2 G}
    (hRS' : R ≤ (S' : Subgroup G)) (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G}
    (hg : g ∉ H274 Ω K z) (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)}) :
    ∃ u v : G, u ∈ (S' : Subgroup G) ∧ v ∈ (S' : Subgroup G) ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧
      (g⁻¹ * (z * t) * g) * u = u * (g⁻¹ * (z * t) * g) ∧
      (g⁻¹ * (z * t) * g) * v = v * (g⁻¹ * (z * t) * g) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, u * y = y * u) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, v * y = y * v) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  exact exists_four_group_gen hΩ.conjInvariant hK hs.hz hRΩ
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK) hRS'
    (fun hM => hΩ.exists_uniqueInvolution hp hq hM)
    (mul_self_zt hp hΩ hs.hz hs.hJ hs.ht)
    (fun hXS hM hXM hXΩ hx => conjSub_ne_of_not_mem_H274 hs hcomp hS'H hg hXS hM hXM hXΩ hx)
    (fun hX hY hXS hYS hXY => l6_7_proved p f hp hq G Ω hΩ S' _ hX _ hY hXS hYS hXY)
    (fun hX hx => IsFrameInv.mem hp hΩ hX hx)
    (fun hx hy hXY hc => IsFrameInv.ne hs hx hy hXY hc)
    hdS hcount

omit [Finite G] in
theorem mul_comm_mul {x w y : G} (h1 : x * y = y * x) (h2 : w * y = y * w) :
    (x * w) * y = y * (x * w) := by
  calc x * w * y = x * (w * y) := by group
    _ = x * (y * w) := by rw [h2]
    _ = (x * y) * w := by group
    _ = (y * x) * w := by rw [h1]
    _ = y * (x * w) := by group

theorem mem_H274_of_min {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z)
    {g : G} (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) : g ∈ H274 Ω K z := by
  by_contra hg
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
  have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  obtain ⟨S', hRS', hS'a⟩ := exists_sylow_centralizer hs
  have hS'H := sylow_le_H274_of_ge hs hRS'
  obtain ⟨g', hg', hdS, hCS⟩ := exists_normalized_conj hs hS'a hS'H hg hgH
  have hcount := eight_le_card_RSet hs hcomp hRS' hS'H hg' hdS hCS
  obtain ⟨u, v, huS, hvS, hu1, hv1, huv, hu2, hv2, hc, hdu, hdv, hcu, hcv⟩ :=
    exists_four_group hs hcomp hRS' hS'H hg' hdS hcount
  obtain ⟨S₃, hS₃⟩ : ∃ S₃ : Sylow 2 G, (S₃ : Subgroup G) = conjSub g'⁻¹ (S' : Subgroup G) :=
    ⟨g'⁻¹ • S', by
      rw [Sylow.coe_subgroup_smul]
      ext x
      simp [conjSub, Subgroup.pointwise_smul_def]⟩
  have hu₃ : u ∈ (S₃ : Subgroup G) := by
    rw [hS₃, mem_conjSub_iff]
    simpa using hCS u huS hdu
  have hv₃ : v ∈ (S₃ : Subgroup G) := by
    rw [hS₃, mem_conjSub_iff]
    simpa using hCS v hvS hdv
  have hgood := sylow_le_H274_of_good_four hs hcomp hu₃ hv₃ hu1 hv1 huv hu2 hv2 hc
    (hmin S' hRS' hcount u huS hu2 hu1 hcu) (hmin S' hRS' hcount v hvS hv2 hv1 hcv)
    (hmin S' hRS' hcount (u * v) (S'.mul_mem huS hvS) (mul_self_of_commute hu2 hv2 hc)
      (mul_ne_one_of_ne hu2 huv)
      (fun Y hY hYS y hy => mul_comm_mul (hcu Y hY hYS y hy) (hcv Y hY hYS y hy)))
  have hz₃ : g'⁻¹ * z * g' ∈ (S₃ : Subgroup G) := by
    rw [hS₃]
    simpa using conj_mem_conjSub (n := g'⁻¹) (hRS' hzR)
  exact hg' (mem_H274_of_conj_mem_H274 hs hcomp (hgood hz₃))

end Min

end T8

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_4M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
        8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
          ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
            (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
              Subgroup.centralizer ({x} : Set G) ≤ T8.H274 Ω K z

variable {p f}

theorem c27_4a_of_min (h2 : C27_2 p f) (hmin : C27_4M p f) : C27_4a p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hcomp : dComp Ω K = dstarComp Ω K := h2 G Ω K J S R T W z t hs hdisc
  have hmin' := hmin G Ω K J S R T W z t hs hdisc
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  exact T8.mem_H274_of_min hs hcomp hmin' hg

theorem c27_4b_of_min (h2 : C27_2 p f) (hmin : C27_4M p f) : C27_4b p f :=
  c27_4b_of_c27_4a (c27_4a_of_min h2 hmin)

end CFSG.ClassicalInvolution.Asc77
