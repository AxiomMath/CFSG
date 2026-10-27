module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Rung

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

structure OuterS16Ctx (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G)
    (T E : Subgroup G) (Q : Sylow 2 G) (x : G) (B : Subgroup G) (β : G) (S : Subgroup G) :
    Prop where
  hyp : OuterS16Hyp G L z t T E Q x B β
  S2 : IsPGroup 2 S
  SC : S ≤ centralizer (E : Set G)
  Smax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S
  zS : z ∈ S
  card16 : Nat.card ↥S = 16

theorem OuterS16Hyp.exists_ctx {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T E : Subgroup G} {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G}
    (h : OuterS16Hyp G L z t T E Q x B β) :
    ∃ S : Subgroup G, OuterS16Ctx G L z t T E Q x B β S := by
  obtain ⟨S, hS2, hSC, hSmax, hzS, hcard⟩ := h.sixteen
  exact ⟨S, ⟨h, hS2, hSC, hSmax, hzS, hcard⟩⟩

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem facts : OuterSylowFacts z E S := (c.hyp.sylowS S c.S2 c.SC c.Smax c.zS).1

theorem BS : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b := (c.hyp.sylowS S c.S2 c.SC c.Smax c.zS).2

theorem zconj : ∀ g : G, g * z * g⁻¹ ∈ S → ∃ s ∈ S, g * z * g⁻¹ = s * z * s⁻¹ := c.facts.2.2

theorem shape :
    Nonempty (↥S ≃* DihedralGroup 8) ∨ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup 4) :=
  shape_of_card_sixteen c.facts.1 c.card16

theorem t_comm_S : ∀ s ∈ S, s * t = t * s := fun s hs =>
  (mem_centralizer_iff.1 (c.SC hs) t c.hyp.outerE.econfig.t_mem).symm

theorem t_mem_S : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := c.hyp.outerE.cfg
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcfg.t_sq) hcfg.t_ne
  have hZ : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
  have hSc : S ≤ centralizer ((zpowers t : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute t s from (c.t_comm_S s hs).symm) k).eq
  have hSn : S ≤ normalizer ((zpowers t : Subgroup G) : Set G) :=
    hSc.trans (centralizer_le_normalizer _)
  have hS' : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) := c.S2.to_sup_of_normal_right' hZ hSn
  have htC : t ∈ centralizer (E : Set G) :=
    mem_centralizer_iff.2 fun e he => c.hyp.outerE.t_comm_E he
  have hle : (S ⊔ zpowers t : Subgroup G) ≤ centralizer (E : Set G) :=
    sup_le c.SC (zpowers_le.2 htC)
  have heq := c.Smax _ hS' hle le_sup_left
  rw [← heq]
  exact mem_sup_right (mem_zpowers t)

theorem cent_z_mem_S {v : G} (hv : v ∈ centralizer (E : Set G)) (hvz : v * z = z * v) : v ∈ S := by
  rcases c.hyp.centZ v hv hvz with h1 | h1 | h1 | h1
  · rw [h1]; exact one_mem _
  · rw [h1]; exact c.zS
  · rw [h1]; exact c.t_mem_S
  · rw [h1]; exact mul_mem c.t_mem_S c.zS

theorem normHE_norm_S {n : G} (hn : n ∈ normalizer (E : Set G)) (hnz : n * z = z * n) {s : G}
    (hs : s ∈ S) : n * s * n⁻¹ ∈ S := by
  obtain ⟨hS'2, hS'E, hS'max⟩ := conj_max_cent hn c.S2 c.SC c.Smax
  obtain ⟨g, hgC, hg⟩ := sylow_conj (Θ := centralizer (E : Set G)) c.SC hS'E c.S2 hS'2
    (fun R hR hRE hle => (c.Smax R hR hRE hle).le) (fun R hR hRE hle => hS'max R hR hRE hle)
  have hmem : ∀ y : G, y ∈ S.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * y * n ∈ S := by
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro hy
      exact ⟨n⁻¹ * y * n, hy, by simp [MulAut.conj_apply]; group⟩
  have hzS' : z ∈ S.map (MulAut.conj n).toMonoidHom := by
    rw [hmem]
    have : n⁻¹ * z * n = z := by
      calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
        _ = n⁻¹ * (n * z) := by rw [hnz]
        _ = z := by group
    rw [this]
    exact c.zS
  have hgz : g⁻¹ * z * g ∈ S := (hg z).1 hzS'
  obtain ⟨s', hs', hs'z⟩ := c.zconj g⁻¹ (by simpa using hgz)
  simp only [inv_inv] at hs'z
  have hgS : g ∈ S := by
    have hgs'C : g * s' ∈ centralizer (E : Set G) := mul_mem hgC (c.SC hs')
    have hcomm : (g * s') * z = z * (g * s') := by
      have h1 : (g * s') * z * (g * s')⁻¹ = z := by
        calc (g * s') * z * (g * s')⁻¹ = g * (s' * z * s'⁻¹) * g⁻¹ := by group
          _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hs'z]
          _ = z := by group
      calc (g * s') * z = ((g * s') * z * (g * s')⁻¹) * (g * s') := by group
        _ = z * (g * s') := by rw [h1]
    have := mul_mem (c.cent_z_mem_S hgs'C hcomm) (inv_mem hs')
    simpa using this
  have hy : n * s * n⁻¹ ∈ S.map (MulAut.conj n).toMonoidHom := ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hy' := (hg _).1 hy
  have := mul_mem (mul_mem hgS hy') (inv_mem hgS)
  simpa [mul_assoc] using this

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
