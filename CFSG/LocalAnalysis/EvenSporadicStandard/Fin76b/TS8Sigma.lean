module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Hyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem conj_max_cent {G : Type} [Group G] {E : Subgroup G} {n : G}
    (hn : n ∈ normalizer (E : Set G)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPE : P ≤ centralizer (E : Set G))
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → P ≤ R → R = P) :
    IsPGroup 2 (P.map (MulAut.conj n).toMonoidHom) ∧
      P.map (MulAut.conj n).toMonoidHom ≤ centralizer (E : Set G) ∧
      ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) →
        P.map (MulAut.conj n).toMonoidHom ≤ R → R ≤ P.map (MulAut.conj n).toMonoidHom := by
  have hnE : ∀ e ∈ E, n * e * n⁻¹ ∈ E := fun e he => (mem_normalizer_iff.1 hn e).1 he
  have hnE' : ∀ e ∈ E, n⁻¹ * e * n ∈ E := fun e he => by
    have := (mem_normalizer_iff.1 (inv_mem hn : n⁻¹ ∈ normalizer (E : Set G)) e).1 he
    simpa using this
  have hmem : ∀ y : G, y ∈ P.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * y * n ∈ P := by
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro hy
      exact ⟨n⁻¹ * y * n, hy, by simp [MulAut.conj_apply]; group⟩
  refine ⟨hP.map _, ?_, ?_⟩
  · intro y hy
    rw [hmem] at hy
    refine mem_centralizer_iff.2 fun e he => ?_
    have h1 := mem_centralizer_iff.1 (hPE hy) (n⁻¹ * e * n) (hnE' e he)
    calc e * y = n * ((n⁻¹ * e * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
      _ = y * e := by group
  · intro R hR hRE hle
    have hR₀2 : IsPGroup 2 (R.map (MulAut.conj n⁻¹).toMonoidHom) := hR.map _
    have hR₀E : R.map (MulAut.conj n⁻¹).toMonoidHom ≤ centralizer (E : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      refine mem_centralizer_iff.2 fun e he => ?_
      have h1 := mem_centralizer_iff.1 (hRE hr) (n * e * n⁻¹) (hnE e he)
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
      calc e * (n⁻¹ * r * n) = n⁻¹ * ((n * e * n⁻¹) * r) * n := by group
        _ = n⁻¹ * (r * (n * e * n⁻¹)) * n := by rw [h1]
        _ = n⁻¹ * r * n * e := by group
    have hSle : P ≤ R.map (MulAut.conj n⁻¹).toMonoidHom := by
      intro s hs
      have h2 : n⁻¹ * (n * s * n⁻¹) * n = s := by group
      refine ⟨n * s * n⁻¹, hle ((hmem _).2 (by rw [h2]; exact hs)), ?_⟩
      simpa [MulAut.conj_apply] using h2
    have heq := hmax _ hR₀2 hR₀E hSle
    intro r hr
    rw [hmem]
    have : n⁻¹ * r * n ∈ R.map (MulAut.conj n⁻¹).toMonoidHom := ⟨r, hr, by simp [MulAut.conj_apply]⟩
    rw [heq] at this
    exact this

theorem actOn_mem_ker {G : Type} [Group G] {E X : Subgroup G} (hX : X ≤ normalizer (E : Set G))
    {x : ↥X} (hx : ∀ e ∈ E, (x : G) * e = e * (x : G)) : x ∈ (actOn E X hX).ker := by
  rw [MonoidHom.mem_ker]
  refine MulEquiv.ext fun e => Subtype.ext ?_
  rw [actOn_apply, MulAut.one_apply]
  calc (x : G) * e * (x : G)⁻¹ = ((e : G) * x) * (x : G)⁻¹ := by rw [hx e e.2]
    _ = e := by group

structure OuterSigma {G : Type} [Group G] (L : Subgroup G) (z : G) (T E S : Subgroup G) (α σ : G) :
    Prop where
  mem_T : σ ∈ T
  sq : σ * σ = 1
  not_mem : σ ∉ L ⊔ zpowers z
  comm_z : σ * z = z * σ
  norm_E : σ ∈ normalizer (E : Set G)
  norm_S : ∀ s ∈ S, σ * s * σ⁻¹ ∈ S
  fix_alpha : σ * α * σ⁻¹ = α


namespace OuterS8Hyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (h : OuterS8Hyp G L z t T E Q x B β S)

include h

theorem t_mem_S' : t ∈ S := by
  obtain ⟨α, hα⟩ := h.alpha
  have hrel := hα.rel
  have : t = α * z * α⁻¹ * z⁻¹ := by
    calc t = (t * (z * α)) * α⁻¹ * z⁻¹ := by group
      _ = α * z * α⁻¹ * z⁻¹ := by rw [← hrel]
  rw [this]
  exact mul_mem (mul_mem (mul_mem hα.mem h.zS) (inv_mem hα.mem)) (inv_mem h.zS)

theorem exists_conj_zt_S : ∃ s ∈ S, s * z * s⁻¹ = z * t := by
  obtain ⟨α, hα⟩ := h.alpha
  refine ⟨α, hα.mem, ?_⟩
  calc α * z * α⁻¹ = (α * z) * α⁻¹ := by group
    _ = (t * (z * α)) * α⁻¹ := by rw [hα.rel]
    _ = t * z := by group
    _ = z * t := h.outerE.cfg.t_comm_z

theorem normHE_norm_S {n : G} (hn : n ∈ normalizer (E : Set G)) (hnz : n * z = z * n) {s : G}
    (hs : s ∈ S) : n * s * n⁻¹ ∈ S := by
  have hcfg := h.outerE.cfg
  have htE : t ∈ E := h.outerE.econfig.t_mem
  obtain ⟨hS'2, hS'E, hS'max⟩ := conj_max_cent hn h.S2 h.SC h.Smax
  obtain ⟨g, hgC, hg⟩ := sylow_conj (Θ := centralizer (E : Set G)) h.SC hS'E h.S2 hS'2
    (fun R hR hRE hle => (h.Smax R hR hRE hle).le) (fun R hR hRE hle => hS'max R hR hRE hle)
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
    exact h.zS
  have hgz : g⁻¹ * z * g ∈ S := (hg z).1 hzS'
  have hcases := h.h67 g⁻¹ (by simpa using hgz)
  simp only [inv_inv] at hcases
  have hgS : g ∈ S := by
    have hgE : ∀ e ∈ E, g * e = e * g := fun e he => (mem_centralizer_iff.1 hgC e he).symm
    have htg : g * t * g⁻¹ = t := by
      calc g * t * g⁻¹ = (g * t) * g⁻¹ := by group
        _ = (t * g) * g⁻¹ := by rw [hgE t htE]
        _ = t := by group
    have hcentS : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v ∈ S := by
      intro v hv hvz
      rcases h.centZ v hv hvz with h1 | h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact h.zS
      · rw [h1]; exact h.t_mem_S'
      · rw [h1]; exact mul_mem h.t_mem_S' h.zS
    rcases hcases with h1 | h1
    · refine hcentS g hgC ?_
      calc g * z = g * (g⁻¹ * z * g) := by rw [h1]
        _ = z * g := by group
    · have hgzt : (g * z * g⁻¹) * t = z := by
        calc (g * z * g⁻¹) * t = (g * z * g⁻¹) * (g * t * g⁻¹) := by rw [htg]
          _ = g * (z * t) * g⁻¹ := by group
          _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
          _ = z := by group
      have hgz' : g * z * g⁻¹ = z * t := by
        have := eq_mul_inv_of_mul_eq hgzt
        rwa [inv_eq_of_mul_eq_one_right hcfg.t_sq] at this
      obtain ⟨s₀, hs₀, hs₀z⟩ := h.exists_conj_zt_S
      have hc : (g * s₀) * z * (g * s₀)⁻¹ = z := by
        calc (g * s₀) * z * (g * s₀)⁻¹ = g * (s₀ * z * s₀⁻¹) * g⁻¹ := by group
          _ = g * (z * t) * g⁻¹ := by rw [hs₀z]
          _ = (g * z * g⁻¹) * (g * t * g⁻¹) := by group
          _ = (z * t) * t := by rw [hgz', htg]
          _ = z := by rw [mul_assoc, hcfg.t_sq, mul_one]
      have hcomm : (g * s₀) * z = z * (g * s₀) := by
        calc (g * s₀) * z = ((g * s₀) * z * (g * s₀)⁻¹) * (g * s₀) := by group
          _ = z * (g * s₀) := by rw [hc]
      have hgs₀S : g * s₀ ∈ S := hcentS _ (mul_mem hgC (h.SC hs₀)) hcomm
      have := mul_mem hgs₀S (inv_mem hs₀)
      simpa using this
  have hy : n * s * n⁻¹ ∈ S.map (MulAut.conj n).toMonoidHom := ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hy' := (hg _).1 hy
  have := mul_mem (mul_mem hgS hy') (inv_mem hgS)
  simpa [mul_assoc] using this


theorem normHE_le_normU :
    normalizer (E : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
  have key : ∀ n : G, n ∈ normalizer (E : Set G) → n * z = z * n →
      ∀ u ∈ S ⊔ E, n * u * n⁻¹ ∈ S ⊔ E := by
    intro n hn hnz u hu
    have hle : S ⊔ E ≤ (S ⊔ E).comap (MulAut.conj n).toMonoidHom :=
      sup_le (fun s hs => mem_sup_left (h.normHE_norm_S hn hnz hs))
        (fun e he => mem_sup_right ((mem_normalizer_iff.1 hn e).1 he))
    exact hle hu
  intro n hn
  have hn1 : n ∈ normalizer (E : Set G) := hn.1
  have hnz : n * z = z * n := mem_centralizer_singleton_iff.1 hn.2
  have hnz' : n⁻¹ * z = z * n⁻¹ := by
    calc n⁻¹ * z = n⁻¹ * (z * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * z) * n⁻¹ := by rw [hnz]
      _ = z * n⁻¹ := by group
  rw [mem_normalizer_iff]
  intro u
  constructor
  · exact key n hn1 hnz u
  · intro hu
    have := key n⁻¹ (inv_mem hn1) hnz' _ hu
    simpa [mul_assoc] using this

theorem cent_z_normU :
    normalizer ((S ⊔ E : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
      normalizer (E : Set G) ⊓ centralizer ({z} : Set G) := by
  refine le_antisymm ?_ ?_
  · rintro m ⟨hmU, hmz⟩
    refine ⟨?_, hmz⟩
    refine h.outerE.normalizes_of_cent_z ⟨x, h.x_z⟩ h.SC h.centZ hmU ?_
    have := mem_centralizer_singleton_iff.1 hmz
    calc m * z * m⁻¹ = (z * m) * m⁻¹ := by rw [this]
      _ = z := by group
  · exact fun m hm => ⟨h.normHE_le_normU hm, hm.2⟩


theorem t_comm_S' : ∀ s ∈ S, s * t = t * s := fun s hs =>
  (mem_centralizer_iff.1 (h.SC hs) t h.outerE.econfig.t_mem).symm

theorem z_alpha_z {α : G} (hα : AlphaSpec S z t α) : z * α * z = α * t := by
  have hcfg := h.outerE.cfg
  calc z * α * z = z * (α * z) := by group
    _ = z * (t * (z * α)) := by rw [hα.rel]
    _ = (z * t) * (z * α) := by group
    _ = (t * z) * (z * α) := by rw [← hcfg.t_comm_z]
    _ = t * (z * z) * α := by group
    _ = t * α := by rw [hcfg.z_sq, mul_one]
    _ = α * t := (h.t_comm_S' α hα.mem).symm

theorem card_normHE :
    Nat.card ↥(normalizer (E : Set G) ⊓ centralizer ({z} : Set G)) = 7680 := by
  have hcfg := h.outerE.cfg
  set NH := normalizer (E : Set G) ⊓ centralizer ({z} : Set G) with hNH
  have hX : NH ≤ normalizer (E : Set G) := inf_le_left
  set f := actOn E NH hX with hf
  have hrange : f.range = ⊤ := by
    refine eq_top_iff.2 fun α _ => ?_
    obtain ⟨n, hnz, hnα⟩ := h.outerE.exists_cover ⟨x, h.x_z⟩ h.wFacts h.autE h.cardT α
    exact ⟨⟨n.1, n.2, hnz⟩, hnα⟩
  have hr : Nat.card f.range = 1920 := by rw [hrange, Subgroup.card_top, h.autE]
  have hzN : z ∈ normalizer (E : Set G) := centralizer_le_normalizer E (h.SC h.zS)
  have htN : t ∈ normalizer (E : Set G) := le_normalizer h.outerE.econfig.t_mem
  have hzNH : z ∈ NH := ⟨hzN, mem_centralizer_singleton_iff.2 rfl⟩
  have htNH : t ∈ NH := ⟨htN, mem_centralizer_singleton_iff.2 hcfg.t_comm_z⟩
  have hzker : (⟨z, hzNH⟩ : ↥NH) ∈ f.ker := actOn_mem_ker hX (fun e he =>
    (mem_centralizer_iff.1 (h.SC h.zS) e he).symm)
  have htker : (⟨t, htNH⟩ : ↥NH) ∈ f.ker := actOn_mem_ker hX (fun e he =>
    (hcfg.t_central e (h.outerE.E_le_T he)).symm)
  have hker : f.ker.map NH.subtype = zpowers z ⊔ zpowers t := by
    refine le_antisymm ?_ (sup_le (zpowers_le.2 ⟨_, hzker, rfl⟩) (zpowers_le.2 ⟨_, htker, rfl⟩))
    rintro _ ⟨k, hk, rfl⟩
    have hkE : (k : G) ∈ centralizer (E : Set G) :=
      mem_centralizer_iff.2 fun e he => (actOn_ker hX hk e he).symm
    have hkz : (k : G) * z = z * (k : G) := mem_centralizer_singleton_iff.1 k.2.2
    have hzmem : z ∈ zpowers z ⊔ zpowers t := mem_sup_left (mem_zpowers z)
    have htmem : t ∈ zpowers z ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rcases h.centZ _ hkE hkz with h1 | h1 | h1 | h1
    · rw [Subgroup.coe_subtype, h1]; exact one_mem _
    · rw [Subgroup.coe_subtype, h1]; exact hzmem
    · rw [Subgroup.coe_subtype, h1]; exact htmem
    · rw [Subgroup.coe_subtype, h1]; exact mul_mem htmem hzmem
  have hk4 : Nat.card f.ker = 4 := by
    have hc : Nat.card (f.ker.map NH.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective NH.subtype_injective
    rw [hker, h.outerE.card_zpowers_sup] at hc
    omega
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hr, hk4] at h1
  omega


theorem exists_sigma {α : G} (hα : AlphaSpec S z t α) : ∃ σ, OuterSigma L z T E S α σ := by
  have hcfg := h.outerE.cfg
  obtain ⟨σ₀, hσT, hσ2, hσL⟩ := h.sigma
  have hσz : σ₀ * z = z * σ₀ := by
    have := mem_centralizer_singleton_iff.1 (hcfg.T_le hσT)
    exact this
  have hσN : σ₀ ∈ normalizer (E : Set G) := h.outerE.T_le_normalizer ⟨x, h.x_z⟩ hσT
  have hσS : ∀ s ∈ S, σ₀ * s * σ₀⁻¹ ∈ S := fun s hs => h.normHE_norm_S hσN hσz hs
  have hσt : σ₀ * t = t * σ₀ := hcfg.t_central σ₀ hσT
  have hσzi : σ₀ * z * σ₀⁻¹ = z := by
    calc σ₀ * z * σ₀⁻¹ = (z * σ₀) * σ₀⁻¹ := by rw [hσz]
      _ = z := by group
  have hσti : σ₀ * t * σ₀⁻¹ = t := by
    calc σ₀ * t * σ₀⁻¹ = (t * σ₀) * σ₀⁻¹ := by rw [hσt]
      _ = t := by group
  set u := σ₀ * α * σ₀⁻¹ with hu
  have huS : u ∈ S := hσS α hα.mem
  have hu2 : u * u = 1 := by
    calc u * u = σ₀ * (α * α) * σ₀⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hα.sq]; group
  have hα_u : α = σ₀⁻¹ * u * σ₀ := by rw [hu]; group
  have hzt_sq : (α * z) * (α * z) = t := by
    calc (α * z) * (α * z) = α * (z * α * z) := by group
      _ = α * (α * t) := by rw [h.z_alpha_z hα]
      _ = (α * α) * t := by group
      _ = t := by rw [hα.sq, one_mul]
  have hztt_sq : (α * z * t) * (α * z * t) = t := by
    calc (α * z * t) * (α * z * t) = ((α * z) * (α * z)) * (t * t) := by
          have hαzt : (α * z) * t = t * (α * z) := by
            calc α * z * t = α * (z * t) := by group
              _ = α * (t * z) := by rw [hcfg.t_comm_z]
              _ = (α * t) * z := by group
              _ = (t * α) * z := by rw [h.t_comm_S' α hα.mem]
              _ = t * (α * z) := by group
          calc (α * z * t) * (α * z * t) = (α * z) * (t * (α * z)) * t := by group
            _ = (α * z) * ((α * z) * t) * t := by rw [hαzt]
            _ = ((α * z) * (α * z)) * (t * t) := by group
      _ = t := by rw [hzt_sq, hcfg.t_sq, mul_one]
  have hcases : u = α ∨ u = α * t := by
    rcases hα.list u huS with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exfalso
      apply hα.ne_one
      rw [hα_u, h1]; group
    · exfalso
      apply hα.ne_t
      rw [hα_u, h1]
      calc σ₀⁻¹ * t * σ₀ = σ₀⁻¹ * (t * σ₀) := by group
        _ = σ₀⁻¹ * (σ₀ * t) := by rw [hσt]
        _ = t := by group
    · exfalso
      apply hα.ne_z
      rw [hα_u, h1]
      calc σ₀⁻¹ * z * σ₀ = σ₀⁻¹ * (z * σ₀) := by group
        _ = σ₀⁻¹ * (σ₀ * z) := by rw [hσz]
        _ = z := by group
    · exfalso
      apply hα.ne_zt
      rw [hα_u, h1]
      calc σ₀⁻¹ * (z * t) * σ₀ = (σ₀⁻¹ * z * σ₀) * (σ₀⁻¹ * t * σ₀) := by group
        _ = z * t := by
          have e1 : σ₀⁻¹ * z * σ₀ = z := by
            calc σ₀⁻¹ * z * σ₀ = σ₀⁻¹ * (z * σ₀) := by group
              _ = σ₀⁻¹ * (σ₀ * z) := by rw [hσz]
              _ = z := by group
          have e2 : σ₀⁻¹ * t * σ₀ = t := by
            calc σ₀⁻¹ * t * σ₀ = σ₀⁻¹ * (t * σ₀) := by group
              _ = σ₀⁻¹ * (σ₀ * t) := by rw [hσt]
              _ = t := by group
          rw [e1, e2]
    · left; exact h1
    · right; exact h1
    · exfalso
      rw [h1, hzt_sq] at hu2
      exact hcfg.t_ne hu2
    · exfalso
      rw [h1, hztt_sq] at hu2
      exact hcfg.t_ne hu2
  rcases hcases with hu1 | hu1
  · exact ⟨σ₀, hσT, hσ2, hσL, hσz, hσN, hσS, hu1⟩
  · have hzN : z ∈ normalizer (E : Set G) := centralizer_le_normalizer E (h.SC h.zS)
    refine ⟨z * σ₀, mul_mem hcfg.z_mem hσT, ?_, ?_, ?_, mul_mem hzN hσN, ?_, ?_⟩
    · calc z * σ₀ * (z * σ₀) = z * (σ₀ * z) * σ₀ := by group
        _ = z * (z * σ₀) * σ₀ := by rw [hσz]
        _ = (z * z) * (σ₀ * σ₀) := by group
        _ = 1 := by rw [hcfg.z_sq, hσ2, mul_one]
    · intro hmem
      apply hσL
      have hz : z⁻¹ ∈ L ⊔ zpowers z := mem_sup_right (inv_mem (mem_zpowers z))
      have := mul_mem hz hmem
      simpa using this
    · calc z * σ₀ * z = z * (σ₀ * z) := by group
        _ = z * (z * σ₀) := by rw [hσz]
    · intro s hs
      have h1 := hσS s hs
      have : z * σ₀ * s * (z * σ₀)⁻¹ = z * (σ₀ * s * σ₀⁻¹) * z⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem h.zS h1) (inv_mem h.zS)
    · calc z * σ₀ * α * (z * σ₀)⁻¹ = z * (σ₀ * α * σ₀⁻¹) * z⁻¹ := by group
        _ = z * (α * t) * z⁻¹ := by rw [← hu, hu1]
        _ = (z * α * z) * t := by
          have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hcfg.z_sq
          have hzt : z * t = t * z := hcfg.t_comm_z.symm
          calc z * (α * t) * z⁻¹ = z * α * (t * z⁻¹) := by group
            _ = z * α * (t * z) := by rw [hzi]
            _ = z * α * (z * t) := by rw [hcfg.t_comm_z]
            _ = (z * α * z) * t := by group
        _ = (α * t) * t := by rw [h.z_alpha_z hα]
        _ = α := by rw [mul_assoc, hcfg.t_sq, mul_one]

end OuterS8Hyp

end CFSG.EvenSporadicStandard.Fin76b
