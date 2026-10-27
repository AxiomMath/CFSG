module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Nrm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56C2b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y56_conj_t (s : Setting3 G L) (y : G) : y * s.t * y⁻¹ = f3phi s y * s.t := by
  unfold f3phi
  group

theorem y56_phi_mem {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ e4Y s, f3phi s y ∈ s.fr.E := by
  intro y hy
  obtain ⟨v, hv, hvy⟩ := y56_tX_sub hH y hy.1
  unfold f3phi
  rw [hvy, mul_assoc, mul_inv_cancel, mul_one]
  exact hv

theorem y56_phi_mul {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ e4Y s, ∀ y' ∈ e4Y s, f3phi s (y * y') = f3phi s y * f3phi s y' := by
  intro y hy y' hy'
  have hφy := y56_phi_mem hH y hy
  have hφy' := y56_phi_mem hH y' hy'
  have hcomm : y * f3phi s y' * y⁻¹ = f3phi s y' := by
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 (f3phi s y') hφy'
    calc y * f3phi s y' * y⁻¹ = (f3phi s y' * y) * y⁻¹ := by rw [← hc]
      _ = f3phi s y' := by group
  have hab : f3phi s y' * f3phi s y = f3phi s y * f3phi s y' :=
    (y56_E_comm hH (f3phi s y) hφy (f3phi s y') hφy').symm
  calc f3phi s (y * y')
      = y * (y' * s.t * y'⁻¹) * y⁻¹ * s.t⁻¹ := by unfold f3phi; group
    _ = y * (f3phi s y' * s.t) * y⁻¹ * s.t⁻¹ := by rw [y56_conj_t s y']
    _ = (y * f3phi s y' * y⁻¹) * (y * s.t * y⁻¹) * s.t⁻¹ := by group
    _ = (y * f3phi s y' * y⁻¹) * (f3phi s y * s.t) * s.t⁻¹ := by rw [y56_conj_t s y]
    _ = f3phi s y' * f3phi s y := by rw [hcomm]; group
    _ = f3phi s y * f3phi s y' := hab

theorem y56_phi_eq_one {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ e4Y s, (f3phi s y = 1 ↔ y ∈ e4X0 s) := by
  intro y hy
  have h1 : f3phi s y = 1 ↔ y * s.t * y⁻¹ = s.t := by
    constructor
    · intro h
      have := congrArg (· * s.t) h
      simpa [f3phi, mul_assoc] using this
    · intro h; simp [f3phi, h]
  have h2 : y * s.t * y⁻¹ = s.t ↔ y * s.t = s.t * y := by
    constructor
    · intro h
      have := congrArg (· * y) h
      simpa [mul_assoc] using this
    · intro h; rw [h]; group
  have hHiff : y * s.t = s.t * y ↔ y ∈ s.H := by
    show y * s.t = s.t * y ↔ y ∈ centralizer ({s.t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.symm
  rw [h1, h2, hHiff]
  exact ⟨fun hh => ⟨hh, hy.2⟩, fun hx => hx.1⟩

theorem y56_phi_conj {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ e4N s, ∀ y : G, f3phi s (n * y * n⁻¹) = n * f3phi s y * n⁻¹ := by
  intro n hn y
  have hnt : n * s.t = s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hn.1
  have hn' : n * s.t * n⁻¹ = s.t := by rw [hnt]; group
  have hn'' : n⁻¹ * s.t * n = s.t := by
    have h := congrArg (fun z => n⁻¹ * z * n) hn'
    simpa [mul_assoc] using h.symm
  have hninv : n⁻¹ * s.t⁻¹ = s.t⁻¹ * n⁻¹ := by
    have h := congrArg Inv.inv hnt
    simpa [mul_inv_rev] using h.symm
  unfold f3phi
  calc n * y * n⁻¹ * s.t * (n * y * n⁻¹)⁻¹ * s.t⁻¹
      = n * y * (n⁻¹ * s.t * n) * y⁻¹ * n⁻¹ * s.t⁻¹ := by group
    _ = n * y * s.t * y⁻¹ * n⁻¹ * s.t⁻¹ := by rw [hn'']
    _ = n * y * s.t * y⁻¹ * s.t⁻¹ * n⁻¹ := by
        simp only [mul_assoc]
        rw [hninv]
    _ = n * (y * s.t * y⁻¹ * s.t⁻¹) * n⁻¹ := by group

theorem y56_d_mem_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.d ∈ e4Y c.s := by
  have hdE : ∀ f ∈ c.s.fr.E, c.d * f * c.d⁻¹ = f :=
    fun f hf => y5_d_cent_A c f (s3_E_le_A c.s hf)
  have hQ : (c.s.fr.E ⊔ zpowers c.s.t : Subgroup G) =
      Subgroup.closure ((c.s.fr.E : Set G) ∪ {c.s.t}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  have hmemX : c.d ∈ e4X c.s := by
    change c.d ∈ Subgroup.normalizer ((c.s.fr.E ⊔ zpowers c.s.t : Subgroup G) : Set G)
    rw [hQ, Subgroup.mem_set_normalizer_iff]
    have hfwd : ∀ p ∈ (Subgroup.closure ((c.s.fr.E : Set G) ∪ {c.s.t}) : Set G),
        c.d * p * c.d⁻¹ ∈ Subgroup.closure ((c.s.fr.E : Set G) ∪ {c.s.t}) := by
      intro p hp
      induction hp using Subgroup.closure_induction with
      | mem x hx =>
          rcases hx with hxE | hxt
          · rw [hdE x hxE]
            exact Subgroup.subset_closure (Or.inl hxE)
          · rw [Set.mem_singleton_iff] at hxt
            rw [hxt, y5_dtd (c := c) hH]
            exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl (y56_z_mem_E hH)))
              (Subgroup.subset_closure (Or.inr rfl))
      | one => simpa using Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
          rw [show c.d * (x * y) * c.d⁻¹ =
            (c.d * x * c.d⁻¹) * (c.d * y * c.d⁻¹) by group]
          exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ih =>
          rw [show c.d * x⁻¹ * c.d⁻¹ = (c.d * x * c.d⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ ih
    intro p
    constructor
    · exact hfwd p
    · intro hp
      have h := hfwd (c.d * p * c.d⁻¹) hp
      have hd : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
      have hconj : c.d * (c.d * p * c.d⁻¹) * c.d⁻¹ = p := by
        calc c.d * (c.d * p * c.d⁻¹) * c.d⁻¹
            = (c.d * c.d) * p * (c.d * c.d)⁻¹ := by group
          _ = p := by rw [hd]; group
      rwa [hconj] at h
  have hcent : c.d ∈ Subgroup.centralizer (c.s.fr.E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h := hdE f hf
    calc f * c.d = (c.d * f * c.d⁻¹) * c.d := by rw [h]
      _ = c.d * f := by group
  exact Subgroup.mem_inf.mpr ⟨hmemX, hcent⟩

theorem y56_phi_d (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : f3phi c.s c.d = c.s.fr.z :=
  y54_phi_d hH

theorem y56_y0_mem_Y {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {y₀ : G}
    (hy₀ : IsY0 s y₀) : y₀ ∈ e4Y s := by
  have hcent : y₀ ∈ Subgroup.centralizer (s.fr.E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h := hy₀.2.1 f hf
    calc f * y₀ = (y₀ * f * y₀⁻¹) * y₀ := by rw [h]
      _ = y₀ * f := by group
  have hv₀E : y56v0 s ∈ s.fr.E := y56_V_le_E hH (y56_v0 hH).1
  have hv₀2 : y56v0 s * y56v0 s = 1 := by
    have h := y56_E_sq hH (y56v0 s) hv₀E
    simpa [pow_two] using h
  have hQ : (s.fr.E ⊔ zpowers s.t : Subgroup G) =
      Subgroup.closure ((s.fr.E : Set G) ∪ {s.t}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  have hcts : ∀ p ∈ (Subgroup.closure ((s.fr.E : Set G) ∪ {s.t}) : Set G),
      y₀ * p * y₀⁻¹ ∈ Subgroup.closure ((s.fr.E : Set G) ∪ {s.t}) := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hxE | hxt
        · rw [hy₀.2.1 x hxE]
          exact Subgroup.subset_closure (Or.inl hxE)
        · rw [Set.mem_singleton_iff] at hxt
          rw [hxt, hy₀.2.2]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hv₀E))
            (Subgroup.subset_closure (Or.inr rfl))
    | one => simpa using Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
        rw [show y₀ * (x * y) * y₀⁻¹ = (y₀ * x * y₀⁻¹) * (y₀ * y * y₀⁻¹) by group]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [show y₀ * x⁻¹ * y₀⁻¹ = (y₀ * x * y₀⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ ih
  have hcts' : ∀ p ∈ (Subgroup.closure ((s.fr.E : Set G) ∪ {s.t}) : Set G),
      y₀⁻¹ * p * y₀ ∈ Subgroup.closure ((s.fr.E : Set G) ∪ {s.t}) := by
    have hconjE : ∀ x ∈ s.fr.E, y₀⁻¹ * x * y₀ = x := by
      intro x hx
      have h := hy₀.2.1 x hx
      calc y₀⁻¹ * x * y₀ = y₀⁻¹ * (y₀ * x * y₀⁻¹) * y₀ := by rw [h]
        _ = x := by group
    have ht_inv : y₀⁻¹ * s.t * y₀ = y56v0 s * s.t := by
      have ht : s.t = y56v0 s * (y₀⁻¹ * s.t * y₀) := by
        calc s.t = y₀⁻¹ * (y₀ * s.t * y₀⁻¹) * y₀ := by group
          _ = y₀⁻¹ * (y56v0 s * s.t) * y₀ := by rw [hy₀.2.2]
          _ = y56v0 s * (y₀⁻¹ * s.t * y₀) := by
              rw [show y₀⁻¹ * (y56v0 s * s.t) * y₀ =
                (y₀⁻¹ * y56v0 s * y₀) * (y₀⁻¹ * s.t * y₀) by group,
                hconjE (y56v0 s) hv₀E]
      have hx : y₀⁻¹ * s.t * y₀ = (y56v0 s)⁻¹ * s.t := by
        calc y₀⁻¹ * s.t * y₀
            = (y56v0 s)⁻¹ * (y56v0 s * (y₀⁻¹ * s.t * y₀)) := by group
          _ = (y56v0 s)⁻¹ * s.t := by rw [← ht]
      rw [hx, inv_eq_of_mul_eq_one_right hv₀2]
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hxE | hxt
        · rw [hconjE x hxE]
          exact Subgroup.subset_closure (Or.inl hxE)
        · rw [Set.mem_singleton_iff] at hxt
          rw [hxt, ht_inv]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hv₀E))
            (Subgroup.subset_closure (Or.inr rfl))
    | one => simpa using Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
        rw [show y₀⁻¹ * (x * y) * y₀ = (y₀⁻¹ * x * y₀) * (y₀⁻¹ * y * y₀) by group]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [show y₀⁻¹ * x⁻¹ * y₀ = (y₀⁻¹ * x * y₀)⁻¹ by group]
        exact Subgroup.inv_mem _ ih
  have hnorm : y₀ ∈ e4X s := by
    change y₀ ∈ Subgroup.normalizer ((s.fr.E ⊔ zpowers s.t : Subgroup G) : Set G)
    rw [hQ, Subgroup.mem_set_normalizer_iff]
    intro p
    constructor
    · exact hcts p
    · intro hp
      have h := hcts' (y₀ * p * y₀⁻¹) hp
      have heq : y₀⁻¹ * (y₀ * p * y₀⁻¹) * y₀ = p := by group
      rwa [heq] at h
  exact Subgroup.mem_inf.mpr ⟨hnorm, hcent⟩

theorem y56_phi_y0 {s : Setting3 G L} {y₀ : G} (hy₀ : IsY0 s y₀) : f3phi s y₀ = y56v0 s := by
  unfold f3phi
  rw [hy₀.2.2]
  group

theorem y56_phi_surj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ f ∈ c.s.fr.E, ∃ y ∈ e4Y c.s, f3phi c.s y = f := by
  intro f hf
  obtain ⟨y₀, hy₀⟩ := y56_exists_y0 c hH
  by_cases hf1 : f = 1
  · rw [hf1]
    exact ⟨1, Subgroup.one_mem _, by unfold f3phi; group⟩
  · by_cases hfz : f = c.s.fr.z
    · rw [hfz]
      exact ⟨c.d, y56_d_mem_Y c hH, y56_phi_d c hH⟩
    · obtain ⟨hv₀V, _, hv₀1, _, hv₀z, _⟩ := y56_v0 hH
      have hv₀E : y56v0 c.s ∈ c.s.fr.E := y56_V_le_E hH hv₀V
      obtain ⟨n, hn, hnz⟩ := y56_NE_trans hH (y56v0 c.s) hv₀E hv₀1 hv₀z f hf hf1 hfz
      have hnN : n ∈ e4N c.s := y56_NL_le_N hH hn
      refine ⟨n * y₀ * n⁻¹, y56_N_norm_Y hH n hnN y₀ (y56_y0_mem_Y hH hy₀), ?_⟩
      rw [y56_phi_conj hH n hnN, y56_phi_y0 hy₀]
      exact hnz

end CFSG.OddStandard.HigherRank.YamadaG23
