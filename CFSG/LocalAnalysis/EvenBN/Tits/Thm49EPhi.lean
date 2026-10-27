module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ECtx
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4CtSplit
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Fourteen

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

private theorem exists_eps {G : Type} [Group G] {t : G} (htt : t * t = 1) {A₀ : Subgroup G}
    (htA : t ∉ A₀) (hcov : ∀ x ∈ centralizer ({t} : Set G), x ∈ A₀ ∨ t * x ∈ A₀) :
    ∃ ε : ↥(centralizer ({t} : Set G)) →* ℤˣ,
      ε ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ = -1 := by
  classical
  have hmul : ∀ x y : ↥(centralizer ({t} : Set G)), (x : G) ∉ A₀ → (y : G) ∉ A₀ →
      (x : G) * y ∈ A₀ := by
    intro x y hx hy
    have hx' := (hcov x x.2).resolve_left hx
    have hy' := (hcov y y.2).resolve_left hy
    have hxt : (x : G) * t = t * x := mem_centralizer_singleton_iff.1 x.2
    have e : t * (x : G) * (t * y) = x * y := by
      calc t * (x : G) * (t * y) = t * ((x : G) * t) * y := by group
        _ = t * (t * x) * y := by rw [hxt]
        _ = (t * t) * x * y := by group
        _ = x * y := by rw [htt, one_mul]
    rw [← e]
    exact mul_mem hx' hy'
  refine ⟨{ toFun := fun x => if (x : G) ∈ A₀ then 1 else -1
            map_one' := by simp
            map_mul' := fun x y => ?_ }, by simp [htA]⟩
  by_cases hx : (x : G) ∈ A₀ <;> by_cases hy : (y : G) ∈ A₀
  · have hxy : (x : G) * y ∈ A₀ := mul_mem hx hy
    simp [hx, hy, hxy]
  · have hxy : (x : G) * y ∉ A₀ := fun h => hy (by simpa using mul_mem (inv_mem hx) h)
    simp [hx, hy, hxy]
  · have hxy : (x : G) * y ∉ A₀ := fun h => hx (by simpa using mul_mem h (inv_mem hy))
    simp [hx, hy, hxy]
  · have hxy : (x : G) * y ∈ A₀ := hmul x y hx hy
    simp [hx, hy, hxy]

private theorem eps_L
    {G : Type} [Group G] [Finite G] {d : Data G} (hd : d.Hyp)
    (ε : ↥(centralizer ({d.t} : Set G)) →* ℤˣ) {l : G} (hl : l ∈ d.L) :
    ε ⟨l, hd.L_le hl⟩ = 1 := by
  have hs : IsSimpleGroup titsD := titsD_simple
  let ψ : titsD →* ℤˣ := (ε.comp (Subgroup.inclusion hd.L_le)).comp d.θ.symm.toMonoidHom
  have hψ : ψ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exfalso
      have hle := Nat.card_le_card_of_injective ψ ((MonoidHom.ker_eq_bot_iff ψ).1 h)
      rw [card_titsD, Nat.card_eq_fintype_card, Fintype.card_units_int] at hle
      omega
    · exact h
  have h1 : ψ (d.θ ⟨l, hl⟩) = 1 := MonoidHom.mem_ker.1 (hψ ▸ mem_top _)
  have h2 : ψ (d.θ ⟨l, hl⟩) = ε ⟨l, hd.L_le hl⟩ := by
    show ε (Subgroup.inclusion hd.L_le (d.θ.symm (d.θ ⟨l, hl⟩))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  exact h2.symm.trans h1

theorem _root_.CFSG.LocalAnalysis.EvenBN.Tits.Data.Hyp.nonempty_ctx
    {G : Type} [Group G] [Finite G] {d : Data G}
    (hd : d.Hyp) (hfail : d.t * d.v ∉ d.tG) :
    Nonempty (Ctx G) := by
  classical
  have htt : d.t * d.t = 1 := hd.t_mul_self
  obtain ⟨A₀, -, htA, hcov⟩ := hd.exists_compl_zpowers_t
  obtain ⟨ε, hεt⟩ := exists_eps htt htA hcov
  let tC : ↥(centralizer ({d.t} : Set G)) := ⟨d.t, d.t_mem_centralizer⟩
  have hεt' : ε tC = -1 := hεt
  have hεL : ∀ {l : G} (hl : l ∈ d.L), ε ⟨l, hd.L_le hl⟩ = 1 := fun hl => eps_L hd ε hl
  let Φ : ↥(centralizer ({d.t} : Set G)) →* Cm := ε.prod (titsA.subtype.comp d.ρ)
  have hΦ : ∀ x, Φ x = (ε x, (d.ρ x : Equiv.Perm (Fin 1755))) := fun x => rfl
  have hρt : d.ρ tC = 1 := hd.ρ_t
  have hker : ∀ x : ↥(centralizer ({d.t} : Set G)), d.ρ x = 1 → x = 1 ∨ x = tC := by
    intro x hx
    have hmem : (x : G) ∈ d.ρ.ker.map (centralizer ({d.t} : Set G)).subtype :=
      ⟨x, MonoidHom.mem_ker.2 hx, rfl⟩
    rw [Model.ker_ρ_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hmem
    rcases hmem with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hΦt : Φ tC = tauH := by
    rw [hΦ]
    exact Prod.ext hεt' (by rw [hρt]; rfl)
  have hΦL : ∀ a ∈ titsD, Φ ⟨d.lift a, hd.L_le (d.lift_mem a)⟩ = inA a := by
    intro a ha
    rw [hΦ]
    refine Prod.ext (hεL (d.lift_mem a)) ?_
    have h := hd.ρ_eq_θ ⟨d.lift a, d.lift_mem a⟩
    rw [d.θ_lift ha] at h
    exact h
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hΦ] at hx
    have h1 : ε x = 1 := congrArg Prod.fst hx
    have h2 : d.ρ x = 1 := Subtype.ext (congrArg Prod.snd hx)
    rcases hker x h2 with h | rfl
    · exact h
    · exfalso
      rw [hεt'] at h1
      exact absurd h1 (by decide)
  have hsurj : ∀ a ∈ Am, ∃ x, Φ x = a := by
    rintro ⟨e, p⟩ hmem
    have hp : p ∈ titsA := (Subgroup.mem_prod.1 hmem).2
    obtain ⟨x₁, hx₁⟩ : (⟨p, hp⟩ : titsA) ∈ d.ρ.range :=
      (hd.thm412_range hfail).symm ▸ mem_top _
    by_cases hε : ε x₁ = e
    · refine ⟨x₁, ?_⟩
      rw [hΦ, hε, hx₁]
    · refine ⟨tC * x₁, ?_⟩
      have hunit : ∀ u v : ℤˣ, u ≠ v → -1 * u = v := by decide
      rw [hΦ, map_mul, map_mul, hεt', hρt, hunit _ _ hε, one_mul, hx₁]
  have hI2 : ∀ x : ↥(centralizer ({d.t} : Set G)),
      (∃ g : G, g * d.t * g⁻¹ = (x : G)) ↔
        (Φ x = tauH ∨ ∃ l, IsLong l ∧ Φ x = tauH * inA l) := by
    intro x
    constructor
    · rintro ⟨g, hg⟩
      have hgC : g * d.t * g⁻¹ ∈ centralizer ({d.t} : Set G) := by
        rw [hg]
        exact x.2
      rcases hd.conj_t_cases_of_failure hfail hgC with h | ⟨m, hm, h⟩
      · left
        have hx : x = tC := Subtype.ext (hg.symm.trans h)
        rw [hx, hΦt]
      · right
        obtain ⟨δ, hδ, hmδ⟩ : ∃ δ ∈ titsD, d.lift δ = m :=
          ⟨_, (d.θ ⟨m, hm⟩).2, d.lift_θ ⟨m, hm⟩⟩
        have hlD : δ * titsZ * δ⁻¹ ∈ titsD := mul_mem (mul_mem hδ titsZ_mem_titsD) (inv_mem hδ)
        refine ⟨δ * titsZ * δ⁻¹, ⟨δ, hδ, rfl⟩, ?_⟩
        have hx : x = tC * ⟨d.lift (δ * titsZ * δ⁻¹), hd.L_le (d.lift_mem _)⟩ := by
          apply Subtype.ext
          show (x : G) = d.t * d.lift (δ * titsZ * δ⁻¹)
          rw [d.lift_conj hδ titsZ_mem_titsD, d.lift_titsZ, hmδ, ← hg, h]
          have hc := hd.L_comm_t hm
          calc m * (d.t * d.z) * m⁻¹ = (m * d.t) * d.z * m⁻¹ := by group
            _ = (d.t * m) * d.z * m⁻¹ := by rw [hc]
            _ = d.t * (m * d.z * m⁻¹) := by group
        rw [hx, map_mul, hΦt, hΦL _ hlD]
    · rintro (h | ⟨l, ⟨δ, hδ, hδl⟩, h⟩)
      · have hx : x = tC := hinj (h.trans hΦt.symm)
        exact ⟨1, by rw [hx]; simp [tC]⟩
      · have hlD : l ∈ titsD := hδl ▸ mul_mem (mul_mem hδ titsZ_mem_titsD) (inv_mem hδ)
        have hx : x = tC * ⟨d.lift l, hd.L_le (d.lift_mem l)⟩ := by
          apply hinj
          rw [map_mul, hΦt, hΦL l hlD, h]
        obtain ⟨k, -, -, hk⟩ := hd.exists_conj_t_tz hfail
        refine ⟨d.lift δ * k, ?_⟩
        rw [hx]
        show _ = d.t * d.lift l
        rw [← hδl, d.lift_conj hδ titsZ_mem_titsD, d.lift_titsZ]
        have hc := hd.L_comm_t (d.lift_mem δ)
        calc d.lift δ * k * d.t * (d.lift δ * k)⁻¹
            = d.lift δ * (k * d.t * k⁻¹) * (d.lift δ)⁻¹ := by group
          _ = d.lift δ * (d.t * d.z) * (d.lift δ)⁻¹ := by rw [hk]
          _ = (d.lift δ * d.t) * d.z * (d.lift δ)⁻¹ := by group
          _ = (d.t * d.lift δ) * d.z * (d.lift δ)⁻¹ := by rw [hc]
          _ = d.t * (d.lift δ * d.z * (d.lift δ)⁻¹) := by group
  exact ⟨⟨d.t, htt, Φ, hinj, fun x => Subgroup.mem_prod.2 ⟨mem_top _, (d.ρ x).2⟩, hsurj, hΦt,
    hI2⟩⟩

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
