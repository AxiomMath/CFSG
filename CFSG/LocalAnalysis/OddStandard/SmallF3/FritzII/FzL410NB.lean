module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Emb

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open _root_.Certificates

theorem fz410_normSL (hB : FzL410.StageB) (σ l : FzL410.A →+ FzL410.A)
    (hσ2 : ∀ p, σ (σ p) = p) (hσρ : ∀ p, σ (FzL410.rho p) = FzL410.rho (σ p))
    (hσt : ∀ p, FzL410.tt (σ p) = σ (FzL410.tt p))
    (hσinv : ∀ p, FzL410.tt p = p → σ p = -p)
    (hl2 : ∀ p, l (l p) = p)
    (hlρ : ∀ p, l (FzL410.rho p) = FzL410.rho (FzL410.rho (l p)))
    (hlt : ∀ p, FzL410.tt (l p) = l (FzL410.tt p)) (hls : ∀ p, σ (l p) = l (σ p)) :
    ∃ ψ : FzL410.A →+ FzL410.A, Function.Injective ψ ∧
      (∀ p, ψ (FzL410.rho p) = FzL410.rho (ψ p)) ∧ (∀ p, ψ (FzL410.tt p) = FzL410.tt (ψ p)) ∧
      (∀ p, l (ψ p) = ψ (FzL410.ll p)) ∧
      ((∀ p, σ (ψ p) = ψ (FzL410.ss p)) ∨ (∀ p, σ (ψ p) = ψ (FzL410.ss (FzL410.tt p)))) := by
  have hσe : ∀ p, σ p = FzL410.evEq (σ (1, 0, 0, 0)) (σ (0, 0, 1, 0)) p := fz410_eq_evEq σ hσρ
  have hle : ∀ p, l p = FzL410.evAn (l (1, 0, 0, 0)) (l (0, 0, 1, 0)) p := fz410_eq_evAn l hlρ
  have hd2 : (2 : ℕ) • σ (0, 0, 1, 0) = 0 := (fz410_hom_gen_two σ).1
  have hl3 : (2 : ℕ) • l (0, 0, 1, 0) = 0 := (fz410_hom_gen_two l).1
  generalize σ (1, 0, 0, 0) = c at hσe
  generalize σ (0, 0, 1, 0) = d at hσe hd2
  generalize l (1, 0, 0, 0) = l1 at hle
  generalize l (0, 0, 1, 0) = l3 at hle hl3
  have hIsS : FzL410.IsS c d := by
    refine ⟨hd2, fun p => ?_, fun p => ?_, fun p hp => ?_⟩
    · rw [← hσe, ← hσe]; exact hσ2 p
    · rw [← hσe, ← hσe]; exact hσt p
    · rw [← hσe]; exact hσinv p hp
  have hIsL : FzL410.IsL c d l1 l3 := by
    refine ⟨hl3, fun p => ?_, fun p => ?_, fun p => ?_⟩
    · rw [← hle, ← hle]; exact hl2 p
    · rw [← hle, ← hle]; exact hlt p
    · simp only [← hσe, ← hle]; exact hls p
  obtain ⟨⟨c0, d0⟩, -, hd0, hconjL, hsame, hcommT, hcommR, hinj⟩ := hB c d hIsS l1 l3 hIsL
  have hd0' : (2 : ℕ) • d0 = 0 := hd0
  have hconjL' : ∀ p, FzL410.evEq c0 d0 (FzL410.evAn l1 l3 p)
      = FzL410.ll (FzL410.evEq c0 d0 p) := hconjL
  have hsame' : (∀ p, FzL410.evEq c0 d0 (FzL410.evEq c d p) = FzL410.ss (FzL410.evEq c0 d0 p)) ∨
      (∀ p, FzL410.evEq c0 d0 (FzL410.evEq c d p)
        = FzL410.ss (FzL410.tt (FzL410.evEq c0 d0 p))) := hsame
  have hcommT' : ∀ p, FzL410.evEq c0 d0 (FzL410.tt p)
      = FzL410.tt (FzL410.evEq c0 d0 p) := hcommT
  have hcommR' : ∀ p, FzL410.evEq c0 d0 (FzL410.rho p)
      = FzL410.rho (FzL410.evEq c0 d0 p) := hcommR
  have hinj' : ∀ p, FzL410.evEq c0 d0 p = 0 → p = 0 := hinj
  let ψ0 : FzL410.A →+ FzL410.A := fz410EvEqHom c0 d0 hd0'
  have hψ0 : ∀ p, ψ0 p = FzL410.evEq c0 d0 p := fun p => rfl
  have hinj0 : Function.Injective ψ0 :=
    (injective_iff_map_eq_zero ψ0).mpr (fun p hp => hinj' p (by rw [← hψ0]; exact hp))
  obtain ⟨ψ', h1, h2'⟩ := fz410_hom_inv ψ0 hinj0
  refine ⟨ψ', ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have := congrArg ψ0 hab
    rwa [h1, h1] at this
  · intro p
    apply hinj0
    have e : ψ0 (FzL410.rho (ψ' p)) = FzL410.rho p := by
      rw [hψ0, hcommR', ← hψ0, h1]
    rw [e, h1]
  · intro p
    apply hinj0
    have e : ψ0 (FzL410.tt (ψ' p)) = FzL410.tt p := by
      rw [hψ0, hcommT', ← hψ0, h1]
    rw [e, h1]
  · intro p
    have e : ψ0 (l (ψ' p)) = FzL410.ll p := by
      rw [hψ0, hle, hconjL', ← hψ0, h1]
    calc l (ψ' p) = ψ' (ψ0 (l (ψ' p))) := (h2' _).symm
      _ = ψ' (FzL410.ll p) := by rw [e]
  · rcases hsame' with h | h
    · left
      intro p
      have e : ψ0 (σ (ψ' p)) = FzL410.ss p := by
        rw [hψ0, hσe, h, ← hψ0, h1]
      calc σ (ψ' p) = ψ' (ψ0 (σ (ψ' p))) := (h2' _).symm
        _ = ψ' (FzL410.ss p) := by rw [e]
    · right
      intro p
      have e : ψ0 (σ (ψ' p)) = FzL410.ss (FzL410.tt p) := by
        rw [hψ0, hσe, h, ← hψ0, h1]
      calc σ (ψ' p) = ψ' (ψ0 (σ (ψ' p))) := (h2' _).symm
        _ = ψ' (FzL410.ss (FzL410.tt p)) := by rw [e]

variable {G : Type} [Group G]

private theorem fz410_nb_act_sq {P : Subgroup G} {emb : FzL410.A → G} (C : Fz410Coord P emb)
    {g : G} {α : FzL410.A → FzL410.A} (hα : ∀ a, g * emb a * g⁻¹ = emb (α a)) (hg : g ^ 2 = 1)
    (p : FzL410.A) : α (α p) = p := by
  apply C.inj
  have e : g * (g * emb p * g⁻¹) * g⁻¹ = (g * g) * emb p * (g * g)⁻¹ := by group
  rw [← hα, ← hα, e, ← pow_two, hg]
  simp

private theorem fz410_nb_act_comm {P : Subgroup G} {emb : FzL410.A → G} (C : Fz410Coord P emb)
    {g h : G} {α β : FzL410.A → FzL410.A} (hα : ∀ a, g * emb a * g⁻¹ = emb (α a))
    (hβ : ∀ a, h * emb a * h⁻¹ = emb (β a)) (hgh : g * h = h * g) (p : FzL410.A) :
    α (β p) = β (α p) := by
  apply C.inj
  calc emb (α (β p)) = g * emb (β p) * g⁻¹ := (hα _).symm
    _ = g * (h * emb p * h⁻¹) * g⁻¹ := by rw [hβ]
    _ = (g * h) * emb p * (g * h)⁻¹ := by group
    _ = (h * g) * emb p * (h * g)⁻¹ := by rw [hgh]
    _ = h * (g * emb p * g⁻¹) * h⁻¹ := by group
    _ = h * emb (α p) * h⁻¹ := by rw [hα]
    _ = emb (β (α p)) := hβ _

theorem fzl410_NB (hB : FzL410.StageB) {P : Subgroup G} {rho t s lam : G} {emb : FzL410.A → G}
    (E : Fz410EmbT P rho t emb) (hs2 : s ^ 2 = 1) (hsn : ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (hsr : s * rho = rho * s) (hst : s * t = t * s)
    (hsinv : ∀ a, FzL410.tt a = a → s * emb a * s⁻¹ = (emb a)⁻¹)
    (hl2 : lam ^ 2 = 1) (hln : ∀ p ∈ P, lam * p * lam⁻¹ ∈ P)
    (hlr : lam * rho * lam⁻¹ = rho⁻¹) (hlt : lam * t = t * lam) (hls : lam * s = s * lam) :
    ∃ (s' : G) (emb' : FzL410.A → G), (s' = s ∨ s' = t * s) ∧ Fz410Emb P t s' lam rho emb' := by
  have C : Fz410Coord P emb := E.toFz410Coord
  obtain ⟨σ, hσ⟩ := Fz410Coord.exists_act C hsn
  obtain ⟨l, hl⟩ := Fz410Coord.exists_act C hln
  have hσ2 : ∀ p, σ (σ p) = p := fz410_nb_act_sq C hσ hs2
  have hl2' : ∀ p, l (l p) = p := fz410_nb_act_sq C hl hl2
  have hσρ : ∀ p, σ (FzL410.rho p) = FzL410.rho (σ p) :=
    fz410_nb_act_comm C hσ E.cj_rho hsr
  have hσt : ∀ p, FzL410.tt (σ p) = σ (FzL410.tt p) :=
    fz410_nb_act_comm C E.cj_t hσ hst.symm
  have hlt' : ∀ p, FzL410.tt (l p) = l (FzL410.tt p) :=
    fz410_nb_act_comm C E.cj_t hl hlt.symm
  have hls' : ∀ p, σ (l p) = l (σ p) := fz410_nb_act_comm C hσ hl hls.symm
  have hσinv : ∀ p, FzL410.tt p = p → σ p = -p := by
    intro p hp
    apply C.inj
    rw [← hσ, hsinv p hp, C.emb_neg]
  have hq : ∀ q, rho⁻¹ * emb q * rho = emb (FzL410.rho (FzL410.rho q)) := by
    intro q
    have h := E.cj_rho (FzL410.rho (FzL410.rho q))
    rw [fz410_rho_cube] at h
    calc rho⁻¹ * emb q * rho
        = rho⁻¹ * (rho * emb (FzL410.rho (FzL410.rho q)) * rho⁻¹) * rho := by rw [h]
      _ = emb (FzL410.rho (FzL410.rho q)) := by group
  have hlρ : ∀ p, l (FzL410.rho p) = FzL410.rho (FzL410.rho (l p)) := by
    intro p
    apply C.inj
    calc emb (l (FzL410.rho p)) = lam * emb (FzL410.rho p) * lam⁻¹ := (hl _).symm
      _ = lam * (rho * emb p * rho⁻¹) * lam⁻¹ := by rw [E.cj_rho]
      _ = (lam * rho * lam⁻¹) * (lam * emb p * lam⁻¹) * (lam * rho * lam⁻¹)⁻¹ := by group
      _ = rho⁻¹ * emb (l p) * rho := by rw [hlr, hl, inv_inv]
      _ = emb (FzL410.rho (FzL410.rho (l p))) := hq _
  obtain ⟨ψ, hψinj, hψρ, hψt, hψl, hψσ⟩ :=
    fz410_normSL hB σ l hσ2 hσρ hσt hσinv hl2' hlρ hlt' hls'
  have hEmbT : Fz410EmbT P rho t (fun a => emb (ψ a)) :=
    ⟨⟨Fz410Coord.comp C hψinj, fun a => by rw [E.cj_rho, hψρ]⟩, fun a => by rw [E.cj_t, hψt]⟩
  rcases hψσ with h | h
  · refine ⟨s, fun a => emb (ψ a), Or.inl rfl, hEmbT, fun a => ?_, fun a => ?_⟩
    · rw [hσ, h]
    · rw [hl, hψl]
  · refine ⟨t * s, fun a => emb (ψ a), Or.inr rfl, hEmbT, fun a => ?_, fun a => ?_⟩
    · calc t * s * emb (ψ a) * (t * s)⁻¹ = t * (s * emb (ψ a) * s⁻¹) * t⁻¹ := by group
        _ = t * emb (σ (ψ a)) * t⁻¹ := by rw [hσ]
        _ = emb (FzL410.tt (σ (ψ a))) := E.cj_t _
        _ = emb (FzL410.tt (ψ (FzL410.ss (FzL410.tt a)))) := by rw [h]
        _ = emb (ψ (FzL410.tt (FzL410.ss (FzL410.tt a)))) := by rw [hψt]
        _ = emb (ψ (FzL410.ss a)) := by rw [fz410_tt_ss, fz410_tt_tt]
    · rw [hl, hψl]

end CFSG.OddStandard.SmallF3.FritzII
