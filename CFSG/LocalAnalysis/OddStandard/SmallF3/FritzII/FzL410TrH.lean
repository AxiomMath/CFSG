module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Dict

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

include M

theorem mu_one : fz410Mu emb t s lam FzL410.oneT = 1 := by
  have h := M.mu_pe 0
  rw [M.emb.emb_zero] at h
  exact h

theorem mu_comm_iff (x y : FzL410.TM) :
    fz410Mu emb t s lam x * fz410Mu emb t s lam y = fz410Mu emb t s lam y * fz410Mu emb t s lam x ↔
      FzL410.mulT x y = FzL410.mulT y x := by
  rw [← M.mu_mul, ← M.mu_mul]
  exact ⟨fun h => M.mu_inj h, fun h => by rw [h]⟩

theorem mu_comm_pe (y : FzL410.TM) (a : FzL410.A) :
    fz410Mu emb t s lam y * emb a = emb a * fz410Mu emb t s lam y ↔
      FzL410.mulT (FzL410.pe a) y = FzL410.mulT y (FzL410.pe a) := by
  rw [← M.mu_pe a, M.mu_comm_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem mu_sq (x : FzL410.TM) :
    fz410Mu emb t s lam x ^ 2 = fz410Mu emb t s lam (FzL410.mulT x x) := by
  rw [M.mu_mul, pow_two]

theorem exists_eE {g : G} (hg : g ∈ E) :
    ∃ a b : ZMod 4, g = emb (a, b, 0, 0) := by
  obtain ⟨c, rfl⟩ := (M.emb.mem g).mp (M.pf.EP hg)
  have hEA : FzL410.EA c := (M.mem_E c).mp hg
  obtain ⟨c1, c2, c3, c4⟩ := c
  have h : (c3, c4) = (0 : ZMod 2 × ZMod 2) := hEA
  have h3 : c3 = 0 := congrArg Prod.fst h
  have h4 : c4 = 0 := congrArg Prod.snd h
  subst h3
  subst h4
  exact ⟨c1, c2, rfl⟩

theorem eE_mem (a b : ZMod 4) : emb (a, b, 0, 0) ∈ E := (M.mem_E _).mpr rfl

theorem card_eq_filter (K : Subgroup G) (hK : K ≤ T) (pr : FzL410.TM → Prop) [DecidablePred pr]
    (hpr : ∀ x, fz410Mu emb t s lam x ∈ K ↔ pr x) :
    Nat.card K = (Finset.univ.filter pr).card := by
  have hbij : Function.Bijective
      (fun x : {x : FzL410.TM // pr x} => (⟨fz410Mu emb t s lam x.1, (hpr x.1).mpr x.2⟩ : K)) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (M.mu_inj (congrArg Subtype.val hxy))
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx⟩ := (M.mem_T g).mp (hK hg)
      refine ⟨⟨x, (hpr x).mp (hx ▸ hg)⟩, Subtype.ext hx⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
