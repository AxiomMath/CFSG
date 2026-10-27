module

public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Split

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight
  CFSG.SL2MinimalFaithful

section Omega

theorem natModule_not_fixed (n : ℕ) [NeZero n] :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (m : NMod n), rhoW n A m ≠ m := by
  let w : Wd (Fz n) (Fq (2 * n)) := (0, 0, 1)
  refine ⟨unipotent 1, Multiplicative.ofAdd w, fun h => ?_⟩
  have h1 : minusHom n (unipotent 1) w = w := h
  have h2 := unip_add_self n 1 w
  rw [h1, wd_add_self n w] at h2
  have h3 := congrArg (fun z : Wd (Fz n) (Fq (2 * n)) => (z.2.1 : Fq (2 * n))) h2
  simp [w] at h3

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)}

theorem simpleQuot_of_omegaMinus {n : ℕ} (hn : 2 ≤ n)
    (hΩ : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) : SimpleQuot Y := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hinv, θ, φ, hφ⟩ := exists_equiv_of_natSection hΩ
  obtain ⟨A₀, m₀, hm₀⟩ := natModule_not_fixed n
  let F : Subgroup (NMod n) :=
    { carrier := {m | ∀ A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)), rhoW n A m = m}
      one_mem' := fun A => map_one _
      mul_mem' := fun {a b} ha hb A => by rw [map_mul, ha A, hb A]
      inv_mem' := fun {a} ha A => by rw [map_inv, ha A] }
  have hF : F = ⊥ := by
    rcases natModule_irreducible n F (fun A m hm => by rw [hm A]; exact hm) with h | h
    · exact h
    · exfalso
      have : m₀ ∈ F := by rw [h]; exact Subgroup.mem_top _
      exact hm₀ (this A₀)
  have hfix : commV Y ⊓ fixV Y = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu, hfu⟩
    rw [Subgroup.mem_bot]
    have hmem : φ ⟨u, hu⟩ ∈ F := by
      intro A
      obtain ⟨g, rfl⟩ := θ.surjective A
      have hgu : (g : MulAut V) u = u := hfu g g.2
      have hp : (g : MulAut V) u ∈ commV Y := by rw [hgu]; exact hu
      have := hφ g ⟨u, hu⟩ hp
      have e : (⟨(g : MulAut V) u, hp⟩ : ↥(commV Y)) = ⟨u, hu⟩ := Subtype.ext hgu
      rw [e] at this
      exact this.symm
    rw [hF, Subgroup.mem_bot] at hmem
    have := (MulEquiv.map_eq_one_iff φ).mp hmem
    exact congrArg Subtype.val this
  have hne : commV Y ≠ ⊥ := by
    intro h
    have hm1 : m₀ ≠ 1 := fun h1 => hm₀ (by rw [h1]; exact map_one _)
    obtain ⟨x, hx, hx1⟩ : ∃ x : V, x ∈ commV Y ∧ x ≠ 1 :=
      ⟨(φ.symm m₀ : V), (φ.symm m₀).2, fun h1 => hm1 (by
        have h2 : φ.symm m₀ = 1 := Subtype.ext h1
        simpa using congrArg φ h2)⟩
    rw [h] at hx
    exact hx1 (Subgroup.mem_bot.mp hx)
  refine ⟨by rw [hfix]; exact hne, fun N hN _ hNU => ?_⟩
  rw [hfix]
  let M : Subgroup (NMod n) := (N.subgroupOf (commV Y)).map φ.toMonoidHom
  have hMinv : ∀ A, ∀ m ∈ M, rhoW n A m ∈ M := by
    intro A m hm
    obtain ⟨u, hu, rfl⟩ := hm
    obtain ⟨g, rfl⟩ := θ.surjective A
    have hp : (g : MulAut V) (u : V) ∈ commV Y := hinv g g.2 u u.2
    have := hφ g u hp
    refine ⟨⟨(g : MulAut V) (u : V), hp⟩, ?_, ?_⟩
    · exact hN g g.2 u hu
    · exact this
  rcases natModule_irreducible n M hMinv with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxU : x ∈ commV Y := hNU hx
    have : (⟨x, hxU⟩ : ↥(commV Y)) ∈ N.subgroupOf (commV Y) := hx
    have h1 : φ ⟨x, hxU⟩ ∈ M := ⟨_, this, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have := (MulEquiv.map_eq_one_iff φ).mp h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    refine le_antisymm hNU (fun x hx => ?_)
    have h1 : φ ⟨x, hx⟩ ∈ M := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨u, hu, hue⟩ := h1
    have : u = ⟨x, hx⟩ := φ.injective hue
    subst this
    exact hu

end Omega

section Cfg

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem simpleQuot_of_cfg (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) : SimpleQuot Y := by
  rcases cfg.hcls2 with h | ⟨n, hn, hΩ⟩
  · exact simpleQuot_of_inClassX hV cfg.adm.hperf h
  · exact simpleQuot_of_omegaMinus hn hΩ

end Cfg

end CFSG.CGT.PushingUpLit.CGT6X.End3
