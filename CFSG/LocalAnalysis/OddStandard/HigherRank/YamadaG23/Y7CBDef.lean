module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79y
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B0Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y7cX (s : Setting3 G L) : Subgroup G := normalizer (M3 s : Set G)

theorem y7c_M3_le_X (s : Setting3 G L) : M3 s ≤ y7cX s := Subgroup.le_normalizer

instance y7c_M3_normal (s : Setting3 G L) : ((M3 s).subgroupOf (y7cX s)).Normal :=
  Subgroup.normal_in_normalizer

abbrev y7cGam (s : Setting3 G L) : Type := ↥(y7cX s) ⧸ (M3 s).subgroupOf (y7cX s)

@[expose] def y7cPi (s : Setting3 G L) : ↥(y7cX s) →* y7cGam s := QuotientGroup.mk' _

@[expose] def y7cImg (s : Setting3 G L) (H : Subgroup G) : Subgroup (y7cGam s) :=
  (H.subgroupOf (y7cX s)).map (y7cPi s)

@[expose] def y7cPre (s : Setting3 G L) (Y : Subgroup (y7cGam s)) : Subgroup G :=
  (Y.comap (y7cPi s)).map (y7cX s).subtype

theorem y7cPi_surjective (s : Setting3 G L) : Function.Surjective (y7cPi s) :=
  QuotientGroup.mk'_surjective _

theorem y7cPi_eq_one_iff (s : Setting3 G L) (x : ↥(y7cX s)) :
    y7cPi s x = 1 ↔ (x : G) ∈ M3 s := by
  simp [y7cPi, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem y7cPi_eq_iff (s : Setting3 G L) (x y : ↥(y7cX s)) :
    y7cPi s x = y7cPi s y ↔ (x : G)⁻¹ * (y : G) ∈ M3 s := by
  simp [y7cPi, QuotientGroup.eq, Subgroup.mem_subgroupOf]

theorem mem_y7cImg (s : Setting3 G L) {H : Subgroup G} {γ : y7cGam s} :
    γ ∈ y7cImg s H ↔ ∃ x : ↥(y7cX s), (x : G) ∈ H ∧ y7cPi s x = γ := by
  simp [y7cImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_y7cPre (s : Setting3 G L) {Y : Subgroup (y7cGam s)} {x : G} :
    x ∈ y7cPre s Y ↔ ∃ h : x ∈ y7cX s, y7cPi s ⟨x, h⟩ ∈ Y := by
  simp [y7cPre, Subgroup.mem_map]

noncomputable def y7cRho (s : Setting3 G L) (hab : ∀ a ∈ M3 s, ∀ b ∈ M3 s, a * b = b * a) :
    y7cGam s →* MulAut ↥(M3 s) :=
  QuotientGroup.lift _ (M3 s).normalizerMonoidHom (by
    rw [Subgroup.normalizerMonoidHom_ker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hab h hh x hx)

structure B7Std (c : Ctx7 G L) : Prop extends B6Std c where
  h76 : c.Fact76

theorem y7cRho_apply (s : Setting3 G L) (hab : ∀ a ∈ M3 s, ∀ b ∈ M3 s, a * b = b * a)
    (x : ↥(y7cX s)) (m : ↥(M3 s)) :
    ((y7cRho s hab (y7cPi s x) m : ↥(M3 s)) : G) = (x : G) * (m : G) * (x : G)⁻¹ := by
  rfl

theorem y7c_t_mem_X (c : Ctx7 G L) (hb : B7Std c) : c.s.t ∈ y7cX c.s := by
  have h : conjSub c.s.t (M3 c.s) = M3 c.s := y7c_conjSub_t_M3 c.toCtx5 hb.hH
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [← h]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  · intro hn
    rw [← h] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    have : m = n := by
      simpa [MulAut.conj_apply] using hmn
    rw [← this]
    exact hm

theorem y7c_M3_comm (c : Ctx7 G L) (hb : B7Std c) :
    ∀ a ∈ M3 c.s, ∀ b ∈ M3 c.s, a * b = b * a := by
  intro a ha b hb'
  have h := (y7c_M3_elem c hb.hH hb.fact57).1
  exact congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩)

noncomputable abbrev y7cRhoC (c : Ctx7 G L) (hb : B7Std c) :
    y7cGam c.s →* MulAut ↥(M3 c.s) :=
  y7cRho c.s (y7c_M3_comm c hb)

abbrev y7cTC (c : Ctx7 G L) (hb : B7Std c) : y7cGam c.s :=
  y7cPi c.s ⟨c.s.t, y7c_t_mem_X c hb⟩

abbrev y7cJC (c : Ctx7 G L) : Subgroup (y7cGam c.s) := y7cImg c.s (JF c.s)

abbrev y7cQC (c : Ctx7 G L) : Subgroup (y7cGam c.s) := y7cImg c.s (f4X0 c.s)

abbrev y7cPC (c : Ctx7 G L) : Subgroup (y7cGam c.s) := y7cImg c.s (P7 c.e)

abbrev y7cM6C (c : Ctx7 G L) : Subgroup (y7cGam c.s) := y7cImg c.s (M6 c.e)

abbrev y7cM7C (c : Ctx7 G L) : Subgroup (y7cGam c.s) := y7cImg c.s (M7 c.s)

end CFSG.OddStandard.HigherRank.YamadaG23
