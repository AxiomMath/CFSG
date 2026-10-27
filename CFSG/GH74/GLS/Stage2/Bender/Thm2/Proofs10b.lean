module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs10
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.KInftyNat
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10C2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem kInfty_ne_bot (hk : KInfty_facts) {p : ℕ} (hp : p.Prime) {R : Subgroup G} (hR : IsPGroup p ↥R)
    (hne : R ≠ ⊥) : kInfty R ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hnt : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  have hc : Nontrivial ↥(center ↥R) := hR.center_nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(center ↥R))
  intro hb
  have hxc : (x : ↥R) ∈ center ↥R := x.2
  have hmem : ((x : ↥R) : G) ∈ zOf R := by
    refine ⟨(x : ↥R).2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.mp hxc ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hle := (hk G p hp R hR).2 hmem
  rw [hb, Subgroup.mem_bot] at hle
  apply hx
  apply Subtype.ext
  apply Subtype.ext
  exact hle

theorem exists_coatom_ge_normalizer {R₀ M : Subgroup G} (hs : IsSimpleGroup G) (hM : M ≠ ⊤) (hR₀ : R₀ ≤ M)
    (hne : R₀ ≠ ⊥) : ∃ N : Subgroup G, IsCoatom N ∧ normalizer (R₀ : Set G) ≤ N := by
  have hne' : normalizer (R₀ : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : R₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R₀ with h | h
    · exact hne h
    · exact hM (top_le_iff.mp (h ▸ hR₀))
  exact (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hne'

omit [Finite G] in
theorem normalizer_ne_top {R₀ M : Subgroup G} (hs : IsSimpleGroup G) (hM : M ≠ ⊤) (hR₀ : R₀ ≤ M)
    (hne : R₀ ≠ ⊥) : normalizer (R₀ : Set G) ≠ ⊤ := by
  intro htop
  have hnorm : R₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R₀ with h | h
  · exact hne h
  · exact hM (top_le_iff.mp (h ▸ hR₀))

theorem exists_maxIn_above {𝒮 : Set (Subgroup G)} {R₁ : Subgroup G} (h : R₁ ∈ 𝒮) :
    ∃ V, MaxIn 𝒮 V ∧ R₁ ≤ V := by
  obtain ⟨V, ⟨hV𝒮, hRV⟩, hmin⟩ :=
    (wellFounded_gt (α := Subgroup G)).has_min {V | V ∈ 𝒮 ∧ R₁ ≤ V} ⟨R₁, h, le_rfl⟩
  refine ⟨V, ⟨hV𝒮, fun V' hV' hVV' => ?_⟩, hRV⟩
  by_contra hne
  exact hmin V' ⟨hV', hRV.trans hVV'⟩ (lt_of_le_of_ne hVV' (Ne.symm hne))

end Helpers

section Triple

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem exists_NV (hk : KInfty_facts) (ctx : Ctx10 G z k S M p Q T U t g) {R : Subgroup G}
    (hR : Rp z k p T U Q M R) :
    ∃ N V : Subgroup G, IsCoatom N ∧ normalizer ((kInfty R : Subgroup G) : Set G) ≤ N ∧
      MaxIn {V' : Subgroup G | R0 k p T U (M ⊓ N) V'} V ∧
      R ⊔ (Op p M ⊓ normalizer ((kInfty R : Subgroup G) : Set G)) ≤ V ∧ Rp z k p T U Q M V := by
  have hp := ctx.ctx9.prime
  have hRp : IsPGroup p ↥R := hR.1.2.1
  have hR₀ne : kInfty R ≠ ⊥ := kInfty_ne_bot hk hp hRp hR.1.1
  have hR₀R : kInfty R ≤ R := (hk G p hp R hRp).1
  have hRM : R ≤ M := hR.1.2.2.1
  have hTR : T ≤ normalizer (R : Set G) := hR.1.2.2.2.1
  have hNR : normalizer (R : Set G) ≤ normalizer ((kInfty R : Subgroup G) : Set G) :=
    normalizer_le_kInfty R
  obtain ⟨N, hN, hNle⟩ :=
    exists_coatom_ge_normalizer ctx.ctx9.simple ctx.ctx9.coatom.1 (hR₀R.trans hRM) hR₀ne
  have hRN : R ≤ N := Subgroup.le_normalizer.trans (hNR.trans hNle)
  have hRnormNP : R ≤ normalizer ((Op p M ⊓ normalizer ((kInfty R : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (le_normalizer_Op' p M (hRM hx))
      (Subgroup.le_normalizer (hNR (Subgroup.le_normalizer hx)))
  have hNPpg : IsPGroup p ↥(Op p M ⊓ normalizer ((kInfty R : Subgroup G) : Set G)) :=
    ctx.ctx9.P_pgroup.to_le inf_le_left
  have hRs0 : R0 k p T U (M ⊓ N) (R ⊔ (Op p M ⊓ normalizer ((kInfty R : Subgroup G) : Set G))) := by
    refine ⟨fun hb => hR.1.1 (le_bot_iff.mp (le_sup_left.trans hb.le)),
      hRp.to_sup_of_normal_right' hNPpg hRnormNP,
      sup_le (le_inf hRM hRN) (le_inf (inf_le_left.trans (Op_le' p M)) (inf_le_right.trans hNle)),
      fun x hx => mem_normalizer_sup (hTR hx) (mem_normalizer_inf
        (le_normalizer_Op' p M (ctx.T_le_M hx)) (Subgroup.le_normalizer (hNR (hTR hx)))), ?_⟩
    refine Cov10.mono ?_ hR.1.2.2.2.2
    exact fun x hx => ⟨⟨hx.1, hNle (hNR hx.2)⟩, mem_normalizer_sup hx.2
      (mem_normalizer_inf (le_normalizer_Op' p M hx.1) (Subgroup.le_normalizer (hNR hx.2)))⟩
  obtain ⟨V, hVmax, hRsV⟩ := exists_maxIn_above (𝒮 := {V' : Subgroup G | R0 k p T U (M ⊓ N) V'}) hRs0
  refine ⟨N, V, hN, hNle, hVmax, hRsV, R0_mono inf_le_left hVmax.1, ?_⟩
  have hNQ : Q ⊓ normalizer (R : Set G) ≤ Q ⊓ normalizer (V : Set G) := by
    intro x hx
    refine ⟨hx.1, Subgroup.le_normalizer ?_⟩
    exact hRsV (Subgroup.mem_sup_right ⟨ctx.Q_le_P hx.1, hNR hx.2⟩)
  intro hb
  apply hR.2
  rw [eq_bot_iff]
  exact (Subgroup.commutator_mono hNQ le_rfl).trans hb.le

end Triple

end CFSG.GH74.GLS.Stage2.Bender.Thm2
