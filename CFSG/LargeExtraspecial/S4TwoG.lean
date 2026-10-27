module

public import CFSG.LargeExtraspecial.S4TwoF
public import CFSG.CGT.Timmesfeld75.Form2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Abstract

variable {X : Type*} [Group X]

theorem exists_mem_center_conj {K : Subgroup X} [K.Normal] (x : X) {c : K} (hc : c ∈ center K) :
    ∃ c' : K, c' ∈ center K ∧ (c' : X) = x * c * x⁻¹ := by
  have hyK : x * (c : X) * x⁻¹ ∈ K := ‹K.Normal›.conj_mem _ c.2 x
  refine ⟨⟨_, hyK⟩, mem_center_iff.mpr fun k => Subtype.ext ?_, rfl⟩
  show (k : X) * (x * (c : X) * x⁻¹) = x * (c : X) * x⁻¹ * (k : X)
  have hk' : x⁻¹ * (k : X) * x ∈ K := by
    have := ‹K.Normal›.conj_mem _ k.2 x⁻¹
    rwa [inv_inv] at this
  have h1 : (⟨x⁻¹ * (k : X) * x, hk'⟩ : K) * c = c * ⟨x⁻¹ * (k : X) * x, hk'⟩ :=
    mem_center_iff.mp hc _
  have h1' : x⁻¹ * (k : X) * x * (c : X) = (c : X) * (x⁻¹ * (k : X) * x) :=
    congrArg Subtype.val h1
  calc (k : X) * (x * (c : X) * x⁻¹) = x * ((x⁻¹ * (k : X) * x) * (c : X)) * x⁻¹ := by group
    _ = x * ((c : X) * (x⁻¹ * (k : X) * x)) * x⁻¹ := by rw [h1']
    _ = x * (c : X) * x⁻¹ * (k : X) := by group

theorem center_eq_bot_of_mulEquiv {Q K : Type*} [Group Q] [Group K] (e : Q ≃* K)
    (h : center K = ⊥) : center Q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hmem : e z ∈ center K := by
    rw [mem_center_iff]
    intro k
    have h2 := congrArg e (mem_center_iff.mp hz (e.symm k))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  rw [h, mem_bot] at hmem
  rw [mem_bot]
  exact e.injective (hmem.trans (map_one _).symm)

theorem exists_mulEquiv_quotient_quotient {K : Type*} [Group K] {P : Subgroup K} [P.Normal]
    (hP : P = ⊥) {Z : Subgroup (K ⧸ P)} [Z.Normal] (hZ : Z = ⊥) (L : Subgroup K) :
    ∃ ψ : K ≃* (K ⧸ P) ⧸ Z,
      L.map ψ.toMonoidHom = (L.map (QuotientGroup.mk' P)).map (QuotientGroup.mk' Z) := by
  have hb : Function.Bijective ((QuotientGroup.mk' Z).comp (QuotientGroup.mk' P)) := by
    refine ⟨?_, (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)⟩
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      hP] at hx
    exact hx
  refine ⟨MulEquiv.ofBijective _ hb, ?_⟩
  rw [Subgroup.map_map]
  exact congrArg (fun φ : K →* (K ⧸ P) ⧸ Z => L.map φ) (MonoidHom.ext fun _ => rfl)

noncomputable def quotientEquivOfEqBot {K : Type*} [Group K] {P : Subgroup K} [P.Normal]
    (hP : P = ⊥) : K ⧸ P ≃* K :=
  (QuotientGroup.quotientMulEquivOfEq hP).trans QuotientGroup.quotientBot

end Abstract

theorem isReducible_of_center_M0_ne_bot (H : Hyp4 S g) (hz : center (M0 S g) ≠ ⊥) :
    S.IsReducible := by
  set Z : Subgroup S.O := ((center (M0 S g)).map (M0 S g).subtype).map S.Mbar.subtype with hZ
  have hcK : ∀ (c : M0 S g), c ∈ center (M0 S g) → ∀ k : S.Mbar, k ∈ M0 S g →
      k * (c : S.Mbar) = (c : S.Mbar) * k := by
    intro c hc k hk
    have := mem_center_iff.mp hc ⟨k, hk⟩
    exact congrArg Subtype.val this
  have hmemZ : ∀ z ∈ Z, ∃ c : M0 S g, c ∈ center (M0 S g) ∧ ((c : S.Mbar) : S.O) = z := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    exact ⟨c, hc, by rw [← hyz, ← hcy]; rfl⟩
  refine isReducible_of_le_centralizer H (Z := Z) ?_ ?_ ?_
  · rw [hZ, Ne, Subgroup.map_eq_bot_iff_of_injective _ S.Mbar.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ (M0 S g).subtype_injective]
    exact hz
  · intro m z hz
    obtain ⟨c, hc, rfl⟩ := hmemZ z hz
    obtain ⟨c', hc', hcc'⟩ := exists_mem_center_conj
      (⟨S.ρ m, MonoidHom.mem_range.mpr ⟨m, rfl⟩⟩ : S.Mbar) hc
    have e := congrArg Subtype.val hcc'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨c', hc', rfl⟩, e⟩
  · intro z hz l hl
    obtain ⟨c, hc, rfl⟩ := hmemZ z hz
    have hlK : (⟨l, S.Lbar_le_Mbar g hl⟩ : S.Mbar) ∈ M0 S g := LM_le_M0 (mem_subgroupOf.mpr hl)
    have := hcK c hc _ hlK
    exact (congrArg Subtype.val this).symm

theorem isReducible_of_center_Form2Q_ne_bot (H : Hyp4 S g)
    (hz : center (Form2Q S.Mbar (LM S g)) ≠ ⊥) : S.IsReducible :=
  isReducible_of_center_M0_ne_bot H fun h0 =>
    hz (center_eq_bot_of_mulEquiv (quotientEquivOfEqBot pCore_M0_eq_bot) h0)

theorem exists_mulEquiv_Form2Q (hz : center (Form2Q S.Mbar (LM S g)) = ⊥) :
    ∃ ψ : M0 S g ≃* (Form2Q S.Mbar (LM S g) ⧸ center (Form2Q S.Mbar (LM S g))),
      (LM0 S g).map ψ.toMonoidHom =
        (Form2L S.Mbar (LM S g)).map (QuotientGroup.mk' (center (Form2Q S.Mbar (LM S g)))) :=
  exists_mulEquiv_quotient_quotient pCore_M0_eq_bot hz (LM0 S g)

theorem card_LM0 : Nat.card (LM0 S g) = Nat.card (S.Lbar g) :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe LM_le_M0).toEquiv).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv)

end CFSG.LargeExtraspecial.S4
