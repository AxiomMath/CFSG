module

public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129Y

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Fixed

variable {Y : Type} [Group Y]

@[instance_reducible] def scpConjAction (Ab M : Subgroup Y)
    (h : ∀ a ∈ Ab, ∀ m ∈ M, a * m * a⁻¹ ∈ M) : MulAction Ab M where
  smul a m := ⟨a * m * a⁻¹, h a a.2 m m.2⟩
  one_smul m := Subtype.ext (by
    show ((1 : Ab) : Y) * (m : Y) * ((1 : Ab) : Y)⁻¹ = m
    simp)
  mul_smul a b m := Subtype.ext (by
    show ((a * b : Ab) : Y) * (m : Y) * ((a * b : Ab) : Y)⁻¹ =
      (a : Y) * ((b : Y) * (m : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
    simp [mul_assoc])

theorem mem_of_isSCp_of_commute_of_pow_eq_one {p : ℕ} {Ab : Subgroup Y} (hAb : IsSCp p ⊤ Ab)
    {x : Y} (hxc : ∀ a ∈ Ab, a * x = x * a) (hxp : x ^ p = 1) : x ∈ Ab := by
  have hE : IsElemAbelian p (Subgroup.closure ((Ab : Set Y) ∪ {x})) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a (ha | ha) b (hb | hb)
      · exact hAb.2.1.comm ha hb
      · rw [Set.mem_singleton_iff.1 hb]
        exact hxc a ha
      · rw [Set.mem_singleton_iff.1 ha]
        exact (hxc b hb).symm
      · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
    · rintro a (ha | ha)
      · exact hAb.2.1.2 a ha
      · rw [Set.mem_singleton_iff.1 ha]
        exact hxp
  have hle : Ab ≤ Subgroup.closure ((Ab : Set Y) ∪ {x}) :=
    fun a ha => Subgroup.subset_closure (Or.inl ha)
  have heq := hAb.2.2 _ le_top hE hle
  rw [← heq]
  exact Subgroup.subset_closure (Or.inr rfl)

variable [Finite Y]

theorem not_dvd_card_of_isSCp_of_normalized {p : ℕ} [Fact p.Prime] {Ab K M : Subgroup Y}
    (hAb : IsSCp p ⊤ Ab) (hfaith : ∀ x ∈ Ab, (∀ y ∈ K, x * y = y * x) → x = 1)
    (hMN : ∀ a ∈ Ab, ∀ m ∈ M, a * m * a⁻¹ ∈ M) (hMK : ∀ m ∈ M, ∀ y ∈ K, m * y = y * m) :
    ¬ p ∣ Nat.card M := by
  intro hdvd
  letI : MulAction Ab M := scpConjAction Ab M hMN
  have hpAb : IsPGroup p Ab := fun a => ⟨1, Subtype.ext (by simpa using hAb.2.1.2 a a.2)⟩
  have hpf : p ∣ Nat.card (MulAction.fixedPoints Ab M) :=
    Nat.modEq_zero_iff_dvd.1 ((hpAb.card_modEq_card_fixedPoints M).symm.trans
      (Nat.modEq_zero_iff_dvd.2 hdvd))
  have hfix : ∀ m : M, m ∈ MulAction.fixedPoints Ab M ↔ ∀ a ∈ Ab, a * (m : Y) = m * a := by
    intro m
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h a ha
      have h1 : a * (m : Y) * a⁻¹ = m := congrArg Subtype.val (h ⟨a, ha⟩)
      calc a * (m : Y) = a * m * a⁻¹ * a := by group
        _ = m * a := by rw [h1]
    · intro h a
      refine Subtype.ext ?_
      show (a : Y) * m * (a : Y)⁻¹ = m
      rw [h a a.2]
      group
  have hcard : Nat.card (MulAction.fixedPoints Ab M) =
      Nat.card (M ⊓ Subgroup.centralizer (Ab : Set Y) : Subgroup Y) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨(m.1 : Y), Subgroup.mem_inf.2 ⟨m.1.2,
          Subgroup.mem_centralizer_iff.2 fun a ha => (hfix m.1).1 m.2 a ha⟩⟩
        invFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.1 c.2).1⟩, (hfix _).2 fun a ha =>
          Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 a ha⟩
        left_inv := fun m => rfl
        right_inv := fun c => rfl }
  rw [hcard] at hpf
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpf
  have hxp : (x : Y) ^ p = 1 := by
    have h1 : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val h1
  have hx1 : (x : Y) ≠ 1 := by
    intro h
    have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have hxM : (x : Y) ∈ M := (Subgroup.mem_inf.1 x.2).1
  have hxc : ∀ a ∈ Ab, a * (x : Y) = x * a := fun a ha =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2 a ha
  exact hx1 (hfaith _ (mem_of_isSCp_of_commute_of_pow_eq_one hAb hxc hxp)
    fun y hy => hMK _ hxM y hy)

theorem subnormal_coprime_eq_bot {p : ℕ} (hp : p.Prime) (hcore : GLAPPrimeCore p Y = ⊥)
    {L : Subgroup Y} (hL : IsSubnormal L ⊤) (hcop : Nat.Coprime p (Nat.card L)) : L = ⊥ := by
  have h1 := glaPPrimeCoreOf_le_of_isSubnormal hp hL
  have h2 : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
    have h3 : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
      have := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := Y))
      rw [hcore] at this
      exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 this
    show (GLAPPrimeCore p ↥(⊤ : Subgroup Y)).map (⊤ : Subgroup Y).subtype = ⊥
    rw [h3, Subgroup.map_bot]
  have h3 : GLAPPrimeCoreOf p L = L := by
    have h4 : GLAPPrimeCore p ↥L = ⊤ := by
      refine top_unique (le_sSup ⟨inferInstance, ?_⟩)
      simpa using hcop
    show (GLAPPrimeCore p ↥L).map L.subtype = L
    rw [h4, Subgroup.map_top, Subgroup.range_subtype]
  rw [h2, h3] at h1
  exact le_bot_iff.1 h1

theorem conj_mem_iSup_of_permuted {Ab : Subgroup Y} {𝒜 : Set (Subgroup Y)}
    (h𝒜 : ∀ a ∈ Ab, ∀ K ∈ 𝒜, GLBConj a K ∈ 𝒜) :
    ∀ a ∈ Ab, ∀ m ∈ (⨆ K ∈ 𝒜, K : Subgroup Y), a * m * a⁻¹ ∈ (⨆ K ∈ 𝒜, K : Subgroup Y) := by
  have hle : ∀ a ∈ Ab, GLBConj a (⨆ K ∈ 𝒜, K : Subgroup Y) ≤ (⨆ K ∈ 𝒜, K : Subgroup Y) := by
    intro a ha
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (GLBConj a K) (h𝒜 a ha K hK) le_rfl
  intro a ha m hm
  apply hle a⁻¹ (Ab.inv_mem ha)
  rw [mem_gLBConj, show a⁻¹ * (a * m * a⁻¹) * a⁻¹⁻¹ = m by group]
  exact hm

end Fixed

theorem scp_centralizer_eq_bot {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hcore : GLAPPrimeCore p Y = ⊥) {Ab : Subgroup Y} (hAb : IsSCp p ⊤ Ab)
    {K₁ : Subgroup Y} (hK₁ : IsComponentOf K₁ ⊤)
    (hfaith : ∀ x ∈ Ab, (∀ y ∈ (⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y), x * y = y * x) → x = 1) :
    (∀ K' : Subgroup Y, IsComponentOf K' ⊤ → ∃ g ∈ Ab, K' = GLBConj g K₁) ∧
      CFSG.pCore p Y = ⊥ ∧
      Subgroup.centralizer ((⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) : Set Y) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hconj_le : ∀ g ∈ Ab, GLBConj g K₁ ≤ (⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) :=
    fun g hg => le_iSup₂_of_le g hg le_rfl
  have hcomp : ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → ∃ g ∈ Ab, K' = GLBConj g K₁ := by
    intro K' hK'
    by_contra hcon
    have hne : ∀ g ∈ Ab, K' ≠ GLBConj g K₁ := fun g hg h => hcon ⟨g, hg, h⟩
    let 𝒜 : Set (Subgroup Y) := {K | IsComponentOf K ⊤ ∧ ∀ g ∈ Ab, K ≠ GLBConj g K₁}
    have hK'𝒜 : K' ∈ 𝒜 := ⟨hK', hne⟩
    have hK'L : K' ≤ (⨆ K ∈ 𝒜, K : Subgroup Y) := le_iSup₂_of_le K' hK'𝒜 le_rfl
    have hLK : ∀ m ∈ (⨆ K ∈ 𝒜, K : Subgroup Y), ∀ y ∈ (⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y),
        m * y = y * m := by
      have h : (⨆ K ∈ 𝒜, K : Subgroup Y) ≤
          Subgroup.centralizer ((⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) : Set Y) := by
        refine iSup₂_le fun K hK => Subgroup.le_centralizer_iff.2 ?_
        refine iSup₂_le fun g hg => ?_
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
            (isComponentOf_gLBConj hK₁ g) hK.1 fun h => hK.2 g hg h.symm)
      intro m hm y hy
      exact (Subgroup.mem_centralizer_iff.1 (h hm) y hy).symm
    have hLN := conj_mem_iSup_of_permuted (Ab := Ab) (𝒜 := 𝒜) fun a ha K hK =>
      ⟨isComponentOf_gLBConj hK.1 a, fun g hg h => by
        refine hK.2 (g * a⁻¹) (Ab.mul_mem hg (Ab.inv_mem ha)) ?_
        calc K = GLBConj a⁻¹ (GLBConj a K) := (gLBConj_inv_gLBConj a K).symm
          _ = GLBConj a⁻¹ (GLBConj g K₁) := by rw [h]
          _ = GLBConj (g * a⁻¹) K₁ := gLBConj_gLBConj a⁻¹ g K₁⟩
    have hndvd := not_dvd_card_of_isSCp_of_normalized hAb hfaith hLN hLK
    have hsub : IsSubnormal (⨆ K ∈ 𝒜, K : Subgroup Y) ⊤ :=
      isSubnormal_iSup_components 𝒜 fun K hK => hK.1
    have hL := subnormal_coprime_eq_bot hp hcore hsub
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
    have hK'bot : K' = ⊥ := le_bot_iff.1 (hL ▸ hK'L)
    have : Nontrivial K' := CFSG.ComponentClassification.Quasisimple.nontrivial hK'.2.2
    exact ((Subgroup.nontrivial_iff_ne_bot K').1 this) hK'bot
  have hpcore : CFSG.pCore p Y = ⊥ := by
    have hcent : ∀ m ∈ CFSG.pCore p Y, ∀ y ∈ (⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y),
        m * y = y * m := by
      haveI : Group.IsNilpotent ↥(CFSG.pCore p Y) := CFSG.pCore_isPGroup.isNilpotent
      have h : (⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) ≤
          Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
        refine iSup₂_le fun g hg => ?_
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal _
            (CFSG.pCore p Y) (isComponentOf_gLBConj hK₁ g)
            (isSubnormal_of_normal CFSG.pCore_normal))
      intro m hm y hy
      exact Subgroup.mem_centralizer_iff.1 (h hy) m hm
    have hndvd := not_dvd_card_of_isSCp_of_normalized hAb hfaith
      (fun a _ m hm => CFSG.pCore_normal.conj_mem m hm a) hcent
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := Y)).exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hndvd (hk ▸ dvd_pow_self p hk0)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  refine ⟨hcomp, hpcore, ?_⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hxK : ∀ K : Subgroup Y, IsComponentOf K ⊤ → x ∈ Subgroup.centralizer (K : Set Y) := by
    intro K hK
    obtain ⟨g, hg, rfl⟩ := hcomp K hK
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (hconj_le g hg)) hx
  have hF : x ∈ Subgroup.centralizer (CFSG.Open.pCore p Y : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ CFSG.pCore p Y := hh
    rw [hpcore] at hh'
    rw [Subgroup.mem_bot.1 hh', one_mul, mul_one]
  have hxF := mem_pCore_of_centralizes hp hcore hF hxK
  have hxF' : x ∈ CFSG.pCore p Y := hxF
  rw [hpcore] at hxF'
  exact Subgroup.mem_bot.1 hxF'

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129Y

end
