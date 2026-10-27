module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxKey
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxGroupC

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {Y : Type} [Group Y] [Finite Y] {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]

@[expose] def orbitSet (ρ : Γ →* MulAut Y) (K₀ : Subgroup (Qt Y)) : Set (Subgroup (Qt Y)) :=
  Set.range fun γ : Γ => K₀.map (qAct ρ γ).toMonoidHom


open scoped Pointwise

section Orbit

omit [Finite Y] [Finite Γ]

variable (ρ : Γ →* MulAut Y) {K₀ : Subgroup (Qt Y)}

theorem self_mem_orbitSet : K₀ ∈ orbitSet ρ K₀ :=
  ⟨1, by ext x; simp⟩

theorem mem_orbitSet_iff {K : Subgroup (Qt Y)} :
    K ∈ orbitSet ρ K₀ ↔ ∃ γ : Γ, K₀.map (qAct ρ γ).toMonoidHom = K := Iff.rfl

theorem map_mem_orbitSet {K : Subgroup (Qt Y)} (hK : K ∈ orbitSet ρ K₀) (δ : Γ) :
    K.map (qAct ρ δ).toMonoidHom ∈ orbitSet ρ K₀ := by
  obtain ⟨γ, rfl⟩ := hK
  refine ⟨δ * γ, ?_⟩
  rw [Subgroup.map_map]
  ext x
  simp [map_mul]

theorem isComponentOf_of_mem_orbitSet [Finite Y] (hK₀ : IsComponentOf K₀ ⊤)
    {K : Subgroup (Qt Y)} (hK : K ∈ orbitSet ρ K₀) : IsComponentOf K ⊤ := by
  obtain ⟨γ, rfl⟩ := hK
  exact isComponentOf_map_qAct ρ hK₀ γ

theorem finite_orbitSet [Finite Γ] : (orbitSet ρ K₀).Finite :=
  Set.finite_range _

theorem nonempty_mulEquiv_of_mem_orbitSet {K : Subgroup (Qt Y)} (hK : K ∈ orbitSet ρ K₀) :
    Nonempty (↥K ≃* ↥K₀) := by
  obtain ⟨γ, rfl⟩ := hK
  exact ⟨(MulEquiv.subgroupMap (qAct ρ γ) K₀).symm⟩

theorem map_iSup_eq_of_stable (ℒ : Set (Subgroup (Qt Y)))
    (hst : ∀ γ : Γ, ∀ K ∈ ℒ, K.map (qAct ρ γ).toMonoidHom ∈ ℒ) (γ : Γ) :
    (⨆ K ∈ ℒ, K : Subgroup (Qt Y)).map (qAct ρ γ).toMonoidHom = (⨆ K ∈ ℒ, K : Subgroup (Qt Y)) := by
  have key : ∀ δ : Γ, (⨆ K ∈ ℒ, K : Subgroup (Qt Y)).map (qAct ρ δ).toMonoidHom ≤
      (⨆ K ∈ ℒ, K : Subgroup (Qt Y)) := by
    intro δ
    rw [Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    exact le_iSup₂ (f := fun K (_ : K ∈ ℒ) => K) _ (hst δ K hK)
  refine le_antisymm (key γ) fun x hx => ?_
  refine ⟨(qAct ρ γ⁻¹) x, key γ⁻¹ ⟨x, hx, rfl⟩, ?_⟩
  change (qAct ρ γ) ((qAct ρ γ⁻¹) x) = x
  rw [← MulAut.mul_apply, ← map_mul]
  simp

end Orbit

@[expose] def restrictAut {G : Type*} [Group G] (φ : MulAut G) (K : Subgroup G)
    (h : K.map φ.toMonoidHom = K) : MulAut K :=
  (MulEquiv.subgroupMap φ K).trans (MulEquiv.subgroupCongr h)

theorem coe_restrictAut {G : Type*} [Group G] (φ : MulAut G) (K : Subgroup G)
    (h : K.map φ.toMonoidHom = K) (x : K) : ((restrictAut φ K h x : K) : G) = φ x := rfl

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {G : Type*} [Group G]
    (h : CFSG.Open.IsQuasisimple G) (hc : Subgroup.center G = ⊥) : IsSimpleGroup G := by
  have hs : IsSimpleGroup (G ⧸ Subgroup.center G) := h.2
  exact @MulEquiv.isSimpleGroup _ _ _ _ hs
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm

theorem nonempty_mulEquiv_pi_of_set {Q : Type*} [Group Q] [Finite Q] (S : Set (Subgroup Q))
    (hS : S.Finite) {K₀ : Type*} [Group K₀] (hiso : ∀ K ∈ S, Nonempty (↥K ≃* K₀))
    (hK : IsSimpleGroup K₀) (hKn : ∃ a b : K₀, a * b ≠ b * a)
    (hcomm : ∀ K ∈ S, ∀ K' ∈ S, K ≠ K' → K ≤ Subgroup.centralizer (K' : Set Q)) :
    Nonempty (↥(⨆ K ∈ S, K : Subgroup Q) ≃* (Fin (Nat.card ↥S) → K₀)) := by
  classical
  have : Fintype ↥S := hS.fintype
  obtain ⟨e⟩ := exists_mulEquiv_pi_fin (Q := Q) (ι := ↥S) (fun i => (i : Subgroup Q))
    (fun i => (hiso i.1 i.2).some) hK hKn
    (fun i j hij => hcomm i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h))
    (n := Nat.card ↥S) (Nat.card_eq_fintype_card.symm)
  have hsup : (⨆ i : ↥S, (i : Subgroup Q)) = ⨆ K ∈ S, K := by
    rw [iSup_subtype]
  exact ⟨(MulEquiv.subgroupCongr hsup.symm).trans e⟩

section Stabilizer

omit [Finite Y] [Finite Γ]

theorem exists_stabilizer_card (ρ : Γ →* MulAut Y) (K₀ : Subgroup (Qt Y)) :
    ∃ Stab : Subgroup Γ, (∀ γ, γ ∈ Stab ↔ K₀.map (qAct ρ γ).toMonoidHom = K₀) ∧
      Nat.card ↥(orbitSet ρ K₀) * Nat.card Stab = Nat.card Γ := by
  let _ : MulAction Γ (Subgroup (Qt Y)) := MulAction.compHom _ (qAct ρ)
  have hsmul : ∀ (γ : Γ) (K : Subgroup (Qt Y)), γ • K = K.map (qAct ρ γ).toMonoidHom :=
    fun γ K => rfl
  refine ⟨MulAction.stabilizer Γ K₀, fun γ => ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, hsmul]
  · have horb : MulAction.orbit Γ K₀ = orbitSet ρ K₀ := by
      ext K
      simp only [MulAction.mem_orbit_iff, hsmul]
      exact Iff.rfl
    rw [← horb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _

end Stabilizer

theorem structure_theorem (hΓ : IsPGroup p Γ) (hcomm : ∀ a b : Γ, a * b = b * a)
    (hexp : ∀ a : Γ, a ^ p = 1) (ρ : Γ →* MulAut Y) (hY : ¬ p ∣ Nat.card Y)
    (hS2 : ∀ S : Subgroup Y, IsPGroup 2 S → (∀ γ, S.map (ρ γ).toMonoidHom = S) → S ≠ ⊥ →
      ∀ K : Subgroup (Qt Y), IsComponentOf K ⊤ →
        ¬ S.map (mkQ Y) ≤ Subgroup.centralizer (K : Set (Qt Y)))
    (hFaith : ∀ γ : Γ, (∀ y ∈ preimQ (Ybar Y), ρ γ y * y⁻¹ ∈ GLAPPrimeCore 2 Y) → γ = 1)
    (hOut : ∀ K : Subgroup (Qt Y), IsComponentOf K ⊤ → IsSimpleGroup ↥K →
      (∃ a b : ↥K, a * b ≠ b * a) → CFSG.Open.pRank p (⊤ : Subgroup (Outer ↥K)) ≤ 1)
    {K₀ : Subgroup (Qt Y)} (hK₀ : IsComponentOf K₀ ⊤) :
    IsSimpleGroup ↥K₀ ∧ (∃ a b : ↥K₀, a * b ≠ b * a) ∧
      Nat.card Γ ≤ p * Nat.card ↥(orbitSet ρ K₀) ∧
      (∀ γ : Γ, (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)).map (qAct ρ γ).toMonoidHom =
        (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y))) ∧
      Nonempty (↥(⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) ≃*
        (Fin (Nat.card ↥(orbitSet ρ K₀)) → ↥K₀)) ∧
      Nonempty (↥(⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)) ≃*
        (Fin (Nat.card ↥(orbitSet ρ K₀) - 1) → ↥K₀)) ∧
      K₀ ≤ Subgroup.centralizer
        ((⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)) : Set (Qt Y)) ∧
      (⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)) ≤
        (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) ∧
      ((⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)).subgroupOf
        (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y))).Normal := by
  classical
  have hcompL : ∀ K ∈ orbitSet ρ K₀, IsComponentOf K ⊤ := fun K hK =>
    isComponentOf_of_mem_orbitSet ρ hK₀ hK
  have hcommC : ∀ K ∈ orbitSet ρ K₀, ∀ K' : Subgroup (Qt Y), IsComponentOf K' ⊤ → K ≠ K' →
      K ≤ Subgroup.centralizer (K' : Set (Qt Y)) := fun K hK K' hK' hne =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K K' (hcompL K hK) hK' hne)
  have hcommL : ∀ K ∈ orbitSet ρ K₀, ∀ K' ∈ orbitSet ρ K₀, K ≠ K' →
      K ≤ Subgroup.centralizer (K' : Set (Qt Y)) := fun K hK K' hK' hne =>
    hcommC K hK K' (hcompL K' hK') hne
  have hst : ∀ γ : Γ, ∀ K ∈ orbitSet ρ K₀, K.map (qAct ρ γ).toMonoidHom ∈ orbitSet ρ K₀ :=
    fun γ K hK => map_mem_orbitSet ρ hK γ
  have hbot := key_centralizer_eq_bot hΓ ρ hY hS2 (orbitSet ρ K₀) hcompL
    ⟨K₀, self_mem_orbitSet ρ⟩ hst
  have hK₀mem : K₀ ∈ orbitSet ρ K₀ := self_mem_orbitSet ρ
  have hLay : ∀ K : Subgroup (Qt Y), IsComponentOf K ⊤ → K ≤ Ybar Y := fun K hK =>
    (CFSG.ComponentClassification.Layer.component_le hK).trans le_sup_left
  have hallL : ∀ K' : Subgroup (Qt Y), IsComponentOf K' ⊤ → K' ∈ orbitSet ρ K₀ := by
    intro K' hK'
    by_contra hnot
    have hc : K' ≤ Subgroup.centralizer ((⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) :
        Set (Qt Y)) := by
      rw [Subgroup.le_centralizer_iff]
      exact iSup₂_le fun K hK => hcommC K hK K' hK' fun h => hnot (h ▸ hK)
    have hle : K' ≤ ⊥ := hbot ▸ le_inf (hLay K' hK') hc
    have : Nontrivial ↥K' := CFSG.ComponentClassification.Quasisimple.nontrivial hK'.2.2
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K')
    exact hx (Subtype.ext (Subgroup.mem_bot.1 (hle x.2)))
  have hLayLb : CFSG.ComponentClassification.Layer.subgroup (Qt Y) ≤
      (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) :=
    sSup_le fun K' hK' => le_iSup₂ (f := fun K (_ : K ∈ orbitSet ρ K₀) => K) K' (hallL K' hK')
  have hLbLay : (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) ≤
      CFSG.ComponentClassification.Layer.subgroup (Qt Y) :=
    iSup₂_le fun K hK => CFSG.ComponentClassification.Layer.component_le (hcompL K hK)
  have hpc : CFSG.Open.pCore 2 (Qt Y) ≤ Subgroup.centralizer
      ((⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) : Set (Qt Y)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn : (CFSG.Open.pCore 2 (Qt Y)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hnil : Group.IsNilpotent ↥(CFSG.Open.pCore 2 (Qt Y)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).isNilpotent
    have h1 := CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal
      (CFSG.Open.pCore 2 (Qt Y)) (isSubnormal_of_normal hn)
    exact Subgroup.le_centralizer_iff.2
      (hLbLay.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1))
  have hYbLb : Ybar Y ≤ (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) := by
    refine sup_le hLayLb ?_
    have : CFSG.Open.pCore 2 (Qt Y) ≤ ⊥ := hbot ▸ le_inf le_sup_right hpc
    exact this.trans bot_le
  have hcenter : ∀ K ∈ orbitSet ρ K₀, Subgroup.center ↥K = ⊥ := by
    intro K hK
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzK : (z : Qt Y) ∈ K := z.2
    have hle : (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) ≤
        Subgroup.centralizer ({(z : Qt Y)} : Set (Qt Y)) := by
      refine iSup₂_le fun K'' hK'' => ?_
      by_cases hKK : K'' = K
      · subst hKK
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨w, hw⟩)).symm
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact Subgroup.mem_centralizer_iff.1 (hcommL K'' hK'' K hK hKK hw) _ hzK
    have hzC : (z : Qt Y) ∈ Subgroup.centralizer
        ((⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) : Set (Qt Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.1 (hle hh) _ rfl).symm
    have hzY : (z : Qt Y) ∈ Ybar Y := hLay K (hcompL K hK) hzK
    have : (z : Qt Y) ∈ (⊥ : Subgroup (Qt Y)) := hbot ▸ Subgroup.mem_inf.2 ⟨hzY, hzC⟩
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hsimple : IsSimpleGroup ↥K₀ :=
    isSimpleGroup_of_isQuasisimple_of_center_eq_bot hK₀.2.2 (hcenter K₀ hK₀mem)
  have hnonab : ∃ a b : ↥K₀, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K₀)
    apply hx
    have hxc : x ∈ Subgroup.center ↥K₀ := Subgroup.mem_center_iff.2 fun g => h g x
    rw [hcenter K₀ hK₀mem] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hOut' := hOut K₀ hK₀ hsimple hnonab
  obtain ⟨Stab, hStab, hcard⟩ := exists_stabilizer_card ρ K₀
  have hStabcard : Nat.card Stab ≤ p := by
    have hKp : ¬ p ∣ Nat.card ↥K₀ := by
      intro h
      apply hY
      refine h.trans ((Subgroup.card_subgroup_dvd_card K₀).trans ?_)
      exact Subgroup.card_quotient_dvd_card _
    let f : Stab →* MulAut ↥K₀ := MonoidHom.mk'
      (fun γ => restrictAut (qAct ρ γ) K₀ ((hStab γ).1 γ.2))
      (fun a b => by
        ext x
        simp [coe_restrictAut])
    refine card_le_of_faithful hKp (hcenter K₀ hK₀mem) hOut'
      (fun a b => Subtype.ext (hcomm _ _)) (fun a => Subtype.ext (by simpa using hexp a.1)) f ?_
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hfix : ∀ x ∈ K₀, qAct ρ γ x = x := by
      intro x hx
      have := congrArg (fun φ : MulAut ↥K₀ => ((φ ⟨x, hx⟩ : ↥K₀) : Qt Y)) hγ
      exact this
    have hfixL : ∀ K ∈ orbitSet ρ K₀, ∀ x ∈ K, qAct ρ γ x = x := by
      rintro K ⟨δ, rfl⟩ x ⟨k, hk, rfl⟩
      change qAct ρ γ (qAct ρ δ k) = qAct ρ δ k
      rw [← MulAut.mul_apply, ← map_mul, hcomm (γ : Γ) δ, map_mul, MulAut.mul_apply, hfix k hk]
    let Fix : Subgroup (Qt Y) :=
      MonoidHom.eqLocus (qAct ρ γ).toMonoidHom (MonoidHom.id (Qt Y))
    have hLbFix : (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) ≤ Fix :=
      iSup₂_le fun K hK x hx => hfixL K hK x hx
    apply Subtype.ext
    show (γ : Γ) = 1
    refine hFaith γ fun y hy => ?_
    have hy' : qAct ρ γ (mkQ Y y) = mkQ Y y := hLbFix (hYbLb hy)
    rw [qAct_mk] at hy'
    have : mkQ Y (ρ γ y * y⁻¹) = 1 := by rw [map_mul, map_inv, hy', mul_inv_cancel]
    exact (QuotientGroup.ker_mk' (GLAPPrimeCore 2 Y)) ▸ (MonoidHom.mem_ker.2 this)
  have hΓcard : Nat.card Γ ≤ p * Nat.card ↥(orbitSet ρ K₀) := by
    rw [← hcard, mul_comm]
    exact Nat.mul_le_mul_right _ hStabcard
  have hfin : (orbitSet ρ K₀).Finite := finite_orbitSet ρ
  have hiso : ∀ K ∈ orbitSet ρ K₀, Nonempty (↥K ≃* ↥K₀) := fun K hK =>
    nonempty_mulEquiv_of_mem_orbitSet ρ hK
  have hdiffsub : orbitSet ρ K₀ \ {K₀} ⊆ orbitSet ρ K₀ := Set.sdiff_subset
  have hiso1 : Nonempty (↥(⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) ≃*
      (Fin (Nat.card ↥(orbitSet ρ K₀)) → ↥K₀)) :=
    nonempty_mulEquiv_pi_of_set (Q := Qt Y) (orbitSet ρ K₀) hfin hiso hsimple hnonab hcommL
  have hcard2 : Nat.card ↥(orbitSet ρ K₀ \ {K₀}) = Nat.card ↥(orbitSet ρ K₀) - 1 := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_sdiff_singleton_of_mem hK₀mem
  have hiso2 : Nonempty (↥(⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)) ≃*
      (Fin (Nat.card ↥(orbitSet ρ K₀) - 1) → ↥K₀)) := by
    have := nonempty_mulEquiv_pi_of_set (Q := Qt Y) (orbitSet ρ K₀ \ {K₀})
      (hfin.subset hdiffsub) (fun K hK => hiso K hK.1) hsimple hnonab
      (fun K hK K' hK' hne => hcommL K hK.1 K' hK'.1 hne)
    rw [hcard2] at this
    exact this
  have hcentral : K₀ ≤ Subgroup.centralizer
      ((⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)) : Set (Qt Y)) := by
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun K hK => hcommL K hK.1 K₀ hK₀mem fun h => hK.2 h
  have hsub : (⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)) ≤
      (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y)) :=
    iSup₂_mono' fun K hK => ⟨K, hK.1, le_rfl⟩
  have hnormal : ((⨆ K ∈ orbitSet ρ K₀ \ {K₀}, K : Subgroup (Qt Y)).subgroupOf
      (⨆ K ∈ orbitSet ρ K₀, K : Subgroup (Qt Y))).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    refine iSup₂_le fun K hK => ?_
    by_cases hKK : K = K₀
    · subst hKK
      exact hcentral.trans (Subgroup.centralizer_le_normalizer _)
    · exact (le_iSup₂ (f := fun K (_ : K ∈ orbitSet ρ K₀ \ {K₀}) => K) K
        ⟨hK, fun h => hKK h⟩).trans
        Subgroup.le_normalizer
  exact ⟨hsimple, hnonab, hΓcard, fun γ => map_iSup_eq_of_stable ρ _ hst γ, hiso1, hiso2,
    hcentral, hsub, hnormal⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
