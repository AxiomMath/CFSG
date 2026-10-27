module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltCent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltFin
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltSn
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

theorem alt_down_core {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hAlt : Lemma25Ns.IsAltType (Y ⧸ Subgroup.center Y)) {α : MulAut Y} (hα : α ^ 3 = 1)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) :
    Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≤ 5040 ∨
      ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β), 5 ≤ Nat.card β ∧
        Nonempty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* alternatingGroup β) := by
  have hKq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  have hLs : IsSimpleGroup (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) := hKq.2
  have hLns : ¬ Group.IsSolvable (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) := fun hs =>
    CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hKq
      (Group.isSolvable_of_subgroup_quotient (Subgroup.center (barOf 3 J)))
  obtain ⟨n, ⟨e⟩⟩ := hAlt
  let φ : Y →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)))
  have hφapp : ∀ y, φ y = ((e (QuotientGroup.mk y) : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n)) := fun y => rfl
  have hker : φ.ker ≤ Subgroup.center Y := by
    intro x hx
    rw [MonoidHom.mem_ker, hφapp] at hx
    have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext hx
    rw [map_eq_one_iff _ e.injective] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hrange : φ.range = alternatingGroup (Fin n) := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact (e (QuotientGroup.mk y)).2
    · intro hp
      obtain ⟨a, ha⟩ := e.surjective ⟨p, hp⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
      exact ⟨y, by rw [hφapp, ha]⟩
  let g : ↥J →* barOf 3 J ⧸ Subgroup.center (barOf 3 J) :=
    (QuotientGroup.mk' (Subgroup.center (barOf 3 J))).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hgk : ∀ j : ↥J, φ j = 1 → g j = 1 := by
    intro j hj
    have hjc := Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hj))
    refine (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_center_iff.2 fun k => ?_)
    obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective k
    show QuotientGroup.mk j' * QuotientGroup.mk j = QuotientGroup.mk j * QuotientGroup.mk j'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hjc j'))
  have hkerle : (φ.subgroupMap J).ker ≤ g.ker := by
    intro x hx
    rw [Subgroup.ker_subgroupMap, Subgroup.mem_subgroupOf] at hx
    exact MonoidHom.mem_ker.2 (hgk x (MonoidHom.mem_ker.1 hx))
  let f : ↥(J.map φ) →* barOf 3 J ⧸ Subgroup.center (barOf 3 J) :=
    MonoidHom.liftOfSurjective (φ.subgroupMap J) (φ.subgroupMap_surjective J) ⟨g, hkerle⟩
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, rfl⟩ := hg l
    exact ⟨φ.subgroupMap J x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨g, hkerle⟩ x⟩
  by_cases hn : n ≤ 7
  · left
    have h1 : Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≤ Nat.card ↥(J.map φ) :=
      Nat.card_le_card_of_surjective f hf
    have h2 : Nat.card ↥(J.map φ) ≤ Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_le_card_group _
    rw [Nat.card_perm, Nat.card_fin] at h2
    have h3 : n.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le hn
    have h4 : (7 : ℕ).factorial = 5040 := by decide
    omega
  · right
    let ᾱ : MulAut (Y ⧸ Subgroup.center Y) :=
      QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) α (map_center_mulEquiv α)
    have hᾱ : ∀ y : Y, ᾱ (QuotientGroup.mk y) = QuotientGroup.mk (α y) := fun y => rfl
    have hᾱk : ∀ (k : ℕ) (y : Y), (ᾱ ^ k) (QuotientGroup.mk y) = QuotientGroup.mk ((α ^ k) y) := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih => intro y; rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hᾱ, ih]
    have hᾱ3 : ᾱ ^ 3 = 1 := by
      ext z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
      rw [hᾱk, hα]
      rfl
    let β : MulAut (alternatingGroup (Fin n)) := MulAut.congr e ᾱ
    have hβe : ∀ z, β (e z) = e (ᾱ z) := fun z => by simp [β]
    have hβ3 : β ^ 3 = 1 := by rw [← map_pow, hᾱ3, map_one]
    have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
      (by omega) (by omega)
    obtain ⟨σ, hσ⟩ := hbij.2 β
    have hσ3 : σ ^ 3 = 1 := by
      refine hbij.1 ?_
      rw [map_pow, hσ, hβ3, map_one]
    have hφ : ∀ y, φ (α y) = σ * φ y * σ⁻¹ := by
      intro y
      rw [hφapp, hφapp, ← hᾱ, ← hβe, ← hσ, MulAut.conjNormal_apply]
    obtain ⟨hle, hsn⟩ := isSubnormal_map_centralizer φ hrange hker α σ hφ hJ.2.1
    have hq : IsSubnormalQuotient (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))))
        (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) :=
      ⟨(J.map φ).subgroupOf (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))), hsn,
        f.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom,
        hf.comp (MulEquiv.surjective _)⟩
    obtain ⟨β', _, _, h5, ⟨e'⟩⟩ := IsSubnormalQuotient.alt_of_centralizer hσ3 hLns hq
    exact ⟨β', inferInstance, inferInstance, h5, ⟨e'⟩⟩

theorem l34Alt_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      Lemma25Ns.IsAltType (Y ⧸ Subgroup.center Y) → ∀ α : MulAut Y, α ^ 3 = 1 →
      ∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J → ¬ IsLThreeFour (barOf 3 J) := by
  intro Y _ _ hY hAlt α hα J hJ hL34
  have hcard : Nat.card (barOf 3 J) = 20160 := card_eq_of_isLThreeFour hL34
  obtain ⟨hs, hna⟩ := isSimpleGroup_of_isLThreeFour hL34
  haveI := hs
  have hZ : Subgroup.center (barOf 3 J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (barOf 3 J)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  let eL : (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* barOf 3 J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hLcard : Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) = 20160 := by
    rw [Nat.card_congr eL.toEquiv]
    exact hcard
  rcases alt_down_core hY hAlt hα hJ with hle | ⟨β, _, _, h5, ⟨eA⟩⟩
  · omega
  · have hnt : Nontrivial β := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    have hcardA : Nat.card (alternatingGroup β) = 20160 := by
      rw [← Nat.card_congr eA.toEquiv]
      exact hLcard
    have h2 := two_mul_nat_card_alternatingGroup (α := β)
    rw [Nat.card_perm, hcardA] at h2
    have hb : Nat.card β = 8 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 : (Nat.card β).factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
        have h7 : (7 : ℕ).factorial = 5040 := by decide
        omega
      · have h1 : (9 : ℕ).factorial ≤ (Nat.card β).factorial := Nat.factorial_le (by omega)
        have h9 : (9 : ℕ).factorial = 362880 := by decide
        omega
    obtain ⟨F, _, _, hF4, ⟨eS⟩⟩ := hL34
    let eP : barOf 3 J ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
      eS.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).symm
    have hcardβ : Fintype.card β = 8 := by rw [← Nat.card_eq_fintype_card]; exact hb
    exact false_of_projectiveSL_alt_eight hF4
      (((eP.symm.trans eL.symm).trans eA).trans
        (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcardβ)))

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
