module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltCent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltFin
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltSn

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem c143Alt_holds : C143Alt := by
  intro Y _ _ hY _ hAlt α hα J hJ hexc
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
  obtain ⟨h20160, -, -⟩ := exc_facts hKq hexc
  by_cases hn : n ≤ 7
  · have h1 : Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≤ Nat.card ↥(J.map φ) :=
      Nat.card_le_card_of_surjective f hf
    have h2 : Nat.card ↥(J.map φ) ≤ Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_le_card_group _
    rw [Nat.card_perm, Nat.card_fin] at h2
    have h3 : n.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le hn
    have h4 : (7 : ℕ).factorial = 5040 := by decide
    omega
  ·
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
    exact false_of_alt hKq hexc h5 e'

end CFSG.HardMathSupport.Solomon.Coordinator
