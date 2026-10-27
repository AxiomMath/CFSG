module

public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

open CFSG Subgroup

theorem fitting_eq_bot_of_cores {X : Type} [Group X] [Finite X]
    (h2 : pCore 2 X = ⊥) (hodd : oddCore X = ⊥) : fittingSubgroup X = ⊥ := by
  have h := WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore (G := X)
  rw [h2, hodd, sup_bot_eq] at h
  exact le_bot_iff.mp h

theorem exists_component_of_cores {X : Type} [Group X] [Finite X] [Nontrivial X]
    (h2 : pCore 2 X = ⊥) (hodd : oddCore X = ⊥) : ∃ K : Subgroup X, IsComponent K := by
  by_contra hno
  push_neg at hno
  have hF := (LocalCores.generalized_fitting_minimal_normal (G := X)).2 inferInstance
  have hL : layer X = ⊥ := LocalCores.layer_eq_bot_of_forall hno
  apply hF
  rw [generalizedFitting.eq_sup, hL, sup_bot_eq, fitting_eq_bot_of_cores h2 hodd]

theorem layer_normal_of_group (X : Type) [Group X] : (layer X).Normal :=
  @Subgroup.normal_of_characteristic X _ (layer X) (LocalCores.layer_characteristic (G := X))

theorem center_component_eq_bot {X : Type} [Group X] [Finite X]
    (h2 : pCore 2 X = ⊥) (hodd : oddCore X = ⊥) {K : Subgroup X} (hK : IsComponent K) :
    Subgroup.center ↥K = ⊥ := by
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup X,
      A = layer X ⊓ Subgroup.centralizer ((layer X : Subgroup X) : Set X) := ⟨_, rfl⟩
  have hAmem : ∀ a : X, a ∈ A ↔ a ∈ layer X ∧ ∀ g ∈ layer X, a * g = g * a := by
    intro a
    rw [hAdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h3⟩
      exact ⟨h1, fun g hg => (h3 g hg).symm⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, fun g hg => (h3 g hg).symm⟩
  have hZ : ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∀ g ∈ layer X, g * z = z * g := by
    intro z hzK hzc
    have hcentL : layer X ≤ Subgroup.centralizer ({z} : Set X) := by
      rw [layer.eq_sSup]
      apply sSup_le
      intro L hL
      have hLc : IsComponent L := hL
      have hall : ∀ l ∈ L, z * l = l * z := by
        by_cases hLK : L = K
        · subst hLK
          intro l hl
          exact (hzc l hl).symm
        · rcases LocalCores.distinct_components_commute hK hLc with hKL | hcom
          · exact absurd hKL.symm hLK
          · intro l hl
            have hzcent : z ∈ Subgroup.centralizer (L : Set X) :=
              commutator_eq_bot_iff_le_centralizer.mp hcom hzK
            exact (Subgroup.mem_centralizer_iff.mp hzcent l hl).symm
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hall l hl
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hcentL hg) z (Set.mem_singleton z)).symm
  have hAnorm : A.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hAmem] at ha ⊢
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨(layer_normal_of_group X).conj_mem a ha1 g, fun h hh => ?_⟩
    have hh' : g⁻¹ * h * g ∈ layer X := by
      have := (layer_normal_of_group X).conj_mem h hh g⁻¹
      rwa [inv_inv] at this
    have hcomm := ha2 _ hh'
    calc g * a * g⁻¹ * h = g * (a * (g⁻¹ * h * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * h * g) * a) * g⁻¹ := by rw [hcomm]
      _ = h * (g * a * g⁻¹) := by group
  have hAcomm : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    apply Subtype.ext
    exact ((hAmem a).mp a.2).2 b (((hAmem b).mp b.2).1)
  have hAfit : A ≤ fittingSubgroup X := by
    letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hAcomm }
    exact le_sSup (show A ∈ {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} from
      ⟨hAnorm, inferInstance⟩)
  rw [fitting_eq_bot_of_cores h2 hodd] at hAfit
  rw [eq_bot_iff]
  intro z hz
  have hzc : ∀ k : K, k * z = z * k := fun k => Subgroup.mem_center_iff.mp hz k
  have hzX : ∀ k ∈ K, k * (z : X) = (z : X) * k := by
    intro k hk
    have := congrArg Subtype.val (hzc ⟨k, hk⟩)
    exact this
  have hzA : (z : X) ∈ A := by
    rw [hAmem]
    refine ⟨le_sSup (show K ∈ {L : Subgroup X | IsComponent L} from hK) z.2, ?_⟩
    intro g hg
    exact (hZ (z : X) z.2 hzX g hg).symm
  have h1 : (z : X) ∈ (⊥ : Subgroup X) := hAfit hzA
  rw [Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext h1

theorem isSimpleGroup_of_component {X : Type} [Group X] [Finite X]
    (h2 : pCore 2 X = ⊥) (hodd : oddCore X = ⊥) {K : Subgroup X} (hK : IsComponent K) :
    IsSimpleGroup ↥K := by
  have hc := center_component_eq_bot h2 hodd hK
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  let e : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := ↥K))
  haveI : Nontrivial ↥K := e.symm.surjective.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

theorem nonabelian_of_component {X : Type} [Group X] {K : Subgroup X} (hK : IsComponent K) :
    ¬ ∀ a b : ↥K, a * b = b * a := by
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  intro hcomm
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a' b']

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
