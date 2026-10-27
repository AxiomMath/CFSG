module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.Goldschmidt.StrongClosure
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Goldschmidt

open CFSG.Open

@[expose] def Conclusion (Y : Type) [Group Y] (S A : Subgroup Y) : Prop :=
  CFSG.Open.pCore 2 (Y ⧸ goldschmidtOddCore Y) ⊔ goldschmidtLayer (Y ⧸ goldschmidtOddCore Y) = ⊤ ∧
  A.map (QuotientGroup.mk' (goldschmidtOddCore Y)) =
    CFSG.Open.pCore 2 (Y ⧸ goldschmidtOddCore Y) ⊔ Subgroup.closure
      {t | t ∈ S.map (QuotientGroup.mk' (goldschmidtOddCore Y)) ⊓
        goldschmidtLayer (Y ⧸ goldschmidtOddCore Y) ∧ t ^ 2 = 1} ∧
  ∀ K : Subgroup (Y ⧸ goldschmidtOddCore Y), IsComponentOf K ⊤ →
    goldschmidtSimpleType (K ⧸ Subgroup.center K)

@[expose] def TopStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (S : Sylow 2 Y) (A : Subgroup Y), A ≤ S →
    IsMulCommutative A → fusionStronglyClosed (A : Set Y) (S : Subgroup Y) →
    Subgroup.normalClosure (A : Set Y) = ⊤ → Conclusion Y S A

theorem normalClosure_subgroupOf_eq_top {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    {A : Subgroup X} (hAP : A ≤ P) (hcl : fusionStronglyClosed (A : Set X) (P : Subgroup X))
    {M : Subgroup X} (hM : M = Subgroup.normalClosure (A : Set X)) :
    Subgroup.normalClosure ((A.subgroupOf M : Subgroup M) : Set M) = ⊤ := by
  subst hM
  set M := Subgroup.normalClosure (A : Set X)
  set N := Subgroup.normalClosure (((A.subgroupOf M) : Subgroup M) : Set M)
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hle : M ≤ N.map M.subtype := by
    change Subgroup.closure (Group.conjugatesOfSet (A : Set X)) ≤ _
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hay
    obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosure P hAP hcl c⁻¹
    have hy : c * a * c⁻¹ ∈ conjSub m A := by
      rw [← hmeq, mem_conjSub]
      simpa [mul_assoc] using ha
    rw [mem_conjSub] at hy
    have hyM : c * a * c⁻¹ ∈ M := by
      have := (Subgroup.normalClosure_normal (s := (A : Set X))).conj_mem a (hAM ha) c
      exact this
    refine ⟨⟨c * a * c⁻¹, hyM⟩, ?_, rfl⟩
    have h1 : (⟨m * (c * a * c⁻¹) * m⁻¹, hAM hy⟩ : M) ∈ N :=
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hy)
    have h2 := hNn.conj_mem _ h1 (⟨m, hm⟩ : M)⁻¹
    have heq : (⟨c * a * c⁻¹, hyM⟩ : M) =
        (⟨m, hm⟩ : M)⁻¹ * ⟨m * (c * a * c⁻¹) * m⁻¹, hAM hy⟩ * (⟨m, hm⟩ : M)⁻¹⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    show (⟨c * a * c⁻¹, hyM⟩ : M) ∈ N
    rw [heq]
    exact h2
  rw [eq_top_iff]
  intro z _
  obtain ⟨w, hw, hwz⟩ := hle z.2
  rw [show z = w from Subtype.ext hwz.symm]
  exact hw

theorem isMulCommutative_subgroupOf {X : Type} [Group X] {A : Subgroup X}
    (hA : IsMulCommutative A) (M : Subgroup X) : IsMulCommutative (A.subgroupOf M) :=
  ⟨⟨fun x y => by
    have h := hA.is_comm.comm ⟨((x : M) : X), x.2⟩ ⟨((y : M) : X), y.2⟩
    have h' : ((x : M) : X) * ((y : M) : X) = ((y : M) : X) * ((x : M) : X) :=
      congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    simpa using h'⟩⟩

theorem milestone_of_topStatement (h : TopStatement) (X : Type) [Group X] [Finite X]
    (S : Sylow 2 X) (A : Subgroup X) (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) :
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  intro M π T
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hMn.isSubnormal
  have hPeq : (P : Subgroup M) = (S : Subgroup X).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hAP : A.subgroupOf M ≤ (P : Subgroup M) := by
    rw [hPeq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAS (Subgroup.mem_subgroupOf.1 hx))
  have hcl' := stronglyClosed_subgroupOf S hclosed hAM P hAP
  have htop := normalClosure_subgroupOf_eq_top S hAS hclosed (M := M) rfl
  have hC := h M P (A.subgroupOf M) hAP (isMulCommutative_subgroupOf hAab M) hcl' htop
  rw [hPeq] at hC
  exact hC

end CFSG.Goldschmidt
