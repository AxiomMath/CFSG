module

public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.ExactNormalFormE

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section General

variable {τ : Tag} {K : Type} [Field K]

theorem units_map_entrywiseHom_rootDiagUnit_ringEquiv (δ : K ≃+* K) (b : Fin τ.rank → Kˣ) :
    Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit τ b) =
      rootDiagUnit τ (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) :=
  Units.ext (entrywise_rootDiag δ.toRingHom b)

theorem units_map_entrywiseHom_mul_ringEquiv (δ ε : K ≃+* K) (x : ModGL τ K) :
    Units.map (entrywiseHom (δ * ε).toRingHom) x =
      Units.map (entrywiseHom δ.toRingHom) (Units.map (entrywiseHom ε.toRingHom) x) := by
  refine Units.ext ?_
  change entrywise (δ * ε).toRingHom (x : Module.End K (RootModule τ K)) =
    entrywise δ.toRingHom (entrywise ε.toRingHom (x : Module.End K (RootModule τ K)))
  exact (entrywise_entrywise δ.toRingHom ε.toRingHom _).symm

theorem units_map_entrywiseHom_one_ringEquiv (x : ModGL τ K) :
    Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
  Units.ext (entrywise_id _)

@[expose] def diagonalFieldActorSet (S : Subgroup (ModGL τ K)) (A : Set (Fin τ.rank → Kˣ))
    (D : Subgroup (K ≃+* K)) : Set (MulAut S) :=
  {φ | ∃ g ∈ S, ∃ a ∈ A, ∃ δ ∈ D, ∀ x : S, (φ x : ModGL τ K) =
    g * rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ * g⁻¹}

variable {S : Subgroup (ModGL τ K)} {A : Set (Fin τ.rank → Kˣ)} {D : Subgroup (K ≃+* K)}

theorem conj_mem_diagonalFieldActorSet (hA : 1 ∈ A) (g : S) :
    MulAut.conj g ∈ diagonalFieldActorSet S A D :=
  ⟨g, g.2, 1, hA, 1, D.one_mem, fun x => by
    rw [rootDiagUnit_one, units_map_entrywiseHom_one_ringEquiv, MulAut.conj_apply]
    simp⟩

theorem exists_mem_diagonalFieldActorSet {g : ModGL τ K} (hg : g ∈ S) {a : Fin τ.rank → Kˣ}
    (ha : a ∈ A) {δ : K ≃+* K} (hδ : δ ∈ D)
    (hda : S.map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = S)
    (hδS : S.map (Units.map (entrywiseHom δ.toRingHom)) = S) :
    ∃ φ ∈ diagonalFieldActorSet S A D, ∀ x : S, (φ x : ModGL τ K) =
      g * rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ *
        g⁻¹ := by
  set α : MulAut (ModGL τ K) := MulAut.conj (g * rootDiagUnit τ a) * exactEntrywiseAut τ δ
  have hαx : ∀ x : ModGL τ K, α x =
      g * rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ *
        g⁻¹ := fun x => by
    rw [MulAut.mul_apply, MulAut.conj_apply, exactEntrywiseAut_apply]
    group
  have e : α.toMonoidHom = ((MulAut.conj g).toMonoidHom.comp
      (MulAut.conj (rootDiagUnit τ a)).toMonoidHom).comp
        (Units.map (entrywiseHom δ.toRingHom)) := MonoidHom.ext fun x => by
    rw [MulEquiv.coe_toMonoidHom, hαx]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hα : S.map α.toMonoidHom = S := by
    rw [e, ← Subgroup.map_map, ← Subgroup.map_map, hδS, hda,
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)]
  refine ⟨mulAutRestrict S α hα, ⟨g, hg, a, ha, δ, hδ, fun x => ?_⟩, fun x => ?_⟩ <;>
    rw [coe_mulAutRestrict, hαx]

theorem mul_mem_diagonalFieldActorSet
    (hA : ∀ a ∈ A, ∀ b ∈ A, ∀ δ ∈ D, a * (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) ∈ A)
    {φ ψ : MulAut S} (hφ : φ ∈ diagonalFieldActorSet S A D)
    (hψ : ψ ∈ diagonalFieldActorSet S A D) : φ * ψ ∈ diagonalFieldActorSet S A D := by
  obtain ⟨g, hg, a, ha, δ, hδ, hφx⟩ := hφ
  obtain ⟨h, hh, b, hb, ε, hε, hψx⟩ := hψ
  refine ⟨(φ ⟨h, hh⟩ : ModGL τ K) * g, mul_mem (φ ⟨h, hh⟩).2 hg,
    a * (fun i => Units.map δ.toRingHom.toMonoidHom (b i)), hA a ha b hb δ hδ, δ * ε,
    mul_mem hδ hε, fun x => ?_⟩
  rw [MulAut.mul_apply, hφx, hψx, hφx, rootDiagUnit_mul, units_map_entrywiseHom_mul_ringEquiv]
  simp only [map_mul, map_inv, units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  group

theorem inv_mem_diagonalFieldActorSet
    (hA : ∀ a ∈ A, ∀ δ ∈ D, (fun i => Units.map δ⁻¹.toRingHom.toMonoidHom (a i))⁻¹ ∈ A)
    {φ : MulAut S} (hφ : φ ∈ diagonalFieldActorSet S A D) :
    φ⁻¹ ∈ diagonalFieldActorSet S A D := by
  obtain ⟨g, hg, a, ha, δ, hδ, hφx⟩ := hφ
  set ι := Units.map (entrywiseHom δ⁻¹.toRingHom) (M := Module.End K (RootModule τ K))
  have key : ∀ z : S, ((φ⁻¹ z : S) : ModGL τ K) = (ι (rootDiagUnit τ a))⁻¹ * (ι g)⁻¹ * ι z *
      ι g * ι (rootDiagUnit τ a) := by
    intro z
    have hz := hφx (φ⁻¹ z)
    rw [MulAut.apply_inv_self] at hz
    have h1 : Units.map (entrywiseHom δ.toRingHom) ((φ⁻¹ z : S) : ModGL τ K) =
        (rootDiagUnit τ a)⁻¹ * g⁻¹ * z * g * rootDiagUnit τ a := by
      rw [hz]
      group
    have h2 := congrArg ι h1
    rw [show ι (Units.map (entrywiseHom δ.toRingHom) ((φ⁻¹ z : S) : ModGL τ K)) =
      ((φ⁻¹ z : S) : ModGL τ K) from exactEntrywiseAut_left_inv δ _] at h2
    rw [h2]
    simp only [map_mul, map_inv]
  refine ⟨((φ⁻¹ ⟨g⁻¹, inv_mem hg⟩ : S) : ModGL τ K), (φ⁻¹ ⟨g⁻¹, inv_mem hg⟩).2,
    (fun i => Units.map δ⁻¹.toRingHom.toMonoidHom (a i))⁻¹, hA a ha δ hδ, δ⁻¹, inv_mem hδ,
    fun y => ?_⟩
  rw [key y, key ⟨g⁻¹, inv_mem hg⟩, ← rootDiagUnit_inv]
  change _ = _ * _ * ι y * _ * _
  rw [show ι (rootDiagUnit τ a) =
    rootDiagUnit τ (fun i => Units.map δ⁻¹.toRingHom.toMonoidHom (a i)) from
      units_map_entrywiseHom_rootDiagUnit_ringEquiv δ⁻¹ a]
  simp only [map_inv]
  group

@[expose] def diagonalFieldActorSubgroup (S : Subgroup (ModGL τ K)) (A : Set (Fin τ.rank → Kˣ))
    (D : Subgroup (K ≃+* K)) (h1 : 1 ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, ∀ δ ∈ D,
      a * (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) ∈ A)
    (hinv : ∀ a ∈ A, ∀ δ ∈ D, (fun i => Units.map δ⁻¹.toRingHom.toMonoidHom (a i))⁻¹ ∈ A) :
    Subgroup (MulAut S) where
  carrier := diagonalFieldActorSet S A D
  one_mem' := by
    have h := conj_mem_diagonalFieldActorSet (D := D) h1 (1 : S)
    rwa [map_one] at h
  mul_mem' := mul_mem_diagonalFieldActorSet hmul
  inv_mem' := inv_mem_diagonalFieldActorSet hinv

end General

@[expose] def diagonalFieldActors (τ : Tag) (K : Type) [Field K] :
    Subgroup (MulAut (adjointGroup τ K)) :=
  diagonalFieldActorSubgroup (adjointGroup τ K) Set.univ ⊤ trivial
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)

section Fixed

variable {K : Type} [Field K]

@[expose] def compatibleTuples (t : TwistTag) (σ : K ≃+* K) : Set (Fin t.tag.rank → Kˣ) :=
  {a | ∀ i, a (t.perm i) = Units.map σ.toRingHom.toMonoidHom (a i)}

variable {t : TwistTag} {σ : K ≃+* K}

theorem apply_comm_of_mem_centralizer {δ : K ≃+* K} (hδ : δ ∈ Subgroup.centralizer {σ})
    (c : K) : δ (σ c) = σ (δ c) :=
  congrArg (fun φ : K ≃+* K => φ c) (Subgroup.mem_centralizer_singleton_iff.1 hδ)

theorem compatibleTuples_mul {a b : Fin t.tag.rank → Kˣ} (ha : a ∈ compatibleTuples t σ)
    (hb : b ∈ compatibleTuples t σ) {δ : K ≃+* K} (hδ : δ ∈ Subgroup.centralizer {σ}) :
    a * (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) ∈ compatibleTuples t σ := by
  intro i
  simp only [Pi.mul_apply]
  rw [map_mul, ha i, hb i]
  congr 1
  exact Units.ext (apply_comm_of_mem_centralizer hδ (b i))

theorem compatibleTuples_inv {a : Fin t.tag.rank → Kˣ} (ha : a ∈ compatibleTuples t σ)
    {δ : K ≃+* K} (hδ : δ ∈ Subgroup.centralizer {σ}) :
    (fun i => Units.map δ⁻¹.toRingHom.toMonoidHom (a i))⁻¹ ∈ compatibleTuples t σ := by
  intro i
  simp only [Pi.inv_apply]
  rw [map_inv, ha i]
  congr 1
  exact Units.ext (apply_comm_of_mem_centralizer (inv_mem hδ) (a i))

end Fixed

@[expose] def fixedDiagonalFieldActors
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)) :=
  diagonalFieldActorSubgroup (graphFixedRootGroup t K σ.toRingHom) (compatibleTuples t σ)
    (Subgroup.centralizer {σ}) (fun _ => (map_one _).symm)
    (fun _ ha _ hb _ hδ => compatibleTuples_mul ha hb hδ)
    (fun _ ha _ hδ => compatibleTuples_inv ha hδ)


theorem Chevalley_diagonal_field_actor_data :
    (∀ (τ : Tag) (K : Type) [Field K],
      (∀ φ : MulAut (adjointGroup τ K), φ ∈ diagonalFieldActors τ K ↔
        ∃ g ∈ adjointGroup τ K, ∃ (a : Fin τ.rank → Kˣ) (δ : K ≃+* K),
          ∀ x : adjointGroup τ K, (φ x : ModGL τ K) = g * rootDiagUnit τ a *
            Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ * g⁻¹) ∧
      (∀ g ∈ adjointGroup τ K, ∀ (a : Fin τ.rank → Kˣ) (δ : K ≃+* K),
        ∃ φ ∈ diagonalFieldActors τ K, ∀ x : adjointGroup τ K, (φ x : ModGL τ K) =
          g * rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x *
            (rootDiagUnit τ a)⁻¹ * g⁻¹) ∧
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ≤
        diagonalFieldActors τ K) ∧
    (∀ (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K),
      (∀ φ : MulAut (graphFixedRootGroup t K σ.toRingHom), φ ∈ fixedDiagonalFieldActors t K σ ↔
        ∃ g ∈ graphFixedRootGroup t K σ.toRingHom, ∃ a : Fin t.tag.rank → Kˣ,
          (∀ i, a (t.perm i) = Units.map σ.toRingHom.toMonoidHom (a i)) ∧
          ∃ δ : K ≃+* K, δ * σ = σ * δ ∧ ∀ x : graphFixedRootGroup t K σ.toRingHom,
            (φ x : ModGL t.tag K) = g * rootDiagUnit t.tag a *
              Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit t.tag a)⁻¹ * g⁻¹) ∧
      (∀ g ∈ graphFixedRootGroup t K σ.toRingHom, ∀ a : Fin t.tag.rank → Kˣ,
        (∀ i, a (t.perm i) = Units.map σ.toRingHom.toMonoidHom (a i)) →
        ∀ δ : K ≃+* K, δ * σ = σ * δ →
        ∃ φ ∈ fixedDiagonalFieldActors t K σ, ∀ x : graphFixedRootGroup t K σ.toRingHom,
          (φ x : ModGL t.tag K) = g * rootDiagUnit t.tag a *
            Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit t.tag a)⁻¹ * g⁻¹) ∧
      (MulAut.conj : graphFixedRootGroup t K σ.toRingHom →*
          MulAut (graphFixedRootGroup t K σ.toRingHom)).range ≤
        fixedDiagonalFieldActors t K σ) := by
  refine ⟨fun τ K _ => ⟨fun φ => ?_, fun g hg a δ => ?_, ?_⟩,
    fun t K _ σ => ⟨fun φ => ?_, fun g hg a ha δ hδ => ?_, ?_⟩⟩
  · constructor
    · rintro ⟨g, hg, a, -, δ, -, hφ⟩
      exact ⟨g, hg, a, δ, hφ⟩
    · rintro ⟨g, hg, a, δ, hφ⟩
      exact ⟨g, hg, a, trivial, δ, trivial, hφ⟩
  · have h := (chevalley_root_character_and_field_conjugation τ K)
    exact exists_mem_diagonalFieldActorSet hg (Set.mem_univ a) (Subgroup.mem_top δ)
      (h.2.2.2.1 a).1 (h.2.2.2.2.1 δ).1
  · rintro _ ⟨g, rfl⟩
    exact conj_mem_diagonalFieldActorSet (Set.mem_univ 1) g
  · constructor
    · rintro ⟨g, hg, a, ha, δ, hδ, hφ⟩
      exact ⟨g, hg, a, ha, δ, Subgroup.mem_centralizer_singleton_iff.1 hδ, hφ⟩
    · rintro ⟨g, hg, a, ha, δ, hδ, hφ⟩
      exact ⟨g, hg, a, ha, δ, Subgroup.mem_centralizer_singleton_iff.2 hδ, hφ⟩
  · have hδ' : δ ∈ Subgroup.centralizer {σ} := Subgroup.mem_centralizer_singleton_iff.2 hδ
    exact exists_mem_diagonalFieldActorSet (A := compatibleTuples t σ) hg ha hδ'
      (map_conj_rootDiagUnit_graphFixedRootGroup (σ := σ.toRingHom) ha)
      (map_units_map_entrywiseHom_graphFixedRootGroup (σ := σ.toRingHom)
        (apply_comm_of_mem_centralizer hδ'))
  · rintro _ ⟨g, rfl⟩
    exact conj_mem_diagonalFieldActorSet (A := compatibleTuples t σ) (fun _ => (map_one _).symm) g

end CFSG.LieType.Chevalley
