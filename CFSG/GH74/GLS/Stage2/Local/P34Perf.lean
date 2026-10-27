module

public import CFSG.GH74.GLS.Stage2.Local.P34Comp
public import CFSG.GH74.GLS.Stage2.Local.P34Kind
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt
public import CFSG.GH74.Uniqueness.SU.SU0GH

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74
open CFSG.ComponentClassification.OuterAutomorphisms (Outer perfect_action_inner)

section Act

variable {Y : Type} [Group Y]

@[expose] def actOn (K P : Subgroup Y) (h : ∀ p ∈ P, ∀ x ∈ K, p * x * p⁻¹ ∈ K) : ↥P →* MulAut ↥K where
  toFun p :=
    { toFun := fun x => ⟨(p : Y) * x * (p : Y)⁻¹, h p p.2 x x.2⟩
      invFun := fun x => ⟨(p : Y)⁻¹ * x * (p : Y), by simpa using h (p : Y)⁻¹ (P.inv_mem p.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext x; simp
  map_mul' := fun p q => by ext x; simp [mul_assoc]

theorem exists_inner_of_perfect {K P : Subgroup Y} (hK : Group.IsSolvable (Outer ↥K)) (hP : ⁅P, P⁆ = P)
    (h : ∀ p ∈ P, ∀ x ∈ K, p * x * p⁻¹ ∈ K) {p : Y} (hp : p ∈ P) :
    ∃ a ∈ K, ∀ x ∈ K, p * x * p⁻¹ = a * x * a⁻¹ := by
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  obtain ⟨a, ha⟩ := perfect_action_inner (actOn K P h) ⟨p, hp⟩
  refine ⟨a, a.2, fun x hx => ?_⟩
  have := congrArg (fun σ : MulAut ↥K => ((σ ⟨x, hx⟩ : ↥K) : Y)) ha
  simpa [actOn] using this

end Act

section Perm

variable {Y : Type} [Group Y]

theorem isComponent_conj (g : Y) {K : Subgroup Y} (hK : IsComponent K) :
    IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

theorem map_conj_mul (g h : Y) (K : Subgroup Y) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (K : Subgroup Y) : K.map (MulAut.conj (1 : Y)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

@[expose] noncomputable def compPerm (Y : Type) [Group Y] :
    Y →* Equiv.Perm {K : Subgroup Y // IsComponent K} where
  toFun g :=
    { toFun := fun K => ⟨K.1.map (MulAut.conj g).toMonoidHom, isComponent_conj g K.2⟩
      invFun := fun K => ⟨K.1.map (MulAut.conj g⁻¹).toMonoidHom, isComponent_conj g⁻¹ K.2⟩
      left_inv := fun K => Subtype.ext (by
        change (K.1.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K.1
        rw [map_conj_mul, inv_mul_cancel, map_conj_one])
      right_inv := fun K => Subtype.ext (by
        change (K.1.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K.1
        rw [map_conj_mul, mul_inv_cancel, map_conj_one]) }
  map_one' := Equiv.ext fun K => Subtype.ext (map_conj_one K.1)
  map_mul' := fun g h => Equiv.ext fun K => Subtype.ext (map_conj_mul g h K.1).symm

theorem perfect_normalizes_component [Finite Y]
    (hcard : Nat.card {K : Subgroup Y // IsComponent K} ≤ 4) {P : Subgroup Y} (hP : ⁅P, P⁆ = P)
    {K : Subgroup Y} (hK : IsComponent K) : ∀ p ∈ P, ∀ x ∈ K, p * x * p⁻¹ ∈ K := by
  have : Finite {K : Subgroup Y // IsComponent K} := inferInstance
  have hsolv : Group.IsSolvable (Equiv.Perm {K : Subgroup Y // IsComponent K}) :=
    Equiv.Perm.isSolvable hcard
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  have h1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    ((compPerm Y).comp P.subtype)
  intro p hp x hx
  have h2 : compPerm Y p = 1 := by
    have := congrArg (fun f : ↥P →* Equiv.Perm {K : Subgroup Y // IsComponent K} => f ⟨p, hp⟩) h1
    simpa using this
  have h3 : (compPerm Y p ⟨K, hK⟩).1 = K := by
    rw [h2]
    rfl
  have h4 : p * x * p⁻¹ ∈ (compPerm Y p ⟨K, hK⟩).1 := by
    change _ ∈ K.map (MulAut.conj p).toMonoidHom
    exact Subgroup.mem_map.2 ⟨x, hx, by simp⟩
  rwa [h3] at h4

end Perm

section Layer

variable {Y : Type} [Group Y] [Finite Y]

theorem outer_solvable_of_component (hSch : GHSchreier) (hGH : Uniqueness.SU.SU0.GHGroup Y)
    (hF : fittingSubgroup Y = ⊥) {K : Subgroup Y} (hK : IsComponent K) :
    Group.IsSolvable (Outer ↥K) := by
  obtain ⟨hs, hn⟩ := component_isSimple hF hK
  have hl : GHList ↥K :=
    Uniqueness.SU.SU0.GHGroup.ghList_of_surjection hGH (A := K) (f := MonoidHom.id ↥K)
      Function.surjective_id hs hn
  exact hSch ↥K hs hn hl

theorem perfect_le_of_unique (hF : fittingSubgroup Y = ⊥) {K : Subgroup Y} (hK : IsComponent K)
    (hall : ∀ L : Subgroup Y, IsComponent L → L = K) (hO : Group.IsSolvable (Outer ↥K))
    {P : Subgroup Y} (hP : ⁅P, P⁆ = P) : P ≤ K := by
  have hFK : generalizedFitting Y = K := by
    rw [generalizedFitting_eq_layer hF]
    exact le_antisymm (sSup_le fun L hL => (hall L hL).le) (CFSG.LocalCores.component_le_layer hK)
  have hnorm : ∀ p ∈ P, ∀ x ∈ K, p * x * p⁻¹ ∈ K := by
    intro p _ x hx
    have h1 := isComponent_conj p hK
    have h2 := hall _ h1
    have : p * x * p⁻¹ ∈ K.map (MulAut.conj p).toMonoidHom := Subgroup.mem_map.2 ⟨x, hx, by simp⟩
    rwa [h2] at this
  intro p hp
  obtain ⟨a, ha, hax⟩ := exists_inner_of_perfect hO hP hnorm hp
  have hcen : a⁻¹ * p ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hax x hx
    calc x * (a⁻¹ * p) = a⁻¹ * (a * x * a⁻¹) * p := by group
      _ = a⁻¹ * (p * x * p⁻¹) * p := by rw [h1]
      _ = a⁻¹ * p * x := by group
  have hmem : a⁻¹ * p ∈ K := by
    have := centralizer_generalizedFitting_le Y
    rw [hFK] at this
    exact this hcen
  have : a * (a⁻¹ * p) ∈ K := K.mul_mem ha hmem
  simpa using this

theorem perfect_le_sup_of_two (hF : fittingSubgroup Y = ⊥) {A B : Subgroup Y} (hA : IsComponent A)
    (hB : IsComponent B) (hAB : A ≠ B) (hall : ∀ K : Subgroup Y, IsComponent K → K = A ∨ K = B)
    (hOA : Group.IsSolvable (Outer ↥A)) (hOB : Group.IsSolvable (Outer ↥B))
    {P : Subgroup Y} (hP : ⁅P, P⁆ = P) : P ≤ A ⊔ B := by
  classical
  have hcard : Nat.card {K : Subgroup Y // IsComponent K} ≤ 4 := by
    have hinj : Function.Injective (fun K : {K : Subgroup Y // IsComponent K} => decide (K.1 = A)) := by
      intro K K' h
      simp only [decide_eq_decide] at h
      apply Subtype.ext
      rcases hall K.1 K.2 with h1 | h1 <;> rcases hall K'.1 K'.2 with h2 | h2
      · rw [h1, h2]
      · exact absurd ((h.1 h1).symm.trans h2) hAB
      · exact absurd ((h.2 h2).symm.trans h1) hAB
      · rw [h1, h2]
    calc Nat.card {K : Subgroup Y // IsComponent K} ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
      _ ≤ 4 := by norm_num
  have hPA := perfect_normalizes_component hcard hP hA
  have hPB := perfect_normalizes_component hcard hP hB
  obtain ⟨hcomm, -⟩ := components_commute_inf hF hA hB hAB
  have hFstar : generalizedFitting Y = A ⊔ B := by
    rw [generalizedFitting_eq_layer hF]
    refine le_antisymm (sSup_le fun K hK => ?_) (sup_le (CFSG.LocalCores.component_le_layer hA)
      (CFSG.LocalCores.component_le_layer hB))
    rcases hall K hK with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  intro p hp
  obtain ⟨a, ha, hax⟩ := exists_inner_of_perfect hOA hP hPA hp
  obtain ⟨b, hb, hby⟩ := exists_inner_of_perfect hOB hP hPB hp
  have hcx : ∀ x ∈ A, (b⁻¹ * a⁻¹ * p) * x * (b⁻¹ * a⁻¹ * p)⁻¹ = x := by
    intro x hx
    have h1 := hax x hx
    have h2 : x * b = b * x := hcomm x hx b hb
    calc (b⁻¹ * a⁻¹ * p) * x * (b⁻¹ * a⁻¹ * p)⁻¹ = b⁻¹ * a⁻¹ * (p * x * p⁻¹) * a * b := by group
      _ = b⁻¹ * a⁻¹ * (a * x * a⁻¹) * a * b := by rw [h1]
      _ = b⁻¹ * (x * b) := by group
      _ = x := by rw [h2]; group
  have hcy : ∀ y ∈ B, (b⁻¹ * a⁻¹ * p) * y * (b⁻¹ * a⁻¹ * p)⁻¹ = y := by
    intro y hy
    have h1 := hby y hy
    have hw : b * y * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hy) (B.inv_mem hb)
    have h2 : (b * y * b⁻¹) * a = a * (b * y * b⁻¹) := (hcomm a ha _ hw).symm
    calc (b⁻¹ * a⁻¹ * p) * y * (b⁻¹ * a⁻¹ * p)⁻¹ = b⁻¹ * a⁻¹ * (p * y * p⁻¹) * a * b := by group
      _ = b⁻¹ * a⁻¹ * (b * y * b⁻¹) * a * b := by rw [h1]
      _ = b⁻¹ * (a⁻¹ * ((b * y * b⁻¹) * a)) * b := by group
      _ = b⁻¹ * (a⁻¹ * (a * (b * y * b⁻¹))) * b := by rw [h2]
      _ = y := by group
  have hcen : b⁻¹ * a⁻¹ * p ∈ Subgroup.centralizer ((A ⊔ B : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute' hcomm hg
    have e1 := hcx x hx
    have e2 := hcy y hy
    have : (b⁻¹ * a⁻¹ * p) * (x * y) * (b⁻¹ * a⁻¹ * p)⁻¹ = x * y := by
      calc (b⁻¹ * a⁻¹ * p) * (x * y) * (b⁻¹ * a⁻¹ * p)⁻¹
          = ((b⁻¹ * a⁻¹ * p) * x * (b⁻¹ * a⁻¹ * p)⁻¹) * ((b⁻¹ * a⁻¹ * p) * y * (b⁻¹ * a⁻¹ * p)⁻¹) := by
            group
        _ = x * y := by rw [e1, e2]
    exact mul_inv_eq_iff_eq_mul.1 this |>.symm
  have hmem : b⁻¹ * a⁻¹ * p ∈ A ⊔ B := by
    have := centralizer_generalizedFitting_le Y
    rw [hFstar] at this
    exact this hcen
  have : a * b * (b⁻¹ * a⁻¹ * p) ∈ A ⊔ B :=
    (A ⊔ B).mul_mem ((A ⊔ B).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)) hmem
  simpa [mul_assoc] using this

end Layer

end CFSG.GH74.GLS.Stage2.Local.P34
