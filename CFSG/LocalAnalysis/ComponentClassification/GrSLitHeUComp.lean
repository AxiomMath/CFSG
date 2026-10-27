module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

namespace HeUC

theorem commute_of_commutator_central {X : Type*} [Group X] {M : Subgroup X}
    (hM : commutator ↥M = ⊤) {x : X} (hxM : x ∈ normalizer (M : Set X))
    (hc : ∀ m ∈ M, ∀ n ∈ M, x * m * x⁻¹ * m⁻¹ * n = n * (x * m * x⁻¹ * m⁻¹)) :
    ∀ m ∈ M, x * m = m * x := by
  have hmem : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ M := fun m hm =>
    mul_mem ((mem_normalizer_iff.mp hxM m).mp hm) (inv_mem hm)
  let φ : ↥M →* ↥M :=
    { toFun := fun m => ⟨x * m * x⁻¹ * (m : X)⁻¹, hmem m m.2⟩
      map_one' := by ext; simp
      map_mul' := fun m₁ m₂ => by
        ext
        simp only [coe_mul]
        have h2 := hc m₂ m₂.2 _ (inv_mem m₁.2)
        calc x * ((m₁ : X) * m₂) * x⁻¹ * ((m₁ : X) * m₂)⁻¹
            = x * m₁ * x⁻¹ * ((x * m₂ * x⁻¹ * (m₂ : X)⁻¹) * (m₁ : X)⁻¹) := by group
          _ = x * m₁ * x⁻¹ * ((m₁ : X)⁻¹ * (x * m₂ * x⁻¹ * (m₂ : X)⁻¹)) := by rw [h2]
          _ = x * m₁ * x⁻¹ * (m₁ : X)⁻¹ * (x * m₂ * x⁻¹ * (m₂ : X)⁻¹) := by group }
  have hrange : φ.range ≤ center ↥M := by
    rintro _ ⟨m, rfl⟩
    rw [mem_center_iff]
    intro n
    exact Subtype.ext (hc m m.2 n n.2).symm
  have h1 : (commutator ↥M).map φ = ⊥ := by
    rw [map_commutator_eq, commutator_eq_bot_iff_le_centralizer]
    exact hrange.trans (center_le_centralizer _)
  rw [hM, ← MonoidHom.range_eq_map] at h1
  intro m hm
  have hφ : φ ⟨m, hm⟩ = 1 := by
    have : φ ⟨m, hm⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [h1] at this
    exact this
  have h3 : x * m * x⁻¹ * m⁻¹ = 1 := congrArg Subtype.val hφ
  calc x * m = x * m * x⁻¹ * m⁻¹ * (m * x) := by group
    _ = m * x := by rw [h3, one_mul]

theorem isComponent_of_central {X : Type} [Group X] [Finite X] {C M : Subgroup X} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C))
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) :
    IsComponent (M.subgroupOf C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : oddIn M ≤ (center ↥M).map M.subtype := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact (hc _ ⟨y, hy, rfl⟩ _ g.2).symm
  have hq : IsQuasisimple ↥M := GrS5.isQuasisimple_of_oddIn_le_center hMC hM hO
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMC).symm hq,
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M C hMC).1 hM).1⟩

theorem commute_of_le_sup {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : ∀ a ∈ A, x * a = a * x) (hB : ∀ b ∈ B, x * b = b * x) {y : G} (hy : y ∈ A ⊔ B) :
    x * y = y * x := by
  have h : A ⊔ B ≤ centralizer ({x} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.mpr (hA a ha).symm)
    (fun b hb => mem_centralizer_singleton_iff.mpr (hB b hb).symm)
  exact (mem_centralizer_singleton_iff.mp (h hy)).symm

theorem le_pCore_of_components {H : Type*} [Group H] [Finite H] {J₁ J₂ V : Subgroup H}
    (h₁ : IsComponent J₁) (h₂ : IsComponent J₂) (hV : IsPGroup 2 V) (hVJ : V ≤ J₁ ⊔ J₂)
    (hc₁ : ∀ v ∈ V, ∀ j ∈ J₁, v * j = j * v) (hc₂ : ∀ v ∈ V, ∀ j ∈ J₂, v * j = j * v) :
    V ≤ pCore 2 H := by
  classical
  set cj : H → Subgroup H → Subgroup H := fun c J => J.map (MulAut.conj c).toMonoidHom
    with hcj
  have hmemc : ∀ c x (J : Subgroup H), x ∈ J → c * x * c⁻¹ ∈ cj c J := fun c x J hx =>
    ⟨x, hx, rfl⟩
  have hdata : ∀ c : H, ∀ y : H, y ∈ cj c V →
      y ∈ cj c J₁ ⊔ cj c J₂ ∧ (∀ j ∈ cj c J₁, y * j = j * y) ∧
        ∀ j ∈ cj c J₂, y * j = j * y := by
    rintro c _ ⟨v, hv, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have h := map_mono (f := (MulAut.conj c).toMonoidHom) hVJ
      rw [Subgroup.map_sup] at h
      exact h ⟨v, hv, rfl⟩
    · rintro _ ⟨j, hj, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c * v * c⁻¹ * (c * j * c⁻¹) = c * (v * j) * c⁻¹ := by group
        _ = c * (j * v) * c⁻¹ := by rw [hc₁ v hv j hj]
        _ = c * j * c⁻¹ * (c * v * c⁻¹) := by group
    · rintro _ ⟨j, hj, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c * v * c⁻¹ * (c * j * c⁻¹) = c * (v * j) * c⁻¹ := by group
        _ = c * (j * v) * c⁻¹ := by rw [hc₂ v hv j hj]
        _ = c * j * c⁻¹ * (c * v * c⁻¹) := by group
  have hcomp : ∀ (c : H) (J : Subgroup H), IsComponent J → IsComponent (cj c J) :=
    fun c J hJ => LocalCores.isComponent_map_mulEquiv (MulAut.conj c) hJ
  have hcent : ∀ c d : H, ∀ x ∈ cj c V, ∀ J : Subgroup H, (J = cj d J₁ ∨ J = cj d J₂) →
      ∀ j ∈ J, x * j = j * x := by
    intro c d x hx J hJ j hj
    obtain ⟨-, hx₁, hx₂⟩ := hdata c x hx
    have hJc : IsComponent J := by
      rcases hJ with rfl | rfl
      · exact hcomp d J₁ h₁
      · exact hcomp d J₂ h₂
    by_cases hJ₁ : J = cj c J₁
    · exact hx₁ j (hJ₁ ▸ hj)
    by_cases hJ₂ : J = cj c J₂
    · exact hx₂ j (hJ₂ ▸ hj)
    have hcomm : ∀ (K : Subgroup H), IsComponent K → J ≠ K → ∀ k ∈ K, j * k = k * j := by
      intro K hK hne k hk
      rcases LocalCores.distinct_components_commute hJc hK with h | h
      · exact absurd h hne
      · have hmem : j * k * j⁻¹ * k⁻¹ ∈ ⁅J, K⁆ := commutator_mem_commutator hj hk
        rw [h, mem_bot] at hmem
        calc j * k = j * k * j⁻¹ * k⁻¹ * (k * j) := by group
          _ = k * j := by rw [hmem, one_mul]
    exact (commute_of_le_sup (hcomm _ (hcomp c J₁ h₁) hJ₁) (hcomm _ (hcomp c J₂ h₂) hJ₂)
      (hdata c x hx).1).symm
  have hpair : ∀ c d : H, ∀ x ∈ cj c V, ∀ y ∈ cj d V, x * y = y * x := by
    intro c d x hx y hy
    exact commute_of_le_sup (hcent c d x hx _ (Or.inl rfl)) (hcent c d x hx _ (Or.inr rfl))
      (hdata d y hy).1
  set S : Set H := Group.conjugatesOfSet (V : Set H) with hS
  have hSmem : ∀ s ∈ S, ∃ c : H, s ∈ cj c V := by
    intro s hs
    obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hs
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    exact ⟨c, hmemc c v V hv⟩
  have hSc : S.Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨c, hc⟩ := hSmem x hx
    obtain ⟨d, hd⟩ := hSmem y hy
    exact hpair c d x hc y hd
  have hcommN := Subgroup.isMulCommutative_closure hSc
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have hSpow : ∀ s ∈ S, s ^ (2 ^ k) = 1 := by
    intro s hs
    obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hs
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    have hv1 : v ^ (2 ^ k) = 1 := by
      have h := pow_card_eq_one' (G := ↥V) (x := ⟨v, hv⟩)
      rw [hk] at h
      exact congrArg Subtype.val h
    rw [conj_pow, hv1, mul_one, mul_inv_cancel]
  set N : Subgroup H := closure S with hN
  have hNpow : ∀ x ∈ N, x ^ (2 ^ k) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hSpow x hx
    | one => exact one_pow _
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := by
        have h := hcommN.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val h
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hNp : IsPGroup 2 N := fun x => ⟨k, Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hNpow x x.2)⟩
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hVN : V ≤ N := fun v hv => Subgroup.subset_normalClosure hv
  exact hVN.trans (le_sSup (s := {K : Subgroup H | K.Normal ∧ IsPGroup 2 K}) ⟨hNn, hNp⟩)

theorem le_pCore_map {X : Type*} [Group X] [Finite X] {C M₁ M₂ U : Subgroup X} (h₁C : M₁ ≤ C)
    (h₁ : IsComponent (M₁.subgroupOf C)) (h₂C : M₂ ≤ C) (h₂ : IsComponent (M₂.subgroupOf C))
    (hU : IsPGroup 2 U) (hUM : U ≤ M₁ ⊔ M₂) (hc₁ : ∀ v ∈ U, ∀ m ∈ M₁, v * m = m * v)
    (hc₂ : ∀ v ∈ U, ∀ m ∈ M₂, v * m = m * v) : U ≤ (pCore 2 ↥C).map C.subtype := by
  have hUC : U ≤ C := hUM.trans (sup_le h₁C h₂C)
  have hU' : IsPGroup 2 ↥(U.subgroupOf C) := hU.comap_of_injective C.subtype C.subtype_injective
  have hUM' : U.subgroupOf C ≤ M₁.subgroupOf C ⊔ M₂.subgroupOf C := by
    rw [← subgroupOf_sup h₁C h₂C]
    exact fun x hx => hUM hx
  have h := le_pCore_of_components h₁ h₂ hU' hUM'
    (fun v hv j hj => Subtype.ext (hc₁ _ hv _ hj)) (fun v hv j hj => Subtype.ext (hc₂ _ hv _ hj))
  intro u hu
  exact ⟨⟨u, hUC hu⟩, h hu, rfl⟩

end HeUC

end CFSG.ComponentClassification.GrSLit
