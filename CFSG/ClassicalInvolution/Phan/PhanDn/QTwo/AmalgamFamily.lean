module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SUFour
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.StandardType.QTwo
open CFSG.StandardType.QTwo.SixPoint CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {n : ℕ} {M : CoxeterMatrix (Fin n)}
variable {X : Type} [Group X] {Y : Type} [Group Y]

theorem QTwoPhanFamily.le_levi_node (S : QTwoPhanFamily K M X) {C : Set (Fin n)} {i : Fin n}
    (hi : i ∈ C) : (S.ι i).range ≤ S.levi C := by
  rw [QTwoPhanFamily.levi]
  refine le_trans ?_ le_sup_left
  apply le_iSup_of_le (f := fun i => ⨆ (_ : i ∈ C), (S.ι i).range) (i := i)
  apply le_iSup_of_le (f := fun _ : i ∈ C => (S.ι i).range) (i := hi)
  exact le_rfl

theorem QTwoPhanFamily.le_levi_edge (S : QTwoPhanFamily K M X) {C : Set (Fin n)} {i j : Fin n}
    (hi : i ∈ C) (hj : j ∈ C) (h3 : M i j = 3) : (S.θ i j).range ≤ S.levi C := by
  rw [QTwoPhanFamily.levi]
  refine le_trans ?_ le_sup_right
  apply le_iSup_of_le (f := fun i => ⨆ (_ : i ∈ C),
    ⨆ (j : Fin n), ⨆ (_ : j ∈ C), ⨆ (_ : M i j = 3), (S.θ i j).range) (i := i)
  apply le_iSup_of_le (f := fun _ : i ∈ C =>
    ⨆ (j : Fin n), ⨆ (_ : j ∈ C), ⨆ (_ : M i j = 3), (S.θ i j).range) (i := hi)
  apply le_iSup_of_le (f := fun j => ⨆ (_ : j ∈ C),
    ⨆ (_ : M i j = 3), (S.θ i j).range) (i := j)
  apply le_iSup_of_le (f := fun _ : j ∈ C =>
    ⨆ (_ : M i j = 3), (S.θ i j).range) (i := hj)
  apply le_iSup_of_le (f := fun _ : M i j = 3 => (S.θ i j).range) (i := h3)
  exact le_rfl

private theorem mem_range_self {G H : Type} [Group G] [Group H] (f : G →* H) (a : G) :
    f a ∈ f.range :=
  (MonoidHom.mem_range (f := f)).mpr ⟨a, rfl⟩

theorem QTwoPhanFamily.mem_levi_node (S : QTwoPhanFamily K M X) {C : Set (Fin n)} {i : Fin n}
    (hi : i ∈ C) (a : Su K 2 1 2) : S.ι i a ∈ S.levi C :=
  S.le_levi_node hi (mem_range_self (S.ι i) a)

theorem QTwoPhanFamily.mem_levi_edge (S : QTwoPhanFamily K M X) {C : Set (Fin n)} {i j : Fin n}
    (hi : i ∈ C) (hj : j ∈ C) (h3 : M i j = 3) (b : Su K 2 1 3) :
    S.θ i j b ∈ S.levi C :=
  S.le_levi_edge hi hj h3 (mem_range_self (S.θ i j) b)

private noncomputable def leviGen (S : QTwoPhanFamily K M X) (C : Set (Fin n)) :
    ({i : Fin n // i ∈ C} ⊕
      {p : Fin n × Fin n // p.1 ∈ C ∧ p.2 ∈ C ∧ M p.1 p.2 = 3}) → Subgroup X
  | Sum.inl ⟨i, _⟩ => (S.ι i).range
  | Sum.inr ⟨⟨i, j⟩, ⟨_, _, _⟩⟩ => (S.θ i j).range

private theorem levi_eq_iSup_gen (S : QTwoPhanFamily K M X) (C : Set (Fin n)) :
    S.levi C = ⨆ g, leviGen S C g := by
  rw [QTwoPhanFamily.levi]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · refine iSup_le fun i => iSup_le fun hi => ?_
      exact le_iSup_of_le (Sum.inl ⟨i, hi⟩) le_rfl
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
        iSup_le fun h3 => ?_
      exact le_iSup_of_le (Sum.inr ⟨⟨i, j⟩, ⟨hi, hj, h3⟩⟩) le_rfl
  · refine iSup_le fun g => ?_
    rcases g with ⟨i, hi⟩ | ⟨⟨i, j⟩, ⟨hi, hj, h3⟩⟩
    · refine le_sup_of_le_left ?_
      apply le_iSup_of_le (f := fun i => ⨆ (_ : i ∈ C), (S.ι i).range) (i := i)
      apply le_iSup_of_le (f := fun _ : i ∈ C => (S.ι i).range) (i := hi)
      exact le_rfl
    · refine le_sup_of_le_right ?_
      apply le_iSup_of_le (f := fun i => ⨆ (_ : i ∈ C),
        ⨆ (j : Fin n), ⨆ (_ : j ∈ C), ⨆ (_ : M i j = 3), (S.θ i j).range) (i := i)
      apply le_iSup_of_le (f := fun _ : i ∈ C =>
        ⨆ (j : Fin n), ⨆ (_ : j ∈ C), ⨆ (_ : M i j = 3), (S.θ i j).range) (i := hi)
      apply le_iSup_of_le (f := fun j => ⨆ (_ : j ∈ C),
        ⨆ (_ : M i j = 3), (S.θ i j).range) (i := j)
      apply le_iSup_of_le (f := fun _ : j ∈ C =>
        ⨆ (_ : M i j = 3), (S.θ i j).range) (i := hj)
      apply le_iSup_of_le (f := fun _ : M i j = 3 => (S.θ i j).range) (i := h3)
      exact le_rfl

private theorem levi_induction (S : QTwoPhanFamily K M X) {C : Set (Fin n)}
    {P : X → Prop} {x : X} (hx : x ∈ S.levi C)
    (hι : ∀ i, i ∈ C → ∀ a, P (S.ι i a))
    (hθ : ∀ i j, i ∈ C → j ∈ C → M i j = 3 → ∀ b, P (S.θ i j b))
    (h1 : P 1) (hmul : ∀ x y, P x → P y → P (x * y)) : P x := by
  rw [levi_eq_iSup_gen] at hx
  refine Subgroup.iSup_induction (S := leviGen S C) (C := P) hx ?_ h1 hmul
  rintro g x hx
  rcases g with ⟨i, hi⟩ | ⟨⟨i, j⟩, ⟨hi, hj, h3⟩⟩
  · rcases hx with ⟨a, rfl⟩
    exact hι i hi a
  · rcases hx with ⟨b, rfl⟩
    exact hθ i j hi hj h3 b

private theorem levi_induction' (S : QTwoPhanFamily K M X) {C : Set (Fin n)}
    {P : ∀ x : X, x ∈ S.levi C → Prop} {x : X} (hx : x ∈ S.levi C)
    (hι : ∀ i (_hi : i ∈ C) a (hmem : S.ι i a ∈ S.levi C), P (S.ι i a) hmem)
    (hθ : ∀ i j (_hi : i ∈ C) (_hj : j ∈ C) (_h3 : M i j = 3) b
      (hmem : S.θ i j b ∈ S.levi C), P (S.θ i j b) hmem)
    (h1 : P 1 (one_mem _))
    (hmul : ∀ x y (hx : x ∈ S.levi C) (hy : y ∈ S.levi C),
      P x hx → P y hy → P (x * y) (mul_mem hx hy)) :
    P x hx := by
  have hx' : x ∈ ⨆ g, leviGen S C g := by
    rwa [← levi_eq_iSup_gen]
  refine Subgroup.iSup_induction' (S := leviGen S C)
    (C := fun z hz => P z (by rw [levi_eq_iSup_gen]; exact hz)) ?_ ?_ ?_ hx'
  · rintro g z hz
    rcases g with ⟨i, hi⟩ | ⟨⟨i, j⟩, ⟨hi, hj, h3⟩⟩
    · rcases hz with ⟨a, rfl⟩
      exact hι i hi a _
    · rcases hz with ⟨b, rfl⟩
      exact hθ i j hi hj h3 b _
  · exact h1
  · intro x y hx hy hxP hyP
    exact hmul x y _ _ hxP hyP

private theorem levi_singleton (S : QTwoPhanFamily K M X) (i : Fin n) :
    S.levi ({i} : Set (Fin n)) = (S.ι i).range := by
  simp [QTwoPhanFamily.levi]

private theorem mem_pair_edge_cases {i j a b : Fin n} (_h3 : M i j = 3)
    (ha : a ∈ ({i, j} : Set (Fin n))) (hb : b ∈ ({i, j} : Set (Fin n)))
    (hab : M a b = 3) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exfalso
    rw [ha, hb, M.diagonal] at hab
    omega
  · left; exact ⟨ha, hb⟩
  · right; exact ⟨ha, hb⟩
  · exfalso
    rw [ha, hb, M.diagonal] at hab
    omega

private theorem levi_pair (S : QTwoPhanFamily K M X) {i j : Fin n} (h3 : M i j = 3) :
    S.levi ({i, j} : Set (Fin n)) = (S.θ i j).range := by
  apply le_antisymm
  · rw [QTwoPhanFamily.levi]
    refine sup_le ?_ ?_
    · refine iSup_le fun a => iSup_le fun ha => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha, ← S.left i j h3, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
      · rw [ha, ← S.right i j h3, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
    · refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb =>
        iSup_le fun hab => ?_
      rcases mem_pair_edge_cases (M := M) h3 ha hb hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb]
      · rw [ha, hb, S.rev i j h3, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
  · exact S.le_levi_edge (by simp) (by simp) h3

private theorem levi_union (S : QTwoPhanFamily K M X) {C₁ C₂ : Set (Fin n)}
    (hcross : ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2) :
    S.levi (C₁ ∪ C₂) = S.levi C₁ ⊔ S.levi C₂ := by
  apply le_antisymm
  · rw [QTwoPhanFamily.levi]
    refine sup_le ?_ ?_
    · refine iSup_le fun i => iSup_le fun hi => ?_
      rw [Set.mem_union] at hi
      rcases hi with hi | hi
      · exact (S.le_levi_node hi).trans le_sup_left
      · exact (S.le_levi_node hi).trans le_sup_right
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
        iSup_le fun h3 => ?_
      rw [Set.mem_union] at hi hj
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (S.le_levi_edge hi hj h3).trans le_sup_left
      · exfalso
        have h2 := hcross i hi j hj
        rw [h3] at h2
        omega
      · exfalso
        have h2 := hcross j hj i hi
        rw [M.symmetric j i, h3] at h2
        omega
      · exact (S.le_levi_edge hi hj h3).trans le_sup_right
  · exact sup_le (S.levi_mono Set.subset_union_left) (S.levi_mono Set.subset_union_right)

private theorem levi_commute (F : QTwoPhanFamily K M Y) {C₁ C₂ : Set (Fin n)}
    (hcross : ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2) :
    ∀ x ∈ F.levi C₁, ∀ y ∈ F.levi C₂, x * y = y * x := by
  intro x hx y hy
  have hxA : x ∈ Subgroup.centralizer (F.levi C₂ : Set Y) := by
    refine levi_induction F hx (P := fun x =>
      x ∈ Subgroup.centralizer (F.levi C₂ : Set Y)) ?_ ?_ ?_ ?_
    · intro i hi a
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      refine levi_induction F hz (P := fun z => z * F.ι i a = F.ι i a * z) ?_ ?_ ?_ ?_
      · intro j hj b
        exact (F.comm i j (hcross i hi j hj) a b).symm
      · intro j l hj hl h3 b
        exact (F.farNodeEdge i j l h3 (hcross i hi j hj) (hcross i hi l hl) a b).symm
      · simp
      · intro u v hu hv
        calc (u * v) * F.ι i a = u * (v * F.ι i a) := by group
          _ = u * (F.ι i a * v) := by rw [hv]
          _ = (u * F.ι i a) * v := by group
          _ = (F.ι i a * u) * v := by rw [hu]
          _ = F.ι i a * (u * v) := by group
    · intro i l hi hl h3 a
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      refine levi_induction F hz (P := fun z => z * F.θ i l a = F.θ i l a * z) ?_ ?_ ?_ ?_
      · intro j hj b
        refine F.farNodeEdge j i l h3 ?_ ?_ b a
        · rw [M.symmetric j i]
          exact hcross i hi j hj
        · rw [M.symmetric j l]
          exact hcross l hl j hj
      · intro j m hj hm h3' b
        exact (F.farEdgeEdge i l j m h3 h3' (hcross i hi j hj) (hcross i hi m hm)
          (hcross l hl j hj) (hcross l hl m hm) a b).symm
      · simp
      · intro u v hu hv
        calc (u * v) * F.θ i l a = u * (v * F.θ i l a) := by group
          _ = u * (F.θ i l a * v) := by rw [hv]
          _ = (u * F.θ i l a) * v := by group
          _ = (F.θ i l a * u) * v := by rw [hu]
          _ = F.θ i l a * (u * v) := by group
    · simp
    · intro u v hu hv
      exact Subgroup.mul_mem _ hu hv
  exact (Subgroup.mem_centralizer_iff.mp hxA y hy).symm

private theorem mem_sup_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : A ≤ Subgroup.centralizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let H : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        have hc : (b1 : G) * a2 = a2 * b1 :=
          (Subgroup.mem_centralizer_iff.mp (hcomm ha2)) b1 hb1
        calc (a1 * a2) * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
          _ = a1 * (b1 * a2) * b2 := by rw [← hc]
          _ = (a1 * b1) * (a2 * b2) := by group
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : (a : G) * b = b * a :=
          ((Subgroup.mem_centralizer_iff.mp (hcomm ha)) b hb).symm
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [hc] }
  have hA : A ≤ H := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hB : B ≤ H := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact sup_le hA hB hx

private noncomputable def mulEquiv_prod_sup {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : A ≤ Subgroup.centralizer (B : Set G)) (hdis : Disjoint A B) :
    ↥A × ↥B ≃* ↥(A ⊔ B) := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        rintro ⟨a1, b1⟩ ⟨a2, b2⟩
        apply Subtype.ext
        change ((a1 : G) * (a2 : G)) * ((b1 : G) * (b2 : G)) =
          ((a1 : G) * (b1 : G)) * ((a2 : G) * (b2 : G))
        have hc : (b1 : G) * (a2 : G) = (a2 : G) * (b1 : G) :=
          (Subgroup.mem_centralizer_iff.mp (hcomm a2.2)) b1 b1.2
        calc ((a1 : G) * a2) * (b1 * b2)
            = (a1 : G) * (a2 * b1) * b2 := by group
          _ = (a1 : G) * (b1 * a2) * b2 := by rw [← hc]
          _ = ((a1 : G) * b1) * (a2 * b2) := by group }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    have hG : ((p.1 : G) * p.2) = ((q.1 : G) * q.2) :=
      congrArg (fun z : ↥(A ⊔ B) => (z : G)) hpq
    exact Subgroup.mul_injective_of_disjoint hdis hG
  · intro y
    rcases mem_sup_of_commute hcomm y.2 with ⟨a, ha, b, hb, hab⟩
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    exact hab

private theorem split_single_pair {a b c : Fin n}
    (hab : M a b = 2) (hac : M a c = 2) :
    ∃ C₁ C₂ : Set (Fin n), C₁.Nonempty ∧ C₂.Nonempty ∧ Disjoint C₁ C₂ ∧
      ({a, b, c} : Set (Fin n)) = C₁ ∪ C₂ ∧ ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2 := by
  have hab_ne : a ≠ b := by
    rintro rfl
    rw [M.diagonal] at hab
    omega
  have hac_ne : a ≠ c := by
    rintro rfl
    rw [M.diagonal] at hac
    omega
  refine ⟨{a}, {b, c}, ⟨a, by simp⟩, ⟨b, by simp⟩, ?_, ?_, ?_⟩
  · rw [Set.disjoint_singleton_left]
    simp [hab_ne, hac_ne]
  · ext w
    simp [or_comm, or_left_comm]
  · intro i hi j hj
    rw [Set.mem_singleton_iff] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    subst hi
    rcases hj with rfl | rfl
    · exact hab
    · exact hac

private theorem three_set_cases (hlab : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3)
    (htri : ∀ i j k, M i j = 3 → M j k = 3 → M i k ≠ 3)
    {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∃ i j k, M i j = 3 ∧ M j k = 3 ∧ M i k = 2 ∧
      ({x, y, z} : Set (Fin n)) = {i, j, k}) ∨
      ∃ C₁ C₂ : Set (Fin n), C₁.Nonempty ∧ C₂.Nonempty ∧ Disjoint C₁ C₂ ∧
        ({x, y, z} : Set (Fin n)) = C₁ ∪ C₂ ∧ ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2 := by
  by_cases hxy3 : M x y = 3
  · by_cases hyz3 : M y z = 3
    · left
      have hxz2 : M x z = 2 := by
        rcases hlab x z hxz with h2 | h3
        · exact h2
        · exact absurd h3 (htri x y z hxy3 hyz3)
      exact ⟨x, y, z, hxy3, hyz3, hxz2, rfl⟩
    · by_cases hxz3 : M x z = 3
      · left
        have hyz2 : M y z = 2 := by
          rcases hlab y z hyz with h2 | h3
          · exact h2
          · exact absurd h3 hyz3
        exact ⟨y, x, z, by rwa [M.symmetric y x], hxz3, hyz2,
          by ext w; simp [or_left_comm]⟩
      · right
        have hxz2 : M x z = 2 := by
          rcases hlab x z hxz with h2 | h3
          · exact h2
          · exact absurd h3 hxz3
        have hyz2 : M y z = 2 := by
          rcases hlab y z hyz with h2 | h3
          · exact h2
          · exact absurd h3 hyz3
        obtain ⟨C₁, C₂, h1, h2, h3, hC, hcross⟩ :=
          split_single_pair (a := z) (b := x) (c := y)
            (by rwa [M.symmetric z x]) (by rwa [M.symmetric z y])
        refine ⟨C₁, C₂, h1, h2, h3, ?_, hcross⟩
        calc ({x, y, z} : Set (Fin n)) = {z, x, y} := by
              ext w
              simp [or_comm, or_left_comm]
          _ = C₁ ∪ C₂ := hC
  · by_cases hxz3 : M x z = 3
    · by_cases hyz3 : M y z = 3
      · left
        have hxy2 : M x y = 2 := by
          rcases hlab x y hxy with h2 | h3
          · exact h2
          · exact absurd h3 hxy3
        exact ⟨x, z, y, hxz3, by rwa [M.symmetric z y], hxy2, by
          ext w
          constructor
          · rintro (h | h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
          · rintro (h | h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)⟩
      · right
        have hxy2 : M x y = 2 := by
          rcases hlab x y hxy with h2 | h3
          · exact h2
          · exact absurd h3 hxy3
        have hyz2 : M y z = 2 := by
          rcases hlab y z hyz with h2 | h3
          · exact h2
          · exact absurd h3 hyz3
        obtain ⟨C₁, C₂, h1, h2, h3, hC, hcross⟩ :=
          split_single_pair (a := y) (b := x) (c := z)
            (by rwa [M.symmetric y x]) hyz2
        refine ⟨C₁, C₂, h1, h2, h3, ?_, hcross⟩
        calc ({x, y, z} : Set (Fin n)) = {y, x, z} := by
              ext w
              simp [or_left_comm]
          _ = C₁ ∪ C₂ := hC
    · by_cases hyz3 : M y z = 3
      · right
        have hxy2 : M x y = 2 := by
          rcases hlab x y hxy with h2 | h3
          · exact h2
          · exact absurd h3 hxy3
        have hxz2 : M x z = 2 := by
          rcases hlab x z hxz with h2 | h3
          · exact h2
          · exact absurd h3 hxz3
        exact split_single_pair (a := x) (b := y) (c := z) hxy2 hxz2
      · right
        have hxy2 : M x y = 2 := by
          rcases hlab x y hxy with h2 | h3
          · exact h2
          · exact absurd h3 hxy3
        have hxz2 : M x z = 2 := by
          rcases hlab x z hxz with h2 | h3
          · exact h2
          · exact absurd h3 hxz3
        exact split_single_pair (a := x) (b := y) (c := z) hxy2 hxz2

theorem qTwoShape_cases (hlab : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3)
    (htri : ∀ i j k, M i j = 3 → M j k = 3 → M i k ≠ 3)
    {C : Set (Fin n)} (hC : C ∈ qTwoShape M) :
    C = ∅ ∨ (∃ i, C = {i}) ∨ (∃ i j, M i j = 3 ∧ C = {i, j}) ∨
      (∃ i j k, M i j = 3 ∧ M j k = 3 ∧ M i k = 2 ∧ C = {i, j, k}) ∨
      ∃ C₁ C₂, C₁.Nonempty ∧ C₂.Nonempty ∧ Disjoint C₁ C₂ ∧ C = C₁ ∪ C₂ ∧
        ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2 := by
  rcases hC.2 with hsmall | hA
  · have hk : C.ncard = 0 ∨ C.ncard = 1 ∨ C.ncard = 2 ∨ C.ncard = 3 := by omega
    rcases hk with h0 | h1 | h2 | h3
    · exact Or.inl ((Set.ncard_eq_zero (s := C)).mp h0)
    · exact Or.inr (Or.inl ((Set.ncard_eq_one (s := C)).mp h1))
    · obtain ⟨x, y, hxy, rfl⟩ := (Set.ncard_eq_two (s := C)).mp h2
      rcases hlab x y hxy with h2' | h3'
      · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        refine ⟨{x}, {y}, ⟨x, by simp⟩, ⟨y, by simp⟩, ?_, ?_, ?_⟩
        · simpa [Set.disjoint_singleton] using hxy
        · ext w
          simp [or_comm]
        · intro a ha b hb
          rw [Set.mem_singleton_iff] at ha hb
          rw [ha, hb]
          exact h2'
      · exact Or.inr (Or.inr (Or.inl ⟨x, y, h3', rfl⟩))
    · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := (Set.ncard_eq_three (s := C)).mp h3
      rcases three_set_cases hlab htri hxy hxz hyz with
        ⟨i, j, k, hij, hjk, hik, hC⟩ | ⟨C₁, C₂, hne1, hne2, hdisj, hC, hcross⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, hij, hjk, hik, hC⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨C₁, C₂, hne1, hne2, hdisj, hC, hcross⟩)))
  · obtain ⟨i, k, j, l, rfl, hik, hjl, hij, hil, hkj, hkl⟩ := hA
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    refine ⟨{i, k}, {j, l}, ⟨i, by simp⟩, ⟨j, by simp⟩, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro w hw1 hw2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw1 hw2
      rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl
      · rw [M.diagonal] at hij
        omega
      · rw [M.diagonal] at hil
        omega
      · rw [M.diagonal] at hkj
        omega
      · rw [M.diagonal] at hkl
        omega
    · ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hij
      · exact hil
      · exact hkj
      · exact hkl

private theorem blk012_sup_blk123 (hK : Nat.card K = 4) :
    (blk012 K).range ⊔ (blk123 K).range = ⊤ := by
  have h0 : (blk012 K).range =
      coordBlockSU K 2 1 ({0,1,2} : Finset (Fin 4)) := by
    rw [blk012, qTwoSixWin_range (m := 4) (k := 3) (i := 0) (by norm_num)]
    congr 1
  have h1 : (blk123 K).range =
      coordBlockSU K 2 1 ({1,2,3} : Finset (Fin 4)) := by
    rw [blk123, qTwoSixWin_range (m := 4) (k := 3) (i := 1) (by norm_num)]
    congr 1
  rw [h0, h1]
  rw [coordBlockSU_sup_three (K := K) hK
    (A := ({0,1,2} : Finset (Fin 4))) (B := ({1,2,3} : Finset (Fin 4)))
    (by decide) (by decide) (by decide)]
  rw [show (({0,1,2} : Finset (Fin 4)) ∪ {1,2,3}) = Finset.univ by decide]
  exact qTwoSixWin_coordBlockSU_univ 4

private theorem mem_triple_edge_cases {i j k a b : Fin n}
    (_hij : M i j = 3) (_hjk : M j k = 3) (hik : M i k = 2)
    (ha : a ∈ ({i, j, k} : Set (Fin n))) (hb : b ∈ ({i, j, k} : Set (Fin n)))
    (hab : M a b = 3) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) ∨ (a = j ∧ b = k) ∨ (a = k ∧ b = j) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · exfalso
    rw [ha, hb, M.diagonal] at hab
    omega
  · left; exact ⟨ha, hb⟩
  · exfalso
    rw [ha, hb] at hab
    rw [hik] at hab
    omega
  · right; left; exact ⟨ha, hb⟩
  · exfalso
    rw [ha, hb, M.diagonal] at hab
    omega
  · right; right; left; exact ⟨ha, hb⟩
  · exfalso
    rw [ha, hb] at hab
    rw [M.symmetric k i, hik] at hab
    omega
  · right; right; right; exact ⟨ha, hb⟩
  · exfalso
    rw [ha, hb, M.diagonal] at hab
    omega

private theorem levi_triple (S : QTwoPhanFamily K M X) (hK : Nat.card K = 4)
    {i j k : Fin n} (hij : M i j = 3) (hjk : M j k = 3) (hik : M i k = 2)
    {κ : Su K 2 1 4 →* X}
    (hκ1 : κ.comp (blk012 K) = S.θ i j) (hκ2 : κ.comp (blk123 K) = S.θ j k) :
    S.levi ({i, j, k} : Set (Fin n)) = κ.range := by
  have hblk : (blk012 K).range ⊔ (blk123 K).range = ⊤ := blk012_sup_blk123 hK
  have hκrange : κ.range = (S.θ i j).range ⊔ (S.θ j k).range := by
    calc κ.range = (⊤ : Subgroup (Su K 2 1 4)).map κ := MonoidHom.range_eq_map κ
      _ = ((blk012 K).range ⊔ (blk123 K).range).map κ := by rw [hblk]
      _ = (blk012 K).range.map κ ⊔ (blk123 K).range.map κ :=
            Subgroup.map_sup (blk012 K).range (blk123 K).range κ
      _ = (κ.comp (blk012 K)).range ⊔ (κ.comp (blk123 K)).range := by
            rw [MonoidHom.range_comp, MonoidHom.range_comp]
      _ = (S.θ i j).range ⊔ (S.θ j k).range := by rw [hκ1, hκ2]
  have hlevi : S.levi ({i, j, k} : Set (Fin n)) =
      (S.θ i j).range ⊔ (S.θ j k).range := by
    apply le_antisymm
    · rw [QTwoPhanFamily.levi]
      refine sup_le ?_ ?_
      · refine iSup_le fun a => iSup_le fun ha => ?_
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with ha | ha | ha
        · rw [ha, ← S.left i j hij, MonoidHom.range_comp]
          exact (Subgroup.map_le_range _ _).trans le_sup_left
        · rw [ha, ← S.right i j hij, MonoidHom.range_comp]
          exact (Subgroup.map_le_range _ _).trans le_sup_left
        · rw [ha, ← S.right j k hjk, MonoidHom.range_comp]
          exact (Subgroup.map_le_range _ _).trans le_sup_right
      · refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb =>
          iSup_le fun hab => ?_
        rcases mem_triple_edge_cases hij hjk hik ha hb hab with
          ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha, hb]
          exact le_sup_left
        · rw [ha, hb, S.rev i j hij, MonoidHom.range_comp]
          exact (Subgroup.map_le_range _ _).trans le_sup_left
        · rw [ha, hb]
          exact le_sup_right
        · rw [ha, hb, S.rev j k hjk, MonoidHom.range_comp]
          exact (Subgroup.map_le_range _ _).trans le_sup_right
    · exact sup_le (S.le_levi_edge (by simp) (by simp) hij)
        (S.le_levi_edge (by simp) (by simp) hjk)
  rw [hlevi, hκrange]

private theorem rotSU_ne_one {F : Type} [Field F] (σ : F ≃+* F) :
    rotSU σ ≠ (1 : ↥(SUid σ 2)) := by
  intro h
  have h' : (0 : F) = 1 := by
    simpa [rotSU, rotMat] using congrArg
      (fun g : ↥(SUid σ 2) => (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)) h
  exact zero_ne_one h'

private structure LeviHomValues (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    {C : Set (Fin n)} (φ : S.levi C →* Y) : Prop where
  node : ∀ i (hi : i ∈ C) a, φ ⟨S.ι i a, S.mem_levi_node hi a⟩ = F.ι i a
  edge : ∀ i j (hi : i ∈ C) (hj : j ∈ C) (h3 : M i j = 3) b,
    φ ⟨S.θ i j b, S.mem_levi_edge hi hj h3 b⟩ = F.θ i j b

private abbrev LeviHomConclusion (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    (C : Set (Fin n)) : Prop :=
  ∃ φ : S.levi C →* Y, LeviHomValues S F φ

private theorem exists_leviHom_empty (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y) :
    LeviHomConclusion S F ∅ := by
  refine ⟨1, { node := ?_, edge := ?_ }⟩
  · intro i hi
    exact absurd hi (by simp)
  · intro i j hi
    exact absurd hi (by simp)

private theorem exists_leviHom_singleton (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    (hS : S.Faithful) (i : Fin n) :
    LeviHomConclusion S F ({i} : Set (Fin n)) := by
  let e : Su K 2 1 2 ≃* S.levi ({i} : Set (Fin n)) :=
    (MonoidHom.ofInjective (hS.ι_inj i)).trans
      (MulEquiv.subgroupCongr (levi_singleton S i).symm)
  refine ⟨(F.ι i).comp e.symm.toMonoidHom, { node := ?_, edge := ?_ }⟩
  · intro j hj a
    rw [Set.mem_singleton_iff] at hj
    have hx : (⟨S.ι j a, S.mem_levi_node (C := {i}) hj a⟩ :
        S.levi ({i} : Set (Fin n))) = e a := by
      apply Subtype.ext
      change S.ι j a = (e a : X)
      rw [hj]
      rfl
    rw [hx]
    change (F.ι i) (e.symm (e a)) = F.ι j a
    rw [MulEquiv.symm_apply_apply, hj]
  · intro j k hj hk h3 b
    rw [Set.mem_singleton_iff] at hj hk
    exfalso
    rw [hj, hk, M.diagonal] at h3
    omega

private theorem exists_leviHom_pair (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    (hS : S.Faithful) {i j : Fin n} (h3 : M i j = 3) :
    LeviHomConclusion S F ({i, j} : Set (Fin n)) := by
  let e : Su K 2 1 3 ≃* S.levi ({i, j} : Set (Fin n)) :=
    (MonoidHom.ofInjective (hS.θ_inj i j h3)).trans
      (MulEquiv.subgroupCongr (levi_pair S h3).symm)
  let φ : S.levi ({i, j} : Set (Fin n)) →* Y :=
    (F.θ i j).comp e.symm.toMonoidHom
  have hφe : ∀ x : Su K 2 1 3, φ (e x) = F.θ i j x := by
    intro x
    simp [φ]
  refine ⟨φ, { node := ?_, edge := ?_ }⟩
  · intro a ha b
    have ha' : a = i ∨ a = j := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    rcases ha' with haeq | haeq
    · have hx : (⟨S.ι a b, S.mem_levi_node (C := {i, j}) ha b⟩ :
          S.levi ({i, j} : Set (Fin n))) =
          e (embSUid (unitaryInvolution K 2 1) 2 b) := by
        apply Subtype.ext
        calc S.ι a b = S.ι i b := by rw [haeq]
          _ = ((S.θ i j).comp (embSUid (unitaryInvolution K 2 1) 2)) b :=
                (DFunLike.congr_fun (S.left i j h3) b).symm
          _ = S.θ i j (embSUid (unitaryInvolution K 2 1) 2 b) := rfl
      rw [hx, hφe, haeq]
      simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun (F.left i j h3) b
    · have hx : (⟨S.ι a b, S.mem_levi_node (C := {i, j}) ha b⟩ :
          S.levi ({i, j} : Set (Fin n))) =
          e (embSUid (unitaryInvolution K 2 1) 0 b) := by
        apply Subtype.ext
        calc S.ι a b = S.ι j b := by rw [haeq]
          _ = ((S.θ i j).comp (embSUid (unitaryInvolution K 2 1) 0)) b :=
                (DFunLike.congr_fun (S.right i j h3) b).symm
          _ = S.θ i j (embSUid (unitaryInvolution K 2 1) 0 b) := rfl
      rw [hx, hφe, haeq]
      simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun (F.right i j h3) b
  · intro a b ha hb hab c
    rcases mem_pair_edge_cases (M := M) h3 ha hb hab with ⟨hae, hbe⟩ | ⟨hae, hbe⟩
    · have hc : (S.θ a b) c ∈ (S.θ a b).range :=
        (MonoidHom.mem_range (f := S.θ a b)).mpr ⟨c, rfl⟩
      have hx : (⟨S.θ a b c, S.mem_levi_edge (C := {i, j}) ha hb hab c⟩ :
          S.levi ({i, j} : Set (Fin n))) = e c := by
        apply Subtype.ext
        change S.θ a b c = S.θ i j c
        rw [hae, hbe]
      rw [hx, hφe, hae, hbe]
    · have hc : (S.θ a b) c ∈ (S.θ a b).range :=
        (MonoidHom.mem_range (f := S.θ a b)).mpr ⟨c, rfl⟩
      have hx : (⟨S.θ a b c, S.mem_levi_edge (C := {i, j}) ha hb hab c⟩ :
          S.levi ({i, j} : Set (Fin n))) = e ((revSU3 K 2 1) c) := by
        apply Subtype.ext
        change S.θ a b c = S.θ i j ((revSU3 K 2 1) c)
        rw [hae, hbe]
        rw [S.rev i j h3]
        rfl
      rw [hx, hφe, hae, hbe, F.rev i j h3]
      rfl

private theorem exists_leviHom_triple (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    (hS : S.Faithful) (hK : Nat.card K = 4) {i j k : Fin n}
    (hij : M i j = 3) (hjk : M j k = 3) (hik : M i k = 2) :
    LeviHomConclusion S F ({i, j, k} : Set (Fin n)) := by
  obtain ⟨κS, hκS1, hκS2⟩ := S.a3 i j k hij hjk hik
  obtain ⟨κF, hκF1, hκF2⟩ := F.a3 i j k hij hjk hik
  have hκSrange : S.levi ({i, j, k} : Set (Fin n)) = κS.range :=
    levi_triple S hK hij hjk hik hκS1 hκS2
  have hκSinj : Function.Injective κS := by
    apply injective_of_exists_ne_one hK
    refine ⟨blk012 K (embSUid (unitaryInvolution K 2 1) 2
      (rotSU (unitaryInvolution K 2 1))), ?_⟩
    intro h
    have hθ : S.θ i j (embSUid (unitaryInvolution K 2 1) 2
        (rotSU (unitaryInvolution K 2 1))) = 1 := by
      rw [← hκS1]
      exact h
    have hι : S.ι i (rotSU (unitaryInvolution K 2 1)) = 1 := by
      rw [← S.left i j hij]
      exact hθ
    have hrot : rotSU (unitaryInvolution K 2 1) = 1 := by
      apply hS.ι_inj i
      rw [hι, map_one]
    exact rotSU_ne_one (unitaryInvolution K 2 1) hrot
  let e : Su K 2 1 4 ≃* S.levi ({i, j, k} : Set (Fin n)) :=
    (MonoidHom.ofInjective hκSinj).trans (MulEquiv.subgroupCongr hκSrange.symm)
  let φ : S.levi ({i, j, k} : Set (Fin n)) →* Y := κF.comp e.symm.toMonoidHom
  have hφe : ∀ x : Su K 2 1 4, φ (e x) = κF x := by
    intro x
    simp [φ]
  refine ⟨φ, { node := ?_, edge := ?_ }⟩
  · intro a ha b
    have ha' : a = i ∨ a = j ∨ a = k := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    rcases ha' with haeq | haeq | haeq
    · have hx : (⟨S.ι a b, S.mem_levi_node (C := {i, j, k}) ha b⟩ :
          S.levi ({i, j, k} : Set (Fin n))) =
          e (blk012 K (embSUid (unitaryInvolution K 2 1) 2 b)) := by
        apply Subtype.ext
        change S.ι a b = (e (blk012 K (embSUid (unitaryInvolution K 2 1) 2 b)) : X)
        rw [haeq]
        change S.ι i b = (κS.comp (blk012 K)) (embSUid (unitaryInvolution K 2 1) 2 b)
        rw [hκS1]
        rw [← S.left i j hij]
        rfl
      rw [hx, hφe, haeq]
      change (κF.comp (blk012 K)) (embSUid (unitaryInvolution K 2 1) 2 b) = F.ι i b
      rw [hκF1]
      simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun (F.left i j hij) b
    · have hx : (⟨S.ι a b, S.mem_levi_node (C := {i, j, k}) ha b⟩ :
          S.levi ({i, j, k} : Set (Fin n))) =
          e (blk012 K (embSUid (unitaryInvolution K 2 1) 0 b)) := by
        apply Subtype.ext
        change S.ι a b = (e (blk012 K (embSUid (unitaryInvolution K 2 1) 0 b)) : X)
        rw [haeq]
        change S.ι j b = (κS.comp (blk012 K)) (embSUid (unitaryInvolution K 2 1) 0 b)
        rw [hκS1]
        rw [← S.right i j hij]
        rfl
      rw [hx, hφe, haeq]
      change (κF.comp (blk012 K)) (embSUid (unitaryInvolution K 2 1) 0 b) = F.ι j b
      rw [hκF1]
      simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun (F.right i j hij) b
    · have hx : (⟨S.ι a b, S.mem_levi_node (C := {i, j, k}) ha b⟩ :
          S.levi ({i, j, k} : Set (Fin n))) =
          e (blk123 K (embSUid (unitaryInvolution K 2 1) 0 b)) := by
        apply Subtype.ext
        change S.ι a b = (e (blk123 K (embSUid (unitaryInvolution K 2 1) 0 b)) : X)
        rw [haeq]
        change S.ι k b = (κS.comp (blk123 K)) (embSUid (unitaryInvolution K 2 1) 0 b)
        rw [hκS2]
        rw [← S.right j k hjk]
        rfl
      rw [hx, hφe, haeq]
      change (κF.comp (blk123 K)) (embSUid (unitaryInvolution K 2 1) 0 b) = F.ι k b
      rw [hκF2]
      simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun (F.right j k hjk) b
  · intro a b ha hb hab c
    rcases mem_triple_edge_cases hij hjk hik ha hb hab with
      ⟨hae, hbe⟩ | ⟨hae, hbe⟩ | ⟨hae, hbe⟩ | ⟨hae, hbe⟩
    · have hc : (S.θ a b) c ∈ (S.θ a b).range :=
        (MonoidHom.mem_range (f := S.θ a b)).mpr ⟨c, rfl⟩
      have hx : (⟨S.θ a b c, S.mem_levi_edge (C := {i, j, k}) ha hb hab c⟩ :
          S.levi ({i, j, k} : Set (Fin n))) = e (blk012 K c) := by
        apply Subtype.ext
        change S.θ a b c = (e (blk012 K c) : X)
        rw [hae, hbe]
        change S.θ i j c = (κS.comp (blk012 K)) c
        rw [hκS1]
      rw [hx, hφe]
      change κF (blk012 K c) = F.θ a b c
      rw [hae, hbe]
      change (κF.comp (blk012 K)) c = F.θ i j c
      rw [hκF1]
    · have hc : (S.θ a b) c ∈ (S.θ a b).range :=
        (MonoidHom.mem_range (f := S.θ a b)).mpr ⟨c, rfl⟩
      have hx : (⟨S.θ a b c, S.mem_levi_edge (C := {i, j, k}) ha hb hab c⟩ :
          S.levi ({i, j, k} : Set (Fin n))) = e (blk012 K ((revSU3 K 2 1) c)) := by
        apply Subtype.ext
        change S.θ a b c = (e (blk012 K ((revSU3 K 2 1) c)) : X)
        rw [hae, hbe]
        change S.θ j i c = (κS.comp (blk012 K)) ((revSU3 K 2 1) c)
        rw [hκS1]
        rw [S.rev i j hij]
        rfl
      rw [hx, hφe]
      change κF (blk012 K ((revSU3 K 2 1) c)) = F.θ a b c
      rw [hae, hbe]
      change (κF.comp (blk012 K)) ((revSU3 K 2 1) c) = F.θ j i c
      rw [hκF1]
      rw [F.rev i j hij]
      rfl
    · have hc : (S.θ a b) c ∈ (S.θ a b).range :=
        (MonoidHom.mem_range (f := S.θ a b)).mpr ⟨c, rfl⟩
      have hx : (⟨S.θ a b c, S.mem_levi_edge (C := {i, j, k}) ha hb hab c⟩ :
          S.levi ({i, j, k} : Set (Fin n))) = e (blk123 K c) := by
        apply Subtype.ext
        change S.θ a b c = (e (blk123 K c) : X)
        rw [hae, hbe]
        change S.θ j k c = (κS.comp (blk123 K)) c
        rw [hκS2]
      rw [hx, hφe]
      change κF (blk123 K c) = F.θ a b c
      rw [hae, hbe]
      change (κF.comp (blk123 K)) c = F.θ j k c
      rw [hκF2]
    · have hc : (S.θ a b) c ∈ (S.θ a b).range :=
        (MonoidHom.mem_range (f := S.θ a b)).mpr ⟨c, rfl⟩
      have hx : (⟨S.θ a b c, S.mem_levi_edge (C := {i, j, k}) ha hb hab c⟩ :
          S.levi ({i, j, k} : Set (Fin n))) = e (blk123 K ((revSU3 K 2 1) c)) := by
        apply Subtype.ext
        change S.θ a b c = (e (blk123 K ((revSU3 K 2 1) c)) : X)
        rw [hae, hbe]
        change S.θ k j c = (κS.comp (blk123 K)) ((revSU3 K 2 1) c)
        rw [hκS2]
        rw [S.rev j k hjk]
        rfl
      rw [hx, hφe]
      change κF (blk123 K ((revSU3 K 2 1) c)) = F.θ a b c
      rw [hae, hbe]
      change (κF.comp (blk123 K)) ((revSU3 K 2 1) c) = F.θ k j c
      rw [hκF2]
      rw [F.rev j k hjk]
      rfl

private theorem exists_leviHom_split (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    (hS : S.Faithful) {C₁ C₂ : Set (Fin n)} (_hne1 : C₁.Nonempty)
    (_hne2 : C₂.Nonempty) (hdisj : Disjoint C₁ C₂)
    (hcross : ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2) (hC : C₁ ∪ C₂ ∈ qTwoShape M)
    {φ₁ : S.levi C₁ →* Y} (hφ₁ : LeviHomValues S F φ₁)
    {φ₂ : S.levi C₂ →* Y} (hφ₂ : LeviHomValues S F φ₂) :
    LeviHomConclusion S F (C₁ ∪ C₂) := by
  have hlevi : S.levi (C₁ ∪ C₂) = S.levi C₁ ⊔ S.levi C₂ := levi_union S hcross
  have hcommS : S.levi C₁ ≤ Subgroup.centralizer (S.levi C₂ : Set X) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (levi_commute S hcross x hx y hy).symm
  have hdisj' : Disjoint (S.levi C₁) (S.levi C₂) :=
    disjoint_iff.mpr (hS.split C₁ C₂ hC hdisj hcross)
  let e : (S.levi C₁ × S.levi C₂) ≃* S.levi (C₁ ∪ C₂) :=
    (mulEquiv_prod_sup hcommS hdisj').trans (MulEquiv.subgroupCongr hlevi.symm)
  have hφ₁range : ∀ x : S.levi C₁, (φ₁ x : Y) ∈ F.levi C₁ := by
    intro x
    refine levi_induction' S x.2 (P := fun z hz => (φ₁ ⟨z, hz⟩ : Y) ∈ F.levi C₁) ?_ ?_ ?_ ?_
    · intro i hi a hmem
      have hx : (⟨S.ι i a, hmem⟩ : S.levi C₁) =
          ⟨S.ι i a, S.mem_levi_node hi a⟩ := Subtype.ext rfl
      rw [hx, hφ₁.node i hi a]
      exact F.le_levi_node hi ⟨a, rfl⟩
    · intro i j hi hj h3 b hmem
      have hx : (⟨S.θ i j b, hmem⟩ : S.levi C₁) =
          ⟨S.θ i j b, S.mem_levi_edge hi hj h3 b⟩ := Subtype.ext rfl
      rw [hx, hφ₁.edge i j hi hj h3 b]
      exact F.le_levi_edge hi hj h3 ⟨b, rfl⟩
    · have h1 : (⟨1, _⟩ : S.levi C₁) = 1 := Subtype.ext rfl
      rw [h1, map_one]
      exact (F.levi C₁).one_mem
    · intro x y hx hy hxP hyP
      have hxy : (⟨x * y, mul_mem hx hy⟩ : S.levi C₁) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
        Subtype.ext rfl
      rw [hxy, map_mul]
      exact (F.levi C₁).mul_mem hxP hyP
  have hφ₂range : ∀ x : S.levi C₂, (φ₂ x : Y) ∈ F.levi C₂ := by
    intro x
    refine levi_induction' S x.2 (P := fun z hz => (φ₂ ⟨z, hz⟩ : Y) ∈ F.levi C₂) ?_ ?_ ?_ ?_
    · intro i hi a hmem
      have hx : (⟨S.ι i a, hmem⟩ : S.levi C₂) =
          ⟨S.ι i a, S.mem_levi_node hi a⟩ := Subtype.ext rfl
      rw [hx, hφ₂.node i hi a]
      exact F.le_levi_node hi ⟨a, rfl⟩
    · intro i j hi hj h3 b hmem
      have hx : (⟨S.θ i j b, hmem⟩ : S.levi C₂) =
          ⟨S.θ i j b, S.mem_levi_edge hi hj h3 b⟩ := Subtype.ext rfl
      rw [hx, hφ₂.edge i j hi hj h3 b]
      exact F.le_levi_edge hi hj h3 ⟨b, rfl⟩
    · have h1 : (⟨1, _⟩ : S.levi C₂) = 1 := Subtype.ext rfl
      rw [h1, map_one]
      exact (F.levi C₂).one_mem
    · intro x y hx hy hxP hyP
      have hxy : (⟨x * y, mul_mem hx hy⟩ : S.levi C₂) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
        Subtype.ext rfl
      rw [hxy, map_mul]
      exact (F.levi C₂).mul_mem hxP hyP
  have hcommF : ∀ m : S.levi C₁, ∀ n : S.levi C₂, Commute (φ₁ m) (φ₂ n) := by
    intro m n
    exact levi_commute F hcross (φ₁ m) (hφ₁range m) (φ₂ n) (hφ₂range n)
  let ψ : (S.levi C₁ × S.levi C₂) →* Y := φ₁.noncommCoprod φ₂ hcommF
  let φ : S.levi (C₁ ∪ C₂) →* Y := ψ.comp e.symm.toMonoidHom
  have hφe : ∀ p, φ (e p) = ψ p := by
    intro p
    simp [φ]
  refine ⟨φ, { node := ?_, edge := ?_ }⟩
  · intro a ha b
    rw [Set.mem_union] at ha
    rcases ha with ha | ha
    · let x : S.levi C₁ := ⟨S.ι a b, S.mem_levi_node ha b⟩
      have hx : (⟨S.ι a b, S.mem_levi_node (C := C₁ ∪ C₂) (Or.inl ha) b⟩ :
          S.levi (C₁ ∪ C₂)) = e (x, 1) := by
        apply Subtype.ext
        change S.ι a b = (e (x, 1) : X)
        change S.ι a b = ((x : X) * 1)
        simp only [mul_one]
        rfl
      rw [hx, hφe]
      change ψ (x, 1) = F.ι a b
      rw [show ψ (x, 1) = φ₁ x by simp [ψ, MonoidHom.noncommCoprod_apply]]
      exact hφ₁.node a ha b
    · let x : S.levi C₂ := ⟨S.ι a b, S.mem_levi_node ha b⟩
      have hx : (⟨S.ι a b, S.mem_levi_node (C := C₁ ∪ C₂) (Or.inr ha) b⟩ :
          S.levi (C₁ ∪ C₂)) = e (1, x) := by
        apply Subtype.ext
        change S.ι a b = (e (1, x) : X)
        change S.ι a b = ((1 : X) * (x : X))
        simp only [one_mul]
        rfl
      rw [hx, hφe]
      change ψ (1, x) = F.ι a b
      rw [show ψ (1, x) = φ₂ x by simp [ψ, MonoidHom.noncommCoprod_apply]]
      exact hφ₂.node a ha b
  · intro a b ha hb hab c
    rw [Set.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · let x : S.levi C₁ := ⟨S.θ a b c, S.mem_levi_edge ha hb hab c⟩
      have hx : (⟨S.θ a b c,
          S.mem_levi_edge (C := C₁ ∪ C₂) (Or.inl ha) (Or.inl hb) hab c⟩ :
          S.levi (C₁ ∪ C₂)) = e (x, 1) := by
        apply Subtype.ext
        change S.θ a b c = (e (x, 1) : X)
        change S.θ a b c = ((x : X) * 1)
        simp only [mul_one]
        rfl
      rw [hx, hφe]
      change ψ (x, 1) = F.θ a b c
      rw [show ψ (x, 1) = φ₁ x by simp [ψ, MonoidHom.noncommCoprod_apply]]
      exact hφ₁.edge a b ha hb hab c
    · exfalso
      have h2 := hcross a ha b hb
      rw [hab] at h2
      omega
    · exfalso
      have h2 := hcross b hb a ha
      rw [M.symmetric b a, hab] at h2
      omega
    · let x : S.levi C₂ := ⟨S.θ a b c, S.mem_levi_edge ha hb hab c⟩
      have hx : (⟨S.θ a b c,
          S.mem_levi_edge (C := C₁ ∪ C₂) (Or.inr ha) (Or.inr hb) hab c⟩ :
          S.levi (C₁ ∪ C₂)) = e (1, x) := by
        apply Subtype.ext
        change S.θ a b c = (e (1, x) : X)
        change S.θ a b c = ((1 : X) * (x : X))
        simp only [one_mul]
        rfl
      rw [hx, hφe]
      change ψ (1, x) = F.θ a b c
      rw [show ψ (1, x) = φ₂ x by simp [ψ, MonoidHom.noncommCoprod_apply]]
      exact hφ₂.edge a b ha hb hab c

private theorem QTwoPhanFamily.exists_leviHom_values {X Y : Type} [Group X] [Group Y]
    {S : QTwoPhanFamily K M X} (hK : Nat.card K = 4)
    (hlab : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3)
    (htri : ∀ i j k, M i j = 3 → M j k = 3 → M i k ≠ 3)
    (hS : S.Faithful) (F : QTwoPhanFamily K M Y) (C : Set (Fin n))
    (hC : C ∈ qTwoShape M) :
    LeviHomConclusion S F C := by
  have main : ∀ k, ∀ C : Set (Fin n), C.ncard = k → C ∈ qTwoShape M →
      LeviHomConclusion S F C := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hk hC
      rcases qTwoShape_cases hlab htri hC with
        rfl | ⟨i, rfl⟩ | ⟨i, j, h3, rfl⟩ |
          ⟨i, j, l, hij, hjl, hil, rfl⟩ |
          ⟨C₁, C₂, hne1, hne2, hdisj, rfl, hcross⟩
      · exact exists_leviHom_empty S F
      · exact exists_leviHom_singleton S F hS i
      · exact exists_leviHom_pair S F hS h3
      · exact exists_leviHom_triple S F hS hK hij hjl hil
      · have hC12 : C₁ ∪ C₂ ∈ qTwoShape M := hC
        have hC1 : C₁ ∈ qTwoShape M := qTwoShape_mono hC12 Set.subset_union_left
        have hC2 : C₂ ∈ qTwoShape M := qTwoShape_mono hC12 Set.subset_union_right
        have hcard : (C₁ ∪ C₂).ncard = C₁.ncard + C₂.ncard := Set.ncard_union_eq hdisj
        have hpos1 : 0 < C₁.ncard := (Set.ncard_pos (s := C₁)).mpr hne1
        have hpos2 : 0 < C₂.ncard := (Set.ncard_pos (s := C₂)).mpr hne2
        have hlt1 : C₁.ncard < k := by
          rw [← hk, hcard]
          omega
        have hlt2 : C₂.ncard < k := by
          rw [← hk, hcard]
          omega
        obtain ⟨φ₁, hφ₁⟩ := ih C₁.ncard hlt1 C₁ rfl hC1
        obtain ⟨φ₂, hφ₂⟩ := ih C₂.ncard hlt2 C₂ rfl hC2
        exact exists_leviHom_split S F hS hne1 hne2 hdisj hcross hC12 hφ₁ hφ₂
  exact main C.ncard C rfl hC

private theorem leviHom_eq_of_le (S : QTwoPhanFamily K M X) (F : QTwoPhanFamily K M Y)
    {C D : Set (Fin n)} (hCD : C ⊆ D)
    {φC : S.levi C →* Y} (hφC : LeviHomValues S F φC)
    {φD : S.levi D →* Y} (hφD : LeviHomValues S F φD) :
    φC = (φD).comp (Subgroup.inclusion (S.levi_mono hCD)) := by
  let incl : S.levi C →* X := Subgroup.subtype _
  let E : Subgroup (S.levi C) :=
    (φC).eqLocus ((φD).comp (Subgroup.inclusion (S.levi_mono hCD)))
  have hmap : E.map incl = S.levi C := by
    apply le_antisymm
    · rintro z ⟨x, hxE, rfl⟩
      exact x.2
    · intro z hz
      have hz' : z ∈ ⨆ g, leviGen S C g := by
        rwa [← levi_eq_iSup_gen]
      refine Subgroup.iSup_induction (S := leviGen S C)
        (C := fun z => z ∈ E.map incl) hz' ?_ ?_ ?_
      · rintro g z hz
        rcases g with ⟨i, hi⟩ | ⟨⟨i, j⟩, ⟨hi, hj, h3⟩⟩
        · rcases hz with ⟨a, rfl⟩
          refine ⟨⟨S.ι i a, S.mem_levi_node hi a⟩, ?_, rfl⟩
          change φC ⟨S.ι i a, S.mem_levi_node hi a⟩ =
            φD ((Subgroup.inclusion (S.levi_mono hCD))
              ⟨S.ι i a, S.mem_levi_node hi a⟩)
          rw [(hφC).node i hi a]
          exact ((hφD).node i (hCD hi) a).symm
        · rcases hz with ⟨b, rfl⟩
          refine ⟨⟨S.θ i j b, S.mem_levi_edge hi hj h3 b⟩, ?_, rfl⟩
          change φC ⟨S.θ i j b, S.mem_levi_edge hi hj h3 b⟩ =
            φD ((Subgroup.inclusion (S.levi_mono hCD))
              ⟨S.θ i j b, S.mem_levi_edge hi hj h3 b⟩)
          rw [(hφC).edge i j hi hj h3 b]
          exact ((hφD).edge i j (hCD hi) (hCD hj) h3 b).symm
      · exact (E.map incl).one_mem
      · intro x y hx hy
        exact (E.map incl).mul_mem hx hy
  have hE : E = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hx : incl x ∈ E.map incl := by
      rw [hmap]
      exact x.2
    rcases hx with ⟨y, hyE, hyx⟩
    have hxy : x = y := (Subtype.ext hyx).symm
    rw [hxy]
    exact hyE
  apply MonoidHom.ext
  intro z
  have hz : z ∈ E := by rw [hE]; trivial
  exact hz

private theorem leviHom_compatible_of_values {S : QTwoPhanFamily K M X}
    {F : QTwoPhanFamily K M Y} {φ : ∀ C : ↥(qTwoShape M), S.levi C.1 →* Y}
    (hφ : ∀ C, LeviHomValues S F (φ C)) :
    IsCompatible (fun C : ↥(qTwoShape M) => S.levi C.1) φ := by
  intro C D hCD x y hxy
  have hCD' : C.1 ⊆ D.1 := hCD
  have hψeq : φ C = (φ D).comp (Subgroup.inclusion (S.levi_mono hCD')) :=
    leviHom_eq_of_le S F hCD' (hφ C) (hφ D)
  have hy : y = Subgroup.inclusion (S.levi_mono hCD') x := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion]
    exact hxy.symm
  rw [hy, ← MonoidHom.comp_apply, ← hψeq]

theorem QTwoPhanFamily.isUniversal_of_isUniversalCompletion {X : Type} [Group X]
    {S : QTwoPhanFamily K M X} (hK : Nat.card K = 4) (hn : 4 ≤ n)
    (hlab : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3)
    (htri : ∀ i j k, M i j = 3 → M j k = 3 → M i k ≠ 3)
    (hS : S.Faithful)
    (hU : IsUniversalCompletion.{0, 0, 0}
      (fun C : ↥(qTwoShape M) => S.levi C.1)) : S.IsUniversal := by
  intro Y _ F
  let φ : (C : ↥(qTwoShape M)) → S.levi C.1 →* Y := fun C =>
    (QTwoPhanFamily.exists_leviHom_values hK hlab htri hS F C.1 C.2).choose
  have hφ : ∀ C, LeviHomValues S F (φ C) := fun C => by
    exact (QTwoPhanFamily.exists_leviHom_values hK hlab htri hS F C.1 C.2).choose_spec
  have hcompat : IsCompatible (fun C : ↥(qTwoShape M) => S.levi C.1) φ :=
    leviHom_compatible_of_values hφ
  obtain ⟨ψ, hψ, -⟩ := hU Y φ hcompat
  refine ⟨ψ, ?_, ?_⟩
  · intro i
    ext a
    let C : ↥(qTwoShape M) :=
      ⟨{i}, mem_qTwoShape_of_ncard_le_three hn (by simp [Set.ncard_singleton])⟩
    have h := hψ C ⟨S.ι i a, S.mem_levi_node (C := {i})
      (by show i ∈ ({i} : Set (Fin n)); simp) a⟩
    change ψ (S.ι i a) = F.ι i a
    rw [h]
    exact (hφ C).node i (by show i ∈ ({i} : Set (Fin n)); simp) a
  · intro i j hij
    ext b
    have hle : ({i, j} : Set (Fin n)).ncard ≤ 3 := by
      have h := Set.ncard_insert_le i ({j} : Set (Fin n))
      simp only [Set.ncard_singleton] at h
      omega
    let C : ↥(qTwoShape M) := ⟨{i, j}, mem_qTwoShape_of_ncard_le_three hn hle⟩
    have h := hψ C ⟨S.θ i j b,
      S.mem_levi_edge (C := {i, j})
        (by show i ∈ ({i, j} : Set (Fin n)); simp)
        (by show j ∈ ({i, j} : Set (Fin n)); simp) hij b⟩
    change ψ (S.θ i j b) = F.θ i j b
    rw [h]
    exact (hφ C).edge i j
      (by show i ∈ ({i, j} : Set (Fin n)); simp)
      (by show j ∈ ({i, j} : Set (Fin n)); simp) hij b

theorem QTwoPhanFamily.levi_le_of_forall_lt (S : QTwoPhanFamily K M X) {C : Set (Fin n)}
    {H : Subgroup X} (hι : ∀ i ∈ C, (S.ι i).range ≤ H)
    (hθ : ∀ i ∈ C, ∀ j ∈ C, i < j → M i j = 3 → (S.θ i j).range ≤ H) :
    S.levi C ≤ H := by
  rw [QTwoPhanFamily.levi]
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => hι i hi
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
      iSup_le fun h3 => ?_
    have hne : i ≠ j := by
      rintro rfl
      rw [M.diagonal] at h3
      omega
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hθ i hi j hj hij h3
    · have hsymm : M j i = 3 := (M.symmetric j i).trans h3
      rw [S.rev j i hsymm, MonoidHom.range_comp]
      exact (Subgroup.map_le_range _ _).trans (hθ j hj i hi hji hsymm)

theorem QTwoPhanFamily.exists_mul_of_mem_levi_union (S : QTwoPhanFamily K M X)
    {C₁ C₂ : Set (Fin n)} (hcross : ∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2) {x : X}
    (hx : x ∈ S.levi (C₁ ∪ C₂)) : ∃ a ∈ S.levi C₁, ∃ b ∈ S.levi C₂, a * b = x := by
  rw [levi_union S hcross] at hx
  have hcomm : S.levi C₁ ≤ Subgroup.centralizer (S.levi C₂ : Set X) := by
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (levi_commute S hcross a ha b hb).symm
  obtain ⟨a, ha, b, hb, h⟩ := mem_sup_of_commute hcomm hx
  exact ⟨a, ha, b, hb, h⟩

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
