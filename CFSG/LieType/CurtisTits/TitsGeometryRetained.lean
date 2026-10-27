module

public import CFSG.LieType.CurtisTits.AmalgamRedundancy
public import CFSG.LieType.CurtisTits.TitsGeometry

public section

namespace CFSG.LieType.CurtisTits

open Subgroup
open CFSG.Monster.B.Recog
open _root_.Classical

universe u v w

variable {I : Type u} {X : Type v} {typ : X → I} {Γ : SimpleGraph X}
variable {G : Type v} [Group G] [MulAction G X]
variable {F : I → X}

@[expose]
def residueVertex (Γ : SimpleGraph X) (typ : X → I) (F : I → X) (J : Set I) : Type v :=
  {x : X // typ x ∉ J ∧ ∀ j ∈ J, Γ.Adj x (F j)}

@[expose]
def residueGraph (Γ : SimpleGraph X) (typ : X → I) (F : I → X) (J : Set I) :
    SimpleGraph (residueVertex Γ typ F J) :=
  Γ.comap (fun x : residueVertex Γ typ F J => x.1)

@[expose]
def residueTyp (J : Set I) (x : residueVertex Γ typ F J) : {i : I // i ∉ J} :=
  ⟨typ x.1, x.2.1⟩

def residueChamber (hFtyp : ∀ i, typ (F i) = i)
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j)) (J : Set I) :
    {i : I // i ∉ J} → residueVertex Γ typ F J :=
  fun i =>
    ⟨F i.1, by
      refine ⟨?_, ?_⟩
      · rw [hFtyp]
        exact i.2
      · intro j hj
        exact hFadj i.1 j (fun h => i.2 (h ▸ hj))⟩

@[instance_reducible]
def residueSMul (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y)) (J : Set I) :
    SMul (parabolic G F J) (residueVertex Γ typ F J) where
  smul g x :=
    ⟨g.1 • x.1, by
      refine ⟨?_, ?_⟩
      · rw [htyp]
        exact x.2.1
      · intro j hj
        rw [← mem_parabolic_iff.1 g.2 j hj]
        exact hadj g.1 (x.2.2 j hj)⟩

@[instance_reducible]
def residueMulAction (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y)) (J : Set I) :
    MulAction (parabolic G F J) (residueVertex Γ typ F J) where
  toSMul := residueSMul htyp hadj J
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g.1 h.1 x.1)

section ResidueLemmas

variable (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
variable (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
variable (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
variable (hFtyp : ∀ i, typ (F i) = i)
variable (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))

include htyp hadj in
theorem residueTyp_smul (J : Set I) (g : parabolic G F J)
    (x : residueVertex Γ typ F J) :
    letI : MulAction (parabolic G F J) (residueVertex Γ typ F J) :=
      residueMulAction htyp hadj J
    residueTyp J (g • x) = residueTyp J x := by
  let := residueMulAction (F := F) htyp hadj J
  exact Subtype.ext (htyp g.1 x.1)

include htyp hadj in
theorem residueGraph_adj_smul (J : Set I) (g : parabolic G F J)
    {x y : residueVertex Γ typ F J} (h : (residueGraph Γ typ F J).Adj x y) :
    letI : MulAction (parabolic G F J) (residueVertex Γ typ F J) :=
      residueMulAction htyp hadj J
    (residueGraph Γ typ F J).Adj (g • x) (g • y) := by
  let := residueMulAction (F := F) htyp hadj J
  rw [residueGraph, SimpleGraph.comap_adj] at h ⊢
  exact hadj g.1 h

include htyp_adj in
theorem residueTyp_ne_of_adj {J : Set I} {x y : residueVertex Γ typ F J}
    (h : (residueGraph Γ typ F J).Adj x y) : residueTyp J x ≠ residueTyp J y := by
  rw [residueGraph, SimpleGraph.comap_adj] at h
  intro hxy
  exact htyp_adj h (congrArg Subtype.val hxy)

include hFtyp hFadj in
theorem residueTyp_residueChamber (J : Set I) (i : {i : I // i ∉ J}) :
    residueTyp J (residueChamber hFtyp hFadj J i) = i :=
  Subtype.ext (hFtyp i.1)

include hFtyp hFadj in
theorem residueChamber_adj (J : Set I) {i j : {i : I // i ∉ J}} (hij : i ≠ j) :
    (residueGraph Γ typ F J).Adj (residueChamber hFtyp hFadj J i)
      (residueChamber hFtyp hFadj J j) := by
  rw [residueGraph, SimpleGraph.comap_adj]
  exact hFadj i.1 j.1 (fun h => hij (Subtype.ext h))

include htyp hadj hFtyp hFadj in
theorem residue_flagTransitive (hflag : FlagTransitive G Γ F) (J : Set I) (hJfin : J.Finite) :
    letI : MulAction (parabolic G F J) (residueVertex Γ typ F J) :=
      residueMulAction htyp hadj J
    FlagTransitive (parabolic G F J) (residueGraph Γ typ F J)
      (residueChamber hFtyp hFadj J) := by
  let := residueMulAction (F := F) htyp hadj J
  intro S' hS'
  let S : Set X := (fun x : residueVertex Γ typ F J => x.1) '' S' ∪ F '' J
  have hSfin : S.Finite :=
    (hS'.1.image (fun x : residueVertex Γ typ F J => x.1)).union (hJfin.image F)
  have hSpair : S.Pairwise Γ.Adj := by
    rw [Set.pairwise_union]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hab' : a' ≠ b' := fun h => hab (by rw [h])
      have hpair := hS'.2 ha' hb' hab'
      simpa only [residueGraph, SimpleGraph.comap_adj] using hpair
    · intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      exact hFadj i j (fun h => hab (by rw [h]))
    · intro a ha b hb _
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      exact ⟨a'.2.2 j hj, (a'.2.2 j hj).symm⟩
  have hS : IsFlag Γ S := ⟨hSfin, hSpair⟩
  obtain ⟨g, hg⟩ := hflag S hS
  have hfix : ∀ j ∈ J, g • F j = F j := by
    intro j hj
    obtain ⟨i, hi⟩ := hg (F j) (Or.inr ⟨j, hj, rfl⟩)
    have hityp : i = j := by
      calc i = typ (F i) := (hFtyp i).symm
        _ = typ (g • F j) := by rw [hi]
        _ = typ (F j) := htyp g (F j)
        _ = j := hFtyp j
    calc g • F j = F i := hi.symm
      _ = F j := by rw [hityp]
  refine ⟨⟨g, mem_parabolic_iff.2 hfix⟩, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hg x.1 (Or.inl ⟨x, hx, rfl⟩)
  have hityp : i = typ x.1 := by
    calc i = typ (F i) := (hFtyp i).symm
      _ = typ (g • x.1) := by rw [hi]
      _ = typ x.1 := htyp g x.1
  refine ⟨⟨i, ?_⟩, ?_⟩
  · rw [hityp]
    exact x.2.1
  · apply Subtype.ext
    exact hi

include htyp hadj hFtyp hFadj in
theorem residueParabolic_eq (J : Set I) (K : Set {i : I // i ∉ J}) :
    letI : MulAction (parabolic G F J) (residueVertex Γ typ F J) :=
      residueMulAction htyp hadj J
    parabolic (parabolic G F J) (residueChamber hFtyp hFadj J) K =
      (parabolic G F (J ∪ (fun i : {i : I // i ∉ J} => i.1) '' K)).subgroupOf
        (parabolic G F J) := by
  let := residueMulAction (F := F) htyp hadj J
  ext g
  rw [mem_parabolic_iff, Subgroup.mem_subgroupOf, mem_parabolic_iff]
  constructor
  · intro h i hi
    rcases hi with hiJ | ⟨k, hk, rfl⟩
    · exact mem_parabolic_iff.1 g.2 i hiJ
    · have := congrArg Subtype.val (h k hk)
      change g.1 • (residueChamber hFtyp hFadj J k).1 = (residueChamber hFtyp hFadj J k).1 at this
      simpa [residueChamber] using this
  · intro h k hk
    apply Subtype.ext
    change g.1 • (residueChamber hFtyp hFadj J k).1 = (residueChamber hFtyp hFadj J k).1
    simpa [residueChamber] using h k.1 (Or.inr ⟨k, hk, rfl⟩)

end ResidueLemmas

theorem residue_isUniversalCompletion
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFtyp : ∀ i, typ (F i) = i)
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F)
    (J : Set I) (hJfin : J.Finite)
    (hconn : (residueGraph Γ typ F J).Connected)
    (htri : Triangulable (residueGraph Γ typ F J)) :
    IsUniversalCompletion (fun K : ParabolicIndex {i : I // i ∉ J} =>
      (parabolic G F (J ∪ (fun i : {i : I // i ∉ J} => i.1) '' OrderDual.ofDual K.1)).subgroupOf
        (parabolic G F J)) := by
  let := residueMulAction (F := F) htyp hadj J
  have hne : Nonempty {i : I // i ∉ J} := by
    obtain ⟨x⟩ := hconn.nonempty
    exact ⟨⟨typ x.1, x.2.1⟩⟩
  let : Nonempty {i : I // i ∉ J} := hne
  have hT : IsUniversalCompletion (fun K : ParabolicIndex {i : I // i ∉ J} =>
      parabolic (parabolic G F J) (residueChamber hFtyp hFadj J) (OrderDual.ofDual K.1)) :=
    tits_geometry_isUniversalCompletion
      (I := {i : I // i ∉ J})
      (X := residueVertex Γ typ F J)
      (typ := residueTyp J)
      (Γ := residueGraph Γ typ F J)
      (G := parabolic G F J)
      (F := residueChamber hFtyp hFadj J)
      (fun i => residueTyp_residueChamber hFtyp hFadj J i)
      (fun g x => residueTyp_smul htyp hadj J g x)
      (fun {x y} h => residueTyp_ne_of_adj htyp_adj h)
      (fun g {x y} h => residueGraph_adj_smul htyp hadj J g h)
      (fun i j hij => residueChamber_adj hFtyp hFadj J hij)
      (residue_flagTransitive htyp hadj hFtyp hFadj hflag J hJfin)
      hconn htri
  have hEq : (fun K : ParabolicIndex {i : I // i ∉ J} =>
      parabolic (parabolic G F J) (residueChamber hFtyp hFadj J) (OrderDual.ofDual K.1)) =
      (fun K : ParabolicIndex {i : I // i ∉ J} =>
        (parabolic G F (J ∪ (fun i : {i : I // i ∉ J} => i.1) '' OrderDual.ofDual K.1)).subgroupOf
          (parabolic G F J)) :=
    funext (fun K => residueParabolic_eq htyp hadj hFtyp hFadj J (OrderDual.ofDual K.1))
  rw [hEq] at hT
  exact hT

section Retained

private theorem union_preimage_eq {J K : Set I} (hJK : J ⊆ K) :
    J ∪ Subtype.val '' (Subtype.val ⁻¹' K : Set {i : I // i ∉ J}) = K := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' K : Set {i : I // i ∉ J}) = K \ J := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxK, hxJ⟩
      exact ⟨⟨x, hxJ⟩, hxK, rfl⟩
  rw [himg, Set.union_diff_cancel hJK]

private theorem preimage_union_eq {J : Set I} (K : Set {i : I // i ∉ J}) :
    Subtype.val ⁻¹' (J ∪ Subtype.val '' K) = K := by
  have hJ : Subtype.val ⁻¹' J = (∅ : Set {i : I // i ∉ J}) := by
    ext x
    simp [x.2]
  rw [Set.preimage_union, hJ, Set.empty_union,
    Set.preimage_image_eq _ Subtype.val_injective]

private noncomputable def localIndexOrderIso (j : ParabolicIndex I) :
    {i : ParabolicIndex I // i < j} ≃o
      ParabolicIndex {i : I // i ∉ OrderDual.ofDual j.1} := by
  classical
  let J : Set I := OrderDual.ofDual j.1
  have hJne : J.Nonempty := j.2
  let toFun : {i : ParabolicIndex I // i < j} →
      ParabolicIndex {i : I // i ∉ J} := fun i =>
    ⟨OrderDual.toDual (Subtype.val ⁻¹' OrderDual.ofDual i.1.1), by
      have hle : J ⊆ OrderDual.ofDual i.1.1 := i.2.le
      have hne : OrderDual.ofDual i.1.1 ≠ J := fun h =>
        i.2.ne (Subtype.ext (OrderDual.ofDual.injective h))
      have hnot : ¬ OrderDual.ofDual i.1.1 ⊆ J := fun h => hne (le_antisymm h hle)
      obtain ⟨x, hxK, hxJ⟩ := Set.not_subset.1 hnot
      exact ⟨⟨x, hxJ⟩, hxK⟩⟩
  let ofFun : ParabolicIndex {i : I // i ∉ J} →
      {i : ParabolicIndex I // i < j} := fun K' =>
    ⟨⟨OrderDual.toDual (J ∪ Subtype.val '' OrderDual.ofDual K'.1),
        hJne.mono Set.subset_union_left⟩,
      lt_of_le_of_ne
        (show OrderDual.ofDual j.1 ⊆ J ∪ Subtype.val '' OrderDual.ofDual K'.1 from
          Set.subset_union_left)
        (by
          intro h
          obtain ⟨x, hxK⟩ := K'.2
          have hx : x.1 ∈ J ∪ Subtype.val '' OrderDual.ofDual K'.1 :=
            Set.mem_union_right J ⟨x, hxK, rfl⟩
          have hsets : J ∪ Subtype.val '' OrderDual.ofDual K'.1 = J := by
            simpa [J] using congrArg (fun i : ParabolicIndex I => OrderDual.ofDual i.1) h
          rw [hsets] at hx
          exact x.2 hx)⟩
  have left_inv : Function.LeftInverse ofFun toFun := by
    intro i
    apply Subtype.ext
    apply Subtype.ext
    apply OrderDual.ofDual.injective
    exact union_preimage_eq i.2.le
  have right_inv : Function.RightInverse ofFun toFun := by
    intro K'
    apply Subtype.ext
    apply OrderDual.ofDual.injective
    exact preimage_union_eq (J := J) (OrderDual.ofDual K'.1)
  let e : {i : ParabolicIndex I // i < j} ≃ ParabolicIndex {i : I // i ∉ J} :=
    { toFun := toFun, invFun := ofFun, left_inv := left_inv, right_inv := right_inv }
  refine e.toOrderIso ?_ ?_
  · intro a b hab
    change Subtype.val ⁻¹' OrderDual.ofDual b.1.1 ⊆
      Subtype.val ⁻¹' OrderDual.ofDual a.1.1
    exact Set.preimage_mono (show OrderDual.ofDual b.1.1 ⊆ OrderDual.ofDual a.1.1 from hab)
  · intro a b hab
    change J ∪ Subtype.val '' OrderDual.ofDual b.1 ⊆
      J ∪ Subtype.val '' OrderDual.ofDual a.1
    intro x hx
    rcases hx with hxJ | ⟨y, hy, rfl⟩
    · exact Or.inl hxJ
    · exact Or.inr ⟨y, (show OrderDual.ofDual b.1 ⊆ OrderDual.ofDual a.1 from hab) hy, rfl⟩

variable [Finite I]

theorem tits_geometry_isUniversalCompletion_of_retained
    (hFtyp : ∀ i, typ (F i) = i)
    (htyp : ∀ (g : G) (x : X), typ (g • x) = typ x)
    (htyp_adj : ∀ {x y : X}, Γ.Adj x y → typ x ≠ typ y)
    (hadj : ∀ (g : G) {x y : X}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hFadj : ∀ i j : I, i ≠ j → Γ.Adj (F i) (F j))
    (hflag : FlagTransitive G Γ F) (hconn : Γ.Connected) (htri : Triangulable Γ)
    (𝒮 : Set (Set I)) (hS_ne : ∀ J ∈ 𝒮, J.Nonempty)
    (hS_up : ∀ ⦃J J'⦄, J ∈ 𝒮 → J ⊆ J' → J' ∈ 𝒮)
    (hres : ∀ J, J.Nonempty → J ∉ 𝒮 →
      (residueGraph Γ typ F J).Connected ∧ Triangulable (residueGraph Γ typ F J)) :
    IsUniversalCompletion.{v, u, w}
      (fun J : {J : ParabolicIndex I // OrderDual.ofDual J.1 ∈ 𝒮} =>
        parabolic G F (OrderDual.ofDual J.1.1)) := by
  classical
  have hneI0 : Nonempty I := by
    obtain ⟨x⟩ := hconn.nonempty
    exact ⟨typ x⟩
  have huniv : Set.univ ∈ 𝒮 := by
    by_contra h
    have hneUniv : (Set.univ : Set I).Nonempty := ⟨hneI0.some, Set.mem_univ _⟩
    have hconnU := (hres Set.univ hneUniv h).1
    obtain ⟨x⟩ := hconnU.nonempty
    exact x.2.1 (Set.mem_univ (typ x.1))
  have hneI : Nonempty I := by
    obtain ⟨x, -⟩ := hS_ne Set.univ huniv
    exact ⟨x⟩
  let L : ParabolicIndex I → Subgroup G := fun J => parabolic G F (OrderDual.ofDual J.1)
  have hmono : Monotone L := by
    intro i j hij
    exact parabolic_antitone hij
  let S : Set (ParabolicIndex I) := {J | OrderDual.ofDual J.1 ∈ 𝒮}
  have hS : IsLowerSet S := by
    intro i j hji hiS
    exact hS_up hiS hji
  have hloc : ∀ j ∉ S,
      IsUniversalCompletion.{v, u, w}
        (fun i : {i : ParabolicIndex I // i < j} => (L i.1).subgroupOf (L j)) := by
    intro j hj
    let J : Set I := OrderDual.ofDual j.1
    have hJne : J.Nonempty := j.2
    have hJnot : J ∉ 𝒮 := by simpa [S, J] using hj
    obtain ⟨hconnJ, htriJ⟩ := hres J hJne hJnot
    have hresU : IsUniversalCompletion.{v, u, w}
        (fun K' : ParabolicIndex {i : I // i ∉ J} =>
          (parabolic G F (J ∪ Subtype.val '' OrderDual.ofDual K'.1)).subgroupOf
            (parabolic G F J)) :=
      residue_isUniversalCompletion htyp htyp_adj hadj hFtyp hFadj hflag J
        (Set.toFinite J) hconnJ htriJ
    let e := localIndexOrderIso j
    have hL' : ∀ i : {i : ParabolicIndex I // i < j},
        (fun K' : ParabolicIndex {i : I // i ∉ J} =>
          (parabolic G F (J ∪ Subtype.val '' OrderDual.ofDual K'.1)).subgroupOf
            (parabolic G F J)) (e i) =
        (fun i : {i : ParabolicIndex I // i < j} =>
          (parabolic G F (OrderDual.ofDual i.1.1)).subgroupOf
            (parabolic G F (OrderDual.ofDual j.1))) i := by
      intro i
      have hset : J ∪ Subtype.val '' OrderDual.ofDual (e i).1 =
          OrderDual.ofDual i.1.1 := by
        change J ∪ Subtype.val '' (Subtype.val ⁻¹' OrderDual.ofDual i.1.1) = _
        exact union_preimage_eq i.2.le
      show (parabolic G F (J ∪ Subtype.val '' OrderDual.ofDual (e i).1)).subgroupOf
          (parabolic G F J) =
        (parabolic G F (OrderDual.ofDual i.1.1)).subgroupOf
          (parabolic G F (OrderDual.ofDual j.1))
      rw [hset]
    have hL'symm : ∀ K' : ParabolicIndex {i : I // i ∉ J},
        (fun i : {i : ParabolicIndex I // i < j} =>
          (parabolic G F (OrderDual.ofDual i.1.1)).subgroupOf
            (parabolic G F (OrderDual.ofDual j.1))) (e.symm K') =
        (fun K' : ParabolicIndex {i : I // i ∉ J} =>
          (parabolic G F (J ∪ Subtype.val '' OrderDual.ofDual K'.1)).subgroupOf
            (parabolic G F J)) K' := by
      intro K'
      have h := hL' (e.symm K')
      rwa [OrderIso.apply_symm_apply] at h
    have hlocal : IsUniversalCompletion.{v, u, w}
        (fun i : {i : ParabolicIndex I // i < j} =>
          (parabolic G F (OrderDual.ofDual i.1.1)).subgroupOf
            (parabolic G F (OrderDual.ofDual j.1))) :=
      IsUniversalCompletion.congr_orderIso
        (L := fun K' : ParabolicIndex {i : I // i ∉ J} =>
          (parabolic G F (J ∪ Subtype.val '' OrderDual.ofDual K'.1)).subgroupOf
            (parabolic G F J))
        (L' := fun i : {i : ParabolicIndex I // i < j} =>
          (parabolic G F (OrderDual.ofDual i.1.1)).subgroupOf
            (parabolic G F (OrderDual.ofDual j.1)))
        e.symm hL'symm hresU
    simpa [L, J] using hlocal
  have hU : IsUniversalCompletion.{v, u, w} L :=
    letI : Nonempty I := hneI
    tits_geometry_isUniversalCompletion hFtyp htyp htyp_adj hadj hFadj hflag hconn htri
  change IsUniversalCompletion.{v, u, w} (fun i : S => L i.1)
  exact isUniversalCompletion_restrict hmono hS hloc hU

end Retained

end CFSG.LieType.CurtisTits
