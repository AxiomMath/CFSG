module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Std

@[expose] def a2 : Fin TwistTag.E6.foldedTag.rank := 3

@[expose] def J0 : Set (Fin TwistTag.E6.foldedTag.rank) := {a | a ≠ a2}

@[expose] def w0word : List (Fin TwistTag.E6.foldedTag.rank) := [3, 2, 1, 0, 2, 1, 2]

@[expose] def w0 : WeylGroup TwistTag.E6.tag := (w0word.map TwistTag.E6.orbitReflection).prod

theorem prod_orbitReflection_smul (l : List (Fin TwistTag.E6.foldedTag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (l.map TwistTag.E6.orbitReflection).prod • v =
      l.foldr (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w) v := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, mul_smul, ih, TwistTag.E6.orbitReflection_smul]

theorem w0_smul_alpha2 :
    w0 • (Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ) = e6HighestRoot := by
  rw [w0, prod_orbitReflection_smul]
  decide +kernel

theorem w0_mem : w0 ∈ relWeylTwist TwistTag.E6 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact TwistTag.E6.orbitReflection_mem a

section Fixed

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] def n0 : ModGL TwistTag.E6.tag K :=
  canonicalRep (coxeterSystem TwistTag.E6.tag) K w0

theorem n0_mem : n0 (K := K) ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
  canonicalRep_mem_graphFixedRootGroup w0_mem

theorem mem_conj_rootSpan_inf_iff {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (x : ModGL TwistTag.E6.tag K) :
    x ∈ rootSpan TwistTag.E6.tag K ((fun α => w • α) '' S) ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom ↔
      (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ * x *
          canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈
        rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
  have hn := canonicalRep_mem_twistedFixedGroup TwistTag.E6 K σ.toRingHom hw
  have h := (canonical_weyl_root_transport TwistTag.E6.tag K).1 w S hS
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← h]
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨y, hy, rfl⟩ := hx1
    refine ⟨?_, mul_mem (mul_mem (inv_mem hn) hx2) hn⟩
    have e : (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ *
        ((MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)).toMonoidHom y) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) K w = y := by
      change _ * (_ * y * _) * _ = y
      group
    rw [e]
    exact hy
  · rintro ⟨hx1, hx2⟩
    refine ⟨⟨_, hx1, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply, mul_assoc]
    · have := mul_mem (mul_mem hn hx2) (inv_mem hn)
      simpa [mul_assoc] using this

theorem E6_orbit_a2 : (TwistTag.E6.orbit a2 : Set (Fin TwistTag.E6.tag.rank)) = {1} := by
  ext i
  simp only [Finset.mem_coe, Set.mem_singleton_iff]
  revert i
  decide

theorem image_single_orbit_a2 :
    ((fun i => (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) ''
      ↑(TwistTag.E6.orbit a2)) = {Pi.single 1 1} := by
  rw [E6_orbit_a2, Set.image_singleton]

theorem image_neg_single_orbit_a2 :
    ((fun i => -(Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) ''
      ↑(TwistTag.E6.orbit a2)) = {-Pi.single 1 1} := by
  rw [E6_orbit_a2, Set.image_singleton]

theorem rootSpan_image_w0_alpha2 :
    rootSpan TwistTag.E6.tag K ((fun α => w0 • α) '' {(Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ)}) =
      rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
  rw [Set.image_singleton, w0_smul_alpha2, rootSpan_singleton]

theorem mem_X0_iff (x : twistedE6RootGroup K σ) :
    x ∈ twE6RootSubgroup K σ e6HighestRoot ↔
      ∃ c : orbitField TwistTag.E6 K σ.toRingHom a2,
        (x : ModGL TwistTag.E6.tag K) =
          n0 * (orbitX TwistTag.E6 K σ.toRingHom a2 c : ModGL TwistTag.E6.tag K) * n0⁻¹ := by
  have hS : ∀ α ∈ ({(Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ)} : Set _),
      IsRoot TwistTag.E6.tag α := by
    rintro α rfl
    exact isRoot_single _ _
  have key := mem_conj_rootSpan_inf_iff σ hS w0_mem (x : ModGL TwistTag.E6.tag K)
  rw [rootSpan_image_w0_alpha2] at key
  have hxΓ : (x : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ x.2
  have hspan : rootSpan TwistTag.E6.tag K
      ((fun i => (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit a2)) =
      rootSubgroup TwistTag.E6.tag K (Pi.single 1 1) := by
    rw [image_single_orbit_a2, rootSpan_singleton]
  constructor
  · intro hx
    have hx' : (x : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 (key.1 (Subgroup.mem_inf.2 ⟨hx', hxΓ⟩))
    rw [rootSpan_singleton] at h1
    rw [← hspan] at h1
    obtain ⟨c, hc⟩ := exists_orbitX_eq (σ := σ.toRingHom) h1
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 h2).2
    refine ⟨c, ?_⟩
    rw [hc]
    unfold n0
    group
  · rintro ⟨c, hc⟩
    have hu := orbitX_mem TwistTag.E6 σ.toRingHom a2 c
    rw [hspan, ← rootSpan_singleton] at hu
    have hx' : (canonicalRep (coxeterSystem TwistTag.E6.tag) K w0)⁻¹ * (x : ModGL TwistTag.E6.tag K) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w0 ∈
        rootSpan TwistTag.E6.tag K {(Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ)} ⊓
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
      have e : (canonicalRep (coxeterSystem TwistTag.E6.tag) K w0)⁻¹ *
          (x : ModGL TwistTag.E6.tag K) * canonicalRep (coxeterSystem TwistTag.E6.tag) K w0 =
            (orbitX TwistTag.E6 K σ.toRingHom a2 c : ModGL TwistTag.E6.tag K) := by
        rw [hc]
        unfold n0
        group
      rw [e]
      exact hu
    have := (key.2 hx').1
    exact this

theorem rootSpan_image_w0_neg_alpha2 :
    rootSpan TwistTag.E6.tag K
        ((fun α => w0 • α) '' {(-Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ)}) =
      rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := by
  rw [Set.image_singleton, smul_neg, w0_smul_alpha2, rootSpan_singleton]

theorem mem_X0m_iff (x : twistedE6RootGroup K σ) :
    x ∈ twE6RootSubgroup K σ (-e6HighestRoot) ↔
      ∃ c : orbitField TwistTag.E6 K σ.toRingHom a2,
        (x : ModGL TwistTag.E6.tag K) =
          n0 * (orbitY TwistTag.E6 K σ.toRingHom a2 c : ModGL TwistTag.E6.tag K) * n0⁻¹ := by
  have hS : ∀ α ∈ ({(-Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ)} : Set _),
      IsRoot TwistTag.E6.tag α := by
    rintro α rfl
    exact isRoot_neg_single _ _
  have key := mem_conj_rootSpan_inf_iff σ hS w0_mem (x : ModGL TwistTag.E6.tag K)
  rw [rootSpan_image_w0_neg_alpha2] at key
  have hxΓ : (x : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ x.2
  have hspan : rootSpan TwistTag.E6.tag K
      ((fun i => -(Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit a2)) =
      rootSubgroup TwistTag.E6.tag K (-Pi.single 1 1) := by
    rw [image_neg_single_orbit_a2, rootSpan_singleton]
  constructor
  · intro hx
    have hx' : (x : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 (key.1 (Subgroup.mem_inf.2 ⟨hx', hxΓ⟩))
    rw [rootSpan_singleton, ← hspan] at h1
    obtain ⟨c, hc⟩ := (orbitYEquiv TwistTag.E6 σ.toRingHom a2).surjective
      ⟨_, Subgroup.mem_inf.2 ⟨h1, h2⟩⟩
    refine ⟨c.toAdd, ?_⟩
    have hc' := congrArg Subtype.val hc
    have hc2 : ((orbitYEquiv TwistTag.E6 σ.toRingHom a2 c : _) : ModGL TwistTag.E6.tag K) =
        (orbitY TwistTag.E6 K σ.toRingHom a2 c.toAdd : ModGL TwistTag.E6.tag K) :=
      coe_orbitYEquiv TwistTag.E6 σ.toRingHom a2 c.toAdd
    rw [hc2] at hc'
    rw [hc']
    unfold n0
    group
  · rintro ⟨c, hc⟩
    have hyc := coe_orbitYEquiv TwistTag.E6 σ.toRingHom a2 c
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1
      (orbitYEquiv TwistTag.E6 σ.toRingHom a2 (Multiplicative.ofAdd c)).2
    rw [hyc] at hu1 hu2
    rw [hspan, ← rootSpan_singleton] at hu1
    have hx' : (canonicalRep (coxeterSystem TwistTag.E6.tag) K w0)⁻¹ * (x : ModGL TwistTag.E6.tag K) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w0 ∈
        rootSpan TwistTag.E6.tag K {(-Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ)} ⊓
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
      have e : (canonicalRep (coxeterSystem TwistTag.E6.tag) K w0)⁻¹ *
          (x : ModGL TwistTag.E6.tag K) * canonicalRep (coxeterSystem TwistTag.E6.tag) K w0 =
            (orbitY TwistTag.E6 K σ.toRingHom a2 c : ModGL TwistTag.E6.tag K) := by
        rw [hc]
        unfold n0
        group
      rw [e]
      exact Subgroup.mem_inf.2 ⟨hu1, hu2⟩
    exact (key.2 hx').1

@[expose] def xG (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) : twistedE6RootGroup K σ :=
  ⟨(orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K),
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
      (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ.toRingHom a c)⟩

@[expose] def yG (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) : twistedE6RootGroup K σ :=
  ⟨(orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K),
    graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
      (orbitY_mem_graphFixedNegUnipotent TwistTag.E6 σ.toRingHom a c)⟩

@[expose] def nG (a : Fin TwistTag.E6.foldedTag.rank) : twistedE6RootGroup K σ :=
  ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a),
    canonicalRep_mem_graphFixedRootGroup (TwistTag.E6.orbitReflection_mem a)⟩

@[expose] def hG (a : Fin TwistTag.E6.foldedTag.rank)
    (u : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) : twistedE6RootGroup K σ :=
  ⟨(orbitH TwistTag.E6 K σ.toRingHom a u : ModGL TwistTag.E6.tag K),
    orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom a u⟩

@[expose] def n0G : twistedE6RootGroup K σ := ⟨n0, n0_mem σ⟩

@[simp] theorem coe_xG (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    ((xG σ a c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) := rfl

@[simp] theorem coe_yG (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    ((yG σ a c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) := rfl

@[simp] theorem coe_nG (a : Fin TwistTag.E6.foldedTag.rank) :
    ((nG σ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) := rfl

@[simp] theorem coe_hG (a : Fin TwistTag.E6.foldedTag.rank)
    (u : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    ((hG σ a u : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (orbitH TwistTag.E6 K σ.toRingHom a u : ModGL TwistTag.E6.tag K) := rfl

@[simp] theorem coe_n0G :
    ((n0G σ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = n0 := rfl

theorem xG_add (a : Fin TwistTag.E6.foldedTag.rank)
    (c c' : orbitField TwistTag.E6 K σ.toRingHom a) :
    xG σ a (c + c') = xG σ a c * xG σ a c' := by
  apply Subtype.ext
  have h := orbitX_add σ.toRingHom a c c'
  have h2 := congrArg
    (Subtype.val : adjointGroup TwistTag.E6.tag K → ModGL TwistTag.E6.tag K) h
  exact h2

theorem xG_zero (a : Fin TwistTag.E6.foldedTag.rank) : xG σ a 0 = 1 := by
  apply Subtype.ext
  have h := orbitX_zero TwistTag.E6 σ.toRingHom a
  have h2 := congrArg
    (Subtype.val : adjointGroup TwistTag.E6.tag K → ModGL TwistTag.E6.tag K) h
  exact h2

theorem mem_X0_iff' (x : twistedE6RootGroup K σ) :
    x ∈ twE6RootSubgroup K σ e6HighestRoot ↔
      ∃ c : orbitField TwistTag.E6 K σ.toRingHom a2,
        x = n0G σ * xG σ a2 c * (n0G σ)⁻¹ := by
  rw [mem_X0_iff]
  refine exists_congr fun c => ?_
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem mem_X0m_iff' (x : twistedE6RootGroup K σ) :
    x ∈ twE6RootSubgroup K σ (-e6HighestRoot) ↔
      ∃ c : orbitField TwistTag.E6 K σ.toRingHom a2,
        x = n0G σ * yG σ a2 c * (n0G σ)⁻¹ := by
  rw [mem_X0m_iff]
  refine exists_congr fun c => ?_
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

end Fixed

end Std

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
