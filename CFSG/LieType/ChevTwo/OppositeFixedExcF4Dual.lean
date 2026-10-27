module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTwisted
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeRoots

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.RelativeRoots

variable {K : Type} [Field K]

section Cert


namespace F4Dual

theorem phi_injective (h2 : (2 : K) = 0) : Function.Injective (e6FixedToF4 K) :=
  fun _ _ h => e6FixedToF4Group_injective h2 (Subtype.ext h)

theorem phi_surj (h2 : (2 : K) = 0) {x : ModGL Tag.F4 K} (hx : x ∈ adjointGroup Tag.F4 K) :
    ∃ g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)), e6FixedToF4 K g = x :=
  MonoidHom.mem_range.1 (adjointGroup_le_range_e6FixedToF4 h2 hx)

abbrev A6 (A : Set (Fin Tag.F4.rank)) : Set (Fin TwistTag.E6.tag.rank) :=
  TwistTag.E6.orbitUnion (f4FoldedIndex '' A)

theorem f4FoldedIndex_injective' :
    ∀ j j' : Fin Tag.F4.rank, f4FoldedIndex j = f4FoldedIndex j' → j = j' := by
  decide

theorem orbitIndex_eq_f4FoldedIndex : ∀ i : Fin TwistTag.E6.tag.rank,
    TwistTag.E6.orbitIndex i = f4FoldedIndex (e6IndexToF4 i) := by
  decide

theorem e6IndexToF4_eq_of_orbitIndex {j : Fin Tag.F4.rank} {i : Fin TwistTag.E6.tag.rank}
    (h : f4FoldedIndex j = TwistTag.E6.orbitIndex i) : e6IndexToF4 i = j :=
  (f4FoldedIndex_injective' _ _ (h.trans (orbitIndex_eq_f4FoldedIndex i))).symm

theorem orbitIndex_f4IndexRep : ∀ j : Fin Tag.F4.rank,
    TwistTag.E6.orbitIndex (f4IndexRep j) = f4FoldedIndex j := by
  decide

theorem orbitIndex_perm_f4IndexRep : ∀ j : Fin Tag.F4.rank,
    TwistTag.E6.orbitIndex (TwistTag.E6.perm (f4IndexRep j)) = f4FoldedIndex j := by
  decide

theorem rhoE6_rhoE6 : ∀ i : Fin Tag.E6.rank, rhoE6 (rhoE6 i) = i := by
  decide

theorem mem_A6_iff (A : Set (Fin Tag.F4.rank)) (i : Fin TwistTag.E6.tag.rank) :
    i ∈ A6 A ↔ e6IndexToF4 i ∈ A := by
  rw [A6, mem_orbitUnion_iff_orbitIndex]
  constructor
  · rintro ⟨j, hj, hji⟩
    rwa [e6IndexToF4_eq_of_orbitIndex hji]
  · intro h
    exact ⟨e6IndexToF4 i, h, (orbitIndex_eq_f4FoldedIndex i).symm⟩

open _root_.Classical in
theorem sum_e6_eq (P : Fin 4 → Prop) (β : Fin 6 → ℤ) :
    (∑ i : Fin 6, if P (e6IndexToF4 i) then 0 else β i) =
      ∑ j : Fin 4, if P j then 0 else e6ToF4 β j := by
  have e0 : e6IndexToF4 (0 : Fin 6) = (3 : Fin 4) := rfl
  have e1 : e6IndexToF4 (1 : Fin 6) = (0 : Fin 4) := rfl
  have e2 : e6IndexToF4 (2 : Fin 6) = (2 : Fin 4) := rfl
  have e3 : e6IndexToF4 (3 : Fin 6) = (1 : Fin 4) := rfl
  have e4 : e6IndexToF4 (4 : Fin 6) = (2 : Fin 4) := rfl
  have e5 : e6IndexToF4 (5 : Fin 6) = (3 : Fin 4) := rfl
  have f0 : e6ToF4 β (0 : Fin 4) = β 1 := rfl
  have f1 : e6ToF4 β (1 : Fin 4) = β 3 := rfl
  have f2 : e6ToF4 β (2 : Fin 4) = β 2 + β 4 := rfl
  have f3 : e6ToF4 β (3 : Fin 4) = β 0 + β 5 := rfl
  simp only [Fin.sum_univ_six, Fin.sum_univ_four, e0, e1, e2, e3, e4, e5, f0, f1, f2, f3]
  split_ifs <;> ring

theorem parabolicDegree_e6_eq (A : Set (Fin Tag.F4.rank)) (β : Fin TwistTag.E6.tag.rank → ℤ) :
    parabolicDegree TwistTag.E6.tag (A6 A) β = parabolicDegree Tag.F4 A (e6ToF4 β) := by
  classical
  unfold parabolicDegree
  simp only [mem_A6_iff]
  exact sum_e6_eq (fun j => j ∈ A) β

theorem mem_parabolicRadicalRoots_e6_iff (A : Set (Fin Tag.F4.rank))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    β ∈ parabolicRadicalRoots TwistTag.E6.tag (A6 A) ↔
      relProj β ∈ parabolicRadicalRoots Tag.F4 A := by
  constructor
  · intro h
    have hd := one_le_parabolicDegree_of_mem h
    refine mem_parabolicRadicalRoots_of_degree (isRoot_relProj hβ) ?_ ?_
    · rw [height_relProj]; exact h.1.2
    · change parabolicDegree Tag.F4 A (e6ToF4 β) ≠ 0
      rw [← parabolicDegree_e6_eq]; omega
  · intro h
    have hd := one_le_parabolicDegree_of_mem h
    refine mem_parabolicRadicalRoots_of_degree hβ ?_ ?_
    · rw [← height_relProj]; exact h.1.2
    · change parabolicDegree Tag.F4 A (e6ToF4 β) ≥ 1 at hd
      rw [parabolicDegree_e6_eq]; omega

theorem e6ToF4_single : ∀ i : Fin Tag.E6.rank,
    e6ToF4 (Pi.single i 1) = Pi.single (e6IndexToF4 i) 1 := by
  decide +kernel

theorem f4UnfoldIndex_f4FoldedIndex (j : Fin Tag.F4.rank) :
    f4UnfoldIndex (f4FoldedIndex j) = j := by
  fin_cases j <;> rfl

theorem relFibre_single (j : Fin Tag.F4.rank) :
    relFibre (Pi.single j 1) =
      (fun i : Fin TwistTag.E6.tag.rank => (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) ''
        ↑(TwistTag.E6.orbit (f4FoldedIndex j)) := by
  have hrep : relProj (Pi.single (f4IndexRep j) 1) = Pi.single j 1 :=
    (e6ToF4_single (f4IndexRep j)).trans
      (congrArg (fun k => (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) (e6IndexToF4_f4IndexRep j))
  have hfib : relFibre (Pi.single j 1) =
      ↑(TwistTag.E6.diagramOrbit (Pi.single (f4IndexRep j) 1)) := by
    rw [← hrep]
    exact relFibre_relProj (isRoot_single _ _)
  rw [hfib, diagramOrbit_eq_pair]
  ext β
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_image, Finset.mem_coe]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, (TwistTag.E6.mem_orbit_iff).2 (orbitIndex_f4IndexRep j), rfl⟩
    · exact ⟨_, (TwistTag.E6.mem_orbit_iff).2 (orbitIndex_perm_f4IndexRep j),
        (permLattice_single _ _).symm⟩
  · rintro ⟨i, hi, rfl⟩
    have hij : e6IndexToF4 i = j :=
      e6IndexToF4_eq_of_orbitIndex ((TwistTag.E6.mem_orbit_iff).1 hi).symm
    rcases f4IndexRep_e6IndexToF4 i with h | h
    · rw [hij] at h
      exact Or.inl (by rw [← h])
    · rw [hij] at h
      refine Or.inr ?_
      have h' : TwistTag.E6.perm (f4IndexRep j) = i := by
        rw [show TwistTag.E6.perm (f4IndexRep j) = rhoE6 (f4IndexRep j) from rfl, h]
        exact rhoE6_rhoE6 i
      have hp := permLattice_single TwistTag.E6.perm (f4IndexRep j)
      rw [h'] at hp
      exact hp.symm

theorem nE_mem (i : Fin Tag.F4.rank) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i) ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  canonicalRep_mem_twistedFixedGroup TwistTag.E6 K (RingHom.id K)
    ((mem_relWeylTwist TwistTag.E6).1 (isLift_nativeRefl i).1)

theorem coe_nE (i : Fin Tag.F4.rank) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i) =
      f4OrbitXUnit K i 1 * f4OrbitYUnit K i (-1) * f4OrbitXUnit K i 1 := by
  have h : nativeReflT i = TwistTag.E6.orbitReflection (f4FoldedIndex i) := by
    change nativeRefl i = _
    rw [nativeRefl_eq i]
    congr 1
    fin_cases i <;> rfl
  rw [h, canonicalRep_orbitReflection_eq_orbitN TwistTag.E6 (RingHom.id K) (f4FoldedIndex i)]
  simp only [orbitN, Subgroup.coe_mul, coe_orbitX_id, coe_orbitY_id,
    f4UnfoldIndex_f4FoldedIndex]
  simp

theorem phi_nE (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) :
    e6FixedToF4 K ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i), nE_mem i⟩ =
      weylElt Tag.F4 K i 1 := by
  have h : (⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i), nE_mem i⟩ :
      ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) =
      ⟨f4OrbitXUnit K i 1, f4OrbitXUnit_mem i 1⟩ *
        ⟨f4OrbitYUnit K i (-1), f4OrbitYUnit_mem i (-1)⟩ *
          ⟨f4OrbitXUnit K i 1, f4OrbitXUnit_mem i 1⟩ := Subtype.ext (coe_nE i)
  rw [h, map_mul, map_mul, e6FixedToF4_f4OrbitXUnit h2, e6FixedToF4_f4OrbitYUnit h2,
    CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (n x : G) :
    x ∈ H.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * x * n ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨n⁻¹ * x * n, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem phi_mem_rootSubgroup_iff (h2 : (2 : K) = 0) {r : Fin Tag.F4.rank → ℤ}
    (hr : IsRoot Tag.F4 r) (g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) :
    e6FixedToF4 K g ∈ rootSubgroup Tag.F4 K r ↔
      (g : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K (relFibre r) := by
  induction hr generalizing g with
  | basis j =>
    rw [relFibre_single]
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hg
      rw [pinnedX_single] at hc
      have hgc : g = ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩ :=
        phi_injective h2 (by rw [e6FixedToF4_f4OrbitXUnit h2]; exact hc.symm)
      rw [hgc]
      show f4OrbitXUnit K j c ∈ _
      rw [f4OrbitXUnit_eq_orbitX]
      exact (Subgroup.mem_inf.1 (orbitX_mem TwistTag.E6 (RingHom.id K) _ _)).1
    · intro hg
      obtain ⟨c, hc⟩ := exists_orbitX_eq hg
        ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 g.2).2
      rw [coe_orbitX_id, f4UnfoldIndex_f4FoldedIndex] at hc
      have hgc : g = ⟨f4OrbitXUnit K j (c : K), f4OrbitXUnit_mem j (c : K)⟩ :=
        Subtype.ext hc.symm
      rw [hgc, e6FixedToF4_f4OrbitXUnit h2, ← pinnedX_single]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
  | @reflect i r hr ih =>
    have hF : rootSubgroup Tag.F4 K (reflect Tag.F4 i r) =
        (rootSubgroup Tag.F4 K r).map (MulAut.conj (weylElt Tag.F4 K i 1)).toMonoidHom :=
      (map_conj_weylElt_rootSubgroup K i hr).symm
    have hfib : relFibre (reflect Tag.F4 i r) = (fun β => nativeReflT i • β) '' relFibre r := by
      rw [← simple_smul]
      exact relFibre_smul (isLift_nativeRefl i) r
    have hE : (rootSpan TwistTag.E6.tag K (relFibre r)).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i))).toMonoidHom =
          rootSpan TwistTag.E6.tag K (relFibre (reflect Tag.F4 i r)) := by
      rw [hfib]
      exact (canonical_weyl_root_transport TwistTag.E6.tag K).1 (nativeReflT i) _
        (relFibre_subset_isRoot r)
    rw [hF, ← hE, mem_map_conj_iff, mem_map_conj_iff]
    have hφ : (weylElt Tag.F4 K i 1)⁻¹ * e6FixedToF4 K g * weylElt Tag.F4 K i 1 =
        e6FixedToF4 K
          ((⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i), nE_mem i⟩ :
            ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)))⁻¹ * g *
          ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K (nativeReflT i), nE_mem i⟩) := by
      rw [map_mul, map_mul, map_inv, phi_nE h2 i]
    rw [hφ, ih]
    rfl

theorem rootSubgroup_le_rootSpan' {τ : Tag} {R : Type*} [CommRing R]
    {S : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ} (hα : α ∈ S) :
    rootSubgroup τ R α ≤ rootSpan τ R S :=
  le_iSup₂_of_le α hα le_rfl

theorem parabolicDegree_relProj (A : Set (Fin Tag.F4.rank))
    (β : Fin TwistTag.E6.tag.rank → ℤ) :
    parabolicDegree Tag.F4 A (relProj β) = parabolicDegree TwistTag.E6.tag (A6 A) β :=
  (parabolicDegree_e6_eq A β).symm

theorem f4OrbitXUnit_mem_parabolicLevi {A : Set (Fin Tag.F4.rank)} {j : Fin Tag.F4.rank}
    (hj : j ∈ A) (c : K) : f4OrbitXUnit K j c ∈ parabolicLevi TwistTag.E6.tag K (A6 A) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  refine xUnit_mem_parabolicLevi ((mem_A6_iff A i).2 ?_) c
  rw [e6IndexToF4_eq_of_orbitIndex
    ((TwistTag.E6.mem_orbit_iff).1 ((TwistTag.E6.mem_orbitWord).1 hi)).symm]
  exact hj

theorem f4OrbitYUnit_mem_parabolicLevi {A : Set (Fin Tag.F4.rank)} {j : Fin Tag.F4.rank}
    (hj : j ∈ A) (c : K) : f4OrbitYUnit K j c ∈ parabolicLevi TwistTag.E6.tag K (A6 A) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  refine yUnit_mem_parabolicLevi ((mem_A6_iff A i).2 ?_) c
  rw [e6IndexToF4_eq_of_orbitIndex
    ((TwistTag.E6.mem_orbit_iff).1 ((TwistTag.E6.mem_orbitWord).1 hi)).symm]
  exact hj

theorem coe_orbitN_id (j : Fin Tag.F4.rank)
    (u : (orbitField TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j))ˣ) :
    (orbitN TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j) u : ModGL TwistTag.E6.tag K) =
      f4OrbitXUnit K j ((u : orbitField TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j)) : K) *
        f4OrbitYUnit K j (-(((u⁻¹ : (orbitField TwistTag.E6 K (RingHom.id K)
          (f4FoldedIndex j))ˣ) : orbitField TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j)) :
            K)) *
          f4OrbitXUnit K j ((u : orbitField TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j)) :
            K) := by
  simp only [orbitN, Subgroup.coe_mul, coe_orbitX_id, coe_orbitY_id,
    f4UnfoldIndex_f4FoldedIndex]
  simp

theorem torusElt_F4_exists (h2 : (2 : K) = 0) (j : Fin Tag.F4.rank) (t : Kˣ) :
    ∃ g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
      (g : ModGL TwistTag.E6.tag K) ∈ torusGroup TwistTag.E6.tag K ∧
        e6FixedToF4 K g = torusElt Tag.F4 K j t := by
  classical
  set a := f4FoldedIndex j with ha
  let c : orbitField TwistTag.E6 K (RingHom.id K) a := ⟨(t : K), mem_orbitField_id a (t : K)⟩
  have hc : c ≠ 0 := fun h => t.ne_zero (congrArg Subtype.val h)
  let u : (orbitField TwistTag.E6 K (RingHom.id K) a)ˣ := Units.mk0 c hc
  have hHΓ : (orbitH TwistTag.E6 K (RingHom.id K) a u : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
    (e6_twistedFixedGroup_id_eq_graphFixedRootGroup K).ge
      (orbitH_mem_graphFixedRootGroup TwistTag.E6 (RingHom.id K) a u)
  refine ⟨⟨_, hHΓ⟩, ?_, ?_⟩
  · show (orbitH TwistTag.E6 K (RingHom.id K) a u : ModGL TwistTag.E6.tag K) ∈ _
    rw [coe_orbitH_eq]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨(i, _), rfl⟩
  · let X : K → ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :=
      fun c => ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩
    let Y : K → ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :=
      fun c => ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩
    have hX : ∀ c, e6FixedToF4 K (X c) = xUnit Tag.F4 K j c := e6FixedToF4_f4OrbitXUnit h2 j
    have hY : ∀ c, e6FixedToF4 K (Y c) = yUnit Tag.F4 K j c := e6FixedToF4_f4OrbitYUnit h2 j
    let N : Kˣ → ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :=
      fun s => X (s : K) * Y (-((s⁻¹ : Kˣ) : K)) * X (s : K)
    have hN : ∀ s : Kˣ, e6FixedToF4 K (N s) = weylElt Tag.F4 K j s := fun s => by
      rw [map_mul, map_mul, hX, hY, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    have hg : (⟨_, hHΓ⟩ : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) =
        N t * (N 1)⁻¹ := by
      apply Subtype.ext
      show (orbitH TwistTag.E6 K (RingHom.id K) a u : ModGL TwistTag.E6.tag K) = _
      rw [orbitH, Subgroup.coe_mul, Subgroup.coe_inv, coe_orbitN_id, coe_orbitN_id]
      simp [N, X, Y, u, c]
    rw [hg, map_mul, map_inv, hN, hN, weylElt_inv]
    rfl

theorem mem_parabolicLevi_e6_of_phi (h2 : (2 : K) = 0) (A : Set (Fin Tag.F4.rank))
    {g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))}
    (hg : e6FixedToF4 K g ∈ parabolicLevi Tag.F4 K A) :
    (g : ModGL TwistTag.E6.tag K) ∈ parabolicLevi TwistTag.E6.tag K (A6 A) := by
  have hle : parabolicLevi Tag.F4 K A ≤
      ((parabolicLevi TwistTag.E6.tag K (A6 A)).subgroupOf
        (twistedFixedGroup TwistTag.E6 K (RingHom.id K))).map (e6FixedToF4 K) := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨⟨j, t⟩, rfl⟩
      obtain ⟨g', hg'T, hg'⟩ := torusElt_F4_exists h2 j t
      exact ⟨g', Subgroup.mem_subgroupOf.2 (torusGroup_le_parabolicLevi _ hg'T), hg'⟩
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · exact ⟨⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩,
          Subgroup.mem_subgroupOf.2 (f4OrbitXUnit_mem_parabolicLevi hj c),
          e6FixedToF4_f4OrbitXUnit h2 j c⟩
      · exact ⟨⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩,
          Subgroup.mem_subgroupOf.2 (f4OrbitYUnit_mem_parabolicLevi hj c),
          e6FixedToF4_f4OrbitYUnit h2 j c⟩
  obtain ⟨g', hg', hgg⟩ := hle hg
  rw [phi_injective h2 hgg] at hg'
  exact Subgroup.mem_subgroupOf.1 hg'

theorem mem_parabolicRadical_e6_of_phi (h2 : (2 : K) = 0) (A : Set (Fin Tag.F4.rank))
    {g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))}
    (hg : e6FixedToF4 K g ∈ parabolicRadical Tag.F4 K A) :
    (g : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K (A6 A) := by
  have hle : parabolicRadical Tag.F4 K A ≤
      ((parabolicRadical TwistTag.E6.tag K (A6 A)).subgroupOf
        (twistedFixedGroup TwistTag.E6 K (RingHom.id K))).map (e6FixedToF4 K) := by
    show rootSpan Tag.F4 K (parabolicRadicalRoots Tag.F4 A) ≤ _
    refine iSup₂_le fun r hr => ?_
    intro x hx
    obtain ⟨g', rfl⟩ := phi_surj h2 (rootSubgroup_le_adjointGroup r hx)
    refine ⟨g', Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    have hx' := (phi_mem_rootSubgroup_iff h2 hr.1.1 g').1 hx
    refine rootSpan_mono ?_ hx'
    intro β hβ
    refine (mem_parabolicRadicalRoots_e6_iff A hβ.1).2 ?_
    rw [hβ.2]
    exact hr
  obtain ⟨g', hg', hgg⟩ := hle hg
  rw [phi_injective h2 hgg] at hg'
  exact Subgroup.mem_subgroupOf.1 hg'

theorem mem_parabolicRadical_f4_of_mem (h2 : (2 : K) = 0) (A : Set (Fin Tag.F4.rank))
    (g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)))
    (hg : (g : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K (A6 A)) :
    e6FixedToF4 K g ∈ parabolicRadical Tag.F4 K A := by
  classical
  have hfin : (parabolicRadicalRoots Tag.F4 A).Finite :=
    (finite_setOf_isRoot Tag.F4).subset fun r hr => hr.1.1
  obtain ⟨k, e, he⟩ := hfin.fin_embedding
  have hmem : ∀ j, e j ∈ parabolicRadicalRoots Tag.F4 A := fun j => by
    rw [← he]; exact Set.mem_range_self j
  have hpos : ∀ j, IsRoot Tag.F4 (e j) := fun j => (hmem j).1.1
  obtain ⟨O, hO⟩ : ∃ O : Fin k → Finset (Fin TwistTag.E6.tag.rank → ℤ),
      ∀ j, (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) = relFibre (e j) :=
    ⟨fun j => (relFibre_finite (e j)).toFinset, fun j => Set.Finite.coe_toFinset _⟩
  have hOinj : Function.Injective O := by
    intro i j hij
    obtain ⟨β, hβ, hβr, -⟩ := exists_relProj_fibre (hpos i)
    have hmem' : β ∈ relFibre (e i) := ⟨hβ, hβr⟩
    rw [← hO i, hij, hO j] at hmem'
    exact e.injective (hβr.symm.trans hmem'.2)
  have hOrange : Set.range O = {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
      (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆
        parabolicRadicalRoots TwistTag.E6.tag (A6 A)} := by
    ext O'
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨α, hα, hαr, hfib⟩ := exists_relFibre_eq (hpos j)
      refine ⟨⟨α, hα, Finset.coe_injective (hfib.symm.trans (hO j).symm)⟩, fun β hβ => ?_⟩
      rw [hO j] at hβ
      refine (mem_parabolicRadicalRoots_e6_iff A hβ.1).2 ?_
      rw [hβ.2]
      exact hmem j
    · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
      have hαR := hsub (TwistTag.E6.self_mem_diagramOrbit α)
      have hr : relProj α ∈ Set.range e := by
        rw [he]; exact (mem_parabolicRadicalRoots_e6_iff A hα).1 hαR
      obtain ⟨j, hj⟩ := hr
      exact ⟨j, Finset.coe_injective (by rw [hO j, hj, relFibre_relProj hα])⟩
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) (σ := RingHom.id K)
    (fun x => ⟨x, rfl⟩) (S := parabolicRadicalRoots TwistTag.E6.tag (A6 A))
    (fun α hα => hα.1) (fun α hα => permLattice_mem_parabolicRadicalRoots hα)
    (fun α hα β hβ a b ha hb hr => add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr)
    O hOinj hOrange
  obtain ⟨u, -, hu⟩ := hbij.2.2 (Subgroup.mem_inf.2 ⟨hg, g.2⟩)
  have hΓmem : ∀ j, (u j : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := fun j => (Subgroup.mem_inf.1 (u j).2).2
  let v : Fin k → ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :=
    fun j => ⟨u j, hΓmem j⟩
  have hgv : g = (List.ofFn v).prod := Subtype.ext (by
    rw [Subgroup.val_list_prod, List.map_ofFn]
    exact hu.symm)
  rw [hgv, map_list_prod, List.map_ofFn]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOspan : ∀ z : ModGL TwistTag.E6.tag K,
      z ∈ rootSpan TwistTag.E6.tag K (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) →
        z ∈ rootSpan TwistTag.E6.tag K (relFibre (e j)) := fun z hz => by
    rw [← hO j]
    exact hz
  have hj : (v j : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K (relFibre (e j)) :=
    hOspan _ (Subgroup.mem_inf.1 (u j).2).1
  exact rootSubgroup_le_rootSpan' (R := K) (hmem j)
    ((phi_mem_rootSubgroup_iff h2 (hpos j) (v j)).2 hj)

theorem conj_phi_rootSubgroup_neg (h2 : (2 : K) = 0) {w₀ : WeylGroup Tag.F4}
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) {w' : WeylGroup TwistTag.E6.tag}
    (hw' : IsLift w₀ w')
    (ν : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)))
    (hν : (ν : ModGL TwistTag.E6.tag K) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w')
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot Tag.F4 r) {x : ModGL Tag.F4 K}
    (hx : x ∈ rootSubgroup Tag.F4 K r) :
    (e6FixedToF4 K ν)⁻¹ * x * e6FixedToF4 K ν ∈ rootSubgroup Tag.F4 K (-r) := by
  obtain ⟨y, rfl⟩ := phi_surj h2 (rootSubgroup_le_adjointGroup r hx)
  have hy := (phi_mem_rootSubgroup_iff h2 hr y).1 hx
  have hφ : (e6FixedToF4 K ν)⁻¹ * e6FixedToF4 K y * e6FixedToF4 K ν =
      e6FixedToF4 K (ν⁻¹ * y * ν) := by
    rw [map_mul, map_mul, map_inv]
  rw [hφ, phi_mem_rootSubgroup_iff h2 (IsRoot.neg hr)]
  have hfib : relFibre r = (fun β => w' • β) '' relFibre (-r) := by
    have h := relFibre_smul hw' (-r)
    rwa [hw₀, neg_neg] at h
  have hE : (rootSpan TwistTag.E6.tag K (relFibre (-r))).map
      (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom =
        rootSpan TwistTag.E6.tag K (relFibre r) := by
    rw [hfib]
    exact (canonical_weyl_root_transport TwistTag.E6.tag K).1 w' _ (relFibre_subset_isRoot (-r))
  rw [← hE, mem_map_conj_iff, ← hν] at hy
  exact hy

theorem phi_mem_oppRadical (h2 : (2 : K) = 0) (A : Set (Fin Tag.F4.rank))
    (g : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)))
    (hg : (g : ModGL TwistTag.E6.tag K) ∈ oppRadical TwistTag.E6.tag K (A6 A)) :
    e6FixedToF4 K g ∈ oppRadical Tag.F4 K A := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : WeylGroup Tag.F4, ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v :=
    ⟨CFSG.LieType.Ree.ReeTag.F4.negOne, CFSG.LieType.Ree.ReeTag.negOne_smul .F4⟩
  obtain ⟨w', hw'⟩ := exists_relWeylTwist_lift w₀
  have hnΓ : canonicalRep (coxeterSystem TwistTag.E6.tag) K w' ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
    canonicalRep_mem_twistedFixedGroup TwistTag.E6 K (RingHom.id K)
      ((mem_relWeylTwist TwistTag.E6).1 hw'.1)
  set ν : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :=
    ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K w', hnΓ⟩ with hνdef
  have hroots : ∀ β ∈ oppRadicalRoots TwistTag.E6.tag (A6 A),
      w' • β ∈ parabolicRadicalRoots TwistTag.E6.tag (A6 A) := by
    intro β hβ
    have hβr := isRoot_of_mem_oppRadicalRoots hβ
    have hrel : relProj (w' • β) = -relProj β := by rw [hw'.2 β, hw₀]
    have hd := one_le_parabolicDegree_of_mem hβ
    refine mem_parabolicRadicalRoots_of_degree (IsRoot.smul hβr w') ?_ ?_
    · have h1 := hβ.1.2
      rw [height_neg] at h1
      rw [← height_relProj (w' • β), hrel, height_neg, height_relProj]
      exact h1
    · rw [← parabolicDegree_relProj A (w' • β), hrel, parabolicDegree_neg,
        parabolicDegree_relProj A β]
      rw [parabolicDegree_neg] at hd
      omega
  have h1 : ((ν * g * ν⁻¹ : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) :
      ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K (A6 A) := by
    have hmap : (oppRadical TwistTag.E6.tag K (A6 A)).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom ≤
          parabolicRadical TwistTag.E6.tag K (A6 A) := by
      rw [oppRadical, (canonical_weyl_root_transport TwistTag.E6.tag K).1 w' _
        (fun α hα => isRoot_of_mem_oppRadicalRoots hα)]
      exact rootSpan_mono (by rintro _ ⟨β, hβ, rfl⟩; exact hroots β hβ)
    exact hmap ⟨_, hg, rfl⟩
  have h2' := mem_parabolicRadical_f4_of_mem h2 A _ h1
  have hconj : (e6FixedToF4 K ν)⁻¹ * e6FixedToF4 K (ν * g * ν⁻¹) * e6FixedToF4 K ν =
      e6FixedToF4 K g := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [← hconj]
  have hle : parabolicRadical Tag.F4 K A ≤ (oppRadical Tag.F4 K A).comap
      (MulAut.conj (e6FixedToF4 K ν)⁻¹).toMonoidHom := by
    show rootSpan Tag.F4 K (parabolicRadicalRoots Tag.F4 A) ≤ _
    refine iSup₂_le fun r hr x hx => ?_
    have hmem := conj_phi_rootSubgroup_neg h2 hw₀ hw' ν rfl hr.1.1 hx
    rw [Subgroup.mem_comap]
    have hneg' : -r ∈ oppRadicalRoots Tag.F4 A := by
      show -(-r) ∈ parabolicRadicalRoots Tag.F4 A
      rw [neg_neg]
      exact hr
    refine rootSubgroup_le_rootSpan' (R := K) hneg' ?_
    simpa [MulAut.conj_apply] using hmem
  simpa [MulAut.conj_apply] using hle h2'

end F4Dual

open F4Dual

theorem exists_fixed_mem_oppRadical_F4 [Finite K] [CharP K 2] {A : Set (Fin Tag.F4.rank)}
    {S : Subgroup (GamL Tag.F4 K)}
    (hS : ∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K ∧ s.left ∈ parabolicLevi Tag.F4 K A)
    (hodd : Odd (Nat.card S)) {u : ModGL Tag.F4 K} (hu : u ∈ parabolicRadical Tag.F4 K A)
    (hu1 : u ≠ 1) (hfix : ∀ s ∈ S, conjAct Tag.F4 K s u = u) :
    ∃ v ∈ oppRadical Tag.F4 K A, v ≠ 1 ∧ ∀ s ∈ S, conjAct Tag.F4 K s v = v := by
  classical
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨-, -, -, -, -, -, hσ, -⟩ := even_E6_pure_graph_fixed_group_exact_F4 K hK2
  have hφσ : ∀ (σ : RingAut K) (g g' : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))),
      (g' : ModGL TwistTag.E6.tag K) = fieldAutHom TwistTag.E6.tag K σ g →
        e6FixedToF4 K g' = fieldAutHom Tag.F4 K σ (e6FixedToF4 K g) :=
    fun σ g g' h => (hσ σ).2 g g' h
  have hΓσ : ∀ (σ : RingAut K) (g : ModGL TwistTag.E6.tag K),
      g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) →
        fieldAutHom TwistTag.E6.tag K σ g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
    fun σ g hg => (hσ σ).1 g hg
  have hSad : ∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K := fun s hs => (hS s hs).1
  choose lift hlift using fun (x : ModGL Tag.F4 K) (hx : x ∈ adjointGroup Tag.F4 K) =>
    phi_surj h2 hx
  let θ : ↥S → GamL TwistTag.E6.tag K := fun s =>
    ⟨(lift s.1.left (hSad s.1 s.2) : ModGL TwistTag.E6.tag K), s.1.right⟩
  have hθ : ∀ s t : ↥S, θ (s * t) = θ s * θ t := by
    intro s t
    refine SemidirectProduct.ext ?_ ?_
    · have hl : lift (s * t).1.left (hSad _ (s * t).2) =
          lift s.1.left (hSad s.1 s.2) *
            ⟨fieldAutHom TwistTag.E6.tag K s.1.right
                (lift t.1.left (hSad t.1 t.2) : ModGL TwistTag.E6.tag K),
              hΓσ _ _ (lift t.1.left (hSad t.1 t.2)).2⟩ := by
        apply phi_injective h2
        rw [hlift, map_mul, hlift, hφσ s.1.right (lift t.1.left (hSad t.1 t.2)) _ rfl, hlift]
        rfl
      exact congrArg Subtype.val hl
    · rfl
  let Θ : ↥S →* GamL TwistTag.E6.tag K := MonoidHom.mk' θ hθ
  have hΘinj : Function.Injective Θ := by
    intro s t h
    have hl := congrArg SemidirectProduct.left h
    have hr := congrArg SemidirectProduct.right h
    have hlift' : lift s.1.left (hSad s.1 s.2) = lift t.1.left (hSad t.1 t.2) := Subtype.ext hl
    have hleft : s.1.left = t.1.left := by
      rw [← hlift s.1.left (hSad s.1 s.2), ← hlift t.1.left (hSad t.1 t.2), hlift']
    exact Subtype.ext (SemidirectProduct.ext hleft hr)
  have hcard : Nat.card Θ.range = Nat.card S :=
    Nat.card_congr (MonoidHom.ofInjective hΘinj).toEquiv.symm
  have hodd' : Odd (Nat.card Θ.range) := hcard ▸ hodd
  have hconj : ∀ (s : ↥S) (z : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))),
      ∃ z' : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
        (z' : ModGL TwistTag.E6.tag K) = conjAct TwistTag.E6.tag K (Θ s) z ∧
          e6FixedToF4 K z' = conjAct Tag.F4 K (s : GamL Tag.F4 K) (e6FixedToF4 K z) := by
    intro s z
    let z₁ : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :=
      ⟨fieldAutHom TwistTag.E6.tag K s.1.right (z : ModGL TwistTag.E6.tag K), hΓσ _ _ z.2⟩
    refine ⟨lift s.1.left (hSad s.1 s.2) * z₁ * (lift s.1.left (hSad s.1 s.2))⁻¹, ?_, ?_⟩
    · rw [conjAct_apply]
      rfl
    · rw [map_mul, map_mul, map_inv, hlift, hφσ s.1.right z z₁ rfl, conjAct_apply]
      rfl
  have hu_ad : u ∈ adjointGroup Tag.F4 K := rootSpan_le_adjointGroup K _ hu
  have hu' : ((lift u hu_ad : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) :
      ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K (A6 A) :=
    mem_parabolicRadical_e6_of_phi h2 A (by rw [hlift]; exact hu)
  have hu1' : ((lift u hu_ad : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) :
      ModGL TwistTag.E6.tag K) ≠ 1 := by
    intro h
    apply hu1
    have h' : lift u hu_ad = 1 := Subtype.ext h
    rw [← hlift u hu_ad, h', map_one]
  have hfix' : ∀ s' ∈ Θ.range, conjAct TwistTag.E6.tag K s'
      ((lift u hu_ad : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) :
        ModGL TwistTag.E6.tag K) = (lift u hu_ad : ModGL TwistTag.E6.tag K) := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨z', hz', hφz'⟩ := hconj s (lift u hu_ad)
    have hz : z' = lift u hu_ad :=
      phi_injective h2 (by rw [hφz', hlift, hfix s s.2])
    rw [← hz', hz]
  have hSL : ∀ s' ∈ Θ.range, s'.left ∈ parabolicLevi TwistTag.E6.tag K
      (TwistTag.E6.orbitUnion (f4FoldedIndex '' A)) := by
    rintro _ ⟨s, rfl⟩
    exact mem_parabolicLevi_e6_of_phi h2 A (g := lift s.1.left (hSad s.1 s.2))
      (by rw [hlift]; exact (hS s.1 s.2).2)
  have hSΓ : ∀ s' ∈ Θ.range,
      twistHom TwistTag.E6 K ((1 : RingAut K) : K →+* K) s'.left = s'.left ∧
        s'.right * (1 : RingAut K) = (1 : RingAut K) * s'.right := by
    rintro _ ⟨s, rfl⟩
    exact ⟨((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (lift s.1.left (hSad s.1 s.2)).2).2, by simp⟩
  obtain ⟨w, hwQ, hw1, hwF, hwS⟩ := exists_fixed_mem_oppRadical_twisted (K := K) (1 : RingAut K)
    (fun c => rfl) (J := f4FoldedIndex '' A) (S := Θ.range) hSL hSΓ hodd' hu' hu1' hfix'
  have hwΓ : w ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨rootSpan_le_adjointGroup K _ hwQ, hwF⟩
  refine ⟨e6FixedToF4 K ⟨w, hwΓ⟩, phi_mem_oppRadical h2 A ⟨w, hwΓ⟩ hwQ, ?_, ?_⟩
  · intro h1
    have h' : (⟨w, hwΓ⟩ : ↥(twistedFixedGroup TwistTag.E6 K (RingHom.id K))) = 1 :=
      phi_injective h2 (by rw [h1, map_one])
    exact hw1 (congrArg Subtype.val h')
  · intro s hs
    obtain ⟨z', hz', hφz'⟩ := hconj ⟨s, hs⟩ ⟨w, hwΓ⟩
    have hz : z' = ⟨w, hwΓ⟩ := Subtype.ext (by rw [hz']; exact hwS _ ⟨⟨s, hs⟩, rfl⟩)
    rw [← hφz', hz]

end Cert

end CFSG.LieType.ChevTwo.Semi
