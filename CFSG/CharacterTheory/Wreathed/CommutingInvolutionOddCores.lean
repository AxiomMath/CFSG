module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.Wreathed

variable {G H : Type*} [Group G] [Group H]

theorem hom_eq_one_of_coprime_card {p : ℕ} [Fact p.Prime] [Finite G]
    (hcard : Nat.Coprime p (Nat.card G)) (hgroup : IsPGroup p H)
    (f : G →* H) (g : G) : f g = 1 := by
  by_contra hne
  have hdvd : p ∣ Nat.card G :=
    (hgroup.dvd_orderOf hne).trans ((orderOf_map_dvd f g).trans (orderOf_dvd_natCard g))
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcard hdvd

noncomputable def centralizerTransport (e : G ≃* H) (x : G) (y : H) (hxy : e x = y) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({y} : Set H) :=
  (e.subgroupMap (Subgroup.centralizer ({x} : Set G))).trans
    (MulEquiv.subgroupCongr (by
      simpa only [hxy, MulEquiv.toMonoidHom_eq_coe] using CFSG.centralizer_singleton_map e x))

@[simp]
theorem centralizerTransport_coe (e : G ≃* H) (x : G) (y : H) (hxy : e x = y)
    (g : Subgroup.centralizer ({x} : Set G)) :
    ((centralizerTransport e x y hxy g : Subgroup.centralizer ({y} : Set H)) : H) =
      e (g : G) := by
  simp [centralizerTransport]

@[simp]
theorem centralizerTransport_symm_coe (e : G ≃* H) (x : G) (y : H) (hxy : e x = y)
    (g : Subgroup.centralizer ({y} : Set H)) :
    ((centralizerTransport e x y hxy).symm g : G) = e.symm (g : H) := by
  apply e.injective
  rw [e.apply_symm_apply]
  have h := centralizerTransport_coe e x y hxy ((centralizerTransport e x y hxy).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

instance centralizerOddCoreRestriction_normal (y : G) :
    ((CFSG.pPrimeCore 2 G).comap (Subgroup.centralizer ({y} : Set G)).subtype).Normal :=
  Subgroup.normal_comap _

theorem centralizerOddCoreRestriction_map_eq (y : G)
    (hcentral : CFSG.pPrimeCore 2 G ≤ Subgroup.centralizer ({y} : Set G)) :
    ((CFSG.pPrimeCore 2 G).comap (Subgroup.centralizer ({y} : Set G)).subtype).map
        (Subgroup.centralizer ({y} : Set G)).subtype = CFSG.pPrimeCore 2 G :=
  Subgroup.map_subgroupOf_eq_of_le hcentral

theorem centralizerOddCoreRestriction_map (e : G ≃* H) (x : G) (y : H) (hxy : e x = y) :
    ((CFSG.pPrimeCore 2 G).comap (Subgroup.centralizer ({x} : Set G)).subtype).map
        (centralizerTransport e x y hxy).toMonoidHom =
      (CFSG.pPrimeCore 2 H).comap (Subgroup.centralizer ({y} : Set H)).subtype := by
  ext g
  rw [Subgroup.mem_map_equiv]
  change ((centralizerTransport e x y hxy).symm g : G) ∈ CFSG.pPrimeCore 2 G ↔
    (g : H) ∈ CFSG.pPrimeCore 2 H
  rw [centralizerTransport_symm_coe, ← CFSG.pPrimeCore_map_iso 2 e,
    Subgroup.mem_map_equiv]

theorem centralizerOddCoreQuotient_isPGroup_transport
    (e : G ≃* H) (x : G) (y : H) (hxy : e x = y)
    (hquot : IsPGroup 2 ((Subgroup.centralizer ({x} : Set G)) ⧸
      ((CFSG.pPrimeCore 2 G).comap (Subgroup.centralizer ({x} : Set G)).subtype))) :
    IsPGroup 2 ((Subgroup.centralizer ({y} : Set H)) ⧸
      ((CFSG.pPrimeCore 2 H).comap (Subgroup.centralizer ({y} : Set H)).subtype)) :=
  hquot.of_equiv (QuotientGroup.congr _ _ (centralizerTransport e x y hxy)
    (by simpa only [MulEquiv.toMonoidHom_eq_coe] using
      centralizerOddCoreRestriction_map e x y hxy))

theorem oddCore_le_centralizer_transport (e : G ≃* H) (y : G)
    (hcentral : CFSG.pPrimeCore 2 G ≤ Subgroup.centralizer ({y} : Set G)) :
    CFSG.pPrimeCore 2 H ≤ Subgroup.centralizer ({e y} : Set H) := by
  rw [← CFSG.pPrimeCore_map_iso 2 e, ← CFSG.centralizer_singleton_map e y]
  exact Subgroup.map_mono hcentral

structure InvolutionOddCoreLocalHypotheses (x : G) : Prop where
  centralizes : ∀ y : Subgroup.centralizer ({x} : Set G), orderOf y = 2 →
    CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) ≤
      Subgroup.centralizer ({y} : Set (Subgroup.centralizer ({x} : Set G)))
  quotient_two_group : ∀ y : Subgroup.centralizer ({x} : Set G), orderOf y = 2 →
    (y : G) ≠ x →
    IsPGroup 2 ((Subgroup.centralizer
      ({y} : Set (Subgroup.centralizer ({x} : Set G)))) ⧸
        ((CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).comap
          (Subgroup.centralizer
            ({y} : Set (Subgroup.centralizer ({x} : Set G)))).subtype))

theorem InvolutionOddCoreLocalHypotheses.coreRestriction_map_eq
    {x : G} (hlocal : InvolutionOddCoreLocalHypotheses x)
    (y : Subgroup.centralizer ({x} : Set G)) (hy : orderOf y = 2) :
    ((CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).comap
      (Subgroup.centralizer
        ({y} : Set (Subgroup.centralizer ({x} : Set G)))).subtype).map
          (Subgroup.centralizer
            ({y} : Set (Subgroup.centralizer ({x} : Set G)))).subtype =
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) :=
  centralizerOddCoreRestriction_map_eq y (hlocal.centralizes y hy)

theorem InvolutionOddCoreLocalHypotheses.transport
    {x : G} {x' : H} (hlocal : InvolutionOddCoreLocalHypotheses x)
    (e : G ≃* H) (hxx' : e x = x') : InvolutionOddCoreLocalHypotheses x' := by
  let f := centralizerTransport e x x' hxx'
  constructor
  · intro y hy
    have hz : orderOf (f.symm y) = 2 := by
      rw [f.symm.orderOf_eq, hy]
    have hcentral := oddCore_le_centralizer_transport f (f.symm y)
      (hlocal.centralizes (f.symm y) hz)
    simpa only [f.apply_symm_apply] using hcentral
  · intro y hy hne
    have hz : orderOf (f.symm y) = 2 := by
      rw [f.symm.orderOf_eq, hy]
    have hzne : ((f.symm y : Subgroup.centralizer ({x} : Set G)) : G) ≠ x := by
      intro heq
      apply hne
      calc
        (y : H) = e ((f.symm y : Subgroup.centralizer ({x} : Set G)) : G) := by
          have hval := centralizerTransport_coe e x x' hxx' (f.symm y)
          change ((f (f.symm y) : Subgroup.centralizer ({x'} : Set H)) : H) =
            e ((f.symm y : Subgroup.centralizer ({x} : Set G)) : G) at hval
          simpa only [f.apply_symm_apply] using hval
        _ = e x := congrArg e heq
        _ = x' := hxx'
    exact centralizerOddCoreQuotient_isPGroup_transport f (f.symm y) y
      (f.apply_symm_apply y) (hlocal.quotient_two_group (f.symm y) hz hzne)

theorem InvolutionOddCoreLocalHypotheses.of_isConj {x u : G}
    (hlocal : InvolutionOddCoreLocalHypotheses x) (hconj : IsConj x u) :
    InvolutionOddCoreLocalHypotheses u := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  exact hlocal.transport (MulAut.conj g) (by simpa only [MulAut.conj_apply] using hg)

def commutingOddCoreIntoDoubleCentralizer (u v : G) (hu : orderOf u = 2)
    (hcomm : Commute u v) (hvlocal : InvolutionOddCoreLocalHypotheses v) :
    CFSG.pPrimeCore 2 (Subgroup.centralizer ({v} : Set G)) →*
      Subgroup.centralizer
        ({(⟨v, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm⟩ :
          Subgroup.centralizer ({u} : Set G))} :
            Set (Subgroup.centralizer ({u} : Set G))) := by
  let uV : Subgroup.centralizer ({v} : Set G) :=
    ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq⟩
  have huV : orderOf uV = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu
  have hcentral := hvlocal.centralizes uV huV
  refine
    { toFun := fun r => ⟨⟨((r : Subgroup.centralizer ({v} : Set G)) : G), ?_⟩, ?_⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hr := Subgroup.mem_centralizer_singleton_iff.mp (hcentral r.property)
    exact congrArg (fun z : Subgroup.centralizer ({v} : Set G) => (z : G)) hr
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (r : Subgroup.centralizer ({v} : Set G)).property

theorem commutingInvolutionOddCore_le [Finite G] (u v : G)
    (hu : orderOf u = 2) (hv : orderOf v = 2) (hne : u ≠ v) (hcomm : Commute u v)
    (hulocal : InvolutionOddCoreLocalHypotheses u)
    (hvlocal : InvolutionOddCoreLocalHypotheses v) :
    (CFSG.pPrimeCore 2 (Subgroup.centralizer ({v} : Set G))).map
        (Subgroup.centralizer ({v} : Set G)).subtype ≤
      (CFSG.pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype := by
  let vU : Subgroup.centralizer ({u} : Set G) :=
    ⟨v, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm⟩
  let D : Subgroup (Subgroup.centralizer ({u} : Set G)) :=
    Subgroup.centralizer ({vU} : Set (Subgroup.centralizer ({u} : Set G)))
  let R : Subgroup D :=
    (CFSG.pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))).comap D.subtype
  let f := commutingOddCoreIntoDoubleCentralizer u v hu hcomm hvlocal
  have hvU : orderOf vU = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hv
  have hquot : IsPGroup 2 (D ⧸ R) := hulocal.quotient_two_group vU hvU hne.symm
  have hcoprime := CFSG.pPrimeCore_coprime_card
    (p := 2) (G := Subgroup.centralizer ({v} : Set G))
  intro g hg
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
  let r' : CFSG.pPrimeCore 2 (Subgroup.centralizer ({v} : Set G)) := ⟨r, hr⟩
  have hone : (QuotientGroup.mk' R) (f r') = 1 :=
    hom_eq_one_of_coprime_card hcoprime hquot ((QuotientGroup.mk' R).comp f) r'
  have hmem : f r' ∈ R := (QuotientGroup.eq_one_iff (f r')).mp hone
  exact Subgroup.mem_map.mpr ⟨(f r' : Subgroup.centralizer ({u} : Set G)), hmem, rfl⟩

theorem commuting_involution_odd_cores_eq [Finite G] (x : G) (hx : orderOf x = 2)
    (hclass : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hlocal : InvolutionOddCoreLocalHypotheses x) (u v : G)
    (hu : orderOf u = 2) (hv : orderOf v = 2) (hne : u ≠ v) (hcomm : Commute u v) :
    (CFSG.pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype =
      (CFSG.pPrimeCore 2 (Subgroup.centralizer ({v} : Set G))).map
        (Subgroup.centralizer ({v} : Set G)).subtype := by
  have hulocal := hlocal.of_isConj (hclass x u hx hu)
  have hvlocal := hlocal.of_isConj (hclass x v hx hv)
  exact le_antisymm
    (commutingInvolutionOddCore_le v u hv hu hne.symm hcomm.symm hvlocal hulocal)
    (commutingInvolutionOddCore_le u v hu hv hne hcomm hulocal hvlocal)

end CFSG.Wreathed
