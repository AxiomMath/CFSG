module

public import CFSG.CharacterTheory.Wreathed.CentricClassification
public import CFSG.Dihedral.DihedralFusionChains
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily
public import CFSG.Dihedral.DihedralFusionDecomposition

public noncomputable section

namespace CFSG.Wreathed

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def ambientWreathSubgroup (S : Subgroup G) {m : ℕ}
    (e : S ≃* Wreath m) (P : Subgroup (Wreath m)) : Subgroup G :=
  (P.map e.symm.toMonoidHom).map S.subtype

theorem ambientWreathSubgroup_le (S : Subgroup G) {m : ℕ}
    (e : S ≃* Wreath m) (P : Subgroup (Wreath m)) :
    ambientWreathSubgroup S e P ≤ S :=
  Subgroup.map_subtype_le _

theorem ambientWreathSubgroup_transport (S U : Subgroup G) (hUS : U ≤ S) {m : ℕ}
    (e : S ≃* Wreath m) :
    ambientWreathSubgroup S e ((U.subgroupOf S).map e.toMonoidHom) = U := by
  unfold ambientWreathSubgroup
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  have hinner : ((U.subgroupOf S).map e.toMonoidHom).map e.symm.toMonoidHom =
      U.subgroupOf S := by
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  rw [hinner]
  exact Subgroup.map_subgroupOf_eq_of_le hUS

theorem fusion_map_conj {A : Type*} [Group A] (P : Subgroup A)
    (f : A →* G) (a : A) :
    (P.map (MulAut.conj a).toMonoidHom).map f =
      (P.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

theorem ambientWreathSubgroup_conj (S : Subgroup G) {m : ℕ}
    (e : S ≃* Wreath m) (P : Subgroup (Wreath m)) (w : Wreath m) :
    ambientWreathSubgroup S e (P.map (MulAut.conj w).toMonoidHom) =
      (ambientWreathSubgroup S e P).map
        (MulAut.conj ((e.symm w : S) : G)).toMonoidHom := by
  unfold ambientWreathSubgroup
  rw [fusion_map_conj P e.symm.toMonoidHom w]
  exact fusion_map_conj (P.map e.symm.toMonoidHom) S.subtype (e.symm w)

theorem centric_of_centralizer_le {m : ℕ} (P : Subgroup (Wreath m))
    (hP : Subgroup.centralizer (P : Set (Wreath m)) ≤ P) : IsCentric P := by
  unfold IsCentric
  ext g
  constructor
  · intro hg
    let gP : P := ⟨g, hP hg⟩
    refine Subgroup.mem_map.mpr ⟨gP, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hg x.val x.property
  · intro hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨x, hx⟩ : P))

theorem centric_subgroup_transport (S U : Subgroup G) (hUS : U ≤ S) {m : ℕ}
    (e : S ≃* Wreath m) (hcentric : subgroupCentralizerIn S U ≤ U) :
    IsCentric ((U.subgroupOf S).map e.toMonoidHom) := by
  apply centric_of_centralizer_le
  intro w hw
  let wS : S := e.symm w
  have hcentral : wS.val ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let xS : S := ⟨x, hUS hx⟩
    have hximage : e xS ∈ (U.subgroupOf S).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨xS, hx, rfl⟩
    have heq := Subgroup.mem_centralizer_iff.mp hw (e xS) hximage
    have hS : xS * wS = wS * xS := by
      apply e.injective
      simpa only [map_mul, show e wS = w from e.apply_symm_apply w] using heq
    exact congrArg Subtype.val hS
  have hwU : wS.val ∈ U := hcentric ⟨wS.property, hcentral⟩
  exact Subgroup.mem_map.mpr ⟨wS, hwU, e.apply_symm_apply w⟩

theorem extremal_two_group_step_replacement [Finite G]
    (S : Sylow 2 G) (U : Subgroup G) (hUext : HuppertExtremal S U)
    (hAut : IsPGroup 2 (MulAut U)) (h : G)
    (hh : h ∈ Subgroup.normalizer (U : Set G)) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧ s ∈ Subgroup.normalizer (U : Set G) ∧
      ∀ x ∈ U, s⁻¹ * x * s = h⁻¹ * x * h := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hUext.exists_sylow_normalizer
  let N := Subgroup.normalizer (U : Set G)
  obtain ⟨q, hq, hqeq⟩ := GorensteinWalter.hom_to_pGroup_image_on_sylow hAut
    U.normalizerMonoidHom Q (⟨h, hh⟩ : N)
  have hqS : (q : G) ∈ (S : Subgroup G) := by
    have hmem : (q : G) ∈ (Q : Subgroup N).map N.subtype :=
      Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hQ] at hmem
    exact hmem.1
  refine ⟨q, hqS, q.property, ?_⟩
  intro x hx
  have heq := DFunLike.congr_fun
    (congrArg MulEquiv.symm hqeq) (⟨x, hx⟩ : U)
  have hval := congrArg Subtype.val heq
  simpa only [Subgroup.normalizerMonoidHom_apply_symm_apply_coe] using hval

theorem centric_odd_automorphism_ambient (S U : Subgroup G) (hUS : U ≤ S)
    (n : ℕ) (hn : 2 ≤ n) (e : S ≃* Wreath (2 ^ n))
    (hcentric : subgroupCentralizerIn S U ≤ U)
    (hAut : ¬ IsPGroup 2 (MulAut U)) :
    U = ambientWreathSubgroup S e (Original.U (2 ^ n)) ∨
      ∃ s : S, U = rightConjugate
        (ambientWreathSubgroup S e (Original.V (2 ^ n))) (s : G) := by
  let U' := (U.subgroupOf S).map e.toMonoidHom
  let eU : U ≃* U' :=
    (Subgroup.subgroupOfEquivOfLe hUS).symm.trans
      ((U.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective)
  have hAut' : ¬ IsPGroup 2 (MulAut U') := by
    intro h
    exact hAut (h.of_equiv (MulAut.congr eU).symm)
  rcases centric_odd_automorphism_classification n hn U'
    (centric_subgroup_transport S U hUS e hcentric) hAut' with hbase | ⟨w, hw⟩
  · exact Or.inl ((ambientWreathSubgroup_transport S U hUS e).symm.trans
      (congrArg (ambientWreathSubgroup S e) hbase))
  · have hback : U' = (Original.V (2 ^ n)).map (MulAut.conj w⁻¹).toMonoidHom := by
      have hmap := congrArg (fun H : Subgroup (Wreath (2 ^ n)) =>
        H.map (MulAut.conj w⁻¹).toMonoidHom) hw
      have hid : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
          MonoidHom.id (Wreath (2 ^ n)) := by
        apply MonoidHom.ext
        intro x
        change w⁻¹ * (w * x * w⁻¹) * (w⁻¹)⁻¹ = x
        group
      rw [Subgroup.map_map, hid, Subgroup.map_id] at hmap
      exact hmap
    refine Or.inr ⟨e.symm w, ?_⟩
    calc
      U = ambientWreathSubgroup S e U' :=
        (ambientWreathSubgroup_transport S U hUS e).symm
      _ = ambientWreathSubgroup S e
          ((Original.V (2 ^ n)).map (MulAut.conj w⁻¹).toMonoidHom) :=
        congrArg (ambientWreathSubgroup S e) hback
      _ = rightConjugate (ambientWreathSubgroup S e (Original.V (2 ^ n)))
          ((e.symm w : S) : G) := by
        rw [ambientWreathSubgroup_conj]
        simp only [rightConjugate, Subgroup.conjBy, map_inv, Subgroup.coe_inv]

@[expose] def WreathedFusionStep (S : Subgroup G) {n : ℕ}
    (e : S ≃* Wreath (2 ^ n)) (T : Subgroup G) (h : G) : Prop :=
  (T = S ∧ h ∈ S) ∨
    (T = ambientWreathSubgroup S e (Original.U (2 ^ n)) ∧
      h ∈ Subgroup.normalizer (T : Set G)) ∨
    ((∃ s : S, T = rightConjugate
        (ambientWreathSubgroup S e (Original.V (2 ^ n))) (s : G)) ∧
      h ∈ Subgroup.normalizer (T : Set G))

theorem wreathedFusionStep_mem_normalizer {S T : Subgroup G} {n : ℕ}
    {e : S ≃* Wreath (2 ^ n)} {h : G} (hstep : WreathedFusionStep S e T h) :
    h ∈ Subgroup.normalizer (T : Set G) := by
  rcases hstep with ⟨rfl, hh⟩ | ⟨_, hh⟩ | ⟨_, hh⟩
  · exact Subgroup.le_normalizer hh
  · exact hh
  · exact hh

inductive WreathedFusionDecomposition (S : Subgroup G) {n : ℕ}
    (e : S ≃* Wreath (2 ^ n)) (P : Subgroup G) : G → Prop
  | one : WreathedFusionDecomposition S e P 1
  | tail {g h : G} {T : Subgroup G} :
      WreathedFusionDecomposition S e P g →
      T ≤ S → rightConjugate P g ≤ T → WreathedFusionStep S e T h →
      WreathedFusionDecomposition S e P (g * h)

theorem wreathedFusionDecomposition_of_huppert [Finite G]
    (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n) (e : S ≃* Wreath (2 ^ n))
    {P : Subgroup G} {g : G}
    (hchain : HuppertCentricConjugationDecomposition (S : Subgroup G)
      (HuppertExtremal S) P g) :
    ∃ z : G, WreathedFusionDecomposition (S : Subgroup G) e P z ∧
      ∀ x ∈ P, z⁻¹ * x * z = g⁻¹ * x * g := by
  induction hchain with
  | one => exact ⟨1, .one, by intro x _; rfl⟩
  | @tail g h T hprev hText hTS hcur hh hcentric ih =>
      obtain ⟨z, hz, hzg⟩ := ih
      have hcurz : rightConjugate P z ≤ T := by
        rw [GorensteinWalter.rightConjugate_eq_of_pointwise P hzg]
        exact hcur
      have himage (x : G) (hx : x ∈ P) : g⁻¹ * x * g ∈ T := hcur
        (Subgroup.mem_map.mpr ⟨x, hx, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
      by_cases hcentral : h ∈ Subgroup.centralizer (T : Set G)
      · refine ⟨z, hz, ?_⟩
        intro x hx
        have hcomm := Subgroup.mem_centralizer_iff.mp hcentral _ (himage x hx)
        have htrivial : h⁻¹ * (g⁻¹ * x * g) * h = g⁻¹ * x * g := by
          calc
            _ = h⁻¹ * ((g⁻¹ * x * g) * h) := by rw [mul_assoc]
            _ = h⁻¹ * (h * (g⁻¹ * x * g)) := by rw [hcomm]
            _ = g⁻¹ * x * g := by group
        calc
          z⁻¹ * x * z = g⁻¹ * x * g := hzg x hx
          _ = h⁻¹ * (g⁻¹ * x * g) * h := htrivial.symm
          _ = (g * h)⁻¹ * x * (g * h) := by group
      · have hcentricT := hcentric.resolve_right hcentral
        by_cases hAut : IsPGroup 2 (MulAut T)
        · obtain ⟨s, hsS, _hsT, hsh⟩ :=
            extremal_two_group_step_replacement S T hText hAut h hh
          refine ⟨z * s, .tail hz le_rfl (hcurz.trans hTS)
            (Or.inl ⟨rfl, hsS⟩), ?_⟩
          intro x hx
          calc
            (z * s)⁻¹ * x * (z * s) = s⁻¹ * (z⁻¹ * x * z) * s := by group
            _ = s⁻¹ * (g⁻¹ * x * g) * s := by rw [hzg x hx]
            _ = h⁻¹ * (g⁻¹ * x * g) * h := hsh _ (himage x hx)
            _ = (g * h)⁻¹ * x * (g * h) := by group
        · have hstep : WreathedFusionStep (S : Subgroup G) e T h := by
            rcases centric_odd_automorphism_ambient (S : Subgroup G) T hTS n hn e
              hcentricT hAut with hbase | hV
            · exact Or.inr (Or.inl ⟨hbase, hh⟩)
            · exact Or.inr (Or.inr ⟨hV, hh⟩)
          refine ⟨z * h, .tail hz hTS hcurz hstep, ?_⟩
          intro x hx
          calc
            (z * h)⁻¹ * x * (z * h) = h⁻¹ * (z⁻¹ * x * z) * h := by group
            _ = h⁻¹ * (g⁻¹ * x * g) * h := by rw [hzg x hx]
            _ = (g * h)⁻¹ * x * (g * h) := by group

theorem wreathed_fusion_decomposition [Finite G]
    (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n) (e : S ≃* Wreath (2 ^ n))
    (P : Subgroup G) (hPS : P ≤ (S : Subgroup G))
    (g : G) (hg : rightConjugate P g ≤ (S : Subgroup G)) :
    ∃ z : G, WreathedFusionDecomposition (S : Subgroup G) e P z ∧
      rightConjugate P z = rightConjugate P g ∧
      ∀ x ∈ P, z⁻¹ * x * z = g⁻¹ * x * g := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzg⟩ := wreathedFusionDecomposition_of_huppert S n hn e
    (HuppertExtremal.centric_conjugation_decomposition S hPS hg)
  exact ⟨z, hz, GorensteinWalter.rightConjugate_eq_of_pointwise P hzg, hzg⟩

theorem WreathedFusionDecomposition.exists_prefixes
    {S P : Subgroup G} {n : ℕ} {e : S ≃* Wreath (2 ^ n)} {z : G}
    (hPS : P ≤ S) (hchain : WreathedFusionDecomposition S e P z) :
    ∃ k : ℕ, ∃ prefixes : Fin (k + 1) → G,
      ∃ supports : Fin k → Subgroup G, ∃ actors : Fin k → G,
        prefixes 0 = 1 ∧ prefixes (Fin.last k) = z ∧
        (∀ i : Fin k, prefixes i.succ = prefixes i.castSucc * actors i) ∧
        (∀ i : Fin k, supports i ≤ S ∧
          rightConjugate P (prefixes i.castSucc) ≤ supports i ∧
          WreathedFusionStep S e (supports i) (actors i)) ∧
        ∀ i : Fin (k + 1), rightConjugate P (prefixes i) ≤ S := by
  induction hchain with
  | one =>
      refine ⟨0, fun _ => 1, Fin.elim0, Fin.elim0, rfl, rfl,
        (by intro i; exact i.elim0), (by intro i; exact i.elim0), ?_⟩
      intro i
      simpa only [rightConjugate, inv_one, Subgroup.conjBy_one] using hPS
  | @tail z h T hprev hTS hcur hallowed ih =>
      obtain ⟨k, prefixes, supports, actors, hfirst, hlast, hstep, hdata, hinside⟩ := ih
      let stepData (a : G) (T : Subgroup G) (b : G) : Prop :=
        T ≤ S ∧ rightConjugate P a ≤ T ∧ WreathedFusionStep S e T b
      let prefixes' : Fin (k + 2) → G := Fin.snoc prefixes (z * h)
      let supports' : Fin (k + 1) → Subgroup G := Fin.snoc supports T
      let actors' : Fin (k + 1) → G := Fin.snoc actors h
      refine ⟨k + 1, prefixes', supports', actors', ?_, ?_, ?_, ?_, ?_⟩
      · change prefixes' (0 : Fin (k + 1)).castSucc = 1
        simpa only [prefixes', Fin.snoc_castSucc] using hfirst
      · exact Fin.snoc_last _ _
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [prefixes', actors', Fin.succ_last, Fin.snoc_last,
            Fin.snoc_castSucc, hlast]
        · simpa only [prefixes', actors', Fin.succ_castSucc, Fin.snoc_castSucc]
            using hstep j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · change stepData (prefixes' (Fin.last k).castSucc)
            (supports' (Fin.last k)) (actors' (Fin.last k))
          dsimp only [supports', actors', prefixes']
          rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_castSucc, hlast]
          exact ⟨hTS, hcur, hallowed⟩
        · change stepData (prefixes' j.castSucc.castSucc)
            (supports' j.castSucc) (actors' j.castSucc)
          dsimp only [supports', actors', prefixes']
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hdata j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · dsimp only [prefixes']
          rw [Fin.snoc_last]
          have hh := wreathedFusionStep_mem_normalizer hallowed
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          have hyT : z⁻¹ * y * z ∈ T := hcur
            (Subgroup.mem_map.mpr ⟨y, hy, by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
          have hhinv := (Subgroup.normalizer (T : Set G)).inv_mem hh
          have himage := (Subgroup.mem_normalizer_iff.mp hhinv (z⁻¹ * y * z)).mp hyT
          apply hTS
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
            mul_inv_rev, mul_assoc] using himage
        · simpa only [prefixes', Fin.snoc_castSucc] using hinside j

structure WreathedFusionChain (S : Subgroup G) {n : ℕ}
    (e : S ≃* Wreath (2 ^ n)) (k : ℕ) where
  subgroups : Fin (k + 1) → Subgroup G
  supports : Fin k → Subgroup G
  automorphisms : (i : Fin k) → MulAut (supports i)
  subgroup_le : ∀ i, subgroups i ≤ S
  support_le : ∀ i, supports i ≤ S
  domain_le : ∀ i, subgroups i.castSucc ≤ supports i
  image_eq : ∀ i,
    (((subgroups i.castSucc).subgroupOf (supports i)).map
      (automorphisms i).toMonoidHom).map (supports i).subtype = subgroups i.succ
  realized : ∀ i, ∃ h : G, WreathedFusionStep S e (supports i) h ∧
    ∀ x : supports i, (automorphisms i x : G) = h⁻¹ * (x : G) * h

namespace WreathedFusionChain

variable {S : Subgroup G} {n k : ℕ} {e : S ≃* Wreath (2 ^ n)}
    (c : WreathedFusionChain S e k)

@[expose] def step (i : Fin k) : c.subgroups i.castSucc →* c.subgroups i.succ where
  toFun x := ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩, by
    rw [← c.image_eq i]
    exact Subgroup.mem_map.mpr
      ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩,
        Subgroup.mem_map.mpr ⟨⟨x, c.domain_le i x.property⟩, x.property, rfl⟩, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G)) (map_one (c.automorphisms i))
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G))
      (map_mul (c.automorphisms i) ⟨x, c.domain_le i x.property⟩
        ⟨y, c.domain_le i y.property⟩)

theorem step_coe (i : Fin k) (x : c.subgroups i.castSucc) :
    (c.step i x : G) =
      (c.automorphisms i ⟨x, c.domain_le i x.property⟩ : G) := rfl

@[expose] def prefixMap : (i : Fin (k + 1)) → c.subgroups 0 →* c.subgroups i :=
  Fin.induction (MonoidHom.id _) (fun i f => (c.step i).comp f)

theorem prefix_zero (x : c.subgroups 0) : c.prefixMap 0 x = x := by
  simp only [prefixMap, Fin.induction_zero, MonoidHom.id_apply]

theorem prefix_succ (i : Fin k) (x : c.subgroups 0) :
    c.prefixMap i.succ x = c.step i (c.prefixMap i.castSucc x) := by
  simp only [prefixMap, Fin.induction_succ, MonoidHom.comp_apply]

@[expose] def composite : c.subgroups 0 →* c.subgroups (Fin.last k) :=
  c.prefixMap (Fin.last k)

theorem composite_empty (c : WreathedFusionChain S e 0) (x : c.subgroups 0) :
    (c.composite x : G) = x :=
  congrArg Subtype.val (c.prefix_zero x)

theorem prefix_coe_eq
    (prefixes : Fin (k + 1) → G) (actors : Fin k → G)
    (hfirst : prefixes 0 = 1)
    (hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i)
    (ha : ∀ i, ∀ x : c.supports i,
      (c.automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i) :
    ∀ i, ∀ x : c.subgroups 0,
      (c.prefixMap i x : G) = (prefixes i)⁻¹ * (x : G) * prefixes i := by
  intro i
  refine Fin.induction ?_ (fun j ih => ?_) i
  · intro x
    rw [hfirst, c.prefix_zero]
    simp only [inv_one, one_mul, mul_one]
  · intro x
    rw [c.prefix_succ, c.step_coe, ha, ih, hstep]
    group

theorem subgroups_eq_rightConjugate
    (prefixes : Fin (k + 1) → G) (actors : Fin k → G)
    (hfirst : prefixes 0 = 1)
    (hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i)
    (ha : ∀ i, ∀ x : c.supports i,
      (c.automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i) :
    ∀ i, c.subgroups i = rightConjugate (c.subgroups 0) (prefixes i) := by
  intro i
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp only [hfirst, rightConjugate, inv_one, Subgroup.conjBy_one]
  · rw [← c.image_eq j,
      GorensteinWalter.support_automorphism_image_eq_rightConjugate (c.domain_le j)
        (c.automorphisms j) (actors j) (ha j), ih, hstep]
    simp only [rightConjugate, mul_inv_rev, Subgroup.conjBy_mul]

theorem exists_realizing_element :
    ∃ g : G, c.subgroups (Fin.last k) = rightConjugate (c.subgroups 0) g ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g := by
  classical
  choose actors _hallowed ha using c.realized
  let prefixes : Fin (k + 1) → G :=
    Fin.induction 1 (fun i g => g * actors i)
  have hfirst : prefixes 0 = 1 := Fin.induction_zero _ _
  have hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i :=
    fun i => Fin.induction_succ _ _ i
  refine ⟨prefixes (Fin.last k),
    c.subgroups_eq_rightConjugate prefixes actors hfirst hstep ha (Fin.last k), ?_⟩
  exact c.prefix_coe_eq prefixes actors hfirst hstep ha (Fin.last k)

end WreathedFusionChain

theorem WreathedFusionDecomposition.exists_chain
    {S P : Subgroup G} {n : ℕ} {e : S ≃* Wreath (2 ^ n)} {z : G}
    (hPS : P ≤ S) (hchain : WreathedFusionDecomposition S e P z) :
    ∃ k : ℕ, ∃ c : WreathedFusionChain S e k,
      c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = rightConjugate P z ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = z⁻¹ * (x : G) * z := by
  obtain ⟨k, prefixes, supports, actors, hfirst, hlast, hstep, hdata, hinside⟩ :=
    hchain.exists_prefixes hPS
  have hnormalizer : ∀ i, actors i ∈ Subgroup.normalizer (supports i : Set G) :=
    fun i => wreathedFusionStep_mem_normalizer (hdata i).2.2
  let automorphisms (i : Fin k) : MulAut (supports i) :=
    ((supports i).normalizerMonoidHom ⟨actors i, hnormalizer i⟩).symm
  have ha : ∀ i, ∀ x : supports i,
      (automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i :=
    fun i x => Subgroup.normalizerMonoidHom_apply_symm_apply_coe _ _ x
  let c : WreathedFusionChain S e k :=
    { subgroups := fun i => rightConjugate P (prefixes i)
      supports := supports
      automorphisms := automorphisms
      subgroup_le := hinside
      support_le := fun i => (hdata i).1
      domain_le := fun i => (hdata i).2.1
      image_eq := by
        intro i
        rw [GorensteinWalter.support_automorphism_image_eq_rightConjugate (hdata i).2.1
          (automorphisms i) (actors i) (ha i), hstep i]
        simp only [rightConjugate, mul_inv_rev, Subgroup.conjBy_mul]
      realized := fun i => ⟨actors i, (hdata i).2.2, ha i⟩ }
  refine ⟨k, c, ?_, ?_, ?_⟩
  · change rightConjugate P (prefixes 0) = P
    simp only [hfirst, rightConjugate, inv_one, Subgroup.conjBy_one]
  · change rightConjugate P (prefixes (Fin.last k)) = rightConjugate P z
    rw [hlast]
  · intro x
    have hx := c.prefix_coe_eq prefixes actors hfirst hstep ha (Fin.last k) x
    simpa only [WreathedFusionChain.composite, hlast] using hx

theorem wreathed_fusion_automorphism_chain [Finite G]
    (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n) (e : S ≃* Wreath (2 ^ n))
    (P : Subgroup G) (hPS : P ≤ (S : Subgroup G))
    (g : G) (hg : rightConjugate P g ≤ (S : Subgroup G)) :
    ∃ k : ℕ, ∃ c : WreathedFusionChain (S : Subgroup G) e k,
      c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = rightConjugate P g ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g := by
  obtain ⟨z, hz, himage, hpointwise⟩ := wreathed_fusion_decomposition S n hn e P hPS g hg
  obtain ⟨k, c, hfirst, hlast, hcomp⟩ := hz.exists_chain hPS
  refine ⟨k, c, hfirst, hlast.trans himage, ?_⟩
  intro x
  rw [hcomp x]
  exact hpointwise x (hfirst ▸ x.property)

theorem wreathed_fusion_generated_by_base_and_central_quaternion_normalizers [Finite G]
    (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n) (e : S ≃* Wreath (2 ^ n)) :
    (∀ (P : Subgroup G), P ≤ (S : Subgroup G) →
      ∀ (g : G), rightConjugate P g ≤ (S : Subgroup G) →
        ∃ k : ℕ, ∃ c : WreathedFusionChain (S : Subgroup G) e k,
          c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = rightConjugate P g ∧
          ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g) ∧
    (∀ (k : ℕ) (c : WreathedFusionChain (S : Subgroup G) e k),
      ∃ g : G, c.subgroups (Fin.last k) = rightConjugate (c.subgroups 0) g ∧
        ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g) := by
  exact ⟨wreathed_fusion_automorphism_chain S n hn e,
    fun _ c => c.exists_realizing_element⟩

end CFSG.Wreathed
