module

public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.Background.PRankCommuteMod
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable def conjOnL (N L : Subgroup G) (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) : ↥N →* MulAut ↥L :=
  letI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe hLN)).toMonoidHom.comp
    (MulAut.conjNormal (G := ↥N) (H := L.subgroupOf N))

theorem conjOnL_apply (N L : Subgroup G) (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (n : ↥N) (l : ↥L) :
    conjOnL N L hLN hNL n l =
      (⟨(n : G) * (l : G) * (n : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL n.2) (l : G)).mp l.2⟩ : ↥L) := by
  letI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  apply Subtype.ext
  simp [conjOnL, MulAut.conjNormal_apply]

noncomputable def conjQuotAction (N L : Subgroup G) (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    ↥N →* MulAut (↥L ⧸ Q) :=
  (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient Q).comp
    (conjOnL N L hLN hNL)

theorem conjQuotAction_apply_mk (N L : Subgroup G) (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) (n : ↥N) (l : ↥L) :
    conjQuotAction N L Q hLN hNL n (QuotientGroup.mk' Q l) =
      QuotientGroup.mk' Q
        (⟨(n : G) * (l : G) * (n : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hNL n.2) (l : G)).mp l.2⟩ : ↥L) := by
  rw [conjQuotAction, MonoidHom.comp_apply,
    CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk, conjOnL_apply]

theorem conjQuotAction_apply_mem (N L : Subgroup G) (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) {n : ↥N} (hn : (n : G) ∈ L)
    (l : ↥L) :
    conjQuotAction N L Q hLN hNL n (QuotientGroup.mk' Q l) =
      MulAut.conj (QuotientGroup.mk' Q (⟨(n : G), hn⟩ : ↥L))
        (QuotientGroup.mk' Q l) := by
  rw [conjQuotAction_apply_mk, MulAut.conj_apply, ← map_mul, ← map_inv]
  rfl

private theorem mem_map_subtype_iff {L : Subgroup G} {Q : Subgroup ↥L} {y : ↥L} :
    (y : G) ∈ Q.map L.subtype ↔ y ∈ Q :=
  ⟨fun ⟨z, hz, hzy⟩ => (Subtype.ext hzy : z = y) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩

noncomputable def quotientCentralizer (N L : Subgroup G) (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) : Subgroup G :=
  (conjQuotAction N L Q hLN hNL).ker.map N.subtype

theorem mem_quotientCentralizer {N L : Subgroup G} (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) {x : G} :
    x ∈ quotientCentralizer N L Q hLN hNL ↔
      ∃ n : ↥N, (n : G) = x ∧ conjQuotAction N L Q hLN hNL n = 1 := by
  simp only [quotientCentralizer, Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, rfl, hn⟩
  · rintro ⟨n, rfl, hn⟩
    exact ⟨n, hn, rfl⟩

theorem quotientCentralizer_le (N L : Subgroup G) (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    quotientCentralizer N L Q hLN hNL ≤ N :=
  Subgroup.map_subtype_le _

theorem map_le_quotientCentralizer (N L : Subgroup G) (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    Q.map L.subtype ≤ quotientCentralizer N L Q hLN hNL := by
  intro q hq
  have hqL : q ∈ L := Subgroup.map_subtype_le Q hq
  have hqN : q ∈ N := hLN hqL
  have hqQ : (⟨q, hqL⟩ : ↥L) ∈ Q :=
    (mem_map_subtype_iff (L := L) (Q := Q)).mp hq
  refine (mem_quotientCentralizer Q hLN hNL).mpr ⟨⟨q, hqN⟩, rfl, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  change conjQuotAction N L Q hLN hNL ⟨q, hqN⟩ (QuotientGroup.mk' Q l) =
    QuotientGroup.mk' Q l
  rw [conjQuotAction_apply_mk]
  have hq1 : QuotientGroup.mk' Q (⟨q, hqL⟩ : ↥L) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hqQ
  have helem : (⟨(q : G) * l * (q : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hNL hqN) (l : G)).mp l.2⟩ : ↥L) =
      (⟨q, hqL⟩ : ↥L) * l * (⟨q, hqL⟩ : ↥L)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [helem, map_mul, map_mul, map_inv, hq1]
  simp

theorem commutator_mem_map_of_mem_quotientCentralizer {N L : Subgroup G}
    (Q : Subgroup ↥L) [Q.Characteristic] (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {x l : G}
    (hx : x ∈ quotientCentralizer N L Q hLN hNL) (hl : l ∈ L) :
    x * l * x⁻¹ * l⁻¹ ∈ Q.map L.subtype := by
  obtain ⟨n, hnx, hnker⟩ := (mem_quotientCentralizer Q hLN hNL).mp hx
  subst hnx
  have hone : conjQuotAction N L Q hLN hNL n
      (QuotientGroup.mk' Q (⟨l, hl⟩ : ↥L)) =
      QuotientGroup.mk' Q (⟨l, hl⟩ : ↥L) := by
    rw [hnker]
    rfl
  rw [conjQuotAction_apply_mk] at hone
  have hmem : (⟨l, hl⟩ : ↥L)⁻¹ *
      (⟨(n : G) * l * (n : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL n.2) l).mp hl⟩ : ↥L) ∈ Q :=
    QuotientGroup.eq.mp hone.symm
  have hmemG : (l : G)⁻¹ * (n : G) * l * (n : G)⁻¹ ∈ Q.map L.subtype := by
    simpa [mul_assoc] using mem_map_subtype_iff.mpr hmem
  have hLQ : L ≤ Subgroup.normalizer ((Q.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic Q)
  have hconj : (l : G) * ((l : G)⁻¹ * (n : G) * l * (n : G)⁻¹) * (l : G)⁻¹ ∈
      Q.map L.subtype :=
    (Subgroup.mem_normalizer_iff.mp (hLQ hl) _).mp hmemG
  simpa [mul_assoc] using hconj

theorem quotientCentralizer_inf_le {N L : Subgroup G} (Q : Subgroup ↥L) [Q.Characteristic]
    (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hcenter : Subgroup.center (↥L ⧸ Q) = ⊥) :
    quotientCentralizer N L Q hLN hNL ⊓ L ≤ Q.map L.subtype := by
  intro x hx
  obtain ⟨hxX, hxL⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hnx, hnker⟩ := (mem_quotientCentralizer Q hLN hNL).mp hxX
  have hnL : (n : G) ∈ L := hnx ▸ hxL
  have hn_eq : (⟨(n : G), hnL⟩ : ↥L) = ⟨x, hxL⟩ := Subtype.ext hnx
  have hz : QuotientGroup.mk' Q (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center (↥L ⧸ Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : conjQuotAction N L Q hLN hNL n (QuotientGroup.mk' Q l) =
        QuotientGroup.mk' Q l := by
      rw [hnker]
      rfl
    rw [conjQuotAction_apply_mem N L Q hLN hNL hnL l] at h1
    set z : ↥L ⧸ Q := QuotientGroup.mk' Q (⟨x, hxL⟩ : ↥L) with hzdef
    have h1' : z * (QuotientGroup.mk' Q l) * z⁻¹ = QuotientGroup.mk' Q l := by
      rw [hzdef]
      rw [← hn_eq]
      rwa [MulAut.conj_apply] at h1
    have h2 : z * (QuotientGroup.mk' Q l) = QuotientGroup.mk' Q l * z := by
      calc z * (QuotientGroup.mk' Q l) = (z * (QuotientGroup.mk' Q l) * z⁻¹) * z := by
            group
        _ = QuotientGroup.mk' Q l * z := by rw [h1']
    exact h2.symm
  rw [hcenter, Subgroup.mem_bot] at hz
  exact mem_map_subtype_iff.mpr ((QuotientGroup.eq_one_iff _).mp hz)

theorem perfect_le_sup_quotientCentralizer {N L K : Subgroup G} (Q : Subgroup ↥L)
    [Q.Characteristic] (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hKN : K ≤ N) (hKperf : Group.IsPerfect ↥K)
    (hOut : Group.IsSolvable (Outer (↥L ⧸ Q))) :
    K ≤ L ⊔ quotientCentralizer N L Q hLN hNL := by
  classical
  haveI : Group.IsPerfect ↥K := hKperf
  haveI : Group.IsSolvable (Outer (↥L ⧸ Q)) := hOut
  let ψ : ↥N →* Outer (↥L ⧸ Q) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (↥L ⧸ Q))).comp (conjQuotAction N L Q hLN hNL)
  have hψK : ψ.comp (Subgroup.inclusion hKN) = 1 :=
    CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one _
  intro k hk
  have hincl : (Subgroup.inclusion hKN) ⟨k, hk⟩ = ⟨k, hKN hk⟩ :=
    Subtype.ext (Subgroup.coe_inclusion hKN ⟨k, hk⟩)
  have hψk : ψ ⟨k, hKN hk⟩ = 1 := by
    have h := congrArg (fun f : ↥K →* Outer (↥L ⧸ Q) => f ⟨k, hk⟩) hψK
    simp only [MonoidHom.comp_apply] at h
    rw [hincl] at h
    simpa [ψ] using h
  have hinner : conjQuotAction N L Q hLN hNL ⟨k, hKN hk⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (↥L ⧸ Q) :=
    (QuotientGroup.eq_one_iff _).mp hψk
  obtain ⟨ybar, hybar⟩ := hinner
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective ybar
  have hℓ : conjQuotAction N L Q hLN hNL (⟨(l : G), hLN l.2⟩ : ↥N) =
      MulAut.conj (QuotientGroup.mk' Q l) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    simpa using conjQuotAction_apply_mem N L Q hLN hNL l.2 m
  have hzmem : (⟨k, hKN hk⟩ : ↥N) * (⟨(l : G), hLN l.2⟩ : ↥N)⁻¹ ∈
      (conjQuotAction N L Q hLN hNL).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hℓ, ← hybar]
    simp only [QuotientGroup.mk'_apply]
    exact mul_inv_cancel _
  have hzX : k * (l : G)⁻¹ ∈ quotientCentralizer N L Q hLN hNL :=
    (mem_quotientCentralizer Q hLN hNL).mpr
      ⟨(⟨k, hKN hk⟩ : ↥N) * (⟨(l : G), hLN l.2⟩ : ↥N)⁻¹, rfl, hzmem⟩
  have hz : k * (l : G)⁻¹ ∈ L ⊔ quotientCentralizer N L Q hLN hNL :=
    Subgroup.mem_sup_right hzX
  have hl : (l : G) ∈ L ⊔ quotientCentralizer N L Q hLN hNL :=
    Subgroup.mem_sup_left l.2
  have hk_eq : k = (k * (l : G)⁻¹) * (l : G) := by group
  rw [hk_eq]
  exact Subgroup.mul_mem _ hz hl

theorem inf_le_pCoreOf_of_quasisimple {N L K : Subgroup G} (hKN : K ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hKperf : Group.IsPerfect ↥K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcenter : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hKL : ¬ K ≤ L) :
    K ⊓ L ≤ CFSG.Open.pCoreOf 2 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ : Subgroup ↥K := (K ⊓ L).subgroupOf K with hM₀
  have hM₀normal : M₀.Normal :=
    Subgroup.Normal.mk fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2),
        (Subgroup.mem_normalizer_iff.mp (hNL (hKN g.2)) (n : G)).mp hn.2⟩
  haveI : M₀.Normal := hM₀normal
  set q : ↥K →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hqdef
  set Mimg : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := M₀.map q with hMimg
  have hMimg_normal : Mimg.Normal := hM₀normal.map q (QuotientGroup.mk'_surjective _)
  haveI : Mimg.Normal := hMimg_normal
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hMimg_normal with htop | hcent
  ·
    exfalso
    apply hKL
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' M₀).comp (Subgroup.subtype (CFSG.pCore 2 ↥K))) := by
      intro y
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective M₀ y
      have hkM : q k ∈ Mimg := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨m, hm, hqm⟩ := Subgroup.mem_map.mp hkM
      refine ⟨⟨k * m⁻¹, ?_⟩, ?_⟩
      · have hkm : q (k * m⁻¹) = 1 := by
          rw [hqdef] at hqm ⊢
          rw [map_mul, map_inv, hqm, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff (k * m⁻¹)).mp hkm
      · rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
        have hm1 : (QuotientGroup.mk' M₀) (m : ↥K) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hm
        rw [map_mul, map_inv, hm1, inv_one, mul_one]
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).isNilpotent
    haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := inferInstance
    haveI : Group.IsSolvable (↥K ⧸ M₀) := Group.isSolvable_of_surjective hsurj
    have hcomm : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
      rw [← _root_.commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    have htop_le : (⊤ : Subgroup ↥K) ≤ M₀ :=
      Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := M₀) hcomm
    intro k hk
    have hmem : (⟨k, hk⟩ : ↥K) ∈ M₀ := htop_le (Subgroup.mem_top _)
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  ·
    have hbot : Mimg = ⊥ := le_bot_iff.mp (hcent.trans_eq hcenter)
    have hM₀le : M₀ ≤ CFSG.pCore 2 ↥K := by
      have h := (Subgroup.map_eq_bot_iff M₀ (f := q)).mp hbot
      rwa [hqdef, QuotientGroup.ker_mk'] at h
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥K) ∈ M₀ := Subgroup.mem_subgroupOf.mpr hx
    exact mem_map_subtype_iff.mpr (hM₀le hx')

theorem exists_elemAbelian_nine_le_quotientCentralizer {N L E : Subgroup G}
    (Q : Subgroup ↥L) [Q.Characteristic] (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hEelem : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hEY : E ≤ L ⊔ quotientCentralizer N L Q hLN hNL)
    (hEinfL : E ⊓ L = ⊥)
    (hXinfL : quotientCentralizer N L Q hLN hNL ⊓ L ≤ Q.map L.subtype)
    (hQ3 : ¬ 3 ∣ Nat.card Q) :
    ∃ F : Subgroup G, F ≤ quotientCentralizer N L Q hLN hNL ∧
      CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  classical
  set X : Subgroup G := quotientCentralizer N L Q hLN hNL with hX
  have hXN : X ≤ N := quotientCentralizer_le N L Q hLN hNL
  set Y : Subgroup G := L ⊔ X with hY
  have hLX : X ≤ Subgroup.normalizer (L : Set G) := hXN.trans hNL
  have hYL : L ≤ Y := le_sup_left
  have hYX : X ≤ Y := le_sup_right
  let L' : Subgroup ↥Y := L.subgroupOf Y
  have hL'normal : L'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYL).mpr (sup_le Subgroup.le_normalizer hLX)
  letI : L'.Normal := hL'normal
  let θ : ↥X →* (↥Y ⧸ L') :=
    (QuotientGroup.mk' L').comp (Subgroup.inclusion hYX)
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective L' q
    have hy : (y : G) ∈ (L : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L X hLX]
      exact y.2
    obtain ⟨l, hl, x, hx, hlx⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    change (x : G)⁻¹ * (y : G) ∈ L
    have hmem : (x : G)⁻¹ * (y : G) = (x : G)⁻¹ * l * x := by
      rw [← hlx]
      group
    rw [hmem]
    simpa using (Subgroup.mem_normalizer_iff.mp (hNL (N.inv_mem (hXN hx))) l).mp hl
  set Ebar0 : Subgroup (↥Y ⧸ L') := (E.subgroupOf Y).map (QuotientGroup.mk' L') with hEbar0
  have hE' : CFSG.Open.IsElemAbelian 3 (E.subgroupOf Y) := hEelem.subgroupOf Y
  have hEbar0elem : CFSG.Open.IsElemAbelian 3 Ebar0 :=
    CFSG.SectionRank.isElemAbelian_map hE' _
  have hE'infL' : E.subgroupOf Y ⊓ L' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxL⟩ := Subgroup.mem_inf.mp hx
    have hxE' : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hxE
    have hxL' : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hxL
    have hbot : (x : G) ∈ E ⊓ L := Subgroup.mem_inf.mpr ⟨hxE', hxL'⟩
    rw [hEinfL, Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  have hinj : Function.Injective
      (fun x : ↥(E.subgroupOf Y) => (QuotientGroup.mk' L') (x : ↥Y)) := by
    intro a b hab
    have h1 : ((a : ↥Y))⁻¹ * (b : ↥Y) ∈ L' := QuotientGroup.eq.mp hab
    have h2 : ((a : ↥Y))⁻¹ * (b : ↥Y) ∈ E.subgroupOf Y :=
      (E.subgroupOf Y).mul_mem ((E.subgroupOf Y).inv_mem a.2) b.2
    have h3 : ((a : ↥Y))⁻¹ * (b : ↥Y) ∈ E.subgroupOf Y ⊓ L' :=
      Subgroup.mem_inf.mpr ⟨h2, h1⟩
    rw [hE'infL', Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hEbar0card : Nat.card Ebar0 = 9 := by
    let f : ↥(E.subgroupOf Y) →* (↥Y ⧸ L') :=
      (QuotientGroup.mk' L').comp (E.subgroupOf Y).subtype
    have hf : Function.Injective f := hinj
    have hfr : f.range = Ebar0 := by
      rw [hEbar0, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hfr, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv]
    exact hEcard
  have hker_eq : θ.ker = (X ⊓ L).subgroupOf X := by
    ext x
    change (QuotientGroup.mk' L') (Subgroup.inclusion hYX x) = 1 ↔
      (x : G) ∈ X ⊓ L
    constructor
    · intro hx
      have hx' : (Subgroup.inclusion hYX x : ↥Y) ∈ L' :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact ⟨x.2, by simpa using Subgroup.mem_subgroupOf.mp hx'⟩
    · rintro ⟨-, hxL⟩
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using hxL))
  have hker_le : θ.ker ≤ (Q.map L.subtype : Subgroup G).subgroupOf X := by
    rw [hker_eq]
    exact Subgroup.subgroupOf_mono X hXinfL
  have hQX : Q.map L.subtype ≤ X := map_le_quotientCentralizer N L Q hLN hNL
  have h3Q : ¬ 3 ∣ Nat.card ((Q.map L.subtype : Subgroup G).subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact hQ3
  have hker_card : ¬ 3 ∣ Nat.card θ.ker := fun h =>
    h3Q (h.trans (Subgroup.card_dvd_of_le hker_le))
  have hrange : θ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  let EbarSub : Subgroup ↥θ.range := Ebar0.subgroupOf θ.range
  let e := QuotientGroup.quotientKerEquivRange θ
  let Ebar : Subgroup (↥X ⧸ θ.ker) := EbarSub.comap e.toMonoidHom
  have hEbarSubcard : Nat.card EbarSub = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Ebar0 ≤ θ.range from
      hrange ▸ le_top)).toEquiv]
    exact hEbar0card
  have hEbar_card : Nat.card Ebar = 9 := by
    rw [show Nat.card Ebar = Nat.card EbarSub from
      Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => Subgroup.mem_comap))]
    exact hEbarSubcard
  have hEbar_elem : CFSG.Open.IsElemAbelian 3 Ebar := by
    constructor
    · refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      apply e.injective
      have hx' : ((e (x : ↥X ⧸ θ.ker) : ↥θ.range) : ↥Y ⧸ L') ∈ Ebar0 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp x.2)
      have hy' : ((e (y : ↥X ⧸ θ.ker) : ↥θ.range) : ↥Y ⧸ L') ∈ Ebar0 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp y.2)
      have h := hEbar0elem.1.is_comm.comm
        (⟨((e (x : ↥X ⧸ θ.ker) : ↥θ.range) : ↥Y ⧸ L'), hx'⟩ : ↥Ebar0)
        (⟨((e (y : ↥X ⧸ θ.ker) : ↥θ.range) : ↥Y ⧸ L'), hy'⟩ : ↥Ebar0)
      have h2 := congrArg (fun z : ↥Ebar0 => (z : ↥Y ⧸ L')) h
      apply Subtype.ext
      simpa using h2
    · intro x hx
      apply e.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      have hx' : ((e x : ↥θ.range) : ↥Y ⧸ L') ∈ Ebar0 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hx)
      have h := hEbar0elem.2 ((e x : ↥θ.range) : ↥Y ⧸ L') hx'
      simpa using h
  obtain ⟨S, -, hS_elem, hS_card⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift θ.ker hker_card hEbar_elem
  exact ⟨S.map X.subtype, Subgroup.map_subtype_le S,
    CFSG.SectionRank.isElemAbelian_map hS_elem _,
    by rw [Subgroup.card_map_of_injective X.subtype_injective, hS_card]; exact hEbar_card⟩

theorem four_le_pRank_of_quotientCentralizer {N L F B : Subgroup G}
    (Q : Subgroup ↥L) [Q.Characteristic] (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hFX : F ≤ quotientCentralizer N L Q hLN hNL)
    (hFelem : CFSG.Open.IsElemAbelian 3 F) (hFcard : Nat.card F = 9)
    (hBL : B ≤ L) (hBelem : CFSG.Open.IsElemAbelian 3 B) (hBcard : Nat.card B = 9)
    (hXinfL : quotientCentralizer N L Q hLN hNL ⊓ L ≤ Q.map L.subtype)
    (hQ3 : ¬ 3 ∣ Nat.card Q) :
    4 ≤ CFSG.Open.pRank 3 N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q' : Subgroup G := Q.map L.subtype with hQ'
  have hQ'3 : ¬ 3 ∣ Nat.card Q' := by
    rw [hQ', Subgroup.card_map_of_injective L.subtype_injective]
    exact hQ3
  have hQ'L : Q' ≤ L := Subgroup.map_subtype_le Q
  have hQ'N : Q' ≤ N := hQ'L.trans hLN
  have hNQ' : N ≤ Subgroup.normalizer (Q' : Set G) :=
    hNL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic Q)
  have hFQ' : F ≤ Subgroup.normalizer (Q' : Set G) :=
    (hFX.trans (quotientCentralizer_le N L Q hLN hNL)).trans hNQ'
  have hBQ' : B ≤ Subgroup.normalizer (Q' : Set G) :=
    hBL.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic Q))
  have hcomm : ⁅F, B⁆ ≤ Q' := by
    rw [Subgroup.commutator_le]
    intro f hf b hb
    exact commutator_mem_map_of_mem_quotientCentralizer Q hLN hNL (hFX hf) (hBL hb)
  have hint : (F ⊔ Q') ⊓ (B ⊔ Q') ≤ Q' := by
    intro x hx
    obtain ⟨hxFQ, hxBQ⟩ := Subgroup.mem_inf.mp hx
    have hxL : x ∈ L := (sup_le hBL hQ'L) hxBQ
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right F Q' hFQ'] at hxFQ
    obtain ⟨f, hf, q, hq, rfl⟩ := hxFQ
    have hfL : f ∈ L := by
      have h : (f * q) * q⁻¹ ∈ L := L.mul_mem hxL (L.inv_mem (hQ'L hq))
      simpa [mul_assoc] using h
    exact Q'.mul_mem (hXinfL (Subgroup.mem_inf.mpr ⟨hFX hf, hfL⟩)) hq
  have h := CFSG.Quasithin.add_le_pRank_of_commute_mod (p := 3) (X := N) (Q := Q')
    (E := F) (F := B) (a := 2) (b := 2) hQ'3 hFQ' hBQ' hFelem hBelem
    (by rw [hFcard]; norm_num) (by rw [hBcard]; norm_num) hcomm hint
    (hFX.trans (quotientCentralizer_le N L Q hLN hNL)) (hBL.trans hLN) hQ'N
  simpa using h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
