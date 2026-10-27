module

public import CFSG.CGT.PushingUpLit.ThmOne.EndField

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mk_oTwo_eq_one_iff {Y : Subgroup G} (y : Y) :
    QuotientGroup.mk' (pCore 2 Y) y = 1 ↔ (y : G) ∈ oTwoIn Y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, oTwoIn_eq_map]
  exact (Subgroup.mem_map_iff_mem Y.subtype_injective).symm

theorem le_oTwoIn_of_map_mk_eq_bot {Y P : Subgroup G} (hPY : P ≤ Y)
    (h : (P.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) = ⊥) : P ≤ oTwoIn Y := by
  intro p hp
  have hmem : QuotientGroup.mk' (pCore 2 Y) ⟨p, hPY hp⟩ = 1 := by
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_map_of_mem _ hp
  exact (mk_oTwo_eq_one_iff _).mp hmem

theorem mk_oTwo_mem_normalizer_map {Y P : Subgroup G} {c : Y}
    (hc : (c : G) ∈ Subgroup.normalizer (P : Set G)) :
    QuotientGroup.mk' (pCore 2 Y) c ∈
      Subgroup.normalizer (((P.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) : Set _)) := by
  refine Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp hc h

variable [Finite G]

theorem inf_oTwoIn_eq_of_isSubnormal {X Y : Subgroup G} (hXY : X ≤ Y)
    (hsub : (X.subgroupOf Y).IsSubnormal) : X ⊓ oTwoIn Y = oTwoIn X :=
  le_antisymm
    (SixThree.le_oTwoIn_of_isPGroup inf_le_left ((isPGroup_oTwoIn Y).to_le inf_le_right)
      ((le_inf Subgroup.le_normalizer (hXY.trans (SixThree.le_normalizer_oTwoIn Y))).trans
        Subgroup.inf_normalizer_le_normalizer_inf))
    (le_inf (oTwoIn_le X) (ThreeFromEight.oTwoIn_le_oTwoIn_of_isSubnormal hXY hsub))

omit [Finite G] in
theorem range_mk_oTwo_comp_inclusion {X Y : Subgroup G} (hXY : X ≤ Y) :
    ((QuotientGroup.mk' (pCore 2 Y)).comp (Subgroup.inclusion hXY)).range =
      (X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_map_of_mem _ (show Subgroup.inclusion hXY x ∈ X.subgroupOf Y from x.2)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem ker_mk_oTwo_comp_inclusion {X Y : Subgroup G} (hXY : X ≤ Y)
    (hsub : (X.subgroupOf Y).IsSubnormal) :
    ((QuotientGroup.mk' (pCore 2 Y)).comp (Subgroup.inclusion hXY)).ker = pCore 2 X := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mk_oTwo_eq_one_iff, Subgroup.coe_inclusion,
    ← Subgroup.mem_map_iff_mem X.subtype_injective (K := pCore 2 X), ← oTwoIn_eq_map,
    ← inf_oTwoIn_eq_of_isSubnormal hXY hsub, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem isComponent_map_mk_oTwo {X Y : Subgroup G} (hq : IsQuasisimple (X ⧸ pCore 2 X))
    (hXY : X ≤ Y) (hsub : (X.subgroupOf Y).IsSubnormal) :
    IsComponent ((X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) := by
  set φ := (QuotientGroup.mk' (pCore 2 Y)).comp (Subgroup.inclusion hXY)
  let e : (X ⧸ pCore 2 X) ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq (ker_mk_oTwo_comp_inclusion hXY hsub).symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  have hq' := LocalCores.isQuasisimple_of_mulEquiv
    (e.trans (MulEquiv.subgroupCongr (range_mk_oTwo_comp_inclusion hXY))) hq
  exact ⟨hq', hsub.map (QuotientGroup.mk'_surjective _)⟩

theorem isPGroup_map_mk_oTwo {X Y : Subgroup G} {p : ℕ} (hp : Nat.card (X ⧸ pCore 2 X) = p)
    (hXY : X ≤ Y) (hsub : (X.subgroupOf Y).IsSubnormal) :
    IsPGroup p ((X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) := by
  rintro ⟨z, y, hy, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hx : ((⟨y, hy⟩ : X) : X ⧸ pCore 2 X) ^ p = 1 := by rw [← hp]; exact pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx
  have hO : ((⟨y, hy⟩ : X) ^ p : G) ∈ oTwoIn X := ⟨_, hx, rfl⟩
  rw [← inf_oTwoIn_eq_of_isSubnormal hXY hsub] at hO
  rw [pow_one, Subgroup.coe_pow, ← map_pow, Subgroup.coe_one, mk_oTwo_eq_one_iff]
  simpa using hO.2

theorem mem_normalizer_of_commutator_mem_twoGroup {X Q : Subgroup G} (hX : SubTwo.NoTwoQuotient X)
    (hQ : IsPGroup 2 Q) (hQX : Q ≤ Subgroup.normalizer (X : Set G)) {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hg : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Q) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  have hdec : ∀ b ∈ X ⊔ Q, ∃ y ∈ X, ∃ q ∈ Q, q ∈ X ⊔ Q ∧ y * q = b := by
    intro b hb
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X Q hQX] at hb
    obtain ⟨y, hy, q, hq, rfl⟩ := hb
    exact ⟨y, hy, q, hq, Subgroup.mem_sup_right hq, rfl⟩
  have hconj : ∀ a : G, a ∈ Subgroup.normalizer (Q : Set G) →
      (∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ Q) → ∀ b ∈ X ⊔ Q, a * b * a⁻¹ ∈ X ⊔ Q := by
    intro a ha hax b hb
    obtain ⟨y, hy, q, hq, -, rfl⟩ := hdec b hb
    rw [show a * (y * q) * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y * (a * q * a⁻¹) by group]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right (hax y hy)) (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp ha q).mp hq))
  have hinv : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ ∈ Q := by
    intro x hx
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hgQ) _).mp (inv_mem (hg x hx))
    convert h using 1
    group
  have hgB : g ∈ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨hconj g hgQ hg b, fun hb => ?_⟩
    have := hconj g⁻¹ (inv_mem hgQ) hinv _ hb
    simpa [mul_assoc] using this
  exact SubTwo.mem_normalizer_of_normal_chain hX le_sup_left (sup_le Subgroup.le_normalizer hQX)
    le_rfl hQ hdec hgB

theorem mem_centralizerModCore_of_commutator_mem_oTwoIn {X Y : Subgroup G} (hX : oResidualTwo X = ⊤)
    (hXY : X ≤ Y) (hsub : (X.subgroupOf Y).IsSubnormal) {g : G} (hgY : g ∈ Y)
    (hg : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ oTwoIn Y) : g ∈ centralizerModCore X := by
  have hgN := mem_normalizer_of_commutator_mem_twoGroup (SubTwo.noTwoQuotient_of_oResidualTwo hX)
    (isPGroup_oTwoIn Y) (oTwoIn_le_normalizer_of_isSubnormal hX hXY hsub)
    (SixThree.le_normalizer_oTwoIn Y hgY) hg
  refine ⟨hgN, fun x hx => ?_⟩
  rw [← inf_oTwoIn_eq_of_isSubnormal hXY hsub]
  exact Subgroup.mem_inf.mpr
    ⟨mul_mem ((Subgroup.mem_normalizer_iff.mp hgN x).mp hx) (inv_mem hx), hg x hx⟩

theorem mem_centralizerModCore_of_mk_mem_centralizer {X Y : Subgroup G}
    (hX : oResidualTwo X = ⊤) (hXY : X ≤ Y) (hsub : (X.subgroupOf Y).IsSubnormal) {y : Y}
    (hy : QuotientGroup.mk' (pCore 2 Y) y ∈ Subgroup.centralizer
      (((X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) : Set _))) :
    (y : G) ∈ centralizerModCore X := by
  refine mem_centralizerModCore_of_commutator_mem_oTwoIn hX hXY hsub y.2 fun x hx => ?_
  have h1 := Subgroup.mem_centralizer_iff.mp hy _
    (Subgroup.mem_map_of_mem _ (show (⟨x, hXY hx⟩ : Y) ∈ X.subgroupOf Y from hx))
  have h2 : QuotientGroup.mk' (pCore 2 Y) (y * ⟨x, hXY hx⟩ * y⁻¹ * ⟨x, hXY hx⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  exact (mk_oTwo_eq_one_iff _).mp h2

theorem oTwoIn_le_centralizer_blockU {X : Subgroup G} (hX : IsShortGroup X) :
    oTwoIn X ≤ Subgroup.centralizer (blockU X : Set G) := fun c hc =>
  Subgroup.mem_centralizer_iff.mpr fun u hu => blockU_comm_of_short hX u hu c hc

theorem commutator_mem_centralizer_blockU {X : Subgroup G} (hX : IsShortGroup X) {g : G}
    (hg : g ∈ centralizerModCore X) {l : G} (hl : l ∈ X) :
    ⁅g, l⁆ ∈ Subgroup.centralizer (blockU X : Set G) := by
  rw [commutatorElement_def]
  exact oTwoIn_le_centralizer_blockU hX (hg.2 l hl)

theorem commutatorElement_mem_centralizer_blockU {X : Subgroup G} (hX : IsShortGroup X)
    {g h : G} (hg : g ∈ centralizerModCore X) (hh : h ∈ centralizerModCore X) :
    ⁅g, h⁆ ∈ Subgroup.centralizer (blockU X : Set G) := by
  have hc : ⁅g, h⁆ ∈ centralizerModCore X := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  refine commutator_eq_one_of_commutator_mem_blockZ hX hc.1
    (fun l hl => commutator_mem_centralizer_blockU hX hc hl) ?_
  exact commutator_commutator_mem_blockZ hX hg.1 hh.1
    (fun l hl _ hu => commutator_mem_blockZ_of_mem_centralizer
      (commutator_mem_centralizer_blockU hX hg hl) hu)
    (fun l hl _ hu => commutator_mem_blockZ_of_mem_centralizer
      (commutator_mem_centralizer_blockU hX hh hl) hu)

omit [Finite G] in
theorem commutatorElement_mem_centralizer_of_normalizer {X : Subgroup G} {g p : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hp : p ∈ Subgroup.centralizer (blockU X : Set G)) :
    ⁅g, p⁆ ∈ Subgroup.centralizer (blockU X : Set G) := by
  have hgp : g * p * g⁻¹ ∈ Subgroup.centralizer (blockU X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : g⁻¹ * u * g ∈ blockU X := by simpa using conj_mem_blockU (inv_mem hg) hu
    have h1 := Subgroup.mem_centralizer_iff.mp hp _ hu'
    calc u * (g * p * g⁻¹) = g * ((g⁻¹ * u * g) * p) * g⁻¹ := by group
      _ = g * (p * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = g * p * g⁻¹ * u := by group
  rw [commutatorElement_def]
  exact mul_mem hgp (inv_mem hp)

theorem map_mk_le_centralizer {X Y P : Subgroup G} (hXY : X ≤ Y)
    (hsub : (X.subgroupOf Y).IsSubnormal) (hPC : P ≤ centralizerModCore X) :
    (X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) ≤ Subgroup.centralizer
      (((P.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) : Set _)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  have hO : ((q * x * q⁻¹ * x⁻¹ : Y) : G) ∈ oTwoIn Y :=
    ThreeFromEight.oTwoIn_le_oTwoIn_of_isSubnormal hXY hsub ((hPC hq).2 _ hx)
  have h := (mk_oTwo_eq_one_iff _).mpr hO
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
  calc QuotientGroup.mk' (pCore 2 Y) q * QuotientGroup.mk' (pCore 2 Y) x =
      (QuotientGroup.mk' (pCore 2 Y) q * QuotientGroup.mk' (pCore 2 Y) x *
        (QuotientGroup.mk' (pCore 2 Y) q)⁻¹ * (QuotientGroup.mk' (pCore 2 Y) x)⁻¹) *
        QuotientGroup.mk' (pCore 2 Y) x * QuotientGroup.mk' (pCore 2 Y) q := by group
    _ = QuotientGroup.mk' (pCore 2 Y) x * QuotientGroup.mk' (pCore 2 Y) q := by
      rw [h, one_mul]

end CFSG.CGT.PushingUpLit.ThmOne
