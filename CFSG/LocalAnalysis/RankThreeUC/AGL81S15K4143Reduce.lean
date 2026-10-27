module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2

open CFSG.Open Subgroup

theorem four_le_pRank_of_commute {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27) {c : X} (hc3 : c ^ 3 = 1) (hcE : c ∉ E)
    (hcomm : ∀ e ∈ E, e * c = c * e) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hS : IsElemAbelian 3 (E ⊔ zpowers c) := by
    refine hE.sup_of_commute (isElemAbelian_zpowers hc3) ?_
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((show Commute a c from hcomm a ha).zpow_right j).eq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hS.isPGroup.exists_card_eq
  have hm4 : 4 ≤ m := by
    by_contra hlt
    have hle : E ≤ E ⊔ zpowers c := le_sup_left
    have hcard : Nat.card ↥(E ⊔ zpowers c) ≤ Nat.card E := by
      rw [hm, h27]
      calc 3 ^ m ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 27 := by norm_num
    have heq : E = E ⊔ zpowers c := Subgroup.eq_of_le_of_card_ge hle hcard
    exact hcE (heq ▸ (le_sup_right : zpowers c ≤ E ⊔ zpowers c) (Subgroup.mem_zpowers c))
  exact hm4.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hS hm)

theorem eq_one_of_mem_of_mem_centralizer {X : Type} [Group X] {L : Subgroup X}
    (hZ : Subgroup.center ↥L = ⊥) {z : X} (hzL : z ∈ L)
    (hzC : z ∈ Subgroup.centralizer (L : Set X)) : z = 1 := by
  have h : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC g g.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem eq_one_of_mem_centralizer_of_pow_three {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hZ : Subgroup.center ↥L = ⊥) (h3L : 3 ≤ CFSG.Open.pRank 3 L)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {c : X}
    (hc : c ∈ Subgroup.centralizer (L : Set X)) (hc3 : c ^ 3 = 1) : c = 1 := by
  by_contra hc1
  obtain ⟨E, hEL, hE, h27⟩ := CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 h3L
  have hcE : c ∉ E := fun hcE => hc1 (eq_one_of_mem_of_mem_centralizer hZ (hEL hcE) hc)
  have h4 := four_le_pRank_of_commute hE h27 hc3 hcE
    (fun e he => Subgroup.mem_centralizer_iff.1 hc e (hEL he))
  omega

theorem eq_one_of_mem_centralizer_of_pow_three_pow {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hZ : Subgroup.center ↥L = ⊥) (h3L : 3 ≤ CFSG.Open.pRank 3 L)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {c : X}
    (hc : c ∈ Subgroup.centralizer (L : Set X)) {k : ℕ} (hck : c ^ 3 ^ k = 1) : c = 1 := by
  induction k generalizing c with
  | zero => simpa using hck
  | succ k ih =>
    have hc3 : c ^ 3 ∈ Subgroup.centralizer (L : Set X) := pow_mem hc 3
    have hck' : (c ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact hck
    exact eq_one_of_mem_centralizer_of_pow_three hZ h3L h3X hc (ih hc3 hck')

theorem mem_of_mem_sup_centralizer {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (hZ : Subgroup.center ↥L = ⊥) (h3L : 3 ≤ CFSG.Open.pRank 3 L)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {y : X}
    (hy : y ∈ L ⊔ Subgroup.centralizer (L : Set X)) {k : ℕ} (hyk : y ^ 3 ^ k = 1) : y ∈ L := by
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
  have hcomm : Commute l c := Subgroup.mem_centralizer_iff.1 hc l hl
  have hpow : l ^ 3 ^ k * c ^ 3 ^ k = 1 := by rw [← hcomm.mul_pow]; exact hyk
  have hcL : c ^ 3 ^ k ∈ L := by
    have h1 : c ^ 3 ^ k = (l ^ 3 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [h1]
    exact inv_mem (pow_mem hl _)
  have hc1 : c ^ 3 ^ k = 1 := eq_one_of_mem_of_mem_centralizer hZ hcL (pow_mem hc _)
  have hc1' : c = 1 := eq_one_of_mem_centralizer_of_pow_three_pow hZ h3L h3X hc hc1
  rw [hc1', mul_one]
  exact hl

theorem conjNormal_eq_one_iff_mem_centralizer {X : Type} [Group X] (L : Subgroup X) [L.Normal]
    {z : X} : MulAut.conjNormal (H := L) z = 1 ↔ z ∈ Subgroup.centralizer (L : Set X) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨g, hg⟩ : ↥L) : X)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc g * z = (z * g * z⁻¹) * z := by rw [h1]
      _ = z * g := by group
  · intro hz
    refine MulEquiv.ext fun ⟨g, hg⟩ => Subtype.ext ?_
    have h1 : g * z = z * g := Subgroup.mem_centralizer_iff.1 hz g hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    calc z * g * z⁻¹ = g * z * z⁻¹ := by rw [h1]
      _ = g := by group

theorem inv_mul_mem_centralizer_of_conj_eq {X : Type} [Group X] {L : Subgroup X} [L.Normal]
    {l : ↥L} {y : X} (h : MulAut.conj l = MulAut.conjNormal y) :
    (l : X)⁻¹ * y ∈ Subgroup.centralizer (L : Set X) := by
  rw [← conjNormal_eq_one_iff_mem_centralizer L, map_mul, map_inv, MulAut.conjNormal_val, h,
    inv_mul_cancel]

theorem pRank_map_of_injOn {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] {p : ℕ}
    (hp : 1 < p) (f : X →* Y) (P : Subgroup X) (hP : ∀ x ∈ P, f x = 1 → x = 1) :
    CFSG.Open.pRank p (P.map f) = CFSG.Open.pRank p P := by
  have hinj : Function.Injective (f.subgroupMap P) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : f (x : X) = 1 := congrArg Subtype.val hx
    exact Subgroup.mem_bot.2 (Subtype.ext (hP x x.2 h1))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := P.map f),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := P)]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp
    (MulEquiv.ofBijective (f.subgroupMap P) ⟨hinj, MonoidHom.subgroupMap_surjective f P⟩)).symm

theorem isSylowOf_inf_inner {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (P : Sylow 3 X) :
    CFSG.ABGLocalTools.IsSylowOf 3
      ((P : Subgroup X).map (MulAut.conjNormal (H := L)) ⊓
        (MulAut.conj : ↥L →* MulAut ↥L).range)
      (MulAut.conj : ↥L →* MulAut ↥L).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c : X →* MulAut ↥L := MulAut.conjNormal (H := L) with hc
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup X).map c) c.range := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨Subgroup.map_le_range c _, (P.isPGroup').map c, ?_⟩
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_left))
  have hInn : (MulAut.conj : ↥L →* MulAut ↥L).range ≤ c.range := by
    rintro _ ⟨l, rfl⟩
    exact ⟨(l : X), MulAut.conjNormal_val (H := L) (h := l)⟩
  haveI : ((MulAut.conj : ↥L →* MulAut ↥L).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥L
  exact hSyl.inf_of_le_normalizer hInn Subgroup.le_normalizer_of_normal

theorem k4143_of_k2
    (H : ∀ (L : Type) [Group L] [Finite L], IsK4143Shape L → Subgroup.center L = ⊥ →
      ∀ R : Subgroup (MulAut L), IsPGroup 3 R →
        CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ (MulAut.conj : L →* MulAut L).range)
          (MulAut.conj : L →* MulAut L).range →
        ¬ R ≤ (MulAut.conj : L →* MulAut L).range → 4 ≤ CFSG.Open.pRank 3 R) :
    K4143 := by
  intro X _ _ L hn hq hZ hshape h3L h3X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (Subgroup.closure_le L).2 ?_
  rintro x ⟨-, k, hk⟩
  have hxk : x ^ 3 ^ k = 1 := hk ▸ pow_orderOf_eq_one x
  by_contra hxL
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 X, x ∈ (P : Subgroup X) := by
    have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers x)⟩
  set c : X →* MulAut ↥L := MulAut.conjNormal (H := L) with hc
  have hinj : ∀ z ∈ (P : Subgroup X), c z = 1 → z = 1 := by
    intro z hz hz1
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨z, hz⟩
    have hzj : z ^ 3 ^ j = 1 := congrArg Subtype.val hj
    exact eq_one_of_mem_centralizer_of_pow_three_pow hZ h3L.ge h3X.le
      ((conjNormal_eq_one_iff_mem_centralizer L).1 hz1) hzj
  have hnle : ¬ (P : Subgroup X).map c ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    intro hle
    obtain ⟨l, hl⟩ := hle ⟨x, hxP, rfl⟩
    have hcen := inv_mul_mem_centralizer_of_conj_eq hl
    have hxeq : x = (l : X) * ((l : X)⁻¹ * x) := by group
    refine hxL (mem_of_mem_sup_centralizer hZ h3L.ge h3X.le ?_ hxk)
    rw [hxeq]
    exact Subgroup.mul_mem_sup l.2 hcen
  have h4 := H ↥L hshape hZ ((P : Subgroup X).map c) ((P.isPGroup').map c)
    (isSylowOf_inf_inner L P) hnle
  rw [pRank_map_of_injOn (by norm_num) c (P : Subgroup X) hinj] at h4
  have h5 : CFSG.Open.pRank 3 (P : Subgroup X) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_top
  omega

end CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2
