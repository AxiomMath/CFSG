module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFiveDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGCfg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGBasic
import CFSG.Quasithin.EmptyFaithful.S152He9A5

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGFive

open CFSG.Open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem S_le_normalizer (d : KGC.KGData p H D S B L M z) : S ≤ normalizer (L : Set G) :=
  fun s hs => d.M_le_L ⟨d.S_le_M hs, d.S_le_H hs⟩

theorem exists_two_pow_mem (d : KGC.KGData p H D S B L M z) {y : G} (hy : y ∈ L ⊔ S) :
    ∃ a : ℕ, y ^ (2 ^ a) ∈ L := by
  obtain ⟨s, hs, k, hk, rfl⟩ := KGB.exists_mul_of_le_normalizer (S_le_normalizer d) hy
  obtain ⟨a, ha⟩ := d.S_two ⟨s, hs⟩
  have hsa : s ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨k', hk', hm⟩ := KGB.pow_mul_mem (S_le_normalizer d hs) hk (2 ^ a)
  refine ⟨a, ?_⟩
  rw [hm, hsa, one_mul]
  exact hk'

theorem le_of_isOTwoPerfect (d : KGC.KGData p H D S B L M z) {J : Subgroup G}
    (hJX : J ≤ L ⊔ S) (hJ : IsOTwoPerfect J) : J ≤ L := by
  have hN : (L.subgroupOf J).Normal := ⟨fun n hn g => by
    have hg : (g : G) ∈ normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer (S_le_normalizer d) (hJX g.2)
    exact (mem_normalizer_iff.mp hg (n : G)).mp hn⟩
  have h2 : IsPGroup 2 (↥J ⧸ L.subgroupOf J) := by
    intro q
    refine QuotientGroup.induction_on q fun j => ?_
    obtain ⟨a, ha⟩ := exists_two_pow_mem d (hJX j.2)
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  exact Subgroup.subgroupOf_eq_top.mp (hJ (L.subgroupOf J) h2)

theorem img_mono {H D : Subgroup G} [(D.subgroupOf H).Normal] {U V : Subgroup G} (h : U ≤ V) :
    KGC.img H D U ≤ KGC.img H D V := by
  intro x hx
  obtain ⟨h', hh', rfl⟩ := KGC.mem_img.mp hx
  exact KGC.mem_img.mpr ⟨h', h hh', rfl⟩

theorem img_sup (d : KGC.KGData p H D S B L M z) [(D.subgroupOf H).Normal] :
    KGC.img H D (L ⊔ S) = KGC.img H D L ⊔ KGC.img H D S := by
  unfold KGC.img
  rw [Subgroup.subgroupOf_sup d.L_le_H d.S_le_H, Subgroup.map_sup]

theorem isSubnormal_img {H D : Subgroup G} [(D.subgroupOf H).Normal] {U V : Subgroup G}
    (h : CFSG.Open.IsSubnormal U V) :
    CFSG.Open.IsSubnormal (KGC.img H D U) (KGC.img H D V) :=
  (h.comap H.subtype).map (KGC.qmk H D)

theorem img_eq_bot_or_eq (d : KGC.KGData p H D S B L M z) [(D.subgroupOf H).Normal]
    {J : Subgroup G} (hJs : CFSG.Open.IsSubnormal J (L ⊔ S)) (hJL : J ≤ L) :
    KGC.img H D J = ⊥ ∨ KGC.img H D J = KGC.img H D L := by
  have hs : CFSG.Open.IsSubnormal (KGC.img H D J)
      (KGC.img H D L ⊔ KGC.img H D S) := by
    rw [← img_sup d]
    exact isSubnormal_img hJs
  have hs' := hs.inf_of_le (le_sup_left : KGC.img H D L ≤ KGC.img H D L ⊔ KGC.img H D S)
  rw [inf_eq_left.mpr (img_mono hJL)] at hs'
  exact hs'.eq_bot_or_eq_of_isSimpleGroup d.simple_img

theorem not_isPGroup_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) {r : ℕ} [Fact r.Prime] (hP : IsPGroup r K) : False := by
  haveI : Nontrivial (Subgroup.center K) := hP.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center K)
    exact hc (Subtype.ext (Subgroup.mem_bot.mp (h.le c.2)))
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h.ge (Subgroup.mem_top a)) b).symm

theorem exists_equiv (d : KGC.KGData p H D S B L M z) [hDn : (D.subgroupOf H).Normal]
    {J : Subgroup G} (hJs : CFSG.Open.IsSubnormal J (L ⊔ S)) (hJ2 : IsOTwoPerfect J)
    (hJM : ¬ J ≤ M) :
    Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* ↥(KGC.img H D L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := d.simple_img
  have hJL : J ≤ L := le_of_isOTwoPerfect d hJs.le hJ2
  have hJH : J ≤ H := hJL.trans d.L_le_H
  rcases img_eq_bot_or_eq d hJs hJL with hbot | heq
  · exfalso
    apply hJM
    intro j hj
    have hm : KGC.qmk H D ⟨j, hJH hj⟩ ∈ KGC.img H D J :=
      KGC.mem_img.mpr ⟨⟨j, hJH hj⟩, hj, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hm
    exact d.D_le_M ((KGC.qmk_eq_one_iff (H := H) (D := D)).mp hm)
  · let φ : ↥J →* ↥(KGC.img H D L) :=
      ((KGC.qmk H D).comp (Subgroup.inclusion hJH)).codRestrict (KGC.img H D L) fun j =>
        KGC.mem_img.mpr ⟨Subgroup.inclusion hJH j, hJL j.2, rfl⟩
    have hφ : Function.Surjective φ := by
      intro k
      have hk : (k : KGC.QA H D) ∈ KGC.img H D J := by
        rw [heq]
        exact k.2
      obtain ⟨h, hhJ, hq⟩ := KGC.mem_img.mp hk
      exact ⟨⟨h, hhJ⟩, Subtype.ext hq⟩
    have hφker : ∀ j : ↥J, φ j = 1 ↔ (j : G) ∈ D := by
      intro j
      constructor
      · intro h
        have h1 : KGC.qmk H D (Subgroup.inclusion hJH j) = 1 := congrArg Subtype.val h
        exact (KGC.qmk_eq_one_iff (H := H) (D := D)).mp h1
      · intro h
        exact Subtype.ext ((KGC.qmk_eq_one_iff (H := H) (D := D)).mpr h)
    have hker : φ.ker = CFSG.pCore 2 ↥J := by
      apply le_antisymm
      · refine le_sSup ⟨φ.normal_ker, ?_⟩
        intro g
        have hgD : ((g : ↥J) : G) ∈ D := (hφker g).mp g.2
        obtain ⟨b, hb⟩ := d.D_two ⟨((g : ↥J) : G), hgD⟩
        refine ⟨b, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hb
        simpa using this
      · intro r hr
        have hmem : φ r ∈ (CFSG.pCore 2 ↥J).map φ := Subgroup.mem_map_of_mem φ hr
        have hbot' : (CFSG.pCore 2 ↥J).map φ = ⊥ := by
          have hn : ((CFSG.pCore 2 ↥J).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥J).map φ) with h | h
          · exact h
          · exfalso
            have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥J).map φ) := CFSG.pCore_isPGroup.map φ
            rw [h] at hP
            exact not_isPGroup_of_simple d.nonab_img (hP.of_equiv Subgroup.topEquiv)
        rw [hbot'] at hmem
        exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hmem)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem false_of_shape {K Q : Type} [Group K] [Group Q] (e : Q ≃* K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hbender : ¬ fusionIsBenderGroup K)
    (h7 : ∀ n : ℕ, 7 ≤ n → ¬ Nonempty (K ≃* alternatingGroup (Fin n)))
    (hshape : (∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ Nonempty (Q ≃* alternatingGroup (Fin n))) ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty (Q ≃* PSL(2, GaloisField 2 n))) : False := by
  rcases hshape with ⟨n, hn3, hodd, ⟨eA⟩⟩ | ⟨n, hn2, ⟨eP⟩⟩
  · have e' : K ≃* alternatingGroup (Fin n) := e.symm.trans eA
    obtain ⟨k, rfl⟩ := hodd
    by_cases h7' : 7 ≤ 2 * k + 1
    · exact h7 _ h7' ⟨e'⟩
    · have hk : k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl
      · have hcomm : ∀ a b : alternatingGroup (Fin (2 * 1 + 1)), a * b = b * a := by
          decide +kernel
        obtain ⟨a, b, hab⟩ := hnab
        apply hab
        apply e'.injective
        rw [map_mul, map_mul, hcomm]
      · obtain ⟨eB⟩ := CFSG.Quasithin.He9.nonempty_psl2_gf4_mulEquiv_alternating
        exact hbender (Or.inl ⟨2, le_rfl, ⟨e'.trans eB.symm⟩⟩)
  · exact hbender (Or.inl ⟨n, hn2, ⟨e.symm.trans eP⟩⟩)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGFive
