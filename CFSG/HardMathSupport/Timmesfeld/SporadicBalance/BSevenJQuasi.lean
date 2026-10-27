module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23L34Rels
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen

private lemma eq_one_of_pow_five_three_seven {H : Type*} [CommGroup H] {x z : H}
    (hx : x ^ 5 = 1) (hz : z ^ 3 = 1) (h : ((z * x) ^ 7) ^ 2 = 1) :
    x = 1 ∧ z = 1 := by
  have h1 : z ^ 2 * x ^ 4 = 1 := by
    have h' : (z * x) ^ 14 = 1 := by
      have h14 : ((z * x) ^ 7) ^ 2 = (z * x) ^ 14 := by group
      rwa [h14] at h
    rw [mul_pow] at h'
    have hz14 : z ^ 14 = z ^ 2 := by
      have hz' : z ^ 14 = (z ^ 3) ^ 4 * z ^ 2 := by group
      rw [hz', hz, one_pow, one_mul]
    have hx14 : x ^ 14 = x ^ 4 := by
      have hx' : x ^ 14 = (x ^ 5) ^ 2 * x ^ 4 := by group
      rw [hx', hx, one_pow, one_mul]
    rwa [hz14, hx14] at h'
  have h2 : x = z ^ 2 := by
    calc x = (z ^ 2 * x ^ 4) * x := by rw [h1, one_mul]
      _ = z ^ 2 * x ^ 5 := by group
      _ = z ^ 2 * 1 := by rw [hx]
      _ = z ^ 2 := mul_one _
  have h3 : z ^ 10 = 1 := by
    have hz10 : z ^ 10 = z ^ 2 * (z ^ 2) ^ 4 := by group
    rw [h2] at h1
    rw [hz10]
    exact h1
  have hz1 : z = 1 := by
    have hz10 : z ^ 10 = z := by
      have hz' : z ^ 10 = (z ^ 3) ^ 3 * z := by group
      rw [hz', hz, one_pow, one_mul]
    rw [← hz10]
    exact h3
  exact ⟨by rw [h2, hz1, one_pow], hz1⟩

theorem quasisimple_closure_of_cover {G : Type} [Group G]
    {a e y u v : G}
    (hJ : Subgroup.closure ({y, e} : Set G) = Subgroup.closure ({u, v} : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hay : a * y = y * a) (hae : a * e = e * a)
    (hy5 : y ^ 5 = 1) (he3 : e ^ 3 = 1) (h7 : (e * y) ^ 7 = a)
    (hrel : ∀ w ∈ rels.map (List.map fun l => ((l.1 : ℕ), l.2)),
      wordProd (img2 u v) w ∈ Subgroup.zpowers a)
    (hu : u ∉ Subgroup.zpowers a) :
    CFSG.Assembly.IsQuasisimple ↥(Subgroup.closure ({y, e} : Set G)) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.closure ({y, e} : Set G))) = 2 ∧
      Nat.card ↥(Subgroup.closure ({y, e} : Set G)) = 40320 := by
  classical
  set J : Subgroup G := Subgroup.closure ({y, e} : Set G) with hJdef
  have hJ' : J = Subgroup.closure ({u, v} : Set G) := hJdef.trans hJ
  have hyJ : y ∈ J := by rw [hJdef]; exact Subgroup.subset_closure (by simp)
  have heJ : e ∈ J := by rw [hJdef]; exact Subgroup.subset_closure (by simp)
  have huJ : u ∈ J := by rw [hJ']; exact Subgroup.subset_closure (by simp)
  have hvJ : v ∈ J := by rw [hJ']; exact Subgroup.subset_closure (by simp)
  have haJ : a ∈ J := h7 ▸ J.pow_mem (J.mul_mem heJ hyJ) 7
  have hJc : J ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hJdef, Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hay)
    · exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hae)
  set y' : ↥J := ⟨y, hyJ⟩ with hy'def
  set e' : ↥J := ⟨e, heJ⟩ with he'def
  set u' : ↥J := ⟨u, huJ⟩ with hu'def
  set v' : ↥J := ⟨v, hvJ⟩ with hv'def
  set a' : ↥J := ⟨a, haJ⟩ with ha'def
  have ha'center : a' ∈ Subgroup.center ↥J := by
    rw [ha'def, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * a = a * (g : G)
    exact ((Subgroup.mem_centralizer_iff.mp (hJc g.property)) a (Set.mem_singleton a)).symm
  set N : Subgroup ↥J := Subgroup.zpowers a' with hNdef
  have hN_le_center : N ≤ Subgroup.center ↥J := by
    rw [hNdef]
    exact Subgroup.zpowers_le.mpr ha'center
  haveI hN_normal : N.Normal := Subgroup.normal_of_le_center hN_le_center
  have hN_eq : (Subgroup.zpowers a).subgroupOf J = N := by
    ext x
    rw [Subgroup.mem_subgroupOf, hNdef, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' := congrArg Subtype.val hk
      simpa [Subgroup.coe_zpow] using hk'
  have ha2' : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  have horder : orderOf a = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact orderOf_eq_prime ha2' ha1
  have hcardN : Nat.card N = 2 := by
    rw [hNdef, Nat.card_zpowers, ha'def, Subgroup.orderOf_mk, horder]
  have hy'5 : y' ^ 5 = 1 := by apply Subtype.ext; simpa using hy5
  have he'3 : e' ^ 3 = 1 := by apply Subtype.ext; simpa using he3
  have ha'2 : a' ^ 2 = 1 := by apply Subtype.ext; simpa [pow_two] using ha2
  have ha'7 : a' = (e' * y') ^ 7 := by
    apply Subtype.ext
    show a = ((e' * y') ^ 7 : ↥J).val
    rw [Subgroup.coe_pow, Subgroup.coe_mul]
    exact h7.symm
  have hclJ : Subgroup.closure ({u', v'} : Set ↥J) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top hJ' huJ hvJ
  have hclQ :
      Subgroup.closure ({QuotientGroup.mk' N u', QuotientGroup.mk' N v'} : Set (↥J ⧸ N)) = ⊤ := by
    have h1 : Subgroup.closure (QuotientGroup.mk' N '' ({u', v'} : Set ↥J)) = ⊤ := by
      rw [← MonoidHom.map_closure (QuotientGroup.mk' N) ({u', v'} : Set ↥J), hclJ,
        Subgroup.map_top_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)]
    have hset : QuotientGroup.mk' N '' ({u', v'} : Set ↥J) =
        ({QuotientGroup.mk' N u', QuotientGroup.mk' N v'} : Set (↥J ⧸ N)) := by
      ext z
      simp
    rwa [hset] at h1
  have hπu : QuotientGroup.mk' N u' ≠ 1 := by
    intro h
    have huN : u' ∈ N := (QuotientGroup.eq_one_iff u').1 (by simpa using h)
    rw [← hN_eq, Subgroup.mem_subgroupOf] at huN
    exact hu huN
  have hrelQ : ∀ w ∈ rels.map (List.map fun l => ((l.1 : ℕ), l.2)),
      wordProd (img2 (QuotientGroup.mk' N u') (QuotientGroup.mk' N v')) w = 1 := by
    intro w hw
    have hmem : wordProd (img2 u' v') w ∈ N := by
      rw [← hN_eq, Subgroup.mem_subgroupOf]
      have hcoe : ((wordProd (img2 u' v') w : ↥J) : G) = wordProd (img2 u v) w := by
        rw [coe_wordProd]
        congr 1
        funext i
        simp only [img2]
        split <;> rfl
      rw [hcoe]
      exact hrel w hw
    have hmap : wordProd (img2 (QuotientGroup.mk' N u') (QuotientGroup.mk' N v')) w =
        QuotientGroup.mk' N (wordProd (img2 u' v') w) := by
      rw [map_wordProd (QuotientGroup.mk' N) (img2 u' v') w]
      congr 1
      funext i
      simp only [img2]
      split <;> rfl
    rw [hmap]
    exact (QuotientGroup.eq_one_iff (wordProd (img2 u' v') w)).2 hmem
  have hPSLcl : CFSG.Quasithin.IsPSL 3 2 2
      ↥(Subgroup.closure ({QuotientGroup.mk' N u', QuotientGroup.mk' N v'} : Set (↥J ⧸ N))) :=
    CFSG.Quasithin.A312M23.isPSL_three_four_of_rels hrelQ hπu
  have hPSLQ : CFSG.Quasithin.IsPSL 3 2 2 (↥J ⧸ N) := by
    have e : ↥(Subgroup.closure ({QuotientGroup.mk' N u', QuotientGroup.mk' N v'} :
        Set (↥J ⧸ N))) ≃* (↥J ⧸ N) :=
      (MulEquiv.subgroupCongr hclQ).trans Subgroup.topEquiv
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hPSLcl
  have hcardQ : Nat.card (↥J ⧸ N) = 20160 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hPSLQ
  have hsimpleQ : IsSimpleGroup (↥J ⧸ N) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity (↥J ⧸ N) 3 2 2 hPSLQ).2
  haveI : IsSimpleGroup (↥J ⧸ N) := hsimpleQ
  have hcenterQ : Subgroup.center (↥J ⧸ N) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥J ⧸ N)) with hc | hc
    · exact hc
    · exfalso
      have hcomm : ∀ p q : (↥J ⧸ N), p * q = q * p := fun p q =>
        (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top q) p)
      let _ : CommGroup (↥J ⧸ N) := { (inferInstance : Group (↥J ⧸ N)) with mul_comm := hcomm }
      have hp := IsSimpleGroup.prime_card (α := (↥J ⧸ N))
      rw [hcardQ] at hp
      norm_num at hp
  have hcenter_le : Subgroup.center ↥J ≤ N := by
    intro x hx
    have hxmap : QuotientGroup.mk' N x ∈
        (Subgroup.center ↥J).map (QuotientGroup.mk' N) :=
      Subgroup.apply_coe_mem_map (QuotientGroup.mk' N) (Subgroup.center ↥J) ⟨x, hx⟩
    have hxπ : QuotientGroup.mk' N x ∈ Subgroup.center (↥J ⧸ N) :=
      Subgroup.map_center_le_center (f := QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) hxmap
    rw [hcenterQ, Subgroup.mem_bot] at hxπ
    exact (QuotientGroup.eq_one_iff x).1 hxπ
  have hcenter_eq : Subgroup.center ↥J = N := le_antisymm hcenter_le hN_le_center
  have hcardCenter : Nat.card ↥(Subgroup.center ↥J) = 2 := by
    rw [hcenter_eq, hcardN]
  have hab : Abelianization.of y' = 1 ∧ Abelianization.of e' = 1 := by
    have hE3 : (Abelianization.of e') ^ 3 = 1 := by rw [← map_pow, he'3, map_one]
    have hA5 : (Abelianization.of y') ^ 5 = 1 := by rw [← map_pow, hy'5, map_one]
    have hrel7 : ((Abelianization.of e' * Abelianization.of y') ^ 7) ^ 2 = 1 := by
      rw [← map_mul, ← map_pow, ← map_pow, ← ha'7, ha'2, map_one]
    exact eq_one_of_pow_five_three_seven hA5 hE3 hrel7
  have hy_comm : y' ∈ commutator ↥J := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hab.1
  have he_comm : e' ∈ commutator ↥J := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hab.2
  have hclJ2 : Subgroup.closure ({y', e'} : Set ↥J) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top hJdef hyJ heJ
  have hcomm_top : commutator ↥J = ⊤ := by
    have hle : Subgroup.closure ({y', e'} : Set ↥J) ≤ commutator ↥J := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hy_comm
      · exact he_comm
    rw [hclJ2] at hle
    exact top_le_iff.mp hle
  have hquot : ((↥J) ⧸ Subgroup.center ↥J) ≃* (↥J ⧸ N) :=
    QuotientGroup.quotientMulEquivOfEq hcenter_eq
  have hsimpleQuot : IsSimpleGroup ((↥J) ⧸ Subgroup.center ↥J) := hquot.isSimpleGroup
  have hcardJ : Nat.card ↥J = 40320 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcardQ, hcardN]
  exact ⟨⟨hcomm_top, hsimpleQuot⟩, hcardCenter, hcardJ⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
