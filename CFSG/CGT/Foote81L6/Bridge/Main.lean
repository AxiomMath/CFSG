module

public import CFSG.CGT.Foote81L6.Bridge.Lifts
public import CFSG.CGT.Foote81L6.Bridge.Sylow
public import CFSG.CGT.Foote81L6.LiftConj
public import CFSG.CGT.Foote81L6.OddQuot

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

theorem zCent_mem_center {H : Type*} [Group H] (z : H) :
    zCent z ∈ center (centralizer ({z} : Set H)) :=
  mem_center_iff.2 fun g => Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

section Embedding

variable {H : Type*} [Group H] {S : Subgroup H} {n : ℕ} (e : ↥S ≃* SModel n)

@[expose] def zOf : H := ((e.symm (zS n) : ↥S) : H)

theorem center_eq_zpowers_zOf (hn : 3 ≤ n) : (center ↥S).map S.subtype = zpowers (zOf e) := by
  rw [← map_center_eq e.symm, center_SModel hn, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem orderOf_zOf (hn : 3 ≤ n) : orderOf (zOf e) = 2 := by
  rw [zOf, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_zS (by omega)]

theorem zOf_comm (x : ↥S) : (x : H) * zOf e = zOf e * x := by
  have hc : e.symm (zS n) ∈ center ↥S := by
    rw [← map_center_eq e.symm]
    exact ⟨zS n, zS_mem_center n, rfl⟩
  exact congrArg Subtype.val (mem_center_iff.1 hc x)

theorem le_centralizer_zOf : S ≤ centralizer ({zOf e} : Set H) := fun x hx =>
  mem_centralizer_singleton_iff.2 (zOf_comm e ⟨x, hx⟩)

theorem inclusion_symm_zS :
    Subgroup.inclusion (le_centralizer_zOf e) (e.symm (zS n)) = zCent (zOf e) := rfl

theorem zCent_zOf_mul_self : zCent (zOf e) * zCent (zOf e) = 1 := by
  rw [← inclusion_symm_zS, ← map_mul, ← map_mul, zS_mul_zS, map_one, map_one]

@[expose] noncomputable def embS : SModel n →* centralizerQuot (zOf e) :=
  (QuotientGroup.mk' (zpowers (zCent (zOf e)))).comp
    ((Subgroup.inclusion (le_centralizer_zOf e)).comp e.symm.toMonoidHom)

theorem embS_apply (y : SModel n) :
    embS e y = (QuotientGroup.mk (Subgroup.inclusion (le_centralizer_zOf e) (e.symm y)) :
      centralizerQuot (zOf e)) := rfl

theorem zpowers_zS_le_ker : zpowers (zS n) ≤ (embS e).ker := by
  rw [zpowers_le, MonoidHom.mem_ker, embS_apply, inclusion_symm_zS, QuotientGroup.eq_one_iff]
  exact mem_zpowers _

@[expose] noncomputable def embT : TM n →* centralizerQuot (zOf e) :=
  QuotientGroup.lift _ (embS e) (zpowers_zS_le_ker e)

theorem embT_mk (y : SModel n) : embT e (QuotientGroup.mk y) = embS e y := rfl

theorem embT_injective : Function.Injective (embT e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [embT_mk, embS_apply, QuotientGroup.eq_one_iff,
    mem_zpowers_of_mul_self_eq_one (zCent_zOf_mul_self e)] at hx
  rw [QuotientGroup.eq_one_iff, mem_zpowers_of_mul_self_eq_one (zS_mul_zS n)]
  rcases hx with h | h
  · exact Or.inl (e.symm.injective (Subgroup.inclusion_injective _ (by rw [h, map_one, map_one])))
  · exact Or.inr (e.symm.injective (Subgroup.inclusion_injective _
      (h.trans (inclusion_symm_zS e).symm)))

theorem embT_eq_one : ∀ x ∈ (⊤ : Subgroup (TM n)), embT e x = 1 → x = 1 :=
  fun x _ hx => (injective_iff_map_eq_one _).1 (embT_injective e) x hx

theorem map_top_embT : (⊤ : Subgroup (TM n)).map (embT e) = sylowQuot S (zOf e) := by
  ext x
  constructor
  · rintro ⟨w, -, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨Subgroup.inclusion (le_centralizer_zOf e) (e.symm y), mem_subgroupOf.2 (e.symm y).2,
      rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨QuotientGroup.mk (e ⟨g, mem_subgroupOf.1 hg⟩), mem_top _, ?_⟩
    rw [embT_mk, embS_apply, MulEquiv.symm_apply_apply]
    rfl

theorem not_isConj_embT (hn : 3 ≤ n) {x y : TM n} (hx : LiftsSqZ x) (hy : LiftsSq1 y) :
    ¬ IsConj (embT e x) (embT e y) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  have hu := hx u rfl
  have hv := hy v rfl
  rw [embT_mk, embT_mk, embS_apply, embS_apply]
  have hz2 : zCent (zOf e) ^ 2 = 1 := by rw [pow_two, zCent_zOf_mul_self]
  have hzne : zCent (zOf e) ≠ 1 := by
    intro h
    have h1 := orderOf_zOf e hn
    rw [show zOf e = 1 from congrArg Subtype.val h, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hg2 : Subgroup.inclusion (le_centralizer_zOf e) (e.symm u) ^ 2 = zCent (zOf e) := by
    rw [← map_pow, ← map_pow, hu, inclusion_symm_zS]
  have hh2 : Subgroup.inclusion (le_centralizer_zOf e) (e.symm v) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, hv, map_one, map_one]
  have hg : orderOf (Subgroup.inclusion (le_centralizer_zOf e) (e.symm u)) = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (by rw [pow_one, hg2]; exact hzne)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hg2, hz2])
  have hc : Commute (Subgroup.inclusion (le_centralizer_zOf e) (e.symm v)) (zCent (zOf e)) :=
    mem_center_iff.1 (zCent_mem_center _) _
  have hle : ∀ w : centralizer ({zOf e} : Set H), w ^ 2 = 1 → orderOf w ≠ 2 ^ (1 + 1) := by
    intro w hw h
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw)
    rw [h] at this
    norm_num at this
  apply not_isConj_mk_of_orderOf_ne (zCent_mem_center _) hz2
  · rw [hg]
    exact (hle _ hh2).symm
  · rw [hg]
    exact (hle _ (by rw [hc.mul_pow, hh2, hz2, one_mul])).symm

end Embedding

section Data

variable {H : Type*} [Group H] {S : Subgroup H} {n : ℕ} (e : ↥S ≃* SModel n) (hn : 3 ≤ n)

@[expose] noncomputable def footeCoreOf :
    FooteCore (centralizerQuot (zOf e)) (sylowQuot S (zOf e)) (n - 1) n :=
  { (footeCoreModel hn).mapOfInjOn (embT e) (embT_eq_one e) with
    T_eq := (map_top_embT e).symm.trans
      ((footeCoreModel hn).mapOfInjOn (embT e) (embT_eq_one e)).T_eq }

theorem Astar_footeCoreOf :
    (footeCoreOf e hn).Astar = (footeCoreModel hn).Astar.map (embT e) :=
  FooteCore.Astar_mapOfInjOn (footeCoreModel hn) (embT e) (embT_eq_one e)

theorem orderOf_embT (x : TM n) : orderOf (embT e x) = orderOf x :=
  orderOf_injective _ (embT_injective e) x

@[expose] noncomputable def footeDataOf :
    FooteData (centralizerQuot (zOf e)) (sylowQuot S (zOf e)) (n - 1) n :=
  { footeCoreOf e hn with
    fusion_i := by
      rintro _ ⟨x, hx, rfl⟩ hx2 hxa _ ⟨r, hr, rfl⟩ hr2
      rw [orderOf_embT] at hx2 hr2
      rw [← map_mul]
      exact not_isConj_embT e hn (lifts_A hn _ (aT_mem_AT hn) (orderOf_aT hn))
        (lifts_i hn x hx hx2 (fun h => hxa (by rw [h]; rfl)) r hr hr2)
    fusion_ii := by
      rintro _ ⟨r, hr, rfl⟩ hr2
      rw [orderOf_embT] at hr2
      change ¬ IsConj (embT e (aT n)) (embT e r * embT e (b₁T hn))
      rw [← map_mul]
      exact not_isConj_embT e hn (lifts_A hn _ (aT_mem_AT hn) (orderOf_aT hn))
        (lifts_ii hn r hr hr2)
    fusion_iii := by
      rintro _ ⟨x, hx, rfl⟩ hx2 hxa _ ⟨y, hy, rfl⟩ hy2 hya _ ⟨r, hr, rfl⟩ hr2 hc
      rw [orderOf_embT] at hx2 hy2 hr2
      rw [← map_mul] at hc
      exact not_isConj_embT e hn (lifts_A hn y hy hy2)
        (lifts_i hn x hx hx2 (fun h => hxa (by rw [h]; rfl)) r hr hr2) hc.symm
    fusion_iv := by
      rintro _ ⟨x, hx, rfl⟩ hx2 hxa _ ⟨r, hr, rfl⟩ hr2
      rw [orderOf_embT] at hx2 hr2
      change ¬ IsConj (embT e x * embT e r * embT e (b₁T hn)) (embT e x * embT e (b₀T hn))
      rw [← map_mul, ← map_mul, ← map_mul]
      obtain ⟨h1, h2⟩ := lifts_iv hn x hx hx2 (fun h => hxa (by rw [h]; rfl)) r hr hr2
      exact not_isConj_embT e hn h1 h2
    fusion_v := by
      rintro _ ⟨r, hr, rfl⟩ hr2
      rw [orderOf_embT] at hr2
      change ¬ IsConj (embT e (aT n)) (embT e r * (embT e (tT n) * embT e r * (embT e (tT n))⁻¹))
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact not_isConj_embT e hn (lifts_A hn _ (aT_mem_AT hn) (orderOf_aT hn))
        (lifts_v hn r hr hr2) }

theorem liftsSquareToZ_footeDataOf : LiftsSquareToZ S (zOf e) (footeDataOf e hn).toFooteCore := by
  intro g hgS hmem hord
  have hg : (QuotientGroup.mk g : centralizerQuot (zOf e)) =
      embT e (QuotientGroup.mk (e ⟨g, hgS⟩)) := by
    rw [embT_mk, embS_apply, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨x, hx, hxg⟩ : ∃ x : TM n, LiftsSqZ x ∧ embT e x = QuotientGroup.mk g := by
    rcases hmem with ⟨x, hx, hxg⟩ | hA
    · refine ⟨x, lifts_A hn x hx ?_, hxg⟩
      rw [← orderOf_embT e, hxg]
      exact hord
    · have hA' : (QuotientGroup.mk g : centralizerQuot (zOf e)) ∈
          (footeCoreModel hn).Astar.map (embT e) := by
        rw [← Astar_footeCoreOf e hn]
        exact hA
      obtain ⟨x, hx, hxg⟩ := hA'
      refine ⟨x, lifts_Astar hn x hx ?_, hxg⟩
      rw [← orderOf_embT e, hxg]
      exact hord
  have hsq := hx _ (embT_injective e (hxg.trans hg)).symm
  calc (g : H) ^ 2 = ((⟨g, hgS⟩ ^ 2 : ↥S) : H) := rfl
    _ = zOf e := by rw [← e.symm_apply_apply (⟨g, hgS⟩ ^ 2), map_pow, hsq]; rfl

end Data

theorem footeData_of_psl6Sylow {H : Type} [Group H] [Finite H] (S : Sylow 2 H)
    (hS : ∃ (p f : ℕ) (L : Type) (_ : Group L), p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧
      CFSG.Blueprint.LieModel L .PSL 6 p f ∧ ∃ P : Sylow 2 L, Nonempty (↥S ≃* ↥P)) :
    ∃ z : H, (Subgroup.center ↥(S : Subgroup H)).map (S : Subgroup H).subtype = Subgroup.zpowers z ∧
      orderOf z = 2 ∧ ∃ (m n : ℕ) (D : FooteData (centralizerQuot z) (sylowQuot S z) m n),
        LiftsSquareToZ S z D.toFooteCore := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_mulEquiv_sModel S hS
  exact ⟨zOf e, center_eq_zpowers_zOf e hn, orderOf_zOf e hn, n - 1, n, footeDataOf e hn,
    liftsSquareToZ_footeDataOf e hn⟩

end CFSG.CGT.Foote81L6.Bridge
