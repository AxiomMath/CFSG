module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

private noncomputable def psiHom {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : ↥L →* ProjSim Q :=
  (ffInducesHom hm e).comp (Subgroup.inclusion Subgroup.le_normalizer)

private lemma psiHom_apply {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    psiHom hm e l = ffInducesHom hm e ⟨l, Subgroup.le_normalizer l.2⟩ := by
  apply congrArg (ffInducesHom hm e)
  exact Subtype.ext rfl

private lemma psiHom_eq_one_iff {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hperf : commutator ↥L = ⊤) (l : ↥L) :
    psiHom hm e l = 1 ↔ l ∈ Subgroup.center ↥L := by
  rw [psiHom_apply, ffInducesHom_eq_one_iff hm e hperf]
  constructor
  · intro hc
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) (x : G) x.2)
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩)

private lemma exists_psiHom_eq {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {f : ProjSim Q}
    (hf : SimInOmegaStar hQ f) : ∃ l : ↥L, psiHom hm e l = f := by
  obtain ⟨y, hy, hyf⟩ := hf
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm ⟨y, hy⟩)
  refine ⟨q, ?_⟩
  have heq : e (QuotientGroup.mk q) = ⟨y, hy⟩ := by
    rw [hq]; exact e.apply_symm_apply ⟨y, hy⟩
  rw [psiHom_apply, ffInducesHom_of_mem hm e q (Subgroup.le_normalizer q.2), heq]
  simpa using hyf

private lemma mem_center_iff_mem_centerIn {L : Subgroup G} (l : ↥L) :
    l ∈ Subgroup.center ↥L ↔ (l : G) ∈ centerIn L := by
  rw [sec4_mem_centerIn_iff]
  constructor
  · intro h
    refine ⟨l.2, fun k hk => ?_⟩
    simpa only [Subgroup.coe_mul] using
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨k, hk⟩)).symm
  · rintro ⟨_, hcomm⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by simpa only [Subgroup.coe_mul] using (hcomm (y : G) y.2).symm)

theorem sec9ci_centerIn_odd_order [Finite G] {L : Subgroup G} (hL : IsOm6M L) {z : G}
    (hz : z ∈ centerIn L) : Odd (orderOf z) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hz2 : (z ^ (orderOf z / 2)) * (z ^ (orderOf z / 2)) = 1 := by
    rw [← pow_two, ← pow_mul, Nat.div_two_mul_two_of_even hodd, pow_orderOf_eq_one]
  have hzt : z ^ (orderOf z / 2) ∈ centerIn L := (centerIn L).pow_mem hz _
  have hne : z ^ (orderOf z / 2) ≠ 1 := by
    intro h
    have hdvd : orderOf z ∣ orderOf z / 2 := orderOf_dvd_of_pow_eq_one h
    have hdivpos : 0 < orderOf z / 2 := by
      have h1 := Nat.two_mul_div_two_of_even hodd
      have h2 := orderOf_pos z
      omega
    have hle : orderOf z ≤ orderOf z / 2 := Nat.le_of_dvd hdivpos hdvd
    have h1 := Nat.two_mul_div_two_of_even hodd
    omega
  exact hne (sec9g_centerIn_sq_eq_one hL hzt hz2)

theorem sec9ci_lift_odd [Finite G] {L : Subgroup G} (hL : IsOm6M L) {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} (hss : s * s = 1)
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) (F : Subgroup (ProjSim Q))
    (hFB : ∀ (b : G) (hb : b ∈ B), ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ ∈ F)
    (hBF : ∀ f ∈ F, ∃ (b : G) (hb : b ∈ B),
      ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ = f)
    {f : ProjSim Q} (hfΩ : SimInOmegaStar hQ f)
    (hfs : f * ffInducesHom hm e ⟨s, hsN⟩ = ffInducesHom hm e ⟨s, hsN⟩ * f)
    (hfF : ∀ f' ∈ F, f * f' * f⁻¹ ∈ F) (hodd : Odd (orderOf f)) :
    ∃ (y : G) (hy : y ∈ L), y * s = s * y ∧ y ∈ Subgroup.normalizer (B : Set G) ∧
      Odd (orderOf y) ∧ ffInducesHom hm e ⟨y, Subgroup.le_normalizer hy⟩ = f := by
  classical
  have hperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  obtain ⟨y₀, hy₀⟩ := exists_psiHom_eq hm e hfΩ
  have hy0L : (y₀ : G) ∈ L := y₀.2
  have hPhiY0 : psiHom hm e y₀ = f := hy₀
  have hy0m_psi : psiHom hm e (y₀ ^ orderOf f) = 1 := by
    rw [map_pow, hPhiY0, pow_orderOf_eq_one]
  have hy0m_center : (y₀ ^ orderOf f : ↥L) ∈ Subgroup.center ↥L :=
    (psiHom_eq_one_iff hm e hperf (y₀ ^ orderOf f)).mp hy0m_psi
  have hy0m_centerIn : (y₀ : G) ^ orderOf f ∈ centerIn L := by
    have h := (mem_center_iff_mem_centerIn (L := L) (y₀ ^ orderOf f)).mp hy0m_center
    simpa only [Subgroup.coe_pow] using h
  have hodd_y0 : Odd (orderOf (y₀ : G)) := by
    have hdvd : orderOf (y₀ : G) ∣ orderOf f * orderOf ((y₀ : G) ^ orderOf f) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat (hodd.mul (sec9ci_centerIn_odd_order hL hy0m_centerIn)) hdvd
  let y1 : G := s * (y₀ : G) * s⁻¹
  have hy1L : y1 ∈ L := (Subgroup.mem_set_normalizer_iff.mp hsN (y₀ : G)).mp hy0L
  have hPhiY0' : ffInducesHom hm e ⟨(y₀ : G), Subgroup.le_normalizer hy0L⟩ = f :=
    (psiHom_apply hm e y₀).symm.trans hPhiY0
  have hPhiy1 : ffInducesHom hm e ⟨y1, Subgroup.le_normalizer hy1L⟩ = f := by
    have hdecomp : (⟨y1, Subgroup.le_normalizer hy1L⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨s, hsN⟩ * ⟨(y₀ : G), Subgroup.le_normalizer hy0L⟩ * ⟨s, hsN⟩⁻¹ := by
      apply Subtype.ext
      show y1 = s * (y₀ : G) * s⁻¹
      rfl
    rw [hdecomp, map_mul, map_mul, map_inv, hPhiY0']
    rw [hfs.symm]
    group
  let z : G := (y₀ : G)⁻¹ * y1
  have hzL : z ∈ L := L.mul_mem (L.inv_mem hy0L) hy1L
  have hPhiZ : ffInducesHom hm e ⟨z, Subgroup.le_normalizer hzL⟩ = 1 := by
    have hdecomp : (⟨z, Subgroup.le_normalizer hzL⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨(y₀ : G), Subgroup.le_normalizer hy0L⟩⁻¹ *
          ⟨y1, Subgroup.le_normalizer hy1L⟩ := by
      apply Subtype.ext
      show z = (y₀ : G)⁻¹ * y1
      rfl
    rw [hdecomp, map_mul, map_inv, hPhiY0', hPhiy1, inv_mul_cancel]
  have hzcenterIn : z ∈ centerIn L := by
    have hcent : z ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hperf ⟨z, Subgroup.le_normalizer hzL⟩).mp hPhiZ
    rw [sec4_mem_centerIn_iff]
    refine ⟨hzL, fun k hk => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hcent k hk).symm
  have hzodd : Odd (orderOf z) := sec9ci_centerIn_odd_order hL hzcenterIn
  have hy1_eq : y1 = (y₀ : G) * z := by
    rw [show z = (y₀ : G)⁻¹ * y1 from rfl]
    group
  have hconj_y1 : s * y1 * s⁻¹ = (y₀ : G) := by
    rw [show y1 = s * (y₀ : G) * s⁻¹ from rfl]
    calc s * (s * (y₀ : G) * s⁻¹) * s⁻¹ = (s * s) * (y₀ : G) * (s⁻¹ * s⁻¹) := by
          group
      _ = (y₀ : G) := by
          rw [hss, one_mul]
          rw [show s⁻¹ * s⁻¹ = 1 from by rw [← mul_inv_rev, hss, inv_one], mul_one]
  have hdecomp_y1 : s * y1 * s⁻¹ = y1 * (s * z * s⁻¹) := by
    have h1 : s * y1 * s⁻¹ = (s * (y₀ : G) * s⁻¹) * (s * z * s⁻¹) := by
      rw [hy1_eq]
      group
    rw [h1, show s * (y₀ : G) * s⁻¹ = y1 from rfl]
  have hmain : (y₀ : G) = (y₀ : G) * z * (s * z * s⁻¹) := by
    calc (y₀ : G) = s * y1 * s⁻¹ := hconj_y1.symm
      _ = y1 * (s * z * s⁻¹) := hdecomp_y1
      _ = (y₀ : G) * z * (s * z * s⁻¹) := by rw [hy1_eq]
  have hcancel : 1 = z * (s * z * s⁻¹) := by
    apply mul_left_cancel (a := (y₀ : G))
    rw [mul_one, ← mul_assoc]
    exact hmain
  have hzs : s * z * s⁻¹ = z⁻¹ := eq_inv_of_mul_eq_one_right hcancel.symm
  let k : ℕ := orderOf z
  have hkodd : Odd k := hzodd
  let u : G := z ^ ((k + 1) / 2)
  have huL : u ∈ L := L.pow_mem ((sec4_mem_centerIn_iff z).mp hzcenterIn).1 _
  have hucenterIn : u ∈ centerIn L := (centerIn L).pow_mem hzcenterIn _
  have huu : u * u = z := by
    rw [show u = z ^ ((k + 1) / 2) from rfl, ← pow_two, ← pow_mul]
    have hk : (k + 1) / 2 * 2 = k + 1 := by
      obtain ⟨t, ht⟩ := hkodd
      omega
    rw [hk, pow_succ, pow_orderOf_eq_one, one_mul]
  have hsu : s * u * s⁻¹ = u⁻¹ := by
    have h1 : s * u * s⁻¹ = (s * z * s⁻¹) ^ ((k + 1) / 2) := by
      rw [show u = z ^ ((k + 1) / 2) from rfl, ← conj_pow]
    rw [h1, hzs, inv_pow]
  let y : G := (y₀ : G) * u
  have hyL : y ∈ L := L.mul_mem hy0L huL
  have hzu : z * u⁻¹ = u := by
    rw [← huu, mul_assoc, mul_inv_cancel, mul_one]
  have hyconj : s * y * s⁻¹ = y := by
    have h1 : s * y * s⁻¹ = (s * (y₀ : G) * s⁻¹) * (s * u * s⁻¹) := by
      rw [show y = (y₀ : G) * u from rfl]
      group
    rw [h1, show s * (y₀ : G) * s⁻¹ = y1 from rfl, hsu, hy1_eq]
    rw [mul_assoc, hzu]
  have hys : y * s = s * y := by
    have h1 : s * y = y * s := by
      calc s * y = (s * y * s⁻¹) * s := by group
        _ = y * s := by rw [hyconj]
    exact h1.symm
  have hu_psi : psiHom hm e ⟨u, huL⟩ = 1 :=
    (psiHom_eq_one_iff hm e hperf ⟨u, huL⟩).mpr
      ((mem_center_iff_mem_centerIn (L := L) ⟨u, huL⟩).mpr hucenterIn)
  have hPhiYpsi : psiHom hm e ⟨y, hyL⟩ = f := by
    have hy_eq : (⟨y, hyL⟩ : ↥L) = ⟨(y₀ : G), hy0L⟩ * ⟨u, huL⟩ := Subtype.ext rfl
    rw [hy_eq, map_mul, hPhiY0, hu_psi, mul_one]
  have hPhiY' : ffInducesHom hm e ⟨y, Subgroup.le_normalizer hyL⟩ = f :=
    (psiHom_apply hm e ⟨y, hyL⟩).symm.trans hPhiYpsi
  have hcomm_y0u : Commute (y₀ : G) u :=
    (((sec4_mem_centerIn_iff u).mp hucenterIn).2 (y₀ : G) hy0L).symm
  have hodd_y : Odd (orderOf y) := by
    have hdvd : orderOf y ∣ orderOf (y₀ : G) * orderOf u := by
      rw [show y = (y₀ : G) * u from rfl]
      exact hcomm_y0u.orderOf_mul_dvd_mul_orderOf
    exact Odd.of_dvd_nat (hodd_y0.mul (sec9ci_centerIn_odd_order hL hucenterIn)) hdvd
  have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
    have hconj_mem : ∀ c ∈ B, y * c * y⁻¹ ∈ B := by
      intro c hc
      have hcL : c ∈ L := hBL hc
      have hc2 : c * c = 1 := by simpa [pow_two] using hB.1.2 c hc
      let a : G := y * c * y⁻¹
      have haL : a ∈ L := L.mul_mem (L.mul_mem hyL hcL) (L.inv_mem hyL)
      have ha_eq : a = MulAut.conj y c := by rw [MulAut.conj_apply]
      have hPhia : ffInducesHom hm e ⟨a, Subgroup.le_normalizer haL⟩ =
          f * ffInducesHom hm e ⟨c, Subgroup.le_normalizer hcL⟩ * f⁻¹ := by
        have hdecomp : (⟨a, Subgroup.le_normalizer haL⟩ :
            ↥(Subgroup.normalizer (L : Set G))) =
            ⟨y, Subgroup.le_normalizer hyL⟩ * ⟨c, Subgroup.le_normalizer hcL⟩ *
              ⟨y, Subgroup.le_normalizer hyL⟩⁻¹ := by
          apply Subtype.ext
          show a = y * c * y⁻¹
          rfl
        rw [hdecomp, map_mul, map_mul, map_inv, hPhiY']
      have hPhiaF : ffInducesHom hm e ⟨a, Subgroup.le_normalizer haL⟩ ∈ F := by
        rw [hPhia]
        exact hfF _ (hFB c hc)
      obtain ⟨c', hc'B, hc'eq⟩ := hBF _ hPhiaF
      have hc'L : c' ∈ L := hBL hc'B
      have hc'2 : c' * c' = 1 := by simpa [pow_two] using hB.1.2 c' hc'B
      let z' : G := a * c'⁻¹
      have hz'L : z' ∈ L := L.mul_mem haL (L.inv_mem hc'L)
      have hPhiZ' : ffInducesHom hm e ⟨z', Subgroup.le_normalizer hz'L⟩ = 1 := by
        have hdecomp : (⟨z', Subgroup.le_normalizer hz'L⟩ :
            ↥(Subgroup.normalizer (L : Set G))) =
            ⟨a, Subgroup.le_normalizer haL⟩ * ⟨c', Subgroup.le_normalizer hc'L⟩⁻¹ := by
          apply Subtype.ext
          show z' = a * c'⁻¹
          rfl
        rw [hdecomp, map_mul, map_inv, hc'eq, mul_inv_cancel]
      have hz'centerIn : z' ∈ centerIn L := by
        have hcent : z' ∈ Subgroup.centralizer (L : Set G) :=
          (ffInducesHom_eq_one_iff hm e hperf ⟨z', Subgroup.le_normalizer hz'L⟩).mp hPhiZ'
        rw [sec4_mem_centerIn_iff]
        refine ⟨hz'L, fun m hm => ?_⟩
        exact (Subgroup.mem_centralizer_iff.mp hcent m hm).symm
      have ha2 : a * a = 1 := by
        show (y * c * y⁻¹) * (y * c * y⁻¹) = 1
        calc
          (y * c * y⁻¹) * (y * c * y⁻¹) = y * c * (y⁻¹ * y) * c * y⁻¹ := by group
          _ = y * c * c * y⁻¹ := by rw [inv_mul_cancel, mul_one]
          _ = y * (c * c) * y⁻¹ := by group
          _ = 1 := by rw [hc2]; group
      have hazc' : a = z' * c' := by
        rw [show z' = a * c'⁻¹ from rfl]
        group
      have hzc' : Commute c' z' :=
        (((sec4_mem_centerIn_iff z').mp hz'centerIn).2 c' hc'L).symm
      have hz'2 : z' * z' = 1 := by
        have ha2' : (z' * c') * (z' * c') = 1 := by rw [← hazc']; exact ha2
        have h1 : (z' * c') * (z' * c') = (z' * z') * (c' * c') :=
          Commute.mul_mul_mul_comm hzc' z' c'
        have h2 : (z' * z') * (c' * c') = 1 := by rw [← h1]; exact ha2'
        rw [hc'2, mul_one] at h2
        exact h2
      have hz'1 : z' = 1 := sec9g_centerIn_sq_eq_one hL hz'centerIn hz'2
      rw [show y * c * y⁻¹ = a from rfl, hazc', hz'1, one_mul]
      exact hc'B
    have hmap_le : B.map (MulAut.conj y).toMonoidHom ≤ B := by
      rintro x ⟨c, hc, rfl⟩
      show y * c * y⁻¹ ∈ B
      exact hconj_mem c hc
    have hcard : Nat.card (B.map (MulAut.conj y).toMonoidHom) = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    have hEq : B.map (MulAut.conj y).toMonoidHom = B :=
      Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq
  exact ⟨y, hyL, hys, hyB, hodd_y, hPhiY'⟩

end CFSG.OddStandard.SmallF3.Omega
