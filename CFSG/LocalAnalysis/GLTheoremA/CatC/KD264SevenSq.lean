module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264GenCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Quasi
public import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem isSimpleGroup_quotient_of_max {Q : Type*} [Group Q] {N : Subgroup Q} [N.Normal]
    (hnt : Nontrivial (Q ⧸ N))
    (hmax : ∀ K : Subgroup Q, K.Normal → N ≤ K → K = N ∨ K = ⊤) : IsSimpleGroup (Q ⧸ N) :=
  { toNontrivial := hnt
    eq_bot_or_eq_top_of_normal := fun K hK' => by
      have hcomap : (K.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = K :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K
      have hNK : N ≤ K.comap (QuotientGroup.mk' N) := by
        intro x hx
        rw [Subgroup.mem_comap,
          show QuotientGroup.mk' N x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
        exact K.one_mem
      rcases hmax (K.comap (QuotientGroup.mk' N)) (Subgroup.Normal.comap hK' _) hNK with h | h
      · left
        rw [← hcomap, h, QuotientGroup.map_mk'_self]
      · right
        rw [← hcomap, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] }

theorem subsingleton_of_perfect_comm {H : Type*} [Group H] (hperf : commutator H = ⊤)
    (hc : ∀ a b : H, a * b = b * a) : Subsingleton H := by
  refine ⟨fun a b => ?_⟩
  have hbot : commutator H = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hc x y
  have ha : a ∈ commutator H := hperf ▸ Subgroup.mem_top a
  have hb : b ∈ commutator H := hperf ▸ Subgroup.mem_top b
  rw [hbot, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem perfect_dvd_168 {H : Type} [Group H] [Finite H] (hperf : commutator H = ⊤)
    (hnt : Nontrivial H) (hd : Nat.card H ∣ 168) : IsSimpleGroup H ∧ Nat.card H = 168 := by
  obtain ⟨N, hNn, hNt, hmax⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148K.exists_maximal_normal_ne_top H hnt
  haveI := hNn
  have hntQ : Nontrivial (H ⧸ N) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hNt
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  haveI hs : IsSimpleGroup (H ⧸ N) := isSimpleGroup_quotient_of_max hntQ hmax
  have hperfQ : commutator (H ⧸ N) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N), ← Subgroup.map_commutator, ← commutator_def, hperf]
  have hnab : ∃ a b : H ⧸ N, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have := subsingleton_of_perfect_comm hperfQ h
    exact not_nontrivial (H ⧸ N) hntQ
  have hdQ : Nat.card (H ⧸ N) ∣ 168 := (Subgroup.card_quotient_dvd_card N).trans hd
  have h168 := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.card_eq_168_of_dvd hnab hdQ
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hH168 : Nat.card H = 168 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    rw [hcard, h168] at hle ⊢
    have hN0 : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hN1 : Nat.card N = 1 := by
    rw [hcard, h168] at hH168
    omega
  have hNbot : N = ⊥ := (Subgroup.eq_bot_iff_card N).2 hN1
  subst hNbot
  exact ⟨(QuotientGroup.quotientBot (G := H)).symm.isSimpleGroup, hH168⟩

theorem commutator_eq_top_of_le {G : Type*} [Group G] {L : Subgroup G} (h : L ≤ ⁅L, L⁆) :
    commutator ↥L = ⊤ := by
  have h1 : (commutator ↥L).map L.subtype = (⊤ : Subgroup ↥L).map L.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) h
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  exact Subgroup.map_injective L.subtype_injective h1

theorem center_eq_bot_of_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (hnab : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)

theorem isQuasisimple_of_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (hperf : commutator H = ⊤) (hnab : ∃ a b : H, a * b ≠ b * a) : CFSG.Open.IsQuasisimple H :=
  ⟨hperf, ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnab)).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

theorem exists_not_comm_of_perfect {H : Type*} [Group H] (hperf : commutator H = ⊤)
    (hnt : Nontrivial H) : ∃ a b : H, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have := subsingleton_of_perfect_comm hperf h
  exact not_nontrivial H hnt

theorem exists_component_of_perfect_1176 {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 7) (hC : Nat.card (Subgroup.centralizer ({z} : Set G)) = 1176)
    {L : Subgroup G} (hLC : L ≤ Subgroup.centralizer ({z} : Set G)) (hperf : L ≤ ⁅L, L⁆)
    (hne : L ≠ ⊥) : ∃ J : Subgroup G, GLAPComponent 7 (Subgroup.centralizer ({z} : Set G)) J := by
  classical
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  have hp7 : Nat.Prime 7 := by norm_num
  have hperfL : commutator ↥L = ⊤ := commutator_eq_top_of_le hperf
  haveI hntL : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hne
  have hzc : ∀ l ∈ L, z * l = l * z := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)).symm
  have hLdvd : Nat.card L ∣ 1176 := hC ▸ Subgroup.card_dvd_of_le hLC
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  by_cases hzL : z ∈ L
  ·
    set zl : ↥L := ⟨z, hzL⟩
    set Zl : Subgroup ↥L := Subgroup.zpowers zl with hZl
    have hZlc : Zl ≤ Subgroup.center ↥L := by
      rw [hZl, Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2).symm
    haveI hZln : Zl.Normal := KD264Gen.zpowers_normal_of_mem_center (Subgroup.zpowers_le.1 hZlc)
    have hZcard : Nat.card Zl = 7 := by
      rw [hZl, Nat.card_zpowers, Subgroup.orderOf_mk, hz]
    have hLQ := Subgroup.card_eq_card_quotient_mul_card_subgroup Zl
    have hperfQ : commutator (↥L ⧸ Zl) = ⊤ := by
      rw [commutator_def, ← Subgroup.map_top_of_surjective (QuotientGroup.mk' Zl)
        (QuotientGroup.mk'_surjective Zl), ← Subgroup.map_commutator, ← commutator_def, hperfL]
    have hntQ : Nontrivial (↥L ⧸ Zl) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have hLZ : (⊤ : Subgroup ↥L) ≤ Subgroup.center ↥L := by
        intro x _
        apply hZlc
        rw [← QuotientGroup.eq_one_iff]
        exact Subsingleton.elim _ _
      obtain ⟨a, b, hab⟩ := exists_not_comm_of_perfect hperfL hntL
      exact hab ((Subgroup.mem_center_iff.1 (hLZ (Subgroup.mem_top b))) a)
    have hQdvd : Nat.card (↥L ⧸ Zl) ∣ 168 := by
      have h1 : Nat.card (↥L ⧸ Zl) * Nat.card Zl ∣ 1176 := hLQ ▸ hLdvd
      rw [hZcard] at h1
      have h2 : Nat.card (↥L ⧸ Zl) * 7 ∣ 168 * 7 := by
        rw [show (168 * 7 : ℕ) = 1176 by norm_num]; exact h1
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2
    obtain ⟨hQs, hQ168⟩ := perfect_dvd_168 hperfQ hntQ hQdvd
    have hL1176 : Nat.card L = 1176 := by rw [hLQ, hQ168, hZcard]
    have hLeq : L = C := Subgroup.eq_of_le_of_card_ge hLC (by rw [hL1176, hC])
    have hcen : Subgroup.center ↥L = Zl := by
      have hn : ((Subgroup.center ↥L).map (QuotientGroup.mk' Zl)).Normal :=
        (Subgroup.center ↥L).normal_of_characteristic.map _ (QuotientGroup.mk'_surjective Zl)
      haveI := hn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Subgroup.center ↥L).map (QuotientGroup.mk' Zl)) with h | h
      · refine le_antisymm (fun c hc => ?_) hZlc
        have : QuotientGroup.mk' Zl c ∈ (Subgroup.center ↥L).map (QuotientGroup.mk' Zl) :=
          ⟨c, hc, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact this
      · exfalso
        obtain ⟨a, b, hab⟩ := exists_not_comm_of_perfect hperfQ hntQ
        obtain ⟨a', ha', rfl⟩ := (h ▸ Subgroup.mem_top a : a ∈ _)
        apply hab
        obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective Zl b
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 ha' b').symm]
    have hq : CFSG.Open.IsQuasisimple ↥L :=
      ⟨hperfL, (QuotientGroup.quotientMulEquivOfEq hcen).isSimpleGroup⟩
    refine ⟨L, CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp7 hq
      (by rw [hL1176]; norm_num) hLC ?_⟩
    rw [hLeq, Subgroup.subgroupOf_self]
    infer_instance
  ·
    have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; rw [hzc h hh, mul_inv_cancel_right]; exact hh
      · intro hh
        have e := hzc _ hh
        have : z * h * z⁻¹ = h := by
          calc z * h * z⁻¹ = z⁻¹ * (z * (z * h * z⁻¹)) := by group
            _ = z⁻¹ * ((z * h * z⁻¹) * z) := by rw [e]
            _ = h := by group
        exact this ▸ hh
    have hprod := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hzN
    have hzcard : Nat.card (Subgroup.zpowers z) = 7 := by rw [Nat.card_zpowers, hz]
    have hinf : Nat.card ↥(Subgroup.zpowers z ⊓ L) = 1 := by
      have hd : Nat.card ↥(Subgroup.zpowers z ⊓ L) ∣ 7 := by
        rw [← hzcard]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp7).1 hd with h1 | h7
      · exact h1
      · exfalso
        have heq : Subgroup.zpowers z ⊓ L = Subgroup.zpowers z :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h7, hzcard])
        have : z ∈ Subgroup.zpowers z ⊓ L := by rw [heq]; exact Subgroup.mem_zpowers z
        exact hzL (Subgroup.mem_inf.1 this).2
    rw [hinf, mul_one, hzcard] at hprod
    have hMC : Subgroup.zpowers z ⊔ L ≤ C := sup_le (Subgroup.zpowers_le.2 hzC) hLC
    have hMdvd : Nat.card ↥(Subgroup.zpowers z ⊔ L) ∣ Nat.card C := Subgroup.card_dvd_of_le hMC
    rw [hprod, hC, show (1176 : ℕ) = 7 * 168 by norm_num] at hMdvd
    have hLd : Nat.card L ∣ 168 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hMdvd
    obtain ⟨hLs, hL168⟩ := perfect_dvd_168 hperfL hntL hLd
    have hMeq : Subgroup.zpowers z ⊔ L = C :=
      Subgroup.eq_of_le_of_card_ge hMC (by rw [hprod, hL168, hC])
    have hq : CFSG.Open.IsQuasisimple ↥L :=
      isQuasisimple_of_simple hperfL (exists_not_comm_of_perfect hperfL hntL)
    refine ⟨L, CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp7 hq
      (by rw [hL168]; norm_num) hLC ?_⟩
    have hCN : C ≤ Subgroup.normalizer (L : Set G) := by
      rw [← hMeq]; exact sup_le hzN Subgroup.le_normalizer
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 hCN

theorem map_conj_centralizer {T : Type*} [Group T] (g z : T) :
    (Subgroup.centralizer ({z} : Set T)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * z * g⁻¹} : Set T) := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hy]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group

theorem centralizer_zpowers_eq {T : Type*} [Group T] (w : T) :
    Subgroup.centralizer ((Subgroup.zpowers w : Subgroup T) : Set T) =
      Subgroup.centralizer ({w} : Set T) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers w))
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute x w := Subgroup.mem_centralizer_singleton_iff.1 hx
    exact ((hc.zpow_right k).eq).symm

theorem kd264RowData_of_sq {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hfac : (Nat.card T).factorization p = 2) {z : T} (hz : orderOf z = p) {J : Subgroup T}
    (hJ : GLAPComponent p (Subgroup.centralizer ({z} : Set T)) J) : KD264RowData p T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro A hA _ k hk1 hk2 hpk
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  have hdvd : p ^ n ∣ Nat.card T := hn ▸ Subgroup.card_subgroup_dvd_card A
  have hn2 : n ≤ 2 := by
    rw [← hfac]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 hdvd
  have hk : k = 1 ∧ n = 2 := by
    have : p ^ (k + 1) ≤ p ^ n := hn ▸ hpk
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨rfl, rfl⟩ := hk
  have hzP : IsPGroup p (Subgroup.zpowers z) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hz]; exact ⟨1, (pow_one p).symm⟩
  obtain ⟨P, hzle⟩ := hzP.exists_le_sylow
  have hAc : Nat.card A = p ^ (Nat.card T).factorization p := by rw [hn, hfac]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T P (Sylow.ofCard A hAc)
  have hmem : g * z * g⁻¹ ∈ A := by
    have : g * z * g⁻¹ ∈ ((g • P : Sylow p T) : Subgroup T) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨z, hzle (Subgroup.mem_zpowers z), by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rwa [hg] at this
  refine ⟨Subgroup.zpowers (g * z * g⁻¹), Subgroup.zpowers_le.2 hmem, ?_, ?_⟩
  · rw [Nat.card_zpowers, show g * z * g⁻¹ = MulAut.conj g z from rfl, MulEquiv.orderOf_eq, hz,
      pow_one]
  · refine ⟨J.map (MulAut.conj g).toMonoidHom, ?_⟩
    rw [centralizer_zpowers_eq, ← map_conj_centralizer]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj g) hJ

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven
