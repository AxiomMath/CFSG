module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem local_mem_sup_decomp {G : Type} [Group G] {S1 S2 : Subgroup G}
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) {s : G} (hs : s ∈ S1 ⊔ S2) :
    ∃ s1 ∈ S1, ∃ s2 ∈ S2, s1 * s2 = s := by
  rw [Subgroup.sup_eq_closure] at hs
  refine Subgroup.closure_induction (p := fun z _ => ∃ s1 ∈ S1, ∃ s2 ∈ S2, s1 * s2 = z)
    ?_ ?_ ?_ ?_ hs
  · rintro z (hz | hz)
    · exact ⟨z, hz, 1, S2.one_mem, by simp⟩
    · exact ⟨1, S1.one_mem, z, hz, by simp⟩
  · exact ⟨1, S1.one_mem, 1, S2.one_mem, by simp⟩
  · rintro a b _ _ ⟨s1, hs1, s2, hs2, rfl⟩ ⟨s1', hs1', s2', hs2', rfl⟩
    refine ⟨s1 * s1', S1.mul_mem hs1 hs1', s2 * s2', S2.mul_mem hs2 hs2', ?_⟩
    calc
      (s1 * s1') * (s2 * s2') = s1 * (s1' * (s2 * s2')) := by group
      _ = s1 * ((s1' * s2) * s2') := by group
      _ = s1 * ((s2 * s1') * s2') := by rw [hcomm s1' hs1' s2 hs2]
      _ = (s1 * s2) * (s1' * s2') := by group
  · rintro a _ ⟨s1, hs1, s2, hs2, rfl⟩
    refine ⟨s1⁻¹, S1.inv_mem hs1, s2⁻¹, S2.inv_mem hs2, ?_⟩
    rw [mul_inv_rev]
    exact hcomm s1⁻¹ (S1.inv_mem hs1) s2⁻¹ (S2.inv_mem hs2)

private theorem local_u_comm {G : Type} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  haveI : IsMulCommutative E := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) (⟨b, hb⟩ : E))

private theorem local_u_inv {G : Type} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) {a : G} (ha : a ∈ E) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE.2 a ha)

private theorem local_card_le_sq_inf_cent {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) {v : G}
    (hnorm : ∀ e ∈ E, v * e * v⁻¹ ∈ E) (hv2 : v * v = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({v} : Set G)) *
      Nat.card ↥(E ⊓ centralizer ({v} : Set G)) := by
  have hvv : v * v = 1 := hv2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hvE : ∀ e ∈ E, v * e * v ∈ E := fun e he => by
    simpa [hvinv] using hnorm e he
  let φ : E →* E :=
    { toFun := fun e => ⟨(e : G) * (v * (e : G) * v), E.mul_mem e.2 (hvE (e : G) e.2)⟩
      map_one' := Subtype.ext (by
        change (1 : G) * (v * 1 * v) = 1
        rw [one_mul, mul_one, hvv])
      map_mul' := fun s t => Subtype.ext (by
        change (s : G) * t * (v * ((s : G) * t) * v) =
          (s : G) * (v * s * v) * (t * (v * t * v))
        have hc := local_u_comm hE t.2 (hvE s s.2)
        have h1 : v * ((s : G) * t) * v = (v * s * v) * (v * t * v) := by
          calc v * ((s : G) * t) * v = v * s * (v * v) * t * v := by rw [hvv]; group
            _ = (v * s * v) * (v * t * v) := by group
        rw [h1]
        calc (s : G) * t * ((v * s * v) * (v * t * v))
            = s * (t * (v * s * v)) * (v * t * v) := by group
          _ = s * ((v * s * v) * t) * (v * t * v) := by rw [hc]
          _ = s * (v * s * v) * (t * (v * t * v)) := by group) }
  set F := E ⊓ centralizer ({v} : Set G) with hF
  have hmemF : ∀ e : E, v * (e : G) * v = e → (e : G) ∈ F := fun e he => by
    refine Subgroup.mem_inf.mpr ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (e : G) * v = (v * e * v) * v := by rw [he]
      _ = v * e * (v * v) := by group
      _ = v * e := by rw [hvv, mul_one]
  have hker : φ.ker ≤ F.subgroupOf E := fun e he => by
    have h1 : (e : G) * (v * e * v) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    rw [eq_inv_of_mul_eq_one_right h1, local_u_inv hE e.2]
  have hrange : φ.range ≤ F.subgroupOf E := by
    rintro _ ⟨e, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    change v * ((e : G) * (v * e * v)) * v = (e : G) * (v * e * v)
    have hc := local_u_comm hE e.2 (hvE e e.2)
    calc v * ((e : G) * (v * e * v)) * v = v * ((v * e * v) * e) * v := by rw [hc]
      _ = (v * v) * e * v * e * v := by group
      _ = e * v * e * v := by rw [hvv, one_mul]
      _ = e * (v * e * v) := by group
  have hcardF : Nat.card (F.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcardF, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)

private theorem local_four_le_card_inf_cent_of_card_sixteen {G : Type} [Group G] [Finite G]
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 16) {v : G}
    (hnorm : ∀ e ∈ E, v * e * v⁻¹ ∈ E) (hv2 : v * v = 1) :
    4 ≤ Nat.card ↥(E ⊓ centralizer ({v} : Set G)) := by
  have h := local_card_le_sq_inf_cent hE hnorm hv2
  rw [hcard] at h
  by_contra hlt
  have h3 : Nat.card ↥(E ⊓ centralizer ({v} : Set G)) ≤ 3 := by omega
  have h9 := Nat.mul_le_mul h3 h3
  omega

private theorem local_cent_lemma {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 16) {v : G}
    (hv2 : v * v = 1) (hnorm : ∀ e ∈ E, v * e * v⁻¹ ∈ E) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A ∧ A ≤ Subgroup.zpowers v ⊔ E ∧
      A ≤ Subgroup.centralizer ({v} : Set G) ∧ 8 ≤ Nat.card A := by
  classical
  set D : Subgroup G := E ⊓ Subgroup.centralizer ({v} : Set G) with hD
  have hDleE : D ≤ E := inf_le_left
  have hDleC : D ≤ Subgroup.centralizer ({v} : Set G) := inf_le_right
  have hcD : ∀ a ∈ Subgroup.zpowers v, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbv : Commute b v :=
      (commute_iff_eq b v).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hb).2)
    exact (hbv.symm.zpow_left k).eq
  have hDea : CFSG.Open.IsElemAbelian 2 D := hE.mono hDleE
  have hVea : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers v) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) (by rw [pow_two]; exact hv2)
  have hAea : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers v ⊔ D) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hVea hDea hcD
  have hAle : Subgroup.zpowers v ⊔ D ≤ Subgroup.zpowers v ⊔ E :=
    sup_le le_sup_left (hDleE.trans le_sup_right)
  have hAcent : Subgroup.zpowers v ⊔ D ≤ Subgroup.centralizer ({v} : Set G) :=
    sup_le
      (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (show v * v = v * v from rfl)))
      hDleC
  have hAcard : 8 ≤ Nat.card ↥(Subgroup.zpowers v ⊔ D) := by
    by_cases hvE : v ∈ E
    · have hEcent : E ≤ Subgroup.centralizer ({v} : Set G) := by
        intro e he
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hE.comm he hvE
      have hDE : D = E :=
        le_antisymm hDleE (le_inf le_rfl hEcent)
      have hzpE : Subgroup.zpowers v ≤ E := Subgroup.zpowers_le.mpr hvE
      have hAeq : Subgroup.zpowers v ⊔ D = E := by
        rw [hDE, sup_eq_right.mpr hzpE]
      rw [hAeq, hcard]
      norm_num
    · have hvne : v ≠ 1 := fun h => hvE (h ▸ E.one_mem)
      have hv2pow : v ^ 2 = 1 := by rw [pow_two]; exact hv2
      have hord : orderOf v = 2 := orderOf_eq_prime hv2pow hvne
      have hD4 : 4 ≤ Nat.card D :=
        local_four_le_card_inf_cent_of_card_sixteen hE hcard hnorm hv2
      have hvnotD : v ∉ D := fun hvD => hvE (hDleE hvD)
      have hinf_bot : Subgroup.zpowers v ⊓ D = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
        have hxmem : x = 1 ∨ x = v := by
          rw [mem_zpowers_iff_mem_range_orderOf, hord] at hx1
          simp only [Finset.mem_image, Finset.mem_range] at hx1
          obtain ⟨a, ha, hav⟩ := hx1
          interval_cases a
          · left; simpa using hav.symm
          · right; simpa using hav.symm
        rcases hxmem with h1 | hv
        · exact h1
        · exact absurd (hv ▸ hx2) hvnotD
      have hcardA : Nat.card ↥(Subgroup.zpowers v ⊔ D) = 2 * Nat.card D := by
        rw [sec124_card_sup hcD hinf_bot, Nat.card_zpowers, hord]
      rw [hcardA]
      omega
  exact ⟨Subgroup.zpowers v ⊔ D, hAea, hAle, hAcent, hAcard⟩

theorem sec8t84_rank_low {G : Type} [Group G] [Finite G] {S1 S2 E1 E2 : Subgroup G}
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hinf : S1 ⊓ S2 = ⊥)
    (hE1 : E1 ≤ S1) (hE2 : E2 ≤ S2)
    (he1 : CFSG.Open.IsElemAbelian 2 E1) (hc1 : Nat.card E1 = 16)
    (he2 : CFSG.Open.IsElemAbelian 2 E2) (hc2 : Nat.card E2 = 16)
    (hn1 : ∀ a ∈ S1, ∀ e ∈ E1, a * e * a⁻¹ ∈ E1) (hn2 : ∀ a ∈ S2, ∀ e ∈ E2, a * e * a⁻¹ ∈ E2)
    {s : G} (hs : s ∈ S1 ⊔ S2) (hs2 : s * s = 1) :
    ∃ A : Subgroup G, A ≤ centralizer ({s} : Set G) ∧ CFSG.Open.IsElemAbelian 2 A ∧
      2 ^ 6 ≤ Nat.card A := by
  classical
  obtain ⟨s1, hs1, s2, hs2m, hprod⟩ := local_mem_sup_decomp hcomm hs
  have hsq : (s1 * s1) * (s2 * s2) = 1 := by
    have h : (s1 * s2) * (s1 * s2) = 1 := by rw [hprod]; exact hs2
    have heq : (s1 * s2) * (s1 * s2) = (s1 * s1) * (s2 * s2) := by
      calc
        (s1 * s2) * (s1 * s2) = s1 * (s2 * (s1 * s2)) := by group
        _ = s1 * ((s2 * s1) * s2) := by group
        _ = s1 * ((s1 * s2) * s2) := by rw [← hcomm s1 hs1 s2 hs2m]
        _ = (s1 * s1) * (s2 * s2) := by group
    rwa [heq] at h
  have hs1sq : s1 * s1 = 1 := by
    have hmem : s1 * s1 ∈ S1 ⊓ S2 := by
      refine Subgroup.mem_inf.mpr ⟨S1.mul_mem hs1 hs1, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact S2.inv_mem (S2.mul_mem hs2m hs2m)
    exact Subgroup.mem_bot.mp (hinf ▸ hmem)
  have hs2sq : s2 * s2 = 1 := by
    have hmem : s2 * s2 ∈ S1 ⊓ S2 := by
      refine Subgroup.mem_inf.mpr ⟨?_, S2.mul_mem hs2m hs2m⟩
      rw [eq_inv_of_mul_eq_one_right hsq]
      exact S1.inv_mem (S1.mul_mem hs1 hs1)
    exact Subgroup.mem_bot.mp (hinf ▸ hmem)
  obtain ⟨A1, hA1ea, hA1le, hA1cent, hA1card⟩ :=
    local_cent_lemma (v := s1) he1 hc1 hs1sq (hn1 s1 hs1)
  obtain ⟨A2, hA2ea, hA2le, hA2cent, hA2card⟩ :=
    local_cent_lemma (v := s2) he2 hc2 hs2sq (hn2 s2 hs2m)
  have hA1S1 : A1 ≤ S1 := hA1le.trans (sup_le (Subgroup.zpowers_le.mpr hs1) hE1)
  have hA2S2 : A2 ≤ S2 := hA2le.trans (sup_le (Subgroup.zpowers_le.mpr hs2m) hE2)
  have hcommA : ∀ a ∈ A1, ∀ b ∈ A2, a * b = b * a :=
    fun a ha b hb => hcomm a (hA1S1 ha) b (hA2S2 hb)
  have hinfA : A1 ⊓ A2 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ S1 ⊓ S2 := Subgroup.mem_inf.mpr ⟨hA1S1 hx1, hA2S2 hx2⟩
    exact Subgroup.mem_bot.mp (hinf ▸ hmem)
  have hAea : CFSG.Open.IsElemAbelian 2 (A1 ⊔ A2) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hA1ea hA2ea hcommA
  have hcardA : Nat.card ↥(A1 ⊔ A2) = Nat.card A1 * Nat.card A2 :=
    sec124_card_sup hcommA hinfA
  have hA1cent_s : A1 ≤ Subgroup.centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx1 : x ∈ S1 := hA1S1 hx
    have hxs1 : x * s1 = s1 * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hA1cent hx)
    have hxs2 : x * s2 = s2 * x := hcomm x hx1 s2 hs2m
    calc x * s = x * (s1 * s2) := by rw [hprod]
      _ = (x * s1) * s2 := by group
      _ = (s1 * x) * s2 := by rw [hxs1]
      _ = s1 * (x * s2) := by group
      _ = s1 * (s2 * x) := by rw [hxs2]
      _ = (s1 * s2) * x := by group
      _ = s * x := by rw [hprod]
  have hA2cent_s : A2 ≤ Subgroup.centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx2 : x ∈ S2 := hA2S2 hx
    have hxs2 : x * s2 = s2 * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hA2cent hx)
    have hxs1 : x * s1 = s1 * x := (hcomm s1 hs1 x hx2).symm
    calc x * s = x * (s1 * s2) := by rw [hprod]
      _ = (x * s1) * s2 := by group
      _ = (s1 * x) * s2 := by rw [hxs1]
      _ = s1 * (x * s2) := by group
      _ = s1 * (s2 * x) := by rw [hxs2]
      _ = (s1 * s2) * x := by group
      _ = s * x := by rw [hprod]
  have hAcent_s : A1 ⊔ A2 ≤ Subgroup.centralizer ({s} : Set G) :=
    sup_le hA1cent_s hA2cent_s
  refine ⟨A1 ⊔ A2, hAcent_s, hAea, ?_⟩
  rw [hcardA]
  calc 2 ^ 6 = 8 * 8 := by norm_num
    _ ≤ Nat.card A1 * Nat.card A2 := Nat.mul_le_mul hA1card hA2card

end CFSG.OddStandard.SmallF3.Omega
