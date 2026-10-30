module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Case2AbComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Maschke
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
  (centralizer_layer_inf_centralizer_pCore_le exists_normal_complement)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem case2ab_core_fact (h : Case2DataAb p P T D F x) : Fact p.Prime := ⟨h.prime⟩

theorem case2ab_core_D_comm (h : Case2DataAb p P T D F x) :
    ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  haveI := h.pdata.D_cyc
  intro a ha b hb
  have := (IsCyclic.isMulCommutative (α := D)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem case2ab_core_T_comm (h : Case2DataAb p P T D F x) :
    ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
  intro a ha b hb
  have := h.pdata.T_comm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem case2ab_core_exists_mul (h : Case2DataAb p P T D F x) :
    ∀ a ∈ P, ∃ t ∈ T, ∃ d ∈ D, a = t * d := by
  intro a ha
  have hP : P = T ⊔ D := h.pdata.sup_eq.symm
  let S : Subgroup Y :=
    { carrier := {a | ∃ t ∈ T, ∃ d ∈ D, a = t * d}
      mul_mem' := by
        rintro _ _ ⟨t, ht, d, hd, rfl⟩ ⟨t', ht', d', hd', rfl⟩
        refine ⟨t * t', T.mul_mem ht ht', d * d', D.mul_mem hd hd', ?_⟩
        have hc : d * t' = t' * d := (h.pdata.comm t' ht' d hd).symm
        calc t * d * (t' * d') = t * (d * t') * d' := by group
          _ = t * (t' * d) * d' := by rw [hc]
          _ = t * t' * (d * d') := by group
      one_mem' := ⟨1, T.one_mem, 1, D.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨t, ht, d, hd, rfl⟩
        refine ⟨t⁻¹, T.inv_mem ht, d⁻¹, D.inv_mem hd, ?_⟩
        rw [mul_inv_rev]
        exact (h.pdata.comm t⁻¹ (T.inv_mem ht) d⁻¹ (D.inv_mem hd)).symm }
  have hle : T ⊔ D ≤ S :=
    sup_le (fun t ht => ⟨t, ht, 1, D.one_mem, (mul_one t).symm⟩)
      (fun d hd => ⟨1, T.one_mem, d, hd, (one_mul d).symm⟩)
  rw [hP] at ha
  exact hle ha

theorem case2ab_core_P_comm (h : Case2DataAb p P T D F x) :
    ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro a ha b hb
  obtain ⟨t, ht, d, hd, rfl⟩ := case2ab_core_exists_mul h a ha
  obtain ⟨t', ht', d', hd', rfl⟩ := case2ab_core_exists_mul h b hb
  have h1 : d * t' = t' * d := (h.pdata.comm t' ht' d hd).symm
  have h2 : d * d' = d' * d := case2ab_core_D_comm h d hd d' hd'
  have h3 : t * t' = t' * t := case2ab_core_T_comm h t ht t' ht'
  have h4 : t * d' = d' * t := h.pdata.comm t ht d' hd'
  calc t * d * (t' * d') = t * (d * t') * d' := by group
    _ = t * (t' * d) * d' := by rw [h1]
    _ = (t * t') * (d * d') := by group
    _ = (t' * t) * (d' * d) := by rw [h3, h2]
    _ = t' * (t * d') * d := by group
    _ = t' * (d' * t) * d := by rw [h4]
    _ = t' * d' * (t * d) := by group

theorem case2ab_core_isPGroup_P (h : Case2DataAb p P T D F x) : IsPGroup p P := by
  obtain ⟨S, hS⟩ := h.sylow
  subst hS
  exact S.isPGroup'

theorem case2ab_core_pCore_le_P (h : Case2DataAb p P T D F x) : CFSG.pCore p Y ≤ P := by
  haveI := case2ab_core_fact h
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS]
  exact (CFSG.pCore_isPGroup (p := p) (G := Y)).le_sylow_of_normal S

theorem case2ab_core_mem_zpowers_of_pow_eq_one (h : Case2DataAb p P T D F x) :
    ∀ d ∈ D, d ^ p = 1 → d ∈ zpowers x := by
  classical
  haveI := case2ab_core_fact h
  haveI : IsCyclic D := h.pdata.D_cyc
  haveI : Fintype D := Fintype.ofFinite D
  intro d hd hdp
  obtain ⟨x', hx'⟩ : ∃ x' : D, (x' : Y) = x := ⟨⟨x, h.pdata.x_mem⟩, rfl⟩
  have hx'ord : orderOf x' = p := by
    rw [← h.pdata.x_ord, ← hx', Subgroup.orderOf_coe]
  have hx'p : x' ^ p = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hx'ord] at this
  have hsub : (zpowers x' : Set D) ⊆ {a : D | a ^ p = 1} := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    show (x' ^ k) ^ p = 1
    calc (x' ^ k) ^ p = (x' ^ k) ^ (p : ℤ) := (zpow_natCast _ _).symm
      _ = x' ^ (k * p) := (zpow_mul _ _ _).symm
      _ = x' ^ ((p : ℤ) * k) := by rw [mul_comm]
      _ = (x' ^ (p : ℤ)) ^ k := zpow_mul _ _ _
      _ = 1 := by rw [zpow_natCast, hx'p, one_zpow]
  have hfin : ({a : D | a ^ p = 1} : Set D).Finite := Set.toFinite _
  have hcard1 : Nat.card ({a : D | a ^ p = 1} : Set D) ≤ p := by
    have h1 : ({a : D | a ^ p = 1} : Set D) =
        ↑(Finset.univ.filter (fun a : D => a ^ p = 1)) := by
      ext a
      simp
    rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact IsCyclic.card_pow_eq_one_le h.prime.pos
  have hcard2 : p ≤ Nat.card (zpowers x' : Set D) := by
    have : Nat.card (zpowers x') = p := by rw [Nat.card_zpowers, hx'ord]
    exact this.ge
  have heq : (zpowers x' : Set D) = {a : D | a ^ p = 1} :=
    Set.Finite.eq_of_subset_of_card_le hfin hsub (hcard1.trans hcard2)
  have hdmem : (⟨d, hd⟩ : D) ∈ zpowers x' := by
    have h1 : (⟨d, hd⟩ : D) ∈ ({a : D | a ^ p = 1} : Set D) := by
      show (⟨d, hd⟩ : D) ^ p = 1
      exact Subtype.ext (by simpa using hdp)
    rw [← heq] at h1
    exact h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdmem
  have h2 := congrArg Subtype.val hk
  simp only [Subgroup.coe_zpow, hx'] at h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩

theorem case2ab_core_x_mem_of_ne_bot (h : Case2DataAb p P T D F x) :
    ∀ C : Subgroup Y, C ≤ D → C ≠ ⊥ → x ∈ C := by
  haveI := case2ab_core_fact h
  intro C hCD hC
  have hCP : C ≤ P := hCD.trans h.pdata.D_le
  have hCp : IsPGroup p C :=
    (case2ab_core_isPGroup_P h).of_injective (Subgroup.inclusion hCP)
      (Subgroup.inclusion_injective hCP)
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC
  obtain ⟨n, hn, hcard⟩ := hCp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card C := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcY : orderOf (c : Y) = p := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hcp : (c : Y) ^ p = 1 := by
    have := pow_orderOf_eq_one (c : Y)
    rwa [hcY] at this
  have hcx : (c : Y) ∈ zpowers x :=
    case2ab_core_mem_zpowers_of_pow_eq_one h (c : Y) (hCD c.2) hcp
  have hle : zpowers (c : Y) ≤ zpowers x := Subgroup.zpowers_le.mpr hcx
  have hcard' : Nat.card (zpowers x) ≤ Nat.card (zpowers (c : Y)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hcY, h.pdata.x_ord]
  have heq : zpowers (c : Y) = zpowers x := Subgroup.eq_of_le_of_card_ge hle hcard'
  have hxc : x ∈ zpowers (c : Y) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr c.2) hxc

theorem case2ab_core_comm_T_zpowers (h : Case2DataAb p P T D F x) :
    ∀ t ∈ T, ∀ c ∈ zpowers x, t * c = c * t := by
  intro t ht c hc
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact (Commute.zpow_right (show Commute t x from h.pdata.comm t ht x h.pdata.x_mem) j).eq

theorem case2ab_core_conj_component (h : Case2DataAb p P T D F x) {f : Y} (hf : f ∈ F)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hTL : ¬ T ≤ centralizer (L : Set Y)) :
    IsComponentOf (L.map (MulAut.conj f).toMonoidHom) ⊤ ∧
      ¬ T ≤ centralizer ((L.map (MulAut.conj f).toMonoidHom : Subgroup Y) : Set Y) ∧
      ∀ c ∈ centralizer (L : Set Y),
        f * c * f⁻¹ ∈ centralizer ((L.map (MulAut.conj f).toMonoidHom : Subgroup Y) : Set Y) := by
  have hmem : ∀ l ∈ L, f * l * f⁻¹ ∈ L.map (MulAut.conj f).toMonoidHom :=
    fun l hl => ⟨l, hl, by simp [MulAut.conj_apply]⟩
  refine ⟨(CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj f) L).mpr hL, ?_, ?_⟩
  · intro hle
    apply hTL
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hc := Subgroup.mem_centralizer_iff.mp (hle (h.F_T f hf t ht)) (f * l * f⁻¹) (hmem l hl)
    have e1 : f * (l * t) * f⁻¹ = f * (t * l) * f⁻¹ := by
      calc f * (l * t) * f⁻¹ = f * l * f⁻¹ * (f * t * f⁻¹) := by group
        _ = f * t * f⁻¹ * (f * l * f⁻¹) := hc
        _ = f * (t * l) * f⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e1)
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc f * l * f⁻¹ * (f * c * f⁻¹) = f * (l * c) * f⁻¹ := by group
      _ = f * (c * l) * f⁻¹ := by rw [hlc]
      _ = f * c * f⁻¹ * (f * l * f⁻¹) := by group

theorem case2ab_core_le_centralizer (h : Case2DataAb p P T D F x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) {L₀ : Subgroup Y} (hL₀ : IsComponentOf L₀ ⊤) :
    T ≤ centralizer (L₀ : Set Y) := by
  classical
  by_contra hTL₀
  haveI := case2ab_core_fact h
  have h5 := h.five
  let 𝒳 : Set (Subgroup Y) := {L | IsComponentOf L ⊤ ∧ ¬ T ≤ centralizer (L : Set Y)}
  have hfin : 𝒳.Finite := Set.toFinite _
  let X : Finset (Subgroup Y) := hfin.toFinset
  have hmemX : ∀ L, L ∈ X ↔ IsComponentOf L ⊤ ∧ ¬ T ≤ centralizer (L : Set Y) :=
    fun L => hfin.mem_toFinset
  have hXcard : X.card ≤ 3 := by
    have := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_pRank_of_isComponentOf h.prime
      (by omega) h.core X (fun K hK => ((hmemX K).mp hK).1)
    exact this.trans h.rank
  have hline : ∀ L ∈ X, Nat.card ↥(T ⊓ centralizer (L : Set Y)) = p := fun L hL => by
    obtain ⟨hLc, hTL⟩ := (hmemX L).mp hL
    exact (case2ab_centralizer_cases h hInn hWC hLc).resolve_right hTL
  have hL₀X : L₀ ∈ X := (hmemX L₀).mpr ⟨hL₀, hTL₀⟩
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a₀ ∈ T ⊓ centralizer (L₀ : Set Y), a₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : T ⊓ centralizer (L₀ : Set Y) = ⊥ :=
      eq_bot_iff.mpr (fun a ha => Subgroup.mem_bot.mpr (hne a ha))
    have h1 := hline L₀ hL₀X
    rw [hbot, Subgroup.card_bot] at h1
    have := h.prime.one_lt
    omega
  have hcover : ∀ a ∈ T, a ≠ 1 → ∃ L ∈ X, a ∈ T ⊓ centralizer (L : Set Y) := by
    intro a ha ha1
    obtain ⟨f, hf, hfa⟩ := h.F_trans a₀ (Subgroup.mem_inf.mp ha₀).1 ha₀1 a ha ha1
    obtain ⟨hc, hTc, hcen⟩ := case2ab_core_conj_component h hf hL₀ hTL₀
    refine ⟨L₀.map (MulAut.conj f).toMonoidHom, (hmemX _).mpr ⟨hc, hTc⟩,
      Subgroup.mem_inf.mpr ⟨ha, ?_⟩⟩
    rw [← hfa]
    exact hcen a₀ (Subgroup.mem_inf.mp ha₀).2
  let A : Subgroup Y → Set Y := fun L => ((T ⊓ centralizer (L : Set Y) : Subgroup Y) : Set Y) \ {1}
  have hsub : (T : Set Y) \ {1} ⊆ ⋃ L ∈ X, A L := by
    intro a ha
    obtain ⟨L, hLX, haL⟩ := hcover a ha.1 ha.2
    exact Set.mem_biUnion hLX ⟨haL, ha.2⟩
  have hTcard : ((T : Set Y) \ {1}).ncard = p ^ 2 - 1 := by
    rw [Set.ncard_diff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) h.pdata.T_card
  have hAcard : ∀ L ∈ X, (A L).ncard = p - 1 := by
    intro L hL
    show (((T ⊓ centralizer (L : Set Y) : Subgroup Y) : Set Y) \ {1}).ncard = p - 1
    rw [Set.ncard_diff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hline L hL)
  have hle : p ^ 2 - 1 ≤ 3 * (p - 1) := by
    calc p ^ 2 - 1 = ((T : Set Y) \ {1}).ncard := hTcard.symm
      _ ≤ (⋃ L ∈ X, A L).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ∑ L ∈ X, (A L).ncard := Finset.set_ncard_biUnion_le X A
      _ = ∑ L ∈ X, (p - 1) := Finset.sum_congr rfl hAcard
      _ = X.card * (p - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 3 * (p - 1) := Nat.mul_le_mul_right _ hXcard
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
  have e : (q + 5) ^ 2 = q * q + 10 * q + 25 := by ring
  rw [e] at hle
  omega

theorem case2ab_core_le_pCore (h : Case2DataAb p P T D F x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) : T ≤ CFSG.pCore p Y := by
  haveI := case2ab_core_fact h
  have hT : ∀ L : Subgroup Y, IsComponentOf L ⊤ → T ≤ centralizer (L : Set Y) :=
    fun L hL => case2ab_core_le_centralizer h hInn hWC hL
  have hTE : T ≤ centralizer (CFSG.layer Y : Set Y) := by
    have hlay : CFSG.layer Y ≤ centralizer (T : Set Y) := by
      rw [CFSG.layer.eq_sSup]
      apply sSup_le
      intro K hK k hk
      rw [mem_centralizer_iff]
      intro t ht
      have h1 : t ∈ centralizer (K : Set Y) := hT K ((CFSG.isComponent_iff_open K).mp hK) ht
      exact (mem_centralizer_iff.mp h1 k hk).symm
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (hlay hz) t ht).symm
  intro t ht
  have h2 : t ∈ centralizer (CFSG.pCore p Y : Set Y) := by
    rw [mem_centralizer_iff]
    intro o ho
    exact case2ab_core_P_comm h o (case2ab_core_pCore_le_P h ho) t (h.pdata.T_le ht)
  exact centralizer_layer_inf_centralizer_pCore_le h.core ⟨hTE ht, h2⟩

theorem case2ab_core_exists_mul_of_mem_sup (A C : Subgroup Y)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) :
    ∀ v ∈ A ⊔ C, ∃ a ∈ A, ∃ c ∈ C, v = a * c := by
  intro v hv
  rw [Subgroup.sup_eq_closure] at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, C.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    obtain ⟨a', ha', c', hc', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', c * c', C.mul_mem hc hc', ?_⟩
    have h1 := hcomm a' ha' c hc
    calc a * c * (a' * c') = a * (c * a') * c' := by group
      _ = a * (a' * c) * c' := by rw [← h1]
      _ = a * a' * (c * c') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
    have h1 := hcomm a ha c hc
    calc (a * c)⁻¹ = (c * a)⁻¹ := by rw [h1]
      _ = a⁻¹ * c⁻¹ := by group

theorem case2ab_core_V_exp (h : Case2DataAb p P T D F x) : ∀ v ∈ T ⊔ zpowers x, v ^ p = 1 := by
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.pdata.x_ord] at this
  intro v hv
  obtain ⟨t, ht, c, hc, rfl⟩ := case2ab_core_exists_mul_of_mem_sup T (zpowers x)
    (case2ab_core_comm_T_zpowers h) v hv
  rw [Commute.mul_pow (case2ab_core_comm_T_zpowers h t ht c hc), h.pdata.T_exp t ht]
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rw [one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

theorem case2ab_core_V_le_P (h : Case2DataAb p P T D F x) : T ⊔ zpowers x ≤ P :=
  sup_le h.pdata.T_le ((Subgroup.zpowers_le).2 (h.pdata.D_le h.pdata.x_mem))

theorem case2ab_core_V_normal (h : Case2DataAb p P T D F x) (hT : T ≤ CFSG.pCore p Y)
    (hx : x ∈ CFSG.pCore p Y) :
    ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x := by
  haveI := case2ab_core_fact h
  have key : ∀ v : Y, v ∈ T ⊔ zpowers x ↔ v ∈ CFSG.pCore p Y ∧ v ^ p = 1 := by
    intro v
    constructor
    · intro hv
      exact ⟨(sup_le hT ((Subgroup.zpowers_le).2 hx)) hv, case2ab_core_V_exp h v hv⟩
    · rintro ⟨hvO, hvp⟩
      obtain ⟨t, ht, d, hd, rfl⟩ :=
        case2ab_core_exists_mul h v (case2ab_core_pCore_le_P h hvO)
      rw [Commute.mul_pow (h.pdata.comm t ht d hd), h.pdata.T_exp t ht, one_mul] at hvp
      exact Subgroup.mul_mem_sup ht (case2ab_core_mem_zpowers_of_pow_eq_one h d hd hvp)
  intro y v hv
  rw [key] at hv ⊢
  obtain ⟨hvO, hvp⟩ := hv
  refine ⟨(CFSG.pCore_normal (p := p) (G := Y)).conj_mem v hvO y, ?_⟩
  rw [conj_pow, hvp]
  simp

theorem case2ab_core_zpowers_normal (h : Case2DataAb p P T D F x)
    (hV : ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x) :
    ∀ y : Y, ∀ v ∈ zpowers x, y * v * y⁻¹ ∈ zpowers x := by
  intro y v hv
  have hle : (zpowers x).map (MulAut.conj y).toMonoidHom ≤ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact case2ab_core_V_le_P h (hV y w (Subgroup.mem_sup_right hw))
  have heq := h.wc y hle
  have hmem : y * v * y⁻¹ ∈ (zpowers x).map (MulAut.conj y).toMonoidHom :=
    ⟨v, hv, by simp [MulAut.conj_apply]⟩
  rwa [heq] at hmem

theorem case2ab_core_eq_of_complement (h : Case2DataAb p P T D F x) {T' : Subgroup Y}
    (hT'V : T' ≤ T ⊔ zpowers x) (hT'Λ : T' ⊓ zpowers x = ⊥)
    (hT'Λ' : T' ⊔ zpowers x = T ⊔ zpowers x) (hF : ∀ f ∈ F, ∀ a ∈ T', f * a * f⁻¹ ∈ T') :
    T' = T := by
  haveI := case2ab_core_fact h
  have hcommV : ∀ v ∈ T ⊔ zpowers x, ∀ c ∈ zpowers x, v * c = c * v := by
    intro v hv c hc
    obtain ⟨t, ht, c', hc', rfl⟩ := case2ab_core_exists_mul_of_mem_sup T (zpowers x)
      (case2ab_core_comm_T_zpowers h) v hv
    have h2 : c' * c = c * c' := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact (Commute.zpow_zpow_self x j i).eq
    calc t * c' * c = t * (c' * c) := mul_assoc _ _ _
      _ = t * (c * c') := by rw [h2]
      _ = (t * c) * c' := (mul_assoc _ _ _).symm
      _ = (c * t) * c' := by rw [case2ab_core_comm_T_zpowers h t ht c hc]
      _ = c * (t * c') := mul_assoc _ _ _
  have hBinv : ∀ f ∈ F, ∀ a ∈ T ⊓ T', f * a * f⁻¹ ∈ T ⊓ T' :=
    fun f hf a ha => ⟨h.F_T f hf a ha.1, hF f hf a ha.2⟩
  have hB : T ⊓ T' = ⊥ ∨ T ⊓ T' = T := by
    by_cases hbot : T ⊓ T' = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨b, hb, hb1⟩ : ∃ b ∈ T ⊓ T', b ≠ 1 := by
        by_contra hne
        push Not at hne
        exact hbot (eq_bot_iff.mpr (fun a ha => Subgroup.mem_bot.mpr (hne a ha)))
      refine le_antisymm inf_le_left (fun a ha => ?_)
      by_cases ha1 : a = 1
      · rw [ha1]
        exact (T ⊓ T').one_mem
      · obtain ⟨f, hf, hfb⟩ := h.F_trans b hb.1 hb1 a ha ha1
        rw [← hfb]
        exact hBinv f hf b hb
  rcases hB with hB | hB
  ·
    exfalso
    have hX_card : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, h.pdata.x_ord]
    have hXV : ∀ c ∈ zpowers x, c ∈ T ⊔ zpowers x := fun c hc => Subgroup.mem_sup_right hc
    have h1 : T'.relIndex (T ⊔ zpowers x) ≤ p := by
      rw [← hX_card]
      let φ : zpowers x → (↥(T ⊔ zpowers x)) ⧸ T'.subgroupOf (T ⊔ zpowers x) :=
        fun c => QuotientGroup.mk ⟨c.1, hXV c.1 c.2⟩
      have hφ : Function.Surjective φ := by
        intro q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        have hv : (v : Y) ∈ T' ⊔ zpowers x := by rw [hT'Λ']; exact v.2
        obtain ⟨a, ha, c, hc, hvac⟩ := case2ab_core_exists_mul_of_mem_sup T' (zpowers x)
          (fun a ha c hc => hcommV a (hT'V ha) c hc) v hv
        refine ⟨⟨c, hc⟩, ?_⟩
        show (QuotientGroup.mk ⟨c, hXV c hc⟩ : (↥(T ⊔ zpowers x)) ⧸ T'.subgroupOf (T ⊔ zpowers x))
          = QuotientGroup.mk v
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hac : a * c = c * a := hcommV a (hT'V ha) c hc
        have hmem : c⁻¹ * (v : Y) ∈ T' := by
          rw [hvac, hac, inv_mul_cancel_left]
          exact ha
        exact hmem
      exact Nat.card_le_card_of_surjective φ hφ
    have hne : T'.relIndex (T ⊔ zpowers x) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card ..) Nat.card_pos).ne'
    have h2 : T'.relIndex T ≤ T'.relIndex (T ⊔ zpowers x) :=
      Subgroup.relIndex_le_of_le_right le_sup_left hne
    have h3 : T'.relIndex T * Nat.card (T' ⊓ T : Subgroup Y) = Nat.card T :=
      Subgroup.relIndex_mul_card T' T
    rw [inf_comm, hB, Subgroup.card_bot, h.pdata.T_card, mul_one] at h3
    have h5 : p ^ 2 ≤ p := h3 ▸ h2.trans h1
    nlinarith [h.five]
  ·
    have hTT' : T ≤ T' := inf_eq_left.1 hB
    refine le_antisymm ?_ hTT'
    intro a ha
    obtain ⟨t, ht, c, hc, rfl⟩ := case2ab_core_exists_mul_of_mem_sup T (zpowers x)
      (case2ab_core_comm_T_zpowers h) a (hT'V ha)
    have hc' : c ∈ T' := by
      have := T'.mul_mem (T'.inv_mem (hTT' ht)) ha
      simpa using this
    have hc1 : c ∈ T' ⊓ zpowers x := ⟨hc', hc⟩
    rw [hT'Λ, Subgroup.mem_bot] at hc1
    rw [hc1, mul_one]
    exact ht

theorem case2ab_core_comm_mem_bot {a b : Y} (hab : a * b = b * a) :
    a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup Y) := by
  rw [Subgroup.mem_bot, hab]
  group

theorem case2ab_core_normal_of_le_pCore (h : Case2DataAb p P T D F x) (hT : T ≤ CFSG.pCore p Y) :
    ∀ y : Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
  haveI := case2ab_core_fact h
  by_cases hx : x ∈ CFSG.pCore p Y
  ·
    obtain ⟨S, hS⟩ := h.sylow
    have hV := case2ab_core_V_normal h hT hx
    have hΛ := case2ab_core_zpowers_normal h hV
    haveI hVn : (T ⊔ zpowers x).Normal := ⟨fun v hv y => hV y v hv⟩
    haveI hΛn : (zpowers x).Normal := ⟨fun v hv y => hΛ y v hv⟩
    obtain ⟨T', hT'n, -, hT'V, hT'Λ, hT'sup⟩ :=
      exists_normal_complement h.prime S (T ⊔ zpowers x) (zpowers x) ⊥ hVn hΛn inferInstance
        le_sup_right bot_le
        (fun a ha b hb => case2ab_core_comm_mem_bot
          (case2ab_core_P_comm h a (case2ab_core_V_le_P h ha) b (case2ab_core_V_le_P h hb)))
        (case2ab_core_V_exp h)
        (fun s hs v hv => case2ab_core_comm_mem_bot
          (case2ab_core_P_comm h s (hS ▸ hs) v (case2ab_core_V_le_P h hv)))
        (by rw [Nat.card_zpowers, h.pdata.x_ord])
        (inf_bot_eq _)
    have hTT' : T' = T :=
      case2ab_core_eq_of_complement h hT'V hT'Λ hT'sup (fun f _ a ha => hT'n.conj_mem a ha f)
    rw [← hTT']
    intro y t ht
    exact hT'n.conj_mem t ht y
  ·
    have hbot : CFSG.pCore p Y ⊓ D = ⊥ := by
      by_contra hne
      exact hx (case2ab_core_x_mem_of_ne_bot h (CFSG.pCore p Y ⊓ D) inf_le_right hne).1
    have hOT : CFSG.pCore p Y ≤ T := by
      intro o ho
      obtain ⟨t, ht, d, hd, rfl⟩ := case2ab_core_exists_mul h o (case2ab_core_pCore_le_P h ho)
      have hd' : d ∈ CFSG.pCore p Y := by
        have := (CFSG.pCore p Y).mul_mem ((CFSG.pCore p Y).inv_mem (hT ht)) ho
        simpa using this
      have hd1 : d ∈ CFSG.pCore p Y ⊓ D := ⟨hd', hd⟩
      rw [hbot, Subgroup.mem_bot] at hd1
      rw [hd1, mul_one]
      exact ht
    intro y t ht
    exact hOT ((CFSG.pCore_normal (p := p) (G := Y)).conj_mem t (hT ht) y)

theorem case2_core_ab (h : Case2DataAb p P T D F x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) : ∀ y : Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T :=
  case2ab_core_normal_of_le_pCore h (case2ab_core_le_pCore h hInn hWC)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
