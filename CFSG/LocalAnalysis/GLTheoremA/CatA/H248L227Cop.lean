module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Cop
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem pGroup_inf_eq_bot_of_coprime {K : Type*} [Group K] {q : ℕ} {R N : Subgroup K}
    (hR : IsPGroup q R) (hN : Nat.Coprime q (Nat.card N)) : R ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hR ⟨x, hx.1⟩
  have h1 : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx.2
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (hN.pow_left k) h1 h2
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)

theorem exists_normalizer_mul {K : Type*} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    {N Q : Subgroup K} [N.Normal] (hN : Nat.Coprime q (Nat.card N)) (hQ : IsPGroup q Q) (x : K)
    (hx : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q ⊔ N) :
    ∃ y ∈ Subgroup.normalizer (Q : Set K), ∃ n ∈ N, x = y * n := by
  have : Fact q.Prime := ⟨hq⟩
  set G' : Subgroup K := Q ⊔ N with hG'
  have hQG' : Q ≤ G' := le_sup_left
  have hNG' : N ≤ G' := le_sup_right
  set R : Subgroup K := Q.map (MulAut.conj x).toMonoidHom with hR
  have hmemR : ∀ w : K, w ∈ R ↔ x⁻¹ * w * x ∈ Q := by
    intro w
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hw
      exact ⟨x⁻¹ * w * x, hw, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hRG' : R ≤ G' := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hx y hy
  have hbot : Q ⊓ N = ⊥ := pGroup_inf_eq_bot_of_coprime hQ hN
  have hNQ : N.subgroupOf Q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h : (y : K) ∈ Q ⊓ N := ⟨y.2, Subgroup.mem_subgroupOf.1 hy⟩
    rw [hbot, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  have hrel : N.relIndex G' = Nat.card Q := by
    rw [hG', Subgroup.relIndex_sup_right, Subgroup.relIndex, hNQ, Subgroup.index_bot]
  have hcardN : Nat.card (N.subgroupOf G') = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG').toEquiv
  have hcardG : Nat.card G' = Nat.card Q * Nat.card N := by
    have h := Subgroup.index_mul_card (N.subgroupOf G')
    rw [hcardN] at h
    rw [← h]
    change N.relIndex G' * Nat.card N = _
    rw [hrel]
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hcardR : Nat.card R = Nat.card Q := Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hNq : ¬ q ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hq).1 hN
  have hidx : ∀ T : Subgroup K, T ≤ G' → Nat.card T = Nat.card Q →
      ¬ q ∣ (T.subgroupOf G').index := by
    intro T hT hTc
    have h := Subgroup.index_mul_card (T.subgroupOf G')
    have hc : Nat.card (T.subgroupOf G') = Nat.card Q :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv).trans hTc
    rw [hc, hcardG] at h
    have : (T.subgroupOf G').index = Nat.card N := by
      have h' : (T.subgroupOf G').index * Nat.card Q = Nat.card N * Nat.card Q := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_right hQpos h'
    rw [this]
    exact hNq
  have hQ₁ : IsPGroup q (Q.subgroupOf G') := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQG').symm
  have hR₁ : IsPGroup q (R.subgroupOf G') :=
    (hQ.map (MulAut.conj x).toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hRG').symm
  let S₁ : Sylow q G' := hQ₁.toSylow (hidx Q hQG' rfl)
  let S₂ : Sylow q G' := hR₁.toSylow (hidx R hRG' hcardR)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G' S₁ S₂
  have hS : ((g • S₁ : Sylow q G') : Subgroup G') = R.subgroupOf G' := by
    rw [hg]; exact IsPGroup.toSylow_coe _ _
  have key : ∀ w : K, w ∈ G' → (w ∈ R ↔ (g : K)⁻¹ * w * g ∈ Q) := by
    intro w hw
    have h := Subgroup.ext_iff.1 hS ⟨w, hw⟩
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      at h
    simp only [S₁, IsPGroup.toSylow_coe, MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply,
      Subgroup.mem_subgroupOf] at h
    exact h.symm
  have hgG : (g : K) ∈ G' := g.2
  set y₀ : K := (g : K)⁻¹ * x with hy₀
  have hy₀N : y₀ ∈ Subgroup.normalizer (Q : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hy : y₀ * h * y₀⁻¹ = (g : K)⁻¹ * (x * h * x⁻¹) * g := by
      simp [hy₀, mul_assoc]
    rw [hy]
    constructor
    · intro hh
      have hw : x * h * x⁻¹ ∈ G' := hx h hh
      exact (key _ hw).1 ((hmemR _).2 (by simpa [mul_assoc] using hh))
    · intro hh
      have hw : x * h * x⁻¹ ∈ G' := by
        have : (g : K) * ((g : K)⁻¹ * (x * h * x⁻¹) * g) * (g : K)⁻¹ ∈ G' :=
          mul_mem (mul_mem hgG (hQG' hh)) (inv_mem hgG)
        simpa [mul_assoc] using this
      have h2 := (key _ hw).2 hh
      have h3 := (hmemR _).1 h2
      simpa [mul_assoc] using h3
  obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.1 hgG
  refine ⟨a * y₀, mul_mem (Subgroup.le_normalizer ha) hy₀N, y₀⁻¹ * n * y₀, ?_, ?_⟩
  · simpa using (inferInstance : N.Normal).conj_mem n hn y₀⁻¹
  · have hg' : (g : K) = a * n := han.symm
    calc x = (g : K) * y₀ := by simp [hy₀]
      _ = a * y₀ * (y₀⁻¹ * n * y₀) := by rw [hg']; group

theorem normal_le_coreIn {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime) (N : Subgroup K)
    [N.Normal] (hN : Nat.Coprime q (Nat.card N)) (P : Subgroup K)
    (hrk : 4 ≤ CFSG.Open.pRank q P) : N ≤ coreIn q 3 P ⊤ := by
  classical
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq1 P
  set r := CFSG.Open.pRank q P with hr
  have : Fact q.Prime := ⟨hq⟩
  have hEA : CFSG.IsElementaryAbelian q E :=
    { hE.1 with
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hE.2 (a : K) a.2) }
  have hnt : Nontrivial E := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hq1
  have hNq : ¬ q ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hq).1 hN
  let : MulDistribMulAction E N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp E.subtype)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := q) (A := E) (H := N) hNq
  have hle : ∀ B : Subgroup E, B.index = q →
      (CFSG.fixedPointSubgroup B N).map N.subtype ≤ coreIn q 3 P ⊤ := by
    intro B hB
    set Q : Subgroup K := B.map E.subtype with hQ
    have hQE : Q ≤ E := Subgroup.map_subtype_le B
    have hQP : Q ≤ P := hQE.trans hEP
    have hcardQ : Nat.card Q = q ^ (r - 1) := by
      have h1 : Nat.card B * q = q ^ r := by
        rw [← hcard, ← hB]; exact Subgroup.card_mul_index B
      have h2 : q ^ r = q ^ (r - 1) * q := by
        rw [← pow_succ]; congr 1; omega
      have h3' : Nat.card B = q ^ (r - 1) := by
        rw [h2] at h1; exact Nat.eq_of_mul_eq_mul_right hq.pos h1
      rw [hQ, Subgroup.card_map_of_injective E.subtype_injective]
      exact h3'
    have hQab : CFSG.Open.IsElemAbelian q Q := CFSG.Open.IsElemAbelian.mono hE hQE
    have hrQ : 3 ≤ CFSG.Open.pRank q Q := by
      have := CFSG.SectionRank.le_pRank hq1 le_rfl hQab hcardQ
      omega
    rintro _ ⟨n, hn, rfl⟩
    unfold coreIn
    refine Subgroup.mem_iSup_of_mem Q (Subgroup.mem_iSup_of_mem ⟨hQP, hrQ⟩ ?_)
    have hc : N.subtype n ∈ Subgroup.centralizer (Q : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h : (b : K) * n * (b : K)⁻¹ = n := congrArg Subtype.val (hn ⟨b, hb⟩)
      change (b : K) * n = n * (b : K)
      calc (b : K) * n = (b : K) * n * (b : K)⁻¹ * b := by group
        _ = n * b := by rw [h]
    exact ⟨Subgroup.mem_top _, Subgroup.centralizer_le_normalizer (Q : Set K) hc⟩
  have hmap : (⊤ : Subgroup N).map N.subtype ≤ coreIn q 3 P ⊤ := by
    have h : (⨆ (B : Subgroup E) (_ : B.index = q), CFSG.fixedPointSubgroup B N).map N.subtype
        ≤ coreIn q 3 P ⊤ := by
      simp only [Subgroup.map_iSup]
      exact iSup₂_le fun B hB => hle B hB
    rwa [hgen] at h
  intro x hx
  exact hmap ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem coreIn_eq_top_of_quotient {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (N : Subgroup K) [N.Normal] (hN : Nat.Coprime q (Nat.card N)) (P : Subgroup K)
    (hP : IsPGroup q P) (hrk : 4 ≤ CFSG.Open.pRank q P)
    (hquot : coreIn q 3 (P.map (QuotientGroup.mk' N)) ⊤ = ⊤) : coreIn q 3 P ⊤ = ⊤ := by
  have hq1 : 1 < q := hq.one_lt
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hPN : P ⊓ N = ⊥ := pGroup_inf_eq_bot_of_coprime hP hN
  have hinjP : ∀ {T : Subgroup K}, T ≤ P → ∀ x ∈ T, π x = 1 → x = 1 := by
    intro T hT x hx h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h1
    have : x ∈ P ⊓ N := ⟨hT hx, hxN⟩
    rwa [hPN, Subgroup.mem_bot] at this
  have hNH : N ≤ coreIn q 3 P ⊤ := normal_le_coreIn hq N hN P hrk
  have hH : coreIn q 3 (P.map π) ⊤ ≤ (coreIn q 3 P ⊤).map π := by
    refine iSup₂_le fun Qb hQb => ?_
    obtain ⟨hQP, hr1⟩ := hQb
    set Q : Subgroup K := P ⊓ Qb.comap π with hQ
    have hQP' : Q ≤ P := inf_le_left
    have hQmap : Q.map π = Qb := by
      ext y
      constructor
      · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
        exact hx2
      · intro hy
        obtain ⟨x, hxP, rfl⟩ := hQP hy
        exact ⟨x, ⟨hxP, hy⟩, rfl⟩
    have hr1' : 3 ≤ CFSG.Open.pRank q Q := by
      have := i227cop_pRank_map_le π (hinjP hQP') hq1
      rw [hQmap] at this
      omega
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hxn : ∀ h : K ⧸ N, h ∈ Qb ↔ (x : K ⧸ N) * h * (x : K ⧸ N)⁻¹ ∈ Qb :=
      Subgroup.mem_normalizer_iff.1 hxb.2
    have hx' : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q ⊔ N := by
      intro y hy
      have hqb : π y ∈ Qb := hQmap ▸ Subgroup.mem_map_of_mem π hy
      have h1 : π (x * y * x⁻¹) ∈ Qb := by
        have := (hxn (π y)).1 hqb
        simpa [hπ] using this
      rw [← hQmap] at h1
      obtain ⟨a, ha, haa⟩ := h1
      have h2 : a⁻¹ * (x * y * x⁻¹) ∈ N := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change π (a⁻¹ * (x * y * x⁻¹)) = 1
        rw [map_mul, map_inv, haa, inv_mul_cancel]
      have h3 : x * y * x⁻¹ = a * (a⁻¹ * (x * y * x⁻¹)) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup ha h2
    obtain ⟨y, hy, n, hn, rfl⟩ := exists_normalizer_mul hq hN (hP.to_le hQP') x hx'
    have hyH : y ∈ coreIn q 3 P ⊤ := by
      unfold coreIn
      exact Subgroup.mem_iSup_of_mem Q
        (Subgroup.mem_iSup_of_mem ⟨hQP', hr1'⟩ ⟨Subgroup.mem_top _, hy⟩)
    refine ⟨y, hyH, ?_⟩
    have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show π y = π (y * n)
    rw [map_mul, hn1, mul_one]
  rw [eq_top_iff]
  intro k _
  have h1 : π k ∈ coreIn q 3 (P.map π) ⊤ := by rw [hquot]; exact Subgroup.mem_top _
  obtain ⟨h, hh, hhk⟩ := hH h1
  have h2 : h⁻¹ * k ∈ N := QuotientGroup.eq.1 hhk
  have h4 : k = h * (h⁻¹ * k) := by group
  rw [h4]
  exact mul_mem hh (hNH h2)

end CFSG.LocalAnalysis.GLTheoremA.H248L227
