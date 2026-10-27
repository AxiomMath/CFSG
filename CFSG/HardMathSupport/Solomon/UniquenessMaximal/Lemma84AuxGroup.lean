module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

open scoped Pointwise

private theorem card_eq_of_sylow_crit {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup q P)
    (hsyl : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P) :
    Nat.card (P.subgroupOf H) = q ^ (Nat.card H).factorization q := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv]
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : q ^ (Nat.card H).factorization q ∣ Nat.card P := hsyl _ (Nat.ordProj_dvd _ _)
  have h2 : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
  rw [hk] at h1 h2 ⊢
  have hle1 : k ≤ (Nat.card H).factorization q :=
    (Fact.out : q.Prime).pow_dvd_iff_le_factorization hH |>.1 h2
  have hle2 : (Nat.card H).factorization q ≤ k :=
    (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).1 h1
  rw [le_antisymm hle1 hle2]


private noncomputable def sylowOfCrit {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup q P)
    (hsyl : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P) : Sylow q H :=
  Sylow.ofCard (P.subgroupOf H) (card_eq_of_sylow_crit hPH hP hsyl)

private theorem sylow_conj_aux {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H P1 P2 : Subgroup G} (h1 : P1 ≤ H) (hp1 : IsPGroup q P1)
    (hs1 : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P1)
    (h2 : P2 ≤ H) (hp2 : IsPGroup q P2)
    (hs2 : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P2) :
    ∃ d ∈ H, ∀ x, x ∈ P2 ↔ d⁻¹ * x * d ∈ P1 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (sylowOfCrit h1 hp1 hs1) (sylowOfCrit h2 hp2 hs2)
  refine ⟨g, g.2, fun x => ?_⟩
  have := congrArg (fun S : Sylow q H => (S : Subgroup H)) hg
  simp only [Sylow.coe_subgroup_smul] at this
  have hx : ∀ y : H, y ∈ P2.subgroupOf H ↔ g⁻¹ * y * g ∈ P1.subgroupOf H := by
    intro y
    change y ∈ (sylowOfCrit h2 hp2 hs2 : Subgroup H) ↔ _
    rw [← this, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  constructor
  · intro hx2
    have hxH : x ∈ H := h2 hx2
    have := (hx ⟨x, hxH⟩).1 hx2
    exact this
  · intro hx1
    have hxH : g⁻¹ * x * g ∈ H := h1 hx1
    have hxH' : x ∈ H := by
      have := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    exact (hx ⟨x, hxH'⟩).2 hx1

private theorem exists_mul_of_mem_sup {G : Type*} [Group G] {T O : Subgroup G}
    (hn : T ≤ Subgroup.normalizer (O : Set G)) {d : G} (hd : d ∈ T ⊔ O) :
    ∃ t ∈ T, ∃ o ∈ O, d = t * o := by
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  have hd' : (⟨d, hd⟩ : ↥(T ⊔ O)) ∈ T.subgroupOf (T ⊔ O) ⊔ O.subgroupOf (T ⊔ O) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hd'
  exact ⟨y, hy, z, hz, by simpa using (congrArg Subtype.val hyz).symm⟩

private theorem exists_conj_le {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H P Q : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup q P)
    (hsyl : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P)
    (hQH : Q ≤ H) (hQ : IsPGroup q Q) : ∃ d ∈ H, ∀ x ∈ Q, d⁻¹ * x * d ∈ P := by
  have hQ' : IsPGroup q (Q.subgroupOf H) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (sylowOfCrit hPH hP hsyl) R
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxH : x ∈ H := hQH hx
  have h1 : (⟨x, hxH⟩ : H) ∈ (R : Subgroup H) := hR (by simpa [Subgroup.mem_subgroupOf] using hx)
  rw [← hg] at h1
  have h2 := h1
  change (⟨x, hxH⟩ : H) ∈ (g • sylowOfCrit hPH hP hsyl : Sylow q H).toSubgroup at h2
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  exact h2


theorem sylow_sup_of_coprime {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {T O : Subgroup G} (hT : IsPGroup q T) (hn : T ≤ Subgroup.normalizer (O : Set G))
    (hO : ¬ q ∣ Nat.card O) :
    ∀ n : ℕ, q ^ n ∣ Nat.card ↥(T ⊔ O) → q ^ n ∣ Nat.card T := by
  have _ := hT
  intro n hnD
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  set D := T ⊔ O
  set O' := O.subgroupOf D
  let f : T →* ↥D ⧸ O' :=
    (QuotientGroup.mk' O').comp (Subgroup.inclusion (le_sup_left : T ≤ D))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨t, ht, o, ho, hdo⟩ := exists_mul_of_mem_sup hn d.2
    refine ⟨⟨t, ht⟩, ?_⟩
    change (QuotientGroup.mk (⟨t, _⟩ : ↥D) : ↥D ⧸ O') = QuotientGroup.mk d
    rw [QuotientGroup.eq]
    have : (⟨t, (le_sup_left : T ≤ D) ht⟩ : ↥D)⁻¹ * d = ⟨o, (le_sup_right : O ≤ D) ho⟩ := by
      apply Subtype.ext
      simp [hdo]
    rw [this]
    exact ho
  have h1 : Nat.card (↥D ⧸ O') ∣ Nat.card T := Subgroup.card_dvd_of_surjective hf
  have h2 : Nat.card D = Nat.card (↥D ⧸ O') * Nat.card O' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O']
  have h3 : Nat.card O' = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : O ≤ D)).toEquiv
  rw [h2, h3] at hnD
  have hcop : Nat.Coprime (q ^ n) (Nat.card O) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hO)
  exact (hcop.dvd_of_dvd_mul_right hnD).trans h1 |>.trans (dvd_refl _)

theorem exists_mem_normalizer_of_sylow {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {T O : Subgroup G} (hT : IsPGroup q T) (hn : T ≤ Subgroup.normalizer (O : Set G))
    (hsyl : ∀ n : ℕ, q ^ n ∣ Nat.card ↥(T ⊔ O) → q ^ n ∣ Nat.card T)
    {j : G} (hc : ∀ t ∈ T, j * t * j⁻¹ * t⁻¹ ∈ O) :
    ∃ o ∈ O, o⁻¹ * j ∈ Subgroup.normalizer (T : Set G) := by
  set D := T ⊔ O with hD
  let S : Subgroup G := T.map (MulAut.conj j).toMonoidHom
  have hmemS : ∀ x, x ∈ S ↔ ∃ t ∈ T, j * t * j⁻¹ = x := by
    intro x
    simp [S, Subgroup.mem_map]
  have hSD : S ≤ D := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hmemS x).1 hx
    have h1 : j * t * j⁻¹ = (j * t * j⁻¹ * t⁻¹) * t := by group
    rw [h1]
    exact D.mul_mem ((le_sup_right : O ≤ D) (hc t ht)) ((le_sup_left : T ≤ D) ht)
  have hcard : Nat.card S = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj j).injective
  have hSp : IsPGroup q S := by
    have e := Subgroup.equivMapOfInjective T (MulAut.conj j).toMonoidHom (MulAut.conj j).injective
    exact hT.of_equiv e
  have hSsyl : ∀ n : ℕ, q ^ n ∣ Nat.card D → q ^ n ∣ Nat.card S := by
    intro n hn'
    rw [hcard]; exact hsyl n hn'
  obtain ⟨d, hdD, hd⟩ := sylow_conj_aux (le_sup_left : T ≤ D) hT hsyl hSD hSp hSsyl
  obtain ⟨t, ht, o, ho, hdo⟩ := exists_mul_of_mem_sup hn hdD
  have hmem : ∀ z, z ∈ T ↔ (j⁻¹ * d)⁻¹ * z * (j⁻¹ * d) ∈ T := by
    intro z
    have h1 : j * z * j⁻¹ ∈ S ↔ z ∈ T := by
      rw [hmemS]
      constructor
      · rintro ⟨t', ht', h'⟩
        have : t' = z := by
          have := mul_left_cancel (mul_right_cancel h')
          exact this
        exact this ▸ ht'
      · intro hz; exact ⟨z, hz, rfl⟩
    rw [← h1, hd]
    have : d⁻¹ * (j * z * j⁻¹) * d = (j⁻¹ * d)⁻¹ * z * (j⁻¹ * d) := by group
    rw [this]
  have hN : d⁻¹ * j ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := hmem z
    have e : (d⁻¹ * j) * z * (d⁻¹ * j)⁻¹ = (j⁻¹ * d)⁻¹ * z * (j⁻¹ * d) := by group
    rw [e]; exact this
  have ho'O : t * o * t⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hn ht) o).1 ho
  refine ⟨t * o * t⁻¹, ho'O, ?_⟩
  have hdo' : d = (t * o * t⁻¹) * t := by rw [hdo]; group
  have h2 : t * (d⁻¹ * j) ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hN
  have e : (t * o * t⁻¹)⁻¹ * j = t * (d⁻¹ * j) := by rw [hdo']; group
  rw [e]; exact h2

theorem sylow_inf_of_normal {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H N P : Subgroup G} (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal)
    (hPH : P ≤ H) (hP : IsPGroup q P)
    (hsyl : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P) :
    ∀ n : ℕ, q ^ n ∣ Nat.card N → q ^ n ∣ Nat.card ↥(P ⊓ N) := by
  intro n hn
  obtain ⟨Q⟩ : Nonempty (Sylow q N) := inferInstance
  let Qs : Subgroup G := (Q : Subgroup N).map N.subtype
  have hQs : Qs ≤ N := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hQcard : Nat.card Qs = Nat.card Q :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hQp : IsPGroup q Qs :=
    Q.2.of_equiv (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective)
  obtain ⟨d, hdH, hd⟩ := exists_conj_le hPH hP hsyl (hQs.trans hNH) hQp
  let Qc : Subgroup G := Qs.map (MulAut.conj d⁻¹).toMonoidHom
  have hQc : Qc ≤ P ⊓ N := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have := hd x hx
      simpa [MulAut.conj_apply] using this
    · have hxN : (⟨x, hQs.trans hNH hx⟩ : H) ∈ N.subgroupOf H := hQs hx
      have := hNn.conj_mem _ hxN (⟨d, hdH⟩⁻¹ : H)
      simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using this
  have hcard : Nat.card Qc = Nat.card Qs :=
    Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective
  have h1 : q ^ n ∣ Nat.card Q := Sylow.pow_dvd_card_of_pow_dvd_card Q hn
  have h2 : Nat.card Qc ∣ Nat.card ↥(P ⊓ N) := Subgroup.card_dvd_of_le hQc
  rw [hcard, hQcard] at h2
  exact h1.trans h2

theorem pRank_le_of_sylow {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup q P)
    (hsyl : ∀ n : ℕ, q ^ n ∣ Nat.card H → q ^ n ∣ Nat.card P) :
    CFSG.Open.pRank q H ≤ CFSG.Open.pRank q P := by
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq H
  have hEp : IsPGroup q E := IsPGroup.of_card hcard
  obtain ⟨d, -, hd⟩ := exists_conj_le hPH hP hsyl hEH hEp
  let f : G →* G := (MulAut.conj d⁻¹).toMonoidHom
  have hEP : E.map f ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [f, MulAut.conj_apply] using hd x hx
  refine CFSG.SectionRank.le_pRank hq hEP (CFSG.SectionRank.isElemAbelian_map hE f) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective, hcard]

theorem exists_isTwoLocal_pRank_pos {K : Type*} [Group K] [Finite K] {r : ℕ} (hr : 1 < r)
    (h : 1 ≤ GLATwoLocalRank r K) : ∃ H : Subgroup K, IsTwoLocal H ∧ 1 ≤ CFSG.Open.pRank r H := by
  have hbdd : BddAbove {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank r H = k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank hr H
    have h1 : CFSG.Open.pRank r H < r ^ CFSG.Open.pRank r H := Nat.lt_pow_self hr
    have h2 : Nat.card E ≤ Nat.card K := Subgroup.card_le_card_group E
    rw [hcard] at h2
    omega
  have hne : {k | ∃ H : Subgroup K, IsTwoLocal H ∧ CFSG.Open.pRank r H = k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : GLATwoLocalRank r K = 0 := by
      unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
      rw [hne]; simp
    omega
  obtain ⟨H, hH, hk⟩ := Nat.sSup_mem hne hbdd
  exact ⟨H, hH, by unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank at h; omega⟩

theorem dvd_card_of_one_le_pRank {K : Type*} [Group K] [Finite K] {r : ℕ} (hr : r.Prime)
    {H : Subgroup K} (h : 1 ≤ CFSG.Open.pRank r H) : r ∣ Nat.card H := by
  obtain ⟨E, hEH, -, hcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt H
  have h1 : r ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self r (by omega)
  exact h1.trans (Subgroup.card_dvd_of_le hEH)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
