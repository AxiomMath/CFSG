module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2AS
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.KFactDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

private theorem false_isElemAbelian_zpowers {p : ℕ} {X : Type} [Group X] {g : X}
    (hg : g ^ p = 1) : IsElemAbelian p (zpowers g) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem false_x_mem_P (h : Case2Data p P T D F x) : x ∈ P := h.pdata.D_le h.pdata.x_mem

private theorem false_x_pow_p (h : Case2Data p P T D F x) : x ^ p = 1 := by
  rw [← h.pdata.x_ord]
  exact pow_orderOf_eq_one x

private theorem false_D_comm (h : Case2Data p P T D F x) {d d' : Y} (hd : d ∈ D) (hd' : d' ∈ D) :
    d * d' = d' * d := by
  haveI := h.pdata.D_cyc
  exact congrArg Subtype.val (mul_comm' (⟨d, hd⟩ : D) ⟨d', hd'⟩)

private theorem false_P_commutator_mem (h : Case2Data p P T D F x) {a b : Y} (ha : a ∈ P) (hb : b ∈ P) :
    a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul a ha
  obtain ⟨t', ht', d', hd', rfl⟩ := h.exists_mul b hb
  have h1 : Commute d t' := (h.pdata.comm t' ht' d hd).symm
  have h2 : Commute d' t := (h.pdata.comm t ht d' hd').symm
  have h3 : d * d' = d' * d := h.false_D_comm hd hd'
  have e1 : t * d * (t' * d') = t * t' * (d * d') := h1.mul_mul_mul_comm t d'
  have e2 : t' * d' * (t * d) = t' * t * (d' * d) := h2.mul_mul_mul_comm t' d
  have hc := h.commutator_mem t ht t' ht'
  have e3 : t * d * (t' * d') = (t * t' * t⁻¹ * t'⁻¹) * (t' * d' * (t * d)) := by
    rw [e1, e2, ← h3]; group
  have e4 : t * d * (t' * d') * (t * d)⁻¹ * (t' * d')⁻¹ = t * t' * t⁻¹ * t'⁻¹ := by
    rw [e3]; group
  rw [e4]; exact hc

private theorem false_exists_not_mem_zOf (h : Case2Data p P T D F x) : ∃ t ∈ T, t ∉ zOf T := by
  by_contra hcon
  push_neg at hcon
  refine h.pdata.T_nonab (isMulCommutative_iff.2 fun a b => ?_)
  have hz : (a : Y) ∈ T ⊓ centralizer (T : Set Y) := hcon a a.2
  exact Subtype.ext (mem_centralizer_iff.1 hz.2 b b.2).symm

private theorem false_x_not_mem_zOf (h : Case2Data p P T D F x) : x ∉ zOf T := by
  intro hxz
  have hx1 : x ∈ T ⊓ zpowers x := ⟨h.zOf_le hxz, Subgroup.mem_zpowers x⟩
  rw [h.T_inf_zpowers] at hx1
  exact h.x_ne_one (Subgroup.mem_bot.1 hx1)

private theorem false_exists_psi (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (K : Subgroup X) (Q : Sylow p X) (ψ : ↥P →* X),
      K.Normal ∧ IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      centralizer (K : Set X) = ⊥ ∧ p ∣ Nat.card K ∧ K ⊔ (Q : Subgroup X) = ⊤ ∧
      (∀ a : ↥P, ψ a = 1 ↔ (a : Y) ∈ centralizer (L : Set Y)) ∧
      ψ.range = (Q : Subgroup X) ∧
      ∀ g : X, (zpowers (ψ ⟨x, h.false_x_mem_P⟩)).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) →
        (zpowers (ψ ⟨x, h.false_x_mem_P⟩)).map (MulAut.conj g).toMonoidHom = zpowers (ψ ⟨x, h.false_x_mem_P⟩) := by
  haveI := h.fact
  obtain ⟨X, hG, hF, π, K, Q, hπ⟩ :=
    exists_almostSimple h.core h.catalog hL h.sylow (h.P_le_normalizer hL)
  have hPL : P ≤ L ⊔ P := le_sup_right
  have hzp : ((zpowers x).subgroupOf (L ⊔ P)).map π
      = zpowers ((π.comp (Subgroup.inclusion hPL)) ⟨x, h.false_x_mem_P⟩) := by
    ext q
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, ⟨k, hk⟩, rfl⟩
      refine ⟨k, ?_⟩
      have : (Subgroup.inclusion hPL ⟨x, h.false_x_mem_P⟩) ^ k = n := by
        apply Subtype.ext
        simpa using hk
      simp only [MonoidHom.comp_apply]
      rw [← map_zpow, this]
    · rintro ⟨k, rfl⟩
      refine ⟨(Subgroup.inclusion hPL ⟨x, h.false_x_mem_P⟩) ^ k, ⟨k, by simp⟩, ?_⟩
      simp
  refine ⟨X, hG, hF, K, Q, π.comp (Subgroup.inclusion hPL), hπ.normal, hπ.simple, hπ.nonab, hπ.catalog,
    hπ.cent, hπ.dvd, hπ.sup, ?_, ?_, ?_⟩
  · intro a
    exact hπ.ker_iff (Subgroup.inclusion hPL a)
  · ext q
    rw [hπ.Q_eq]
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hPL a, a.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  · intro g
    have := hπ.weakClosed_transfer (A := zpowers x) (by simpa using h.false_x_mem_P) h.wc g
    rw [hzp] at this
    exact this

theorem false_of_abelian (h : Case2Data p P T D F x) (hK : KFactWeakClosureRank2)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hC : P ⊓ centralizer (L : Set Y) = zOf T) : False := by
  haveI := h.fact
  obtain ⟨X, _, _, K, Q, ψ, hKn, hKs, hKnab, hKcat, hKc, hKdvd, hKsup, hker, hrange, hwc⟩ :=
    h.false_exists_psi hL
  have hker' : ∀ a : ↥P, ψ a = 1 ↔ (a : Y) ∈ zOf T := by
    intro a
    rw [hker a, ← hC, Subgroup.mem_inf]
    exact ⟨fun hc => ⟨a.2, hc⟩, fun hc => hc.2⟩
  set x' : ↥P := ⟨x, h.false_x_mem_P⟩
  have hψx : ψ x' ≠ 1 := fun h1 => h.false_x_not_mem_zOf ((hker' x').1 h1)
  have hψxp : (ψ x') ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using h.false_x_pow_p)
    rw [this, map_one]
  have hAord : orderOf (ψ x') = p := orderOf_eq_prime hψxp hψx
  have hQab : IsMulCommutative (Q : Subgroup X) := by
    rw [← hrange]
    refine isMulCommutative_iff.2 fun u v => ?_
    obtain ⟨a, ha⟩ := u.2
    obtain ⟨b, hb⟩ := v.2
    apply Subtype.ext
    show (u : X) * v = v * u
    rw [← ha, ← hb]
    have h1 : ψ (a * b * a⁻¹ * b⁻¹) = 1 := (hker' _).2 (h.false_P_commutator_mem a.2 b.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hQrank : 2 ≤ CFSG.Open.pRank p (Q : Subgroup X) := by
    obtain ⟨t, ht, htz⟩ := h.false_exists_not_mem_zOf
    set t' : ↥P := ⟨t, h.pdata.T_le ht⟩
    have hψt : ψ t' ≠ 1 := fun h1 => htz ((hker' t').1 h1)
    have hψtp : (ψ t') ^ p = 1 := by
      rw [← map_pow]
      have : t' ^ p = 1 := Subtype.ext (by simpa using h.pdata.T_exp t ht)
      rw [this, map_one]
    have hcm : Commute (ψ t') (ψ x') := by
      show ψ t' * ψ x' = ψ x' * ψ t'
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (h.pdata.comm t ht x h.pdata.x_mem))
    have hdisj : Disjoint (zpowers (ψ t')) (zpowers (ψ x')) := by
      rw [Subgroup.disjoint_def]
      intro y hy1 hy2
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy2
      have h1 : ψ ((t' ^ i)⁻¹ * x' ^ j) = 1 := by
        rw [map_mul, map_inv, map_zpow, map_zpow, hj, inv_mul_cancel]
      have h2 : (t ^ i)⁻¹ * x ^ j ∈ zOf T := by
        have := (hker' _).1 h1
        simpa using this
      have h3 : x ^ j ∈ T := by
        have := T.mul_mem (T.zpow_mem ht i) (h.zOf_le h2)
        simpa using this
      have h4 : x ^ j ∈ T ⊓ zpowers x := ⟨h3, Subgroup.zpow_mem_zpowers x j⟩
      rw [h.T_inf_zpowers] at h4
      have h5 : x' ^ j = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h4)
      rw [← hj, ← map_zpow, h5, map_one]
    have key := add_le_pRank_of_commute (p := p) (P := (Q : Subgroup X))
      (E₁ := zpowers (ψ t')) (E₂ := zpowers (ψ x')) (r := 1) (s := 1)
      (false_isElemAbelian_zpowers hψtp) (false_isElemAbelian_zpowers hψxp)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime hψtp hψt)
      (by rw [Nat.card_zpowers, pow_one]; exact hAord)
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (hcm.zpow_zpow k l).eq)
      hdisj
      (Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨t', rfl⟩))
      (Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩))
    simpa using key
  have hAQ : zpowers (ψ x') ≤ (Q : Subgroup X) :=
    Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩)
  have hAcard : Nat.card (zpowers (ψ x')) = p := by rw [Nat.card_zpowers]; exact hAord
  obtain ⟨g, hg1, hg2⟩ := hK p h.prime (by have := h.five; omega) X K hKn hKs hKnab hKcat hKc hKdvd Q
    hKsup hQab hQrank (zpowers (ψ x')) hAQ hAcard
  exact hg2 (hwc g hg1)

theorem false_of_faithful (h : Case2Data p P T D F x) (h123 : KFactWeakClosureHeis)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hC : P ⊓ centralizer (L : Set Y) = ⊥) : False := by
  haveI := h.fact
  obtain ⟨X, _, _, K, Q, ψ, hKn, hKs, hKnab, hKcat, hKc, hKdvd, hKsup, hker, hrange, hwc⟩ :=
    h.false_exists_psi hL
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : Y) ∈ P ⊓ centralizer (L : Set Y) := ⟨a.2, (hker a).1 ha⟩
    rw [hC] at h1
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  set x' : ↥P := ⟨x, h.false_x_mem_P⟩
  have hψx : ψ x' ≠ 1 := by
    intro h1
    have := hinj (h1.trans (map_one ψ).symm)
    exact h.x_ne_one (congrArg Subtype.val this)
  have hψxp : (ψ x') ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using h.false_x_pow_p)
    rw [this, map_one]
  have hAord : orderOf (ψ x') = p := orderOf_eq_prime hψxp hψx
  set Q₀ : Subgroup X := (D.subgroupOf P).map ψ with hQ₀
  set Q₁ : Subgroup X := (T.subgroupOf P).map ψ with hQ₁
  have hmem₀ : ∀ {q : X}, q ∈ Q₀ ↔ ∃ a : ↥P, (a : Y) ∈ D ∧ ψ a = q := by
    intro q
    simp only [hQ₀, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hmem₁ : ∀ {q : X}, q ∈ Q₁ ↔ ∃ a : ↥P, (a : Y) ∈ T ∧ ψ a = q := by
    intro q
    simp only [hQ₁, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hcyc : IsCyclic ↥Q₀ := by
    haveI := h.pdata.D_cyc
    haveI : IsCyclic ↥(D.subgroupOf P) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h.pdata.D_le).symm
        (Subgroup.subgroupOfEquivOfLe h.pdata.D_le).symm.surjective
    exact isCyclic_of_surjective (ψ.subgroupMap (D.subgroupOf P))
      (ψ.subgroupMap_surjective (D.subgroupOf P))
  have hQ0ne : Q₀ ≠ ⊥ := by
    intro h0
    have : ψ x' ∈ Q₀ := hmem₀.2 ⟨x', h.pdata.x_mem, rfl⟩
    rw [h0] at this
    exact hψx (Subgroup.mem_bot.1 this)
  have hcard : Nat.card Q₁ = p ^ 3 := by
    rw [hQ₁, Subgroup.card_map_of_injective hinj]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.pdata.T_le).toEquiv]
    exact h.pdata.T_card
  have hnab : ¬ IsMulCommutative Q₁ := by
    intro hab
    refine h.pdata.T_nonab (isMulCommutative_iff.2 fun u v => ?_)
    set a : ↥P := ⟨u, h.pdata.T_le u.2⟩
    set b : ↥P := ⟨v, h.pdata.T_le v.2⟩
    have h1 : ψ a * ψ b = ψ b * ψ a :=
      congrArg Subtype.val (mul_comm' (⟨ψ a, hmem₁.2 ⟨a, u.2, rfl⟩⟩ : ↥Q₁) ⟨ψ b, hmem₁.2 ⟨b, v.2, rfl⟩⟩)
    rw [← map_mul, ← map_mul] at h1
    have h2 : ((a * b : ↥P) : Y) = ((b * a : ↥P) : Y) := congrArg Subtype.val (hinj h1)
    exact Subtype.ext h2
  have hexp : ∀ q ∈ Q₁, q ^ p = 1 := by
    intro q hq
    obtain ⟨a, haT, rfl⟩ := hmem₁.1 hq
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (by simpa using h.pdata.T_exp a haT)
    rw [this, map_one]
  have hcomm : ∀ a ∈ Q₀, ∀ b ∈ Q₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hdD, rfl⟩ := hmem₀.1 ha
    obtain ⟨t, htT, rfl⟩ := hmem₁.1 hb
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (h.pdata.comm t htT d hdD).symm)
  have hdisj : Q₀ ⊓ Q₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨d, hdD, hd⟩ := hmem₀.1 hq.1
    obtain ⟨t, htT, ht⟩ := hmem₁.1 hq.2
    have hdt : d = t := hinj (hd.trans ht.symm)
    have : (d : Y) ∈ T ⊓ D := ⟨hdt ▸ htT, hdD⟩
    rw [h.pdata.inf_eq] at this
    have hd1 : d = 1 := Subtype.ext (Subgroup.mem_bot.1 this)
    rw [← hd, hd1, map_one]
  have hsup : Q₀ ⊔ Q₁ = (Q : Subgroup X) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro q hq
        obtain ⟨a, _, rfl⟩ := hmem₀.1 hq
        rw [← hrange]; exact ⟨a, rfl⟩
      · intro q hq
        obtain ⟨a, _, rfl⟩ := hmem₁.1 hq
        rw [← hrange]; exact ⟨a, rfl⟩
    · intro q hq
      rw [← hrange] at hq
      obtain ⟨a, rfl⟩ := hq
      obtain ⟨t, ht, d, hd, had⟩ := h.exists_mul a a.2
      set t' : ↥P := ⟨t, h.pdata.T_le ht⟩
      set d' : ↥P := ⟨d, h.pdata.D_le hd⟩
      have : a = t' * d' := Subtype.ext had
      rw [this, map_mul, sup_comm]
      exact Subgroup.mul_mem_sup (hmem₁.2 ⟨t', ht, rfl⟩) (hmem₀.2 ⟨d', hd, rfl⟩)
  have hAQ : zpowers (ψ x') ≤ (Q : Subgroup X) :=
    Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩)
  have hAcard : Nat.card (zpowers (ψ x')) = p := by rw [Nat.card_zpowers]; exact hAord
  obtain ⟨g, hg1, hg2⟩ := h123 p h.prime h.five X K hKn hKs hKnab hKcat hKc hKdvd Q hKsup Q₀ Q₁
    hcyc hQ0ne hcard hnab hexp hcomm hdisj hsup (zpowers (ψ x')) hAQ hAcard
  exact hg2 (hwc g hg1)

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
