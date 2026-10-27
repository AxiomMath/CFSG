module

public import CFSG.LieType.SeitzGeneration.HyperPlaneCube
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.RankThree.PartOne.CTP

@[expose] def FixPlaneGen (K : Type*) [Group K] (p : ℕ) : Prop :=
  ∀ σ : MulAut K, IsOuterOfOrder p σ → ∀ A : Subgroup K, A ≤ fixedSubgroup σ →
    IsElemAbelian p A → Nat.card A = p ^ 2 →
      fixedSubgroup σ ≤ Subgroup.closure
        {k | k ∈ fixedSubgroup σ ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}

theorem FixPlaneGen.of_mulEquiv {K P : Type} [Group K] [Group P] (e : K ≃* P) {p : ℕ}
    (hp : p.Prime) (h : FixPlaneGen P p) : FixPlaneGen K p := by
  have : Fact p.Prime := ⟨hp⟩
  intro σ hσ A hA hAa hAc
  have hτ : IsOuterOfOrder p (MulAut.congr e σ) := ⟨(MulEquiv.orderOf_eq (MulAut.congr e) σ).trans
    hσ.1, fun g hg => hσ.2 (e.symm g) (eq_conj_of_congr_eq_conj e hg)⟩
  have hA' : A.map e.toMonoidHom ≤ fixedSubgroup (MulAut.congr e σ) := by
    rw [fixedSubgroup_congr]
    exact Subgroup.map_mono hA
  have hAa' : IsElemAbelian p (A.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa _
  have hAc' : Nat.card (A.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hAc]
  have hgen := h _ hτ _ hA' hAa' hAc'
  intro x hx
  have hex : e x ∈ fixedSubgroup (MulAut.congr e σ) := by
    rw [fixedSubgroup_congr]
    exact ⟨x, hx, rfl⟩
  have h1 := hgen hex
  have hset : {k | k ∈ fixedSubgroup (MulAut.congr e σ) ∧
      ∃ b ∈ A.map e.toMonoidHom, b ≠ 1 ∧ k * b = b * k} ⊆
      e.toMonoidHom '' {k | k ∈ fixedSubgroup σ ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k} := by
    rintro k ⟨hk, b, hb, hb1, hkb⟩
    rw [fixedSubgroup_congr] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨k', ⟨hk', b', hb', fun h1 => hb1 (by rw [h1, map_one]), ?_⟩, rfl⟩
    apply e.injective
    simpa using hkb
  have h2 : e x ∈ (Subgroup.closure
      {k | k ∈ fixedSubgroup σ ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}).map e.toMonoidHom := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hset h1
  obtain ⟨y, hy, hyx⟩ := h2
  rwa [e.injective hyx] at hy

section Cube

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]

omit [Finite Y] in
theorem conjNormal_injective (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgC : g ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hg ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply] at h1
    change g * k * g⁻¹ = k at h1
    calc k * g = g * k * g⁻¹ * g := by rw [h1]
      _ = g * k := by group
  rw [hC, Subgroup.mem_bot] at hgC
  exact hgC

theorem card_inf_eq_of_fieldAutData (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hnoK : ¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (hF : FieldAutData K p) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : Nat.card (E ⊓ K : Subgroup Y) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hEKa : IsElemAbelian p (E ⊓ K : Subgroup Y) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x hx.1⟩
    have h1 := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, a.2.1⟩ : E) ⟨b, b.2.1⟩)
    exact h1
  have hdvd : Nat.card (E ⊓ K : Subgroup Y) ∣ p ^ 3 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rcases (show k ≤ 1 ∨ k = 2 ∨ k = 3 by omega) with hk1 | rfl | rfl
  · exfalso
    obtain ⟨F, hFE, -, hdisj, hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
      hp hE inf_le_left bot_le (inf_bot_eq _)
    have hcF : Nat.card (E ⊓ K : Subgroup Y) * Nat.card F = p ^ 3 := by
      rw [← hEc]
      exact CFSG.SignalizerFunctorTheorem.card_mul_card_complement hE inf_le_left hFE hdisj hsup
    have hFa : IsElemAbelian p F := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
      have h1 := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, hFE a.2⟩ : E) ⟨b, hFE b.2⟩)
      exact h1
    have hFK : F ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ (E ⊓ K) ⊓ F := ⟨⟨hFE hy.1, hy.2⟩, hy.1⟩
      rwa [hdisj] at this
    have hF2 : p ^ 2 ∣ Nat.card F := by
      have hFdvd : Nat.card F ∣ p ^ 3 := ⟨Nat.card (E ⊓ K : Subgroup Y), by rw [← hcF, mul_comm]⟩
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hFdvd
      rw [hk', hj', ← pow_add] at hcF
      have hkj := Nat.pow_right_injective hp.two_le hcF
      rw [hj']
      exact pow_dvd_pow p (by omega)
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p hF2
    let F₁ : Subgroup Y := F₀.map F.subtype
    have hF₁F : F₁ ≤ F := Subgroup.map_subtype_le F₀
    have hF₁c : Nat.card F₁ = p ^ 2 := by
      rw [Subgroup.card_map_of_injective F.subtype_injective, hF₀]
    have hF₁a : IsElemAbelian p F₁ := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hFa.2 x (hF₁F hx)⟩
      have h1 := congrArg Subtype.val (hFa.1.is_comm.comm (⟨a, hF₁F a.2⟩ : F) ⟨b, hF₁F b.2⟩)
      exact h1
    have hinj := conjNormal_injective (K := K) hC
    have hE' : CFSG.IsElementaryAbelian p (F₁.map (MulAut.conjNormal : Y →* MulAut K)) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF₁a _)
    have hc' : Nat.card (F₁.map (MulAut.conjNormal : Y →* MulAut K)) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hinj, hF₁c]
    obtain ⟨g, hg1, hgE⟩ := hF.out_rank _ hE' hc'
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hgE
    rw [← MulAut.conjNormal_val] at hyg
    have hyK : y = (g : Y) := hinj hyg
    have hy1 : y ∈ F ⊓ K := ⟨hF₁F hy, hyK ▸ g.2⟩
    rw [hFK, Subgroup.mem_bot] at hy1
    exact hg1 (Subtype.ext (hyK ▸ hy1))
  · exact hk'
  · exact absurd ⟨E ⊓ K, inf_le_right, hEKa, hk'⟩ hnoK

theorem hyperGen_of_fieldAutData (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hnoK : ¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (hF : FieldAutData K p) (hP : FixPlaneGen K p) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p K E := by
  have hp : p.Prime := Fact.out
  have hinj := conjNormal_injective (K := K) hC
  have hAc := card_inf_eq_of_fieldAutData hC hnoK hF hE hEc
  obtain ⟨x, hxE, hxK⟩ : ∃ x ∈ E, x ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hnoK ⟨E, hcon, hE, hEc⟩
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  let A : Subgroup K := (E ⊓ K).comap K.subtype
  have hAmap : A.map K.subtype = E ⊓ K := by
    rw [Subgroup.map_comap_eq, K.range_subtype]
    exact inf_eq_right.2 inf_le_right
  have hAcK : Nat.card A = p ^ 2 := by
    rw [← hAc, ← hAmap, Subgroup.card_map_of_injective K.subtype_injective]
  have hAa : IsElemAbelian p A := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => Subtype.ext ?_⟩
    · exact hcommE _ a.2.1 _ b.2.1
    · have h1 := hE.2 _ hy.1
      exact h1
  let σ : Y → MulAut K := fun a => MulAut.conjNormal (x * a)
  have hxa : ∀ a ∈ E ⊓ K, x * a ∈ E ∧ x * a ∉ K := fun a ha =>
    ⟨E.mul_mem hxE ha.1, fun h => hxK (by simpa using K.mul_mem h (K.inv_mem ha.2))⟩
  have hout : ∀ a ∈ E ⊓ K, IsOuterOfOrder p (σ a) := by
    intro a ha
    obtain ⟨h1, h2⟩ := hxa a ha
    have hne : x * a ≠ 1 := fun h => h2 (h ▸ K.one_mem)
    refine ⟨?_, fun g hg => h2 ?_⟩
    · rw [orderOf_injective _ hinj]
      exact orderOf_eq_prime (hE.2 _ h1) hne
    · have : x * a = (g : Y) := hinj (hg.trans MulAut.conjNormal_val.symm)
      rw [this]
      exact g.2
  have hAfix : ∀ a ∈ E ⊓ K, A ≤ fixedSubgroup (σ a) := by
    intro a ha b hb
    apply Subtype.ext
    change x * a * (b : Y) * (x * a)⁻¹ = b
    have h := hcommE (x * a) (hxa a ha).1 (b : Y) hb.1
    rw [h, mul_inv_cancel_right]
  have hfixle : ∀ a ∈ E ⊓ K, (fixedSubgroup (σ a)).map K.subtype ≤ hyperClosure p K E := by
    intro a ha
    obtain ⟨hf, hfK⟩ := hxa a ha
    have hf1 : x * a ≠ 1 := fun h => hfK (h ▸ K.one_mem)
    have hzK : ∀ y ∈ K, y ≠ 1 → y ∉ Subgroup.zpowers (x * a) := by
      intro y hyK hy1 hyz
      have hdvd : Nat.card (Subgroup.zpowers (x * a) ⊓ K : Subgroup Y) ∣ p := by
        rw [← orderOf_eq_prime (hE.2 _ hf) hf1, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
      · have : y ∈ (Subgroup.zpowers (x * a) ⊓ K : Subgroup Y) := ⟨hyz, hyK⟩
        rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at this
        exact hy1 this
      · have heq : (Subgroup.zpowers (x * a) ⊓ K : Subgroup Y) = Subgroup.zpowers (x * a) :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by
            rw [h1, Nat.card_zpowers, orderOf_eq_prime (hE.2 _ hf) hf1])
        exact hfK ((heq ▸ inf_le_right : Subgroup.zpowers (x * a) ≤ K)
          (Subgroup.mem_zpowers _))
    refine le_hyperClosure_of_plane hp hE hEc hf hf1 (Subgroup.map_subtype_le _) ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      have h1 := congrArg Subtype.val hk
      change x * a * (k : Y) * (x * a)⁻¹ = k at h1
      calc x * a * (k : Y) = x * a * (k : Y) * (x * a)⁻¹ * (x * a) := by group
        _ = k * (x * a) := by rw [h1]
    · have hgen := hP (σ a) (hout a ha) A (hAfix a ha) hAa hAcK
      refine (Subgroup.map_mono hgen).trans ?_
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨k, ⟨hk, b, hb, hb1, hkb⟩, rfl⟩
      refine ⟨⟨k, hk, rfl⟩, (b : Y), hb.1, hzK _ b.2 (fun h => hb1 (Subtype.ext h)), ?_⟩
      exact (congrArg Subtype.val hkb).symm
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ E ⊓ K, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (E ⊓ K : Subgroup Y) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hAc
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have h1E : (1 : Y) ∈ E ⊓ K := Subgroup.one_mem _
  have hdvd : p ∣ Nat.card (fixedSubgroup (σ 1)) := by
    have := Subgroup.card_dvd_of_le (hAfix 1 h1E)
    rw [hAcK] at this
    exact (dvd_pow_self p (by norm_num)).trans this
  have hne : fixedSubgroup (σ 1) ≠ fixedSubgroup (σ a₀) := by
    intro heq
    apply ha₀1
    have ha₀A : (⟨a₀, ha₀.2⟩ : K) ∈ A := ha₀
    have hcen := hF.center (σ 1) (hout 1 h1E) hdvd ⟨a₀, ha₀.2⟩ (hAfix 1 h1E ha₀A) (by
      intro k hk
      have hk' : k ∈ fixedSubgroup (σ a₀) := heq ▸ hk
      have e1 := congrArg Subtype.val hk
      have e2 := congrArg Subtype.val hk'
      change x * 1 * (k : Y) * (x * 1)⁻¹ = k at e1
      change x * a₀ * (k : Y) * (x * a₀)⁻¹ = k at e2
      apply Subtype.ext
      change a₀ * (k : Y) = k * a₀
      have e3 : x * (a₀ * (k : Y) * a₀⁻¹) * x⁻¹ = x * k * x⁻¹ := by
        rw [mul_one] at e1
        rw [e1]
        calc x * (a₀ * (k : Y) * a₀⁻¹) * x⁻¹ = x * a₀ * (k : Y) * (x * a₀)⁻¹ := by group
          _ = k := e2
      have e4 : a₀ * (k : Y) * a₀⁻¹ = k := by simpa using e3
      calc a₀ * (k : Y) = a₀ * (k : Y) * a₀⁻¹ * a₀ := by group
        _ = k * a₀ := by rw [e4])
    exact congrArg Subtype.val hcen
  rcases hF.gen (σ 1) (σ a₀) (hout 1 h1E) (hout a₀ ha₀) hne with htop | hsmall
  · rw [hyperGen_iff_le]
    intro k hk
    have hk' : (⟨k, hk⟩ : K) ∈ Subgroup.closure
        ((fixedSubgroup (σ 1) : Set K) ∪ (fixedSubgroup (σ a₀) : Set K)) := by
      rw [htop]
      exact Subgroup.mem_top _
    have h2 : (⟨k, hk⟩ : K) ∈ ((fixedSubgroup (σ 1)).map K.subtype ⊔
        (fixedSubgroup (σ a₀)).map K.subtype).comap K.subtype := by
      refine (Subgroup.closure_le _).2 ?_ hk'
      rintro y (hy | hy)
      · exact Subgroup.mem_sup_left ⟨y, hy, rfl⟩
      · exact Subgroup.mem_sup_right ⟨y, hy, rfl⟩
    exact sup_le (hfixle 1 h1E) (hfixle a₀ ha₀) h2
  · exact absurd hdvd hsmall

end Cube

end CFSG.LieType.SeitzGeneration
