module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodIn
public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

section Cube

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]

theorem card_inf_eq_of_fieldAutData_of_not_le (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hF : FieldAutData K p) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hEK : ¬ E ≤ K) : Nat.card (E ⊓ K : Subgroup Y) = p ^ 2 := by
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
  · exfalso
    apply hEK
    have heq : (E ⊓ K : Subgroup Y) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hEc])
    rw [← heq]
    exact inf_le_right

theorem hyperGen_of_fieldAutData_of_not_le (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hF : FieldAutData K p) (hP : FixPlaneGen K p) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hEK : ¬ E ≤ K) : HyperGen p K E := by
  have hp : p.Prime := Fact.out
  have hinj := conjNormal_injective (K := K) hC
  have hAc := card_inf_eq_of_fieldAutData_of_not_le hC hF hE hEc hEK
  obtain ⟨x, hxE, hxK⟩ : ∃ x ∈ E, x ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hEK hcon
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

section Simple

variable {S : Type} [Group S] [Finite S]

theorem seitzHyperGamma_eq_top_of_fieldAutData (hZ : Subgroup.center S = ⊥) {p : ℕ}
    (hp : p.Prime) (hF : FieldAutData S p) (hP : FixPlaneGen S p) {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hout : ¬ E ≤ (MulAut.conj : S →* MulAut S).range) : seitzHyperGamma p E = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := SeitzHyperGoodInAux.conj_injective_of_center_bot hZ
  let ε : S ≃* (MulAut.conj : S →* MulAut S).range := MonoidHom.ofInjective hinj
  refine SeitzHyperGoodInAux.seitzHyperGamma_eq_top_of_hyperGen_inn hZ p ?_
  exact hyperGen_of_fieldAutData_of_not_le (SeitzHyperGoodInAux.centralizer_conj_range_eq_bot hZ)
    (hF.of_mulEquiv ε.symm hp) (hP.of_mulEquiv ε.symm hp) hE hEc hout

end Simple

@[expose] def SeitzGoodOuterHighAt (P : TauCeti.ValidLieTypeIndex → ℕ → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → ∀ d : TauCeti.ValidLieTypeIndex, P d p →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d → ¬ ExcIndex p d.1 →
    ¬ (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) →
    (∃ F : Subgroup S, IsElemAbelian p F ∧ Nat.card F = p ^ 3) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E → Nat.card E = p ^ 3 →
      ¬ E ≤ (MulAut.conj : S →* MulAut S).range → seitzHyperGamma p E = ⊤

theorem seitzGoodOuterHighFor_of_at {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (h : SeitzGoodOuterHighAt fun d _ => Fam d) : SeitzGoodOuterHighFor Fam :=
  fun p hp hp2 S _ _ hs hnab d hd he hpd hl hx hL hcube E hE hc hout =>
    h p hp hp2 S hs hnab d hd he hpd hl hx hL hcube E hE hc hout

theorem SeitzGoodOuterHighAt.of_cover {P Q R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (hc : ∀ d p, P d p → Q d p ∨ R d p) (hQ : SeitzGoodOuterHighAt Q)
    (hR : SeitzGoodOuterHighAt R) : SeitzGoodOuterHighAt P := by
  intro p hp hp2 S _ _ hs hnab d hP he hpd hl hx hL hcube E hE hc' hout
  rcases hc d p hP with h | h
  · exact hQ p hp hp2 S hs hnab d h he hpd hl hx hL hcube E hE hc' hout
  · exact hR p hp hp2 S hs hnab d h he hpd hl hx hL hcube E hE hc' hout

theorem exists_cube_cat_of_equiv {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h : ∃ F : Subgroup S, IsElemAbelian p F ∧ Nat.card F = p ^ 3) :
    ∃ F : Subgroup (Cat d), IsElemAbelian p F ∧ Nat.card F = p ^ 3 := by
  obtain ⟨F, hF, hc⟩ := h
  exact ⟨F.map e.toMonoidHom, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _,
    by rw [Subgroup.card_map_of_injective e.injective, hc]⟩

theorem SeitzGoodOuterHighAt.of_pair {P : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : ∀ d p, P d p → p.Prime → p ≠ 2 → p ≠ d.1.characteristic → ¬ P1ThreeLieList p d →
      ¬ ExcIndex p d.1 →
      ¬ (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) →
      (∃ F : Subgroup (Cat d), IsElemAbelian p F ∧ Nat.card F = p ^ 3) →
      FieldAutData (Cat d) p ∧ FixPlaneGen (Cat d) p) : SeitzGoodOuterHighAt P := by
  intro p hp hp2 S _ _ hs hnab d hP he hpd hl hx hL hcube E hE hc hout
  obtain ⟨e⟩ := he
  obtain ⟨hF, hFix⟩ := h d p hP hp hp2 hpd hl hx hL (exists_cube_cat_of_equiv e hcube)
  exact seitzHyperGamma_eq_top_of_fieldAutData (SeitzBridgeAux.center_eq_bot_of_simple hs hnab) hp
    (hF.of_mulEquiv e hp) (hFix.of_mulEquiv e hp) hE hc hout

theorem closure_comm_of_planeClosure_conj {K : Type*} [Group K] {B : Subgroup K}
    (h : planeClosure (B.map (MulAut.conj : K →* MulAut K)) = ⊤) :
    Subgroup.closure {k : K | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  rw [eq_top_iff, ← h, planeClosure]
  refine Subgroup.closure_mono ?_
  rintro k ⟨_, ⟨x, hx, rfl⟩, hx1, hk⟩
  refine ⟨x, hx, ?_, ?_⟩
  · rintro rfl
    exact hx1 (map_one _)
  · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hk
    exact hk.symm

theorem closure_centralizers_cat_of_kfact (hS : KFactSeitzRankTwo) {d : TauCeti.ValidLieTypeIndex}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (B : Subgroup (Cat d)) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) :
    Subgroup.closure {k : Cat d | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hE : IsElemAbelian p (B.map (MulAut.conj : Cat d →* MulAut (Cat d))) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hB _
  have hEc : Nat.card (B.map (MulAut.conj : Cat d →* MulAut (Cat d))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hBc]
  exact closure_comm_of_planeClosure_conj (hS d p hp hp2 hpd hex _ hE hEc)

theorem closure_centralizers_of_equiv_cat (hS : KFactSeitzRankTwo) {Q : Type} [Group Q]
    {d : TauCeti.ValidLieTypeIndex} (e : Q ≃* Cat d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (B : Subgroup Q) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) :
    Subgroup.closure {k : Q | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have h := closure_centralizers_cat_of_kfact hS hp hp2 hpd hex hinj (B.map e.toMonoidHom)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hB _)
    (by rw [Subgroup.card_map_of_injective e.injective, hBc])
  have h1 : (Subgroup.closure {k : Q | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure, eq_top_iff, ← h]
    refine Subgroup.closure_le _ |>.2 ?_
    rintro k ⟨_, ⟨x, hx, rfl⟩, hx1, hkx⟩
    refine Subgroup.subset_closure ⟨e.symm k, ⟨x, hx, fun h1 => hx1 (by rw [h1, map_one]), ?_⟩,
      by simp⟩
    apply e.injective
    simpa using hkx
  rw [eq_top_iff]
  intro y _
  have : e y ∈ (Subgroup.closure {k : Q | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom := by
    rw [h1]; trivial
  obtain ⟨z, hz, hzy⟩ := this
  rwa [e.injective hzy] at hz

theorem closure_comm_planes_of_simple_kfact (hS : KFactSeitzRankTwo)
    {d₀ : TauCeti.ValidLieTypeIndex} {P₀ : Type} [Group P₀] [IsSimpleGroup P₀]
    (hnab : ∃ a b : P₀, a * b ≠ b * a) (ε : Cat d₀ ≃* P₀) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ≠ d₀.1.characteristic) (hex : ¬ IsD2SeitzException p d₀.1) :
    ∀ E₁ : Subgroup P₀, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hs : IsSimpleGroup (Cat d₀) := MulEquiv.isSimpleGroup ε
  have hnab' : ∃ a b : Cat d₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨ε.symm a, ε.symm b, fun h => hab ?_⟩
    have := congrArg ε h
    simpa using this
  have hinj := SeitzHyperGoodInAux.conj_injective_of_center_bot
    (SeitzBridgeAux.center_eq_bot_of_simple hs hnab')
  intro E₁ hE₁ hc₁
  exact closure_centralizers_of_equiv_cat hS ε.symm hp hp2 hpd hex hinj E₁ hE₁ hc₁

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

end
