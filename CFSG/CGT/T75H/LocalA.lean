module

public import CFSG.CGT.T75H.Classify
public import CFSG.CGT.Timmesfeld75.JLemmaQuot

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

section JCore

variable {R : Type} [Group R] [Finite R]

theorem jCore' {n : ℕ} (hInd : SimpleCaseUpTo n) (h215 : Lemma215Stmt) {T : Subgroup R}
    (hT : IsWC T) (hcl : Subgroup.normalClosure (T : Set R) = ⊤)
    (h4 : 4 ≤ Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 R))))
    (hn : Nat.card (R ⧸ CFSG.pCore 2 R) < n) :
    IsSimpleGroup (jQuot R) ∧ ListGroup (jQuot R) ∧ IsWC (T.map (jMap R)) ∧
      4 ≤ Nat.card (T.map (jMap R)) ∧ T ⊓ (jMap R).ker = T ⊓ CFSG.pCore 2 R := by
  classical
  set O := CFSG.pCore 2 R with hO
  set T₁ : Subgroup (R ⧸ O) := T.map (QuotientGroup.mk' O) with hT₁
  have hT₁wc : IsWC T₁ := isWC_map_pCore hT hcl
  have hcl₁ : Subgroup.normalClosure (T₁ : Set (R ⧸ O)) = ⊤ := by
    rw [hT₁, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _),
      hcl, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hO2 : ∀ N : Subgroup (R ⧸ O), N.Normal → IsPGroup 2 N → N = ⊥ :=
    normal_pGroup_quot_pCore_eq_bot
  have hnc₁ : ∃ a b : R ⧸ O, a * b ≠ b * a := exists_not_comm_quot_pCore hT hcl h4
  have hZodd := odd_card_center hO2
  set Z : Subgroup (R ⧸ O) := Subgroup.center (R ⧸ O) with hZ
  have hWCb : IsWC (T₁.map (QuotientGroup.mk' Z)) :=
    hT₁wc.map_quotient_central_odd Z le_rfl hZodd
  have hKb : Subgroup.normalClosure
      ((T₁.map (QuotientGroup.mk' Z) : Subgroup ((R ⧸ O) ⧸ Z)) : Set ((R ⧸ O) ⧸ Z)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), hcl₁,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h4b : 4 ≤ Nat.card (T₁.map (QuotientGroup.mk' Z)) :=
    four_le_card_map_central_odd hT₁wc.1 Z hZodd h4
  have hrad := solvable_radical_bot_quotient hT₁wc h4 hcl₁ hO2
  have hsimple : IsSimpleGroup ((R ⧸ O) ⧸ Z) := h215 _ _ hWCb h4b hKb hrad
  have hbot : T₁.map (QuotientGroup.mk' Z) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h4b
    omega
  have hnab : ∃ a b : (R ⧸ O) ⧸ Z, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hsolv : Group.IsSolvable (⊤ : Subgroup ((R ⧸ O) ⧸ Z)) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hcomm a b)
    have htop := hrad ⊤ inferInstance hsolv
    have hb : T₁.map (QuotientGroup.mk' Z) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [← htop]
      exact Subgroup.mem_top x
    exact hbot hb
  have hlt : Nat.card ((R ⧸ O) ⧸ Z) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective Z)) hn
  obtain ⟨hlist, htrans⟩ := hInd _ hlt hnab _ hWCb h4b
  have hTmap : T.map (jMap R) = T₁.map (QuotientGroup.mk' Z) := by
    rw [hT₁, jMap, Subgroup.map_map]
  rw [hTmap]
  refine ⟨hsimple, hlist, hWCb, h4b, ?_⟩
  · have hTZ : T₁ ⊓ Z = ⊥ := inf_center_eq_bot_of_not_comm hT₁wc hcl₁ hnc₁
    refine le_antisymm ?_ fun t ht => ⟨ht.1, pCore_le_ker_jMap ht.2⟩
    rintro t ⟨htT, htk⟩
    refine ⟨htT, ?_⟩
    have hz : QuotientGroup.mk' O t ∈ Z := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 htk)
    have hm : QuotientGroup.mk' O t ∈ T₁ ⊓ Z := ⟨Subgroup.mem_map_of_mem _ htT, hz⟩
    rw [hTZ, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff t).1 hm

end JCore

structure LocalCfg {R : Type} [Group R] (T : Subgroup R) (ℓ a b y x₁ : R) : Prop where
  card_four : Nat.card T = 4
  ha : a ∈ T
  hb : b ∈ T
  hT : ∀ t ∈ T, t = 1 ∨ t = a ∨ t = b ∨ t = b * a
  ha1 : a ≠ 1
  aa : a * a = 1
  ℓℓ : ℓ * ℓ = 1
  yy : y * y = 1
  comm_aℓ : a * ℓ = ℓ * a
  conj_ℓ_b : b * ℓ * b = ℓ * a
  conj_b_ℓ : ℓ * b * ℓ = b * a
  conj_a_y : a * y * a = y * ℓ
  hℓN : ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T
  hℓ : ℓ ∈ conjSubgroup x₁ T
  hy : y ∈ conjSubgroup x₁ T
  haN : ∀ u ∈ conjSubgroup x₁ T, a * u * a⁻¹ ∈ conjSubgroup x₁ T

section LocalA

variable {R : Type} [Group R] [Finite R]

omit [Finite R] in
theorem eq_one_of_mem_pCore {z : R} (hz : z ∈ CFSG.pCore 2 R) {q k : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hord : orderOf z = q ^ k) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.pCore 2 R) := CFSG.pCore_isPGroup
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hp) ⟨z, hz⟩
  have hm' : orderOf z = 2 ^ m := by
    rw [← Subgroup.orderOf_coe ⟨z, hz⟩] at hm
    exact hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact orderOf_eq_one_iff.1 (by simpa using hm')
  · exfalso
    have h2 : 2 ∣ q ^ k := by
      rw [← hord, hm']
      exact dvd_pow_self 2 hmpos.ne'
    have h2q : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h2q
    omega

omit [Finite R] in
theorem mem_normalizer_map {Y : Type} [Group Y] (f : R →* Y) {H : Subgroup R} {g : R}
    (hg : g ∈ Subgroup.normalizer (H : Set R)) :
    f g ∈ Subgroup.normalizer ((H.map f : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ g' ∈ Subgroup.normalizer (H : Set R), ∀ h' ∈ H.map f,
      f g' * h' * (f g')⁻¹ ∈ H.map f := by
    intro g' hg' h' hh'
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hh'
    refine Subgroup.mem_map.2 ⟨g' * r * g'⁻¹, (Subgroup.mem_normalizer_iff.1 hg' r).1 hr, ?_⟩
    simp
  constructor
  · exact key g hg h
  · intro h'
    have := key g⁻¹ ((Subgroup.normalizer (H : Set R)).inv_mem hg) _ h'
    have e : f g⁻¹ * (f g * h * (f g)⁻¹) * (f g⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    rwa [e] at this

omit [Finite R] in
theorem map_conjSubgroup' {Y : Type} [Group Y] (f : R →* Y) (x : R) (T : Subgroup R) :
    (conjSubgroup x T).map f = conjSubgroup (f x) (T.map f) := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [mem_conjSubgroup] at hr ⊢
    exact Subgroup.mem_map.2 ⟨_, hr, by simp⟩
  · intro hu
    rw [mem_conjSubgroup] at hu
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hu
    refine ⟨x * t * x⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup]
      simpa [mul_assoc] using ht
    · simp only [map_mul, map_inv, hte]
      group

omit [Finite R] in
theorem card_map_eq_of_inf_ker_eq_bot' {Y : Type} [Group Y] (f : R →* Y) {U : Subgroup R}
    (hU : U ⊓ f.ker = ⊥) : Nat.card (U.map f) = Nat.card U := by
  have hinj : Function.Injective (f.comp U.subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have : (q : R) ∈ U ⊓ f.ker := ⟨q.2, hq⟩
    rw [hU, Subgroup.mem_bot] at this
    exact Subtype.ext this
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
    Subgroup.range_subtype]

omit [Finite R] in
theorem map_pCore_equiv' [Finite R] (φ : R ≃* R) {r : R} (hr : r ∈ CFSG.pCore 2 R) :
    φ r ∈ CFSG.pCore 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((CFSG.pCore 2 R).map φ.toMonoidHom).Normal :=
    (CFSG.pCore_normal (p := 2) (G := R)).map φ.toMonoidHom φ.surjective
  have hp : IsPGroup 2 ((CFSG.pCore 2 R).map φ.toMonoidHom) :=
    (CFSG.pCore_isPGroup (p := 2) (G := R)).map φ.toMonoidHom
  have hle : (CFSG.pCore 2 R).map φ.toMonoidHom ≤ CFSG.pCore 2 R := le_sSup ⟨hn, hp⟩
  exact hle (Subgroup.mem_map.2 ⟨r, hr, rfl⟩)

theorem local_A {n : ℕ} (hInd : SimpleCaseUpTo n) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) (hn : Nat.card R < n) {T : Subgroup R} (hT : IsWC T)
    (hcl : Subgroup.normalClosure (T : Set R) = ⊤) {ℓ a b y x₁ : R}
    (C : LocalCfg T ℓ a b y x₁) (φ : R ≃* R) (hφ : ∀ t ∈ T, φ t = t) {q k : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hz : orderOf (ℓ * φ ℓ) = q ^ k) : φ ℓ = ℓ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 R with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hφO : ∀ r ∈ O, φ r ∈ O := fun r hr => map_pCore_equiv' φ hr
  have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right C.ℓℓ
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right C.aa
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right C.yy
  have hbb : b * b = 1 := elemAbelian_mul_self hT.1 C.hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hφℓℓ : φ ℓ * φ ℓ = 1 := by rw [← map_mul, C.ℓℓ, map_one]
  have hφℓinv : (φ ℓ)⁻¹ = φ ℓ := inv_eq_of_mul_eq_one_right hφℓℓ
  set z := ℓ * φ ℓ with hzdef
  have hzO_imp : z ∈ O → φ ℓ = ℓ := by
    intro hzO
    have h1 : z = 1 := eq_one_of_mem_pCore hzO hq hq5 hz
    have h2 : φ ℓ = ℓ⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, hℓinv]
  have hbO_imp : b ∈ O → a ∈ O := by
    intro hbO
    have h1 : ℓ * b * ℓ⁻¹ ∈ O := hOn.conj_mem b hbO ℓ
    rw [hℓinv, C.conj_b_ℓ] at h1
    have : a = b⁻¹ * (b * a) := by group
    rw [this]
    exact O.mul_mem (O.inv_mem hbO) h1
  have hℓO_imp : ℓ ∈ O → a ∈ O := by
    intro hℓO
    have h1 : b * ℓ * b⁻¹ ∈ O := hOn.conj_mem ℓ hℓO b
    rw [hbinv] at h1
    have : a = ℓ⁻¹ * (b * ℓ * b) := by rw [C.conj_ℓ_b, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact O.mul_mem (O.inv_mem hℓO) h1
  have haO_imp : a ∈ O → ℓ ∈ O := by
    intro haO
    have h1 : y⁻¹ * a * y⁻¹⁻¹ ∈ O := hOn.conj_mem a haO y⁻¹
    have e : y⁻¹ * a * y⁻¹⁻¹ * a = ℓ := by
      calc y⁻¹ * a * y⁻¹⁻¹ * a = y⁻¹ * (a * y * a) := by group
        _ = y⁻¹ * (y * ℓ) := by rw [C.conj_a_y]
        _ = ℓ := by group
    rw [← e]
    exact O.mul_mem h1 haO
  by_cases hTO : T ⊓ O = ⊥
  ·
    have hker : T ⊓ (QuotientGroup.mk' O).ker = ⊥ := by rw [QuotientGroup.ker_mk', hTO]
    have h4 : 4 ≤ Nat.card (T.map (QuotientGroup.mk' O)) := by
      rw [card_map_eq_of_inf_ker_eq_bot' _ hker, C.card_four]
    have hnlt : Nat.card (R ⧸ O) < n :=
      lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective O)) hn
    obtain ⟨hsimple, hlist, hWC, h4Y, hkerY⟩ := jCore' hInd h215 hT hcl h4 hnlt
    have : IsSimpleGroup (jQuot R) := hsimple
    have : Finite (jQuot R) := Finite.of_surjective _ (jMap_surjective (R := R))
    have hstd : StdPair (jQuot R) (T.map (jMap R)) := hI _ hlist _ hWC h4Y
    have hkerT : T ⊓ (jMap R).ker = ⊥ := by rw [hkerY, hTO]
    have hc4Y : Nat.card (T.map (jMap R)) = 4 := by
      rw [card_map_eq_of_inf_ker_eq_bot' _ hkerT, C.card_four]
    have hzT : ∀ t ∈ T, z * t = t * z := by
      intro t ht
      have ht' : ℓ * t * ℓ⁻¹ ∈ T := C.hℓN t ht
      have h1 : φ ℓ * t * (φ ℓ)⁻¹ = ℓ * t * ℓ⁻¹ := by
        have := hφ _ ht'
        rw [map_mul, map_mul, map_inv, hφ t ht] at this
        exact this
      have hconj : z * t * z⁻¹ = t := by
        calc z * t * z⁻¹ = ℓ * (φ ℓ * t * (φ ℓ)⁻¹) * ℓ⁻¹ := by rw [hzdef]; group
          _ = ℓ * (ℓ * t * ℓ⁻¹) * ℓ⁻¹ := by rw [h1]
          _ = (ℓ * ℓ) * t * (ℓ * ℓ)⁻¹ := by group
          _ = t := by rw [C.ℓℓ]; group
      exact mul_inv_eq_iff_eq_mul.1 hconj
    have hne : (conjSubgroup x₁ T).map (jMap R) ≠ T.map (jMap R) := by
      intro heq
      have hyT : jMap R y ∈ T.map (jMap R) := heq ▸ Subgroup.mem_map_of_mem _ C.hy
      obtain ⟨t, htT, hte⟩ := Subgroup.mem_map.1 hyT
      have hk : y * t⁻¹ ∈ (jMap R).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hte, mul_inv_cancel]
      have hc := mem_ker_jMap.1 hk a
      have hta : t * a = a * t := elemAbelian_mul_comm hT.1 htT C.ha
      have e : ⁅y * t⁻¹, a⁆ = ℓ := by
        rw [commutatorElement_def]
        calc y * t⁻¹ * a * (y * t⁻¹)⁻¹ * a⁻¹
            = y * (t⁻¹ * a * t) * y⁻¹ * a⁻¹ := by group
          _ = y * a * y * a := by
              have : t⁻¹ * a * t = a := by
                calc t⁻¹ * a * t = t⁻¹ * (a * t) := by group
                  _ = t⁻¹ * (t * a) := by rw [hta]
                  _ = a := by group
              rw [this, hyinv, hainv]
          _ = y * (a * y * a) := by group
          _ = y * (y * ℓ) := by rw [C.conj_a_y]
          _ = ℓ := by
              calc y * (y * ℓ) = (y * y) * ℓ := by group
                _ = ℓ := by rw [C.yy, one_mul]
      rw [e] at hc
      have haO : a ∈ O := hℓO_imp hc
      have : a ∈ T ⊓ O := ⟨C.ha, haO⟩
      rw [hTO, Subgroup.mem_bot] at this
      exact C.ha1 this
    have hconj : (conjSubgroup x₁ T).map (jMap R) = conjSubgroup (jMap R x₁) (T.map (jMap R)) :=
      map_conjSubgroup' _ _ _
    have haN0 : a ∈ Subgroup.normalizer ((conjSubgroup x₁ T : Subgroup R) : Set R) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      refine ⟨fun hu => C.haN u hu, fun hu => ?_⟩
      have := C.haN _ hu
      have e : a * (a * u * a⁻¹) * a⁻¹ = u := by
        calc a * (a * u * a⁻¹) * a⁻¹ = (a * a) * u * (a * a)⁻¹ := by group
          _ = u := by rw [C.aa]; group
      rwa [e] at this
    have haN : jMap R a ∈ Subgroup.normalizer
        (((conjSubgroup x₁ T).map (jMap R) : Subgroup (jQuot R)) : Set (jQuot R)) :=
      mem_normalizer_map _ haN0
    have hπa1 : jMap R a ≠ 1 := by
      intro h
      have : a ∈ T ⊓ (jMap R).ker := ⟨C.ha, h⟩
      rw [hkerT, Subgroup.mem_bot] at this
      exact C.ha1 this
    have hπaT : jMap R a ∈ T.map (jMap R) := Subgroup.mem_map_of_mem _ C.ha
    obtain ⟨j, -, hj⟩ : ∃ j ≤ k, orderOf (jMap R z) = q ^ j :=
      (Nat.dvd_prime_pow hq).1 ((orderOf_map_dvd _ z).trans (hz ▸ dvd_rfl))
    have hπz : jMap R z = 1 :=
      eq_one_of_centralizes hWC hstd hc4Y (jMap R x₁) hconj hne hπaT hπa1 haN hq hq5 hj
        (by
          rintro _ ⟨t, ht, rfl⟩
          rw [← map_mul, ← map_mul, hzT t ht])
    have hzk : z ∈ (jMap R).ker := hπz
    have hc := mem_ker_jMap.1 hzk ℓ
    have hzinv : z⁻¹ = φ ℓ * ℓ := by
      apply inv_eq_of_mul_eq_one_right
      calc z * (φ ℓ * ℓ) = ℓ * (φ ℓ * φ ℓ) * ℓ := by rw [hzdef]; group
        _ = 1 := by rw [hφℓℓ, mul_one, C.ℓℓ]
    have hz2 : z * z ∈ O := by
      have e : ⁅z, ℓ⁆ = z * z := by
        rw [commutatorElement_def, hzinv, hℓinv]
        calc z * ℓ * (φ ℓ * ℓ) * ℓ = ℓ * φ ℓ * ℓ * (φ ℓ * ℓ) * ℓ := by rw [hzdef]
          _ = ℓ * φ ℓ * (ℓ * φ ℓ) * (ℓ * ℓ) := by group
          _ = z * z := by rw [C.ℓℓ, mul_one]
      rw [← e]
      exact hc
    have hodd : Odd (q ^ k) := (hq.odd_of_ne_two (by omega)).pow
    obtain ⟨m, hm⟩ := hodd
    have hzpow : z ^ (2 * m + 1) = 1 := by rw [← hm, ← hz]; exact pow_orderOf_eq_one z
    have hzm : (z * z) ^ (m + 1) = z := by
      calc (z * z) ^ (m + 1) = z ^ (2 * m + 1) * z := by rw [← sq, ← pow_mul]; group
        _ = z := by rw [hzpow, one_mul]
    apply hzO_imp
    rw [← hzm]
    exact O.pow_mem hz2 _
  ·
    obtain ⟨t₀, ht₀⟩ : ∃ t : ↥(T ⊓ O), t ≠ 1 := (Subgroup.ne_bot_iff_exists_ne_one).1 hTO
    have ht₀T : (t₀ : R) ∈ T := t₀.2.1
    have ht₀O : (t₀ : R) ∈ O := t₀.2.2
    have ht₀1 : (t₀ : R) ≠ 1 := fun h => ht₀ (Subtype.ext h)
    have haO : a ∈ O := by
      rcases C.hT _ ht₀T with h | h | h | h
      · exact absurd h ht₀1
      · rw [← h]; exact ht₀O
      · exact hbO_imp (h ▸ ht₀O)
      · have hbaO : b * a ∈ O := h ▸ ht₀O
        have h1 : ℓ * (b * a) * ℓ⁻¹ ∈ O := hOn.conj_mem _ hbaO ℓ
        have e1 : ℓ * a * ℓ = a := by
          calc ℓ * a * ℓ = (a * ℓ) * ℓ := by rw [C.comm_aℓ]
            _ = a * (ℓ * ℓ) := by group
            _ = a := by rw [C.ℓℓ, mul_one]
        have e : ℓ * (b * a) * ℓ⁻¹ = b := by
          calc ℓ * (b * a) * ℓ⁻¹ = (ℓ * b * ℓ⁻¹) * (ℓ * a * ℓ⁻¹) := by group
            _ = (ℓ * b * ℓ) * (ℓ * a * ℓ) := by rw [hℓinv]
            _ = (b * a) * a := by rw [C.conj_b_ℓ, e1]
            _ = b := by rw [mul_assoc, C.aa, mul_one]
        rw [e] at h1
        exact hbO_imp h1
    have hℓO : ℓ ∈ O := haO_imp haO
    apply hzO_imp
    exact O.mul_mem hℓO (hφO ℓ hℓO)

end LocalA

end CFSG.CGT.T75H
