module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonabBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.EdgeAux

open CFSG.Quasithin
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem mem_sup_of_normalizes {X Y : Subgroup G} (hY : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    {g : G} (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  let T : Subgroup G :=
    { carrier := {g | ∃ x ∈ X, ∃ y ∈ Y, g = x * y}
      one_mem' := ⟨1, X.one_mem, 1, Y.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
        exact ⟨x₁ * (y₁ * x₂ * y₁⁻¹), X.mul_mem hx₁ (hY y₁ hy₁ x₂ hx₂), y₁ * y₂,
          Y.mul_mem hy₁ hy₂, by group⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact ⟨y⁻¹ * x⁻¹ * y⁻¹⁻¹, hY y⁻¹ (Y.inv_mem hy) x⁻¹ (X.inv_mem hx), y⁻¹, Y.inv_mem hy,
          by group⟩ }
  have hle : X ⊔ Y ≤ T :=
    sup_le (fun x hx => ⟨x, hx, 1, Y.one_mem, (mul_one x).symm⟩)
      (fun y hy => ⟨1, X.one_mem, y, hy, (one_mul y).symm⟩)
  exact hle hg

theorem eq_one_of_odd_orderOf_of_pow_two {g : G} (hodd : Odd (orderOf g)) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf g) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 dvd_rfl)

theorem orderOf_two_pow_of_mem {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q) :
    ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  exact ⟨j, hj⟩

theorem normal_subgroupOf_of_le_normalizer {X L : Subgroup G}
    (h : L ≤ Subgroup.normalizer (X : Set G)) : (X.subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg := Subgroup.mem_normalizer_iff.mp (h g.2) (n : G)
  simpa using hg.1 hn

theorem commutatorElement_mul_central_left {r y z : G} (hz : z ∈ Subgroup.center G) :
    ⁅r * z, y⁆ = ⁅r, y⁆ := by
  have hzy : z * y = y * z := (Subgroup.mem_center_iff.1 hz y).symm
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : r * z * y * (r * z)⁻¹ * y⁻¹ = r * (z * y) * z⁻¹ * r⁻¹ * y⁻¹ := by group
  rw [e1, hzy]
  group

theorem commutatorElement_mul_central_right {r y z : G} (hz : z ∈ Subgroup.center G) :
    ⁅r, y * z⁆ = ⁅r, y⁆ := by
  have hzr : r⁻¹ * z = z * r⁻¹ := Subgroup.mem_center_iff.1 hz r⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : r * (y * z) * r⁻¹ * (y * z)⁻¹ = r * y * (z * r⁻¹) * z⁻¹ * y⁻¹ := by group
  rw [e1, ← hzr]
  group

theorem commute_of_isSimpleGroup_of_isPGroup_two {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : IsPGroup 2 Y) (a b : Y) : a * b = b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (Subgroup.center Y) := hY.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h0 | h1
  · exfalso
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center Y))
    apply hz
    apply Subtype.ext
    have hz2 : (z : Y) ∈ (⊥ : Subgroup Y) := by
      rw [← h0]
      exact z.2
    exact Subgroup.mem_bot.1 hz2
  · have ha : a ∈ Subgroup.center Y := by
      rw [h1]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem normal_le_center_or_eq_top_of_isQuasisimpleTwoNonab {E : Type*} [Group E] [Finite E]
    (h : IsQuasisimpleTwoNonab E) (R : Subgroup E) [R.Normal] :
    R ≤ Subgroup.center E ∨ R = ⊤ := by
  obtain ⟨hperf, hs, -, -, -⟩ := h
  haveI := hs
  haveI : (R.map (QuotientGroup.mk' (Subgroup.center E))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (R.map (QuotientGroup.mk' (Subgroup.center E))) with h0 | h1
  · left
    intro r hr
    have hmem : QuotientGroup.mk' (Subgroup.center E) r ∈
        R.map (QuotientGroup.mk' (Subgroup.center E)) :=
      Subgroup.mem_map_of_mem _ hr
    rw [h0, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff r).1 hmem
  · right
    have hdec : ∀ x : E, ∃ r ∈ R, ∃ z ∈ Subgroup.center E, x = r * z := by
      intro x
      have hx : QuotientGroup.mk' (Subgroup.center E) x ∈
          R.map (QuotientGroup.mk' (Subgroup.center E)) := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.1 hx
      refine ⟨r, hr, r⁻¹ * x, ?_, by group⟩
      exact (QuotientGroup.eq (s := Subgroup.center E)).1 hrx
    have hc : commutator E ≤ R := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ := hdec g₁
      obtain ⟨r₂, hr₂, z₂, hz₂, rfl⟩ := hdec g₂
      rw [commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂,
        commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
    rw [hperf] at hc
    exact top_le_iff.1 hc

theorem eq_bot_of_normal_isPGroup_two_of_isQuasisimpleTwoNonab {E : Type*} [Group E] [Finite E]
    (h : IsQuasisimpleTwoNonab E) (R : Subgroup E) [R.Normal] (hR : IsPGroup 2 R) : R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases normal_le_center_or_eq_top_of_isQuasisimpleTwoNonab h R with hle | htop
  · rw [eq_bot_iff]
    intro r hr
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact Subgroup.mem_bot.2 (eq_one_of_odd_orderOf_of_pow_two (h.2.2.2.1 r (hle hr)) hk')
  · exfalso
    obtain ⟨hperf, hs, -, -, Q, hQ, a, ha, b, hb, hab⟩ := h
    haveI := hs
    have hE : IsPGroup 2 E := by
      intro g
      have hgR : g ∈ R := by
        rw [htop]
        exact Subgroup.mem_top g
      obtain ⟨k, hk⟩ := hR ⟨g, hgR⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hcomm := commute_of_isSimpleGroup_of_isPGroup_two (hE.to_quotient (Subgroup.center E))
    have hcen : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E := by
      intro x y
      have h1 : QuotientGroup.mk' (Subgroup.center E) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hc : commutator E ≤ Subgroup.center E :=
      Subgroup.commutator_le.2 (fun x _ y _ => hcen x y)
    rw [hperf] at hc
    exact hab (Subgroup.mem_center_iff.1 (hc (Subgroup.mem_top a)) b).symm

theorem mem_center_of_map_mem_center {E F : Type*} [Group E] [Group F] (ψ : E →* F)
    (hker : ∀ e ∈ ψ.ker, e ∈ Subgroup.center E) (hperf : commutator E = ⊤) {x : E}
    (hx : ψ x ∈ Subgroup.center F) : x ∈ Subgroup.center E := by
  have hc : ∀ y : E, ⁅x, y⁆ ∈ Subgroup.center E := fun y => hker _ (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hx (ψ y)).symm)
  let d : E →* ↥(Subgroup.center E) :=
    { toFun := fun y => ⟨⁅x, y⁆, hc y⟩
      map_one' := Subtype.ext (commutatorElement_one_right x)
      map_mul' := fun y y' => Subtype.ext (by
        have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        have hy' := Subgroup.mem_center_iff.1 (hc y') y
        show ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆
        rw [e, show y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ by rw [hy']; group]) }
  have hd : commutator E ≤ d.ker := Abelianization.commutator_subset_ker d
  rw [hperf] at hd
  refine Subgroup.mem_center_iff.2 fun y => ?_
  have h1 : ⁅x, y⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 (hd (Subgroup.mem_top y)))
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem isQuasisimpleTwoNonab_of_central_odd_image {E F : Type*} [Group E] [Finite E] [Group F]
    (ψ : E →* F) (hψ : Function.Surjective ψ)
    (hker : ∀ e ∈ ψ.ker, e ∈ Subgroup.center E ∧ Odd (orderOf e))
    (h : IsQuasisimpleTwoNonab E) : IsQuasisimpleTwoNonab F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, hs, hn, ho, Q, hQ, a, ha, b, hb, hab⟩ := h
  haveI := hs
  have hcen : ∀ x : E, ψ x ∈ Subgroup.center F → x ∈ Subgroup.center E :=
    fun x hx => mem_center_of_map_mem_center ψ (fun e he => (hker e he).1) hperf hx
  let χ : E →* F ⧸ Subgroup.center F := (QuotientGroup.mk' (Subgroup.center F)).comp ψ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ
  have hkerχ : χ.ker = Subgroup.center E := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      exact hcen x ((QuotientGroup.eq_one_iff _).1 hx)
    · intro hx
      refine (QuotientGroup.eq_one_iff _).2 ?_
      refine Subgroup.mem_center_iff.2 fun g => ?_
      obtain ⟨y, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  let eq : E ⧸ Subgroup.center E ≃* F ⧸ Subgroup.center F :=
    (QuotientGroup.quotientMulEquivOfEq hkerχ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχ)
  have hsimple : IsSimpleGroup (F ⧸ Subgroup.center F) := MulEquiv.isSimpleGroup eq.symm
  have hcomm : commutator F = ⊤ := by
    have hmap : (commutator E).map ψ = commutator F := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective ψ hψ]
    rw [← hmap, hperf, Subgroup.map_top_of_surjective ψ hψ]
  have hcard : 120 < Nat.card (F ⧸ Subgroup.center F) := by
    rw [Nat.card_congr eq.symm.toEquiv]
    exact hn
  have hodd' : ∀ z ∈ Subgroup.center F, Odd (orderOf z) := by
    intro z hz
    obtain ⟨x, rfl⟩ := hψ z
    exact Odd.of_dvd_nat (ho x (hcen x hz)) (orderOf_map_dvd ψ x)
  refine ⟨hcomm, hsimple, hcard, hodd', Q.map ψ, hQ.map ψ, ψ a, Subgroup.mem_map_of_mem ψ ha,
    ψ b, Subgroup.mem_map_of_mem ψ hb, fun hcab => hab ?_⟩
  have hkab : ⁅a, b⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcab
  have hz := hker _ hkab
  have hQab : ⁅a, b⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  obtain ⟨j, hj⟩ := orderOf_two_pow_of_mem hQ hQab
  have hpow : ⁅a, b⁆ ^ 2 ^ j = 1 := by
    rw [← hj]
    exact pow_orderOf_eq_one _
  rw [← commutatorElement_eq_one_iff_mul_comm]
  exact eq_one_of_odd_orderOf_of_pow_two hz.2 hpow

theorem twoResidual_mono_aux [Finite G] {X Y : Subgroup G} (h : X ≤ Y) :
    twoResidual X ≤ twoResidual Y := by
  refine le_trans (twoResidual_le_of_isTwoQuotient (H := X) (N := twoResidual Y ⊓ X) inf_le_right
    ?_ ?_) inf_le_left
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have h1 : x * n * x⁻¹ ∈ twoResidual Y ↔ n ∈ twoResidual Y :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual Y (h hx)) n).symm
    have h2 : x * n * x⁻¹ ∈ X ↔ n ∈ X := by
      constructor
      · intro hn
        have := X.mul_mem (X.mul_mem (X.inv_mem hx) hn) hx
        simpa [mul_assoc] using this
      · intro hn
        exact X.mul_mem (X.mul_mem hx hn) (X.inv_mem hx)
    simp only [Subgroup.mem_inf, h1, h2]
  · intro y hy
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient Y y (h hy)
    exact ⟨k, Subgroup.mem_inf.2 ⟨hk, X.pow_mem hy _⟩⟩

theorem map_twoResidual_le_aux [Finite G] {G' : Type*} [Group G'] (φ : G →* G') (X : Subgroup G) :
    (twoResidual X).map φ ≤ twoResidual (X.map φ) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [mem_twoResidual_iff]
  intro N' _ hN'norm hN'2
  have key : twoResidual X ≤ N'.comap φ ⊓ X := by
    refine twoResidual_le_of_isTwoQuotient (H := X) (N := N'.comap φ ⊓ X) inf_le_right ?_ ?_
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have h1 : φ (x * n * x⁻¹) ∈ N' ↔ φ n ∈ N' := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp (hN'norm ⟨x, hx, rfl⟩) (φ n)).symm
      have h2 : x * n * x⁻¹ ∈ X ↔ n ∈ X := by
        constructor
        · intro hn
          have := X.mul_mem (X.mul_mem (X.inv_mem hx) hn) hx
          simpa [mul_assoc] using this
        · intro hn
          exact X.mul_mem (X.mul_mem hx hn) (X.inv_mem hx)
      simp only [Subgroup.mem_inf, Subgroup.mem_comap, h1, h2]
    · intro y hy
      obtain ⟨k, hk⟩ := hN'2 (φ y) ⟨y, hy, rfl⟩
      exact ⟨k, by simpa [map_pow] using hk, X.pow_mem hy _⟩
  exact (key hm).1

end Group

section Factor

variable {S : Type*} [Group S]

theorem quasisimpleModTwoNonab_of_factor [Finite S] {V L' P : Subgroup S}
    (hV : ∀ v ∈ V, ∃ k : ℕ, v ^ 2 ^ k = 1)
    (hL'V : L' ≤ Subgroup.normalizer (V : Set S))
    (hPL : P ≤ L')
    (hL'P : L' ≤ Subgroup.normalizer (P : Set S))
    (hP2 : ∀ x ∈ L', ∃ k : ℕ, x ^ 2 ^ k ∈ P)
    (hPT : P ≤ twoResidual (V ⊔ L'))
    (hP : IsQuasisimpleTwoNonab ↥P) :
    QuasisimpleModTwoNonab ↥(twoResidual (V ⊔ L')) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : ∀ y ∈ L', ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hL'V hy) v).mp hv
  have hL'N : L' ≤ Subgroup.normalizer ((V ⊔ P : Subgroup S) : Set S) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.1 (hL'V hx),
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hL'P hx)]
  have hWN : V ⊔ L' ≤ Subgroup.normalizer ((V ⊔ P : Subgroup S) : Set S) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) hL'N
  have hN0W : V ⊔ P ≤ V ⊔ L' := sup_le le_sup_left (hPL.trans le_sup_right)
  have hA2 : twoResidual (V ⊔ L') ≤ V ⊔ P := by
    refine twoResidual_le_of_isTwoQuotient hN0W hWN ?_
    intro y hy
    obtain ⟨v, hv, x, hx, rfl⟩ := mem_sup_of_normalizes hVL hy
    obtain ⟨k, hk⟩ := hP2 x hx
    have claim : ∀ m : ℕ, ∃ n ∈ V ⊔ P, (v * x) ^ m = x ^ m * n := by
      intro m
      induction m with
      | zero => exact ⟨1, (V ⊔ P).one_mem, by simp⟩
      | succ m ih =>
        obtain ⟨n, hn, hvx⟩ := ih
        refine ⟨x⁻¹ * (n * v) * x, ?_, ?_⟩
        · have hnv : n * v ∈ V ⊔ P := (V ⊔ P).mul_mem hn ((le_sup_left : V ≤ V ⊔ P) hv)
          have hxinv : x⁻¹ ∈ V ⊔ L' := (le_sup_right : L' ≤ V ⊔ L') (L'.inv_mem hx)
          have h := (Subgroup.mem_normalizer_iff.mp (hWN hxinv) (n * v)).mp hnv
          rw [inv_inv] at h
          exact h
        · rw [pow_succ, hvx, pow_succ]
          group
    obtain ⟨n, hn, e⟩ := claim (2 ^ k)
    refine ⟨k, ?_⟩
    rw [e]
    exact (V ⊔ P).mul_mem ((le_sup_right : P ≤ V ⊔ P) hk) hn
  have hdecA : ∀ a ∈ twoResidual (V ⊔ L'), ∃ v ∈ V, ∃ p ∈ P, a = v * p := by
    intro a ha
    obtain ⟨v, hv, p, hp, rfl⟩ := mem_sup_of_normalizes (X := V) (Y := P)
      (fun p hp v hv => (Subgroup.mem_normalizer_iff.mp (hL'V (hPL hp)) v).mp hv) (hA2 ha)
    exact ⟨v, hv, p, hp, rfl⟩
  set A : Subgroup S := twoResidual (V ⊔ L') with hAdef
  have hAW : A ≤ V ⊔ L' := twoResidual_le _
  have hWV : V ⊔ L' ≤ Subgroup.normalizer (V : Set S) := sup_le Subgroup.le_normalizer hL'V
  haveI hMn : ((V ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnV, hnA⟩ := Subgroup.mem_inf.1 hn
    have hg := Subgroup.mem_normalizer_iff.mp (hWV (hAW g.2)) (n : S)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.2 ⟨hg.1 hnV,
      A.mul_mem (A.mul_mem g.2 hnA) (A.inv_mem g.2)⟩
  have hMp : IsPGroup 2 ((V ⊓ A).subgroupOf A) := by
    intro m
    have hm : ((m : A) : S) ∈ V := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 m.2)).1
    obtain ⟨k, hk⟩ := hV _ hm
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hk
  have hMle : (V ⊓ A).subgroupOf A ≤ CFSG.pCore 2 ↥A := le_sSup ⟨hMn, hMp⟩
  let ι : ↥P →* ↥A := Subgroup.inclusion hPT
  let g : ↥P →* ↥A ⧸ CFSG.pCore 2 ↥A := (QuotientGroup.mk' (CFSG.pCore 2 ↥A)).comp ι
  have hR : (CFSG.pCore 2 ↥A).comap ι = ⊥ := by
    haveI : ((CFSG.pCore 2 ↥A).comap ι).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥A)).comap ι
    exact eq_bot_of_normal_isPGroup_two_of_isQuasisimpleTwoNonab hP _
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥A)).comap_of_injective ι
        (Subgroup.inclusion_injective hPT))
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hmem : ι p ∈ CFSG.pCore 2 ↥A := (QuotientGroup.eq_one_iff (ι p)).1 hp
    have hpR : p ∈ (CFSG.pCore 2 ↥A).comap ι := hmem
    rw [hR, Subgroup.mem_bot] at hpR
    exact hpR
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v, hv, p, hp, hap⟩ := hdecA (a : S) a.2
    have hvA : v ∈ A := by
      have hv' : v = (a : S) * p⁻¹ := by
        rw [hap]
        group
      rw [hv']
      exact A.mul_mem a.2 (A.inv_mem (hPT hp))
    have hvM : (⟨v, hvA⟩ : ↥A) ∈ CFSG.pCore 2 ↥A :=
      hMle (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hv, hvA⟩))
    refine ⟨⟨p, hp⟩, ?_⟩
    have ha : a = (⟨v, hvA⟩ : ↥A) * ι ⟨p, hp⟩ := Subtype.ext hap
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥A) (⟨v, hvA⟩ : ↥A) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hvM
    calc g ⟨p, hp⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥A) ((⟨v, hvA⟩ : ↥A) * ι ⟨p, hp⟩) := by
          rw [map_mul, h1, one_mul]
          rfl
      _ = QuotientGroup.mk' (CFSG.pCore 2 ↥A) a := by rw [ha]
  exact quasisimpleModTwoNonab_of_mulEquiv (MulEquiv.ofBijective g ⟨hinj, hsurj⟩).symm hP

end Factor

end CFSG.AGLEmbeddingD2.Tits.GN516.EdgeAux
