module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusU3Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

namespace InnerQ.KFC1

theorem zpow_mul_self_of_pow_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) {m : ℤ}
    (hm : ¬ (3 : ℤ) ∣ m) : x ^ (m * m) = x := by
  have hmod : m * m ≡ 1 [ZMOD 3] := by
    have h : m % 3 = 1 ∨ m % 3 = 2 := by omega
    unfold Int.ModEq
    rw [Int.mul_emod]
    rcases h with h | h <;> rw [h] <;> norm_num
  have hdvd : (orderOf x : ℤ) ∣ 3 := by exact_mod_cast orderOf_dvd_of_pow_eq_one hx
  conv_rhs => rw [← zpow_one x]
  exact (zpow_eq_zpow_iff_modEq).mpr (Int.ModEq.of_dvd hdvd hmod)

theorem exists_zpow_of_card_three {W : Type*} [Group W] (hW : Nat.card W = 3) (φ : W →* W)
    (hφ : ∃ w, φ w ≠ 1) : ∀ w, φ (φ w) = w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic W := isCyclic_of_prime_card hW
  have : Finite W := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ
  have hpow : ∀ w : W, w ^ 3 = 1 := fun w => by rw [← hW]; exact pow_card_eq_one'
  have h3 : ¬ (3 : ℤ) ∣ m := by
    rintro ⟨k, rfl⟩
    obtain ⟨w, hw⟩ := hφ
    apply hw
    rw [hm, zpow_mul, zpow_ofNat, hpow, one_zpow]
  intro w
  rw [hm, hm, ← zpow_mul, zpow_mul_self_of_pow_three (hpow w) h3]

theorem sq_eq_one_of_line {V : Type*} [CommGroup V] (hV3 : ∀ v : V, v ^ 3 = 1)
    (hV : Nat.card V = 9) {L : Subgroup V} (hL : Nat.card L = 3) (σ : MulAut V)
    (hσL : ∀ l ∈ L, σ l ∈ L) (hσ8 : σ ^ 8 = 1) : σ ^ 2 = 1 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  set σL : L →* L :=
    { toFun := fun l => ⟨σ l, hσL l l.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : V) (b : V)) } with hσLdef
  have hL1 : ∃ l : L, σL l ≠ 1 := by
    have : Nontrivial L := by
      rw [← Finite.one_lt_card_iff_nontrivial, hL]
      norm_num
    obtain ⟨l, hl⟩ := exists_ne (1 : L)
    refine ⟨l, fun h => hl ?_⟩
    have h1 : σ (l : V) = 1 := congrArg Subtype.val h
    rw [map_eq_one_iff _ σ.injective] at h1
    exact Subtype.ext h1
  have hfixL : ∀ l ∈ L, σ (σ l) = l := fun l hl => by
    have := exists_zpow_of_card_three hL σL hL1 ⟨l, hl⟩
    exact congrArg Subtype.val this
  set σQ : V ⧸ L →* V ⧸ L := QuotientGroup.map L L σ.toMonoidHom fun l hl => hσL l hl
  have hQ : Nat.card (V ⧸ L) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    rw [hV, hL] at h
    omega
  have hQ1 : ∃ w, σQ w ≠ 1 := by
    have : Nontrivial (V ⧸ L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hQ]
      norm_num
    obtain ⟨w₀, hw₀⟩ := exists_ne (1 : V ⧸ L)
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective L w₀
    refine ⟨QuotientGroup.mk' L (σ.symm v), ?_⟩
    rw [show σQ (QuotientGroup.mk' L (σ.symm v)) = QuotientGroup.mk' L v by
      simp [σQ, QuotientGroup.map_mk']]
    exact hw₀
  have hfixQ : ∀ v : V, (σ (σ v))⁻¹ * v ∈ L := fun v => by
    have h := exists_zpow_of_card_three hQ σQ hQ1 (QuotientGroup.mk' L v)
    simp only [σQ, QuotientGroup.map_mk', MulEquiv.coe_toMonoidHom] at h
    exact (QuotientGroup.eq).mp h
  have hτ : ∀ v : V, (σ ^ 2) v = v := by
    intro v
    set c := (σ ^ 2) v * v⁻¹ with hc
    have hcL : c ∈ L := by
      have := inv_mem (hfixQ v)
      simpa [hc, pow_two, mul_comm] using this
    have hτc : (σ ^ 2) c = c := by
      rw [pow_two, MulAut.mul_apply]
      exact hfixL c hcL
    have hτv : (σ ^ 2) v = c * v := by rw [hc]; group
    have hiter : ∀ k : ℕ, ((σ ^ 2) ^ k) v = c ^ k * v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hτc, hτv, pow_succ]
        group
    have h4 := hiter 4
    rw [← pow_mul, show 2 * 4 = 8 from rfl, hσ8, MulAut.one_apply] at h4
    have hc4 : c ^ 4 = 1 := by
      have := congrArg (· * v⁻¹) h4
      simpa using this.symm
    have hc1 : c = 1 := by
      calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
        _ = 1 := by rw [hc4, hV3, one_mul, inv_one]
    rw [hτv, hc1, one_mul]
  exact MulEquiv.ext hτ

open CFSG.OrderReductions.FrattiniAutomorphisms in
theorem le_frattini_or_eq_top {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (h27 : Nat.card P = 27) (hnab : ¬ ∀ a b : P, a * b = b * a) (f : MulAut P) (hf8 : f ^ 8 = 1)
    (hf4 : f ^ 4 ≠ 1) (D : Subgroup P) (hD : ∀ d ∈ D, f d ∈ D) : D ≤ frattini P ∨ D = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hchar, hcomm, hpow, -, e, hcard, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  set Φ := frattini P with hΦ
  letI : CommGroup (P ⧸ Φ) :=
    { (inferInstance : Group (P ⧸ Φ)) with mul_comm := hcomm.is_comm.comm }
  have hmk : ∀ a b : P, QuotientGroup.mk' Φ a = QuotientGroup.mk' Φ b → a⁻¹ * b ∈ Φ :=
    fun a b h => (QuotientGroup.eq).mp h
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup Φ
  rw [h27] at hsplit
  have hcomm_of : (∀ a b : P ⧸ Φ, a * b = b * a) → Φ = ⊥ → False := fun h hb => hnab fun a b => by
    have := hmk (a * b) (b * a) (by rw [map_mul, map_mul]; exact h _ _)
    rw [hb, mem_bot, inv_mul_eq_one] at this
    exact this
  have hV : Nat.card (P ⧸ Φ) = 9 := by
    rw [hcard] at hsplit ⊢
    have he3 : e ≤ 3 := by
      by_contra h
      have : 3 ^ 4 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < Nat.card Φ := Nat.card_pos
      nlinarith
    interval_cases e
    ·
      exfalso
      have hΦtop : Φ = ⊤ := by
        rw [pow_zero, one_mul] at hsplit
        exact Subgroup.eq_top_of_card_eq Φ (by rw [h27]; exact hsplit.symm)
      have := frattini_nongenerating (K := (⊥ : Subgroup P)) (by rw [← hΦ, hΦtop, sup_top_eq])
      obtain ⟨a, b, hab⟩ : ∃ a b : P, a * b ≠ b * a := by
        by_contra h
        push Not at h
        exact hnab h
      apply hab
      have ha : a ∈ (⊥ : Subgroup P) := this ▸ mem_top a
      rw [mem_bot] at ha
      rw [ha, one_mul, mul_one]
    ·
      exfalso
      have hcyc : IsCyclic (P ⧸ Φ) := isCyclic_of_prime_card (p := 3) (by simpa using hcard)
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Φ g
      have hsup : zpowers x ⊔ Φ = ⊤ := by
        refine eq_top_iff.mpr fun y _ => ?_
        obtain ⟨k, hk⟩ := hg (QuotientGroup.mk' Φ y)
        have hk' : QuotientGroup.mk' Φ (x ^ k) = QuotientGroup.mk' Φ y := by
          rw [map_zpow]; exact hk
        have h1 := hmk _ _ hk'
        have : y = x ^ k * ((x ^ k)⁻¹ * y) := by group
        rw [this]
        exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers x) k)) (mem_sup_right h1)
      have htop := frattini_nongenerating hsup
      apply hnab
      intro a b
      have ha : a ∈ zpowers x := htop ▸ mem_top a
      have hb : b ∈ zpowers x := htop ▸ mem_top b
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      simp only
      rw [← zpow_add, ← zpow_add, add_comm]
    · norm_num
    ·
      exfalso
      have hΦ1 : Φ = ⊥ := by
        rw [← Subgroup.card_eq_one]
        omega
      exact hcomm_of (fun a b => mul_comm a b) hΦ1
  by_cases hDΦ : D ≤ Φ
  · exact Or.inl hDΦ
  right
  set L := D.map (QuotientGroup.mk' Φ) with hLdef
  by_cases hLtop : L = ⊤
  · refine frattini_nongenerating (eq_top_iff.mpr fun y _ => ?_)
    obtain ⟨d, hd, hdy⟩ : QuotientGroup.mk' Φ y ∈ L := hLtop ▸ mem_top _
    have h1 := hmk _ _ hdy
    have : y = d * (d⁻¹ * y) := by group
    rw [this]
    exact mul_mem (mem_sup_left hd) (mem_sup_right h1)
  exfalso
  have hL1 : L ≠ ⊥ := by
    intro h
    apply hDΦ
    intro d hd
    have : QuotientGroup.mk' Φ d ∈ L := ⟨d, hd, rfl⟩
    rw [h, mem_bot] at this
    exact (QuotientGroup.eq_one_iff d).mp this
  have hL3 : Nat.card L = 3 := by
    have hdvd : Nat.card L ∣ 9 := hV ▸ L.card_subgroup_dvd_card
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at hdvd
    obtain ⟨i, hi, hLi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hLi)) hL1
    · simpa using hLi
    · exact absurd (Subgroup.eq_top_of_card_eq L (by rw [hLi, hV]; norm_num)) hLtop
  set σ := quotientAutomorphism Φ f
  have hσ : ∀ y : P, σ (QuotientGroup.mk' Φ y) = QuotientGroup.mk' Φ (f y) :=
    fun y => quotientEquivalence_apply Φ f y
  have hσL : ∀ l ∈ L, σ l ∈ L := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hσ]
    exact ⟨f d, hD d hd, rfl⟩
  have hσ8 : σ ^ 8 = 1 := by rw [← map_pow, hf8, map_one]
  have hσ2 := sq_eq_one_of_line hpow hV hL3 σ hσL hσ8
  have hker : f ^ 2 ∈ (quotientAutomorphism Φ).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hσ2
  obtain ⟨k, hk⟩ := frattini_automorphism_kernel_isPGroup 3 hP ⟨_, hker⟩
  have hk' : (f ^ 2) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h4 : (f ^ 2) ^ 2 ^ 2 = 1 := by rw [← pow_mul, show 2 * 2 ^ 2 = 8 from rfl, hf8]
  have hdvd : orderOf (f ^ 2) ∣ Nat.gcd (2 ^ 2) (3 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h4) (orderOf_dvd_of_pow_eq_one hk')
  rw [(Nat.Coprime.pow 2 k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact hf4 (by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hdvd, one_pow])

theorem u33_local {L : Type} [Group L] [Finite L]
    (hL : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsUThreeThree L) (U : Sylow 3 L) :
    Nat.card (U : Subgroup L) = 27 ∧ ¬ (∀ a ∈ (U : Subgroup L), ∀ b ∈ (U : Subgroup L),
      a * b = b * a) ∧
    (∀ g : L, (∀ u ∈ (U : Subgroup L), g * u = u * g) → g ∈ (U : Subgroup L)) ∧
    ∃ j ∈ normalizer ((U : Subgroup L) : Set L), j ^ 8 = 1 ∧ j ^ 4 ∉ (U : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcardL, hZ⟩ := CFSG.AGLEmbeddingD2.McLaughlin.u33_simple_card_center hL
  obtain ⟨d, ⟨q, hq3, hdq⟩, he⟩ := hL
  have hqp : q.p = 3 := by
    have h := TauCeti.PrimePower.card_def q
    rw [hq3] at h
    have := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp
      ⟨q.p ^ (q.exponent - 1), by
        rw [h, ← pow_succ', Nat.sub_add_cancel q.exponent_pos]⟩
    exact this
  have hqe : q.exponent = 1 := by
    have h := TauCeti.PrimePower.card_def q
    rw [hq3, hqp] at h
    exact (Nat.pow_eq_self_iff (by norm_num)).mp h.symm
  have hfe : d.1.fieldExponent = 1 := by rw [hdq, TauCeti.LieTypeIndex.fieldExponent_twistedA, hqe]
  have hd : CFSG.AGLEmbedding.IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  obtain ⟨hcU, hcomm, -, -⟩ :=
    CFSG.AGLEmbedding.kFactUnitarySylowStructure L 3 d (by norm_num) hd he U
  rw [hfe] at hcU
  have hU27 : Nat.card (U : Subgroup L) = 27 := by rw [hcU]; norm_num
  have hC : ∀ g : L, (∀ u ∈ (U : Subgroup L), g * u = u * g) → g ∈ (U : Subgroup L) := by
    intro g hg
    obtain ⟨u, hu, hgu⟩ := CFSG.AGLEmbedding.kFactUnitaryUnipotentCentralizer L 3 d hd he U
      (MulAut.conj g) fun v hv => by
        rw [MulAut.conj_apply, hg v hv, mul_inv_cancel_right]
    have hZg : u⁻¹ * g ∈ center L := by
      rw [mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut L => φ y) hgu
      simp only [MulAut.conj_apply] at h1
      symm
      calc (u⁻¹ * g) * y = u⁻¹ * (g * y * g⁻¹) * g := by group
        _ = u⁻¹ * (u * y * u⁻¹) * g := by rw [h1]
        _ = y * (u⁻¹ * g) := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at hZg
    rw [← hZg]
    exact hu
  have hnab : ¬ (∀ a ∈ (U : Subgroup L), ∀ b ∈ (U : Subgroup L), a * b = b * a) := by
    intro h
    have hc : ⁅(U : Subgroup L), (U : Subgroup L)⁆ = ⊥ := by
      rw [eq_bot_iff, commutator_le]
      intro a ha b hb
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h a ha b hb
    have hUC : (U : Subgroup L) ≤ centralizer ((U : Subgroup L) : Set L) := fun a ha =>
      mem_centralizer_iff.mpr fun b hb => h b hb a ha
    rw [hc, inf_eq_left.mpr hUC] at hcomm
    have : Nat.card (U : Subgroup L) = 1 := by rw [← hcomm, card_bot]
    omega
  refine ⟨hU27, hnab, hC, ?_⟩
  obtain ⟨-, -, hidx, J, hJ, hNJ⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.unitary_rankOne_data hd he U
  rw [hfe] at hidx
  set N := normalizer ((U : Subgroup L) : Set L) with hNdef
  have hN216 : Nat.card N = 216 := by
    have h := N.card_mul_index
    rw [hidx, hcardL] at h
    norm_num at h
    omega
  obtain ⟨⟨g, hgJ⟩, hgen⟩ := hJ.exists_generator
  have hJN : J ≤ N := hNJ ▸ le_sup_right
  have hgN : g ∈ N := hJN hgJ
  have hJg : ∀ y ∈ J, ∃ k : ℤ, g ^ k = y := fun y hy => by
    obtain ⟨k, hk⟩ := hgen ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨g ^ 27, pow_mem hgN _, ?_, ?_⟩
  · have hdvd := Subgroup.orderOf_dvd_natCard N hgN
    rw [hN216] at hdvd
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  · intro h108
    set U' := (U : Subgroup L).subgroupOf N
    have hUN : (U : Subgroup L) ≤ N := le_normalizer
    have hQ8 : Nat.card (N ⧸ U') = 8 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U'
      rw [hN216, Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv, hU27] at h
      omega
    set gq := QuotientGroup.mk' U' (⟨g, hgN⟩ : N)
    have hgen' : ∀ y : N ⧸ U', y ∈ zpowers gq := by
      intro y
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective U' y
      have hn : (n : L) ∈ (U : Subgroup L) ⊔ J := hNJ ▸ n.2
      rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (hNJ ▸ le_sup_right :
        J ≤ N)] at hn
      obtain ⟨u, hu, y, hy, huy⟩ := Set.mem_mul.mp hn
      obtain ⟨k, rfl⟩ := hJg y hy
      refine ⟨k, ?_⟩
      have hn' : n = ⟨u, hUN hu⟩ * (⟨g, hgN⟩ : N) ^ k := Subtype.ext (by simpa using huy.symm)
      rw [hn', map_mul, map_zpow]
      have : QuotientGroup.mk' U' (⟨u, hUN hu⟩ : N) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hu)
      rw [this, one_mul]
    have hord : orderOf gq = 8 := by
      rw [← hQ8]
      exact orderOf_eq_card_of_forall_mem_zpowers hgen'
    have h1 : gq ^ 108 = 1 := by
      rw [← map_pow]
      refine (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr ?_)
      simpa [← pow_mul] using h108
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    omega

@[expose] def conjOf {X : Type*} [Group X] {B : Subgroup X} {j : X}
    (hj : j ∈ normalizer (B : Set X)) : MulAut B where
  toFun b := ⟨j * b * j⁻¹, (mem_normalizer_iff.mp hj b).mp b.2⟩
  invFun b := ⟨j⁻¹ * b * j, by
    have := (mem_normalizer_iff.mp hj (j⁻¹ * b * j)).mpr (by simpa [mul_assoc] using b.2)
    exact this⟩
  left_inv b := Subtype.ext (by simp [mul_assoc])
  right_inv b := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjOf_pow_apply {X : Type*} [Group X] {B : Subgroup X} {j : X}
    (hj : j ∈ normalizer (B : Set X)) (n : ℕ) (b : B) :
    (((conjOf hj) ^ n) b : X) = j ^ n * b * (j ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    show j * (((conjOf hj) ^ n) b : X) * j⁻¹ = _
    rw [ih, pow_succ']
    group

end InnerQ.KFC1

open CFSG.RankThree.PartOne.Census3 in
theorem kFactU33SylowIrr : KFactU33SylowIrr := by
  intro X _ _ K hq B hBK hBp hidx D hDB hDN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, -, hq3, hv, he⟩ := hq
  have hL : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsUThreeThree K :=
    ⟨⟨_, hv⟩, ⟨q, hq3, rfl⟩, he⟩
  have hBp' : IsPGroup 3 (B.subgroupOf K) := hBp.comap_subtype
  have hidx' : ¬ 3 ∣ (B.subgroupOf K).index := by rw [relIndex] at hidx; exact hidx
  set U : Sylow 3 K := hBp'.toSylow hidx' with hUdef
  have hmemU : ∀ k : K, k ∈ (U : Subgroup K) ↔ (k : X) ∈ B := fun k => by
    rw [hUdef, IsPGroup.toSylow_coe, mem_subgroupOf]
  obtain ⟨h27, hnab, hC, j, hjN, hj8, hj4⟩ := InnerQ.KFC1.u33_local hL U
  have hUB : (U : Subgroup K).map K.subtype = B := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hmemU k).mp hk
    · intro hy
      exact ⟨⟨y, hBK hy⟩, (hmemU _).mpr hy, rfl⟩
  have hjB : (j : X) ∈ normalizer (B : Set X) := by
    have := CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.KFC1.coe_mem_normalizer_map hjN
    rwa [hUB] at this
  set f := InnerQ.KFC1.conjOf hjB
  have hcardB : Nat.card B = 27 := by
    rw [← hUB, card_map_of_injective K.subtype_injective, h27]
  have hnabB : ¬ ∀ a b : B, a * b = b * a := by
    intro h
    apply hnab
    intro a ha b hb
    have := h ⟨a, (hmemU a).mp ha⟩ ⟨b, (hmemU b).mp hb⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hf8 : f ^ 8 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have hj8' : (j : X) ^ 8 = 1 := by rw [← coe_pow, hj8, coe_one]
    rw [InnerQ.KFC1.conjOf_pow_apply, hj8']
    simp
  have hf4 : f ^ 4 ≠ 1 := by
    intro h
    apply hj4
    apply hC
    intro u hu
    have h1 := congrArg (fun φ : MulAut B => ((φ ⟨u, (hmemU u).mp hu⟩ : B) : X)) h
    simp only [f, InnerQ.KFC1.conjOf_pow_apply, MulAut.one_apply] at h1
    apply Subtype.ext
    simp only [coe_mul, coe_pow]
    calc (j : X) ^ 4 * u = (j : X) ^ 4 * u * ((j : X) ^ 4)⁻¹ * (j : X) ^ 4 := by group
      _ = u * (j : X) ^ 4 := by rw [h1]
  have hfD : ∀ d ∈ D.subgroupOf B, f d ∈ D.subgroupOf B := by
    intro d hd
    rw [mem_subgroupOf] at hd ⊢
    have hjD : (j : X) ∈ normalizer (D : Set X) := hDN ⟨j.2, hjB⟩
    exact (mem_normalizer_iff.mp hjD d).mp hd
  rcases InnerQ.KFC1.le_frattini_or_eq_top hBp hcardB hnabB f hf8 hf4 (D.subgroupOf B) hfD with
    h | h
  · left
    intro d hd
    exact ⟨⟨d, hDB hd⟩, h (mem_subgroupOf.mpr hd), rfl⟩
  · right
    refine le_antisymm hDB fun b hb => ?_
    have : (⟨b, hb⟩ : B) ∈ D.subgroupOf B := h ▸ mem_top _
    exact mem_subgroupOf.mp this

end CFSG.LocalAnalysis.RankThreeTheoremC
