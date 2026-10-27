module

public import CFSG.GH74.E2.OuterL33
public import CFSG.GH74.E2.RankFibre

public section

namespace CFSG.GH74.E2

open Subgroup Pointwise




open Subgroup

theorem q8_sq_mem {S : Type} [Group S] (Q : Subgroup S) (eQ : ↥Q ≃* QuaternionGroup 2) {t : S}
    (htQ : t ∈ Q) (ht1 : t ≠ 1) (ht2 : t * t = 1) : ∀ q ∈ Q, q * q = 1 ∨ q * q = t := by
  intro q hq
  have hta : eQ ⟨t, htQ⟩ = QuaternionGroup.a (2 : ℕ) := by
    have ht : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
    exact eD_t_eq_a htQ ht (m := 2) (Or.inl rfl) eQ
  have hsq : ∀ x : QuaternionGroup 2, x * x = 1 ∨ x * x = QuaternionGroup.a (2 : ℕ) := by decide
  rcases hsq (eQ ⟨q, hq⟩) with h | h
  · left
    have : (⟨q, hq⟩ : ↥Q) * ⟨q, hq⟩ = 1 := eQ.injective (by rw [map_mul, h, map_one])
    simpa using congrArg Subtype.val this
  · right
    have : (⟨q, hq⟩ : ↥Q) * ⟨q, hq⟩ = ⟨t, htQ⟩ := eQ.injective (by rw [map_mul, h, hta])
    simpa using congrArg Subtype.val this

theorem rank_quot_ge_three_of_inner {S : Type} [Group S] [Finite S]
    {Q TK : Subgroup S} [hTKn : TK.Normal] (eQ : ↥Q ≃* QuaternionGroup 2) {t : S}
    (htQ : t ∈ Q) (ht1 : t ≠ 1) (ht2 : t * t = 1) (htc : ∀ s : S, s * t = t * s)
    (hcomm : ∀ a ∈ TK, ∀ b ∈ Q, a * b = b * a) (hdisj : TK ⊓ Q = ⊥)
    (hcard : Nat.card S = 2 * (Nat.card TK * Nat.card Q)) {e : S} (heQ : ∀ y ∈ Q, e * y = y * e)
    (heM : e ∉ TK ⊔ Q) : 3 ≤ Group.rank (S ⧸ TK) := by
  classical
  set M₀ : Subgroup S := TK ⊔ Q with hM₀
  have hM0card : Nat.card ↥M₀ = Nat.card TK * Nat.card Q := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (prodSupEquiv TK Q hcomm hdisj).toEquiv).symm
  have hpos : 0 < Nat.card TK * Nat.card Q := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hidx : M₀.index = 2 := by
    have h1 := Subgroup.index_mul_card M₀
    rw [hM0card, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  have ht : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hQ8 : Nat.card Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have htz : ∀ m : ℤ, ∀ s : S, s * t ^ m = t ^ m * s := fun m s =>
    ((Commute.zpow_right (show Commute s t from htc s) m)).eq
  have hZn : (Subgroup.zpowers t).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * t ^ m * g⁻¹ = t ^ m := by
      rw [mul_inv_eq_iff_eq_mul]
      exact htz m g
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) m
  set W : Subgroup S := TK ⊔ Subgroup.zpowers t with hW
  have hWn : W.Normal := Subgroup.sup_normal TK (Subgroup.zpowers t)
  have hzpow : ∀ x ∈ Subgroup.zpowers t, x = 1 ∨ x = t := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h2 : t ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact ht2
    obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 2 * k ∨ m = 2 * k + 1 := by
      rcases Int.even_or_odd' m with ⟨k, hk | hk⟩
      · exact ⟨k, Or.inl hk⟩
      · exact ⟨k, Or.inr hk⟩
    rcases hk with hk | hk
    · left
      rw [hk, zpow_mul, h2, one_zpow]
    · right
      rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  have htTK : t ∉ TK := by
    intro h
    have : t ∈ TK ⊓ Q := ⟨h, htQ⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact ht1 this
  have hdisjW : TK ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxZ⟩
    rcases hzpow x hxZ with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hxK) htTK
  have hcommW : ∀ a ∈ TK, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
    intro a _ b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact htz m a
  have hWcard : Nat.card ↥W = Nat.card TK * 2 := by
    have : Nat.card ↥W = Nat.card TK * Nat.card (Subgroup.zpowers t) := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (prodSupEquiv TK (Subgroup.zpowers t) hcommW hdisjW).toEquiv).symm
    rw [this, Nat.card_zpowers, ht]
  have hWindex : W.index = 8 := by
    have h1 := Subgroup.index_mul_card W
    rw [hWcard, hcard, hQ8] at h1
    have hTKpos : 0 < Nat.card TK := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < Nat.card TK * 2) ?_
    rw [h1]
    ring
  have hQcen : ∀ y ∈ Q, (∀ q ∈ Q, y * q = q * y) → y = 1 ∨ y = t := q8_center_eq eQ htQ ht2 ht1
  have hsqQ := q8_sq_mem Q eQ htQ ht1 ht2
  have hmemW1 : ∀ k ∈ TK, k ∈ W := fun k hk => Subgroup.mem_sup_left hk
  have htW : t ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hsqW : ∀ q ∈ Q, q * q ∈ W := by
    intro q hq
    rcases hsqQ q hq with h | h
    · rw [h]; exact W.one_mem
    · rw [h]; exact htW
  have he2 : e * e ∈ W := by
    have h2 : e * e ∈ M₀ := Subgroup.mul_self_mem_of_index_two hidx e
    obtain ⟨k₁, hk₁, q₁, hq₁, hkq⟩ := (mem_sup_iff_of_commute hcomm).1 h2
    have hq₁c : ∀ q ∈ Q, q₁ * q = q * q₁ := by
      intro q hq
      have hee : e * e * q = q * (e * e) := by
        rw [mul_assoc, heQ q hq, ← mul_assoc, heQ q hq, mul_assoc]
      have h3 : q₁ = k₁⁻¹ * (e * e) := by
        rw [← hkq]; group
      have hk1q : k₁⁻¹ * q = q * k₁⁻¹ := hcomm _ (TK.inv_mem hk₁) q hq
      rw [h3]
      calc k₁⁻¹ * (e * e) * q = k₁⁻¹ * ((e * e) * q) := by rw [mul_assoc]
        _ = k₁⁻¹ * (q * (e * e)) := by rw [hee]
        _ = (k₁⁻¹ * q) * (e * e) := by rw [← mul_assoc]
        _ = (q * k₁⁻¹) * (e * e) := by rw [hk1q]
        _ = q * (k₁⁻¹ * (e * e)) := by rw [mul_assoc]
    have hq₁t : q₁ = 1 ∨ q₁ = t := hQcen q₁ hq₁ hq₁c
    rw [← hkq]
    refine W.mul_mem (hmemW1 k₁ hk₁) ?_
    rcases hq₁t with h | h
    · rw [h]; exact W.one_mem
    · rw [h]; exact htW
  have hsq_all : ∀ x : S, x * x ∈ W := by
    intro x
    by_cases hx : x ∈ M₀
    · obtain ⟨k, hk, q, hq, rfl⟩ := (mem_sup_iff_of_commute hcomm).1 hx
      have h1 : k * q * (k * q) = (k * k) * (q * q) := by
        calc k * q * (k * q) = k * (q * k) * q := by group
          _ = k * (k * q) * q := by rw [← hcomm k hk q hq]
          _ = (k * k) * (q * q) := by group
      rw [h1]
      exact W.mul_mem (hmemW1 _ (TK.mul_mem hk hk)) (hsqW q hq)
    · have hxe : x * e⁻¹ ∈ M₀ := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        constructor
        · intro h; exact absurd h hx
        · intro h; exact absurd (M₀.inv_mem_iff.1 h) heM
      obtain ⟨k, hk, q, hq, hkq⟩ := (mem_sup_iff_of_commute hcomm).1 hxe
      have hxeq : x = k * q * e := by
        rw [hkq]; group
      have hk' : e * k * e⁻¹ ∈ TK := hTKn.conj_mem k hk e
      have hck' : e * k * e⁻¹ * q = q * (e * k * e⁻¹) := hcomm _ hk' q hq
      have hex : e * k = (e * k * e⁻¹) * e := by group
      have h1 : x * x = (k * (e * k * e⁻¹)) * (q * q) * (e * e) := by
        rw [hxeq]
        calc k * q * e * (k * q * e) = k * q * (e * k) * q * e := by group
          _ = k * q * ((e * k * e⁻¹) * e) * q * e := by rw [← hex]
          _ = k * (q * (e * k * e⁻¹)) * (e * q) * e := by group
          _ = k * ((e * k * e⁻¹) * q) * (q * e) * e := by rw [← hck', heQ q hq]
          _ = (k * (e * k * e⁻¹)) * (q * q) * (e * e) := by group
      rw [h1]
      exact W.mul_mem (W.mul_mem (hmemW1 _ (TK.mul_mem hk hk')) (hsqW q hq)) he2
  have hY2 : ∀ y : S ⧸ W, y ^ 2 = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
    exact hsq_all x
  have hcommY : IsMulCommutative (S ⧸ W) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    have h : ∀ y : S ⧸ W, y = y⁻¹ := fun y =>
      (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hY2 y)).symm
    calc a * b = (a * b)⁻¹ := h _
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [← h a, ← h b]
  have hrank : Group.rank (S ⧸ W) = 3 := by
    have h1 := two_pow_rank_eq_card_of_exponent_two hY2
    have h2 : Nat.card (S ⧸ W) = 8 := hWindex
    rw [h2] at h1
    have : (2 : ℕ) ^ Group.rank (S ⧸ W) = 2 ^ 3 := by rw [h1]; norm_num
    exact Nat.pow_right_injective le_rfl this
  let π : S ⧸ TK →* S ⧸ W :=
    QuotientGroup.map TK W (MonoidHom.id S) (fun x hx => hmemW1 x hx)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have := Group.rank_le_of_surjective π hπ
  omega




theorem exists_conj_into_sylow {C : Type} [Group C] [Finite C] (S : Sylow 2 C) {x : C}
    (hx2 : x * x = 1) : ∃ g : C, g * x * g⁻¹ ∈ (S : Subgroup C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x ∣ 2 ^ 1 := by
    simpa [sq] using orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [sq]; exact hx2)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S' S
  refine ⟨g, ?_⟩
  have hx' : x ∈ (S' : Subgroup C) := hS' (Subgroup.mem_zpowers x)
  have h1 : (MulAut.conj g) • x ∈ (MulAut.conj g) • (S' : Subgroup C) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx'
  have h2 : ((g • S' : Sylow 2 C) : Subgroup C) = (MulAut.conj g) • (S' : Subgroup C) := rfl
  rw [hg] at h2
  rw [h2]
  simpa using h1


theorem not_inner_on_Q_of_outer
    {C : Type} [Group C] [Finite C]
    (hgen : Gen4 C) {Q K : Subgroup C}
    (hloc : LocalK C Q K) (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2)) {t : C} (ht : orderOf t = 2)
    (htQ : t ∈ Q) (htc : ∀ g : C, g * t = t * g) (hcen : Subgroup.center ↥K = ⊥)
    (hT : SD16Tables ↥K) (hOut2 : Nat.card (MulAut ↥K) = 2 * Nat.card ↥K)
    {c : C} (hc3 : orderOf c = 3) (hcK : ∀ k ∈ K, c * k = k * c)
    (hD24 : Nat.card ↥(Subgroup.centralizer (K : Set C)) = 24)
    {u : C} (hu2 : u ^ 2 = 1) (huout : ¬ ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹) :
    ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹ := by
  classical
  rintro ⟨q₀, hq₀Q, hq₀⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := hloc.K_normal
  have hQn := hloc.Q_normal
  set D : Subgroup C := Subgroup.centralizer (K : Set C) with hD
  obtain ⟨hQD, hDcases⟩ := dt_structure hloc hQ8 hc3 hcK
  obtain ⟨PD⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  obtain ⟨TK⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hPDQ : (PD : Subgroup ↥D).map D.subtype = Q := by
    rcases hDcases PD with ⟨-, h⟩ | ⟨h48, -⟩
    · exact h
    · exact absurd (hD24.symm.trans h48) (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  obtain ⟨SK, hSKdef⟩ : ∃ SK : Subgroup C, SK = (TK : Subgroup ↥K).map K.subtype := ⟨_, rfl⟩
  have hSKK : SK ≤ K := by rw [hSKdef]; exact sylow_map_le K TK
  have hSKp : IsPGroup 2 SK := by rw [hSKdef]; exact sylow_map_isPGroup K TK
  have hSKmax : ∀ P : Subgroup C, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK := fun P hP h1 h2 => by
    rw [hSKdef] at h2 ⊢
    exact sylow_map_max K TK P hP h1 h2
  have hSDD : Q ≤ D := hQD
  have hSDp : IsPGroup 2 Q := hloc.Q_pgroup
  have hSDmax : ∀ P : Subgroup C, IsPGroup 2 P → P ≤ D → Q ≤ P → P = Q := fun P hP h1 h2 => by
    rw [← hPDQ] at h2 ⊢
    exact sylow_map_max D PD P hP h1 h2
  have hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := fun k hk d hd =>
    Subgroup.mem_centralizer_iff.1 hd k hk
  have hdisj : K ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxD⟩
    have hxz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxD y y.2)
    rw [hcen, Subgroup.mem_bot] at hxz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxz
  have hcommS : ∀ a ∈ SK, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    hcomm a (hSKK ha) b (hSDD hb)
  have hdisjS : SK ⊓ Q = ⊥ := le_bot_iff.1 ((inf_le_inf hSKK hSDD).trans hdisj.le)
  have hprod : Nat.card ↥(SK ⊔ Q) = Nat.card SK * Nat.card Q := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (prodSupEquiv SK Q hcommS hdisjS).toEquiv).symm
  have hS12 : IsPGroup 2 ↥(SK ⊔ Q) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hSKp
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hSDp
    exact IsPGroup.of_card (n := a + b) (by rw [hprod, ha, hb, pow_add])
  obtain ⟨S, hS⟩ := hS12.exists_le_sylow
  have hout : ¬ ∀ g : C, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹ := fun h => by
    obtain ⟨k, hk, hk2⟩ := h u
    exact huout ⟨k, hk, hk2⟩
  have hcard := card_cen_outer (K := K) hcen hOut2 hout
  have hS1card := card_sylow_outer (K := K) (D := D) (SD := Q) hcard hSKK hSKp hSKmax hSDD hSDp
    hSDmax S.isPGroup' (fun P hP h => S.is_maximal' hP h)
  set S₁ : Subgroup C := (S : Subgroup C) with hS₁def
  have hSKS : SK ≤ S₁ := le_sup_left.trans hS
  have hQS : Q ≤ S₁ := le_sup_right.trans hS
  obtain ⟨g, hgu⟩ := exists_conj_into_sylow S (x := u) (by simpa [sq] using hu2)
  set u' : C := g * u * g⁻¹ with hu'
  have hu'2 : u' * u' = 1 := by
    calc u' * u' = g * (u * u) * g⁻¹ := by rw [hu']; group
      _ = 1 := by rw [show u * u = 1 by simpa [sq] using hu2]; group
  have hu'out : ¬ ∃ k ∈ K, ∀ x ∈ K, u' * x * u'⁻¹ = k * x * k⁻¹ := by
    rintro ⟨k, hk, hk2⟩
    apply huout
    refine ⟨g⁻¹ * k * g, by simpa using hKn.conj_mem k hk g⁻¹, fun x hx => ?_⟩
    have hgx : g * x * g⁻¹ ∈ K := hKn.conj_mem x hx g
    have := hk2 _ hgx
    calc u * x * u⁻¹ = g⁻¹ * (g * u * g⁻¹ * (g * x * g⁻¹) * (g * u * g⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * (k * (g * x * g⁻¹) * k⁻¹) * g := by rw [← hu', this]
      _ = (g⁻¹ * k * g) * x * (g⁻¹ * k * g)⁻¹ := by group
  set q₁ : C := g * q₀ * g⁻¹ with hq₁
  have hq₁Q : q₁ ∈ Q := hQn.conj_mem q₀ hq₀Q g
  have hu'Q : ∀ y ∈ Q, u' * y * u'⁻¹ = q₁ * y * q₁⁻¹ := by
    intro y hy
    have hgy : g⁻¹ * y * g ∈ Q := by simpa using hQn.conj_mem y hy g⁻¹
    have := hq₀ _ hgy
    calc u' * y * u'⁻¹ = g * (u * (g⁻¹ * y * g) * u⁻¹) * g⁻¹ := by rw [hu']; group
      _ = g * (q₀ * (g⁻¹ * y * g) * q₀⁻¹) * g⁻¹ := by rw [this]
      _ = q₁ * y * q₁⁻¹ := by rw [hq₁]; group
  set e : C := q₁⁻¹ * u' with he
  have heS : e ∈ S₁ := S₁.mul_mem (S₁.inv_mem (hQS hq₁Q)) hgu
  have heQ : ∀ y ∈ Q, e * y = y * e := by
    intro y hy
    have h1 := hu'Q y hy
    have h2 : u' * y = (q₁ * y * q₁⁻¹) * u' := by
      rw [← h1]; group
    calc e * y = q₁⁻¹ * (u' * y) := by rw [he]; group
      _ = q₁⁻¹ * ((q₁ * y * q₁⁻¹) * u') := by rw [h2]
      _ = y * (q₁⁻¹ * u') := by group
  have heM : e ∉ SK ⊔ Q := by
    intro hmem
    have hu'mem : u' ∈ SK ⊔ Q := by
      have : u' = q₁ * e := by rw [he]; group
      rw [this]
      exact (SK ⊔ Q).mul_mem (Subgroup.mem_sup_right hq₁Q) hmem
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_commute hcommS).1 hu'mem
    apply hu'out
    refine ⟨a, hSKK ha, fun x hx => ?_⟩
    have hbx : b * x = x * b := (hcomm x hx b (hSDD hb)).symm
    rw [← hab]
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
      _ = a * x * a⁻¹ := by group
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hS₁K : S₁ ⊓ K = SK := hSKmax _ S.isPGroup'.to_inf_left inf_le_right (le_inf hSKS hSKK)
  have hTKn' : (SK.subgroupOf S₁).Normal := by
    have : SK.subgroupOf S₁ = K.subgroupOf S₁ := by
      ext x
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · intro h; exact hSKK h
      · intro h; rw [← hS₁K]; exact ⟨x.2, h⟩
    rw [this]
    exact hKn.subgroupOf S₁
  have hQn' : (Q.subgroupOf S₁).Normal := hQn.subgroupOf S₁
  have hQ8S : Nonempty (↥(Q.subgroupOf S₁) ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hQS).trans hQ8.some⟩
  obtain ⟨eQ⟩ := hQ8S
  have hcardSK : Nat.card ↥(SK.subgroupOf S₁) = Nat.card SK :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSKS).toEquiv
  have hcardQ : Nat.card ↥(Q.subgroupOf S₁) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
  have hcardS : Nat.card ↥S₁ =
      2 * (Nat.card ↥(Q.subgroupOf S₁) * Nat.card ↥(SK.subgroupOf S₁)) := by
    rw [hcardSK, hcardQ, hS1card, mul_comm (Nat.card Q)]
  have hdisj' : SK.subgroupOf S₁ ⊓ Q.subgroupOf S₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : (x : C) ∈ SK ⊓ Q := ⟨hx1, hx2⟩
    rw [hdisjS, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hcomm' : ∀ a ∈ SK.subgroupOf S₁, ∀ b ∈ Q.subgroupOf S₁, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hcommS a ha b hb)
  have htS : t ∈ S₁ := hQS htQ
  let t' : ↥S₁ := ⟨t, htS⟩
  have ht'Q : t' ∈ Q.subgroupOf S₁ := Subgroup.mem_subgroupOf.2 htQ
  have ht1' : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht2' : t' * t' = 1 := Subtype.ext ht2
  have htc' : ∀ s : ↥S₁, s * t' = t' * s := fun s => Subtype.ext (htc s)
  let e' : ↥S₁ := ⟨e, heS⟩
  have heQ' : ∀ y ∈ Q.subgroupOf S₁, e' * y = y * e' := fun y hy =>
    Subtype.ext (heQ y (Subgroup.mem_subgroupOf.1 hy))
  have heM' : e' ∉ SK.subgroupOf S₁ ⊔ Q.subgroupOf S₁ := by
    intro h
    rw [← Subgroup.subgroupOf_sup hSKS hQS] at h
    exact heM (Subgroup.mem_subgroupOf.1 h)
  have hr3 : 3 ≤ Group.rank (↥S₁ ⧸ SK.subgroupOf S₁) :=
    rank_quot_ge_three_of_inner eQ ht'Q ht1' ht2' htc' hcomm' hdisj' (by
      rw [hcardS]; ring) heQ' heM'
  let eK : ↥(SK.subgroupOf S₁) ≃* OuterRank.SD :=
    (Subgroup.subgroupOfEquivOfLe hSKS).trans
      ((MulEquiv.subgroupCongr hSKdef).trans
        (((sylowMapEquiv K TK).symm.trans (hT.sylow TK).some).trans
          (CFSG.Semidihedral.presentationEquivModel 4 (by norm_num))))
  have hidx : (SK.subgroupOf S₁ ⊔ Q.subgroupOf S₁).index = 2 := by
    rw [← Subgroup.subgroupOf_sup hSKS hQS]
    have h1 := Subgroup.index_mul_card ((SK ⊔ Q).subgroupOf S₁)
    have hc1 : Nat.card ↥((SK ⊔ Q).subgroupOf S₁) = Nat.card ↥(SK ⊔ Q) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hSKS hQS)).toEquiv
    rw [hc1, hprod, hS1card] at h1
    have hpos : 0 < Nat.card SK * Nat.card Q := Nat.mul_pos Nat.card_pos Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1])
  have hr3' : 3 ≤ Group.rank (↥S₁ ⧸ Q.subgroupOf S₁) :=
    rank_quot_ge_three (Q.subgroupOf S₁) (SK.subgroupOf S₁) hdisj' eK hidx
  have hrk := rank_add_le_of_disjoint (S := ↥S₁) S.isPGroup' (Q.subgroupOf S₁)
    (SK.subgroupOf S₁) (by rw [inf_comm]; exact hdisj') hcardS
  have h4 : Group.rank ↥S₁ ≤ 4 := by
    have hTop : IsPGroup 2 (⊤ : Subgroup ↥S₁) := S.isPGroup'.of_equiv Subgroup.topEquiv.symm
    have := Gen4.rank_le_four (hgen.subgroup S₁) hTop
    rwa [Group.rank_congr (Subgroup.topEquiv : (⊤ : Subgroup ↥S₁) ≃* ↥S₁)] at this
  omega


end CFSG.GH74.E2
