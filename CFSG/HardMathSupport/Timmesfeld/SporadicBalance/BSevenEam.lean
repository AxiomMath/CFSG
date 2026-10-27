module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

section Abstract

private theorem mem_of_index_eq_two_of_odd_orderOf {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.index = 2) {g : G} (hg : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨m, hm⟩ := hg
  have h : (g ^ (m + 1)) ^ 2 = g := by
    rw [← pow_mul, show (m + 1) * 2 = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  exact h ▸ Subgroup.sq_mem_of_index_two hH _

private theorem orderOf_eq_six {G : Type*} [Monoid G] {g : G} (h6 : g ^ 6 = 1) (h2 : g ^ 2 ≠ 1)
    (h3 : g ^ 3 ≠ 1) : orderOf g = 6 := by
  have hd : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have h2' : ¬ orderOf g ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.1 h)
  have h3' : ¬ orderOf g ∣ 3 := fun h => h3 (orderOf_dvd_iff_pow_eq_one.1 h)
  have hle : orderOf g ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  obtain ⟨n, hn⟩ : ∃ n, orderOf g = n := ⟨_, rfl⟩
  rw [hn] at hd h2' h3' hle ⊢
  interval_cases n <;> omega

private def quotHom {G Q : Type*} [Group G] [Group Q] {Z H : Subgroup G} [Z.Normal]
    (φ : H ⧸ Z.subgroupOf H ≃* Q) : H →* Q :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf H))

private theorem quotHom_apply {G Q : Type*} [Group G] [Group Q] {Z H : Subgroup G} [Z.Normal]
    (φ : H ⧸ Z.subgroupOf H ≃* Q) (u : H) : quotHom φ u = φ (u : H ⧸ Z.subgroupOf H) :=
  rfl

private theorem quotHom_pow_eq_one_iff {G Q : Type*} [Group G] [Group Q] {Z H : Subgroup G}
    [Z.Normal] (φ : H ⧸ Z.subgroupOf H ≃* Q) (u : H) (n : ℕ) :
    quotHom φ u ^ n = 1 ↔ (u : G) ^ n ∈ Z := by
  rw [← map_pow, quotHom_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.coe_pow]

private theorem quotHom_eq_one_iff {G Q : Type*} [Group G] [Group Q] {Z H : Subgroup G}
    [Z.Normal] (φ : H ⧸ Z.subgroupOf H ≃* Q) (u : H) : quotHom φ u = 1 ↔ (u : G) ∈ Z := by
  simpa using quotHom_pow_eq_one_iff φ u 1

private theorem orderOf_quotHom {G Q : Type*} [Group G] [Group Q] {Z H : Subgroup G} [Z.Normal]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZ2 : Nat.card Z = 2) (φ : H ⧸ Z.subgroupOf H ≃* Q)
    {t : H} (ht : orderOf (t : G) = p) : orderOf (quotHom φ t) = p := by
  have hd : orderOf (quotHom φ t) ∣ p := by
    have := orderOf_map_dvd (quotHom φ) t
    rwa [← Subgroup.orderOf_coe t, ht] at this
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · refine absurd ((quotHom_eq_one_iff φ t).1 (orderOf_eq_one_iff.1 h)) fun htZ => hp2 ?_
    have := Z.orderOf_dvd_natCard htZ
    rw [ht, hZ2] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  · exact h

private theorem exists_mem_centralizer_lift {G Q : Type*} [Group G] [Finite G] [Group Q] {p : ℕ}
    (hp : p.Prime) {M : Subgroup G} [M.Normal] (hcop : Nat.Coprime p (Nat.card M))
    (φ : G ⧸ M ≃* Q) {t : G} (ht : orderOf t = p) {g : Q}
    (hg : g ∈ Subgroup.centralizer ({φ (t : G ⧸ M)} : Set Q)) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), φ (c : G ⧸ M) = g := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p (Subgroup.zpowers t)) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])⟩
  have hcent := CFSG.centralizer_map_quotient_eq_map_centralizer p (Subgroup.zpowers t) M
    inferInstance hcop
  simp only [MonoidHom.map_zpowers] at hcent
  simp only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hcent
  obtain ⟨g₀, rfl⟩ := φ.surjective g
  have h1 : g₀ ∈ Subgroup.centralizer ({QuotientGroup.mk' M t} : Set (G ⧸ M)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    apply φ.injective
    simpa only [map_mul, QuotientGroup.mk'_apply] using hg
  rw [hcent] at h1
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 h1
  exact ⟨c, hc, by rw [← hcg]; rfl⟩

variable {Y R : Type*} [Group Y] [Finite Y] [Group R] {p : ℕ} {Z Y' : Subgroup Y} [Z.Normal]

theorem eam_inf_le_center (hp : p.Prime) (hp2 : p ≠ 2) (hZc : Z ≤ Subgroup.center Y)
    (hZ2 : Nat.card Z = 2) (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ s : R, orderOf s = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set R)) = ⊥)
    {x : Y} (hx : orderOf x = p) {K : Subgroup Y} (hK : K ≤ Subgroup.centralizer ({x} : Set Y))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set Y), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKp : ¬ p ∣ Nat.card K) : ∀ k ∈ K, k ∈ Y' → k ∈ Z := by
  have hxY' : x ∈ Y' := mem_of_index_eq_two_of_odd_orderOf hY' (hx ▸ hp.odd_of_ne_two hp2)
  obtain ⟨x', rfl⟩ : ∃ x' : Y', (x' : Y) = x := ⟨⟨x, hxY'⟩, rfl⟩
  have hcop : Nat.Coprime p (Nat.card (Z.subgroupOf Y')) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY').toEquiv, hZ2]
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hs : orderOf (quotHom φ x') = p := orderOf_quotHom hp hp2 hZ2 φ hx
  have hlift : ∀ g ∈ Subgroup.centralizer ({quotHom φ x'} : Set R),
      ∃ c : Y', (c : Y) ∈ Subgroup.centralizer ({(x' : Y)} : Set Y) ∧ quotHom φ c = g := by
    intro g hg
    obtain ⟨c, hc, hcg⟩ := exists_mem_centralizer_lift hp hcop φ
      (by rw [← Subgroup.orderOf_coe]; exact hx) hg
    refine ⟨c, ?_, hcg⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc
  set S : Subgroup R := (K.subgroupOf Y').map (quotHom φ)
  have hSC : S ≤ Subgroup.centralizer ({quotHom φ x'} : Set R) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (quotHom φ) (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hK ha)))
  have hSn : ∀ g ∈ Subgroup.centralizer ({quotHom φ x'} : Set R), ∀ r ∈ S, g * r * g⁻¹ ∈ S := by
    intro g hg r hr
    obtain ⟨c, hc, rfl⟩ := hlift g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hr
    refine Subgroup.mem_map.2 ⟨c * a * c⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hKn _ hc _ ha
  have hScop : Nat.Coprime p (Nat.card S) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hKp (hdvd.trans ?_)
    refine (Subgroup.card_map_dvd (K.subgroupOf Y') (quotHom φ)).trans ?_
    rw [← Subgroup.card_map_of_injective (K := K.subgroupOf Y') (f := Y'.subtype)
      Subtype.val_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hSbot := le_GLAPPrimeCoreOf_of_normal hSC hSn hScop
  rw [hR _ hs] at hSbot
  intro k hk hkY'
  have hmem : quotHom φ ⟨k, hkY'⟩ ∈ S :=
    Subgroup.mem_map_of_mem (quotHom φ) (Subgroup.mem_subgroupOf.2 hk)
  exact (quotHom_eq_one_iff φ _).1 (Subgroup.mem_bot.1 (hSbot hmem))

theorem eam_odd_eq_bot (hp : p.Prime) (hp2 : p ≠ 2) (hZc : Z ≤ Subgroup.center Y)
    (hZ2 : Nat.card Z = 2) (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ s : R, orderOf s = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set R)) = ⊥)
    {x : Y} (hx : orderOf x = p) {K : Subgroup Y} (hK : K ≤ Subgroup.centralizer ({x} : Set Y))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set Y), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (hKp : ¬ p ∣ Nat.card K) : K = ⊥ := by
  have ha := eam_inf_le_center hp hp2 hZc hZ2 hY' hZY' φ hR hx hK hKn hKp
  have hKZ : K ≤ Z := fun k hk => ha k hk (mem_of_index_eq_two_of_odd_orderOf hY'
    (hodd.of_dvd_nat (K.orderOf_dvd_natCard hk)))
  have hd : Nat.card K ∣ 2 := hZ2 ▸ Subgroup.card_dvd_of_le hKZ
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact Subgroup.card_eq_one.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem eam_le_center (hp : p.Prime) (hp2 : p ≠ 2) (hZc : Z ≤ Subgroup.center Y)
    (hZ2 : Nat.card Z = 2) (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ s : R, orderOf s = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set R)) = ⊥)
    (hR6 : ∀ s : R, orderOf s = p → ∀ r ∈ Subgroup.centralizer ({s} : Set R), orderOf r ≠ 6)
    {x : Y} (hx : orderOf x = p) {w y : Y} (hwx : w ∈ Subgroup.centralizer ({x} : Set Y))
    (hyx : y ∈ Subgroup.centralizer ({x} : Set Y)) (hw6 : w ^ 6 = 1) (hw2 : w ^ 2 ∉ Z)
    (hw3 : w ^ 3 ∉ Z) (hwy : w ^ 3 * y * (w ^ 3)⁻¹ * y⁻¹ ∉ Z)
    {K : Subgroup Y} (hK : K ≤ Subgroup.centralizer ({x} : Set Y))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set Y), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKp : ¬ p ∣ Nat.card K) : K ≤ Z := by
  have ha := eam_inf_le_center hp hp2 hZc hZ2 hY' hZY' φ hR hx hK hKn hKp
  have hxY' : x ∈ Y' := mem_of_index_eq_two_of_odd_orderOf hY' (hx ▸ hp.odd_of_ne_two hp2)
  obtain ⟨x', rfl⟩ : ∃ x' : Y', (x' : Y) = x := ⟨⟨x, hxY'⟩, rfl⟩
  have hs : orderOf (quotHom φ x') = p := orderOf_quotHom hp hp2 hZ2 φ hx
  have L6 : ∀ u : Y', (u : Y) ∈ Subgroup.centralizer ({(x' : Y)} : Set Y) → (u : Y) ^ 6 ∈ Z →
      (u : Y) ^ 2 ∉ Z → (u : Y) ^ 3 ∉ Z → False := by
    intro u huc h6 h2 h3
    refine hR6 _ hs (quotHom φ u) ?_ (orderOf_eq_six ?_ ?_ ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg (quotHom φ) (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 huc))
    · exact (quotHom_pow_eq_one_iff φ u 6).2 h6
    · exact fun h => h2 ((quotHom_pow_eq_one_iff φ u 2).1 h)
    · exact fun h => h3 ((quotHom_pow_eq_one_iff φ u 3).1 h)
  intro k₀ hk₀
  by_contra hk₀Z
  have hk₀Y' : k₀ ∉ Y' := fun h => hk₀Z (ha k₀ hk₀ h)
  set π : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  have hπ : ∀ u : Y, π u = 1 ↔ u ∈ Z := fun u => QuotientGroup.eq_one_iff u
  have hcomm : ∀ g ∈ Subgroup.centralizer ({(x' : Y)} : Set Y), Commute (π g) (π k₀) := by
    intro g hg
    have h1 : g * k₀ * g⁻¹ * k₀⁻¹ ∈ K := K.mul_mem (hKn g hg k₀ hk₀) (K.inv_mem hk₀)
    have h2 : g * k₀ * g⁻¹ * k₀⁻¹ ∈ Y' := by
      simp only [Subgroup.mul_mem_iff_of_index_two hY', inv_mem_iff]
      tauto
    have h3 := (hπ _).2 (ha _ h1 h2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
    exact h3
  have hk₀sq : π k₀ ^ 2 = 1 := by
    rw [← map_pow, hπ]
    exact ha _ (K.pow_mem hk₀ 2) (Subgroup.sq_mem_of_index_two hY' k₀)
  by_cases hwY' : w ∈ Y'
  · exact L6 ⟨w, hwY'⟩ hwx (hw6 ▸ Z.one_mem) hw2 hw3
  have hu : k₀ * w ∈ Y' := (Subgroup.mul_mem_iff_of_index_two hY').2 (iff_of_false hk₀Y' hwY')
  have huc : k₀ * w ∈ Subgroup.centralizer ({(x' : Y)} : Set Y) :=
    Subgroup.mul_mem _ (hK hk₀) hwx
  have hpow : ∀ n : ℕ, π ((k₀ * w) ^ n) = π k₀ ^ n * π w ^ n := fun n => by
    rw [map_pow, map_mul, (hcomm w hwx).symm.mul_pow]
  have h6 : (k₀ * w) ^ 6 ∈ Z := by
    rw [← hπ, hpow, show π k₀ ^ 6 = (π k₀ ^ 2) ^ 3 by rw [← pow_mul], hk₀sq, one_pow, one_mul,
      ← map_pow, hw6, map_one]
  have h2 : (k₀ * w) ^ 2 ∉ Z := by
    rw [← hπ, hpow, hk₀sq, one_mul, ← map_pow, hπ]
    exact hw2
  by_cases h3 : (k₀ * w) ^ 3 ∈ Z
  · rw [← hπ, hpow, show π k₀ ^ 3 = π k₀ by rw [pow_succ, hk₀sq, one_mul]] at h3
    have hy := hcomm y hyx
    rw [eq_inv_of_mul_eq_one_left h3] at hy
    have hy3 : Commute (π (w ^ 3)) (π y) := by
      rw [map_pow]
      exact (Commute.inv_right_iff.1 hy).symm
    apply hwy
    rw [← hπ, map_mul, map_mul, map_mul, map_inv, map_inv, hy3.eq, mul_inv_cancel_right,
      mul_inv_cancel]
  · exact L6 ⟨k₀ * w, hu⟩ huc h6 h2 h3

end Abstract



end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
