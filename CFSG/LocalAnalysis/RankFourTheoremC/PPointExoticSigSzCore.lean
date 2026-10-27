module

public import CFSG.RankThree.PartOne.K159.AutSzAbs
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer

open CFSG.RankThree.PartOne.K159.SzAbs Subgroup

variable {K : Type} [Group K] [Finite K]

theorem card_two (hSz : SzSylow K) (V : Sylow 2 K) : Nat.card (V : Subgroup K) = 1024 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [Sylow.card_eq_multiplicity V, hSz.card, factorization_two]
  norm_num

theorem card_normalizer (hSz : SzSylow K) (V : Sylow 2 K) :
    Nat.card (normalizer (V : Set K)) = 31744 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h0 := Sylow.card_eq_index_normalizer V
  have h1 := Subgroup.card_mul_index (normalizer (V : Set K))
  rw [← h0, hSz.card_sylow, hSz.card] at h1
  omega

theorem eq_one_of_smul_eq (hSz : SzSylow K) {g : K} (hg : Nat.Coprime (orderOf g) 31744)
    {V : Sylow 2 K} (h : g • V = V) : g = 1 := by
  have hmem : g ∈ normalizer (V : Set K) := Sylow.smul_eq_iff_mem_normalizer.1 h
  have hdvd : orderOf g ∣ 31744 := by
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [card_normalizer hSz V] at this
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hg hdvd)

theorem mem_smul_iff (g x : K) (V : Sylow 2 K) :
    x ∈ ((g • V : Sylow 2 K) : Subgroup K) ↔ g⁻¹ * x * g ∈ (V : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.conj_apply]

theorem smul_eq_of_mem (hSz : SzSylow K) {g x : K} {V : Sylow 2 K} (hx1 : x ≠ 1)
    (hxV : x ∈ (V : Subgroup K)) (hxg : g⁻¹ * x * g ∈ (V : Subgroup K)) : g • V = V := by
  by_contra hne
  have hx : x ∈ (V : Subgroup K) ⊓ ((g • V : Sylow 2 K) : Subgroup K) :=
    ⟨hxV, (mem_smul_iff g x V).2 hxg⟩
  rw [hSz.ti V (g • V) (Ne.symm hne)] at hx
  exact hx1 (Subgroup.mem_bot.1 hx)

theorem eq_one_of_mem_of_smul_eq (hSz : SzSylow K) {V W : Sylow 2 K} (hWV : W ≠ V) {v : K}
    (hv : v ∈ (V : Subgroup K)) (h : v • W = W) : v = 1 := by
  have h1 : v ∈ normalizer (W : Set K) := Sylow.smul_eq_iff_mem_normalizer.1 h
  have h2' : v ∈ (V : Subgroup K) ⊓ normalizer (W : Set K) := ⟨hv, h1⟩
  rw [IsPGroup.inf_normalizer_sylow V.2 W, hSz.ti V W (Ne.symm hWV)] at h2'
  exact Subgroup.mem_bot.1 h2'

theorem eq_one_of_forall_smul_eq (hSz : SzSylow K) (hsimple : IsSimpleGroup K) {g : K}
    (hall : ∀ W : Sylow 2 K, g • W = W) : g = 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨V⟩ : Nonempty (Sylow 2 K) := inferInstance
  let N : Subgroup K := (MulAction.toPermHom K (Sylow 2 K)).ker
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hgN : g ∈ N := by
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun W => hall W
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [hbot] at hgN
    exact Subgroup.mem_bot.1 hgN
  · exfalso
    have hVn : (V : Subgroup K).Normal := by
      refine ⟨fun x hx k => ?_⟩
      have hk : k ∈ N := htop ▸ Subgroup.mem_top k
      rw [MonoidHom.mem_ker] at hk
      have h1 : k • V = V := by simpa using congrArg (fun π : Equiv.Perm (Sylow 2 K) => π V) hk
      have h2' := Subgroup.mem_normalizer_iff.1 (Sylow.smul_eq_iff_mem_normalizer.1 h1) x
      exact h2'.1 hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V : Subgroup K) with h | h
    · have := card_two hSz V
      rw [h, Subgroup.card_bot] at this
      omega
    · have := card_two hSz V
      rw [h, Subgroup.card_top, hSz.card] at this
      omega

theorem smul_fix {ψ z : K} (hz : z ∈ normalizer ((zpowers ψ : Subgroup K) : Set K))
    {W : Sylow 2 K} (hW : ψ • W = W) : ψ • (z • W) = z • W := by
  have h1 : z⁻¹ * ψ * z ∈ zpowers ψ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hz) ψ).1 (Subgroup.mem_zpowers ψ)
    simpa using this
  have h2 : zpowers ψ ≤ normalizer (W : Set K) :=
    (Subgroup.zpowers_le).2 (Sylow.smul_eq_iff_mem_normalizer.1 hW)
  have h3 : (z⁻¹ * ψ * z) • W = W := Sylow.smul_eq_iff_mem_normalizer.2 (h2 h1)
  calc ψ • (z • W) = (ψ * z) • W := (mul_smul _ _ _).symm
    _ = (z * (z⁻¹ * ψ * z)) • W := by group
    _ = z • ((z⁻¹ * ψ * z) • W) := mul_smul _ _ _
    _ = z • W := by rw [h3]

theorem orderOf_dvd_card_fix (hSz : SzSylow K) {ψ z : K}
    (hz : z ∈ normalizer ((zpowers ψ : Subgroup K) : Set K))
    (hcop : Nat.Coprime (orderOf z) 31744) :
    orderOf z ∣ Nat.card {W : Sylow 2 K // ψ • W = W} := by
  have hfree : ∀ q : ↥(zpowers z), ∀ W : Sylow 2 K, q • W = W → q = 1 := by
    intro q W hq
    have hq' : (q : K) • W = W := hq
    have hord : Nat.Coprime (orderOf (q : K)) 31744 :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_mem_zpowers q.2) hcop
    exact Subtype.ext (eq_one_of_smul_eq hSz hord hq')
  have hY : ∀ q : ↥(zpowers z), ∀ W ∈ {W : Sylow 2 K | ψ • W = W},
      q • W ∈ {W : Sylow 2 K | ψ • W = W} := by
    intro q W hW
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 q.2
    show ψ • ((q : K) • W) = (q : K) • W
    rw [← hk]
    exact smul_fix (zpow_mem hz k) hW
  have := card_dvd_of_free_invariant (Q := ↥(zpowers z)) (X := Sylow 2 K) hfree _ hY
  rwa [Nat.card_zpowers] at this

theorem card_fix_of_orderOf_31 (hSz : SzSylow K) (hsimple : IsSimpleGroup K) {ψ : K}
    (hψ : orderOf ψ = 31) :
    Nat.card {W : Sylow 2 K // ψ • W = W} = 2 ∨ Nat.card {W : Sylow 2 K // ψ • W = W} = 33 := by
  have h31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hG : IsPGroup 31 (zpowers ψ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hψ]; norm_num)
  have hmod := hG.card_modEq_card_fixedPoints (Sylow 2 K)
  have hfix : Nat.card (MulAction.fixedPoints (zpowers ψ) (Sylow 2 K)) =
      Nat.card {W : Sylow 2 K // ψ • W = W} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun W => ?_)
    rw [Subgroup.sylow_mem_fixedPoints_iff, Subgroup.zpowers_le,
      Sylow.smul_eq_iff_mem_normalizer]
  rw [hfix, hSz.card_sylow] at hmod
  have hmod' : (1025 : ℕ) % 31 = Nat.card {W : Sylow 2 K // ψ • W = W} % 31 := hmod
  have hne1025 : Nat.card {W : Sylow 2 K // ψ • W = W} ≠ 1025 := by
    intro h
    have hall : ∀ W : Sylow 2 K, ψ • W = W := by
      intro W
      by_contra hW
      have := Finite.card_subtype_lt (p := fun W : Sylow 2 K => ψ • W = W) (x := W) hW
      rw [hSz.card_sylow] at this
      omega
    have h1 := eq_one_of_forall_smul_eq hSz hsimple hall
    rw [h1, orderOf_one] at hψ
    omega
  have hnt : Nontrivial {W : Sylow 2 K // ψ • W = W} :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨V, hV⟩, ⟨V₁, hV₁⟩, hne⟩ := exists_pair_ne {W : Sylow 2 K // ψ • W = W}
  have hVV₁ : V₁ ≠ V := fun h => hne (Subtype.ext h.symm)
  have hψN : ψ ∈ normalizer (V : Set K) := Sylow.smul_eq_iff_mem_normalizer.1 hV
  have hreg := card_fixed_eq_of_regular (G := K) (Ω := Sylow 2 K) (V : Subgroup K) V
    (fun u hu => Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hu))
    (fun u hu W hW => eq_one_of_mem_of_smul_eq hSz hW hu)
    (by rw [card_two hSz V, hSz.card_sylow])
    ψ (fun u hu => (Subgroup.mem_normalizer_iff.1 hψN u).1 hu) hV V₁ hVV₁ hV₁
  let Csub : Subgroup (V : Subgroup K) :=
    { carrier := {u | ψ * (u : K) * ψ⁻¹ = (u : K)}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ψ * (a : K) * ψ⁻¹ = (a : K) := ha
        have hb' : ψ * (b : K) * ψ⁻¹ = (b : K) := hb
        show ψ * ((a : K) * (b : K)) * ψ⁻¹ = (a : K) * (b : K)
        calc ψ * ((a : K) * (b : K)) * ψ⁻¹ = (ψ * (a : K) * ψ⁻¹) * (ψ * (b : K) * ψ⁻¹) := by
              group
          _ = (a : K) * (b : K) := by rw [ha', hb']
      one_mem' := by
        show ψ * (1 : K) * ψ⁻¹ = 1
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ψ * (a : K) * ψ⁻¹ = (a : K) := ha
        show ψ * (a : K)⁻¹ * ψ⁻¹ = (a : K)⁻¹
        calc ψ * (a : K)⁻¹ * ψ⁻¹ = (ψ * (a : K) * ψ⁻¹)⁻¹ := by group
          _ = (a : K)⁻¹ := by rw [ha'] }
  have hCdvd : Nat.card {u : (V : Subgroup K) // ψ * u * ψ⁻¹ = u} ∣ 2 ^ 10 := by
    have e : Nat.card {u : (V : Subgroup K) // ψ * u * ψ⁻¹ = u} = Nat.card Csub :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => Iff.rfl)
    rw [e]
    have := Subgroup.card_subgroup_dvd_card Csub
    rwa [card_two hSz V, show (1024 : ℕ) = 2 ^ 10 by norm_num] at this
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).1 hCdvd
  rw [hjeq] at hreg
  interval_cases j <;> omega

theorem conj_injective (hSz : SzSylow K) (hsimple : IsSimpleGroup K) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  refine eq_one_of_forall_smul_eq hSz hsimple fun W => ?_
  refine Sylow.smul_eq_iff_mem_normalizer.2 ?_
  refine Subgroup.mem_normalizer_iff.2 fun h => ?_
  have : g * h * g⁻¹ = h := by
    have := congrArg (fun f : MulAut K => f h) hg
    simpa [MulAut.conj_apply] using this
  rw [this]

theorem prime_dvd_card {q : ℕ} (hq : q.Prime) (h : q ∣ 32537600) :
    q = 2 ∨ q = 5 ∨ q = 31 ∨ q = 41 := by
  have e : (32537600 : ℕ) = 2 ^ 10 * 5 ^ 2 * 31 * 41 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1
          (hq.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h)))

theorem factorization_forty_one : (32537600 : ℕ).factorization 41 = 1 := by
  have h : (32537600 : ℕ) = 41 ^ 1 * (2 ^ 10 * 5 ^ 2 * 31) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_pow (by norm_num)]
  have : ¬ 41 ∣ 2 ^ 10 * 5 ^ 2 * 31 := by norm_num
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp

theorem exists_zpowers_eq_of_card_prime {R : Subgroup K} {q : ℕ} (hq : q.Prime)
    (hR : Nat.card R = q) : ∃ ψ : K, orderOf ψ = q ∧ R = zpowers ψ := by
  have hne : R ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hR
    exact hq.one_lt.ne hR
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1 : (a : K) ≠ 1 := fun h => ha (Subtype.ext h)
  have hord : orderOf (a : K) = q := by
    have h1 : orderOf (a : K) ∣ q := by
      have := Subgroup.orderOf_dvd_natCard R a.2
      rwa [hR] at this
    rcases (Nat.dvd_prime hq).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  refine ⟨a, hord, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 a.2) ?_
  rw [Nat.card_zpowers, hord, hR]

theorem card_eq_of_isPGroup {q : ℕ} (hq : q.Prime) {R : Subgroup K} (hR : IsPGroup q R)
    (hne : R ≠ ⊥) (h2 : ¬ q ^ 2 ∣ Nat.card K) : Nat.card R = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
  have hdvd : Nat.card R ∣ Nat.card K := Subgroup.card_subgroup_dvd_card R
  rcases n with _ | _ | n
  · exfalso
    apply hne
    rw [← Subgroup.card_eq_one]
    simpa using hn
  · simpa using hn
  · exfalso
    apply h2
    exact (pow_dvd_pow q (by omega : 2 ≤ n + 2)).trans (hn ▸ hdvd)

theorem card_dvd_of_forall_orderOf_dvd {q : ℕ} (hq : q.Prime) {H : Type} [Group H] [Finite H]
    (hord : ∀ h : H, orderOf h ∣ q) (hdvd : Nat.card H ∣ Nat.card K)
    (h2 : ¬ q ^ 2 ∣ Nat.card K) : Nat.card H ∣ q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hp : IsPGroup q H := by
    rw [IsPGroup.iff_orderOf]
    intro g
    rcases (Nat.dvd_prime hq).1 (hord g) with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  rcases n with _ | _ | n
  · rw [hn]; simp
  · rw [hn]; simp
  · exfalso
    apply h2
    exact (pow_dvd_pow q (by omega : 2 ≤ n + 2)).trans (hn ▸ hdvd)

theorem no_two_commute (hSz : SzSylow K) {y c : K} (hy : orderOf y = 41) (hc : orderOf c = 2)
    (hcy : y * c = c * y) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hG : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc]; norm_num)
  obtain ⟨V, hV⟩ := hG.exists_le_sylow
  have hcV : c ∈ (V : Subgroup K) := hV (Subgroup.mem_zpowers c)
  have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc; omega
  have hyV : y⁻¹ * c * y ∈ (V : Subgroup K) := by
    have : y⁻¹ * c * y = c := by
      calc y⁻¹ * c * y = y⁻¹ * (c * y) := by group
        _ = y⁻¹ * (y * c) := by rw [hcy]
        _ = c := by group
    rw [this]
    exact hcV
  have := eq_one_of_smul_eq hSz (by rw [hy]; norm_num) (smul_eq_of_mem hSz hc1 hcV hyV)
  rw [this, orderOf_one] at hy
  omega

theorem no_five_commute
    (hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K))
    {y c : K} (hy : orderOf y = 41) (hc : orderOf c = 5) (hcy : y * c = c * y) : False := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hG : IsPGroup 5 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc]; norm_num)
  obtain ⟨T, hT⟩ := hG.exists_le_sylow
  have hcT : c ∈ (T : Subgroup K) := hT (Subgroup.mem_zpowers c)
  have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc; omega
  have hyT : y ∈ (T : Subgroup K) := hC T c hcT hc1 y hcy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 T.2) ⟨y, hyT⟩
  have h41 : 41 = 5 ^ k := by
    rw [← hy, ← hk]
    exact Subgroup.orderOf_coe (⟨y, hyT⟩ : (T : Subgroup K))
  rcases k with _ | k
  · norm_num at h41
  · have : 5 ∣ 41 := by
      rw [h41]
      exact dvd_pow_self 5 (Nat.succ_ne_zero k)
    omega

theorem mem_normalizer_zpowers_of_commute {y c : K} (hcy : y * c = c * y) :
    y ∈ normalizer ((zpowers c : Subgroup K) : Set K) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact (Commute.zpow_left (hcy.symm : Commute c y) k)

theorem no_thirtyone_commute (hSz : SzSylow K) (hsimple : IsSimpleGroup K) {y c : K}
    (hy : orderOf y = 41) (hc : orderOf c = 31) (hcy : y * c = c * y) : False := by
  have h := orderOf_dvd_card_fix hSz (mem_normalizer_zpowers_of_commute hcy)
    (by rw [hy]; norm_num)
  rw [hy] at h
  rcases card_fix_of_orderOf_31 hSz hsimple hc with h' | h' <;> rw [h'] at h <;> omega

theorem orderOf_dvd_of_commute (hSz : SzSylow K) (hsimple : IsSimpleGroup K)
    (hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K))
    {y : K} (hy : orderOf y = 41) {c : K} (hcy : y * c = c * y) : orderOf c ∣ 41 := by
  have hcop : Nat.Coprime (orderOf c) (2 ^ 10 * 5 ^ 2 * 31) := by
    refine Nat.coprime_of_dvd fun r hr hrc hrk => ?_
    have hr0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    have hc' : orderOf (c ^ (orderOf c / r)) = r := orderOf_pow_orderOf_div hr0 hrc
    have hcy' : y * c ^ (orderOf c / r) = c ^ (orderOf c / r) * y :=
      Commute.pow_right (hcy : Commute y c) _
    have hrK : r ∣ 32537600 := hrk.trans (by norm_num)
    rcases prime_dvd_card hr hrK with rfl | rfl | rfl | rfl
    · exact no_two_commute hSz hy hc' hcy'
    · exact no_five_commute hC hy hc' hcy'
    · exact no_thirtyone_commute hSz hsimple hy hc' hcy'
    · exact absurd hrk (by norm_num)
  have hdvd : orderOf c ∣ 2 ^ 10 * 5 ^ 2 * 31 * 41 := by
    have := orderOf_dvd_natCard c
    rwa [hSz.card, show (32537600 : ℕ) = 2 ^ 10 * 5 ^ 2 * 31 * 41 by norm_num] at this
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem case_two (hSz : SzSylow K) {z : K} (hz : orderOf z = 5) {R : Subgroup K}
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥) (hzR : z ∈ normalizer (R : Set K)) : False := by
  obtain ⟨V, hV⟩ := hR.exists_le_sylow
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hx1' : (x : K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxV : (x : K) ∈ (V : Subgroup K) := hV x.2
  have hxz : z⁻¹ * x * z ∈ R := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hzR) x).1 x.2
    simpa using this
  have := eq_one_of_smul_eq hSz (by rw [hz]; norm_num) (smul_eq_of_mem hSz hx1' hxV (hV hxz))
  rw [this, orderOf_one] at hz
  omega

theorem case_thirtyone (hSz : SzSylow K) (hsimple : IsSimpleGroup K) {z ψ : K}
    (hz : orderOf z = 5) (hψ : orderOf ψ = 31)
    (hzψ : z ∈ normalizer ((zpowers ψ : Subgroup K) : Set K)) : False := by
  have h := orderOf_dvd_card_fix hSz hzψ (by rw [hz]; norm_num)
  rw [hz] at h
  rcases card_fix_of_orderOf_31 hSz hsimple hψ with h' | h' <;> rw [h'] at h <;> omega

theorem case_fortyone (hSz : SzSylow K) (hsimple : IsSimpleGroup K)
    (hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K))
    {z y : K} (hz : orderOf z = 5) (hy : orderOf y = 41)
    (hzy : z ∈ normalizer ((zpowers y : Subgroup K) : Set K)) : False := by
  have h41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  set W : Subgroup K := zpowers y with hW
  have hWcard : Nat.card W = 41 := by rw [hW, Nat.card_zpowers, hy]
  have hcyc : IsCyclic W := isCyclic_of_prime_card hWcard
  have hWN : W ≤ normalizer (W : Set K) := Subgroup.le_normalizer
  have hker : Nat.card W.normalizerMonoidHom.ker ∣ 41 := by
    refine card_dvd_of_forall_orderOf_dvd (K := K) (by norm_num) ?_ ?_ ?_
    · intro g
      have h1 : W.normalizerMonoidHom (g : normalizer (W : Set K)) = 1 := g.2
      have h2 := congrArg (fun f : MulAut W => ((f ⟨y, Subgroup.mem_zpowers y⟩ : W) : K)) h1
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
      set n : K := ((g : normalizer (W : Set K)) : K) with hn
      have hcomm : y * n = n * y := by
        calc y * n = n * y * n⁻¹ * n := by rw [h2]
          _ = n * y := by group
      have := orderOf_dvd_of_commute hSz hsimple hC hy hcomm
      rwa [hn, Subgroup.orderOf_coe, Subgroup.orderOf_coe] at this
    · exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
    · rw [hSz.card]
      norm_num
  have hrange : Nat.card W.normalizerMonoidHom.range ∣ 40 := by
    have h1 : Nat.card W.normalizerMonoidHom.range ∣ Nat.card (MulAut W) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.totient 41 = 40 := by decide
    rwa [IsCyclic.card_mulAut, hWcard, h2] at h1
  have hmul := Subgroup.card_ker_mul_card_range W.normalizerMonoidHom
  have hNdvd : Nat.card (normalizer (W : Set K)) ∣ 41 * 40 := by
    rw [← hmul]
    exact mul_dvd_mul hker hrange
  have h5N : 5 ∣ Nat.card (normalizer (W : Set K)) := by
    have := Subgroup.orderOf_dvd_natCard _ hzy
    rwa [hz] at this
  have h41N : 41 ∣ Nat.card (normalizer (W : Set K)) := by
    rw [← hWcard]
    exact Subgroup.card_dvd_of_le hWN
  have hsyl : Nat.card W = 41 ^ (Nat.card K).factorization 41 := by
    rw [hWcard, hSz.card, factorization_forty_one]
    norm_num
  let P : Sylow 41 K := Sylow.ofCard W hsyl
  have hmod := card_sylow_modEq_one 41 K
  have hidx : Nat.card (Sylow 41 K) = (normalizer (W : Set K)).index :=
    Sylow.card_eq_index_normalizer P
  have hcm := Subgroup.card_mul_index (normalizer (W : Set K))
  rw [hSz.card] at hcm
  rw [hidx] at hmod
  unfold Nat.ModEq at hmod
  obtain ⟨a, ha⟩ : 205 ∣ Nat.card (normalizer (W : Set K)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 41) h5N h41N
  rw [ha] at hNdvd hcm
  have ha8 : a ∣ 8 := by
    have : 205 * a ∣ 205 * 8 := by simpa using hNdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have ha8' : a ≤ 8 := Nat.le_of_dvd (by norm_num) ha8
  generalize (normalizer (W : Set K)).index = idx at hcm hmod
  interval_cases a <;> omega

theorem eq_bot_of_normalizes (hSz : SzSylow K) (hsimple : IsSimpleGroup K)
    (hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K))
    {z : K} (hz : orderOf z = 5) {W : Subgroup K} (hW : ¬ 5 ∣ Nat.card W)
    (hzW : z ∈ normalizer (W : Set K)) : W = ⊥ := by
  by_contra hne
  have hW1 : Nat.card W ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨q, hq, hqW⟩ := Nat.exists_prime_and_dvd hW1
  have hqK : q ∣ 32537600 := by
    have := hqW.trans (Subgroup.card_subgroup_dvd_card W)
    rwa [hSz.card] at this
  have hz5 : IsPGroup 5 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; norm_num)
  have hzn : zpowers z ≤ normalizer (W : Set K) := (Subgroup.zpowers_le).2 hzW
  obtain ⟨S, hS⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      5 Nat.prime_five (zpowers z) W hz5 hW hzn q hq
  set R : Subgroup K := (S : Subgroup W).map W.subtype with hR
  have hRp : IsPGroup q R := S.2.map W.subtype
  have hzR : z ∈ normalizer (R : Set K) := hS (Subgroup.mem_zpowers z)
  have hRne : R ≠ ⊥ := by
    haveI : Fact q.Prime := ⟨hq⟩
    intro h
    have h1 := S.dvd_card_of_dvd_card hqW
    have h2 : Nat.card R = Nat.card S := Subgroup.card_map_of_injective W.subtype_injective
    rw [h, Subgroup.card_bot] at h2
    rw [← h2] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
  rcases prime_dvd_card hq hqK with rfl | rfl | rfl | rfl
  · exact case_two hSz hz hRp hRne hzR
  · exact hW hqW
  · have hRcard : Nat.card R = 31 :=
      card_eq_of_isPGroup (by norm_num) hRp hRne (by rw [hSz.card]; norm_num)
    obtain ⟨ψ, hψ, hRψ⟩ := exists_zpowers_eq_of_card_prime (by norm_num) hRcard
    exact case_thirtyone hSz hsimple hz hψ (hRψ ▸ hzR)
  · have hRcard : Nat.card R = 41 :=
      card_eq_of_isPGroup (by norm_num) hRp hRne (by rw [hSz.card]; norm_num)
    obtain ⟨y, hy, hRy⟩ := exists_zpowers_eq_of_card_prime (by norm_num) hRcard
    exact case_fortyone hSz hsimple hC hz hy (hRy ▸ hzR)

end CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer
