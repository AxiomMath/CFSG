module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017SylowQ
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1114

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

variable {K : Type} [Group K]

@[expose] def PElemsClosed (p : ℕ) (H : Subgroup K) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, (∃ m, a ^ p ^ m = 1) → (∃ m, b ^ p ^ m = 1) → ∃ m, (a * b) ^ p ^ m = 1

theorem pElemsClosed_mono {p : ℕ} {H H' : Subgroup K} (hle : H' ≤ H) (h : PElemsClosed p H) :
    PElemsClosed p H' := fun a ha b hb => h a (hle ha) b (hle hb)

theorem pElemsClosed_conj {p : ℕ} {H : Subgroup K} (g : K) (h : PElemsClosed p H) :
    PElemsClosed p (H.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ⟨m, hm⟩ ⟨m', hm'⟩
  simp only [MulEquiv.coe_toMonoidHom] at hm hm' ⊢
  rw [← map_pow, map_eq_one_iff _ (MulAut.conj g).injective] at hm hm'
  obtain ⟨k, hk⟩ := h a ha b hb ⟨m, hm⟩ ⟨m', hm'⟩
  exact ⟨k, by rw [← map_mul, ← map_pow, hk, map_one]⟩

theorem centralizer_map_conj (g : K) (D : Subgroup K) :
    Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup K) : Set K) =
      (Subgroup.centralizer (D : Set K)).map (MulAut.conj g).toMonoidHom := by
  ext c
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Subgroup.coe_map, Set.mem_image,
    SetLike.mem_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hc
    refine ⟨g⁻¹ * c * g, fun d hd => ?_, by group⟩
    have h := hc d hd
    calc d * (g⁻¹ * c * g) = g⁻¹ * ((g * d * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * d * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * c * g * d := by group
  · rintro ⟨c', hc', rfl⟩ d hd
    have h := hc' d hd
    calc g * d * g⁻¹ * (g * c' * g⁻¹) = g * (d * c') * g⁻¹ := by group
      _ = g * (c' * d) * g⁻¹ := by rw [h]
      _ = g * c' * g⁻¹ * (g * d * g⁻¹) := by group

theorem eq_one_of_pow_two_pow_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : K} {m k : ℕ}
    (h1 : c ^ p ^ m = 1) (h2 : c ^ 2 ^ k = 1) : c = 1 := by
  have hcop : Nat.Coprime (p ^ m) (2 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

variable [Finite K]

theorem noTwist_of_closed {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ E D : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ r → D ≤ E →
      Nat.card D = 3 ^ (r - 1) → PElemsClosed 3 (Subgroup.centralizer (D : Set K)))
    (E₀ : Subgroup K) (hE₀ : IsElemAbelian 3 E₀) (hcard : 3 ^ r ≤ Nat.card E₀) (T : Subgroup K)
    (hT : IsPGroup 2 T) (hET : E₀ ≤ Subgroup.normalizer (T : Set K)) :
    ∀ e ∈ E₀, ∀ t ∈ T, e * t = t * e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro e he t ht
  have hE₀p : IsPGroup 3 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hE₀.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE₀p
  have hrn : r ≤ n := by
    rw [hn] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hze : Nat.card (Subgroup.zpowers e) ∣ 3 ^ r := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hE₀.2 e he)).trans (dvd_pow_self 3 (by omega))
  obtain ⟨E, hEcard, hzE, hEE₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hze
    (show 3 ^ r ∣ Nat.card E₀ from hn ▸ Nat.pow_dvd_pow 3 hrn)
    ((Subgroup.zpowers_le).2 he)
  have heE : e ∈ E := hzE (Subgroup.mem_zpowers e)
  have hE : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hE₀ hEE₀
  have hEne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hEcard
    have : 3 ≤ 3 ^ r := Nat.le_self_pow (by omega) 3
    omega
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1114.gen_by_hyperplanes
    Nat.prime_three hE hEne (hEE₀.trans hET) hT3
  have hcent : ∀ D : Subgroup K, D ≤ E ∧ (D.subgroupOf E).index = 3 →
      T ⊓ Subgroup.centralizer (D : Set K) ≤ Subgroup.centralizer (E : Set K) := by
    rintro D ⟨hDE, hDi⟩ x ⟨hxT, hxD⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hDcard : Nat.card D = 3 ^ (r - 1) := by
      have h1 := (D.subgroupOf E).card_mul_index
      rw [hDi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv, hEcard] at h1
      have : 3 ^ r = 3 ^ (r - 1) * 3 := by rw [← pow_succ]; congr 1; omega
      rw [this] at h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    have hcl := h E D hE hEcard hDE hDcard
    have haD : a ∈ Subgroup.centralizer (D : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact comm_of_isElemAbelian' hE (hDE hd) ha
    have hxD' : x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (D : Set K) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxD (Subgroup.inv_mem _ haD)) (Subgroup.inv_mem _ hxD)
    have ha3 : a ^ 3 ^ 1 = 1 := by simpa using hE.2 a ha
    have hb3 : (x * a⁻¹ * x⁻¹) ^ 3 ^ 1 = 1 := by
      rw [pow_one, conj_pow, inv_pow, ← pow_one (a ^ 3), ← pow_one 3, ha3]
      group
    obtain ⟨m, hm⟩ := hcl a haD _ hxD' ⟨1, ha3⟩ ⟨1, hb3⟩
    have haT : a * x * a⁻¹ ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 (hEE₀.trans hET ha) x).1 hxT
      exact this
    have hcT : a * (x * a⁻¹ * x⁻¹) ∈ T := by
      have e1 : a * (x * a⁻¹ * x⁻¹) = (a * x * a⁻¹) * x⁻¹ := by group
      rw [e1]
      exact T.mul_mem haT (T.inv_mem hxT)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨_, hcT⟩
    have h2 : (a * (x * a⁻¹ * x⁻¹)) ^ 2 ^ k = 1 := by
      have := pow_orderOf_eq_one (⟨_, hcT⟩ : T)
      rw [hk] at this
      simpa using congrArg Subtype.val this
    have h1 := eq_one_of_pow_two_pow_p Nat.prime_three (by norm_num) hm h2
    calc a * x = a * (x * a⁻¹ * x⁻¹) * x * a := by group
      _ = x * a := by rw [h1, one_mul]
  have hTE : T ≤ Subgroup.centralizer (E : Set K) :=
    hgen.trans (iSup₂_le fun D hD => hcent D hD)
  exact Subgroup.mem_centralizer_iff.1 (hTE ht) e heE

theorem noTwist_of_invClosed {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ E D : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ r → D ≤ E →
      Nat.card D = 3 ^ (r - 1) → (∃ t : K, orderOf t = 2 ∧ D ≤ Subgroup.centralizer ({t} : Set K)) →
      PElemsClosed 3 (Subgroup.centralizer (D : Set K)))
    (E₀ : Subgroup K) (hE₀ : IsElemAbelian 3 E₀) (hcard : 3 ^ r ≤ Nat.card E₀) (T : Subgroup K)
    (hT : IsPGroup 2 T) (hET : E₀ ≤ Subgroup.normalizer (T : Set K)) :
    ∀ e ∈ E₀, ∀ t ∈ T, e * t = t * e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro e he t ht
  have hE₀p : IsPGroup 3 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hE₀.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE₀p
  have hrn : r ≤ n := by
    rw [hn] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hze : Nat.card (Subgroup.zpowers e) ∣ 3 ^ r := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hE₀.2 e he)).trans (dvd_pow_self 3 (by omega))
  obtain ⟨E, hEcard, hzE, hEE₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hze
    (show 3 ^ r ∣ Nat.card E₀ from hn ▸ Nat.pow_dvd_pow 3 hrn)
    ((Subgroup.zpowers_le).2 he)
  have heE : e ∈ E := hzE (Subgroup.mem_zpowers e)
  have hE : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hE₀ hEE₀
  have hEne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hEcard
    have : 3 ≤ 3 ^ r := Nat.le_self_pow (by omega) 3
    omega
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1114.gen_by_hyperplanes
    Nat.prime_three hE hEne (hEE₀.trans hET) hT3
  have hcent : ∀ D : Subgroup K, D ≤ E ∧ (D.subgroupOf E).index = 3 →
      T ⊓ Subgroup.centralizer (D : Set K) ≤ Subgroup.centralizer (E : Set K) := by
    rintro D ⟨hDE, hDi⟩ x ⟨hxT, hxD⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, one_mul]
    have hDcard : Nat.card D = 3 ^ (r - 1) := by
      have h1 := (D.subgroupOf E).card_mul_index
      rw [hDi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv, hEcard] at h1
      have : 3 ^ r = 3 ^ (r - 1) * 3 := by rw [← pow_succ]; congr 1; omega
      rw [this] at h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    have hinv : ∃ t : K, orderOf t = 2 ∧ D ≤ Subgroup.centralizer ({t} : Set K) := by
      have hQ2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (D : Set K)) := hT.to_le inf_le_left
      have hQne : T ⊓ Subgroup.centralizer (D : Set K) ≠ ⊥ := fun hb =>
        hx1 ((Subgroup.mem_bot).1 (hb ▸ ⟨hxT, hxD⟩))
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact hQne (Subgroup.card_eq_one.1 hn)
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T ⊓ Subgroup.centralizer (D : Set K))) 2
        (by rw [hn]; exact dvd_pow_self 2 hn0)
      refine ⟨g, by rw [← hg, Subgroup.orderOf_coe], fun d hd => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 g.2.2 d hd
    have hcl := h E D hE hEcard hDE hDcard hinv
    have haD : a ∈ Subgroup.centralizer (D : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact comm_of_isElemAbelian' hE (hDE hd) ha
    have hxD' : x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (D : Set K) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxD (Subgroup.inv_mem _ haD)) (Subgroup.inv_mem _ hxD)
    have ha3 : a ^ 3 ^ 1 = 1 := by simpa using hE.2 a ha
    have hb3 : (x * a⁻¹ * x⁻¹) ^ 3 ^ 1 = 1 := by
      rw [pow_one, conj_pow, inv_pow, ← pow_one (a ^ 3), ← pow_one 3, ha3]
      group
    obtain ⟨m, hm⟩ := hcl a haD _ hxD' ⟨1, ha3⟩ ⟨1, hb3⟩
    have haT : a * x * a⁻¹ ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 (hEE₀.trans hET ha) x).1 hxT
      exact this
    have hcT : a * (x * a⁻¹ * x⁻¹) ∈ T := by
      have e1 : a * (x * a⁻¹ * x⁻¹) = (a * x * a⁻¹) * x⁻¹ := by group
      rw [e1]
      exact T.mul_mem haT (T.inv_mem hxT)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨_, hcT⟩
    have h2 : (a * (x * a⁻¹ * x⁻¹)) ^ 2 ^ k = 1 := by
      have := pow_orderOf_eq_one (⟨_, hcT⟩ : T)
      rw [hk] at this
      simpa using congrArg Subtype.val this
    have h1 := eq_one_of_pow_two_pow_p Nat.prime_three (by norm_num) hm h2
    calc a * x = a * (x * a⁻¹ * x⁻¹) * x * a := by group
      _ = x * a := by rw [h1, one_mul]
  have hTE : T ≤ Subgroup.centralizer (E : Set K) :=
    hgen.trans (iSup₂_le fun D hD => hcent D hD)
  exact Subgroup.mem_centralizer_iff.1 (hTE ht) e heE

theorem closed_of_sylow {r : ℕ} (P : Sylow 3 K)
    (h : ∀ E D : Subgroup K, E ≤ P → IsElemAbelian 3 E → Nat.card E = 3 ^ r → D ≤ E →
      Nat.card D = 3 ^ (r - 1) → PElemsClosed 3 (Subgroup.centralizer (D : Set K))) :
    ∀ E D : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ r → D ≤ E →
      Nat.card D = 3 ^ (r - 1) → PElemsClosed 3 (Subgroup.centralizer (D : Set K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro E D hE hEcard hDE hDcard
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  set φ := (MulAut.conj g).toMonoidHom with hφ
  have hmapQ : ∀ x ∈ (Q : Subgroup K), φ x ∈ (P : Subgroup K) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup K) hx
  have hE' : E.map φ ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmapQ x (hEQ hx)
  have hc := h (E.map φ) (D.map φ) hE' (isElemAbelian_map' φ hE)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard])
    (Subgroup.map_mono hDE)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hDcard])
  rw [centralizer_map_conj] at hc
  have := pElemsClosed_conj g⁻¹ hc
  rwa [Subgroup.map_map, show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
    MonoidHom.id K from by ext; simp [MulAut.conj_apply]; group, Subgroup.map_id] at this

omit [Finite K] in
theorem noTwistRank_of_model {s : TauCeti.SporadicName} {r : ℕ} {X : Type} [Group X]
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h : ∀ E : Subgroup X, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E → ∀ T : Subgroup X,
      IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set X) → ∀ e ∈ E, ∀ t ∈ T, e * t = t * e) :
    NoTwistRank s r := by
  intro K' _ _ hcat E hE hcard T hT hET e he t ht
  obtain ⟨i, hi, ⟨φ0⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := hX
  let φ : K' ≃* X := φ0.trans b.symm
  have hmem : ∀ (H : Subgroup K') (x : K'), x ∈ H → φ x ∈ H.map φ.toMonoidHom :=
    fun H x hx => ⟨x, hx, rfl⟩
  have key := h (E.map φ.toMonoidHom) (isElemAbelian_map' _ hE)
    (by rwa [Subgroup.card_map_of_injective φ.injective]) (T.map φ.toMonoidHom)
    (hT.map φ.toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        refine ⟨x * y' * x⁻¹, (Subgroup.mem_normalizer_iff.1 (hET hx) y').1 hy', ?_⟩
        simp [map_mul, map_inv]
      · intro hy
        obtain ⟨y', hy', hy'e⟩ := hy
        have : y = φ (x⁻¹ * y' * x) := by
          apply φ.symm.injective
          have e2 : φ.symm (φ x * y * (φ x)⁻¹) = φ.symm (φ y') := by
            simp only [MulEquiv.coe_toMonoidHom] at hy'e
            rw [hy'e]
          simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at e2 ⊢
          rw [← e2]
          group
        rw [this]
        refine ⟨_, ?_, rfl⟩
        have := (Subgroup.mem_normalizer_iff.1 (hET (E.inv_mem hx)) y').1 hy'
        simpa using this)
    (φ e) (hmem E e he) (φ t) (hmem T t ht)
  rw [← map_mul, ← map_mul] at key
  exact φ.injective key

section Gen

variable {G : Type} [Group G]

theorem exists_gen_pair [Finite G] {D : Subgroup G} (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 9) : ∃ x ∈ D, ∃ y ∈ D, x ≠ 1 ∧ y ∉ Subgroup.zpowers x ∧
      D = Subgroup.closure {x, y} := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc
    omega
  obtain ⟨⟨x, hxD⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : x ^ 3 = 1 := hD.2 x hxD
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1'
  have hzc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
  have hzD : Subgroup.zpowers x ≤ D := (Subgroup.zpowers_le).2 hxD
  have hlt : Subgroup.zpowers x ≠ D := by
    intro h
    rw [h, hc] at hzc
    omega
  obtain ⟨y, hyD, hyz⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    exact hlt (le_antisymm hzD hall)
  refine ⟨x, hxD, y, hyD, hx1', hyz, ?_⟩
  have hcl : Subgroup.closure {x, y} ≤ D := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact hxD
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hyD
  have hzc' : Subgroup.zpowers x ≤ Subgroup.closure {x, y} :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hdvd : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ 9 := hc ▸ Subgroup.card_dvd_of_le hcl
  have h3 : 3 ∣ Nat.card (Subgroup.closure ({x, y} : Set G)) := hzc ▸ Subgroup.card_dvd_of_le hzc'
  have hne3 : Nat.card (Subgroup.closure ({x, y} : Set G)) ≠ 3 := by
    intro h3'
    have := Subgroup.eq_of_le_of_card_ge hzc' (by rw [h3', hzc])
    exact hyz (this ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have h9 : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
    have hpos := Nat.card_pos (α := Subgroup.closure ({x, y} : Set G))
    have : Nat.card (Subgroup.closure ({x, y} : Set G)) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hd9 : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd9] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  exact (Subgroup.eq_of_le_of_card_ge hcl (by rw [h9, hc])).symm

theorem exists_gen_triple [Finite G] {D : Subgroup G} (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 27) : ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, x ≠ 1 ∧ y ∉ Subgroup.zpowers x ∧
      z ∉ Subgroup.closure ({x, y} : Set G) ∧ D = Subgroup.closure {x, y, z} := by
  classical
  obtain ⟨H, hH, -, hHD⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 2)
    (H := ⊥) (L := D) (by rw [Subgroup.card_bot]; exact one_dvd _) (by rw [hc]; norm_num) bot_le
  obtain ⟨x, hxH, y, hyH, hx1, hyz, hHeq⟩ :=
    exists_gen_pair (CFSG.Open.IsElemAbelian.mono hD hHD) (by rw [hH]; norm_num)
  have hHne : H ≠ D := by
    intro h
    rw [h, hc] at hH
    norm_num at hH
  obtain ⟨z, hzD, hzH⟩ : ∃ z ∈ D, z ∉ H := by
    by_contra hall
    push Not at hall
    exact hHne (le_antisymm hHD hall)
  refine ⟨x, hHD hxH, y, hHD hyH, z, hzD, hx1, hyz, hHeq ▸ hzH, ?_⟩
  have hCD : Subgroup.closure ({x, y, z} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl | hw
    · exact hHD hxH
    · exact hHD hyH
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hzD
  have hHC : H ≤ Subgroup.closure ({x, y, z} : Set G) := by
    rw [hHeq, Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | hw
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hzC : z ∈ Subgroup.closure ({x, y, z} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hdvd : Nat.card (Subgroup.closure ({x, y, z} : Set G)) ∣ 27 :=
    hc ▸ Subgroup.card_dvd_of_le hCD
  have h9 : 9 ∣ Nat.card (Subgroup.closure ({x, y, z} : Set G)) := by
    have := Subgroup.card_dvd_of_le hHC
    rwa [hH] at this
  have hne9 : Nat.card (Subgroup.closure ({x, y, z} : Set G)) ≠ 9 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hHC (by rw [h, hH]; norm_num)
    exact hzH (this ▸ hzC)
  have h27 : Nat.card (Subgroup.closure ({x, y, z} : Set G)) = 27 := by
    have : Nat.card (Subgroup.closure ({x, y, z} : Set G)) ∈ Nat.divisors 27 :=
      Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hd27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd27] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  exact (Subgroup.eq_of_le_of_card_ge hCD (by rw [h27, hc])).symm

theorem exists_conj_into_of_card [Finite G] {p : ℕ} [Fact p.Prime] {H Q D : Subgroup G}
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) (hDH : D ≤ H)
    (hD : IsPGroup p D) : ∃ g ∈ H, D.map (MulAut.conj g).toMonoidHom ≤ Q := by
  let S : Sylow p H := Sylow.ofCard (Q.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ])
  have hD' : IsPGroup p (D.subgroupOf H) := hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm
  obtain ⟨R, hR⟩ := hD'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H R S
  refine ⟨h, h.2, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hdR : (⟨d, hDH hd⟩ : H) ∈ (R : Subgroup H) := hR (Subgroup.mem_subgroupOf.2 hd)
  have hmem : (MulAut.conj h) • (⟨d, hDH hd⟩ : H) ∈ (S : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hdR
  have hS : (S : Subgroup H) = Q.subgroupOf H := Sylow.coe_ofCard _ _
  rw [hS, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hmem

theorem pElemsClosed_of_map_conj {p : ℕ} (g : G) {D : Subgroup G}
    (h : PElemsClosed p
      (Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))) :
    PElemsClosed p (Subgroup.centralizer (D : Set G)) := by
  rw [centralizer_map_conj] at h
  have := pElemsClosed_conj g⁻¹ h
  rwa [Subgroup.map_map, show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
    MonoidHom.id G from by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group, Subgroup.map_id] at this

theorem map_conj_le_centralizer_singleton (k : G) {D : Subgroup G} {t : G}
    (h : D ≤ Subgroup.centralizer ({t} : Set G)) :
    D.map (MulAut.conj k).toMonoidHom ≤ Subgroup.centralizer ({k * t * k⁻¹} : Set G) := by
  rintro _ ⟨d, hd, rfl⟩
  have hc : t * d = d * t := Subgroup.mem_centralizer_iff.1 (h hd) t (Set.mem_singleton t)
  rw [Subgroup.mem_centralizer_iff]
  rintro s rfl
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc k * t * k⁻¹ * (k * d * k⁻¹) = k * (t * d) * k⁻¹ := by group
    _ = k * (d * t) * k⁻¹ := by rw [hc]
    _ = k * d * k⁻¹ * (k * t * k⁻¹) := by group

end Gen


end CFSG.LocalAnalysis.GLTheoremA.H1017
