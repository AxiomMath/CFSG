module

public import CFSG.CGT.Foote82.Lemma62Special
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L K : Subgroup (GLV V)} {s : GLV V} {p : ℕ}

private theorem mem_fixedSpace_zpowers_iff {g : GLV V} {v : V} :
    v ∈ fixedSpace (Subgroup.zpowers g) ↔ g v = v := by
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h t ht
    have : t ∈ MulAction.stabilizer (GLV V) v :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h) ht
    exact MulAction.mem_stabilizer_iff.1 this

private theorem glv_mul_apply (a b : GLV V) (v : V) : (a * b) v = a (b v) := rfl

private theorem glv_inv_apply_of_apply_eq {a : GLV V} {v : V} (h : a v = v) : a⁻¹ v = v := by
  have : a⁻¹ v = a⁻¹ (a v) := by rw [h]
  rw [this]
  exact (LinearEquiv.symm_apply_apply a v)

private theorem card_sup_le_mul {M : Type*} [Group M] [Finite M] {H N : Subgroup M}
    (h : H ≤ Subgroup.normalizer (N : Set M)) :
    Nat.card ↥(H ⊔ N) ≤ Nat.card H * Nat.card N := by
  have hsurj : Function.Surjective (fun x : H × N =>
      (⟨x.1 * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
        (Subgroup.mem_sup_right x.2.2)⟩ : ↥(H ⊔ N))) := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ ((H ⊔ N : Subgroup M) : Set M) := hz
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H N h] at hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := hz'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(H ⊔ N) ≤ Nat.card (H × N) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card H * Nat.card N := Nat.card_prod _ _

private theorem eq_one_of_inv_eq_self {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : M} (hx : x ^ p = 1) (h : x⁻¹ = x) : x = 1 := by
  have h2 : x ^ 2 = 1 := by
    have : x * x = 1 := by
      calc x * x = x⁻¹ * x := by rw [h]
        _ = 1 := inv_mul_cancel x
    simpa [pow_two] using this
  have h1 := orderOf_dvd_of_pow_eq_one h2
  have h2' := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime hp).1 h2' with h3 | h3
  · exact orderOf_eq_one_iff.1 h3
  · rw [h3] at h1
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1) hp2

theorem Core62.exists_inverted (hc : Core62 G L K s p) :
    ∀ k ∈ K, ∃ d ∈ frat K, s * (k * d) * s⁻¹ = (k * d)⁻¹ := by
  intro k hk
  have hφ : s * k * s⁻¹ * k ∈ frat K := hc.inverts k hk
  obtain ⟨m, hm⟩ := hc.prime.eq_two_or_odd'.resolve_left hc.p_ne
  have hφp : (s * k * s⁻¹ * k) ^ p = 1 := hc.pow_eq_one _ (frat_le K hφ)
  generalize hφdef : s * k * s⁻¹ * k = φ at hφ hφp
  have hsk : s * k * s⁻¹ = φ * k⁻¹ := by rw [← hφdef]; group
  have ha : φ ^ m ∈ frat K := (frat K).pow_mem hφ m
  refine ⟨φ ^ m, ha, ?_⟩
  have h1 : s * (φ ^ m) * s⁻¹ = φ ^ m := hc.s_centralizes_frat _ ha
  have h2 : k⁻¹ * φ ^ m = φ ^ m * k⁻¹ := by
    have := Subgroup.mem_centralizer_iff.1 (hc.frat_center ha) k⁻¹ (K.inv_mem hk)
    exact this
  have h3 : φ * φ ^ m = (φ ^ m)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc φ * φ ^ m * φ ^ m = φ ^ (1 + m + m) := by rw [pow_add, pow_add, pow_one]
      _ = φ ^ p := by congr 1; omega
      _ = 1 := hφp
  calc s * (k * φ ^ m) * s⁻¹ = (s * k * s⁻¹) * (s * φ ^ m * s⁻¹) := by group
    _ = φ * k⁻¹ * φ ^ m := by rw [hsk, h1]
    _ = φ * (k⁻¹ * φ ^ m) := mul_assoc _ _ _
    _ = φ * (φ ^ m * k⁻¹) := by rw [h2]
    _ = (φ * φ ^ m) * k⁻¹ := (mul_assoc _ _ _).symm
    _ = (φ ^ m)⁻¹ * k⁻¹ := by rw [h3]
    _ = (k * φ ^ m)⁻¹ := (mul_inv_rev k (φ ^ m)).symm

theorem Core62.centralizes_fixedSpace (hc : Core62 G L K s p) {e : GLV V} (he : e ∈ K)
    (heK : e ∉ frat K) (hinv : s * e * s⁻¹ = e⁻¹) :
    ∀ v ∈ fixedSpace (Subgroup.zpowers e), s v = v := by
  intro v hv
  rw [mem_fixedSpace_zpowers_iff] at hv
  have hes : e * s = s * e⁻¹ := by
    have h1 : s * e⁻¹ * s⁻¹ = e := by
      have := congrArg (fun x => x⁻¹) hinv
      simpa [mul_assoc] using this
    calc e * s = (s * e⁻¹ * s⁻¹) * s := by rw [h1]
      _ = s * e⁻¹ := by group
  have hsv : e (s v) = s v := by
    have h := congrArg (fun f : GLV V => f v) hes
    simp only [glv_mul_apply] at h
    rw [h, glv_inv_apply_of_apply_eq hv]
  have hwe : e (s v - v) = s v - v := by rw [map_sub, hsv, hv]
  have hwc : s v - v ∈ commSpace (Subgroup.zpowers s) ⊤ :=
    sub_mem_commSpace (Subgroup.mem_zpowers s) Submodule.mem_top
  have hL : ∀ l ∈ L, l (s v - v) = s v - v := fun l hl =>
    (Setup6.lemma61 hc.conf.setup (Subgroup.mem_zpowers s)).1 l hl _ hwc
  set gens : Set (GLV V) := {x | ∃ l ∈ L, x = l * e * l⁻¹} with hgens
  set M₀ : Subgroup (GLV V) := Subgroup.closure gens with hM₀
  have hfixM₀ : ∀ m ∈ M₀, m (s v - v) = s v - v := by
    have hle : M₀ ≤ MulAction.stabilizer (GLV V) (s v - v) := by
      rw [hM₀, Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      show (l * e * l⁻¹) (s v - v) = s v - v
      rw [glv_mul_apply, glv_mul_apply, hL l⁻¹ (L.inv_mem hl), hwe, hL l hl]
    exact fun m hm => MulAction.mem_stabilizer_iff.1 (hle hm)
  have hLK : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := Subgroup.le_normalizer_iff.1 hc.conf.L_le
  have hM₀K : M₀ ≤ K := by
    rw [hM₀, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hLK l hl e he
  have heM₀ : e ∈ M₀ := Subgroup.subset_closure ⟨1, L.one_mem, by simp⟩
  have hLM₀ : L ≤ Subgroup.normalizer (M₀ : Set (GLV V)) := by
    rw [hM₀, Subgroup.le_normalizer_closure_iff]
    rintro l hl _ ⟨l', hl', rfl⟩
    refine Subgroup.subset_closure ⟨l * l', L.mul_mem hl hl', ?_⟩
    simp [mul_assoc]
  have hLfrat : L ≤ Subgroup.normalizer (frat K : Set (GLV V)) :=
    hc.conf.L_le.trans (normalizer_le_normalizer_frat K)
  have hLM : L ≤ Subgroup.normalizer ((M₀ ⊔ frat K : Subgroup (GLV V)) : Set (GLV V)) :=
    (le_inf hLM₀ hLfrat).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hMK : M₀ ⊔ frat K = K := by
    rcases hc.irreducible (M₀ ⊔ frat K) le_sup_right (sup_le hM₀K (frat_le K)) hLM with h | h
    · exact absurd (h ▸ (Subgroup.mem_sup_left heM₀)) heK
    · exact h
  have hM₀eq : M₀ = K := eq_of_sup_frat hM₀K hMK
  have hw : s v - v ∈ fixedSpace K := fun k hk => hfixM₀ k (hM₀eq ▸ hk)
  rw [hc.fix, Submodule.mem_bot, sub_eq_zero] at hw
  exact hw

private theorem Core62.false_of_pow_four_le (hc : Core62 G L K s p) (h4 : p ^ 4 ≤ Nat.card K) :
    False := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hp := hc.prime
  have hfrat : Nat.card (frat K) = p := hc.card_frat
  have hKne : K ≠ ⊥ := by
    intro hK
    have h1 : Nat.card (frat K) ≤ Nat.card K := Subgroup.card_le_of_le (frat_le K)
    rw [hfrat, hK, Subgroup.card_bot] at h1
    have := hp.two_le
    omega
  obtain ⟨k₀, hk₀K, hk₀⟩ := SetLike.exists_of_lt (frat_lt hc.pgroup hKne)
  obtain ⟨d₀, hd₀, hinv₀⟩ := hc.exists_inverted k₀ hk₀K
  have hk₁K : k₀ * d₀ ∈ K := K.mul_mem hk₀K (frat_le K hd₀)
  have hk₁ : k₀ * d₀ ∉ frat K := fun h => hk₀ (by
    simpa using (frat K).mul_mem h ((frat K).inv_mem hd₀))
  generalize k₀ * d₀ = k₁ at hk₁K hk₁ hinv₀
  have hk₁p : k₁ ^ p = 1 := hc.pow_eq_one k₁ hk₁K
  have hk₁ne : k₁ ≠ 1 := fun h => hk₁ (h ▸ (frat K).one_mem)
  have hord : orderOf k₁ = p := orderOf_eq_prime hk₁p hk₁ne
  have hD : Nat.card ↥(Subgroup.zpowers k₁ ⊔ frat K) ≤ p ^ 2 := by
    have hnorm : Subgroup.zpowers k₁ ≤ Subgroup.normalizer (frat K : Set (GLV V)) :=
      Subgroup.zpowers_le.2 (normalizer_le_normalizer_frat K (Subgroup.le_normalizer hk₁K))
    calc Nat.card ↥(Subgroup.zpowers k₁ ⊔ frat K)
        ≤ Nat.card (Subgroup.zpowers k₁) * Nat.card (frat K) := card_sup_le_mul hnorm
      _ = p * p := by rw [Nat.card_zpowers, hord, hfrat]
      _ = p ^ 2 := (sq p).symm
  have hcomm_mem : ∀ k ∈ K, ⁅k₁, k⁆ ∈ frat K := fun k hk => by
    rw [hc.frat_eq_commutator]
    exact Subgroup.commutator_mem_commutator hk₁K hk
  let φ : ↥K →* GLV V := MonoidHom.mk' (fun k => ⁅k₁, (k : GLV V)⁆) (by
    intro a b
    have hcb : (a : GLV V)⁻¹ * ⁅k₁, (b : GLV V)⁆ = ⁅k₁, (b : GLV V)⁆ * (a : GLV V)⁻¹ :=
      Subgroup.mem_centralizer_iff.1 (hc.frat_center (hcomm_mem b b.2)) _ (K.inv_mem a.2)
    show ⁅k₁, (a : GLV V) * b⁆ = ⁅k₁, (a : GLV V)⁆ * ⁅k₁, (b : GLV V)⁆
    simp only [commutatorElement_def] at hcb ⊢
    calc k₁ * (↑a * ↑b) * k₁⁻¹ * (↑a * ↑b)⁻¹
        = (k₁ * ↑a * k₁⁻¹) * ((k₁ * ↑b * k₁⁻¹ * (↑b)⁻¹) * (↑a)⁻¹) := by group
      _ = (k₁ * ↑a * k₁⁻¹) * ((↑a)⁻¹ * (k₁ * ↑b * k₁⁻¹ * (↑b)⁻¹)) := by rw [← hcb]
      _ = (k₁ * ↑a * k₁⁻¹ * (↑a)⁻¹) * (k₁ * ↑b * k₁⁻¹ * (↑b)⁻¹) := by group)
  have hrange : φ.range ≤ frat K := by
    rintro _ ⟨y, rfl⟩
    exact hcomm_mem y y.2
  have hkr := Subgroup.card_ker_mul_card_range φ
  have hr : Nat.card φ.range ≤ p := hfrat ▸ Subgroup.card_le_of_le hrange
  have hker : p ^ 3 ≤ Nat.card φ.ker := by
    have h1 : p ^ 3 * p ≤ Nat.card φ.ker * p := by
      calc p ^ 3 * p = p ^ 4 := by ring
        _ ≤ Nat.card K := h4
        _ = Nat.card φ.ker * Nat.card φ.range := hkr.symm
        _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hr
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  obtain ⟨y, hy1, hy2⟩ : ∃ y : ↥K, y ∈ φ.ker ∧
      (y : GLV V) ∉ Subgroup.zpowers k₁ ⊔ frat K := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : φ.ker.map K.subtype ≤ Subgroup.zpowers k₁ ⊔ frat K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hcon y hy
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective K.subtype_injective] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨d₁, hd₁, hinv₁⟩ := hc.exists_inverted (y : GLV V) y.2
  have hk₂K : (y : GLV V) * d₁ ∈ K := K.mul_mem y.2 (frat_le K hd₁)
  have hk₂D : (y : GLV V) * d₁ ∉ Subgroup.zpowers k₁ ⊔ frat K := fun h => hy2 (by
    simpa using (Subgroup.zpowers k₁ ⊔ frat K).mul_mem h
      ((Subgroup.zpowers k₁ ⊔ frat K).inv_mem (Subgroup.mem_sup_right hd₁)))
  have hcomm₂ : Commute k₁ ((y : GLV V) * d₁) := by
    have h1 : k₁ * (y : GLV V) = y * k₁ :=
      commutatorElement_eq_one_iff_mul_comm.1 (MonoidHom.mem_ker.1 hy1)
    have h2 : k₁ * d₁ = d₁ * k₁ :=
      Subgroup.mem_centralizer_iff.1 (hc.frat_center hd₁) k₁ hk₁K
    show k₁ * ((y : GLV V) * d₁) = ((y : GLV V) * d₁) * k₁
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  generalize (y : GLV V) * d₁ = k₂ at hk₂K hk₂D hinv₁ hcomm₂
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (GLV V), A = Subgroup.closure {k₁, k₂} := ⟨_, rfl⟩
  have hk₁A : k₁ ∈ A := hA ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hk₂A : k₂ ∈ A := hA ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hAK : A ≤ K := by
    rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl) <;> assumption
  haveI hAcomm : IsMulCommutative A := by
    rw [hA]
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hcomm₂
    · exact hcomm₂.symm
    · exact absurd rfl hxy
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hinvA : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹ := by
    intro a ha
    rw [hA] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hinv₀
      · exact hinv₁
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := hcommA x (hA ▸ hx) y (hA ▸ hy)
      calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
        _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
        _ = (x * y)⁻¹ := by rw [hxy]
    | inv x hx ih =>
      calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [ih]
  have hApG : IsPGroup p A := hc.pgroup.to_le hAK
  have hAle : Nat.card A ≤ p ^ 2 := by
    have hAsub : A ≤ Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂ := by
      rw [hA, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hnorm : Subgroup.zpowers k₁ ≤ Subgroup.normalizer (Subgroup.zpowers k₂ : Set (GLV V)) := by
      rw [Subgroup.le_normalizer_iff]
      intro h hh n hn
      have hhA : h ∈ A := Subgroup.zpowers_le.2 hk₁A hh
      have hnA : n ∈ A := Subgroup.zpowers_le.2 hk₂A hn
      rw [hcommA h hhA n hnA, mul_inv_cancel_right]
      exact hn
    have hk₂p : orderOf k₂ ≤ p :=
      Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hc.pow_eq_one k₂ hk₂K))
    calc Nat.card A ≤ Nat.card ↥(Subgroup.zpowers k₁ ⊔ Subgroup.zpowers k₂) :=
          Subgroup.card_le_of_le hAsub
      _ ≤ Nat.card (Subgroup.zpowers k₁) * Nat.card (Subgroup.zpowers k₂) :=
          card_sup_le_mul hnorm
      _ = p * orderOf k₂ := by rw [Nat.card_zpowers, Nat.card_zpowers, hord]
      _ ≤ p * p := Nat.mul_le_mul_left _ hk₂p
      _ = p ^ 2 := (sq p).symm
  have hltA : Subgroup.zpowers k₁ < A := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.2 hk₁A) fun heq => hk₂D ?_
    rw [← heq] at hk₂A
    exact Subgroup.mem_sup_left hk₂A
  have hpA : p < Nat.card A := by
    have := Subgroup.card_lt_of_lt hltA
    rwa [Nat.card_zpowers, hord] at this
  obtain ⟨m, hm⟩ := hApG.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm' : m < 2 := not_le.1 hlt
    interval_cases m
    · have := hp.two_le
      rw [pow_zero] at hm
      omega
    · rw [pow_one] at hm
      omega
  have hAcard : Nat.card A = p ^ 2 :=
    le_antisymm hAle (by rw [hm]; exact Nat.pow_le_pow_right hp.pos hm2)
  have hsup := iSup_fixedSpace_eq_top (E := A) hp hc.p_ne hcommA
    (fun e he => hc.pow_eq_one e (hAK he)) hAcard
  have hsfix : ∀ v : V, s v = v := by
    intro v
    have hv : v ∈ (⨆ (H : Subgroup (GLV V)) (_ : H ≤ A) (_ : Nat.card H = p), fixedSpace H) := by
      rw [hsup]
      exact Submodule.mem_top
    have hle : (⨆ (H : Subgroup (GLV V)) (_ : H ≤ A) (_ : Nat.card H = p), fixedSpace H) ≤
        LinearMap.eqLocus (s : V →ₗ[ZMod 2] V) LinearMap.id := by
      refine iSup_le fun H => iSup_le fun hHA => iSup_le fun hHp => ?_
      obtain ⟨e, heH, hne⟩ : ∃ e ∈ H, e ≠ 1 := by
        by_contra hcon
        have hH : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 fun e he =>
          by_contra fun hne => hcon ⟨e, he, hne⟩
        rw [hH, Subgroup.card_bot] at hHp
        exact hp.one_lt.ne hHp
      have heK : e ∈ K := hAK (hHA heH)
      have hinve : s * e * s⁻¹ = e⁻¹ := hinvA e (hHA heH)
      have hefrat : e ∉ frat K := by
        intro hef
        apply hne
        have h1 := hc.s_centralizes_frat e hef
        exact eq_one_of_inv_eq_self hp hc.p_ne (hc.pow_eq_one e heK) (by rw [← hinve, h1])
      intro w hw
      have hw' : w ∈ fixedSpace (Subgroup.zpowers e) :=
        fixedSpace_anti (Subgroup.zpowers_le.2 heH) hw
      exact hc.centralizes_fixedSpace heK hefrat hinve w hw'
    exact hle hv
  have hs1 : s = 1 := LinearEquiv.ext hsfix
  have h1 : orderOf s = 1 := by rw [hs1]; exact orderOf_one
  have := hc.s_ord
  omega

theorem Core62.card_eq (hc : Core62 G L K s p) : Nat.card K = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hp := hc.prime
  have hfrat : Nat.card (frat K) = p := hc.card_frat
  obtain ⟨n, hn⟩ := hc.pgroup.exists_card_eq
  have hKne : K ≠ ⊥ := by
    intro hK
    have h1 : Nat.card (frat K) ≤ Nat.card K := Subgroup.card_le_of_le (frat_le K)
    rw [hfrat, hK, Subgroup.card_bot] at h1
    have := hp.two_le
    omega
  have hlt : p < p ^ n := by
    have := Subgroup.card_lt_of_lt (frat_lt hc.pgroup hKne)
    rwa [hfrat, hn] at this
  have h3 : 3 ≤ n := by
    by_contra hn3
    have hn3' : n < 3 := not_le.1 hn3
    have hn2 : n = 2 := by
      have := hp.two_le
      interval_cases n
      · simp at hlt
        omega
      · simp at hlt
      · rfl
    subst hn2
    haveI hcomm : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
    have h1 : frat K = ⊥ := by
      rw [hc.frat_eq_commutator, eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact setLike_mul_comm ha hb
    rw [h1, Subgroup.card_bot] at hfrat
    exact hp.one_lt.ne hfrat
  have h4 : n < 4 := by
    by_contra hn4
    refine hc.false_of_pow_four_le ?_
    rw [hn]
    exact Nat.pow_le_pow_right hp.pos (not_lt.1 hn4)
  rw [hn]
  congr 1
  omega

end CFSG.CGT.Foote82
