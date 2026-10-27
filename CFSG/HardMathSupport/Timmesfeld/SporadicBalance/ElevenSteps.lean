module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

theorem mem_centralizer_conj_of_mem {s c y : G} (hy : y ∈ Subgroup.centralizer ({s} : Set G)) :
    c * y * c⁻¹ ∈ Subgroup.centralizer ({c * s * c⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc c * y * c⁻¹ * (c * s * c⁻¹) = c * (y * s) * c⁻¹ := by group
    _ = c * (s * y) * c⁻¹ := by rw [hy]
    _ = c * s * c⁻¹ * (c * y * c⁻¹) := by group

theorem odd_card_gLAPPrimeCoreOf_eleven [Finite G] {t s : G} (hs : orderOf s = 11)
    (hP : ∃ P : Subgroup G, IsPGroup 11 P ∧ P ≤ Subgroup.centralizer ({s} : Set G) ∧
      ∀ u : G, orderOf u = 2 → ∃ g ∈ P, g * u ≠ u * g)
    (hpure : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card A → ∃ u ∈ A, IsConj t u)
    (hbound : ∀ x : G, orderOf x = 11 → x * t = t * x →
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G) < 11 * 2 ^ 10) :
    Odd (Nat.card (GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set G)))) := by
  have h11 : Nat.Prime 11 := by norm_num
  set N := GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set G)) with hN
  by_contra hodd
  have h2N : 2 ∣ Nat.card N := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨P, hPp, hPC, hfix⟩ := hP
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact GLAPPrimeCoreOf_conj_mem g (hPC hg) y hy
    · intro hy
      have := GLAPPrimeCoreOf_conj_mem g⁻¹ (Subgroup.inv_mem _ (hPC hg)) _ hy
      simpa [mul_assoc] using this
  have hcopN : ¬ 11 ∣ Nat.card N := fun h =>
    (Nat.Prime.coprime_iff_not_dvd h11).1 (coprime_card_GLAPPrimeCoreOf h11 _) h
  obtain ⟨A, hAN, hA1, hA2, hAc, hAe, hAmod⟩ := exists_elemAbelian_modEq_one h11 Nat.prime_two hPp
    hcopN hPN h2N (fun a ha => by
      obtain ⟨g, hg, hga⟩ := hfix a ha
      exact ⟨g, hg, hga⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.eq_bot_of_card_eq A (by rw [hk, pow_zero]))
  have hk10 : 10 ≤ k := ten_le_of_two_pow_modEq_eleven (by rw [← hk]; exact hAmod) hk0
  have hA8 : 8 ≤ Nat.card A := by
    rw [hk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, huA, hu⟩ := hpure A hAc hAe hA8
  obtain ⟨c, hc⟩ := isConj_iff.1 hu
  set x := c⁻¹ * s * c with hxdef
  have hNs : ∀ a ∈ A, a * s = s * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ (hAN ha))
  have hxo : orderOf x = 11 := by
    rw [hxdef, show c⁻¹ * s * c = (MulAut.conj c⁻¹) s by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq]
    exact hs
  have hxt : x * t = t * x := by
    have h1 := hNs u huA
    rw [← hc] at h1
    calc x * t = c⁻¹ * (s * (c * t * c⁻¹)) * c := by rw [hxdef]; group
      _ = c⁻¹ * ((c * t * c⁻¹) * s) * c := by rw [h1]
      _ = t * x := by rw [hxdef]; group
  set D := Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) with hD
  have hA'D : A.map (MulAut.conj c⁻¹).toMonoidHom ≤ D := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have h1 := hAc a ha u huA
      rw [← hc] at h1
      calc c⁻¹ * a * c * t = c⁻¹ * (a * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * t * c⁻¹) * a) * c := by rw [h1]
        _ = t * (c⁻¹ * a * c) := by group
    · have h1 := hNs a ha
      calc c⁻¹ * a * c * x = c⁻¹ * (a * s) * c := by rw [hxdef]; group
        _ = c⁻¹ * (s * a) * c := by rw [h1]
        _ = x * (c⁻¹ * a * c) := by rw [hxdef]; group
  have hcardA' : Nat.card (A.map (MulAut.conj c⁻¹).toMonoidHom) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hk]
  have h2D : 2 ^ k ∣ Nat.card D := hcardA' ▸ Subgroup.card_dvd_of_le hA'D
  have hxD : x ∈ D := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxt,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have h11D : 11 ∣ Nat.card D := hxo ▸ Subgroup.orderOf_dvd_natCard D hxD
  have hcop : Nat.Coprime 11 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hdvd : 11 * 2 ^ k ∣ Nat.card D := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h11D h2D
  have hle : 11 * 2 ^ k ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos hdvd
  have h10 : 11 * 2 ^ 10 ≤ 11 * 2 ^ k :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk10)
  have hb : Nat.card D < 11 * 2 ^ 10 := hbound x hxo hxt
  omega

theorem conj_mem_gLAPPrimeCoreOf_conj [Finite G] {p : ℕ} (hp : p.Prime) {x m n : G}
    (hn : n ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    m * n * m⁻¹ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({m * x * m⁻¹} : Set G)) := by
  set S := (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))).map
    (MulAut.conj m).toMonoidHom with hS
  have hle : S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({m * x * m⁻¹} : Set G)) := by
    refine le_GLAPPrimeCoreOf_of_normal ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_centralizer_conj_of_mem (GLAPPrimeCoreOf_le _ hy)
    · rintro g hg _ ⟨y, hy, rfl⟩
      refine ⟨(m⁻¹ * g * m) * y * (m⁻¹ * g * m)⁻¹, GLAPPrimeCoreOf_conj_mem _ ?_ y hy, ?_⟩
      · have := mem_centralizer_conj_of_mem (c := m⁻¹) hg
        simpa [mul_assoc] using this
      · simp [MulAut.conj_apply, mul_assoc]
    · rw [hS, Subgroup.card_map_of_injective (MulAut.conj m).injective]
      exact coprime_card_GLAPPrimeCoreOf hp _
  exact hle ⟨n, hn, by simp [MulAut.conj_apply]⟩

@[expose] def fourGroup (t w : G) (ht : t * t = 1) (hw : w * w = 1) (htw : t * w = w * t) :
    Subgroup G where
  carrier := {1, t, w, t * w}
  mul_mem' := by
    have e1 : t * (t * w) = w := by rw [← mul_assoc, ht, one_mul]
    have e2 : w * (t * w) = t := by rw [← mul_assoc, ← htw, mul_assoc, hw, mul_one]
    have e3 : t * w * t = w := by rw [htw, mul_assoc, ht, mul_one]
    have e4 : t * w * w = t := by rw [mul_assoc, hw, mul_one]
    have e5 : t * w * (t * w) = 1 := by rw [mul_assoc, ← mul_assoc w, ← htw, mul_assoc, hw,
      mul_one, ht]
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [ht, hw, e1, e2, e3, e4, e5, ← htw]
  one_mem' := by simp
  inv_mem' := by
    have ti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have wi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    rintro a (rfl | rfl | rfl | rfl) <;> simp [ti, wi, ← htw]

theorem gLAPPrimeCoreOf_eq_bot_of_four [Finite G] {s t w : G} (hs : orderOf s = 11)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set G)))))
    (ht : t * t = 1) (hw : w * w = 1) (htw : t * w = w * t) (ht1 : t ≠ 1) (hw1 : w ≠ 1)
    (hwt : w ≠ t) (hts : t * s = s * t) (hws : w * s = s * w)
    (hcore : GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set G)) ⊓
      Subgroup.centralizer ({t} : Set G) = ⊥)
    (htrans : ∀ v, v = w ∨ v = t * w → ∃ m : G, m * v * m⁻¹ = t ∧ ∃ k : ℕ, m * s * m⁻¹ = s ^ k) :
    GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  have h11 : Nat.Prime 11 := by norm_num
  have : Fact (Nat.Prime 11) := ⟨h11⟩
  set N := GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set G)) with hN
  set V := fourGroup t w ht hw htw with hV
  have hVs : ∀ v ∈ V, v * s = s * v := by
    rintro v (rfl | rfl | rfl | rfl)
    · simp
    · exact hts
    · exact hws
    · rw [mul_assoc, hws, ← mul_assoc, hts, mul_assoc]
  have key : ∀ u, (u = w ∨ u = t * w) → N ⊓ Subgroup.centralizer ({u} : Set G) = ⊥ := by
    intro u hu
    obtain ⟨m, hm, k, hk⟩ := htrans u hu
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨hnN, hnv⟩ := Subgroup.mem_inf.1 hn
    have h1 := conj_mem_gLAPPrimeCoreOf_conj (m := m) h11 hnN
    have hk1 : s ^ k ≠ 1 := by
      rw [← hk]
      intro h
      apply (show s ≠ 1 from fun h' => by rw [h', orderOf_one] at hs; norm_num at hs)
      have := congrArg (fun g => m⁻¹ * g * m) h
      simpa [mul_assoc] using this
    rw [hk, centralizer_pow_eq_of_prime hs hk1] at h1
    have h2 := mem_centralizer_conj_of_mem (c := m) hnv
    rw [hm] at h2
    have h3 : m * n * m⁻¹ ∈ N ⊓ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hcore, Subgroup.mem_bot] at h3
    rw [Subgroup.mem_bot]
    have := congrArg (fun g => m⁻¹ * g * m) h3
    simpa [mul_assoc] using this
  have hzero : ∀ v ∈ V, v ≠ 1 → N ⊓ Subgroup.centralizer ({v} : Set G) = ⊥ := by
    intro v hv hv1
    rcases hv with h | h | h | h
    · exact absurd h hv1
    · rw [h]; exact hcore
    · rw [h]; exact key w (Or.inl rfl)
    · rw [h]; exact key (t * w) (Or.inr rfl)
  have htw1 : t * w ≠ 1 := fun h => hwt (by
    have : w = t⁻¹ := by rw [← mul_eq_one_iff_eq_inv]; rw [← htw]; exact h
    rw [this, inv_eq_of_mul_eq_one_right ht])
  have htwt : t * w ≠ t := fun h => hw1 (by
    have := congrArg (fun g => t⁻¹ * g) h
    simpa using this)
  have htww : t * w ≠ w := fun h => ht1 (by
    have := congrArg (fun g => g * w⁻¹) h
    simpa using this)
  have hcard : Nat.card V = 2 ^ 2 := by
    have : Nat.card V = Set.ncard ({1, t, w, t * w} : Set G) := by
      rw [← Nat.card_coe_set_eq]
      rfl
    have hs1 : (1 : G) ∉ ({t, w, t * w} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm ht1, Ne.symm hw1, Ne.symm htw1⟩
    have hs2 : t ∉ ({w, t * w} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hwt, Ne.symm htwt⟩
    rw [this, Set.ncard_insert_of_notMem hs1, Set.ncard_insert_of_notMem hs2,
      Set.ncard_pair htww.symm]
    norm_num
  have hpow : ∀ v : V, v ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    show v ^ 2 = 1
    rcases hv with h | h | h | h
    · rw [h, one_pow]
    · rw [h, pow_two, ht]
    · rw [h, pow_two, hw]
    · rw [h, pow_two, mul_assoc, ← mul_assoc w, ← htw, mul_assoc, hw, mul_one, ht]
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two V N hpow hcard (fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h))
    (by
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hvC : v ∈ Subgroup.centralizer ({s} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 (hVs v hv)
      constructor
      · exact fun hy => GLAPPrimeCoreOf_conj_mem v hvC y hy
      · intro hy
        have := GLAPPrimeCoreOf_conj_mem v⁻¹ (Subgroup.inv_mem _ hvC) _ hy
        simpa [mul_assoc] using this)
  rw [hgen]
  refine le_bot_iff.1 (iSup_le fun v => iSup_le fun hv1 => ?_)
  rw [hzero v v.2 (fun h => hv1 (Subtype.ext h))]

theorem exists_eleven_subgroup_of_factorization [Finite G]
    (hG : (Nat.card G).factorization 11 = 2)
    (hinv : ∀ u : G, orderOf u = 2 →
      (Nat.card (Subgroup.centralizer ({u} : Set G))).factorization 11 ≤ 1)
    {s : G} (hs : orderOf s = 11) :
    ∃ P : Subgroup G, IsPGroup 11 P ∧ P ≤ Subgroup.centralizer ({s} : Set G) ∧
      ∀ u : G, orderOf u = 2 → ∃ g ∈ P, g * u ≠ u * g := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hsz : IsPGroup 11 (Subgroup.zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsz.exists_le_sylow
  have hQc : Nat.card (Q : Subgroup G) = 11 ^ 2 := by rw [Q.card_eq_multiplicity, hG]
  have hcomm : ∀ a ∈ (Q : Subgroup G), ∀ b ∈ (Q : Subgroup G), a * b = b * a := by
    letI := IsPGroup.commGroupOfCardEqPrimeSq hQc
    intro a ha b hb
    have := mul_comm (⟨a, ha⟩ : (Q : Subgroup G)) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hsQ : s ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers s)
  refine ⟨Q, Q.isPGroup', fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (hcomm g hg s hsQ),
    fun u hu => ?_⟩
  by_contra hall
  push_neg at hall
  have hle : (Q : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hall g hg)
  have hdvd : 11 ^ 2 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) :=
    hQc ▸ Subgroup.card_dvd_of_le hle
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').1 hdvd
  have h2 := hinv u hu
  omega

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
