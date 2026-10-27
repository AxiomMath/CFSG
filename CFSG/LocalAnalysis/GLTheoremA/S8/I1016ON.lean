module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.SevenCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section


namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.SignalizerFunctor.Helpers

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_hyperplane_fixed {p : ℕ} [Fact p.Prime] {E Q : Subgroup X}
    (hE : IsElemAbelian p E) (hEne : E ≠ ⊥) (hQ : ¬ p ∣ Nat.card Q) (hQne : Q ≠ ⊥)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set X)) :
    ∃ B : Subgroup E, B.index = p ∧ ∃ x ∈ Q, x ≠ 1 ∧ ∀ b ∈ B, (b : X) * x = x * b := by
  have : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun e =>
        Subtype.ext (by simpa using hE.2 e e.2) }
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
  let _ := conjugationAction E Q hEQ
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := Q) hQ
  by_contra hcon
  push Not at hcon
  have hbot : (⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B Q) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun B hB y hy => ?_)
    rw [Subgroup.mem_bot]
    by_contra hy1
    obtain ⟨b, hbB, hb⟩ := hcon B hB y y.2 (fun h => hy1 (Subtype.ext h))
    apply hb
    have h := congrArg Subtype.val (hy ⟨b, hbB⟩)
    change (b : X) * (y : X) * (b : X)⁻¹ = y at h
    calc (b : X) * y = (b : X) * y * (b : X)⁻¹ * b := by group
      _ = y * b := by rw [h]
  rw [hbot] at hgen
  apply hQne
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : Q) ∈ (⊥ : Subgroup Q) := hgen ▸ Subgroup.mem_top _
  simpa using congrArg Subtype.val ((Subgroup.mem_bot).mp this)

theorem false_of_sq_normalizes_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E V : Subgroup X}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hEV : E ≤ Subgroup.normalizer (V : Set X))
    (hinv : ∀ t : X, orderOf t = 2 → ¬ p ^ 2 ∣ Nat.card (Subgroup.centralizer ({t} : Set X)))
    (hcent : ∀ f : X, orderOf f = p → ∀ W : Subgroup X, IsPGroup 2 W →
      W ≤ Subgroup.centralizer ({f} : Set X) → Nat.card W ≡ 1 [MOD p] → W = ⊥) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    have := hp.one_lt
    nlinarith
  have hVp : ¬ p ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hV)
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨B, hBi, x, hxV, hx1, hBx⟩ := exists_hyperplane_fixed hE hEne hVp hV1 hEV
  have hBcard : Nat.card B = p := by
    have h := Subgroup.card_mul_index B
    rw [hBi, Nat.card_congr (Equiv.refl E), hEcard] at h
    have hp0 := hp.pos
    nlinarith
  obtain ⟨f₀, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot B).mp (hBcard ▸ hp.one_lt))
  set f : E := (f₀ : E) with hfdef
  have hfB : f ∈ B := f₀.2
  set f' : X := (f : X) with hf'
  have hf'E : f' ∈ E := f.2
  have hf'1 : f' ≠ 1 := by
    intro h
    apply hf1
    exact Subtype.ext (Subtype.ext h)
  have hfo : orderOf f' = p := orderOf_eq_prime (hE.2 f' hf'E) hf'1
  set V₁ : Subgroup X := V ⊓ Subgroup.centralizer ({f'} : Set X) with hV₁
  have hxV₁ : x ∈ V₁ := ⟨hxV, Subgroup.mem_centralizer_singleton_iff.mpr (hBx f hfB).symm⟩
  have hV₁ne : V₁ ≠ ⊥ := fun h => hx1 ((Subgroup.mem_bot).mp (h ▸ hxV₁))
  have hV₁2 : IsPGroup 2 V₁ := hV.to_le inf_le_left
  have hEC : E ≤ Subgroup.centralizer ({f'} : Set X) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f', hf'E⟩))
  have hEV₁ : E ≤ Subgroup.normalizer (V₁ : Set X) :=
    (le_inf hEV (hEC.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  let _ := conjugationAction E V₁ hEV₁
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  have hmod := hEp.card_modEq_card_fixedPoints (α := V₁)
  obtain ⟨y, hyfix, hy1⟩ : ∃ y : V₁, y ∈ MulAction.fixedPoints E V₁ ∧ y ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 : Nat.card (MulAction.fixedPoints E V₁) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((hno a a.2).trans (hno b b.2).symm)⟩,
        ⟨⟨1, fun e => smul_one e⟩⟩⟩
    rw [h1] at hmod
    exact hV₁ne (hcent f' hfo V₁ hV₁2 inf_le_right hmod)
  have hy1' : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have h2y : 2 ∣ Nat.card (Subgroup.zpowers (y : X)) := by
    rw [Nat.card_zpowers]
    obtain ⟨k, hk⟩ := hV₁2 y
    have hdvd : orderOf (y : X) ∣ 2 ^ k := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hm]
    rcases m with _ | m
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hm)) hy1'
    · exact dvd_pow_self 2 (Nat.succ_ne_zero m)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers (y : X)) 2 h2y
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp t.2
  have hto : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  apply hinv t hto
  rw [← hEcard]
  refine Subgroup.card_dvd_of_le fun e he => ?_
  have hey : Commute e (y : X) := by
    have h := congrArg Subtype.val (hyfix ⟨e, he⟩)
    change e * (y : X) * e⁻¹ = y at h
    calc e * (y : X) = e * y * e⁻¹ * e := by group
      _ = y * e := by rw [h]
  rw [Subgroup.mem_centralizer_singleton_iff, ← hn]
  exact (hey.zpow_right n).eq

theorem elemAbelian_of_le {p : ℕ} {E F : Subgroup X} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (by
    simpa using congrArg Subtype.val (hE.1.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩))⟩⟩,
    fun x hx => hE.2 x (hFE hx)⟩

theorem exists_orderOf_two_mem_zpowers {x : X} (hx1 : x ≠ 1) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    ∃ t ∈ Subgroup.zpowers x, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    rw [hm]
    rcases m with _ | m
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hm)) hx1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero m)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) 2 h2
  exact ⟨t, t.2, by rw [← Subgroup.orderOf_coe] at ht; exact ht⟩

theorem card_le_of_involution_centralizers {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E V : Subgroup X} (hE : IsElemAbelian p E) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hEV : E ≤ Subgroup.normalizer (V : Set X))
    (hC : ∀ t : X, orderOf t = 2 → ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) →
      IsPGroup p F → Nat.card F ≤ p ^ k) :
    Nat.card E ≤ p ^ (k + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hEne : E = ⊥
  · rw [hEne, Subgroup.card_bot]
    exact Nat.one_le_pow _ _ hp.pos
  have hVp : ¬ p ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hV)
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨B, hBi, x, hxV, hx1, hBx⟩ := exists_hyperplane_fixed hE hEne hVp hV1 hEV
  obtain ⟨k', hk'⟩ := hV ⟨x, hxV⟩
  obtain ⟨t, ht, hto⟩ := exists_orderOf_two_mem_zpowers hx1
    (k := k') (by simpa using congrArg Subtype.val hk')
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hBmap : B.map E.subtype ≤ Subgroup.centralizer ({x ^ n} : Set X) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.zpow_right (hBx b hb) n).eq
  have hcard := hC _ hto _ hBmap ((hEp.to_subgroup B).map E.subtype)
  rw [Subgroup.card_map_of_injective E.subtype_injective] at hcard
  have h := Subgroup.card_mul_index B
  rw [hBi] at h
  rw [← h, pow_succ]
  exact Nat.mul_le_mul_right p hcard

end General

section ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7 CFSG.ONSchreier

theorem false_of_seven_sq_normalizes_two_ON
    {T : Type} [Group T] [Finite T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {E V : Subgroup T} (hE : IsElemAbelian 7 E)
    (hEcard : Nat.card E = 7 ^ 2) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hEV : E ≤ Subgroup.normalizer (V : Set T)) : False := by
  refine false_of_sq_normalizes_two (by norm_num) (by norm_num) hE hEcard hV hV1 hEV
    (fun t ht => ?_) (fun f hf W hW hWC hmod => ?_)
  · set φ : T ≃* Pv := e.trans onEquivPv
    rw [← card_centralizer_map_equiv φ t,
      CFSG.EvenSporadicStandard.Solomon78.pv_card_centralizer (φ t)
        (by rw [MulEquiv.orderOf_eq]; exact ht)]
    norm_num
  · have hdvd := Subgroup.card_dvd_of_le hWC
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
    rw [← Subgroup.card_eq_one, hk]
    rw [hk] at hdvd hmod
    have hle : 2 ^ k ≤ 1372 := by
      rcases card_centralizer_seven_ON e hf with h | h <;> rw [h] at hdvd <;>
        exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
    have hk11 : k < 11 := by
      by_contra hk11
      push Not at hk11
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk11
      omega
    rcases card_centralizer_seven_ON e hf with h | h <;> rw [h] at hdvd <;>
      interval_cases k <;>
      first | exact absurd hmod (by decide) | exact absurd hdvd (by decide) | rfl

theorem pow_le_of_dvd_card_ON {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    (h : p ^ n ∣ 460815505920) : p ^ n ≤ p := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simpa using hp.one_lt.le
    · simp
  exfalso
  have h2 : p ^ 2 ∣ 460815505920 := (pow_dvd_pow p hn).trans h
  have h1 : p ∣ 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31 :=
    (dvd_pow_self p two_ne_zero).trans (by norm_num at h2 ⊢; exact h2)
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h => (Nat.prime_dvd_prime_iff_eq hp hq).1 h
  simp only [hp.dvd_mul] at h1
  rcases h1 with ((((((h | h) | h) | h) | h) | h) | h)
  · exact hp2 (key 2 (by norm_num) (hp.dvd_of_dvd_pow h))
  · exact hp3 (key 3 (by norm_num) (hp.dvd_of_dvd_pow h))
  · rw [key 5 (by norm_num) h] at h2; norm_num at h2
  · exact hp7 (key 7 (by norm_num) (hp.dvd_of_dvd_pow h))
  · rw [key 11 (by norm_num) h] at h2; norm_num at h2
  · rw [key 19 (by norm_num) h] at h2; norm_num at h2
  · rw [key 31 (by norm_num) h] at h2; norm_num at h2

theorem i1016_ON_native
    {T : Type} [Group T] [Finite T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E V : Subgroup T} (hE : IsElemAbelian p E) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hEV : E ≤ Subgroup.normalizer (V : Set T)) :
    (p = 3 ∧ Nat.card E ≤ 3 ^ 3) ∨ Nat.card E ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hcardT : Nat.card T = 460815505920 := by
    rw [Nat.card_congr (e.trans CFSG.Sporadic.ON.onEquivJ).toEquiv, CFSG.Sporadic.ON.card_J]
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  have hdvd : p ^ n ∣ 460815505920 := hn ▸ hcardT ▸ Subgroup.card_subgroup_dvd_card E
  by_cases h3 : p = 3
  · subst h3
    refine Or.inl ⟨rfl, card_le_of_involution_centralizers (k := 2) Nat.prime_three (by norm_num)
      hE hV hV1 hEV fun t ht F hF hFp => ?_⟩
    set φ : T ≃* Pv := e.trans onEquivPv
    have hCt : Nat.card (Subgroup.centralizer ({t} : Set T)) = 161280 := by
      rw [← card_centralizer_map_equiv φ t,
        CFSG.EvenSporadicStandard.Solomon78.pv_card_centralizer (φ t)
          (by rw [MulEquiv.orderOf_eq]; exact ht)]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFp
    have hFd : 3 ^ m ∣ 161280 := hm ▸ hCt ▸ Subgroup.card_dvd_of_le hF
    rw [hm]
    have hm3 : m < 3 := by
      by_contra hm3
      push Not at hm3
      exact absurd ((pow_dvd_pow 3 hm3).trans hFd) (by norm_num)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  right
  rw [hn]
  by_cases h7 : p = 7
  · subst h7
    by_contra hlt
    push Not at hlt
    have hn2 : 2 ≤ n := by
      by_contra hn2
      push Not at hn2
      interval_cases n <;> simp at hlt
    have h49 : 7 ^ 2 ∣ Nat.card E := hn ▸ pow_dvd_pow 7 hn2
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 7 h49
    refine false_of_seven_sq_normalizes_two_ON e (E := P.map E.subtype) ?_ ?_ hV hV1 ?_
    · refine elemAbelian_of_le hE ?_
      rintro _ ⟨a', -, rfl⟩
      exact a'.2
    · rw [Subgroup.card_map_of_injective E.subtype_injective, hP]
    · rintro _ ⟨a', -, rfl⟩
      exact hEV a'.2
  · exact pow_le_of_dvd_card_ON hp hp2 h3 h7 hdvd

end ON

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
