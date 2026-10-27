module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Two
public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Fin

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_invol {t s : G} (ht : t * t = 1) (hs : s ∈ Subgroup.zpowers t) :
    s = 1 ∨ s = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]
    simp

omit [Finite G] in
theorem conj_mem_iff {N : Subgroup G} {t x : G} (ht : t ∈ N) : t * x * t⁻¹ ∈ N ↔ x ∈ N := by
  constructor
  · intro h
    have := N.mul_mem (N.mul_mem (N.inv_mem ht) h) ht
    simpa [mul_assoc] using this
  · intro h
    exact N.mul_mem (N.mul_mem ht h) (N.inv_mem ht)

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem part_two (h3 : Theorem3Statement) (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀)
    (hth : Three M J) {g : G} (hg : g ∉ M) {t₀ : G} (ht₀J : t₀ ∈ rightConjugate J g)
    (ht₀M : t₀ ∈ M) (ht₀1 : t₀ ≠ 1) (ht₀2 : t₀ * t₀ = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJgM : rightConjugate J g ≤ rightConjugate M g := Subgroup.map_mono c.le
  have hgood₀ : Good M J g (Subgroup.zpowers t₀) := by
    obtain ⟨b, hb, hb1, hb2⟩ := hth.exists_notin J (rightConjugate J t₀)
    refine ⟨L54.isPGroup_zpowers (twoElem_of_mul_self ht₀2),
      Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨ht₀J, ht₀M⟩), b, hb, ?_⟩
    intro s hs
    rcases mem_zpowers_invol ht₀2 hs with rfl | rfl
    · rw [rightConjugate_one]
      exact fun h => hb1 h.symm
    · exact fun h => hb2 h.symm
  obtain ⟨T, ⟨hT2, hTle, b, hb, hnd⟩, hmax⟩ := exists_maxGood ⟨_, hgood₀⟩
  have hTJ : T ≤ rightConjugate J g := hTle.trans inf_le_left
  have hTM : T ≤ M := hTle.trans inf_le_right
  have hT0 : T ≠ ⊥ := by
    intro hbot
    have h1 := hmax _ hgood₀
    have h2 : Nat.card (Subgroup.zpowers t₀) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact ht₀2) ht₀1
    rw [hbot, Subgroup.card_bot, h2] at h1
    omega
  obtain ⟨⟨a, haJ, haa, haMg, ka, hka, hnca⟩, ⟨a', ha'Jg, ha'a', ha'M, k', hk', hnca'⟩⟩ :=
    c.exists_two_noncentral hA hz₀ hg hT2 hTJ hTM hT0 hb hnd
  set X := Lgen J T ⊓ rightConjugate M g with hX
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := by
    intro t ht
    have h1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_Lgen J T ht)
    have h2 := Subgroup.mem_normalizer_iff.1
      (Subgroup.le_normalizer (H := rightConjugate M g) (hJgM (hTJ ht)))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hX, Subgroup.mem_inf]
    rw [h1 x, h2 x]
  obtain ⟨Q, hQ, hTQ⟩ := L54.exists_invariant_sylow hT2 hTX
  have hQ2 : IsPGroup 2 Q := hQ.isPGroup
  have hQX : Q ≤ X := hQ.le
  have hQL : Q ≤ Lgen J T := hQX.trans inf_le_left
  have hQMg : Q ≤ rightConjugate M g := hQX.trans inf_le_right
  have hQT : Q ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨hsQ, hsT⟩ := Subgroup.mem_inf.1 hs
    rw [Subgroup.mem_bot]
    by_contra hs1
    obtain ⟨c', hc', hX1, -⟩ := hth.exists_notin_g g (rightConjugate J g) (rightConjugate J g)
    refine hg (c.kp_g hs1 (two_elem_of_mem hQ2 hsQ) hb hc' ?_ ?_)
    · intro x hx
      exact (c.Lgen_comm hTM hb hnd s (hQL hsQ) x hx).symm
    · intro x hx
      refine (c.comm_conj_g g M.one_mem hc' ?_ ?_ hx).symm
      · rw [one_mul]
        exact fun h => hX1 h.symm
      · rw [one_mul]
        exact hTJ hsT
  have hQN : Q ≤ Subgroup.normalizer (T : Set G) := by
    by_contra hnot
    set R := Q ⊓ Subgroup.normalizer (T : Set G) with hR
    have hTR : T ≤ Subgroup.normalizer (R : Set G) := by
      intro t ht
      have h1 := Subgroup.mem_normalizer_iff.1 (hTQ ht)
      have hNT : t ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hR, Subgroup.mem_inf]
      rw [h1 x, conj_mem_iff hNT]
    set K := T ⊔ R with hK
    set H := T ⊔ Q with hH
    have hH2 : IsPGroup 2 H := hT2.to_sup_of_normal_right' hQ2 hTQ
    have hKH : K ≤ H := sup_le_sup_left inf_le_left T
    have hKN : K ≤ Subgroup.normalizer (T : Set G) :=
      sup_le Subgroup.le_normalizer inf_le_right
    have hKne : K ≠ H := by
      intro hKH'
      apply hnot
      intro q hq
      exact hKN (hKH' ▸ (le_sup_right : Q ≤ H) hq)
    obtain ⟨y, hyH, hyK, hyKn⟩ := L54.exists_mem_normalizer_not_mem hH2 hKH hKne
    obtain ⟨t, ht, q, hq, rfl⟩ := exists_mul_of_mem_sup hTQ hyH
    have hqK : q ∈ Subgroup.normalizer (K : Set G) := by
      have ht' : t ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.le_normalizer (le_sup_left (a := T) (b := R) ht)
      have := Subgroup.mul_mem _ ((Subgroup.normalizer (K : Set G)).inv_mem ht') hyK
      simpa using this
    have hqnK : q ∉ K := fun hq' => hyKn (K.mul_mem (le_sup_left (a := T) (b := R) ht) hq')
    have hqnN : q ∉ Subgroup.normalizer (T : Set G) := fun hqN =>
      hqnK (le_sup_right (a := T) (b := R) ⟨hq, hqN⟩)
    have hexs : ∃ s ∈ T, q⁻¹ * s * q ∉ T := by
      by_contra hno
      push Not at hno
      apply hqnN
      have hle : rightConjugate T q ≤ T := by
        intro x hx
        rw [mem_rightConjugate_iff] at hx
        have := hno (q * x * q⁻¹) hx
        simpa [mul_assoc] using this
      have heq : rightConjugate T q = T :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
      exact (rightConjugate_eq_self_iff T q).1 heq
    obtain ⟨s, hsT, hsq⟩ := hexs
    set x := q⁻¹ * s * q with hxdef
    have hxK : x ∈ K := by
      have : q * x * q⁻¹ ∈ K := by
        have e : q * x * q⁻¹ = s := by rw [hxdef]; group
        rw [e]
        exact le_sup_left (a := T) (b := R) hsT
      exact (Subgroup.mem_normalizer_iff.1 hqK x).2 this
    obtain ⟨t', ht', r, hr, htr⟩ := exists_mul_of_mem_sup hTR hxK
    have hrQ : r ∈ Q := (Subgroup.mem_inf.1 hr).1
    have hr1 : r ≠ 1 := by
      rintro rfl
      have : x = t' := by rw [← htr, mul_one]
      exact hsq (this ▸ ht')
    have hrdef : r = t'⁻¹ * x := by rw [← htr]; group
    have hm₀ : g * q * g⁻¹ ∈ M := (mem_rightConjugate_iff _ _ _).1 (hQMg hq)
    have hxJ : x ∈ rightConjugate J (g * q * g⁻¹ * g) := by
      rw [mem_rightConjugate_iff]
      have e : g * q * g⁻¹ * g * x * (g * q * g⁻¹ * g)⁻¹ = g * s * g⁻¹ := by
        rw [hxdef]
        group
      rw [e]
      exact (mem_rightConjugate_iff _ _ _).1 (hTJ hsT)
    obtain ⟨c', hc', hX1, hX2⟩ :=
      hth.exists_notin_g g (rightConjugate J g) (rightConjugate J (g * q * g⁻¹ * g))
    refine hg (c.kp_g hr1 (two_elem_of_mem hQ2 hrQ) hb hc' ?_ ?_)
    · intro y hy
      exact (c.Lgen_comm hTM hb hnd r (hQL hrQ) y hy).symm
    · intro y hy
      have h1 : t'⁻¹ * y = y * t'⁻¹ := by
        refine c.comm_conj_g g M.one_mem hc' ?_ ?_ hy
        · rw [one_mul]
          exact fun h => hX1 h.symm
        · rw [one_mul]
          exact (rightConjugate J g).inv_mem (hTJ ht')
      have h2 : x * y = y * x := c.comm_conj_g g hm₀ hc' (fun h => hX2 h.symm) hxJ hy
      rw [hrdef]
      calc y * (t'⁻¹ * x) = (y * t'⁻¹) * x := by group
        _ = (t'⁻¹ * y) * x := by rw [← h1]
        _ = t'⁻¹ * (y * x) := by group
        _ = t'⁻¹ * (x * y) := by rw [← h2]
        _ = t'⁻¹ * x * y := by group
  have hQcomm : ∀ q ∈ Q, ∀ s ∈ T, q * s = s * q := by
    intro q hq s hs
    have h1 : q * s * q⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hQN hq) s).1 hs
    have h2 : s * q⁻¹ * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 (hTQ hs) q⁻¹).1 (Q.inv_mem hq)
    have hc : q * s * q⁻¹ * s⁻¹ ∈ Q ⊓ T := by
      refine ⟨?_, T.mul_mem h1 (T.inv_mem hs)⟩
      have := Q.mul_mem hq h2
      simpa [mul_assoc] using this
    rw [hQT, Subgroup.mem_bot] at hc
    calc q * s = (q * s * q⁻¹ * s⁻¹) * (s * q) := by group
      _ = s * q := by rw [hc, one_mul]
  have haX : a ∈ X := Subgroup.mem_inf.2 ⟨le_Lgen J T haJ, haMg⟩
  obtain ⟨x, hxX, hxQ⟩ := L54.exists_conj_mem_sylow hQ haX (twoElem_of_mul_self haa)
  have hxN : x ∈ Subgroup.normalizer (J : Set G) :=
    c.Lgen_le_normalizer hTM (Subgroup.mem_inf.1 hxX).1
  have ha₁J : x * a * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hxN a).1 haJ
  have hk₁J : x * ka * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hxN ka).1 hka
  have hnc₁ : (x * a * x⁻¹) * (x * ka * x⁻¹) ≠ (x * ka * x⁻¹) * (x * a * x⁻¹) := by
    intro h
    apply hnca
    have e1 : x * a * x⁻¹ * (x * ka * x⁻¹) = x * (a * ka) * x⁻¹ := by group
    have e2 : x * ka * x⁻¹ * (x * a * x⁻¹) = x * (ka * a) * x⁻¹ := by group
    rw [e1, e2] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := by
    intro s hs
    rw [← rightConjugate_eq_self_iff]
    by_contra hne
    have ha₁s : x * a * x⁻¹ ∈ rightConjugate J s := by
      rw [mem_rightConjugate_iff]
      have hcs := hQcomm _ hxQ s hs
      have : s * (x * a * x⁻¹) * s⁻¹ = x * a * x⁻¹ := by
        calc s * (x * a * x⁻¹) * s⁻¹ = (x * a * x⁻¹) * s * s⁻¹ := by rw [hcs]
          _ = x * a * x⁻¹ := by group
      rw [this]
      exact ha₁J
    exact hnc₁ (c.comm_J (hTM hs) hne hk₁J ha₁s).symm
  have hJLT : Lgen J T = J := by
    refine le_antisymm ?_ (le_Lgen J T)
    unfold Lgen
    refine iSup₂_le fun s hs => ?_
    rw [(rightConjugate_eq_self_iff J s).2 (hTN hs)]
  have hTZ : ∃ t ∈ T, ∃ k ∈ rightConjugate J g, t * k ≠ k * t := by
    by_contra hnot
    push Not at hnot
    have ha'2 : ∃ n : ℕ, a' ^ 2 ^ n = 1 := twoElem_of_mul_self ha'a'
    have hTn : T ≤ Subgroup.normalizer ((Subgroup.zpowers a' : Subgroup G) : Set G) := fun t ht =>
      mem_normalizer_zpowers (hnot t ht a' ha'Jg)
    have hT₂2 : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers a') :=
      hT2.to_sup_of_normal_right' (L54.isPGroup_zpowers ha'2) hTn
    obtain ⟨b', hb', hb1', hb2'⟩ := hth.exists_notin J (rightConjugate J a')
    have hgood : Good M J g (T ⊔ Subgroup.zpowers a') := by
      refine ⟨hT₂2, sup_le hTle (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨ha'Jg, ha'M⟩)),
        b', hb', ?_⟩
      intro s hs
      obtain ⟨t, ht, z, hz, rfl⟩ := exists_mul_of_mem_sup hTn hs
      rw [← rightConjugate_mul, (rightConjugate_eq_self_iff J t).2 (hTN ht)]
      rcases mem_zpowers_invol ha'a' hz with rfl | rfl
      · rw [rightConjugate_one]
        exact fun h => hb1' h.symm
      · exact fun h => hb2' h.symm
    have hle := hmax _ hgood
    have hlt : T < T ⊔ Subgroup.zpowers a' := by
      refine lt_of_le_of_ne le_sup_left fun heq => ?_
      have ha'T : a' ∈ T := by
        rw [heq]
        exact (le_sup_right : Subgroup.zpowers a' ≤ T ⊔ Subgroup.zpowers a')
          (Subgroup.mem_zpowers a')
      exact hnca' (hnot a' ha'T k' hk')
    exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.2 hle)
  have hQNg : Q ≤ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
    intro q hq
    rw [← rightConjugate_eq_self_iff]
    by_contra hne
    have hm₀ : g * q * g⁻¹ ∈ M := (mem_rightConjugate_iff _ _ _).1 (hQMg hq)
    have hJq : rightConjugate (rightConjugate J g) q = rightConjugate J (g * q * g⁻¹ * g) := by
      rw [rightConjugate_mul]
      congr 1
      group
    obtain ⟨t, ht, k, hk, hnct⟩ := hTZ
    apply hnct
    have hts : t ∈ rightConjugate J (g * q * g⁻¹ * g) := by
      rw [← hJq, mem_rightConjugate_iff]
      have : q * t * q⁻¹ = t := by
        calc q * t * q⁻¹ = t * q * q⁻¹ := by rw [hQcomm q hq t ht]
          _ = t := by group
      rw [this]
      exact hTJ ht
    have hk' : k ∈ rightConjugate J (1 * g) := by rwa [one_mul]
    have hne' : rightConjugate J (1 * g) ≠ rightConjugate J (g * q * g⁻¹ * g) := by
      rw [one_mul, ← hJq]
      exact fun h => hne h.symm
    exact (c.comm_conj_g g M.one_mem hm₀ hne' hk' hts).symm
  have ha₁Q : x * a * x⁻¹ ∈ Q := hxQ
  have ha₁1 : x * a * x⁻¹ ≠ 1 := by
    intro h
    apply hnc₁
    rw [h]
    simp
  have hE : ∀ E : Subgroup G, IsPGroup 2 E → E ≤ rightConjugate J g →
      (∀ e ∈ E, ∀ q ∈ Q, e * q = q * e) → Nat.card E ≤ Nat.card T := by
    intro E hE2 hEJ hEQ
    have hEM : E ≤ M := fun e he =>
      c.centralizer_le_of_mem ha₁J (two_elem_of_mem hQ2 ha₁Q) ha₁1
        (Subgroup.mem_centralizer_singleton_iff.2 (hEQ e he _ ha₁Q))
    have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (J : Set G) := by
      intro e he
      rw [← rightConjugate_eq_self_iff]
      by_contra hne
      have ha₁e : x * a * x⁻¹ ∈ rightConjugate J e := by
        rw [mem_rightConjugate_iff]
        have hce := hEQ e he _ ha₁Q
        have : e * (x * a * x⁻¹) * e⁻¹ = x * a * x⁻¹ := by
          calc e * (x * a * x⁻¹) * e⁻¹ = (x * a * x⁻¹) * e * e⁻¹ := by rw [hce]
            _ = x * a * x⁻¹ := by group
        rw [this]
        exact ha₁J
      exact hnc₁ (c.comm_J (hEM he) hne hk₁J ha₁e).symm
    obtain ⟨a₂, ha₂, ha₂1⟩ := c.exists_conj_ne
    refine hmax E ⟨hE2, le_inf hEJ hEM, a₂, ha₂, fun s hs => ?_⟩
    rw [(rightConjugate_eq_self_iff J s).2 (hEN s hs)]
    exact fun h => ha₂1 h.symm
  by_cases hQT_le : Nat.card Q ≤ Nat.card T
  · obtain ⟨t₁, ht₁T, ht₁1, ht₁2⟩ := L54.exists_involution_of_isPGroup hT2 hT0
    refine c.fin h3 hth hg hT2 hTJ hTN hTZ ?_
    intro E hE2 hEJ hEc
    have hEX : E ≤ X := by
      intro e he
      refine Subgroup.mem_inf.2 ⟨le_Lgen J T (hEJ he), ?_⟩
      exact c.centralizer_le_conj (hTJ ht₁T) (twoElem_of_mul_self ht₁2) ht₁1
        (Subgroup.mem_centralizer_singleton_iff.2 (hEc e he t₁ ht₁T))
    exact (card_le_of_isSylowOf hQ hEX hE2).trans hQT_le
  · push Not at hQT_le
    have hc' := c.transport g
    have hJ' : rightConjugate (rightConjugate J g) g⁻¹ = J := by
      rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have hg' : g⁻¹ ∉ rightConjugate M g := by
      intro hmem
      rw [mem_rightConjugate_iff] at hmem
      apply hg
      simpa using M.inv_mem (by simpa using hmem)
    refine hc'.fin h3 (hth.transport g) hg' hQ2 ?_ hQNg ?_ ?_
    · rw [hJ']
      rw [hJLT] at hQL
      exact hQL
    · rw [hJ']
      exact ⟨x * a * x⁻¹, ha₁Q, x * ka * x⁻¹, hk₁J, hnc₁⟩
    · intro E hE2 hEJ hEc
      exact (hE E hE2 hEJ hEc).trans hQT_le.le

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
