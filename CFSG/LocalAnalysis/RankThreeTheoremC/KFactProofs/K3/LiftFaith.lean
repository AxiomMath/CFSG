module

public import CFSG.RankThree.PartTwo.Sec5.Bender.Core
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms


public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open Subgroup CFSG.Open
open scoped commutatorElement

theorem fn_card_eq_prime_pow_of_ne_top {V : Type} [Group V] [Finite V] {q : ℕ} [Fact q.Prime]
    {k : ℕ} (hV : Nat.card V = q ^ k) {W : Subgroup V} (hW : W ≠ ⊤) :
    ∃ m < k, Nat.card W = q ^ m := by
  have hdvd : Nat.card W ∣ q ^ k := by
    rw [← hV]
    exact Subgroup.card_subgroup_dvd_card W
  obtain ⟨m, hm, hWm⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).1 hdvd
  refine ⟨m, lt_of_le_of_ne hm ?_, hWm⟩
  rintro rfl
  exact hW (Subgroup.eq_top_of_card_eq W (hWm.trans hV.symm))

theorem fn_sup_eq_top {V : Type} [Group V] [Finite V] {q : ℕ} [Fact q.Prime]
    (hV : Nat.card V = q ^ 2) {W₁ W₂ : Subgroup V} (h₁ : Nat.card W₁ = q)
    (h₂ : Nat.card W₂ = q) (hne : W₁ ≠ W₂) : W₁ ⊔ W₂ = ⊤ := by
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hlt : W₁ < W₁ ⊔ W₂ := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have hW2 : W₂ ≤ W₁ := le_of_le_of_eq le_sup_right h.symm
    exact (Subgroup.eq_of_le_of_card_ge hW2 (h₁.trans h₂.symm).le).symm
  have hlt' : Nat.card W₁ < Nat.card (W₁ ⊔ W₂ : Subgroup V) := Subgroup.card_lt_of_lt hlt
  rw [h₁] at hlt'
  have hdvd : Nat.card (W₁ ⊔ W₂ : Subgroup V) ∣ q ^ 2 := by
    rw [← hV]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).1 hdvd
  have hj2 : j = 2 := by
    interval_cases j
    · rw [hjc, pow_zero] at hlt'
      omega
    · rw [hjc, pow_one] at hlt'
      omega
    · rfl
  subst hj2
  exact Subgroup.eq_top_of_card_eq _ (hjc.trans hV.symm)

theorem fn_iSup_ne_top_of_all_bot {V B : Type} [Group V] [Finite V] [Group B] {n : ℕ}
    [MulDistribMulAction B V] (hV : 1 < Nat.card V)
    (hall : ∀ H : Subgroup B, H.index = n → CFSG.fixedPointSubgroup H V = ⊥) :
    (⨆ (B₀ : Subgroup B) (_ : B₀.index = n), CFSG.fixedPointSubgroup B₀ V) ≠ ⊤ := by
  intro htop
  have hbot : (⨆ (B₀ : Subgroup B) (_ : B₀.index = n), CFSG.fixedPointSubgroup B₀ V) = ⊥ :=
    iSup₂_eq_bot.mpr fun H hH => hall H hH
  rw [hbot] at htop
  have h := congrArg (fun H : Subgroup V => Nat.card H) htop
  simp only [Subgroup.card_bot, Subgroup.card_top] at h
  omega

theorem fn_exists_pair {V B : Type} [Group V] [Finite V] [Group B] [MulDistribMulAction B V]
    {q : ℕ} [Fact q.Prime] (hk : Nat.card V = q ^ 2)
    (hsup : (⨆ (B₀ : Subgroup B) (_ : B₀.index = 3), CFSG.fixedPointSubgroup B₀ V) = ⊤)
    (hproper : ∀ H : Subgroup B, H.index = 3 → CFSG.fixedPointSubgroup H V ≠ ⊤) :
    ∃ H₁ H₂ : Subgroup B, H₁.index = 3 ∧ H₂.index = 3 ∧
      Nat.card (CFSG.fixedPointSubgroup H₁ V) = q ∧
      Nat.card (CFSG.fixedPointSubgroup H₂ V) = q ∧
      CFSG.fixedPointSubgroup H₁ V ≠ CFSG.fixedPointSubgroup H₂ V := by
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hcardq : ∀ H : Subgroup B, H.index = 3 →
      Nat.card (CFSG.fixedPointSubgroup H V) = 1 ∨ Nat.card (CFSG.fixedPointSubgroup H V) = q := by
    intro H hH
    obtain ⟨m, hm, hmq⟩ := fn_card_eq_prime_pow_of_ne_top hk (hproper H hH)
    interval_cases m
    · exact Or.inl (by rw [hmq, pow_zero])
    · exact Or.inr (by rw [hmq, pow_one])
  by_contra hno
  by_cases hex : ∃ H₀ : Subgroup B, H₀.index = 3 ∧
      Nat.card (CFSG.fixedPointSubgroup H₀ V) = q
  ·
    obtain ⟨H₁, hH₁, hq₁⟩ := hex
    have hle : ∀ H : Subgroup B, H.index = 3 →
        CFSG.fixedPointSubgroup H V ≤ CFSG.fixedPointSubgroup H₁ V := by
      intro H hH
      rcases hcardq H hH with h1 | hq
      · rw [Subgroup.eq_bot_of_card_eq _ h1]
        exact bot_le
      · have heq : CFSG.fixedPointSubgroup H V = CFSG.fixedPointSubgroup H₁ V := by
          by_contra hne
          exact hno ⟨H, H₁, hH, hH₁, hq, hq₁, hne⟩
        exact heq.le
    have hle' : (⨆ (B₀ : Subgroup B) (_ : B₀.index = 3), CFSG.fixedPointSubgroup B₀ V) ≤
        CFSG.fixedPointSubgroup H₁ V :=
      iSup₂_le fun H hH => hle H hH
    rw [hsup, top_le_iff] at hle'
    exact hproper H₁ hH₁ hle'
  ·
    have hall : ∀ H : Subgroup B, H.index = 3 → CFSG.fixedPointSubgroup H V = ⊥ := by
      intro H hH
      rcases hcardq H hH with h1 | hq
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact (hex ⟨H, hH, hq⟩).elim
    exact fn_iSup_ne_top_of_all_bot (by rw [hk]; nlinarith) hall hsup

theorem fn_inf_eq_bot {V B : Type} [Group V] [Finite V] [Group B] [MulDistribMulAction B V]
    (ρ : B →* MulAut V) (hρ : Function.Injective ρ) (hact : ∀ (b : B) (v : V), b • v = ρ b v)
    {H₁ H₂ : Subgroup B}
    (hjoin : CFSG.fixedPointSubgroup H₁ V ⊔ CFSG.fixedPointSubgroup H₂ V = ⊤) :
    H₁ ⊓ H₂ = ⊥ := by
  rw [eq_bot_iff_forall]
  intro b hb
  obtain ⟨hb₁, hb₂⟩ := Subgroup.mem_inf.mp hb
  have hle : CFSG.fixedPointSubgroup H₁ V ⊔ CFSG.fixedPointSubgroup H₂ V ≤
      CFSG.fixedPointSubgroup (Subgroup.zpowers b) V :=
    sup_le (fun w hw => (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff b w).mpr
        (hw ⟨b, hb₁⟩))
      (fun w hw => (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff b w).mpr
        (hw ⟨b, hb₂⟩))
  rw [hjoin] at hle
  have hρb : ρ b = 1 := by
    apply MulEquiv.ext
    intro v
    exact (hact b v).symm.trans
      ((CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff b v).mp (hle (Subgroup.mem_top v)))
  exact hρ (hρb.trans (map_one ρ).symm)

theorem no_faithful_E27_small {V B : Type} [Group V] [Finite V] [Group B] [Finite B] {q : ℕ}
    [Fact q.Prime] (hq3 : q ≠ 3) (hVab : ∀ a b : V, a * b = b * a) (hVq : IsPGroup q V)
    (hV : Nat.card V ≤ q ^ 2) (hBab : ∀ a b : B, a * b = b * a) (hB3 : ∀ b : B, b ^ 3 = 1)
    (hB27 : Nat.card B = 27) (ρ : B →* MulAut V) (hρ : Function.Injective ρ) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hBm : IsMulCommutative B := ⟨⟨hBab⟩⟩
  haveI : IsElementaryAbelian 3 B :=
    { toIsMulCommutative := hBm, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hB3 }
  haveI : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hB27]; norm_num)
  letI : MulDistribMulAction B V := MulDistribMulAction.compHom V ρ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hVq
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hk2 : k ≤ 2 := by
    have h : q ^ k ≤ q ^ 2 := by rw [← hk]; exact hV
    exact (Nat.pow_le_pow_iff_right hq1).mp h
  have hndvd : ¬ 3 ∣ Nat.card V := by
    rw [hk]
    intro h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : q.Prime)).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hsup : (⨆ (B₀ : Subgroup B) (_ : B₀.index = 3), CFSG.fixedPointSubgroup B₀ V) = ⊤ := by
    letI : CommGroup V := { ‹Group V› with mul_comm := hVab }
    exact CFSG.SolvableHall.abelian_hyperplane_generation hndvd
  have hcard9 : ∀ H : Subgroup B, H.index = 3 → Nat.card H = 9 := by
    intro H hH
    have h := H.card_mul_index
    rw [hH, hB27] at h
    omega
  have hproper : ∀ H : Subgroup B, H.index = 3 → CFSG.fixedPointSubgroup H V ≠ ⊤ := by
    intro H hH htop
    have hbot : H = ⊥ := by
      rw [eq_bot_iff_forall]
      intro b hb
      have hρb : ρ b = 1 := by
        apply MulEquiv.ext
        intro v
        have hv : v ∈ CFSG.fixedPointSubgroup H V := by
          rw [htop]
          exact Subgroup.mem_top v
        exact hv ⟨b, hb⟩
      exact hρ (hρb.trans (map_one ρ).symm)
    have h := hcard9 H hH
    rw [hbot, Subgroup.card_bot] at h
    omega
  obtain ⟨H₀, hH₀⟩ := CFSG.SolvableHall.exists_index_eq_prime (p := 3)
    (CFSG.IsElementaryAbelian.isPGroup 3 B)
  interval_cases k
  ·
    obtain ⟨m, hm, -⟩ := fn_card_eq_prime_pow_of_ne_top hk (hproper H₀ hH₀)
    omega
  ·
    have hall : ∀ H : Subgroup B, H.index = 3 → CFSG.fixedPointSubgroup H V = ⊥ := by
      intro H hH
      obtain ⟨m, hm, hmq⟩ := fn_card_eq_prime_pow_of_ne_top hk (hproper H hH)
      have hm0 : m = 0 := by omega
      subst hm0
      rw [pow_zero] at hmq
      exact Subgroup.eq_bot_of_card_eq _ hmq
    exact fn_iSup_ne_top_of_all_bot (by rw [hk, pow_one]; exact hq1) hall hsup
  ·
    obtain ⟨H₁, H₂, hH₁, hH₂, hc₁, hc₂, hne⟩ := fn_exists_pair hk hsup hproper
    have hinf := fn_inf_eq_bot ρ hρ (fun _ _ => rfl) (fn_sup_eq_top hk hc₁ hc₂ hne)
    have hidx := Subgroup.index_inf_le (H := H₁) (K := H₂)
    rw [hinf, Subgroup.index_bot, hH₁, hH₂] at hidx
    omega

theorem cr_comm_of_le_sq {V : Type} [Group V] [Finite V] {q : ℕ} [Fact q.Prime]
    (hVq : IsPGroup q V) (hV : Nat.card V ≤ q ^ 2) : ∀ a b : V, a * b = b * a := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hVq
  have hq1 : 1 < q := (Fact.out : Nat.Prime q).one_lt
  have hn2 : n ≤ 2 := by
    by_contra h
    have h3 : q ^ 3 ≤ q ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq1 (by norm_num)
    have h5 : q ^ 2 < Nat.card V := by rw [hn]; exact lt_of_lt_of_le h4 h3
    exact absurd hV (not_le.mpr h5)
  interval_cases n
  · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact fun a b => Subsingleton.elim _ _
  · haveI := isCyclic_of_prime_card (α := V) (p := q) (by simpa using hn)
    have : IsMulCommutative V := inferInstance
    exact fun a b => this.is_comm.comm a b
  · exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hn).is_comm.comm a b

theorem cr_eq_one_of_mem_isPGroup {G : Type} [Group G] {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {H : Subgroup G} (hH : IsPGroup q H) {x : G} (hx : x ∈ H) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  have hk' : x ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (q ^ k) :=
    Nat.Coprime.pow_right k
      ((Nat.coprime_primes Nat.prime_three (Fact.out : Nat.Prime q)).mpr (Ne.symm hq3))
  have hd : orderOf x ∣ Nat.gcd 3 (q ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem cr_mem_centralizer_of_ker {X : Type} [Group X] {D : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (D : Set X)) (h : D.normalizerMonoidHom ⟨b, hb⟩ = 1) :
    b ∈ Subgroup.centralizer (D : Set X) := by
  have hmem : (⟨b, hb⟩ : Subgroup.normalizer (D : Set X)) ∈ D.normalizerMonoidHom.ker :=
    MonoidHom.mem_ker.mpr h
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem cr_not_dvd_card_zpowers {X : Type} [Group X] {q : ℕ} (hq5 : 5 ≤ q) {b : X}
    (hb3 : b ^ 3 = 1) : ¬ q ∣ Nat.card (Subgroup.zpowers b) := by
  rw [Nat.card_zpowers]
  intro hdiv
  have := Nat.le_of_dvd (by norm_num) (hdiv.trans (orderOf_dvd_of_pow_eq_one hb3))
  omega

theorem cr_ne_bot {X : Type} [Group X] {R B : Subgroup X} (hB27 : Nat.card B = 27)
    (hfaith : ∀ b ∈ B, (∀ r ∈ R, b * r = r * b) → b = 1) : R ≠ ⊥ := by
  intro hR0
  have hB1 : B = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine hfaith b hb (fun r hr => ?_)
    rw [hR0, Subgroup.mem_bot] at hr
    rw [hr, mul_one, one_mul]
  rw [hB1] at hB27
  simp at hB27

theorem no_faithful_E27 {X : Type} [Group X] [Finite X] {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2) {R : Subgroup X} (hR : IsPGroup q R)
    {B : Subgroup X} (hBR : B ≤ Subgroup.normalizer (R : Set X)) (hB27 : Nat.card B = 27)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (hfaith : ∀ b ∈ B, (∀ r ∈ R, b * r = r * b) → b = 1) : False := by
  have hq1 : 1 < q := (Fact.out : Nat.Prime q).one_lt
  have hq3 : q ≠ 3 := by omega
  have hqp : q ≠ 2 := by omega
  obtain ⟨D, hDR, hDN, hDexp, -, hDcrit⟩ :=
    CFSG.RankThree.PartTwo.Sec5.Bender.exists_critical_faithful (p := q) hqp hR
      (cr_ne_bot hB27 hfaith)
  have hDq : IsPGroup q D := hR.to_le hDR
  have hDexp' : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hDexp x.1 x.2)
  have hDrank : CFSG.Open.pRank q (⊤ : Subgroup D) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hq1 D.subtype D.subtype_injective).trans hrank
  have hV : Nat.card (↥D ⧸ frattini ↥D) ≤ q ^ 2 :=
    (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hDq hDexp' hDrank).2
  have hVq : IsPGroup q (↥D ⧸ frattini ↥D) := hDq.to_quotient (frattini ↥D)
  have hBN : B ≤ Subgroup.normalizer (D : Set X) := fun b hb => hDN b (hBR hb)
  let ρ₀ : B →* MulAut D := D.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let ρ₁ : B →* MulAut (↥D ⧸ frattini ↥D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥D)).comp ρ₀
  have hB3' : ∀ b : ↥B, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hB3 (b : X) b.2)
  have hρ₁ : Function.Injective ρ₁ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hker : ρ₀ b ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini ↥D)).ker := MonoidHom.mem_ker.mpr hb
    have h3 : ρ₀ b ^ 3 = 1 := by rw [← map_pow, hB3' b, map_one]
    have hx : ρ₀ b = 1 :=
      cr_eq_one_of_mem_isPGroup hq3
        (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup q hDq)
        hker h3
    have hbC : (b : X) ∈ Subgroup.centralizer (D : Set X) :=
      cr_mem_centralizer_of_ker (hBN b.2) hx
    have hbR : (b : X) ∈ Subgroup.centralizer (R : Set X) :=
      hDcrit _ (cr_not_dvd_card_zpowers hq5 (hB3 (b : X) b.2))
        (Subgroup.zpowers_le.mpr (hBR b.2)) (Subgroup.zpowers_le.mpr hbC)
        (Subgroup.mem_zpowers _)
    have hfb : (b : X) = 1 :=
      hfaith (b : X) b.2 (fun r hr => (Subgroup.mem_centralizer_iff.mp hbR r hr).symm)
    exact Subtype.ext (by simpa using hfb)
  exact no_faithful_E27_small (V := ↥D ⧸ frattini ↥D) (B := ↥B) hq3
    (cr_comm_of_le_sq hVq hV) hVq hV (fun a b => Subtype.ext (hBab (a : X) a.2 (b : X) b.2))
    hB3' hB27 ρ₁ hρ₁

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
