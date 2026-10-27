module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Endgame

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2End
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open scoped commutatorElement

section OddPart

variable (H : Type*) [Group H]

@[expose] def centerPow (n : ℕ) : center H →* H where
  toFun z := (z : H) ^ n
  map_one' := by simp
  map_mul' x y := by
    simp only [coe_mul]
    exact Commute.mul_pow (mem_center_iff.mp y.2 x) n

@[expose] def centerPowRange (n : ℕ) : Subgroup H := (centerPow H n).range

variable {H}

theorem centerPowRange_le_center (n : ℕ) : centerPowRange H n ≤ center H := by
  rintro _ ⟨z, rfl⟩
  exact pow_mem z.2 n

instance centerPowRange_normal (n : ℕ) : (centerPowRange H n).Normal :=
  ⟨fun x hx g => by
    have hc := mem_center_iff.mp (centerPowRange_le_center n hx) g
    rwa [hc, mul_inv_cancel_right]⟩

theorem pow_mem_centerPowRange {n : ℕ} {z : H} (hz : z ∈ center H) :
    z ^ n ∈ centerPowRange H n :=
  ⟨⟨z, hz⟩, rfl⟩

theorem odd_orderOf_of_mem_centerPowRange [Finite H] {x : H}
    (hx : x ∈ centerPowRange H (2 ^ (Nat.card (center H)).factorization 2)) :
    Odd (orderOf x) := by
  obtain ⟨z, rfl⟩ := hx
  set N := Nat.card (center H) with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  have hsplit : 2 ^ N.factorization 2 * ordCompl[2] N = N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have hpow : ((centerPow H (2 ^ N.factorization 2)) z) ^ (ordCompl[2] N) = 1 := by
    change ((z : H) ^ (2 ^ N.factorization 2)) ^ (ordCompl[2] N) = 1
    rw [← pow_mul, hsplit, hN, ← SubgroupClass.coe_pow, pow_card_eq_one', OneMemClass.coe_one]
  have hodd : Odd (ordCompl[2] N) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hN0))
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)

end OddPart

section Quot

variable {H : Type*} [Group H]

theorem center_eq_bot_of_not_prime [IsSimpleGroup H] (hp : ¬ (Nat.card H).Prime) :
    center H = ⊥ := by
  rcases (center H).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : IsMulCommutative H := ⟨⟨fun a b => by
      have hb : b ∈ center H := by rw [h]; trivial
      exact (mem_center_iff.mp hb a)⟩⟩
    exact hp ((Group.is_simple_iff_prime_card).mp inferInstance)

theorem center_quot_eq_map (hZ : center (H ⧸ center H) = ⊥) {O : Subgroup H} [O.Normal]
    (hO : O ≤ center H) : center (H ⧸ O) = (center H).map (QuotientGroup.mk' O) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O q
    refine ⟨x, ?_, rfl⟩
    have hx : (x : H ⧸ center H) ∈ center (H ⧸ center H) := by
      rw [mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        have hc := mem_center_iff.mp hq (QuotientGroup.mk' O g)
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul] at hc
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        exact hO (QuotientGroup.eq.mp hc)
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hx
    exact hx
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul]
      rw [mem_center_iff.mp hz g]

end Quot

theorem four_dvd_orderOf_of_even {G : Type*} [Group G] [Finite G] {c : G}
    (h : Even (orderOf (c ^ 2))) : 4 ∣ orderOf c := by
  have hpos := orderOf_pos c
  rw [orderOf_pow' c two_ne_zero] at h
  set n := orderOf c
  have hg : Nat.gcd n 2 ∣ 2 := Nat.gcd_dvd_right n 2
  rcases (Nat.dvd_prime Nat.prime_two).mp hg with h1 | h2
  · rw [h1, Nat.div_one] at h
    have : 2 ∣ n := even_iff_two_dvd.mp h
    rw [Nat.gcd_eq_right this] at h1
    exact absurd h1 (by norm_num)
  · rw [h2] at h
    have h2n : 2 ∣ n := h2 ▸ Nat.gcd_dvd_left n 2
    obtain ⟨r, hr⟩ := h
    omega

section Tools

variable {M : Type*} [Group M]

theorem commElem_mem {H : Subgroup M} {x y : M} (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

@[expose] def tree3 (x : Fin 8 → M) : M :=
  ⁅⁅⁅x 0, x 1⁆, ⁅x 2, x 3⁆⁆, ⁅⁅x 4, x 5⁆, ⁅x 6, x 7⁆⁆⁆

theorem map_tree3 {N : Type*} [Group N] (f : M →* N) (x : Fin 8 → M) :
    f (tree3 x) = tree3 (f ∘ x) := by
  simp only [tree3, map_commutatorElement, Function.comp_apply]

theorem tree3_mem {H : Subgroup M} {x : Fin 8 → M} (hx : ∀ i, x i ∈ H) : tree3 x ∈ H :=
  commElem_mem (commElem_mem (commElem_mem (hx 0) (hx 1)) (commElem_mem (hx 2) (hx 3)))
    (commElem_mem (commElem_mem (hx 4) (hx 5)) (commElem_mem (hx 6) (hx 7)))

theorem commute_of_mem_closure {S T : Set M} (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x y : M}
    (hx : x ∈ closure S) (hy : y ∈ closure T) : x * y = y * x := by
  have h1 : closure T ≤ centralizer S := by
    rw [closure_le]
    intro t ht
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro s hs
    exact h s hs t ht
  have h2 : closure S ≤ centralizer (closure T : Set M) := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro t ht
    exact (mem_centralizer_iff.mp (h1 ht) s hs).symm
  exact (mem_centralizer_iff.mp (h2 hx) y hy).symm

theorem commutator_closure_le {S : Set M} {N : Subgroup M}
    (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N ∧ s⁻¹ * n * s ∈ N)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ N) : ⁅closure S, closure S⁆ ≤ N := by
  have hnorm : closure S ≤ normalizer (N : Set M) := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro n
    refine ⟨fun hn => (hN s hs n hn).1, fun hn => ?_⟩
    have := (hN s hs _ hn).2
    simpa [mul_assoc] using this
  have hconj : ∀ y ∈ closure S, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (mem_normalizer_iff.mp (hnorm hy) n).mp hn
  have hconj' : ∀ y ∈ closure S, ∀ n ∈ N, y⁻¹ * n * y ∈ N := fun y hy n hn => by
    have := hconj y⁻¹ (inv_mem hy) n hn
    rwa [inv_inv] at this
  have h1 : ∀ s ∈ S, ∀ y ∈ closure S, ⁅s, y⁆ ∈ N := by
    intro s hs y hy
    induction hy using closure_induction with
    | mem y hy => exact hS s hs y hy
    | one => rw [commutatorElement_one_right]; exact one_mem N
    | mul y₁ y₂ hy₁ _ ih₁ ih₂ =>
      have e : ⁅s, y₁ * y₂⁆ = ⁅s, y₁⁆ * (y₁ * ⁅s, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ih₁ (hconj y₁ hy₁ _ ih₂)
    | inv y hy ih =>
      have e : ⁅s, y⁻¹⁆ = y⁻¹ * ⁅s, y⁆⁻¹ * y := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj' y hy _ (inv_mem ih)
  rw [commutator_le]
  intro x hx y hy
  induction hx using closure_induction with
  | mem x hx => exact h1 x hx y hy
  | one => rw [commutatorElement_one_left]; exact one_mem N
  | mul x₁ x₂ hx₁ _ ih₁ ih₂ =>
    have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hconj x₁ hx₁ _ ih₂) ih₁
  | inv x hx ih =>
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj' x hx _ (inv_mem ih)

end Tools

section Conj

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def conjNorm (A : Subgroup G) (g : G) :
    normalizer (rightConjugate A g : Set G) →* normalizer (A : Set G) where
  toFun y := ⟨g * y * g⁻¹, (mem_normalizer_conj_iff A g y).mp y.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' y z := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem conjNorm_apply (g : G) (y : normalizer (rightConjugate A g : Set G)) :
    ((conjNorm A g y : normalizer (A : Set G)) : G) = g * y * g⁻¹ := rfl

variable {n : ℕ} {R E₀ : Subgroup (Equiv.Perm (Fin n))} {ψ : normalizer (A : Set G) →* ↥R}
  {T : Subgroup G} {w : Equiv.Perm (Fin n)}

theorem mem_of_excClass
    (hw : ((T.subgroupOf (normalizer (A : Set G))).map ψ).map R.subtype =
      E₀.map (MulAut.conj w).toMonoidHom)
    {m : normalizer (A : Set G)} (hm : (m : G) ∈ T) :
    ∃ e ∈ E₀, ((ψ m : ↥R) : Equiv.Perm (Fin n)) = w * e * w⁻¹ := by
  have h1 : ((ψ m : ↥R) : Equiv.Perm (Fin n)) ∈ E₀.map (MulAut.conj w).toMonoidHom := by
    rw [← hw]
    exact ⟨ψ m, ⟨m, hm, rfl⟩, rfl⟩
  obtain ⟨e, he, hee⟩ := h1
  exact ⟨e, he, by rw [← hee]; simp [MulAut.conj_apply]⟩

theorem exists_of_excClass
    (hw : ((T.subgroupOf (normalizer (A : Set G))).map ψ).map R.subtype =
      E₀.map (MulAut.conj w).toMonoidHom)
    {e : Equiv.Perm (Fin n)} (he : e ∈ E₀) :
    ∃ m : normalizer (A : Set G), (m : G) ∈ T ∧
      ((ψ m : ↥R) : Equiv.Perm (Fin n)) = w * e * w⁻¹ := by
  have h1 : w * e * w⁻¹ ∈ ((T.subgroupOf (normalizer (A : Set G))).map ψ).map R.subtype := by
    rw [hw]
    exact ⟨e, he, by simp [MulAut.conj_apply]⟩
  obtain ⟨_, ⟨m, hm, rfl⟩, hme⟩ := h1
  exact ⟨m, hm, hme⟩

end Conj

theorem odd_card_center_of_lift (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : AS76b.Hyp31 A) {n : ℕ} {R P : Subgroup (Equiv.Perm (Fin n))}
    (hPR : P ≤ R) {ψ : normalizer (A : Set G) →* ↥R} (hψ : IsActionHom A (P.subgroupOf R) ψ)
    (hsimp : IsSimpleGroup (↥A ⧸ center ↥A)) (hprime : ¬ (Nat.card (↥A ⧸ center ↥A)).Prime)
    (hbound : ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
      IsPGroup 2 (center L) → Nonempty (L ⧸ center L ≃* ↥A ⧸ center ↥A) →
        Nat.card (center L) ≤ 2)
    {Q : Equiv.Perm (Fin n) → Prop}
    (hlift : ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
      ∀ t : L, orderOf t = 2 → center L = zpowers t → ∀ π : L →* ↥P,
        Function.Surjective π → π.ker = zpowers t → ∀ v : L, orderOf (π v) = 2 →
          Q ((π v : ↥P) : Equiv.Perm (Fin n)) → v ^ 2 = t)
    (hQ1 : ¬ Q 1) {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1)
    (htX : ψ t ∈ P.subgroupOf R) (hQ : Q ((ψ t : ↥R) : Equiv.Perm (Fin n))) :
    Odd (Nat.card (center ↥A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZ
  have hZ2 : 2 ∣ Nat.card (center ↥A) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hZ)
  set k := (Nat.card (center ↥A)).factorization 2 with hk
  set O := centerPowRange (↥A) (2 ^ k) with hO
  have hOZ : O ≤ center ↥A := centerPowRange_le_center _
  obtain ⟨z₂, hz₂⟩ := exists_prime_orderOf_dvd_card' (G := center ↥A) 2 hZ2
  have hz₂O : (z₂ : ↥A) ∉ O := by
    intro h
    have h' := odd_orderOf_of_mem_centerPowRange h
    rw [Subgroup.orderOf_coe, hz₂] at h'
    exact absurd h' (by decide)
  have hZbar : center (↥A ⧸ center ↥A) = ⊥ := center_eq_bot_of_not_prime hprime
  have hcL : center (↥A ⧸ O) = (center ↥A).map (QuotientGroup.mk' O) :=
    center_quot_eq_map hZbar hOZ
  have eL : (↥A ⧸ O) ⧸ center (↥A ⧸ O) ≃* ↥A ⧸ center ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcL).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (center ↥A) hOZ)
  have hperf : commutator (↥A ⧸ O) = ⊤ := by
    have hAp : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.standard.1.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O))
  have hLq : CFSG.Assembly.IsQuasisimple (↥A ⧸ O) :=
    ⟨hperf, @MulEquiv.isSimpleGroup _ _ _ _ hsimp eL⟩
  have hL2 : IsPGroup 2 (center (↥A ⧸ O)) := by
    rintro ⟨q, hq⟩
    rw [hcL] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_centerPowRange hz
  have hcard : Nat.card (center (↥A ⧸ O)) ≤ 2 := hbound (↥A ⧸ O) hLq hL2 ⟨eL⟩
  set t₀ : ↥A ⧸ O := QuotientGroup.mk' O (z₂ : ↥A) with ht₀
  have ht₀C : t₀ ∈ center (↥A ⧸ O) := by
    rw [hcL]
    exact ⟨z₂, z₂.2, rfl⟩
  have ht₀1 : t₀ ≠ 1 := by
    rw [ht₀, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hz₂O
  have hz₂sq : (z₂ : ↥A) ^ 2 = 1 := by
    rw [← SubgroupClass.coe_pow, ← hz₂, pow_orderOf_eq_one, OneMemClass.coe_one]
  have ht₀2 : orderOf t₀ = 2 := by
    refine orderOf_eq_prime ?_ ht₀1
    rw [ht₀, ← map_pow, hz₂sq, map_one]
  have hZL : center (↥A ⧸ O) = zpowers t₀ := by
    refine (eq_of_le_of_card_ge (zpowers_le.mpr ht₀C) ?_).symm
    rw [Nat.card_zpowers, ht₀2]
    exact hcard
  let ψA : ↥A →* ↥(P.subgroupOf R) :=
    (ψ.comp (inclusion le_normalizer)).codRestrict (P.subgroupOf R) fun a => hψ.map_mem a a.2
  have hψA : ∀ a : ↥A, ((ψA a : ↥R)) = ψ ⟨a, le_normalizer a.2⟩ := fun _ => rfl
  have hkerA : ψA.ker = center ↥A := by
    ext a
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, hψA, OneMemClass.coe_one, hψ.eq_one_iff,
      mem_center_iff, mem_centralizer_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g g.2)
    · intro h g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
  have hOker : O ≤ ψA.ker := hkerA ▸ hOZ
  let π : ↥A ⧸ O →* ↥P :=
    (subgroupOfEquivOfLe hPR).toMonoidHom.comp (QuotientGroup.lift O ψA hOker)
  have hπ : ∀ a : ↥A, ((π (QuotientGroup.mk' O a) : ↥P) : Equiv.Perm (Fin n)) =
      ((ψ ⟨a, le_normalizer a.2⟩ : ↥R) : Equiv.Perm (Fin n)) := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro p
    obtain ⟨a, ha, hae⟩ := hψ.exists_eq _ ((subgroupOfEquivOfLe hPR).symm p).2
    refine ⟨QuotientGroup.mk' O ⟨a, ha⟩, Subtype.ext ?_⟩
    rw [hπ]
    exact congrArg Subtype.val hae
  have hπk : π.ker = zpowers t₀ := by
    have h1 : π.ker = (QuotientGroup.lift O ψA hOker).ker := by
      ext q
      simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    rw [h1, QuotientGroup.ker_lift, hkerA, ← hcL, hZL]
  obtain ⟨a, ha, hat⟩ := hψ.exists_eq _ htX
  have hψt2 : ψ t ^ 2 = 1 := by
    rw [← map_pow, show t ^ 2 = 1 from Subtype.ext (by simpa using ht2), map_one]
  have hψt1 : ψ t ≠ 1 := by
    intro h1
    rw [h1, OneMemClass.coe_one] at hQ
    exact hQ1 hQ
  have hord : orderOf (ψ t) = 2 := orderOf_eq_prime hψt2 hψt1
  set v : ↥A ⧸ O := QuotientGroup.mk' O ⟨a, ha⟩ with hv
  have hπv : ((π v : ↥P) : Equiv.Perm (Fin n)) = ((ψ t : ↥R) : Equiv.Perm (Fin n)) := by
    rw [hv, hπ]
    exact congrArg Subtype.val hat
  have hordv : orderOf (π v) = 2 := by
    rw [← Subgroup.orderOf_coe, hπv, Subgroup.orderOf_coe, hord]
  have hv2 : v ^ 2 = t₀ := hlift _ hLq t₀ ht₀2 hZL π hπs hπk v hordv (by rw [hπv]; exact hQ)
  have ha4 : (⟨a, ha⟩ : ↥A) ^ 4 ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    change v ^ 4 = 1
    rw [show v ^ 4 = (v ^ 2) ^ 2 by rw [← pow_mul], hv2]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ht₀2)
  have ha2 : Even (orderOf ((⟨a, ha⟩ : ↥A) ^ 2)) := by
    by_contra hodd
    obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hodd
    have he : (⟨a, ha⟩ : ↥A) ^ 2 = ((⟨a, ha⟩ : ↥A) ^ 4) ^ (j + 1) := by
      rw [← pow_mul, show 4 * (j + 1) = 2 * (2 * j + 1) + 2 by ring, pow_add, pow_mul, ← hj,
        pow_orderOf_eq_one, one_mul]
    apply ht₀1
    rw [← hv2, hv, ← map_pow, he, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact pow_mem ha4 _
  set c : G := a⁻¹ * t with hc
  have hcK : c ∈ centralizer (A : Set G) := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hat, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hac : Commute a c := (mem_centralizer_iff.mp hcK a ha)
  have hc2 : c ^ 2 = (a ^ 2)⁻¹ := by
    have h1 : (a * c) ^ 2 = 1 := by rw [hc, mul_inv_cancel_left]; exact ht2
    rw [hac.mul_pow] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hc4 : 4 ∣ orderOf c := by
    apply four_dvd_orderOf_of_even
    rw [hc2, orderOf_inv]
    have := ha2
    rwa [← Subgroup.orderOf_coe, SubgroupClass.coe_pow] at this
  set x := c ^ (orderOf c / 4) with hx
  have hx4 : orderOf x = 4 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hc4
  have hxK : x ∈ centralizer (A : Set G) := pow_mem hcK _
  have hxP : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have hsq := sq_eq_one_of_isPGroup_zpowers (h32 G A hA) hxK hxP
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [hx4] at this
  exact absurd this (by norm_num)

structure EndFacts {n : ℕ} (R P E₀ : Subgroup (Equiv.Perm (Fin n))) (e₀ : Equiv.Perm (Fin n))
    (Q : Equiv.Perm (Fin n) → Prop) : Prop where
  le_P : E₀ ≤ P
  mem : e₀ ∈ E₀
  Q_of_mem : ∀ e ∈ E₀, e ≠ 1 → Q e
  Q_conj : ∀ g ∈ R, ∀ x, Q x → Q (g * x * g⁻¹)
  exists_conj : ∃ a₀ ∈ P,
    (∀ e ∈ E₀, ∀ e' ∈ E₀, e * (a₀⁻¹ * e' * a₀) = a₀⁻¹ * e' * a₀ * e) ∧
    a₀⁻¹ * e₀ * a₀ ∉ E₀ ∧
    ∃ x : Fin 8 → Equiv.Perm (Fin n), (∀ i, x i ∈ P ∧ ∀ e ∈ E₀, x i * e = e * x i) ∧
      tree3 x = e₀ * (a₀⁻¹ * e₀ * a₀)
  not_Q : ∀ z ∈ ⁅P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))),
    P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n)))⁆, z ^ 2 = 1 → z ≠ 1 → ¬ Q z

theorem false_of_endgame (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : AS76b.Hyp31 A) {n : ℕ} {R P E₀ : Subgroup (Equiv.Perm (Fin n))}
    {e₀ : Equiv.Perm (Fin n)} {Q : Equiv.Perm (Fin n) → Prop} (hPR : P ≤ R)
    (hRN : R ≤ normalizer (P : Set (Equiv.Perm (Fin n))))
    (hcomm : ∀ x y : ↥R, ⁅x, y⁆ ∈ P.subgroupOf R) (hF : EndFacts R P E₀ e₀ Q)
    {ψ : normalizer (A : Set G) →* ↥R} (hψ : IsActionHom A (P.subgroupOf R) ψ)
    (hc : YCensus (P.subgroupOf R) (ExcClass R E₀))
    (h175 : ∀ t : normalizer (A : Set G), (t : G) ^ 2 = 1 → ψ t ∈ P.subgroupOf R →
      Q ((ψ t : ↥R) : Equiv.Perm (Fin n)) → Odd (Nat.card (center ↥A)))
    {g : G} (hg : g ∉ normalizer (A : Set G)) {RK T : Subgroup G}
    (hR : IsSylowOf 2 RK (centralizer (A : Set G)))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTN : T ≤ normalizer (A : Set G)) (hRN' : RK ≤ normalizer (rightConjugate A g : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hleP, he₀, hQE, hQc, ⟨a₀, ha₀P, hcomm₀, hnot₀, x, hx, htree⟩, hnotQ⟩ := hF
  set K := centralizer (A : Set G) with hK
  have hT1 : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (A : Set G)) :=
    hT.of_le (le_inf hT.le hTN) inf_le_left
  obtain ⟨w, hwR, hw⟩ := exc_of_sylow h32 hA hψ hc hg hT1 hT
  have hTab := sq_eq_one_of_isSylowOf h32 hA hT
  have hconjP : ∀ {v y : Equiv.Perm (Fin n)}, v ∈ R → y ∈ P → v * y * v⁻¹ ∈ P :=
    fun hv hy => (mem_normalizer_iff.mp (hRN hv) _).mp hy
  have hTX : ∀ m : normalizer (A : Set G), (m : G) ∈ T → ψ m ∈ P.subgroupOf R := by
    intro m hm
    obtain ⟨e', he', hee⟩ := mem_of_excClass hw hm
    change ((ψ m : ↥R) : Equiv.Perm (Fin n)) ∈ P
    rw [hee]
    exact hconjP hwR (hleP he')
  have he₀1 : e₀ ≠ 1 := fun h1 => hnot₀ (by rw [h1, mul_one, inv_mul_cancel]; exact one_mem _)
  obtain ⟨t, htT, htψ⟩ := exists_of_excClass hw he₀
  have ht2 : (t : G) ^ 2 = 1 := hTab _ htT
  have htK : (t : G) ∈ rightConjugate K g := hT.le htT
  have hψt1 : ((ψ t : ↥R) : Equiv.Perm (Fin n)) ≠ 1 := by
    rw [htψ]
    intro h1
    apply he₀1
    have := congrArg (fun y => w⁻¹ * y * w) h1
    simpa [mul_assoc] using this
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    apply hψt1
    rw [show t = 1 from Subtype.ext h1, map_one, OneMemClass.coe_one]
  have hZ : Odd (Nat.card (center ↥A)) := by
    refine h175 t ht2 (hTX t htT) ?_
    rw [htψ]
    exact hQc w hwR _ (hQE _ he₀ he₀1)
  have hlift : ∀ y ∈ P, ∃ (b : G) (hb : b ∈ A),
      ((ψ ⟨b, le_normalizer hb⟩ : ↥R) : Equiv.Perm (Fin n)) = w * y * w⁻¹ := by
    intro y hy
    obtain ⟨b, hb, hbe⟩ := hψ.exists_eq (⟨w * y * w⁻¹, R.mul_mem (R.mul_mem hwR (hPR hy))
      (R.inv_mem hwR)⟩ : ↥R) (hconjP hwR hy)
    exact ⟨b, hb, by rw [hbe]⟩
  obtain ⟨a, haA, haψ⟩ := hlift a₀ ha₀P
  choose b hbA hbψ using fun i => hlift (x i) (hx i).1
  set aN : normalizer (A : Set G) := ⟨a, le_normalizer haA⟩ with haN
  have hcommT : ∀ s ∈ T, ∀ y ∈ T, s * (a⁻¹ * y * a) = a⁻¹ * y * a * s := by
    intro s hs y hy
    obtain ⟨es, hes, hesψ⟩ := mem_of_excClass hw (m := ⟨s, hTN hs⟩) hs
    obtain ⟨ey, hey, heyψ⟩ := mem_of_excClass hw (m := ⟨y, hTN hy⟩) hy
    refine commute_conj_of_map hψ hZ (s := ⟨s, hTN hs⟩) (y := ⟨y, hTN hy⟩) haA
      (y' := aN⁻¹ * ⟨y, hTN hy⟩ * aN) rfl (commute_of_sq_eq_one hTab hs hy) (hTab s hs)
      (hTab y hy) (hTX _ hs) ?_
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hesψ, heyψ, haψ]
    have hc' := hcomm₀ es hes ey hey
    calc w * es * w⁻¹ * ((w * a₀ * w⁻¹)⁻¹ * (w * ey * w⁻¹) * (w * a₀ * w⁻¹))
        = w * (es * (a₀⁻¹ * ey * a₀)) * w⁻¹ := by group
      _ = w * (a₀⁻¹ * ey * a₀ * es) * w⁻¹ := by rw [hc']
      _ = (w * a₀ * w⁻¹)⁻¹ * (w * ey * w⁻¹) * (w * a₀ * w⁻¹) * (w * es * w⁻¹) := by group
  have hcommTa : ∀ s ∈ T, ∀ z ∈ rightConjugate T a, s * z = z * s := by
    intro s hs z hz
    have hz' : a * z * a⁻¹ ∈ T := (mem_rightConjugate_iff T a z).mp hz
    have := hcommT s hs _ hz'
    simpa [mul_assoc] using this
  set t' : normalizer (A : Set G) := aN⁻¹ * t * aN with ht'
  have ht'G : (t' : G) = a⁻¹ * t * a := rfl
  have ht'ψ : ((ψ t' : ↥R) : Equiv.Perm (Fin n)) = w * (a₀⁻¹ * e₀ * a₀) * w⁻¹ := by
    simp only [ht', map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, haψ, htψ]
    group
  have hct : (t : G) * t' = t' * t := by rw [ht'G]; exact hcommT _ htT _ htT
  have ht'2 : (t' : G) ^ 2 = 1 := by
    rw [ht'G, sq]
    calc a⁻¹ * (t : G) * a * (a⁻¹ * t * a) = a⁻¹ * ((t : G) ^ 2) * a := by rw [sq]; group
      _ = 1 := by rw [ht2]; group
  set u : normalizer (A : Set G) := t * t' with hu
  have huG : (u : G) = t * t' := rfl
  have hu2 : (u : G) ^ 2 = 1 := by
    rw [huG, Commute.mul_pow hct, ht2, ht'2, one_mul]
  have huA : (u : G) ∈ A := by
    have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
    have h1 : (t : G) * a⁻¹ * (t : G)⁻¹ ∈ A :=
      (mem_normalizer_iff.mp t.2 a⁻¹).mp (A.inv_mem haA)
    have e1 : (u : G) = (t : G) * a⁻¹ * (t : G)⁻¹ * a := by
      rw [huG, ht'G, htinv]
      group
    rw [e1]
    exact A.mul_mem h1 haA
  have huψ : ((ψ u : ↥R) : Equiv.Perm (Fin n)) = w * tree3 x * w⁻¹ := by
    rw [hu, map_mul, Subgroup.coe_mul, htψ, ht'ψ, htree]
    group
  set bN : Fin 8 → normalizer (A : Set G) := fun i => ⟨b i, le_normalizer (hbA i)⟩ with hbN
  have hũG : ((tree3 bN : normalizer (A : Set G)) : G) = tree3 b :=
    map_tree3 (normalizer (A : Set G)).subtype bN
  have hũA : ((tree3 bN : normalizer (A : Set G)) : G) ∈ A := by
    rw [hũG]
    exact tree3_mem hbA
  have hũψ : ((ψ (tree3 bN) : ↥R) : Equiv.Perm (Fin n)) = w * tree3 x * w⁻¹ := by
    rw [map_tree3]
    change R.subtype (tree3 (ψ ∘ bN)) = _
    rw [map_tree3]
    have hfun : (R.subtype ∘ (ψ ∘ bN)) = (MulAut.conj w).toMonoidHom ∘ x := by
      funext i
      simp only [Function.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      exact hbψ i
    rw [hfun, ← map_tree3]
    simp [MulAut.conj_apply]
  have hk : ((tree3 bN : normalizer (A : Set G)) : G)⁻¹ * u ∈ K := by
    have h1 : ψ ((tree3 bN)⁻¹ * u) = 1 := by
      rw [map_mul, map_inv]
      have : ψ (tree3 bN) = ψ u := Subtype.ext (hũψ.trans huψ.symm)
      rw [this, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  obtain ⟨m, hm⟩ := exists_pow_eq hZ huA hũA hk hu2
  have hbs : ∀ (s : normalizer (A : Set G)), (s : G) ∈ T → ∀ i,
      ψ s * ψ (bN i) = ψ (bN i) * ψ s := by
    intro s hs i
    obtain ⟨es, hes, hesψ⟩ := mem_of_excClass hw hs
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hesψ]
    rw [show ((ψ (bN i) : ↥R) : Equiv.Perm (Fin n)) = w * x i * w⁻¹ from hbψ i]
    have hc' := (hx i).2 es hes
    calc w * es * w⁻¹ * (w * x i * w⁻¹) = w * (es * x i) * w⁻¹ := by group
      _ = w * (x i * es) * w⁻¹ := by rw [hc']
      _ = w * x i * w⁻¹ * (w * es * w⁻¹) := by group
  have hlT : ∀ (s : normalizer (A : Set G)), (s : G) ∈ T → ∀ i j,
      (s : G) * ⁅b i, b j⁆ = ⁅b i, b j⁆ * s :=
    fun s hs i j => commute_commutatorElement hψ (hbA i) (hbA j) (hbs s hs i) (hbs s hs j)
  have hnormT : ∀ {c : G}, c * t = t * c → c ∈ normalizer (rightConjugate A g : Set G) :=
    fun hc' => mem_normalizer_conj_of_commute hA htK ht1 ht2 hc'
  have hlN : ∀ i j, ⁅b i, b j⁆ ∈ normalizer (rightConjugate A g : Set G) :=
    fun i j => hnormT (hlT t htT i j).symm
  have hKg : rightConjugate K 1 ≠ rightConjugate K g := by
    rw [rightConjugate_one]
    intro h
    apply hg
    rw [← hA.standard.2.2.2.1, ← rightConjugate_eq_self_iff]
    exact h.symm
  obtain ⟨w', hw'R, hw'⟩ :=
    exc_of_sylow_conj h32 hA hψ hc hKg (by rwa [rightConjugate_one]) hRN'
  set φ : normalizer (rightConjugate A g : Set G) →* ↥R := ψ.comp (conjNorm A g) with hφ
  set L : Fin 8 → Fin 8 → normalizer (rightConjugate A g : Set G) :=
    fun i j => ⟨⁅b i, b j⁆, hlN i j⟩ with hL
  have hlR : ∀ i j (r₀ : normalizer (A : Set G)), (r₀ : G) ∈ rightConjugate RK g⁻¹ →
      φ (L i j) * ψ r₀ = ψ r₀ * φ (L i j) := by
    intro i j r₀ hr₀
    have hr : g⁻¹ * (r₀ : G) * g ∈ K :=
      hR.le (by simpa using (mem_rightConjugate_iff _ _ _).mp hr₀)
    change ψ (conjNorm A g (L i j)) * ψ r₀ = ψ r₀ * ψ (conjNorm A g (L i j))
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, conjNorm_apply, hL]
    have hlA : ⁅b i, b j⁆ ∈ A := commElem_mem (hbA i) (hbA j)
    have hc' : ⁅b i, b j⁆ * (g⁻¹ * r₀ * g) = (g⁻¹ * r₀ * g) * ⁅b i, b j⁆ :=
      mem_centralizer_iff.mp hr _ hlA
    calc g * ⁅b i, b j⁆ * g⁻¹ * r₀ = g * (⁅b i, b j⁆ * (g⁻¹ * r₀ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r₀ * g) * ⁅b i, b j⁆) * g⁻¹ := by rw [hc']
      _ = r₀ * (g * ⁅b i, b j⁆ * g⁻¹) := by group
  set Θ : normalizer (rightConjugate A g : Set G) →* Equiv.Perm (Fin n) :=
    (MulAut.conj w'⁻¹).toMonoidHom.comp (R.subtype.comp φ) with hΘ
  have hΘ' : ∀ y, Θ y = w'⁻¹ * ((φ y : ↥R) : Equiv.Perm (Fin n)) * w' := fun y => by
    simp [hΘ]
  have hΘL : ∀ i j, Θ (L i j) ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) := by
    intro i j
    rw [hΘ']
    refine mem_inf.mpr ⟨R.mul_mem (R.mul_mem (R.inv_mem hw'R) (φ _).2) hw'R,
      mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨r₀, hr₀, hr₀ψ⟩ := exists_of_excClass hw' he
    have h1 := congrArg Subtype.val (hlR i j r₀ hr₀)
    simp only [Subgroup.coe_mul] at h1
    rw [hr₀ψ] at h1
    calc e * (w'⁻¹ * ((φ (L i j) : ↥R) : Equiv.Perm (Fin n)) * w')
        = w'⁻¹ * ((w' * e * w'⁻¹) * ((φ (L i j) : ↥R) : Equiv.Perm (Fin n))) * w' := by group
      _ = w'⁻¹ * (((φ (L i j) : ↥R) : Equiv.Perm (Fin n)) * (w' * e * w'⁻¹)) * w' := by
          rw [h1]
      _ = w'⁻¹ * ((φ (L i j) : ↥R) : Equiv.Perm (Fin n)) * w' * e := by group
  have hMP : ∀ y z : normalizer (rightConjugate A g : Set G),
      Θ y ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) →
      Θ z ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) →
      Θ ⁅y, z⁆ ∈ P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) := by
    intro y z hy hz
    have h1 : Θ ⁅y, z⁆ ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) := by
      rw [map_commutatorElement]
      exact commElem_mem hy hz
    refine mem_inf.mpr ⟨?_, (mem_inf.mp h1).2⟩
    rw [hΘ', map_commutatorElement]
    have h2 : ((⁅φ y, φ z⁆ : ↥R) : Equiv.Perm (Fin n)) ∈ P := hcomm (φ y) (φ z)
    have := hconjP (R.inv_mem hw'R) h2
    rwa [inv_inv] at this
  set U' : normalizer (rightConjugate A g : Set G) :=
    ⁅⁅L 0 1, L 2 3⁆, ⁅L 4 5, L 6 7⁆⁆ with hU'
  have hΘU : Θ U' ∈ ⁅P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))),
      P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n)))⁆ := by
    rw [hU', map_commutatorElement]
    exact commutator_mem_commutator (hMP _ _ (hΘL 0 1) (hΘL 2 3)) (hMP _ _ (hΘL 4 5) (hΘL 6 7))
  have htN : (t : G) ∈ normalizer (rightConjugate A g : Set G) := hnormT rfl
  have ht'N : (t' : G) ∈ normalizer (rightConjugate A g : Set G) := hnormT hct.symm
  set tG : normalizer (rightConjugate A g : Set G) := ⟨t, htN⟩ with htG
  set t'G : normalizer (rightConjugate A g : Set G) := ⟨t', ht'N⟩ with ht'G'
  have hUG : ((U' : normalizer (rightConjugate A g : Set G)) : G) =
      ((tree3 bN : normalizer (A : Set G)) : G) := by
    rw [hũG]
    rfl
  have huU : tG * t'G = U' ^ m := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hUG, hm]
    rfl
  have hφt : φ tG = 1 := by
    rw [hφ, MonoidHom.comp_apply, hψ.eq_one_iff]
    exact (mem_rightConjugate_iff _ g _).mp htK
  have hφu : φ (U' ^ m) = φ t'G := by rw [← huU, map_mul, hφt, one_mul]
  have hne : rightConjugate K (g * a) ≠ rightConjugate K g := by
    intro heq
    have hTaK : rightConjugate T a ≤ rightConjugate K g := by
      rw [← heq, ← rightConjugate_mul]
      exact Subgroup.map_mono hT.le
    have hTnorm : T ≤ normalizer (rightConjugate T a : Set G) := by
      intro s hs
      rw [mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [hcommTa s hs z hz, mul_inv_cancel_right]
        exact hz
      · intro hz
        have h1 := hcommTa s⁻¹ (T.inv_mem hs) _ hz
        have e1 : z = s * z * s⁻¹ := by
          calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
            _ = s * z * s⁻¹ * s⁻¹ * s := by rw [h1]
            _ = s * z * s⁻¹ := by group
        rw [e1]
        exact hz
    have hQ : IsPGroup 2 (T ⊔ rightConjugate T a : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hT.isPGroup (hT.isPGroup.map _) hTnorm
    have hQT := hT.eq_of_le le_sup_left (sup_le hT.le hTaK) hQ
    have ht'T : (t' : G) ∈ T := by
      have h1 : (t' : G) ∈ rightConjugate T a := by
        rw [mem_rightConjugate_iff, ht'G]
        simpa [mul_assoc] using htT
      rw [← hQT]
      exact mem_sup_right h1
    obtain ⟨e', he', he'ψ⟩ := mem_of_excClass hw ht'T
    apply hnot₀
    have h1 := ht'ψ.symm.trans he'ψ
    have : a₀⁻¹ * e₀ * a₀ = e' := by
      have := congrArg (fun y => w⁻¹ * y * w) h1
      simpa [mul_assoc] using this
    rw [this]
    exact he'
  have hgag : g * a * g⁻¹ ∉ normalizer (A : Set G) := by
    intro h
    rw [← hA.standard.2.2.2.1, ← rightConjugate_eq_self_iff] at h
    apply hne
    rw [show g * a = g * a * g⁻¹ * g by group, ← rightConjugate_mul, h]
  have hTa : IsSylowOf 2 (rightConjugate T a) (rightConjugate K (g * a)) := by
    rw [← rightConjugate_mul]
    exact isSylowOf_conj hT a
  have hTaN : rightConjugate T a ≤ normalizer (rightConjugate A g : Set G) :=
    fun z hz => hnormT (hcommTa _ htT z hz).symm
  obtain ⟨w₁, hw₁R, hw₁⟩ := exc_of_sylow_conj h32 hA hψ hc hne hTa hTaN
  have hmem₁ : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ∈
      rightConjugate (rightConjugate T a) g⁻¹ := by
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, conjNorm_apply]
    have e1 : a * (g⁻¹ * (g * ((t'G : normalizer (rightConjugate A g : Set G)) : G) * g⁻¹) *
        g⁻¹⁻¹) * a⁻¹ = t := by
      rw [ht'G']
      change a * (g⁻¹ * (g * (t' : G) * g⁻¹) * g⁻¹⁻¹) * a⁻¹ = t
      rw [ht'G]
      group
    rw [e1]
    exact htT
  obtain ⟨e₁, he₁, he₁ψ⟩ := mem_of_excClass hw₁ hmem₁
  have hφt'1 : φ t'G ≠ 1 := by
    intro h1
    have hK1 : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ∈ K :=
      (hψ.eq_one_iff _).mp h1
    have hzy : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ∈
        rightConjugate K (g * a * g⁻¹) := by
      rw [mem_rightConjugate_iff, conjNorm_apply]
      have e1 : g * a * g⁻¹ * (g * ((t'G : normalizer (rightConjugate A g : Set G)) : G) *
          g⁻¹) * (g * a * g⁻¹)⁻¹ = g * t * g⁻¹ := by
        rw [ht'G']
        change g * a * g⁻¹ * (g * (t' : G) * g⁻¹) * (g * a * g⁻¹)⁻¹ = g * t * g⁻¹
        rw [ht'G]
        group
      rw [e1]
      exact (mem_rightConjugate_iff _ g _).mp htK
    have hz2 : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ^ 2 = 1 := by
      rw [conjNorm_apply, conj_pow]
      change g * (t' : G) ^ 2 * g⁻¹ = 1
      rw [ht'2, mul_one, mul_inv_cancel]
    have h1' := eq_one_of_mem_inf hA hgag hK1 hzy hz2
    rw [conjNorm_apply] at h1'
    apply ht1
    have h2 : (t' : G) = 1 := by
      have h3 : g⁻¹ * (g * (t' : G) * g⁻¹) * g = g⁻¹ * 1 * g :=
        congrArg (fun z => g⁻¹ * z * g) h1'
      rwa [show g⁻¹ * (g * (t' : G) * g⁻¹) * g = (t' : G) by group,
        show g⁻¹ * 1 * g = (1 : G) by group] at h3
    have e2 : (t : G) = a * t' * a⁻¹ := by rw [ht'G]; group
    rw [e2, h2, mul_one, mul_inv_cancel]
  have hQ1 : Q ((φ t'G : ↥R) : Equiv.Perm (Fin n)) := by
    change Q ((ψ (conjNorm A g t'G) : ↥R) : Equiv.Perm (Fin n))
    rw [he₁ψ]
    refine hQc w₁ hw₁R _ (hQE e₁ he₁ fun h1 => hφt'1 (Subtype.ext ?_))
    change ((ψ (conjNorm A g t'G) : ↥R) : Equiv.Perm (Fin n)) = 1
    rw [he₁ψ, h1, mul_one, mul_inv_cancel]
  have hΘu : Θ (U' ^ m) ∈ ⁅P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))),
      P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n)))⁆ := by
    rw [map_pow]
    exact pow_mem hΘU m
  have hΘu2 : Θ (U' ^ m) ^ 2 = 1 := by
    rw [← map_pow, ← huU]
    have h1 : (tG * t'G) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hu2
    rw [h1, map_one]
  have hΘu1 : Θ (U' ^ m) ≠ 1 := by
    rw [hΘ', hφu]
    intro h1
    apply hφt'1
    apply Subtype.ext
    have := congrArg (fun z => w' * z * w'⁻¹) h1
    simpa [mul_assoc] using this
  apply hnotQ _ hΘu hΘu2 hΘu1
  rw [hΘ', hφu]
  have e3 : w'⁻¹ * ((φ t'G : ↥R) : Equiv.Perm (Fin n)) * w' =
      w'⁻¹ * ((φ t'G : ↥R) : Equiv.Perm (Fin n)) * w'⁻¹⁻¹ := by rw [inv_inv]
  rw [e3]
  exact hQc _ (R.inv_mem hw'R) _ hQ1

end CFSG.ComponentClassification.RankTwoSporadic.Endgame
