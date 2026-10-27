module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

theorem center_le_commutator_of_isPerfect {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    {p : ℕ} [Fact p.Prime] (T : Sylow p K) {z : K} (hz : z ∈ Subgroup.center K)
    (hzp : ∃ k, z ^ p ^ k = 1) : z ∈ ⁅(T : Subgroup K), (T : Subgroup K)⁆ := by
  have hkey : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ (T : Subgroup K) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k * g₀ = g₀ * z ^ k :=
      ((Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k)) g₀).symm
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  let ϕ : (T : Subgroup K) →* Abelianization (T : Subgroup K) := Abelianization.of
  have h1 := MonoidHom.transfer_eq_pow ϕ z hkey
  have h2 : MonoidHom.transfer ϕ z = 1 := by
    have hle : commutator K ≤ (MonoidHom.transfer ϕ).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [Group.IsPerfect.commutator_eq_top] at hle
    exact hle (Subgroup.mem_top z)
  rw [h2] at h1
  have hmem : (⟨z ^ (T : Subgroup K).index, MonoidHom.transfer_eq_pow_aux z hkey⟩ :
      (T : Subgroup K)) ∈ commutator (T : Subgroup K) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1.symm
  have hmem' : z ^ (T : Subgroup K).index ∈ ⁅(T : Subgroup K), (T : Subgroup K)⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨k, hk⟩ := hzp
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hk)
  have hcop : (T : Subgroup K).index.gcd (orderOf z) = 1 := by
    rw [hj]
    exact Nat.Coprime.pow_right j
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr T.not_dvd_index).symm
  exact Subgroup.zpowers_le.mpr hmem' (mem_zpowers_pow_iff.mpr hcop)

section Isotropic

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_eq_mul_of_commute {a b t : G} (ha : Commute a ⁅b, t⁆)
    (hab : Commute ⁅a, t⁆ ⁅b, t⁆) : ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ := by
  have h : b * t * b⁻¹ = ⁅b, t⁆ * t := by rw [commutatorElement_def]; group
  calc ⁅a * b, t⁆ = a * (b * t * b⁻¹) * a⁻¹ * t⁻¹ := by rw [commutatorElement_def]; group
    _ = a * ⁅b, t⁆ * t * a⁻¹ * t⁻¹ := by rw [h]; simp only [mul_assoc]
    _ = ⁅b, t⁆ * ⁅a, t⁆ := by rw [ha.eq, commutatorElement_def a t]; simp only [mul_assoc]
    _ = ⁅a, t⁆ * ⁅b, t⁆ := hab.eq.symm

variable [Finite G]

theorem card_le_card_mul_card_of_le_sup_zpowers {T Z A : Subgroup G} (hZT : Z ≤ T)
    (hZc : ∀ z ∈ Z, ∀ g ∈ T, g * z = z * g)
    (hcen : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x ∈ Z) (hc : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Z)
    (hAT : A ≤ T) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {t : G} (ht : t ∈ T)
    (hTA : T ≤ A ⊔ Subgroup.zpowers t) : Nat.card A ≤ Nat.card Z * Nat.card Z := by
  let f : A →* Z :=
    { toFun := fun a => ⟨⁅(a : G), t⁆, hc _ (hAT a.2) _ ht⟩
      map_one' := Subtype.ext (commutatorElement_one_left t)
      map_mul' := fun a b => Subtype.ext (commutatorElement_mul_left_eq_mul_of_commute
        (hZc _ (hc _ (hAT b.2) _ ht) _ (hAT a.2))
        (hZc _ (hc _ (hAT b.2) _ ht) _ (hZT (hc _ (hAT a.2) _ ht)))) }
  have hker : ∀ a : A, f a = 1 → (a : G) ∈ Z := by
    intro a ha
    have h0 : ⁅(a : G), t⁆ = 1 := congrArg Subtype.val ha
    have h1 : (a : G) * t = t * a := commutatorElement_eq_one_iff_mul_comm.mp h0
    refine hcen _ (hAT a.2) fun y hy => ?_
    have hle : A ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer {(a : G)} := by
      refine sup_le (fun x hx => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hA _ hx _ a.2)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h1.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hTA hy))).symm
  have h1 : Nat.card f.ker ≤ Nat.card Z :=
    Nat.card_le_card_of_injective (fun a => ⟨((a : A) : G), hker a (MonoidHom.mem_ker.mp a.2)⟩)
      fun a b hab => by
        have h : ((a : A) : G) = ((b : A) : G) := congrArg (fun w : Z => (w : G)) hab
        exact Subtype.ext (Subtype.ext h)
  have h2 : f.ker.index ≤ Nat.card Z := by
    rw [Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  calc Nat.card A = Nat.card f.ker * f.ker.index := (Subgroup.card_mul_index f.ker).symm
    _ ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul h1 h2

theorem card_sup_le_pow_of_commute {p : ℕ} (hp : p.Prime) {T Z E : Subgroup G} (hZT : Z ≤ T)
    (hZc : ∀ z ∈ Z, ∀ g ∈ T, g * z = z * g)
    (hcen : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x ∈ Z) (hc : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Z)
    (hZ : Nat.card Z = p) {n : ℕ} (hn : n ≤ 4) (hT : Nat.card T = p ^ (1 + n)) (hET : E ≤ T)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card (E ⊔ Z : Subgroup G) ≤ p ^ (1 + n / 2) := by
  set A := E ⊔ Z with hAdef
  have hAT : A ≤ T := sup_le hET hZT
  have hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    have h1 : A ≤ Subgroup.centralizer (E : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hE y hy x hx)
        (fun z hz => Subgroup.mem_centralizer_iff.mpr fun y hy => hZc z hz y (hET hy))
    have h2 : A ≤ Subgroup.centralizer (A : Set G) :=
      sup_le (Subgroup.le_centralizer_iff.mp h1)
        (fun z hz => Subgroup.mem_centralizer_iff.mpr fun y hy => hZc z hz y (hAT hy))
    exact fun x hx y hy => Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  have hp1 := hp.one_lt
  obtain ⟨j, hjn, hjA⟩ : ∃ j, j ≤ 1 + n ∧ Nat.card A = p ^ j := by
    have h := Subgroup.card_dvd_of_le hAT
    rw [hT] at h
    exact (Nat.dvd_prime_pow hp).mp h
  rw [hjA]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hcon
  rcases Nat.lt_or_ge j (1 + n) with hlt | hge
  ·
    have hjn' : j = n := by omega
    have hAT' : A < T := lt_of_le_of_ne hAT fun h => by
      have h' : p ^ j = p ^ (1 + n) := by rw [← hjA, ← hT, h]
      have := Nat.pow_right_injective hp.two_le h'
      omega
    obtain ⟨t, htT, htA⟩ := IsConcreteLE.exists_of_lt hAT'
    have hBT : A ⊔ Subgroup.zpowers t ≤ T := sup_le hAT (Subgroup.zpowers_le.mpr htT)
    have hTB : T ≤ A ⊔ Subgroup.zpowers t := by
      have hB := Subgroup.card_dvd_of_le hBT
      rw [hT] at hB
      obtain ⟨i, hi, hiB⟩ := (Nat.dvd_prime_pow hp).mp hB
      have hAi := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ Subgroup.zpowers t)
      rw [hjA, hiB, Nat.pow_dvd_pow_iff_le_right hp1] at hAi
      have hi' : i = 1 + n := by
        by_contra hne
        have hBA : A = A ⊔ Subgroup.zpowers t :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hiB, hjA]; rw [show i = j by omega])
        exact htA (hBA ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      exact (Subgroup.eq_of_le_of_card_ge hBT (by rw [hT, hiB, hi'])).ge
    have h := card_le_card_mul_card_of_le_sup_zpowers hZT hZc hcen hc hAT hA htT hTB
    rw [hjA, hZ, ← pow_two, Nat.pow_le_pow_iff_right hp1] at h
    omega
  ·
    have hj : j = 1 + n := le_antisymm hjn hge
    have hAT' : A = T := Subgroup.eq_of_le_of_card_ge hAT (by rw [hT, hjA, hj])
    have hTZ : T ≤ Z := fun x hx =>
      hcen x hx fun y hy => hA x (hAT' ▸ hx) y (hAT' ▸ hy)
    have h := Subgroup.card_le_of_le hTZ
    rw [hT, hZ] at h
    have : 1 + n ≤ 1 := (Nat.pow_le_pow_iff_right hp1).mp (by simpa using h)
    omega

end Isotropic

theorem forall_pow_eq_one_and_card_le_of_cover {K : Type} [Group K] [Finite K]
    [Group.IsPerfect K] {p : ℕ} (hp : p.Prime) (hZ1 : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (T : Sylow p K) {n : ℕ} (hn : n ≤ 4)
    (hcard : Nat.card (T : Subgroup K) = Nat.card (Subgroup.center K) * p ^ n)
    (hc : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ∈ Subgroup.center K)
    (hcp : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ^ p = 1)
    (hcen : (∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x * y = y * x) ∨
      ∀ x ∈ (T : Subgroup K), (∀ y ∈ (T : Subgroup K), x * y = y * x) →
        x ∈ Subgroup.center K)
    (hpow : ∀ x ∈ (T : Subgroup K), ∃ z ∈ Subgroup.center K, x ^ p = z ^ p) :
    (∀ t ∈ (T : Subgroup K), t ^ p = 1) ∧ ∀ E : Subgroup K, E ≤ (T : Subgroup K) →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hZT' : Subgroup.center K ≤ ⁅(T : Subgroup K), (T : Subgroup K)⁆ := fun z hz => by
    obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
    exact center_le_commutator_of_isPerfect T hz ⟨k, congrArg Subtype.val hk⟩
  have hT' : ∀ z ∈ ⁅(T : Subgroup K), (T : Subgroup K)⁆, z ∈ Subgroup.center K ∧ z ^ p = 1 := by
    intro z hz
    rw [Subgroup.commutator_def] at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨hc a ha b hb, hcp a ha b hb⟩
    | one => exact ⟨Subgroup.one_mem _, one_pow p⟩
    | mul x y _ _ hx hy =>
      refine ⟨Subgroup.mul_mem _ hx.1 hy.1, ?_⟩
      have hxy : Commute x y := Subgroup.mem_center_iff.mp hy.1 x
      rw [hxy.mul_pow, hx.2, hy.2, one_mul]
    | inv x _ hx => exact ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩
  have hZexp : ∀ z ∈ Subgroup.center K, z ^ p = 1 := fun z hz => (hT' z (hZT' hz)).2
  have hZcard : Nat.card (Subgroup.center K) = p := by
    have hdvd : Nat.card (Subgroup.center K) ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hZexp _ g.2)
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ1
    · exact h
  have hnc : ¬ ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x * y = y * x := by
    intro h
    apply hZ1
    have hbot : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => h y hy x hx
    exact le_bot_iff.mp (hbot ▸ hZT')
  have hZT := hcen.resolve_left hnc
  refine ⟨fun t ht => ?_, fun E hET hE => ?_⟩
  · obtain ⟨z, hz, hzt⟩ := hpow t ht
    rw [hzt, hZexp z hz]
  · have hZle : Subgroup.center K ≤ (T : Subgroup K) := IsPGroup.le_sylow_of_normal hZp T
    have hTcard : Nat.card (T : Subgroup K) = p ^ (1 + n) := by
      rw [hcard, hZcard, pow_add, pow_one]
    calc Nat.card E ≤ Nat.card (E ⊔ Subgroup.center K : Subgroup K) :=
          Subgroup.card_le_of_le le_sup_left
      _ ≤ p ^ (1 + n / 2) := card_sup_le_pow_of_commute hp hZle
          (fun z hz g _ => Subgroup.mem_center_iff.mp hz g) hZT hc hZcard hn hTcard hET hE
      _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by omega)

end CFSG.AGLEmbedding
