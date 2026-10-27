module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase

public section

namespace CertificateChecks.KernelFi23Nt

open CFSG.Sporadic.Fi23 CFSG.Perm
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.LocalAnalysis.GLTheoremA.H1017 CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

section General

variable {G : Type} [Group G] [Finite G]

theorem card_inf_mul_relIndex (H K : Subgroup G) :
    Nat.card ↥(H ⊓ K) * H.relIndex K = Nat.card K := by
  rw [← Subgroup.inf_relIndex_right, Subgroup.relIndex,
    ← Subgroup.card_mul_index ((H ⊓ K).subgroupOf K),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv]

theorem eq_of_card_inf_centralizer_le {Q A₀ A : Subgroup G} (hA₀Q : A₀ ≤ Q)
    (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hc₀ : Nat.card A₀ = 81) (hAQ : A ≤ Q)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hc : Nat.card A = 81)
    (hcent : ∀ x ∈ Q, x ∉ A₀ → Nat.card ↥(A₀ ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 9)
    (hQ : Nat.card Q * 9 < 81 * 81 ∨
      (Nat.card Q = 729 ∧ Nat.card ↥(A₀ ⊓ Subgroup.centralizer (Q : Set G)) < 9)) :
    A = A₀ := by
  by_contra hne
  have hnle : ¬ A ≤ A₀ := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc₀]))
  obtain ⟨x, hxA, hxA₀⟩ := SetLike.not_le_iff_exists.1 hnle
  have hI : A₀ ⊓ A ≤ A₀ ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨hy.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro z rfl
    exact hA z hxA y hy.2
  have hcI : Nat.card ↥(A₀ ⊓ A) ≤ 9 :=
    (Subgroup.card_le_of_le hI).trans (hcent x (hAQ hxA) hxA₀)
  have hrA := card_inf_mul_relIndex A₀ A
  have hrQ := card_inf_mul_relIndex A₀ Q
  rw [inf_of_le_left hA₀Q, hc₀] at hrQ
  rw [hc] at hrA
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hrQ0 : A₀.relIndex Q ≠ 0 := by
    intro h0
    rw [h0] at hrQ
    omega
  have hle := Subgroup.relIndex_le_of_le_right hAQ hrQ0
  have h9 : 9 ≤ A₀.relIndex A := by
    by_contra hlt
    have : Nat.card ↥(A₀ ⊓ A) * A₀.relIndex A ≤ 9 * 8 :=
      Nat.mul_le_mul hcI (by omega)
    omega
  rcases hQ with hQ | ⟨hQ, hZ⟩
  · have : 81 * 9 ≤ 81 * A₀.relIndex Q := Nat.mul_le_mul_left _ (h9.trans hle)
    omega
  ·
    have hr9 : A₀.relIndex Q = 9 := by omega
    have hrA9 : A₀.relIndex A = 9 := by omega
    have hcI9 : Nat.card ↥(A₀ ⊓ A) = 9 := by
      rw [hrA9] at hrA
      omega
    have hSQ : A ⊔ A₀ ≤ Q := sup_le hAQ hA₀Q
    have hmul := Subgroup.relIndex_mul_relIndex A₀ (A ⊔ A₀) Q le_sup_right hSQ
    rw [hr9] at hmul
    have hS0 : A₀.relIndex (A ⊔ A₀) ≠ 0 := by
      intro h0
      rw [h0] at hmul
      omega
    have hS9 : 9 ≤ A₀.relIndex (A ⊔ A₀) :=
      hrA9 ▸ Subgroup.relIndex_le_of_le_right le_sup_left hS0
    have hS1 : (A ⊔ A₀).relIndex Q = 1 := by
      have hpos : 0 < (A ⊔ A₀).relIndex Q := by
        rcases Nat.eq_zero_or_pos ((A ⊔ A₀).relIndex Q) with h | h
        · rw [h] at hmul
          omega
        · exact h
      by_contra h1
      have : 9 * 2 ≤ A₀.relIndex (A ⊔ A₀) * (A ⊔ A₀).relIndex Q :=
        Nat.mul_le_mul hS9 (by omega)
      omega
    have hQS : Q ≤ A ⊔ A₀ := Subgroup.relIndex_eq_one.1 hS1
    have hIZ : A₀ ⊓ A ≤ A₀ ⊓ Subgroup.centralizer (Q : Set G) := by
      intro y hy
      refine Subgroup.mem_inf.2 ⟨hy.1, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      have hle' : A ⊔ A₀ ≤ Subgroup.centralizer ({y} : Set G) := by
        refine sup_le (fun a ha => ?_) (fun a ha => ?_) <;>
          refine Subgroup.mem_centralizer_iff.2 ?_ <;> rintro z rfl
        · exact hA z hy.2 a ha
        · exact hA₀ z hy.1 a ha
      have := Subgroup.mem_centralizer_iff.1 (hle' (hQS hq)) y rfl
      exact this.symm
    have := Subgroup.card_le_of_le hIZ
    omega

theorem inf_centralizer_mul_eq {A₀ : Subgroup G} (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a)
    (t : G) {a : G} (ha : a ∈ A₀) :
    A₀ ⊓ Subgroup.centralizer ({t * a} : Set G) = A₀ ⊓ Subgroup.centralizer ({t} : Set G) := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, and_congr_right_iff]
  intro hy
  have hay := hA₀ a ha y hy
  constructor
  · intro e
    refine mul_right_cancel (b := a) ?_
    calc y * t * a = y * (t * a) := mul_assoc _ _ _
      _ = t * a * y := e
      _ = t * (a * y) := mul_assoc _ _ _
      _ = t * (y * a) := by rw [hay]
      _ = t * y * a := (mul_assoc _ _ _).symm
  · intro e
    calc y * (t * a) = y * t * a := (mul_assoc _ _ _).symm
      _ = t * y * a := by rw [e]
      _ = t * (y * a) := mul_assoc _ _ _
      _ = t * (a * y) := by rw [hay]
      _ = t * a * y := (mul_assoc _ _ _).symm

theorem card_inf_centralizer_le_of_reps {Q A₀ : Subgroup G}
    (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) {b : ℕ}
    (hrep : ∀ x ∈ Q, x ∉ A₀ → ∃ t a, a ∈ A₀ ∧ x = t * a ∧
      Nat.card ↥(A₀ ⊓ Subgroup.centralizer ({t} : Set G)) ≤ b) :
    ∀ x ∈ Q, x ∉ A₀ → Nat.card ↥(A₀ ⊓ Subgroup.centralizer ({x} : Set G)) ≤ b := by
  intro x hx hxA
  obtain ⟨t, a, ha, rfl, hb⟩ := hrep x hx hxA
  rwa [inf_centralizer_mul_eq hA₀ t ha]

theorem card_inf_centralizer_lt_of_injective {Q : Subgroup G} (hQ : Nat.card Q = 729) {c : G}
    (f : Fin 4 → G) (hf : ∀ i, f i ∈ Q) (hinj : Function.Injective fun i => f i * c * (f i)⁻¹) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({c} : Set G)) < 243 := by
  set S := Subgroup.centralizer ({c} : Set G)
  have hr := card_inf_mul_relIndex S Q
  rw [inf_comm, hQ] at hr
  have h4 : 4 ≤ S.relIndex Q := by
    let F : Fin 4 → Q ⧸ S.subgroupOf Q := fun i => QuotientGroup.mk ⟨f i, hf i⟩
    have hF : Function.Injective F := by
      intro i j e
      apply hinj
      have hm := QuotientGroup.eq.1 e
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hm
      have hc := Subgroup.mem_centralizer_iff.1 hm c rfl
      simp only
      calc f i * c * (f i)⁻¹ = f i * (c * ((f i)⁻¹ * f j)) * (f j)⁻¹ := by group
        _ = f i * ((f i)⁻¹ * f j * c) * (f j)⁻¹ := by rw [hc]
        _ = f j * c * (f j)⁻¹ := by group
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this
  have : Nat.card ↥(Q ⊓ S) * 4 ≤ 729 := hr ▸ Nat.mul_le_mul_left _ h4
  omega

theorem card_le_of_determined {K : Subgroup G} (f : G → ℕ) (T : Finset ℕ)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, f x = f y → x = y) (hT : ∀ x ∈ K, f x ∈ T) :
    Nat.card K ≤ T.card := by
  let F : K → T := fun x => ⟨f x, hT x x.2⟩
  have hF : Function.Injective F := fun x y e =>
    Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val e))
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_eq_fintype_card (α := T), Fintype.card_coe] at this

theorem pElemsClosed_of_card_two_mul_pow {K : Subgroup G} {n : ℕ} (hK : Nat.card K = 2 * 3 ^ n) :
    PElemsClosed 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 K))
  have hP : Nat.card P = 3 ^ n := by
    rw [Sylow.card_eq_multiplicity, hK, mul_comm,
      factorization_three_pow_mul n 2 (by norm_num)]
  have hi : (P : Subgroup K).index = 2 := by
    have := Subgroup.card_mul_index (P : Subgroup K)
    rw [hP, hK] at this
    have h3 : 0 < 3 ^ n := by positivity
    have : 3 ^ n * (P : Subgroup K).index = 3 ^ n * 2 := by rw [this, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left h3 this
  have hN : (P : Subgroup K).Normal := Subgroup.normal_of_index_eq_two hi
  have := Sylow.unique_of_normal P hN
  have hmem : ∀ a : K, (∃ m, a ^ 3 ^ m = 1) → a ∈ (P : Subgroup K) := by
    rintro a ⟨m, hm⟩
    have hZ : IsPGroup 3 (Subgroup.zpowers a) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hm)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
    obtain ⟨R, hR⟩ := hZ.exists_le_sylow
    rw [Subsingleton.elim R P] at hR
    exact hR (Subgroup.mem_zpowers a)
  intro a ha b hb ⟨m, hm⟩ ⟨m', hm'⟩
  have hPa := hmem ⟨a, ha⟩ ⟨m, Subtype.ext (by simpa using hm)⟩
  have hPb := hmem ⟨b, hb⟩ ⟨m', Subtype.ext (by simpa using hm')⟩
  have hab := (P : Subgroup K).mul_mem hPa hPb
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨_, hab⟩
  refine ⟨k, ?_⟩
  have := pow_orderOf_eq_one (⟨_, hab⟩ : (P : Subgroup K))
  rw [hk] at this
  simpa using congrArg (fun z : (P : Subgroup K) => ((z : K) : G)) this

theorem card_centralizer_map_conj (g : G) (D : Subgroup G) :
    Nat.card ↥(Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card ↥(Subgroup.centralizer (D : Set G)) := by
  rw [centralizer_map_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem conj_comm_iff (g c c' : G) :
    g * c * g⁻¹ * (g * c' * g⁻¹) = g * c' * g⁻¹ * (g * c * g⁻¹) ↔ c * c' = c' * c := by
  have e1 : g * c * g⁻¹ * (g * c' * g⁻¹) = g * (c * c') * g⁻¹ := by group
  have e2 : g * c' * g⁻¹ * (g * c * g⁻¹) = g * (c' * c) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro e
    simpa using e
  · intro e
    rw [e]

end General

section Fi23


theorem conjPt_idx (g : CFSG.Sporadic.Fi23.J) {k : ℕ} (hk : k < 31671) :
    g * conjPt k * g⁻¹ = conjPt (idx 31671 g k) :=
  (idx_eq_iff hk (idx_lt g hk)).1 rfl

theorem factB_of_math {Q A₀ : Subgroup CFSG.Sporadic.Fi23.J} (F : List ℕ)
    (hQdd : Q ≤ Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J))
    (hQ : Nat.card Q = 729) (hA₀Q : A₀ ≤ Q) (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a)
    (hc₀ : Nat.card A₀ = 81)
    (hcent : ∀ x ∈ Q, x ∉ A₀ → Nat.card ↥(A₀ ⊓ Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) ≤ 9)
    (hZ : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (Q : Set CFSG.Sporadic.Fi23.J)) < 9)
    (hfix : ∀ p < 31671, A₀ ≤ Subgroup.centralizer ({conjPt p} : Set CFSG.Sporadic.Fi23.J) → p ∈ F)
    (hpair : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → conjPt p * conjPt q = conjPt q * conjPt p →
      conjPt p * conjPt q * (d * d1) = d * d1 * (conjPt p * conjPt q) →
      (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0))
    (hstab : ∀ k < 31671, k ≠ 0 → k ≠ 1 → conjPt k * d = d * conjPt k →
      conjPt k * d1 = d1 * conjPt k →
      ∃ f : Fin 4 → CFSG.Sporadic.Fi23.J, (∀ i, f i ∈ Q) ∧ Function.Injective fun i => idx 31671 (f i) k) :
    FactB := by
  refine ⟨Q, hQdd, hQ, ?_, ?_⟩
  · intro A hAQ hA hcA p hp q hq hpq hAp hAq hcomm hpd
    have e : A = A₀ := eq_of_card_inf_centralizer_le hA₀Q hA₀ hc₀ hAQ
      (fun a ha b hb => comm_of_isElemAbelian' hA ha hb) hcA hcent (Or.inr ⟨hQ, hZ⟩)
    subst e
    exact hpair p (hfix p hp hAp) q (hfix q hq hAq) hpq hcomm hpd
  · intro k hk hk0 hk1 hkd hkd1
    obtain ⟨f, hfQ, hinj⟩ := hstab k hk hk0 hk1 hkd hkd1
    refine card_inf_centralizer_lt_of_injective hQ f hfQ fun i j e => hinj ?_
    simp only [conjPt_idx _ hk] at e
    by_contra hne
    exact conjPt_ne (idx_lt _ hk) (idx_lt _ hk) hne e

theorem factC_of_math {Q A₀ C' : Subgroup CFSG.Sporadic.Fi23.J} (h : CFSG.Sporadic.Fi23.J) {ν₀ : ℕ} (hν₀ : ν₀ < 31671)
    (S : List (CFSG.Sporadic.Fi23.J × Bool)) (T : Finset ℕ)
    (hQt : Q ≤ Subgroup.centralizer ({t2} : Set CFSG.Sporadic.Fi23.J)) (hQ : Nat.card Q = 243) (hA₀Q : A₀ ≤ Q)
    (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hc₀ : Nat.card A₀ = 81)
    (hcent : ∀ x ∈ Q, x ∉ A₀ → Nat.card ↥(A₀ ⊓ Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) ≤ 9)
    (hy : ∀ t < 6, ∃ y ∈ A₀, idx 31671 (h * y) ν₀ = t)
    (hSA : ∀ s ∈ S, s.1 ∈ A₀)
    (hν₀S : ∀ s ∈ S, (conjPt ν₀ * conjPt (idx 31671 s.1 ν₀) =
      conjPt (idx 31671 s.1 ν₀) * conjPt ν₀ ↔ s.2 = true))
    (hT : ∀ ν < 31671, (∀ s ∈ S, (conjPt ν * conjPt (idx 31671 s.1 ν) =
      conjPt (idx 31671 s.1 ν) * conjPt ν ↔ s.2 = true)) → ν ∈ T)
    (hTc : T.card ≤ 486)
    (hC'B : C' ≤ Subgroup.centralizer ((A₀.map (MulAut.conj h).toMonoidHom : Subgroup CFSG.Sporadic.Fi23.J) : Set CFSG.Sporadic.Fi23.J))
    (hC' : Nat.card C' = 486) : FactC := by
  refine ⟨Q, hQt, hQ, fun A hAQ hA hcA => ?_⟩
  have e : A = A₀ := eq_of_card_inf_centralizer_le hA₀Q hA₀ hc₀ hAQ
    (fun a ha b hb => comm_of_isElemAbelian' hA ha hb) hcA hcent (Or.inl (by rw [hQ]; norm_num))
  subst e
  set K := Subgroup.centralizer (A : Set CFSG.Sporadic.Fi23.J)
  have hcomm : ∀ g ∈ K, ∀ y ∈ A, g * y = y * g := fun g hg y hy =>
    (Subgroup.mem_centralizer_iff.1 hg y hy).symm
  have hinj : ∀ g ∈ K, ∀ g' ∈ K, idx 31671 g ν₀ = idx 31671 g' ν₀ → g = g' := by
    intro g hg g' hg' e
    have key : ∀ x ∈ K, ∀ t < 6, ∀ y ∈ A, idx 31671 (h * y) ν₀ = t →
        idx 31671 (h * x * h⁻¹) t = idx 31671 (h * y) (idx 31671 x ν₀) := by
      intro x hx t _ y hyA hyt
      have e1 : h * x * h⁻¹ * (h * y) = h * (x * y) := by group
      have e2 : h * x * h⁻¹ * (h * y) = h * y * x := by
        rw [e1, hcomm x hx y hyA, mul_assoc]
      rw [← hyt, ← idx_mul, ← idx_mul, e2]
    have hb : h * g * h⁻¹ = h * g' * h⁻¹ := eq_of_base fun t ht => by
      obtain ⟨y, hyA, hyt⟩ := hy t ht
      rw [key g hg t ht y hyA hyt, key g' hg' t ht y hyA hyt, e]
    simpa using hb
  have hpass : ∀ g ∈ K, idx 31671 g ν₀ ∈ T := by
    intro g hg
    refine hT _ (idx_lt g hν₀) fun s hs => ?_
    have hsn : idx 31671 s.1 (idx 31671 g ν₀) = idx 31671 g (idx 31671 s.1 ν₀) := by
      rw [← idx_mul, ← idx_mul, hcomm g hg s.1 (hSA s hs)]
    rw [hsn, ← conjPt_idx g hν₀, ← conjPt_idx g (idx_lt _ hν₀), conj_comm_iff]
    exact hν₀S s hs
  have hK : Nat.card K ≤ 486 :=
    (card_le_of_determined (fun g => idx 31671 g ν₀) T hinj hpass).trans hTc
  have hKB : Nat.card ↥(Subgroup.centralizer
      ((A.map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J)) = 486 := by
    have h1 := Subgroup.card_le_of_le hC'B
    rw [hC', card_centralizer_map_conj] at h1
    rw [card_centralizer_map_conj]
    exact le_antisymm hK h1
  have h2 : Nat.card ↥(Subgroup.centralizer
      ((A.map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J)) = 2 * 3 ^ 5 := by
    rw [hKB]
    norm_num
  exact pElemsClosed_of_map_conj h (pElemsClosed_of_card_two_mul_pow h2)

end Fi23

end CertificateChecks.KernelFi23Nt
