module

public import CFSG.CharacterTheory.BrauerLinearThree.LocalFacts
public import CFSG.CharacterTheory.BrauerLinearThree.LocalSetting
public import CFSG.CharacterTheory.BrauerLinearThree.SylowTools

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

section Joins

variable {G : Type} [Group G]

theorem commutes_sup {H K : Subgroup G} (hH : Commutes H H) (hK : Commutes K K)
    (hHK : Commutes H K) : Commutes (H ⊔ K) (H ⊔ K) := by
  have h1 : H ⊔ K ≤ Subgroup.centralizer (H : Set G) := by
    apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hH h hh x hx
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hHK h hh x hx
  have h2 : H ⊔ K ≤ Subgroup.centralizer (K : Set G) := by
    apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hHK x hx k hk).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact hK k hk x hx
  have h3 : H ⊔ K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
    apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (h1 hy)) x hx).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (h2 hy)) x hx).symm
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (h3 hb)) a ha

theorem Inverts.sup {t : G} {H K : Subgroup G} (hH : Inverts t H) (hK : Inverts t K)
    (hc : Commutes (H ⊔ K) (H ⊔ K)) : Inverts t (H ⊔ K) := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ H ⊔ K ∧ t * x * t⁻¹ = x⁻¹}
      one_mem' := ⟨(H ⊔ K).one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨(H ⊔ K).mul_mem hx hy, ?_⟩
        calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx', hy']
          _ = (y * x)⁻¹ := by group
          _ = (x * y)⁻¹ := by rw [hc x hx y hy]
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨(H ⊔ K).inv_mem hx, ?_⟩
        calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          _ = x⁻¹⁻¹ := by rw [hx'] }
  have hle : H ⊔ K ≤ S := by
    apply sup_le
    · intro x hx
      exact ⟨Subgroup.mem_sup_left hx, hH x hx⟩
    · intro x hx
      exact ⟨Subgroup.mem_sup_right hx, hK x hx⟩
  intro x hx
  exact (hle hx).2

theorem isPGroup_of_forall_pow {p : ℕ} {H : Subgroup G} (h : ∀ x ∈ H, x ^ p = 1) :
    IsPGroup p H := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using h x x.2)⟩

end Joins

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

omit [Finite F] in
theorem isTorus_J : IsTorus φ J := ⟨rfl, (J_commute_invJ₁ φ).symm⟩

omit [Finite F] in
theorem isTorus_invJ₁ : IsTorus φ (invJ₁ φ) := ⟨J_commute_invJ₁ φ, rfl⟩

omit [Finite F] in
theorem rootUp_one_ne_one (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) :
    rootUp φ 1 ≠ 1 := by
  intro h
  have h0 : rootUp φ 0 = 1 := by rw [rootUp, upperGL_zero, map_one]
  exact one_ne_zero (rootUp_injective φ hZ (h.trans h0.symm))

omit [Finite F] in
theorem rootUp_one_mem : rootUp φ 1 ∈ rootX₁ φ := (mem_rootX₁ φ).mpr ⟨1, rfl⟩

section Setting

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
include hZ h2 in
theorem orderOf_invJ₁ : orderOf (invJ₁ φ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [sq]
    exact invJ₁_mul_self φ
  · intro h
    have h1 := inverts_invJ₁_rootX₁ φ _ (rootUp_one_mem φ)
    rw [h, one_mul, inv_one, mul_one, ← rootUp_neg] at h1
    have h3 := rootUp_injective φ hZ h1.symm
    apply h2
    linear_combination -h3

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem invJ₂_mul_self : invJ₂ φ * invJ₂ φ = 1 := by
  rw [invJ₂_eq φ hZ hZodd h2 hJ]
  calc J * invJ₁ φ * (J * invJ₁ φ) = (J * J) * (invJ₁ φ * invJ₁ φ) := by
        rw [mul_assoc J (invJ₁ φ), ← mul_assoc (invJ₁ φ) J, ← J_commute_invJ₁ φ]
        group
    _ = 1 := by rw [J_mul_self hJ, invJ₁_mul_self, one_mul]

include hZ hZodd h2 hJ in
theorem card_eq_mul_of_isPGroup [Finite G] (M : Subgroup G) (hMp : IsPGroup (ringChar F) M)
    (hMJ : ∀ m ∈ M, J * m * J⁻¹ ∈ M) (hMJ₁ : ∀ m ∈ M, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ M) :
    Nat.card M = Nat.card (M ⊓ Subgroup.centralizer {J} : Subgroup G) *
      Nat.card (M ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) *
      Nat.card (M ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  have hp2 : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  have hodd : Odd (Nat.card M) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hMp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have h := card_mul_card_sq_eq_of_four hJ (orderOf_invJ₁ φ hZ h2) (J_commute_invJ₁ φ)
    (J_ne_invJ₁ φ hZ h2) M hodd hMJ hMJ₁
  have hbot : (M ⊓ Subgroup.centralizer {J} ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) =
      ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨hxM, hxJ⟩, hxJ₁⟩ := hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hMp ⟨x, hxM⟩
    exact eq_one_of_isTorus_of_pow_eq_one φ hZ hZodd h2
      ⟨(Subgroup.mem_centralizer_singleton_iff.mp hxJ).symm,
        (Subgroup.mem_centralizer_singleton_iff.mp hxJ₁).symm⟩ (k := k)
      (by simpa using congrArg Subtype.val hk)
  rw [hbot, Subgroup.card_bot, one_pow, mul_one, ← invJ₂_eq φ hZ hZodd h2 hJ] at h
  exact h

include hZ h2 in
theorem card_centralizer_eq_rootUp_one {z : G} (hzJ : J * z = z * J) (hz1 : z ≠ 1)
    (hzp : z ^ ringChar F = 1) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
  obtain ⟨h, -, hh⟩ := exists_conj_mem_rootX₁ φ hZ h2 hzJ hzp
  have hh1 : h * z * h⁻¹ ≠ 1 := by
    intro h'
    apply hz1
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = 1 := by rw [h']; group
  obtain ⟨t, -, ht⟩ := torusTransitive_rootX₁ φ _ hh _ (rootUp_one_mem φ) hh1
    (rootUp_one_ne_one φ hZ)
  rw [conjHom_apply] at ht
  rw [← ht, show t * (h * z * h⁻¹) * t⁻¹ = (t * h) * z * (t * h)⁻¹ by group,
    card_centralizer_conj]

omit [Finite F] in
include hZ in
theorem commutes_rootX₁_of_commute_rootUp_one {A : Subgroup G}
    (hA : ∀ t, IsTorus φ t → A.map (conjHom t) = A)
    (hcomm : ∀ a ∈ A, a * rootUp φ 1 = rootUp φ 1 * a) : Commutes (rootX₁ φ) A := by
  intro x hx a ha
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  obtain ⟨t, ht, htx⟩ := torusTransitive_rootX₁ φ _ (rootUp_one_mem φ) x hx
    (rootUp_one_ne_one φ hZ) hx1
  have ha' : t⁻¹ * a * t ∈ A := by
    rw [← hA t⁻¹ ht.inv]
    exact ⟨a, ha, by rw [conjHom_apply, inv_inv]⟩
  have h1 := hcomm _ ha'
  rw [conjHom_apply] at htx
  rw [← htx]
  calc t * rootUp φ 1 * t⁻¹ * a = t * (rootUp φ 1 * (t⁻¹ * a * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * a * t) * rootUp φ 1) * t⁻¹ := by rw [h1]
    _ = a * (t * rootUp φ 1 * t⁻¹) := by group

section Y

variable {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

omit [Finite F] in
include hZ hZodd h2 hJ hY₁ hY₂ in
theorem commutes_rootX₁_of_mem {i j : Fin 3} (hij : i ≠ j) {a : G} (ha : a ∈ rootSub φ Y i j)
    (ha1 : a ≠ 1) (hcomm : ∀ x ∈ rootX₁ φ, x * a = a * x) :
    Commutes (rootX₁ φ) (rootSub φ Y i j) := by
  intro x hx b hb
  by_cases hb1 : b = 1
  · rw [hb1, mul_one, one_mul]
  obtain ⟨t, ht, htab⟩ := rootSub_transitive φ hZ hZodd h2 hJ hY₁ hY₂ hij a ha b hb ha1 hb1
  have hx' : t⁻¹ * x * t ∈ rootX₁ φ := by
    rw [← torus_map_rootX₁ φ hZ hZodd h2 ht.inv]
    exact ⟨x, hx, by rw [conjHom_apply, inv_inv]⟩
  have h1 := hcomm _ hx'
  rw [conjHom_apply] at htab
  rw [← htab]
  calc x * (t * a * t⁻¹) = t * ((t⁻¹ * x * t) * a) * t⁻¹ := by group
    _ = t * (a * (t⁻¹ * x * t)) * t⁻¹ := by rw [h1]
    _ = t * a * t⁻¹ * x := by group

section PCore

variable (N : Subgroup G) (hN : N ≤ Subgroup.centralizer {rootUp φ 1})
  (hNp : IsPGroup (ringChar F) N)
  (hNall : ∀ x ∈ Subgroup.centralizer ({rootUp φ 1} : Set G), ∀ k : ℕ,
    x ^ (ringChar F ^ k) = 1 → x ∈ N)

omit [Finite F] in
include hN hNp hNall in
theorem conj_mem_pcore {t : G}
    (ht : t * rootUp φ 1 * t⁻¹ = rootUp φ 1 ∨ t * rootUp φ 1 * t⁻¹ = (rootUp φ 1)⁻¹)
    {x : G} (hx : x ∈ N) : t * x * t⁻¹ ∈ N := by
  obtain ⟨k, hk⟩ := hNp ⟨x, hx⟩
  have hk' : x ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
  apply hNall _ _ k (by rw [conj_pow, hk', mul_one, mul_inv_cancel])
  have hxQ := Subgroup.mem_centralizer_singleton_iff.mp (hN hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := commute_conj t hxQ
  rcases ht with ht | ht
  · rwa [ht] at h1
  · rw [ht] at h1
    exact (Commute.inv_right_iff.mp h1).eq

omit [Finite F] in
include hN hNp hNall in
theorem conj_J_mem_pcore {x : G} (hx : x ∈ N) : J * x * J⁻¹ ∈ N :=
  conj_mem_pcore φ N hN hNp hNall
    (Or.inl (by rw [commute_J_of_mem_rootX₁ (rootUp_one_mem φ), mul_inv_cancel_right])) hx

omit [Finite F] in
include hN hNp hNall in
theorem conj_invJ₁_mem_pcore {x : G} (hx : x ∈ N) : invJ₁ φ * x * (invJ₁ φ)⁻¹ ∈ N :=
  conj_mem_pcore φ N hN hNp hNall (Or.inr (inverts_invJ₁_rootX₁ φ _ (rootUp_one_mem φ))) hx

omit [Finite F] in
include hZ hZodd h2 hJ hN hNp hNall in
theorem conj_invJ₂_mem_pcore {x : G} (hx : x ∈ N) : invJ₂ φ * x * (invJ₂ φ)⁻¹ ∈ N := by
  rw [invJ₂_eq φ hZ hZodd h2 hJ, show J * invJ₁ φ * x * (J * invJ₁ φ)⁻¹ =
    J * (invJ₁ φ * x * (invJ₁ φ)⁻¹) * J⁻¹ by group]
  exact conj_J_mem_pcore φ N hN hNp hNall (conj_invJ₁_mem_pcore φ N hN hNp hNall hx)

omit [Finite F] in
include hNall in
theorem rootX₁_le_pcore : rootX₁ φ ≤ N := by
  intro x hx
  apply hNall x _ 1 (by rw [pow_one]; exact pow_ringChar_of_mem_rootX₁ hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact comm_rootX₁ x hx _ (rootUp_one_mem φ)

include hZ hZodd h2 hN hNp in
theorem mem_rootX₁_of_mem_pcore {x : G} (hx : x ∈ N) (hxJ : J * x = x * J) :
    x ∈ rootX₁ φ := by
  have hxQ := Subgroup.mem_centralizer_singleton_iff.mp (hN hx)
  obtain ⟨a, b, hab⟩ := centralizer_rootUp φ hZ hZodd h2 one_ne_zero hxJ hxQ
  obtain ⟨k, hk⟩ := hNp ⟨x, hx⟩
  have hk' : x ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hk'' : x ^ (ringChar F ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
  set s := linearCentralizerHom φ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) with hs_def
  have hsC : s ∈ centerSub φ := (mem_centerSub φ).mpr ⟨a, rfl⟩
  have hsc : Commute s (rootUp φ b) := commute_of_mem_centerSub φ hsC
    (linearCentralizerHom_commute φ _)
  have hbk : rootUp φ b ^ (ringChar F ^ (k + 1)) = 1 := by
    rw [pow_succ', pow_mul, rootUp_pow_ringChar, one_pow]
  have hs : s ^ (ringChar F ^ (k + 1)) = 1 := by
    rw [hab, hsc.mul_pow, hbk, mul_one] at hk''
    exact hk''
  have hst : IsTorus φ s :=
    ⟨(commute_of_mem_centerSub φ hsC (rfl : J * J = J * J)).symm,
      (commute_of_mem_centerSub φ hsC (J_commute_invJ₁ φ)).symm⟩
  have hs1 := eq_one_of_isTorus_of_pow_eq_one φ hZ hZodd h2 hst hs
  rw [hab, hs1, one_mul]
  exact (mem_rootX₁ φ).mpr ⟨b, rfl⟩

include hZ hZodd h2 hJ hY₁ hY₂ hN hNp hNall in
theorem pcore_inf_invJ₁_le [Finite G] :
    (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) ≤ rootSub φ Y 1 2 ∨
      (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) ≤ rootSub φ Y 2 1 := by
  apply le_or_le_of_forall_mem_or
  have hJ₂J₁ : invJ₂ φ * invJ₁ φ = invJ₁ φ * invJ₂ φ := by
    rw [invJ₂_eq φ hZ hZodd h2 hJ, ← mul_assoc (invJ₁ φ) J, ← J_commute_invJ₁ φ]
  have hnorm : ∀ h ∈ (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G),
      invJ₂ φ * h * (invJ₂ φ)⁻¹ ∈ (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) := by
    intro h hh
    obtain ⟨hhN, hhJ₁⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨conj_invJ₂_mem_pcore φ hZ hZodd h2 hJ N hN hNp hNall hhN, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hhJ₁ ⊢
    have h1 := commute_conj (invJ₂ φ) hhJ₁
    rwa [show invJ₂ φ * invJ₁ φ * (invJ₂ φ)⁻¹ = invJ₁ φ by
      rw [hJ₂J₁, mul_inv_cancel_right]] at h1
  have hfree : ∀ h ∈ (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G),
      invJ₂ φ * h * (invJ₂ φ)⁻¹ = h → h = 1 := by
    intro h hh hfix
    obtain ⟨hhN, hhJ₁⟩ := Subgroup.mem_inf.mp hh
    have hJ₂h : invJ₂ φ * h = h * invJ₂ φ := by
      calc invJ₂ φ * h = invJ₂ φ * h * (invJ₂ φ)⁻¹ * invJ₂ φ := by group
        _ = h * invJ₂ φ := by rw [hfix]
    have hJ₁h : invJ₁ φ * h = h * invJ₁ φ :=
      (Subgroup.mem_centralizer_singleton_iff.mp hhJ₁).symm
    have hJh : J * h = h * J := by
      rw [← invJ₂_mul_invJ₁ φ hZ hZodd h2 hJ, mul_assoc, hJ₁h, ← mul_assoc, hJ₂h, mul_assoc]
    obtain ⟨k, hk⟩ := hNp ⟨h, hhN⟩
    exact eq_one_of_isTorus_of_pow_eq_one φ hZ hZodd h2 ⟨hJh, hJ₁h⟩ (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hinv := inv_eq_of_fixedPointFree_involution (invJ₂_mul_self φ hZ hZodd h2 hJ) hnorm hfree
  intro x hx
  obtain ⟨hxN, hxJ₁⟩ := Subgroup.mem_inf.mp hx
  have hxJ₁' : x * invJ₁ φ = invJ₁ φ * x := Subgroup.mem_centralizer_singleton_iff.mp hxJ₁
  have hYJ₁ : Y * invJ₁ φ * Y⁻¹ = J := conj_eq_of_inv_conj_eq hY₁
  have hYJ₂ : Y * invJ₂ φ * Y⁻¹ = invJ₁ φ := conj_eq_of_inv_conj_eq hY₂
  have hyJ : J * (Y * x * Y⁻¹) = (Y * x * Y⁻¹) * J := by
    have h1 := commute_conj Y hxJ₁'
    rw [hYJ₁] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := hNp ⟨x, hxN⟩
  have hk' : x ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hyp : (Y * x * Y⁻¹) ^ ringChar F = 1 :=
    pow_ringChar_eq_one_of_commute φ hZ hZodd h2 hyJ (k := k)
      (by rw [conj_pow, hk', mul_one, mul_inv_cancel])
  have hyinv : invJ₁ φ * (Y * x * Y⁻¹) * (invJ₁ φ)⁻¹ = (Y * x * Y⁻¹)⁻¹ := by
    calc invJ₁ φ * (Y * x * Y⁻¹) * (invJ₁ φ)⁻¹ =
          (Y * invJ₂ φ * Y⁻¹) * (Y * x * Y⁻¹) * (Y * invJ₂ φ * Y⁻¹)⁻¹ := by rw [hYJ₂]
      _ = Y * (invJ₂ φ * x * (invJ₂ φ)⁻¹) * Y⁻¹ := by group
      _ = Y * x⁻¹ * Y⁻¹ := by rw [hinv x (Subgroup.mem_inf.mpr ⟨hxN, hxJ₁⟩)]
      _ = (Y * x * Y⁻¹)⁻¹ := by group
  have hmem : ∀ X : Subgroup G, Y * x * Y⁻¹ ∈ X → x ∈ X.map (conjHom Y⁻¹) := by
    intro X hX
    exact ⟨Y * x * Y⁻¹, hX, by rw [conjHom_apply, inv_inv]; group⟩
  rcases inverted_mem_rootX φ hZ h2 hyJ hyp hyinv with h | h
  · left
    rw [rootSub_12]
    exact hmem _ h
  · right
    rw [rootSub_21]
    exact hmem _ h

include hZ hZodd h2 hJ hY₁ hY₂ hN hNp hNall in
theorem pcore_inf_invJ₂_le [Finite G] :
    (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) ≤ rootSub φ Y 2 0 ∨
      (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) ≤ rootSub φ Y 0 2 := by
  apply le_or_le_of_forall_mem_or
  have hJJ₂ : J * invJ₂ φ = invJ₂ φ * J := by
    rw [invJ₂_eq φ hZ hZodd h2 hJ, mul_assoc J (invJ₁ φ) J, ← J_commute_invJ₁ φ]
  have hnorm : ∀ h ∈ (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G),
      J * h * J⁻¹ ∈ (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
    intro h hh
    obtain ⟨hhN, hhJ₂⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨conj_J_mem_pcore φ N hN hNp hNall hhN, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hhJ₂ ⊢
    have h1 := commute_conj J hhJ₂
    rwa [show J * invJ₂ φ * J⁻¹ = invJ₂ φ by rw [hJJ₂, mul_inv_cancel_right]] at h1
  have hfree : ∀ h ∈ (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G),
      J * h * J⁻¹ = h → h = 1 := by
    intro h hh hfix
    obtain ⟨hhN, hhJ₂⟩ := Subgroup.mem_inf.mp hh
    have hJh : J * h = h * J := by
      calc J * h = J * h * J⁻¹ * J := by group
        _ = h * J := by rw [hfix]
    have hJ₂h : invJ₂ φ * h = h * invJ₂ φ :=
      (Subgroup.mem_centralizer_singleton_iff.mp hhJ₂).symm
    have hJ₁h : invJ₁ φ * h = h * invJ₁ φ := by
      rw [← J_mul_invJ₂ φ hZ hZodd h2 hJ, mul_assoc, hJ₂h, ← mul_assoc, hJh, mul_assoc]
    obtain ⟨k, hk⟩ := hNp ⟨h, hhN⟩
    exact eq_one_of_isTorus_of_pow_eq_one φ hZ hZodd h2 ⟨hJh, hJ₁h⟩ (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hinv := inv_eq_of_fixedPointFree_involution (J_mul_self hJ) hnorm hfree
  intro x hx
  obtain ⟨hxN, hxJ₂⟩ := Subgroup.mem_inf.mp hx
  have hxJ₂' : x * invJ₂ φ = invJ₂ φ * x := Subgroup.mem_centralizer_singleton_iff.mp hxJ₂
  have hY3 : Y⁻¹ * invJ₂ φ * Y = J := conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂
  have hYJ₂ : Y ^ 2 * invJ₂ φ * (Y ^ 2)⁻¹ = J := by
    have h1 : Y * invJ₂ φ * Y⁻¹ = invJ₁ φ := conj_eq_of_inv_conj_eq hY₂
    have h3 : Y * invJ₁ φ * Y⁻¹ = J := conj_eq_of_inv_conj_eq hY₁
    rw [show Y ^ 2 * invJ₂ φ * (Y ^ 2)⁻¹ = Y * (Y * invJ₂ φ * Y⁻¹) * Y⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], h1, h3]
  have hYJ : Y ^ 2 * J * (Y ^ 2)⁻¹ = invJ₁ φ := by
    have h1 : Y * J * Y⁻¹ = invJ₂ φ := conj_eq_of_inv_conj_eq hY3
    have h3 : Y * invJ₂ φ * Y⁻¹ = invJ₁ φ := conj_eq_of_inv_conj_eq hY₂
    rw [show Y ^ 2 * J * (Y ^ 2)⁻¹ = Y * (Y * J * Y⁻¹) * Y⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], h1, h3]
  have hyJ : J * (Y ^ 2 * x * (Y ^ 2)⁻¹) = (Y ^ 2 * x * (Y ^ 2)⁻¹) * J := by
    have h1 := commute_conj (Y ^ 2) hxJ₂'
    rw [hYJ₂] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := hNp ⟨x, hxN⟩
  have hk' : x ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hyp : (Y ^ 2 * x * (Y ^ 2)⁻¹) ^ ringChar F = 1 :=
    pow_ringChar_eq_one_of_commute φ hZ hZodd h2 hyJ (k := k)
      (by rw [conj_pow, hk', mul_one, mul_inv_cancel])
  have hyinv : invJ₁ φ * (Y ^ 2 * x * (Y ^ 2)⁻¹) * (invJ₁ φ)⁻¹ =
      (Y ^ 2 * x * (Y ^ 2)⁻¹)⁻¹ := by
    calc invJ₁ φ * (Y ^ 2 * x * (Y ^ 2)⁻¹) * (invJ₁ φ)⁻¹ =
          (Y ^ 2 * J * (Y ^ 2)⁻¹) * (Y ^ 2 * x * (Y ^ 2)⁻¹) * (Y ^ 2 * J * (Y ^ 2)⁻¹)⁻¹ := by
          rw [hYJ]
      _ = Y ^ 2 * (J * x * J⁻¹) * (Y ^ 2)⁻¹ := by group
      _ = Y ^ 2 * x⁻¹ * (Y ^ 2)⁻¹ := by rw [hinv x (Subgroup.mem_inf.mpr ⟨hxN, hxJ₂⟩)]
      _ = (Y ^ 2 * x * (Y ^ 2)⁻¹)⁻¹ := by group
  have hmem : ∀ X : Subgroup G, Y ^ 2 * x * (Y ^ 2)⁻¹ ∈ X → x ∈ X.map (conjHom (Y ^ 2)⁻¹) := by
    intro X hX
    exact ⟨Y ^ 2 * x * (Y ^ 2)⁻¹, hX, by rw [conjHom_apply, inv_inv]; group⟩
  rcases inverted_mem_rootX φ hZ h2 hyJ hyp hyinv with h | h
  · left
    rw [rootSub_20]
    exact hmem _ h
  · right
    rw [rootSub_02]
    exact hmem _ h

end PCore

end Y

end Setting

end CFSG.BrauerLinearThree
