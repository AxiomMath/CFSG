module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

open scoped Pointwise

namespace CFSG.GH74.GLS.Stage1.Main

theorem noout_zmod_two_mul_eq_zero {N : ℕ} [NeZero N] {i : ZMod (2 * N)} (h : 2 * i = 0) :
    i = 0 ∨ i = (N : ZMod (2 * N)) := by
  have hk : i = (i.val : ZMod (2 * N)) := (ZMod.natCast_zmod_val i).symm
  have h2 : ((2 * i.val : ℕ) : ZMod (2 * N)) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ← hk]; exact h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hN : N ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2) h2
  obtain ⟨m, hm⟩ := hN
  have hlt : i.val < 2 * N := ZMod.val_lt i
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hm2 : m < 2 := by
    by_contra hcon
    have := Nat.mul_le_mul_left N (not_lt.mp hcon)
    omega
  interval_cases m
  · left; rw [hk, hm]; simp
  · right; rw [hk, hm]; simp

theorem noout_quat_central {N : ℕ} (hN : 2 ≤ N) {X : QuaternionGroup N}
    (hX : ∀ w : QuaternionGroup N, w * X = X * w) :
    X = 1 ∨ X = QuaternionGroup.a (N : ZMod (2 * N)) := by
  have : NeZero N := ⟨by omega⟩
  have h2 : (2 : ZMod (2 * N)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod (2 * N)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  cases X with
  | a i =>
    have h := hX (QuaternionGroup.xa 0)
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h
    have h' : (0 : ZMod (2 * N)) + i = 0 - i := by injection h
    have h3 : 2 * i = 0 := by linear_combination h'
    rcases noout_zmod_two_mul_eq_zero h3 with h0 | hN'
    · left; rw [h0, QuaternionGroup.a_zero]
    · right; rw [hN']
  | xa i =>
    exfalso
    have h := hX (QuaternionGroup.a 1)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
    have h' : i - 1 = i + 1 := by injection h
    apply h2
    linear_combination -h'

theorem noout_quat_sq {N : ℕ} (hN2 : 2 ∣ N) :
    (QuaternionGroup.a (N : ZMod (2 * N)) : QuaternionGroup N) =
      QuaternionGroup.a ((N / 2 : ℕ) : ZMod (2 * N)) *
        QuaternionGroup.a ((N / 2 : ℕ) : ZMod (2 * N)) := by
  rw [QuaternionGroup.a_mul_a, ← Nat.cast_add]
  have : N / 2 + N / 2 = N := by omega
  rw [this]

theorem noout_central_unique {G : Type} [Group G] {N : ℕ} (hN : 2 ≤ N)
    (e : G ≃* QuaternionGroup N) {x y : G} (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx : ∀ z : G, z * x = x * z) (hy : ∀ z : G, z * y = y * z) : x = y := by
  have key : ∀ x : G, x ≠ 1 → (∀ z : G, z * x = x * z) →
      e x = QuaternionGroup.a (N : ZMod (2 * N)) := by
    intro x hx1 hx
    have hc : ∀ w : QuaternionGroup N, w * e x = e x * w := by
      intro w
      have := congrArg e (hx (e.symm w))
      simpa using this
    rcases noout_quat_central hN hc with h | h
    · exact absurd (e.injective (by simpa using h)) hx1
    · exact h
  exact e.injective ((key x hx1 hx).trans (key y hy1 hy).symm)

theorem noout_central_sq {G : Type} [Group G] {N : ℕ} (hN : 2 ≤ N) (hN2 : 2 ∣ N)
    (e : G ≃* QuaternionGroup N) {x : G} (hx : ∀ z : G, z * x = x * z) :
    ∃ u : G, x = u * u := by
  have hc : ∀ w : QuaternionGroup N, w * e x = e x * w := by
    intro w
    have := congrArg e (hx (e.symm w))
    simpa using this
  rcases noout_quat_central hN hc with h | h
  · exact ⟨1, by rw [mul_one]; exact e.injective (by simpa using h)⟩
  · refine ⟨e.symm (QuaternionGroup.a ((N / 2 : ℕ) : ZMod (2 * N))), ?_⟩
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, h, ← noout_quat_sq hN2]

theorem noout_not_comm {G : Type} [Group G] {N : ℕ} (hN : 2 ≤ N) (e : G ≃* QuaternionGroup N) :
    ∃ x y : G, x * y ≠ y * x := by
  by_contra hcon
  have hcon' : ∀ x y : G, x * y = y * x := fun x y => by
    by_contra h
    exact hcon ⟨x, y, h⟩
  have hc : ∀ w : QuaternionGroup N, w * QuaternionGroup.xa 0 = QuaternionGroup.xa 0 * w :=
    fun w => by
      have := congrArg e (hcon' (e.symm w) (e.symm (QuaternionGroup.xa 0)))
      simpa using this
  rcases noout_quat_central hN hc with h | h
  · rw [← QuaternionGroup.a_zero] at h
    cases h
  · cases h

theorem noout_comm_of_sq {A : Type*} [Group A] (hsq : ∀ a : A, a * a = 1) (a b : A) :
    a * b = b * a := by
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

theorem noout_sup_eq_top {G : Type} [Group G] {H₁ H₂ : Subgroup G} (hne : H₁ ≠ H₂)
    (h₁ : H₁.index = 2) (h₂ : H₂.index = 2) : H₁ ⊔ H₂ = ⊤ := by
  have hc₁ : IsCoatom H₁ := Subgroup.isCoatom_of_index_prime (by rw [h₁]; exact Nat.prime_two)
  have hc₂ : IsCoatom H₂ := Subgroup.isCoatom_of_index_prime (by rw [h₂]; exact Nat.prime_two)
  have hlt : H₁ < H₁ ⊔ H₂ := by
    refine lt_of_le_of_ne le_sup_left fun heq => ?_
    have hle : H₂ ≤ H₁ := by rw [heq]; exact le_sup_right
    rcases hle.lt_or_eq with hlt | heq'
    · exact hc₁.1 (hc₂.2 _ hlt)
    · exact hne heq'.symm
  exact hc₁.2 _ hlt

theorem noout_exists_hom_of_not_cyclic {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hnc : ¬ IsCyclic G) :
    ∃ (A : Type) (_ : Group A) (φ : G →* A), Function.Surjective φ ∧
      (∀ a b : A, a * b = b * a) ∧ (∀ a : A, a * a = 1) ∧ Nat.card A = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨H₁, H₂, hne, h₁, h₂⟩ := hG.not_isCyclic_iff_exists_ne_index_eq_prime.1 hnc
  have : H₁.Normal := Subgroup.normal_of_index_eq_two h₁
  have : H₂.Normal := Subgroup.normal_of_index_eq_two h₂
  have hc₁ : Nat.card (G ⧸ H₁) = 2 := by rw [← Subgroup.index_eq_card]; exact h₁
  have hc₂ : Nat.card (G ⧸ H₂) = 2 := by rw [← Subgroup.index_eq_card]; exact h₂
  have hsq : ∀ a : (G ⧸ H₁) × (G ⧸ H₂), a * a = 1 := by
    intro a
    refine Prod.ext ?_ ?_
    · have := pow_card_eq_one' (x := a.1)
      rw [hc₁] at this
      simpa [sq] using this
    · have := pow_card_eq_one' (x := a.2)
      rw [hc₂] at this
      simpa [sq] using this
  refine ⟨(G ⧸ H₁) × (G ⧸ H₂), inferInstance,
    (QuotientGroup.mk' H₁).prod (QuotientGroup.mk' H₂), ?_, noout_comm_of_sq hsq, hsq, ?_⟩
  · rintro ⟨u, v⟩
    induction u using QuotientGroup.induction_on with | H a =>
    induction v using QuotientGroup.induction_on with | H b =>
    have hmem : a⁻¹ * b ∈ H₁ ⊔ H₂ := by
      rw [noout_sup_eq_top hne h₁ h₂]; exact Subgroup.mem_top _
    have hmem' : a⁻¹ * b ∈ ((H₁ : Set G) * (H₂ : Set G)) := by
      rw [← Subgroup.mul_normal]; exact hmem
    obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := hmem'
    refine ⟨a * x₁, Prod.ext ?_ ?_⟩
    · simp only [MonoidHom.prod_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa using hx₁
    · simp only [MonoidHom.prod_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have : (a * x₁)⁻¹ * b = x₂ := by
        rw [mul_inv_rev, mul_assoc, ← hx, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact hx₂
  · rw [Nat.card_prod, hc₁, hc₂]

theorem noout_card_le_eight {T B : Type} [Group T] [Finite T] [Group B] [Finite B]
    (hcomm : ∀ a b : B, a * b = b * a) (hsq : ∀ b : B, b * b = 1) (Φ : T →* B)
    (hΦ : Function.Surjective Φ)
    (hgen : ∃ a t y : T, Subgroup.closure ({a, t, y} : Set T) = ⊤) : Nat.card B ≤ 8 := by
  classical
  obtain ⟨a, t, y, hclosure⟩ := hgen
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative B := ⟨⟨hcomm⟩⟩
  have : CFSG.IsElementaryAbelian 2 B :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one (fun b => by rw [pow_two]; exact hsq b)⟩
  have hcard : Nat.card B = 2 ^ Group.rank B := by
    rw [CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := 2) B,
      CFSG.generatorRank_eq_group_rank]
  have hrankT : Group.rank T ≤ 3 := by
    have := Group.rank_le (S := ({a, t, y} : Finset T)) (by simpa using hclosure)
    exact this.trans Finset.card_le_three
  have hrankB : Group.rank B ≤ Group.rank T := Group.rank_le_of_surjective Φ hΦ
  rw [hcard]
  calc 2 ^ Group.rank B ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hrankB.trans hrankT)
    _ = 8 := by norm_num

theorem noout_exists_hom_central_product {T : Type} [Group T] {P C : Subgroup T}
    (hPC : ∀ p ∈ P, ∀ c ∈ C, p * c = c * p) (hT : ∀ x : T, ∃ p ∈ P, ∃ c ∈ C, x = p * c)
    {A₁ A₂ : Type} [Group A₁] [Group A₂] (φ₁ : ↥P →* A₁) (φ₂ : ↥C →* A₂)
    (hker : ∀ (p : ↥P) (c : ↥C), (p : T) * (c : T) = 1 → φ₁ p = 1 ∧ φ₂ c = 1)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂) :
    ∃ Φ : T →* A₁ × A₂, Function.Surjective Φ := by
  let μ : ↥P × ↥C →* T :=
    MonoidHom.noncommCoprod P.subtype C.subtype fun p c => hPC p p.2 c c.2
  have hμ : Function.Surjective μ := by
    intro x
    obtain ⟨p, hp, c, hc, rfl⟩ := hT x
    exact ⟨(⟨p, hp⟩, ⟨c, hc⟩), rfl⟩
  let Ψ : ↥P × ↥C →* A₁ × A₂ := MonoidHom.prodMap φ₁ φ₂
  have hker' : μ.ker ≤ Ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    obtain ⟨p, c⟩ := z
    have h : (p : T) * (c : T) = 1 := hz
    obtain ⟨h1, h2⟩ := hker p c h
    simp [Ψ, h1, h2]
  refine ⟨MonoidHom.liftOfSurjective μ hμ ⟨Ψ, hker'⟩, ?_⟩
  rintro ⟨a, b⟩
  obtain ⟨p, rfl⟩ := hφ₁ a
  obtain ⟨c, rfl⟩ := hφ₂ b
  exact ⟨μ (p, c), by simp [Ψ]⟩

theorem noout_mem_sup_of_commute {T : Type} [Group T] [Finite T] {A B : Subgroup T}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : T} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2
  have : x ∈ ((A ⊔ B : Subgroup T) : Set T) := hx
  rw [h] at this
  obtain ⟨a, ha, b, hb, hab⟩ := this
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem noout_not_isCyclic_of_noncomm {G : Type} [Group G] {x y : G} (h : x * y ≠ y * x) :
    ¬ IsCyclic G := by
  intro _
  exact h (IsMulCommutative.is_comm.comm x y)

theorem no_outside_centralizer {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (hgen : ∃ a t y : T, Subgroup.closure ({a, t, y} : Set T) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) {P₁ P₂ : Subgroup T}
    (h₁ : IVK.IsQuaternionTwoGroup ↥P₁ (n + 1)) (h₂ : IVK.IsQuaternionTwoGroup ↥P₂ (n + 1))
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2)
    (hidx : (P₁ ⊔ P₂).index = 2) {g : T} (hg : g ∉ P₁ ⊔ P₂)
    (hgc : ∀ p ∈ P₁, g * p = p * g) : False := by
  obtain ⟨-, ⟨e₁⟩⟩ := h₁
  obtain ⟨-, ⟨e₂⟩⟩ := h₂
  have hN : 2 ≤ 2 ^ (n + 1 - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1 - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN2 : 2 ∣ 2 ^ (n + 1 - 2) := dvd_pow_self 2 (by omega)
  obtain ⟨ζ, hζ1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(P₁ ⊓ P₂))).1 hinf
  have hζP₁ : (ζ : T) ∈ P₁ := (Subgroup.mem_inf.1 ζ.2).1
  have hζP₂ : (ζ : T) ∈ P₂ := (Subgroup.mem_inf.1 ζ.2).2
  have hζ1' : (ζ : T) ≠ 1 := fun h => hζ1 (Subtype.ext h)
  have hcen1 : ∀ x ∈ P₁, (∀ p ∈ P₁, p * x = x * p) → x = 1 ∨ x = ζ := by
    intro x hx hxc
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      have := noout_central_unique hN e₁ (x := ⟨x, hx⟩) (y := ⟨ζ, hζP₁⟩)
        (fun h => hx1 (congrArg Subtype.val h)) (fun h => hζ1' (congrArg Subtype.val h))
        (fun z => Subtype.ext (hxc z z.2)) (fun z => Subtype.ext (hc z z.2 ζ hζP₂))
      exact congrArg Subtype.val this
  obtain ⟨u, hu⟩ : ∃ u : ↥P₁, (⟨ζ, hζP₁⟩ : ↥P₁) = u * u :=
    noout_central_sq hN hN2 e₁ (fun z => Subtype.ext (hc z z.2 ζ hζP₂))
  obtain ⟨v, hv⟩ : ∃ v : ↥P₂, (⟨ζ, hζP₂⟩ : ↥P₂) = v * v :=
    noout_central_sq hN hN2 e₂ (fun z => Subtype.ext (hc ζ hζP₁ z z.2).symm)
  have hζu' : (ζ : T) = (u : T) * u := congrArg Subtype.val hu
  have hζv' : (ζ : T) = (v : T) * v := congrArg Subtype.val hv
  set C : Subgroup T := Subgroup.centralizer (P₁ : Set T) with hCdef
  have hPC : ∀ p ∈ P₁, ∀ c ∈ C, p * c = c * p := fun p hp c hcC =>
    (Subgroup.mem_centralizer_iff.1 hcC) p hp
  have hP₂C : P₂ ≤ C := fun q hq => Subgroup.mem_centralizer_iff.2 fun p hp => hc p hp q hq
  have hgC : g ∈ C := Subgroup.mem_centralizer_iff.2 fun p hp => (hgc p hp).symm
  have hdecomp : ∀ x : T, ∃ p ∈ P₁, ∃ c ∈ C, x = p * c := by
    intro x
    by_cases hx : x ∈ P₁ ⊔ P₂
    · obtain ⟨p, hp, q, hq, rfl⟩ := noout_mem_sup_of_commute hc hx
      exact ⟨p, hp, q, hP₂C hq, rfl⟩
    · have hxg : x * g⁻¹ ∈ P₁ ⊔ P₂ := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        constructor
        · intro h; exact absurd h hx
        · intro h; exact absurd (inv_mem_iff.1 h) hg
      obtain ⟨p, hp, q, hq, hpq⟩ := noout_mem_sup_of_commute hc hxg
      refine ⟨p, hp, q * g, C.mul_mem (hP₂C hq) hgC, ?_⟩
      calc x = x * g⁻¹ * g := by group
        _ = p * q * g := by rw [hpq]
        _ = p * (q * g) := by group
  obtain ⟨x₀, y₀, hxy₀⟩ := noout_not_comm hN e₂
  have hP₁nc : ¬ IsCyclic ↥P₁ := by
    obtain ⟨x, y, hxy⟩ := noout_not_comm hN e₁
    exact noout_not_isCyclic_of_noncomm hxy
  have hCnc : ¬ IsCyclic ↥C := by
    refine noout_not_isCyclic_of_noncomm (x := ⟨x₀, hP₂C x₀.2⟩) (y := ⟨y₀, hP₂C y₀.2⟩) ?_
    intro h
    exact hxy₀ (Subtype.ext (by simpa using congrArg (fun z : ↥C => (z : T)) h))
  obtain ⟨A₁, _, φ₁, hφ₁, -, hsq₁, hcard₁⟩ :=
    noout_exists_hom_of_not_cyclic (hT.to_subgroup P₁) hP₁nc
  obtain ⟨A₂, _, φ₂, hφ₂, -, hsq₂, hcard₂⟩ :=
    noout_exists_hom_of_not_cyclic (hT.to_subgroup C) hCnc
  have hker : ∀ (p : ↥P₁) (c : ↥C), (p : T) * (c : T) = 1 → φ₁ p = 1 ∧ φ₂ c = 1 := by
    intro p c hpc
    have hcp : (p : T) = (c : T)⁻¹ := eq_inv_of_mul_eq_one_left hpc
    have hpcent : ∀ z ∈ P₁, z * (p : T) = (p : T) * z := by
      intro z hz
      rw [hcp]
      exact (Commute.inv_right (show Commute z (c : T) from hPC z hz c c.2)).eq
    rcases hcen1 p p.2 hpcent with h1 | h1
    · have hp1 : p = 1 := Subtype.ext h1
      have hc1 : c = 1 := Subtype.ext (by rw [hcp] at h1; simpa using h1)
      rw [hp1, hc1]
      exact ⟨map_one φ₁, map_one φ₂⟩
    · have hpu : p = u * u := Subtype.ext (h1.trans hζu')
      have hcv : c⁻¹ = (⟨v, hP₂C v.2⟩ : ↥C) * ⟨v, hP₂C v.2⟩ :=
        Subtype.ext (by
          show ((c : T))⁻¹ = (v : T) * v
          rw [← hcp, h1]; exact hζv')
      refine ⟨?_, ?_⟩
      · rw [hpu, map_mul]; exact hsq₁ _
      · have : φ₂ c⁻¹ = 1 := by rw [hcv, map_mul]; exact hsq₂ _
        rw [map_inv, inv_eq_one] at this
        exact this
  obtain ⟨Φ, hΦ⟩ := noout_exists_hom_central_product hPC hdecomp φ₁ φ₂ hker hφ₁ hφ₂
  have : Finite (A₁ × A₂) := Finite.of_surjective Φ hΦ
  have hsq : ∀ b : A₁ × A₂, b * b = 1 := fun b => Prod.ext (hsq₁ b.1) (hsq₂ b.2)
  have h8 := noout_card_le_eight (noout_comm_of_sq hsq) hsq Φ hΦ hgen
  rw [Nat.card_prod, hcard₁, hcard₂] at h8
  omega

end CFSG.GH74.GLS.Stage1.Main
