module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims135
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma135b
public import CFSG.HardMathSupport.Timmesfeld.Proving.MapGLAPPrimeCore
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims135b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma135b

section Generic

variable {X : Type} [Group X]

theorem mem_sup_of_le_normalizer {H K : Subgroup X} (hK : K ≤ Subgroup.normalizer (H : Set X))
    {x : X} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let P : Subgroup X :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * (b * a' * b⁻¹), H.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hK hb) a').1 ha'),
          b * b', K.mul_mem hb hb', by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (hK (K.inv_mem hb)) a⁻¹).1
          (H.inv_mem ha), b⁻¹, K.inv_mem hb, by group⟩ }
  have hle : H ⊔ K ≤ P := sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, by group⟩)
    (fun b hb => ⟨1, H.one_mem, b, hb, by group⟩)
  exact hle hx

theorem mem_normalizer_of_map_conj_eq {K : Subgroup X} {g : X}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set X) := by
  by_contra hg
  exact map_conj_ne_of_not_mem_normalizer K hg h

theorem map_conj_injective (g : X) :
    Function.Injective (fun K : Subgroup X => K.map (MulAut.conj g).toMonoidHom) :=
  Subgroup.map_injective (MulEquiv.injective _)

theorem mem_of_mul_self_mem {H : Subgroup X} {y : X} {n : ℕ} (hn : y ^ (3 ^ n) = 1)
    (h : y * y ∈ H) : y ∈ H := by
  obtain ⟨k, hk⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  have e : y = (y * y) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    calc y = y ^ (3 ^ n) * y := by rw [hn, one_mul]
      _ = y ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
  rw [e]
  exact H.pow_mem h _

theorem mem_centralizer_sup3 {K₁ K₂ K₃ : Subgroup X} {z : X}
    (h₁ : ∀ k ∈ K₁, k * z = z * k) (h₂ : ∀ k ∈ K₂, k * z = z * k)
    (h₃ : ∀ k ∈ K₃, k * z = z * k) :
    z ∈ Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) := by
  have hle : K₁ ⊔ K₂ ⊔ K₃ ≤ Subgroup.centralizer ({z} : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro k hk <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact h₁ k hk
    · exact h₂ k hk
    · exact h₃ k hk
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have := hle hk
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end Generic

section Quot

variable {X : Type} [Group X] [Finite X]

theorem ne_bot_of_isComponentOf {J : Subgroup X} (hJ : IsComponentOf J ⊤) : J ≠ ⊥ := by
  intro h
  haveI := hJ.2.2.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥J ⧸ Subgroup.center ↥J)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h1 := (Subgroup.eq_bot_iff_forall J).1 h
  rw [show a' = b' from Subtype.ext ((h1 _ a'.2).trans (h1 _ b'.2).symm)]

theorem comm_of_comp {K K' : Subgroup X} (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤)
    (hne : K ≠ K') : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
  CFSG.ClassicalInvolution.Balance.LocalBalance.commute_of_isComponent_of_ne
    ((CFSG.isComponent_iff_open K).2 hK) ((CFSG.isComponent_iff_open K').2 hK') hne

theorem comp_eq_of_cent {K₁ K₂ K₃ J : Subgroup X}
    (hC : Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) = ⊥)
    (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (h₃ : IsComponentOf K₃ ⊤)
    (hJ : IsComponentOf J ⊤) : J = K₁ ∨ J = K₂ ∨ J = K₃ := by
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  have hle : J ≤ Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) := by
    intro a ha
    refine mem_centralizer_sup3 (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    · exact (comm_of_comp hJ h₁ n1 a ha k hk).symm
    · exact (comm_of_comp hJ h₂ n2 a ha k hk).symm
    · exact (comm_of_comp hJ h₃ n3 a ha k hk).symm
  rw [hC] at hle
  exact ne_bot_of_isComponentOf hJ (le_bot_iff.1 hle)

theorem card_le_of_three {K₁ K₂ K₃ H : Subgroup X}
    (e₁ : ↥K₁ ≃* alternatingGroup (Fin 7)) (e₂ : ↥K₂ ≃* alternatingGroup (Fin 7))
    (e₃ : ↥K₃ ≃* alternatingGroup (Fin 7)) (hH : IsPGroup 3 ↥H)
    (h₁ : H ≤ Subgroup.normalizer (K₁ : Set X)) (h₂ : H ≤ Subgroup.normalizer (K₂ : Set X))
    (h₃ : H ≤ Subgroup.normalizer (K₃ : Set X))
    (hC : Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) = ⊥) :
    Nat.card H ≤ 9 * 9 * 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π₁, hπ₁⟩ := exists_inner_hom e₁ hH h₁
  obtain ⟨π₂, hπ₂⟩ := exists_inner_hom e₂ hH h₂
  obtain ⟨π₃, hπ₃⟩ := exists_inner_hom e₃ hH h₃
  have key : ∀ {K : Subgroup X} (π : ↥H →* ↥K), (∀ (h : ↥H) (k : ↥K),
      (h : X) * (k : X) * (h : X)⁻¹ = ((π h : ↥K) : X) * (k : X) * ((π h : ↥K) : X)⁻¹) →
      ∀ a b : ↥H, π a = π b → ∀ k ∈ K, k * ((a : X)⁻¹ * b) = ((a : X)⁻¹ * b) * k := by
    intro K π hπ a b hab k hk
    have h1 := hπ (a⁻¹ * b) ⟨k, hk⟩
    rw [map_mul, map_inv, hab, inv_mul_cancel] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, one_mul, inv_one,
      mul_one] at h1
    calc k * ((a : X)⁻¹ * b) = ((a : X)⁻¹ * b * k * ((a : X)⁻¹ * b)⁻¹) * ((a : X)⁻¹ * b) := by
          rw [h1]
      _ = ((a : X)⁻¹ * b) * k := by group
  let f : ↥H → ↥π₁.range × ↥π₂.range × ↥π₃.range := fun h =>
    (⟨π₁ h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩, ⟨π₂ h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩,
      ⟨π₃ h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨e1, e2, e3⟩ := hab
    have hc : (a : X)⁻¹ * b ∈ Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) :=
      mem_centralizer_sup3 (key π₁ hπ₁ a b e1) (key π₂ hπ₂ a b e2) (key π₃ hπ₃ a b e3)
    rw [hC, Subgroup.mem_bot] at hc
    exact Subtype.ext (inv_mul_eq_one.1 hc)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod] at hcard
  have hr : ∀ {K : Subgroup X} (e : ↥K ≃* alternatingGroup (Fin 7)) (π : ↥H →* ↥K),
      Nat.card π.range ≤ 9 := fun e π =>
    card_three_le_nine e (hH.of_surjective π.rangeRestrict π.rangeRestrict_surjective)
  calc Nat.card H ≤ Nat.card π₁.range * (Nat.card π₂.range * Nat.card π₃.range) := hcard
    _ ≤ 9 * (9 * 9) := Nat.mul_le_mul (hr e₁ π₁) (Nat.mul_le_mul (hr e₂ π₂) (hr e₃ π₃))
    _ = 9 * 9 * 9 := by norm_num

theorem card_three_inf {K₁ K₂ K₃ B : Subgroup X}
    (e₁ : ↥K₁ ≃* alternatingGroup (Fin 7)) (e₂ : ↥K₂ ≃* alternatingGroup (Fin 7))
    (e₃ : ↥K₃ ≃* alternatingGroup (Fin 7))
    (c₁ : IsComponentOf K₁ ⊤) (c₂ : IsComponentOf K₂ ⊤) (c₃ : IsComponentOf K₃ ⊤)
    (n12 : K₁ ≠ K₂) (n13 : K₁ ≠ K₃) (n23 : K₂ ≠ K₃)
    (h₁ : Nat.card ↥(B ⊓ K₁) = 9) (h₂ : Nat.card ↥(B ⊓ K₂) = 9) (h₃ : Nat.card ↥(B ⊓ K₃) = 9) :
    Nat.card ↥(B ⊓ K₁ ⊔ B ⊓ K₂ ⊔ B ⊓ K₃) = 9 * 9 * 9 := by
  have hc12 : ∀ a ∈ B ⊓ K₁, ∀ b ∈ B ⊓ K₂, a * b = b * a := fun a ha b hb =>
    comm_of_comp c₁ c₂ n12 a ha.2 b hb.2
  have hi12 : B ⊓ K₁ ⊓ (B ⊓ K₂) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨⟨-, hx1⟩, -, hx2⟩
    exact central_eq_one e₁ hx1 fun k hk => (comm_of_comp c₂ c₁ n12.symm x hx2 k hk).symm
  have hC3 : B ⊓ K₁ ⊔ B ⊓ K₂ ≤ Subgroup.centralizer (K₃ : Set X) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro k hk
    · exact (comm_of_comp c₁ c₃ n13 a ha.2 k hk).symm
    · exact (comm_of_comp c₂ c₃ n23 a ha.2 k hk).symm
  have hc3 : ∀ a ∈ B ⊓ K₁ ⊔ B ⊓ K₂, ∀ b ∈ B ⊓ K₃, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hC3 ha) b hb.2).symm
  have hi3 : (B ⊓ K₁ ⊔ B ⊓ K₂) ⊓ (B ⊓ K₃) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hx, -, hx3⟩
    exact central_eq_one e₃ hx3 fun k hk => Subgroup.mem_centralizer_iff.1 (hC3 hx) k hk
  rw [card_sup_of_commute hc3 hi3, card_sup_of_commute hc12 hi12, h₁, h₂, h₃]

theorem mem_normalizer_of_three {K₁ K₂ K₃ : Subgroup X}
    (c₂ : IsComponentOf K₂ ⊤) (c₃ : IsComponentOf K₃ ⊤)
    (n12 : K₁ ≠ K₂) (n13 : K₁ ≠ K₃) (n23 : K₂ ≠ K₃)
    (hall : ∀ J : Subgroup X, IsComponentOf J ⊤ → J = K₁ ∨ J = K₂ ∨ J = K₃)
    {y : X} {n : ℕ} (hy : y ^ (3 ^ n) = 1) (hy1 : y ∈ Subgroup.normalizer (K₁ : Set X)) :
    y ∈ Subgroup.normalizer (K₂ : Set X) ∧ y ∈ Subgroup.normalizer (K₃ : Set X) := by
  have e1 : K₁.map (MulAut.conj y).toMonoidHom = K₁ := map_conj_eq_self_of_mem_normalizer hy1
  have hinj := map_conj_injective y
  have h2 : K₂.map (MulAut.conj y).toMonoidHom = K₂ ∨ K₂.map (MulAut.conj y).toMonoidHom = K₃ := by
    rcases hall _ (isComponentOf_conj' c₂ y) with h | h | h
    · exact absurd (hinj (h.trans e1.symm)) n12.symm
    · exact Or.inl h
    · exact Or.inr h
  have h3 : K₃.map (MulAut.conj y).toMonoidHom = K₂ ∨ K₃.map (MulAut.conj y).toMonoidHom = K₃ := by
    rcases hall _ (isComponentOf_conj' c₃ y) with h | h | h
    · exact absurd (hinj (h.trans e1.symm)) n13.symm
    · exact Or.inl h
    · exact Or.inr h
  have hK2 : y ∈ Subgroup.normalizer (K₂ : Set X) := by
    rcases h2 with h2 | h2
    · exact mem_normalizer_of_map_conj_eq h2
    · rcases h3 with h3 | h3
      · apply mem_of_mul_self_mem hy
        apply mem_normalizer_of_map_conj_eq
        rw [← map_map_conj, h2, h3]
      · exact absurd (hinj (h2.trans h3.symm)) n23
  refine ⟨hK2, ?_⟩
  have e2 : K₂.map (MulAut.conj y).toMonoidHom = K₂ := map_conj_eq_self_of_mem_normalizer hK2
  rcases h3 with h3 | h3
  · exact absurd (hinj (h3.trans e2.symm)) n23.symm
  · exact mem_normalizer_of_map_conj_eq h3

theorem zpow_cases {δ : X} (hδ : δ ^ 3 = 1) (k : ℤ) :
    δ ^ k = 1 ∨ δ ^ k = δ ∨ δ ^ k = δ * δ := by
  have hδ' : δ ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hδ
  rw [zpow_eq_zpow_emod k hδ']
  have h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h with h | h | h <;> rw [h]
  · left; exact zpow_zero δ
  · right; left; exact zpow_one δ
  · right; right; rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two]

theorem comm_map_conj {K : Subgroup X} {z g : X} (hK : ∀ k ∈ K, k * z = z * k)
    (hg : g * z = z * g) : ∀ k ∈ K.map (MulAut.conj g).toMonoidHom, k * z = z * k := by
  intro k hk
  rw [mem_conj_map_iff] at hk
  have h1 := hK _ hk
  have hgi : g⁻¹ * z = z * g⁻¹ := by
    calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hg]
      _ = z * g⁻¹ := by group
  calc k * z = g * (g⁻¹ * k * g) * g⁻¹ * z := by group
    _ = g * (g⁻¹ * k * g) * (z * g⁻¹) := by rw [mul_assoc _ g⁻¹ z, hgi]
    _ = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = (g * z) * (g⁻¹ * k * g) * g⁻¹ := by group
    _ = (z * g) * (g⁻¹ * k * g) * g⁻¹ := by rw [hg]
    _ = z * k := by group

theorem inv_mul_mem_normalizer {K : Subgroup X} {r g : X}
    (h : K.map (MulAut.conj r).toMonoidHom = K.map (MulAut.conj g).toMonoidHom) :
    g⁻¹ * r ∈ Subgroup.normalizer (K : Set X) := by
  apply mem_normalizer_of_map_conj_eq
  rw [← map_map_conj, h, map_map_conj, inv_mul_cancel]
  exact map_conj_eq_self_of_mem_normalizer (Subgroup.one_mem _)

theorem orbit_three {K D : Subgroup X} (hD : IsElemAbelian 3 D) (hDc : Nat.card ↥D = 9)
    {δ₀ δ : X} (hδ₀D : δ₀ ∈ D) (hδ₀1 : δ₀ ≠ 1) (hδ₀K : δ₀ ∈ Subgroup.normalizer (K : Set X))
    (hδD : δ ∈ D) (hδK : δ ∉ Subgroup.normalizer (K : Set X)) {ε : X} (hε : ε ∈ D) :
    K.map (MulAut.conj ε).toMonoidHom = K ∨
      K.map (MulAut.conj ε).toMonoidHom = K.map (MulAut.conj δ).toMonoidHom ∨
        K.map (MulAut.conj ε).toMonoidHom = K.map (MulAut.conj (δ * δ)).toMonoidHom := by
  have hcomm := comm_of_isElemAbelian hD
  have hδ1 : δ ≠ 1 := fun h => hδK (h ▸ Subgroup.one_mem _)
  have o₀ : orderOf δ₀ = 3 := orderOf_eq_prime (hD.2 δ₀ hδ₀D) hδ₀1
  have o : orderOf δ = 3 := orderOf_eq_prime (hD.2 δ hδD) hδ1
  have hZ : Subgroup.zpowers δ₀ ≤ Subgroup.normalizer (K : Set X) := Subgroup.zpowers_le.2 hδ₀K
  have hZD : Subgroup.zpowers δ ≤ D := Subgroup.zpowers_le.2 hδD
  have hZ₀D : Subgroup.zpowers δ₀ ≤ D := Subgroup.zpowers_le.2 hδ₀D
  have hi : Subgroup.zpowers δ₀ ⊓ Subgroup.zpowers δ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro y ⟨hy0, hy⟩
    by_contra hy1
    apply hδK
    have hyy : Subgroup.zpowers y = Subgroup.zpowers δ := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hy)
      rw [Nat.card_zpowers, Nat.card_zpowers, o, orderOf_eq_prime (hD.2 y (hZD hy)) hy1]
    have : δ ∈ Subgroup.zpowers y := hyy ▸ Subgroup.mem_zpowers δ
    exact hZ ((Subgroup.zpowers_le.2 hy0) this)
  have hc : ∀ a ∈ Subgroup.zpowers δ₀, ∀ b ∈ Subgroup.zpowers δ, a * b = b * a :=
    fun a ha b hb => hcomm a (hZ₀D ha) b (hZD hb)
  have hsup : Subgroup.zpowers δ₀ ⊔ Subgroup.zpowers δ = D := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hZ₀D hZD) ?_
    rw [card_sup_of_commute hc hi, Nat.card_zpowers, Nat.card_zpowers, o₀, o, hDc]
  have hcen : Subgroup.zpowers δ ≤
      Subgroup.centralizer ((Subgroup.zpowers δ₀ : Subgroup X) : Set X) :=
    fun b hb => Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb
  have hnorm : Subgroup.zpowers δ ≤ Subgroup.normalizer ((Subgroup.zpowers δ₀ : Subgroup X) : Set X) :=
    hcen.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_le_normalizer hnorm (hsup ▸ hε)
  have e1 : K.map (MulAut.conj (a * b)).toMonoidHom = K.map (MulAut.conj b).toMonoidHom := by
    rw [hc a ha b hb, ← map_map_conj, map_conj_eq_self_of_mem_normalizer (hZ ha)]
  rw [e1]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rcases zpow_cases (hD.2 δ hδD) k with h | h | h <;> rw [h]
  · left; exact map_conj_eq_self_of_mem_normalizer (Subgroup.one_mem _)
  · right; left; rfl
  · right; right; rfl

theorem false_of_one_comp {K B D : Subgroup X} {m : ℕ} (e : ↥K ≃* alternatingGroup (Fin 7))
    (hBp : IsPGroup 3 ↥B) (hBc : Nat.card ↥B = 3 ^ m) (hm : 4 ≤ m)
    (hBn : B ≤ Subgroup.normalizer (K : Set X))
    (hcent : Subgroup.centralizer
      (((⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom : Subgroup X)) : Set X) = ⊥)
    (hDK : D ≤ Subgroup.normalizer (K : Set X)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : (⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom) = K := by
    apply le_antisymm
    · exact iSup₂_le fun ε hε => (map_conj_eq_self_of_mem_normalizer (hDK hε)).le
    · exact le_iSup₂_of_le (f := fun ε (_ : ε ∈ D) => K.map (MulAut.conj ε).toMonoidHom) 1
        D.one_mem (map_conj_eq_self_of_mem_normalizer (Subgroup.one_mem _)).ge
  rw [hL] at hcent
  obtain ⟨π, hπ⟩ := exists_inner_hom e hBp hBn
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hc : (b : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hπ b ⟨k, hk⟩
      rw [hb] at h1
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
      calc k * (b : X) = ((b : X) * k * (b : X)⁻¹) * b := by rw [h1]
        _ = (b : X) * k := by group
    rw [hcent, Subgroup.mem_bot] at hc
    exact Subtype.ext hc
  have h1 : Nat.card ↥B ≤ 9 := by
    calc Nat.card ↥B = Nat.card π.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      _ ≤ 9 := card_three_le_nine e (hBp.of_surjective π.rangeRestrict π.rangeRestrict_surjective)
  rw [hBc] at h1
  have : 3 ^ 4 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem core_eq_bot_of_nine {K D : Subgroup X} (hO : GLAPPrimeCore 3 X = ⊥)
    (hK : IsComponentOf K ⊤) (hD : IsElemAbelian 3 D)
    (hcent : Subgroup.centralizer
      (((⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom : Subgroup X)) : Set X) = ⊥)
    (h9 : ∀ ε ∈ D, ε ≠ 1 → ε ∉ Subgroup.normalizer (K : Set X)) {δ : X} (hδ : δ ∈ D)
    (hδ1 : δ ≠ 1) : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({δ} : Set X)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hcomm := comm_of_isElemAbelian hD
  have hkey : ∀ ε ∈ D, ∀ x ∈ K.map (MulAut.conj ε).toMonoidHom, z * x = x * z := by
    intro ε hε
    have hJ' : CFSG.IsComponent (K.map (MulAut.conj ε).toMonoidHom) :=
      (CFSG.isComponent_iff_open _).2 (isComponentOf_conj' hK ε)
    refine CFSG.HardMathSupport.Timmesfeld.Balance.commute_of_moved_p Nat.prime_three hJ'
      (CFSG.HardMathSupport.Timmesfeld.Balance.p_dvd_card_center_quot Nat.prime_three hO hJ')
      (hD.2 δ hδ) ?_ hz
    show (K.map (MulAut.conj ε).toMonoidHom).map (MulAut.conj δ).toMonoidHom ≠
      K.map (MulAut.conj ε).toMonoidHom
    intro h
    rw [map_map_conj, hcomm δ hδ ε hε, ← map_map_conj] at h
    exact h9 δ hδ hδ1 (mem_normalizer_of_map_conj_eq (map_conj_injective ε h))
  have hzc : z ∈ Subgroup.centralizer
      (((⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom : Subgroup X)) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    have hle : (⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom) ≤
        Subgroup.centralizer ({z} : Set X) :=
      iSup₂_le fun ε hε x hx => Subgroup.mem_centralizer_singleton_iff.2 (hkey ε hε x hx).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  rw [hcent, Subgroup.mem_bot] at hzc
  exact hzc

theorem card_ge_of_not_mem {B S : Subgroup X} (hS : IsPGroup 3 ↥S) (hBS : B ≤ S) {k : ℕ}
    (hB : Nat.card ↥B = 3 ^ k) {x : X} (hxS : x ∈ S) (hxB : x ∉ B) :
    3 ^ (k + 1) ≤ Nat.card ↥S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS
  have hdvd : 3 ^ k ∣ 3 ^ n := hB ▸ hn ▸ Subgroup.card_dvd_of_le hBS
  have hkn : k ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hne : k ≠ n := by
    rintro rfl
    have : B = S := Subgroup.eq_of_le_of_card_ge hBS (by rw [hB, hn])
    exact hxB (this ▸ hxS)
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_le_three_mul {R N : Subgroup X} {δ : X} (hδ : δ ∈ R)
    (h : ∀ r ∈ R, ∃ j : ℕ, j < 3 ∧ (δ ^ j)⁻¹ * r ∈ N) : Nat.card ↥R ≤ 3 * Nat.card ↥(R ⊓ N) := by
  classical
  choose! j hj using h
  let f : ↥R → Fin 3 × ↥(R ⊓ N) := fun r =>
    (⟨j r, (hj r r.2).1⟩, ⟨(δ ^ j r)⁻¹ * r, Subgroup.mem_inf.2
      ⟨R.mul_mem (R.inv_mem (R.pow_mem hδ _)) r.2, (hj r r.2).2⟩⟩)
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨h1, h2⟩ := Prod.mk.inj hab
    have h1' : j a = j b := congrArg Fin.val h1
    have h2' : (δ ^ j a)⁻¹ * (a : X) = (δ ^ j b)⁻¹ * (b : X) := congrArg Subtype.val h2
    rw [h1'] at h2'
    exact Subtype.ext (mul_left_cancel h2')
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this

theorem conj_mem_normalizer3 {K₁ K₂ K₃ : Subgroup X}
    (c₁ : IsComponentOf K₁ ⊤) (c₂ : IsComponentOf K₂ ⊤) (c₃ : IsComponentOf K₃ ⊤)
    (hall : ∀ J : Subgroup X, IsComponentOf J ⊤ → J = K₁ ∨ J = K₂ ∨ J = K₃) {n : X}
    (hn : n ∈ Subgroup.normalizer (K₁ : Set X) ⊓ Subgroup.normalizer (K₂ : Set X) ⊓
      Subgroup.normalizer (K₃ : Set X)) (g : X) :
    g * n * g⁻¹ ∈ Subgroup.normalizer (K₁ : Set X) ⊓ Subgroup.normalizer (K₂ : Set X) ⊓
      Subgroup.normalizer (K₃ : Set X) := by
  have key : ∀ {J : Subgroup X}, IsComponentOf J ⊤ →
      g * n * g⁻¹ ∈ Subgroup.normalizer (J : Set X) := by
    intro J hJ
    apply mem_normalizer_of_map_conj_eq
    have hnJ : n ∈ Subgroup.normalizer
        ((J.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) : Set X) := by
      rcases hall _ (isComponentOf_conj' hJ g⁻¹) with h | h | h <;> rw [h]
      · exact hn.1.1
      · exact hn.1.2
      · exact hn.2
    rw [show g * n * g⁻¹ = g * (n * g⁻¹) by group, ← map_map_conj, ← map_map_conj,
      map_conj_eq_self_of_mem_normalizer hnJ, map_map_conj, mul_inv_cancel]
    exact map_conj_eq_self_of_mem_normalizer (Subgroup.one_mem _)
  exact ⟨⟨key c₁, key c₂⟩, key c₃⟩

theorem three_main {K₁ K₂ K₃ B R : Subgroup X} {δ : X}
    (e₁ : ↥K₁ ≃* alternatingGroup (Fin 7)) (e₂ : ↥K₂ ≃* alternatingGroup (Fin 7))
    (e₃ : ↥K₃ ≃* alternatingGroup (Fin 7))
    (c₁ : IsComponentOf K₁ ⊤) (c₂ : IsComponentOf K₂ ⊤) (c₃ : IsComponentOf K₃ ⊤)
    (n12 : K₁ ≠ K₂) (n13 : K₁ ≠ K₃) (n23 : K₂ ≠ K₃)
    (hC : Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) = ⊥)
    (b₁ : B ≤ Subgroup.normalizer (K₁ : Set X)) (b₂ : B ≤ Subgroup.normalizer (K₂ : Set X))
    (b₃ : B ≤ Subgroup.normalizer (K₃ : Set X))
    (h₁ : Nat.card ↥(B ⊓ K₁) = 9) (h₂ : Nat.card ↥(B ⊓ K₂) = 9) (h₃ : Nat.card ↥(B ⊓ K₃) = 9)
    (hR : IsPGroup 3 ↥R) (hBR : B ≤ R) (hδR : δ ∈ R)
    (hK₂ : K₂ = K₁.map (MulAut.conj δ).toMonoidHom)
    (hK₃ : K₃ = K₁.map (MulAut.conj (δ * δ)).toMonoidHom) :
    Nat.card ↥B = 3 ^ 6 ∧
      B = R ⊓ (Subgroup.normalizer (K₁ : Set X) ⊓ Subgroup.normalizer (K₂ : Set X) ⊓
        Subgroup.normalizer (K₃ : Set X)) ∧ Nat.card ↥R ≤ 3 ^ 7 := by
  have hall : ∀ J : Subgroup X, IsComponentOf J ⊤ → J = K₁ ∨ J = K₂ ∨ J = K₃ :=
    fun J hJ => comp_eq_of_cent hC c₁ c₂ c₃ hJ
  set N₃ := Subgroup.normalizer (K₁ : Set X) ⊓ Subgroup.normalizer (K₂ : Set X) ⊓
    Subgroup.normalizer (K₃ : Set X) with hN₃
  have hR₀ : Nat.card ↥(R ⊓ N₃) ≤ 9 * 9 * 9 :=
    card_le_of_three e₁ e₂ e₃ (hR.to_le inf_le_left) (fun x hx => hx.2.1.1)
      (fun x hx => hx.2.1.2) (fun x hx => hx.2.2) hC
  have hBR₀ : B ≤ R ⊓ N₃ := le_inf hBR (le_inf (le_inf b₁ b₂) b₃)
  have hS := card_three_inf e₁ e₂ e₃ c₁ c₂ c₃ n12 n13 n23 h₁ h₂ h₃
  have hSB : B ⊓ K₁ ⊔ B ⊓ K₂ ⊔ B ⊓ K₃ ≤ B := sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hBge : 9 * 9 * 9 ≤ Nat.card ↥B := hS ▸ Subgroup.card_le_of_le hSB
  have hBle : Nat.card ↥B ≤ 9 * 9 * 9 := (Subgroup.card_le_of_le hBR₀).trans hR₀
  have hBeq : B = R ⊓ N₃ := Subgroup.eq_of_le_of_card_ge hBR₀ (hR₀.trans hBge)
  refine ⟨by rw [le_antisymm hBle hBge]; norm_num, hBeq, ?_⟩
  have hRN : R ⊓ Subgroup.normalizer (K₁ : Set X) ≤ R ⊓ N₃ := by
    rintro y ⟨hyR, hy1⟩
    obtain ⟨n, hn⟩ := hR ⟨y, hyR⟩
    have hyn : y ^ (3 ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨h2, h3⟩ := mem_normalizer_of_three c₂ c₃ n12 n13 n23 hall hyn hy1
    exact ⟨hyR, ⟨hy1, h2⟩, h3⟩
  have hdec : ∀ r ∈ R, ∃ j : ℕ, j < 3 ∧ (δ ^ j)⁻¹ * r ∈ Subgroup.normalizer (K₁ : Set X) := by
    intro r _
    rcases hall _ (isComponentOf_conj' c₁ r) with h | h | h
    · refine ⟨0, by norm_num, ?_⟩
      rw [pow_zero, inv_one, one_mul]
      exact mem_normalizer_of_map_conj_eq h
    · refine ⟨1, by norm_num, ?_⟩
      rw [pow_one]
      exact inv_mul_mem_normalizer (h.trans hK₂)
    · refine ⟨2, by norm_num, ?_⟩
      rw [pow_two]
      exact inv_mul_mem_normalizer (h.trans hK₃)
  calc Nat.card ↥R ≤ 3 * Nat.card ↥(R ⊓ Subgroup.normalizer (K₁ : Set X)) :=
        card_le_three_mul hδR hdec
    _ ≤ 3 * (9 * 9 * 9) := Nat.mul_le_mul_left 3 ((Subgroup.card_le_of_le hRN).trans hR₀)
    _ = 3 ^ 7 := by norm_num

theorem norm_mem {B : Subgroup X} (hB : IsElemAbelian 3 B) {δ b : X}
    (hδB : δ ∈ Subgroup.normalizer (B : Set X)) (hδ3 : δ ^ 3 ∈ B) (hb : b ∈ B) :
    b * (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹) ∈ B ⊓ Subgroup.centralizer ({δ} : Set X) := by
  have hcB := comm_of_isElemAbelian hB
  have hu : δ * b * δ⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hδB b).1 hb
  have hv : δ * δ * b * δ⁻¹ * δ⁻¹ ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 hδB _).1 hu
    simpa [mul_assoc] using this
  refine Subgroup.mem_inf.2 ⟨B.mul_mem (B.mul_mem hb hu) hv, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hd : δ * δ * δ ∈ B := by rw [show δ * δ * δ = δ ^ 3 by rw [pow_three, mul_assoc]]; exact hδ3
  have hw : δ * δ * δ * b * δ⁻¹ * δ⁻¹ * δ⁻¹ = b := by
    calc δ * δ * δ * b * δ⁻¹ * δ⁻¹ * δ⁻¹ = (δ * δ * δ) * b * (δ * δ * δ)⁻¹ := by group
      _ = b * (δ * δ * δ) * (δ * δ * δ)⁻¹ := by rw [hcB _ hd b hb]
      _ = b := by group
  have hbuv : b * (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹) =
      (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹) * b := by
    rw [hcB b hb _ hu, mul_assoc (δ * b * δ⁻¹) b, hcB b hb _ hv, ← mul_assoc]
  calc b * (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹) * δ =
      (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹) * b * δ := by rw [hbuv]
    _ = (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹) * (δ * δ * δ * b * δ⁻¹ * δ⁻¹ * δ⁻¹) * δ := by
        rw [hw]
    _ = δ * (b * (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹)) := by group

theorem card_cent_delta {K₁ K₂ K₃ B : Subgroup X} {δ : X}
    (e₁ : ↥K₁ ≃* alternatingGroup (Fin 7)) (e₂ : ↥K₂ ≃* alternatingGroup (Fin 7))
    (e₃ : ↥K₃ ≃* alternatingGroup (Fin 7))
    (c₁ : IsComponentOf K₁ ⊤) (c₂ : IsComponentOf K₂ ⊤) (c₃ : IsComponentOf K₃ ⊤)
    (n12 : K₁ ≠ K₂) (n13 : K₁ ≠ K₃) (n23 : K₂ ≠ K₃)
    (hC : Subgroup.centralizer ((K₁ ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) = ⊥)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card ↥B = 3 ^ 6)
    (h₁ : Nat.card ↥(B ⊓ K₁) = 9) (h₂ : Nat.card ↥(B ⊓ K₂) = 9) (h₃ : Nat.card ↥(B ⊓ K₃) = 9)
    (hδB : δ ∈ Subgroup.normalizer (B : Set X)) (hδ3 : δ ^ 3 = 1)
    (hK₂ : K₂ = K₁.map (MulAut.conj δ).toMonoidHom)
    (hK₃ : K₃ = K₁.map (MulAut.conj (δ * δ)).toMonoidHom) :
    Nat.card ↥(B ⊓ Subgroup.centralizer ({δ} : Set X)) = 9 := by
  have hcB := comm_of_isElemAbelian hB
  apply le_antisymm
  · set S := B ⊓ K₂ ⊔ B ⊓ K₃ with hSdef
    have hSB : S ≤ B := sup_le inf_le_left inf_le_left
    have hc23 : ∀ a ∈ B ⊓ K₂, ∀ b ∈ B ⊓ K₃, a * b = b * a := fun a ha b hb =>
      comm_of_comp c₂ c₃ n23 a ha.2 b hb.2
    have hi23 : B ⊓ K₂ ⊓ (B ⊓ K₃) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨⟨-, hx2⟩, -, hx3⟩
      exact central_eq_one e₂ hx2 fun k hk => (comm_of_comp c₃ c₂ n23.symm x hx3 k hk).symm
    have hS : Nat.card ↥S = 9 * 9 := by rw [card_sup_of_commute hc23 hi23, h₂, h₃]
    have hSK : S ≤ Subgroup.centralizer (K₁ : Set X) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
        intro k hk
      · exact comm_of_comp c₁ c₂ n12 k hk a ha.2
      · exact comm_of_comp c₁ c₃ n13 k hk a ha.2
    have hi : (B ⊓ Subgroup.centralizer ({δ} : Set X)) ⊓ S = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro z ⟨⟨-, hzδ⟩, hzS⟩
      have hzK : ∀ k ∈ K₁, k * z = z * k := fun k hk =>
        Subgroup.mem_centralizer_iff.1 (hSK hzS) k hk
      have hzd : δ * z = z * δ := (Subgroup.mem_centralizer_singleton_iff.1 hzδ).symm
      have hzdd : δ * δ * z = z * (δ * δ) := by
        rw [mul_assoc, hzd, ← mul_assoc, hzd, mul_assoc]
      have h2 := comm_map_conj hzK hzd
      have h3 := comm_map_conj hzK hzdd
      rw [← hK₂] at h2
      rw [← hK₃] at h3
      have := mem_centralizer_sup3 hzK h2 h3
      rw [hC, Subgroup.mem_bot] at this
      exact this
    have hc : ∀ a ∈ B ⊓ Subgroup.centralizer ({δ} : Set X), ∀ b ∈ S, a * b = b * a :=
      fun a ha b hb => hcB a ha.1 b (hSB hb)
    have hle := Subgroup.card_le_of_le (sup_le (inf_le_left : B ⊓ Subgroup.centralizer
      ({δ} : Set X) ≤ B) hSB)
    rw [card_sup_of_commute hc hi, hS, hBc] at hle
    omega
  · rw [← h₁]
    let f : ↥(B ⊓ K₁) → ↥(B ⊓ Subgroup.centralizer ({δ} : Set X)) := fun b =>
      ⟨b * (δ * b * δ⁻¹) * (δ * δ * b * δ⁻¹ * δ⁻¹),
        norm_mem hB hδB (by rw [hδ3]; exact B.one_mem) b.2.1⟩
    have hmem2 : ∀ a ∈ K₁, δ * a * δ⁻¹ ∈ K₂ := fun a ha => by
      rw [hK₂, mem_conj_map_iff]
      simpa [mul_assoc] using ha
    have hmem3 : ∀ a ∈ K₁, δ * δ * a * δ⁻¹ * δ⁻¹ ∈ K₃ := fun a ha => by
      rw [hK₃, mem_conj_map_iff]
      simpa [mul_assoc] using ha
    have hf : Function.Injective f := by
      intro a a' h
      have h' : (a : X) * (δ * a * δ⁻¹) * (δ * δ * a * δ⁻¹ * δ⁻¹) =
          (a' : X) * (δ * a' * δ⁻¹) * (δ * δ * a' * δ⁻¹ * δ⁻¹) := congrArg Subtype.val h
      have hkey : (a' : X)⁻¹ * a = (δ * a' * δ⁻¹) * (δ * δ * a' * δ⁻¹ * δ⁻¹) *
          (δ * δ * a * δ⁻¹ * δ⁻¹)⁻¹ * (δ * a * δ⁻¹)⁻¹ := by
        calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * ((a : X) * (δ * a * δ⁻¹) * (δ * δ * a * δ⁻¹ * δ⁻¹)) *
              (δ * δ * a * δ⁻¹ * δ⁻¹)⁻¹ * (δ * a * δ⁻¹)⁻¹ := by group
          _ = (a' : X)⁻¹ * ((a' : X) * (δ * a' * δ⁻¹) * (δ * δ * a' * δ⁻¹ * δ⁻¹)) *
              (δ * δ * a * δ⁻¹ * δ⁻¹)⁻¹ * (δ * a * δ⁻¹)⁻¹ := by rw [h']
          _ = _ := by group
      have ha1 : (a' : X)⁻¹ * a ∈ K₁ := K₁.mul_mem (K₁.inv_mem a'.2.2) a.2.2
      have hcomm : ∀ k ∈ K₁, k * ((a' : X)⁻¹ * a) = ((a' : X)⁻¹ * a) * k := by
        intro k hk
        rw [hkey]
        have c1 : Commute k (δ * a' * δ⁻¹) := comm_of_comp c₁ c₂ n12 k hk _ (hmem2 _ a'.2.2)
        have c2 : Commute k (δ * δ * a' * δ⁻¹ * δ⁻¹) :=
          comm_of_comp c₁ c₃ n13 k hk _ (hmem3 _ a'.2.2)
        have c3 : Commute k (δ * δ * a * δ⁻¹ * δ⁻¹)⁻¹ :=
          (Commute.inv_right (comm_of_comp c₁ c₃ n13 k hk _ (hmem3 _ a.2.2) : Commute k _))
        have c4 : Commute k (δ * a * δ⁻¹)⁻¹ :=
          (Commute.inv_right (comm_of_comp c₁ c₂ n12 k hk _ (hmem2 _ a.2.2) : Commute k _))
        exact (((c1.mul_right c2).mul_right c3).mul_right c4).eq
      have h1 := central_eq_one e₁ ha1 hcomm
      exact Subtype.ext (inv_mul_eq_one.1 h1).symm
    exact Nat.card_le_card_of_injective f hf

structure QuotData (B D : Subgroup X) (δ : X) : Prop where
  sylow : ∀ R : Subgroup X, IsPGroup 3 ↥R → B ⊔ D ≤ R → R = B ⊔ D
  cardP : Nat.card ↥(B ⊔ D) = 3 ^ 7
  cardB : Nat.card ↥B = 3 ^ 6
  norm : B ⊔ D ≤ Subgroup.normalizer (B : Set X)
  memD : δ ∈ D
  notB : δ ∉ B
  centd : Nat.card ↥(B ⊓ Subgroup.centralizer ({δ} : Set X)) = 9
  closed : ∃ L : Subgroup X, (⊤ : Subgroup X) ≤ Subgroup.normalizer (L : Set X) ∧ B ≤ L ∧
    (B ⊔ D) ⊓ L ≤ B

theorem quotData_of_three {K B D : Subgroup X} {m : ℕ} (e : ↥K ≃* alternatingGroup (Fin 7))
    (hK : IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hBc : Nat.card ↥B = 3 ^ m)
    (hrank : ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card ↥E ≤ 3 ^ m)
    (hD : IsElemAbelian 3 D) (hDc : Nat.card ↥D = 9) (hW : IsPGroup 3 ↥(B ⊔ D))
    (hBn : ∀ ε ∈ D, B ≤ Subgroup.normalizer
      ((K.map (MulAut.conj ε).toMonoidHom : Subgroup X) : Set X))
    (hcent : Subgroup.centralizer
      (((⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom : Subgroup X)) : Set X) = ⊥)
    {δ₀ δ : X} (hδ₀D : δ₀ ∈ D) (hδ₀1 : δ₀ ≠ 1) (hδ₀K : δ₀ ∈ Subgroup.normalizer (K : Set X))
    (hδD : δ ∈ D) (hδK : δ ∉ Subgroup.normalizer (K : Set X)) :
    QuotData B D δ := by
  set K₂ := K.map (MulAut.conj δ).toMonoidHom with hK₂
  set K₃ := K.map (MulAut.conj (δ * δ)).toMonoidHom with hK₃
  have hδ3 : δ ^ 3 = 1 := hD.2 δ hδD
  have c₂ : IsComponentOf K₂ ⊤ := isComponentOf_conj' hK δ
  have c₃ : IsComponentOf K₃ ⊤ := isComponentOf_conj' hK (δ * δ)
  obtain ⟨e₂⟩ := card_map_conj_iso e δ
  obtain ⟨e₃⟩ := card_map_conj_iso e (δ * δ)
  have hδδK : δ * δ ∉ Subgroup.normalizer (K : Set X) := fun h =>
    hδK (mem_of_mul_self_mem (n := 1) (by simpa using hδ3) h)
  have n12 : K ≠ K₂ := fun h => hδK (mem_normalizer_of_map_conj_eq h.symm)
  have n13 : K ≠ K₃ := fun h => hδδK (mem_normalizer_of_map_conj_eq h.symm)
  have n23 : K₂ ≠ K₃ := by
    intro h
    have h' : K.map (MulAut.conj δ).toMonoidHom =
        (K.map (MulAut.conj δ).toMonoidHom).map (MulAut.conj δ).toMonoidHom := by
      rw [map_map_conj]
      exact h
    exact n12 (map_conj_injective δ h')
  have hLle : (⨆ ε ∈ D, K.map (MulAut.conj ε).toMonoidHom) ≤ K ⊔ K₂ ⊔ K₃ := by
    refine iSup₂_le fun ε hε => ?_
    rcases orbit_three hD hDc hδ₀D hδ₀1 hδ₀K hδD hδK hε with h | h | h <;> rw [h]
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hC : Subgroup.centralizer ((K ⊔ K₂ ⊔ K₃ : Subgroup X) : Set X) = ⊥ :=
    le_bot_iff.1 (hcent ▸ Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hLle))
  have hall : ∀ J : Subgroup X, IsComponentOf J ⊤ → J = K ∨ J = K₂ ∨ J = K₃ :=
    fun J hJ => comp_eq_of_cent hC hK c₂ c₃ hJ
  have b₁ : B ≤ Subgroup.normalizer (K : Set X) := by
    have := hBn 1 D.one_mem
    rwa [map_conj_eq_self_of_mem_normalizer (Subgroup.one_mem _)] at this
  have b₂ : B ≤ Subgroup.normalizer (K₂ : Set X) := hBn δ hδD
  have b₃ : B ≤ Subgroup.normalizer (K₃ : Set X) := hBn (δ * δ) (D.mul_mem hδD hδD)
  have h₁ := card_inf_eq_nine e hB hBc hrank b₁
  have h₂ := card_inf_eq_nine e₂ hB hBc hrank b₂
  have h₃ := card_inf_eq_nine e₃ hB hBc hrank b₃
  have hδB : δ ∉ B := fun h => hδK (b₁ h)
  have hδR : δ ∈ B ⊔ D := (le_sup_right : D ≤ B ⊔ D) hδD
  obtain ⟨hB6, hBeq, hRle⟩ := three_main e e₂ e₃ hK c₂ c₃ n12 n13 n23 hC b₁ b₂ b₃ h₁ h₂ h₃ hW
    le_sup_left hδR rfl rfl
  have hcardP : Nat.card ↥(B ⊔ D) = 3 ^ 7 :=
    le_antisymm hRle (card_ge_of_not_mem hW le_sup_left hB6 hδR hδB)
  have fwd : ∀ r ∈ B ⊔ D, ∀ b ∈ B, r * b * r⁻¹ ∈ B := by
    intro r hr b hb
    rw [hBeq] at hb ⊢
    exact ⟨(B ⊔ D).mul_mem ((B ⊔ D).mul_mem hr hb.1) ((B ⊔ D).inv_mem hr),
      conj_mem_normalizer3 hK c₂ c₃ hall hb.2 r⟩
  have hnorm : B ⊔ D ≤ Subgroup.normalizer (B : Set X) := fun r hr =>
    Subgroup.mem_normalizer_iff.2 fun b => ⟨fwd r hr b, fun h => by
      have := fwd r⁻¹ ((B ⊔ D).inv_mem hr) _ h
      simpa [mul_assoc] using this⟩
  refine ⟨fun R hR hBDR => ?_, hcardP, hB6, hnorm, hδD, hδB, ?_, ?_⟩
  · obtain ⟨-, -, hRle'⟩ := three_main e e₂ e₃ hK c₂ c₃ n12 n13 n23 hC b₁ b₂ b₃ h₁ h₂ h₃ hR
      (le_sup_left.trans hBDR) (hBDR hδR) rfl rfl
    exact (Subgroup.eq_of_le_of_card_ge hBDR (hRle'.trans hcardP.ge)).symm
  · exact card_cent_delta e e₂ e₃ hK c₂ c₃ n12 n13 n23 hC hB hB6 h₁ h₂ h₃ (hnorm hδR) hδ3 rfl rfl
  · refine ⟨K ⊔ K₂ ⊔ K₃, fun g _ => ?_, ?_, ?_⟩
    · have hmap : ∀ y : X, (K ⊔ K₂ ⊔ K₃).map (MulAut.conj y).toMonoidHom ≤ K ⊔ K₂ ⊔ K₃ := by
        intro y
        have hJ : ∀ {J : Subgroup X}, IsComponentOf J ⊤ →
            J.map (MulAut.conj y).toMonoidHom ≤ K ⊔ K₂ ⊔ K₃ := by
          intro J hJ
          rcases hall _ (isComponentOf_conj' hJ y) with h | h | h <;> rw [h]
          · exact le_sup_left.trans le_sup_left
          · exact le_sup_right.trans le_sup_left
          · exact le_sup_right
        rw [Subgroup.map_sup, Subgroup.map_sup]
        exact sup_le (sup_le (hJ hK) (hJ c₂)) (hJ c₃)
      exact mem_normalizer_of_map_le (hmap g) (hmap g⁻¹)
    · have hS := card_three_inf e e₂ e₃ hK c₂ c₃ n12 n13 n23 h₁ h₂ h₃
      have hSB : B ⊓ K ⊔ B ⊓ K₂ ⊔ B ⊓ K₃ ≤ B :=
        sup_le (sup_le inf_le_left inf_le_left) inf_le_left
      have hBS : B = B ⊓ K ⊔ B ⊓ K₂ ⊔ B ⊓ K₃ :=
        (Subgroup.eq_of_le_of_card_ge hSB (by rw [hS, hB6]; norm_num)).symm
      rw [hBS]
      exact sup_le (sup_le (inf_le_right.trans (le_sup_left.trans le_sup_left))
        (inf_le_right.trans (le_sup_right.trans le_sup_left))) (inf_le_right.trans le_sup_right)
    · have hcen : ∀ {J J' : Subgroup X}, IsComponentOf J ⊤ → IsComponentOf J' ⊤ → J ≠ J' →
          J' ≤ Subgroup.normalizer (J : Set X) := fun hJ hJ' hne x hx =>
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk =>
          comm_of_comp hJ hJ' hne k hk x hx)
      have hL : K ⊔ K₂ ⊔ K₃ ≤ Subgroup.normalizer (K : Set X) ⊓
          Subgroup.normalizer (K₂ : Set X) ⊓ Subgroup.normalizer (K₃ : Set X) := by
        refine le_inf (le_inf ?_ ?_) ?_
        · exact sup_le (sup_le Subgroup.le_normalizer (hcen hK c₂ n12)) (hcen hK c₃ n13)
        · exact sup_le (sup_le (hcen c₂ hK n12.symm) Subgroup.le_normalizer) (hcen c₂ c₃ n23)
        · exact sup_le (sup_le (hcen c₃ hK n13.symm) (hcen c₃ c₂ n23.symm)) Subgroup.le_normalizer
      exact (inf_le_inf_left _ hL).trans hBeq.ge

end Quot

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_barX {M H : Subgroup G} {y : G} (hy : y ∈ M) (hyH : y ∈ H) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hy⟩ ∈ barX 3 M H :=
  ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.2 hyH, rfl⟩

theorem exists_of_mem_barX {M H : Subgroup G} {z : ↥M ⧸ GLAPPrimeCore 3 ↥M}
    (hz : z ∈ barX 3 M H) :
    ∃ y ∈ H, ∃ hy : y ∈ M, QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hy⟩ = z := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, x.2, rfl⟩

theorem mk_injOn {M P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup 3 ↥P) {y y' : G}
    (hy : y ∈ P) (hy' : y' ∈ P)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hPM hy⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y', hPM hy'⟩) : y = y' := by
  have hS : IsPGroup 3 ↥(P.subgroupOf M) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hbot := isPGroup_inf_eq_bot_of_not_dvd Nat.prime_three hS
    (not_dvd_card_pPrimeCore Nat.prime_three M)
  have h1 : (⟨y, hPM hy⟩ : ↥M)⁻¹ * ⟨y', hPM hy'⟩ ∈ GLAPPrimeCore 3 ↥M := QuotientGroup.eq.1 h
  have h2 : (⟨y, hPM hy⟩ : ↥M)⁻¹ * ⟨y', hPM hy'⟩ ∈ P.subgroupOf M :=
    Subgroup.mem_subgroupOf.2 (P.mul_mem (P.inv_mem hy) hy')
  have h3 : (⟨y, hPM hy⟩ : ↥M)⁻¹ * ⟨y', hPM hy'⟩ ∈ P.subgroupOf M ⊓ GLAPPrimeCore 3 ↥M :=
    Subgroup.mem_inf.2 ⟨h2, h1⟩
  rw [hbot, Subgroup.mem_bot] at h3
  have h4 : y⁻¹ * y' = 1 := congrArg Subtype.val h3
  exact (inv_mul_eq_one.1 h4)

theorem barX_gLBConj_eq {M L : Subgroup G} {g : G} (hg : g ∈ M) :
    barX 3 M (GLBConj g L) = (barX 3 M L).map
      (MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩)⁻¹).toMonoidHom := by
  ext z
  rw [mem_conj_map_iff, inv_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : g * x * g⁻¹ ∈ L := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hx)
    have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩ * QuotientGroup.mk' _ x *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩)⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g * x * g⁻¹,
          M.mul_mem (M.mul_mem hg x.2) (M.inv_mem hg)⟩ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [this]
    exact mk_mem_barX _ hx'
  · intro hz
    obtain ⟨w, hwL, hwM, hw⟩ := exists_of_mem_barX hz
    have hz' : z = QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)
        ⟨g⁻¹ * w * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hwM) hg⟩ := by
      have e : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)
          ⟨g⁻¹ * w * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hwM) hg⟩ =
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩)⁻¹ *
            QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨w, hwM⟩ *
              QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e, hw]
      group
    rw [hz']
    refine mk_mem_barX _ (mem_gLBConj.2 ?_)
    rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
    exact hwL

structure Wreath (P B : Subgroup G) (d : G) : Prop where
  le : B ≤ P
  elem : IsElemAbelian 3 B
  cardB : Nat.card ↥B = 3 ^ 6
  cardP : Nat.card ↥P = 3 ^ 7
  norm : P ≤ Subgroup.normalizer (B : Set G)
  memP : d ∈ P
  notB : d ∉ B
  pow : d ^ 3 = 1
  sup : P = B ⊔ Subgroup.zpowers d
  centd : Nat.card ↥(B ⊓ Subgroup.centralizer ({d} : Set G)) = 9

theorem wreath_of_quotData {M B D P : Subgroup G} (hBM : B ≤ M) (hDM : D ≤ M) (hPM : P ≤ M)
    (hP : IsPGroup 3 ↥P) (hBDP : B ⊔ D ≤ P) (hB : IsElemAbelian 3 B) (hD : IsElemAbelian 3 D)
    {δ : ↥M ⧸ GLAPPrimeCore 3 ↥M} (hQ : QuotData (barX 3 M B) (barX 3 M D) δ) :
    ∃ d ∈ D, Wreath P B d ∧ ∀ b ∈ B, ∀ g ∈ M, g * b * g⁻¹ ∈ P → g * b * g⁻¹ ∈ B := by
  have hBP : B ≤ P := le_sup_left.trans hBDP
  have hDP : D ≤ P := le_sup_right.trans hBDP
  have hBp : IsPGroup 3 ↥B := hP.to_le hBP
  have hbarP : barX 3 M P = barX 3 M B ⊔ barX 3 M D :=
    hQ.sylow _ (Lemma135.isPGroup_barX hPM hP)
      (sup_le (barX_mono_of_le 3 hBP) (barX_mono_of_le 3 hDP))
  have hcardP : Nat.card ↥P = 3 ^ 7 := by
    rw [← Lemma135.card_barX_of_isPGroup hPM hP, hbarP, hQ.cardP]
  have hcardB : Nat.card ↥B = 3 ^ 6 := by
    rw [← Lemma135.card_barX_of_isPGroup hBM hBp, hQ.cardB]
  obtain ⟨d, hdD, hdM, hdδ⟩ := exists_of_mem_barX hQ.memD
  have hdP : d ∈ P := hDP hdD
  have hdB : d ∉ B := fun h => hQ.notB (hdδ ▸ mk_mem_barX hdM h)
  have himP : ∀ y (hy : y ∈ P), QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y, hPM hy⟩ ∈
      barX 3 M B ⊔ barX 3 M D := fun y hy => hbarP ▸ mk_mem_barX (hPM hy) hy
  have fwd : ∀ y ∈ P, ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro y hy b hb
    have h1 := (Subgroup.mem_normalizer_iff.1 (hQ.norm (himP y hy)) _).1 (mk_mem_barX (hBM hb) hb)
    obtain ⟨b', hb'B, hb'M, hb'⟩ := exists_of_mem_barX h1
    have hyb : y * b * y⁻¹ ∈ P := P.mul_mem (P.mul_mem hy (hBP hb)) (P.inv_mem hy)
    have e : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨b', hPM (hBP hb'B)⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨y * b * y⁻¹, hPM hyb⟩ := by
      rw [show (⟨b', hPM (hBP hb'B)⟩ : ↥M) = ⟨b', hb'M⟩ from rfl, hb', ← map_inv, ← map_mul,
        ← map_mul]
      rfl
    rw [← mk_injOn hPM hP (hBP hb'B) hyb e]
    exact hb'B
  have hnorm : P ≤ Subgroup.normalizer (B : Set G) := fun y hy =>
    Subgroup.mem_normalizer_iff.2 fun b => ⟨fwd y hy b, fun h => by
      have := fwd y⁻¹ (P.inv_mem hy) _ h
      simpa [mul_assoc] using this⟩
  have hsup : P = B ⊔ Subgroup.zpowers d := by
    have hle : B ⊔ Subgroup.zpowers d ≤ P := sup_le hBP (Subgroup.zpowers_le.2 hdP)
    have hge := card_ge_of_not_mem (hP.to_le hle) le_sup_left hcardB
      ((le_sup_right : Subgroup.zpowers d ≤ B ⊔ Subgroup.zpowers d) (Subgroup.mem_zpowers d)) hdB
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP]; exact hge)).symm
  have hcent : barX 3 M (B ⊓ Subgroup.centralizer ({d} : Set G)) =
      barX 3 M B ⊓ Subgroup.centralizer ({δ} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, hbBC, hbM, rfl⟩ := exists_of_mem_barX hz
      obtain ⟨hbB, hbd⟩ := Subgroup.mem_inf.1 hbBC
      refine Subgroup.mem_inf.2 ⟨mk_mem_barX hbM hbB, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hbd ⊢
      rw [← hdδ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hbd
    · intro hz
      obtain ⟨hzB, hzd⟩ := Subgroup.mem_inf.1 hz
      obtain ⟨b, hbB, hbM, rfl⟩ := exists_of_mem_barX hzB
      rw [Subgroup.mem_centralizer_singleton_iff, ← hdδ, ← map_mul, ← map_mul] at hzd
      have hbd : b * d = d * b := by
        have h1 := mk_injOn hPM hP (P.mul_mem (hBP hbB) hdP) (P.mul_mem hdP (hBP hbB))
          (y := b * d) (y' := d * b) hzd
        exact h1
      exact mk_mem_barX hbM (Subgroup.mem_inf.2 ⟨hbB, Subgroup.mem_centralizer_singleton_iff.2 hbd⟩)
  have hcentd : Nat.card ↥(B ⊓ Subgroup.centralizer ({d} : Set G)) = 9 := by
    rw [← Lemma135.card_barX_of_isPGroup (inf_le_left.trans hBM) (hBp.to_le inf_le_left), hcent,
      hQ.centd]
  refine ⟨d, hdD, ⟨hBP, hB, hcardB, hcardP, hnorm, hdP, hdB, hD.2 d hdD, hsup, hcentd⟩, ?_⟩
  intro b hb g hg hgP
  obtain ⟨L, hLn, hBL, hPL⟩ := hQ.closed
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g * b * g⁻¹, hPM hgP⟩ ∈ barX 3 M B := by
    apply hPL
    refine ⟨himP _ hgP, ?_⟩
    have e : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g * b * g⁻¹, hPM hgP⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩ *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨b, hBM hb⟩ *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hLn (Subgroup.mem_top _)) _).1
      (hBL (mk_mem_barX (hBM hb) hb))
  obtain ⟨b', hb'B, hb'M, hb'⟩ := exists_of_mem_barX h1
  rw [← mk_injOn hPM hP (hBP hb'B) hgP hb']
  exact hb'B

theorem wreath_of_cex (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hcent : Lemma135.cent M D L = ⊥) {P : Subgroup G} (hPM : IsSylowIn 3 M P)
    (hBDP : B ⊔ D ≤ P) :
    ∃ d ∈ D, Wreath P B d ∧ ∀ b ∈ B, ∀ g ∈ M, g * b * g⁻¹ ∈ P → g * b * g⁻¹ ∈ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, eL, -⟩ := Lemma135b.cex134_gamma hP95 h111 h121 hcomp h
  obtain ⟨hLc, hnc⟩ := hcomp h.toSec13 h.hL
  have hS : GLStanding G m 3 := h.standing
  have hB : IsBOneMax 3 B := h.bOne
  have hM2 : CFSG.Open.IsTwoLocal M := h.pre.1.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDA : D ≤ A := h.hD.1
  have hDM : D ≤ M := hDA.trans hAM
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have hBEA : CFSG.Open.IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ m := by
    have := hB.1.2.1
    rw [hS.rank_eq] at this
    exact this
  have hTLR : CFSG.Open.twoLocalPrimeRank 3 G = m := hS.rank_eq
  have hBp : IsPGroup 3 ↥B := IsPGroup.iff_card.2 ⟨m, hBcard⟩
  have hDEA : IsElemAbelian 3 D := h.hD.2.1
  have hDcard : Nat.card D = 3 ^ 2 := h.hD.2.2
  have hDp : IsPGroup 3 ↥D := IsPGroup.iff_card.2 ⟨2, hDcard⟩
  set K := barX 3 M L with hKdef
  have hK : IsComponentOf K ⊤ := hLc.2.2.1
  have hBe : IsElemAbelian 3 (barX 3 M B) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.isElemAbelian_map (QuotientGroup.mk' _)
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.isElemAbelian_subgroupOf hBM hBEA)
  have hBc : Nat.card (barX 3 M B) = 3 ^ m := by
    rw [Lemma135.card_barX_of_isPGroup hBM hBp, hBcard]
  have hDe : IsElemAbelian 3 (barX 3 M D) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.isElemAbelian_map (QuotientGroup.mk' _)
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.isElemAbelian_subgroupOf hDM hDEA)
  have hDc : Nat.card (barX 3 M D) = 9 := by
    rw [Lemma135.card_barX_of_isPGroup hDM hDp, hDcard]
    norm_num
  have hTop := Lemma135.pRank_quotient_le hM2 hTLR
  have hrank : ∀ E : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), CFSG.Open.IsElemAbelian 3 E →
      Nat.card ↥E ≤ 3 ^ m := by
    intro E hE
    have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
    have hkm : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hkm.trans hTop)
  have hW : IsPGroup 3 ↥(barX 3 M B ⊔ barX 3 M D) := by
    have hABM : A ⊔ B ≤ M := sup_le hAM hBM
    have hABp : IsPGroup 3 ↥(barX 3 M (A ⊔ B)) := Lemma135.isPGroup_barX hABM h.hAB
    have hle : barX 3 M B ⊔ barX 3 M D ≤ barX 3 M (A ⊔ B) :=
      sup_le (barX_mono_of_le 3 le_sup_right) (barX_mono_of_le 3 (hDA.trans le_sup_left))
    exact hABp.to_le hle
  have hLI : L ≤ Istar 3 M D := (h.hL.1).trans (Lemma135.iof_le_istar' 3 M D)
  have hBn : ∀ ε ∈ barX 3 M D, barX 3 M B ≤
      Subgroup.normalizer ((K.map (MulAut.conj ε).toMonoidHom : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    intro ε hε
    obtain ⟨d, hd, hdM, rfl⟩ := exists_of_mem_barX hε
    have hdi : d⁻¹ ∈ M := M.inv_mem hdM
    have e0 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨d⁻¹, hdi⟩)⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨d, hdM⟩ := by
      rw [← map_inv]
      congr 1
      exact Subtype.ext (inv_inv d)
    have e1 : K.map (MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨d, hdM⟩)).toMonoidHom =
        barX 3 M (GLBConj d⁻¹ L) := by
      rw [barX_gLBConj_eq hdi, e0]
    rw [e1]
    apply barX_le_normalizer
    exact (((h133 h.toSec13).2 (GLBConj d⁻¹ L)
      (Lemma135.glaPComponent_istar_conj Nat.prime_three hLc hLI hdi)).2).1
  have hcent' : Subgroup.centralizer
      (((⨆ ε ∈ barX 3 M D, K.map (MulAut.conj ε).toMonoidHom :
        Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M))) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) = ⊥ := by
    have hle : barX 3 M (Lstarsub D L) ≤
        ⨆ ε ∈ barX 3 M D, K.map (MulAut.conj ε).toMonoidHom := by
      rw [Prop95Parts.barX_le_iff (Claims135.lstarsub_le hDM hLc.1)]
      refine iSup₂_le fun d hd => ?_
      rw [← Prop95Parts.barX_le_iff (Claims135.gLBConj_le_of_mem hLc.1 (hDM hd)),
        barX_gLBConj_eq (hDM hd)]
      exact le_iSup₂_of_le (f := fun ε (_ : ε ∈ barX 3 M D) => K.map (MulAut.conj ε).toMonoidHom)
        _ ((barX 3 M D).inv_mem (mk_mem_barX (hDM hd) hd)) le_rfl
    unfold Lemma135.cent at hcent
    exact le_bot_iff.1 (hcent ▸ Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hle))
  have hBK : barX 3 M B ≤ Subgroup.normalizer (K : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    have := hBn 1 (Subgroup.one_mem _)
    rwa [map_conj_eq_self_of_mem_normalizer (Subgroup.one_mem _)] at this
  by_cases h1 : barX 3 M D ≤ Subgroup.normalizer (K : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))
  · exact (false_of_one_comp eL (Lemma135.isPGroup_barX hBM hBp) hBc hS.four_le hBK hcent'
      h1).elim
  obtain ⟨δ, hδD, hδK⟩ := Set.not_subset.1 h1
  by_cases h9 : ∃ δ₀ ∈ barX 3 M D, δ₀ ≠ 1 ∧
      δ₀ ∈ Subgroup.normalizer (K : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))
  ·
    obtain ⟨δ₀, hδ₀D, hδ₀1, hδ₀K⟩ := h9
    exact wreath_of_quotData hBM hDM hPM.1 hPM.2.1 hBDP hBEA hDEA
      (quotData_of_three eL hK hBe hBc hrank hDe hDc hW hBn hcent' hδ₀D hδ₀1 hδ₀K hδD hδK)
  exfalso
  push Not at h9
  have hO : GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hH1 : CFSG.HardMathSupport.Timmesfeld.Balance.H1Stmt.{0} := by
    intro X Z _ _ _ φ hφ p hp Q hQ
    exact CFSG.HardMathSupport.Timmesfeld.Proving.map_glaPPrimeCoreOf_centralizer_le φ hφ hp hQ
  have hsig : sigmaStar D ≤ GLAPPrimeCoreOf 3 M := by
    refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
    have hO2M : pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≤ M :=
      (pCoreOf_two_le_glaPPrimeCoreOf Nat.prime_three (by norm_num) _).trans
        (h111 h.toSec11 (hDA hd) hd1)
    apply CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_glaPPrimeCoreOf_of_barX_eq_bot hO2M
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨x, hx, hxM, rfl⟩ := exists_of_mem_barX hz
    have hp2 : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) :=
      (CFSG.pCore_isPGroup (p := 2)).of_equiv
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _))
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp2
    have hx' : x ∈ GLAPPrimeCoreOf 3 (M ⊓ Subgroup.centralizer ({d} : Set G)) := by
      refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.le_glaPPrimeCoreOf
        (le_inf hO2M (Subgroup.map_subtype_le _)) ?_ ?_ hx
      · intro a ha n hn
        exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ (Subgroup.mem_inf.1 ha).2)
          n).1 hn
      · rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num)
    have hmk := CFSG.HardMathSupport.Timmesfeld.Balance.mk_mem_centralizer_core hH1
      Nat.prime_three hDM hDEA (x := ⟨x, hxM⟩) (e := ⟨d, hDM hd⟩) hd
      (fun h => hd1 (congrArg Subtype.val h)) hx'
    have hδ1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨d, hDM hd⟩ ≠ 1 := by
      intro h0
      apply hd1
      refine mk_injOn hDM hDp hd D.one_mem ?_
      rw [h0]
      exact (map_one _).symm
    have hcore := core_eq_bot_of_nine hO hK hDe hcent' h9 (mk_mem_barX (hDM hd) hd) hδ1
    have hmk' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨x, hxM⟩ ∈
        GLAPPrimeCoreOf 3 (Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) ⟨d, hDM hd⟩} :
            Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := hmk
    rw [hcore, Subgroup.mem_bot] at hmk'
    exact hmk'
  have hbar : barX 3 M (gammaStar 3 D) = ⊥ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.barX_eq_bot_of_le
      ((gammaStar_le_gammaD 3 D).trans ((gammaD_le_sigmaStar D).trans hsig))
  exact hnc (by rw [hbar]; exact bot_le)

end Transfer

section WreathFacts

variable {G : Type} [Group G] [Finite G]

theorem card_eq_card_ker_mul_card_range {H K : Type} [Group H] [Group K] [Finite H]
    (φ : H →* K) : Nat.card H = Nat.card φ.ker * Nat.card φ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]

namespace Wreath

variable {P B : Subgroup G} {d : G}

theorem normal_subgroupOf (w : Wreath P B d) : (B.subgroupOf P).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer w.le).2 w.norm

theorem card_quot (w : Wreath P B d) :
    haveI := w.normal_subgroupOf; Nat.card (↥P ⧸ B.subgroupOf P) = 3 := by
  haveI := w.normal_subgroupOf
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf P)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe w.le).toEquiv, w.cardB, w.cardP] at h
  omega

theorem card_of_not_le (w : Wreath P B d) {H : Subgroup G} (hHP : H ≤ P) (hHB : ¬ H ≤ B) :
    Nat.card ↥H = 3 * Nat.card ↥(H ⊓ B) := by
  haveI := w.normal_subgroupOf
  let φ : ↥H →* ↥P ⧸ B.subgroupOf P := (QuotientGroup.mk' _).comp (Subgroup.inclusion hHP)
  have hker : Nat.card φ.ker = Nat.card ↥(H ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have := (QuotientGroup.eq_one_iff _).1 hx
      exact Subgroup.mem_subgroupOf.1 this
    · rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 y.2.2)
  have hrange : Nat.card φ.range = 3 := by
    have hdvd : Nat.card φ.range ∣ 3 := w.card_quot ▸ Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exfalso
      apply hHB
      intro x hx
      have hφ : φ ⟨x, hx⟩ ∈ φ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [(Subgroup.card_eq_one).1 h1, Subgroup.mem_bot] at hφ
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hφ)
    · exact h3
  rw [card_eq_card_ker_mul_card_range φ, hker, hrange, mul_comm]

theorem pow_three_mem (w : Wreath P B d) {x : G} (hx : x ∈ P) : x ^ 3 ∈ B := by
  haveI := w.normal_subgroupOf
  have h1 : (QuotientGroup.mk' (B.subgroupOf P) ⟨x, hx⟩) ^ 3 = 1 := by
    have := pow_card_eq_one' (x := QuotientGroup.mk' (B.subgroupOf P) ⟨x, hx⟩)
    rwa [w.card_quot] at this
  rw [← map_pow] at h1
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

theorem commutator_mem (w : Wreath P B d) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ B := by
  haveI := w.normal_subgroupOf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (↥P ⧸ B.subgroupOf P) := isCyclic_of_prime_card w.card_quot
  letI : CommGroup (↥P ⧸ B.subgroupOf P) := IsCyclic.commGroup
  have h1 : QuotientGroup.mk' (B.subgroupOf P) (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_comm (QuotientGroup.mk' (B.subgroupOf P) ⟨x, hx⟩)]
    group
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

theorem exists_eq_mul_pow (w : Wreath P B d) {x : G} (hx : x ∈ P) :
    ∃ b ∈ B, x = b ∨ x = b * d ∨ x = b * (d * d) := by
  rw [w.sup] at hx
  obtain ⟨b, hb, z, hz, rfl⟩ := mem_sup_of_le_normalizer
    ((Subgroup.zpowers_le.2 (w.norm w.memP)).trans le_rfl) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine ⟨b, hb, ?_⟩
  rcases zpow_cases w.pow k with h | h | h <;> rw [h]
  · left; exact mul_one b
  · right; left; rfl
  · right; right; rfl

theorem mem_centralizer_mul_iff {b b₀ y : G} (hb : b * b₀ = b₀ * b) :
    b ∈ Subgroup.centralizer ({b₀ * y} : Set G) ↔ b ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have : b₀ * (b * y) = b₀ * (y * b) := by
      calc b₀ * (b * y) = (b₀ * b) * y := (mul_assoc _ _ _).symm
        _ = (b * b₀) * y := by rw [hb]
        _ = b * (b₀ * y) := mul_assoc _ _ _
        _ = b₀ * y * b := h
        _ = b₀ * (y * b) := mul_assoc _ _ _
    exact mul_left_cancel this
  · intro h
    calc b * (b₀ * y) = (b * b₀) * y := (mul_assoc _ _ _).symm
      _ = (b₀ * b) * y := by rw [hb]
      _ = b₀ * (b * y) := mul_assoc _ _ _
      _ = b₀ * (y * b) := by rw [h]
      _ = b₀ * y * b := (mul_assoc _ _ _).symm

theorem inf_centralizer_eq (w : Wreath P B d) {x : G} (hxP : x ∈ P) (hxB : x ∉ B) :
    B ⊓ Subgroup.centralizer ({x} : Set G) = B ⊓ Subgroup.centralizer ({d} : Set G) := by
  have hcB := comm_of_isElemAbelian w.elem
  have hd4 : d * d * (d * d) = d := by
    calc d * d * (d * d) = d * (d * d) * d := by group
      _ = d := by rw [← pow_three, w.pow, one_mul]
  have hsq : ∀ b : G, b ∈ Subgroup.centralizer ({d * d} : Set G) ↔
      b ∈ Subgroup.centralizer ({d} : Set G) := by
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc b * d = b * (d * d * (d * d)) := by rw [hd4]
        _ = (d * d * (d * d)) * b := by
          rw [← mul_assoc, h, mul_assoc, h, ← mul_assoc]
        _ = d * b := by rw [hd4]
    · intro h
      rw [← mul_assoc, h, mul_assoc, h, ← mul_assoc]
  obtain ⟨b₀, hb₀, hx | hx | hx⟩ := w.exists_eq_mul_pow hxP
  · exact absurd (hx ▸ hb₀) hxB
  · ext b
    simp only [Subgroup.mem_inf]
    refine and_congr_right fun hb => ?_
    rw [hx]
    exact mem_centralizer_mul_iff (hcB b hb b₀ hb₀)
  · ext b
    simp only [Subgroup.mem_inf]
    refine and_congr_right fun hb => ?_
    rw [hx, mem_centralizer_mul_iff (hcB b hb b₀ hb₀)]
    exact hsq b

theorem card_inf_centralizer (w : Wreath P B d) {x : G} (hxP : x ∈ P) (hxB : x ∉ B) :
    Nat.card ↥(B ⊓ Subgroup.centralizer ({x} : Set G)) = 9 := by
  rw [w.inf_centralizer_eq hxP hxB, w.centd]

theorem centerOf_eq (w : Wreath P B d) {x : G} (hxP : x ∈ P) (hxB : x ∉ B) :
    centerOf P = B ⊓ Subgroup.centralizer ({x} : Set G) := by
  have hcB := comm_of_isElemAbelian w.elem
  ext z
  rw [Claims135.mem_centerOf_iff]
  constructor
  · rintro ⟨hzP, hz⟩
    have hzB : z ∈ B := by
      by_contra hzB
      have h9 := w.card_inf_centralizer hzP hzB
      have hle : B ≤ B ⊓ Subgroup.centralizer ({z} : Set G) := fun b hb =>
        ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 (hz b (w.le hb))⟩
      have := Subgroup.card_le_of_le hle
      rw [h9, w.cardB] at this
      norm_num at this
    exact ⟨hzB, Subgroup.mem_centralizer_singleton_iff.2 (hz x hxP).symm⟩
  · intro hz
    rw [w.inf_centralizer_eq hxP hxB] at hz
    obtain ⟨hzB, hzd⟩ := Subgroup.mem_inf.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hzd
    refine ⟨w.le hzB, fun y hy => ?_⟩
    have hzd' : d * z = z * d := hzd.symm
    obtain ⟨b, hb, hy' | hy' | hy'⟩ := w.exists_eq_mul_pow hy <;> rw [hy']
    · exact hcB b hb z hzB
    · rw [mul_assoc, hzd', ← mul_assoc, hcB b hb z hzB, mul_assoc]
    · rw [mul_assoc, mul_assoc, hzd', ← mul_assoc d, hzd', mul_assoc, ← mul_assoc b z,
        hcB b hb z hzB, mul_assoc]

theorem inf_centralizer_P (w : Wreath P B d) {x : G} (hxP : x ∈ P) (hxB : x ∉ B) :
    P ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x ⊔ centerOf P ∧
      Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) = 27 := by
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hZ := w.centerOf_eq hxP hxB
  have hcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) = 27 := by
    rw [w.card_of_not_le inf_le_left (fun h => hxB (h ⟨hxP, hxC⟩)),
      show P ⊓ Subgroup.centralizer ({x} : Set G) ⊓ B = B ⊓ Subgroup.centralizer ({x} : Set G) by
        ext y
        simp only [Subgroup.mem_inf]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨w.le h.1, h.2⟩, h.1⟩⟩,
      w.card_inf_centralizer hxP hxB]
  have hle : Subgroup.zpowers x ⊔ centerOf P ≤ P ⊓ Subgroup.centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.2 ⟨hxP, hxC⟩)
      (hZ ▸ fun y hy => ⟨w.le (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩)
  have hge : 27 ≤ Nat.card ↥(Subgroup.zpowers x ⊔ centerOf P) := by
    rw [w.card_of_not_le (hle.trans inf_le_left) (fun h => hxB (h ((le_sup_left :
      Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x))))]
    have : B ⊓ Subgroup.centralizer ({x} : Set G) ≤ (Subgroup.zpowers x ⊔ centerOf P) ⊓ B :=
      fun y hy => ⟨(le_sup_right : centerOf P ≤ _) (hZ ▸ hy), (Subgroup.mem_inf.1 hy).1⟩
    have h2 := Subgroup.card_le_of_le this
    rw [w.card_inf_centralizer hxP hxB] at h2
    omega
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hge)).symm, hcard⟩

end Wreath

end WreathFacts

theorem centerInput_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement) :
    Claims135.CenterInput := by
  intro G _ _ m B M E A D T L h hcent P hPM hBDP
  obtain ⟨d, -, w, -⟩ := wreath_of_cex hP95 h111 h121 hcomp h133 h hcent hPM hBDP
  rw [w.centerOf_eq w.memP w.notB]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_of_le w.elem inf_le_left)
    (by rw [w.centd]; norm_num)

section FamilyCore

variable {G : Type} [Group G] [Finite G]

@[expose] def transv (F W : Subgroup G) (x : G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (F : Set G) ∧ y ∈ Subgroup.centralizer (W : Set G) ∧
    y * x * y⁻¹ * x⁻¹ ∈ W}
  mul_mem' := by
    rintro y₁ y₂ ⟨h1F, h1W, h1x⟩ ⟨h2F, h2W, h2x⟩
    refine ⟨Subgroup.mul_mem _ h1F h2F, Subgroup.mul_mem _ h1W h2W, ?_⟩
    have hc := Subgroup.mem_centralizer_iff.1 h1W _ h2x
    have e : y₁ * y₂ * x * (y₁ * y₂)⁻¹ * x⁻¹ =
        (y₁ * (y₂ * x * y₂⁻¹ * x⁻¹) * y₁⁻¹) * (y₁ * x * y₁⁻¹ * x⁻¹) := by group
    rw [e, ← hc, show y₂ * x * y₂⁻¹ * x⁻¹ * y₁ * y₁⁻¹ = y₂ * x * y₂⁻¹ * x⁻¹ by group]
    exact W.mul_mem h2x h1x
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, by simp⟩
  inv_mem' := by
    rintro y ⟨hF, hW, hx⟩
    refine ⟨Subgroup.inv_mem _ hF, Subgroup.inv_mem _ hW, ?_⟩
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hW) _ (W.inv_mem hx)
    have e : y⁻¹ * x * y⁻¹⁻¹ * x⁻¹ = y⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * y := by group
    rw [e, ← hc, show (y * x * y⁻¹ * x⁻¹)⁻¹ * y⁻¹ * y = (y * x * y⁻¹ * x⁻¹)⁻¹ by group]
    exact W.inv_mem hx

@[expose] def transvHom {F W : Subgroup G} {x : G} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    ↥(transv F W x) →* G :=
  MonoidHom.mk' (fun y => (y : G) * x * (y : G)⁻¹ * x⁻¹) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨-, haW, hax⟩ := ha
    obtain ⟨-, -, hbx⟩ := hb
    show a * b * x * (a * b)⁻¹ * x⁻¹ = a * x * a⁻¹ * x⁻¹ * (b * x * b⁻¹ * x⁻¹)
    have hc := Subgroup.mem_centralizer_iff.1 haW _ hbx
    calc a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
      _ = (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) := by rw [← hc]; group
      _ = a * x * a⁻¹ * x⁻¹ * (b * x * b⁻¹ * x⁻¹) := hW _ hbx _ hax)

theorem transvHom_apply {F W : Subgroup G} {x : G} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (y : ↥(transv F W x)) : transvHom hW y = (y : G) * x * (y : G)⁻¹ * x⁻¹ := rfl

theorem transvHom_mem {F W : Subgroup G} {x : G} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (y : ↥(transv F W x)) : transvHom hW y ∈ W := y.2.2.2

section Bundle

variable {F W : Subgroup G} {x : G} (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hxF : x ∈ F)
  (hWF : W ≤ F) (hFsup : F = Subgroup.zpowers x ⊔ W)
include hFab hxF hWF hFsup

theorem exists_zpow_mul {f : G} (hf : f ∈ F) : ∃ k : ℤ, ∃ w ∈ W, f = x ^ k * w := by
  have hn : W ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    refine le_trans (fun w hw => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hFab z ((Subgroup.zpowers_le.2 hxF) hz) w (hWF hw)
  rw [hFsup] at hf
  obtain ⟨a, ha, w, hw, rfl⟩ := mem_sup_of_le_normalizer hn hf
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact ⟨k, w, hw, rfl⟩

theorem transv_formula' {y : G} (hy : y ∈ transv F W x) (k : ℤ) {w : G} (hw : w ∈ W) :
    y * (x ^ k * w) * y⁻¹ * (x ^ k * w)⁻¹ = (y * x * y⁻¹ * x⁻¹) ^ k := by
  obtain ⟨hyF, hyW, hyx⟩ := hy
  set c := y * x * y⁻¹ * x⁻¹ with hc
  have hcx : Commute c x := hFab c (hWF hyx) x hxF
  have h1 : y * x * y⁻¹ = c * x := by rw [hc]; group
  have h2 : y * w * y⁻¹ = w := by
    have := Subgroup.mem_centralizer_iff.1 hyW w hw
    rw [← this]; group
  have h3 : y * x ^ k * y⁻¹ = (c * x) ^ k := by
    rw [← h1, conj_zpow]
  calc y * (x ^ k * w) * y⁻¹ * (x ^ k * w)⁻¹ =
      (y * x ^ k * y⁻¹) * (y * w * y⁻¹) * (x ^ k * w)⁻¹ := by group
    _ = (c * x) ^ k * w * (x ^ k * w)⁻¹ := by rw [h3, h2]
    _ = c ^ k * x ^ k * w * (x ^ k * w)⁻¹ := by rw [hcx.mul_zpow]
    _ = c ^ k := by group

theorem transv_formula {y : G} (hy : y ∈ transv F W x) {f : G} (hf : f ∈ F) :
    ∃ k : ℤ, y * f * y⁻¹ * f⁻¹ = (y * x * y⁻¹ * x⁻¹) ^ k := by
  obtain ⟨k, w, hw, rfl⟩ := exists_zpow_mul hFab hxF hWF hFsup hf
  exact ⟨k, transv_formula' hFab hxF hWF hFsup hy k hw⟩

theorem comm_mem_of_transv {y : G} (hy : y ∈ transv F W x) {f : G} (hf : f ∈ F) :
    y * f * y⁻¹ * f⁻¹ ∈ W := by
  obtain ⟨k, hk⟩ := transv_formula hFab hxF hWF hFsup hy hf
  rw [hk]
  exact W.zpow_mem hy.2.2 k

theorem centralizer_le_transv : Subgroup.centralizer (F : Set G) ≤ transv F W x := by
  intro c hc
  refine ⟨Subgroup.centralizer_le_normalizer _ hc,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hWF) hc, ?_⟩
  have := Subgroup.mem_centralizer_iff.1 hc x hxF
  rw [show c * x * c⁻¹ * x⁻¹ = 1 by rw [← this]; group]
  exact W.one_mem

theorem mem_centralizer_of_transv {y : G} (hy : y ∈ transv F W x)
    (h1 : y * x * y⁻¹ * x⁻¹ = 1) : y ∈ Subgroup.centralizer (F : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  obtain ⟨k, hk⟩ := transv_formula hFab hxF hWF hFsup hy hf
  rw [h1, one_zpow] at hk
  have : y * f * y⁻¹ = f := by
    calc y * f * y⁻¹ = y * f * y⁻¹ * f⁻¹ * f := by group
      _ = f := by rw [hk, one_mul]
  calc f * y = y * f * y⁻¹ * y := by rw [this]
    _ = y * f := by group

theorem card_transv (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    Nat.card ↥(transv F W x) = Nat.card ↥(Subgroup.centralizer (F : Set G)) *
      Nat.card (transvHom (F := F) (x := x) hW).range := by
  rw [card_eq_card_ker_mul_card_range (transvHom (F := F) (x := x) hW)]
  congr 1
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1.1, mem_centralizer_of_transv hFab hxF hWF hFsup y.1.2 y.2⟩
      invFun := fun c => ⟨⟨c.1, centralizer_le_transv hFab hxF hWF hFsup c.2⟩, ?_⟩
      left_inv := fun y => rfl
      right_inv := fun c => rfl }
  rw [MonoidHom.mem_ker, transvHom_apply]
  have := Subgroup.mem_centralizer_iff.1 c.2 x hxF
  show (c : G) * x * (c : G)⁻¹ * x⁻¹ = 1
  rw [← this]; group

theorem conj_mem_transv {g : G} (hgF : g ∈ Subgroup.normalizer (F : Set G))
    (hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) (hgW' : ∀ w ∈ W, g⁻¹ * w * g ∈ W) {y : G}
    (hy : y ∈ transv F W x) : g * y * g⁻¹ ∈ transv F W x := by
  obtain ⟨hyF, hyW, hyx⟩ := hy
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgF hyF) (Subgroup.inv_mem _ hgF), ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := Subgroup.mem_centralizer_iff.1 hyW _ (hgW' w hw)
    calc w * (g * y * g⁻¹) = g * ((g⁻¹ * w * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * w := by group
  · have hx' : g⁻¹ * x * g ∈ F := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgF) x).1 hxF
      simpa using this
    have h := comm_mem_of_transv hFab hxF hWF hFsup ⟨hyF, hyW, hyx⟩ hx'
    have e : g * y * g⁻¹ * x * (g * y * g⁻¹)⁻¹ * x⁻¹ =
        g * (y * (g⁻¹ * x * g) * y⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact hgW _ h

end Bundle

theorem Wreath.alperin_shape {P B : Subgroup G} {d : G} (w : Wreath P B d) {F : Subgroup G}
    (hF : CFSG.RankTwoShapes.IsAlperinSubgroup 3 P F) (hFB : ¬ F ≤ B)
    (hZ : centerOf F ≠ centerOf P) :
    ∃ x ∈ F, x ∉ B ∧ F = P ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧ F = Subgroup.zpowers x ⊔ centerOf P := by
  obtain ⟨x, hxF, hxB⟩ := Set.not_subset.1 hFB
  have hxP : x ∈ P := hF.1 hxF
  have hW9 : Nat.card ↥(centerOf P) = 9 := by
    rw [w.centerOf_eq hxP hxB]
    exact w.card_inf_centralizer hxP hxB
  obtain ⟨hCx, hCx27⟩ := w.inf_centralizer_P hxP hxB
  have hWF : centerOf P ≤ F := by
    intro z hz
    obtain ⟨hzP, hz'⟩ := Claims135.mem_centerOf_iff.1 hz
    exact hF.2.2.1 ⟨Subgroup.mem_centralizer_iff.2 fun f hf => hz' f (hF.1 hf), hzP⟩
  have hWZF : centerOf P ≤ centerOf F := fun z hz => Claims135.mem_centerOf_iff.2
    ⟨hWF hz, fun f hf => (Claims135.mem_centerOf_iff.1 hz).2 f (hF.1 hf)⟩
  have hZFC : centerOf F ≤ P ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    obtain ⟨hzF, hz'⟩ := Claims135.mem_centerOf_iff.1 hz
    exact ⟨hF.1 hzF, Subgroup.mem_centralizer_singleton_iff.2 (hz' x hxF).symm⟩
  have hZF27 : Nat.card ↥(centerOf F) = 27 := by
    have h1 : 9 ∣ Nat.card ↥(centerOf F) := hW9 ▸ Subgroup.card_dvd_of_le hWZF
    have h2 : Nat.card ↥(centerOf F) ∣ 3 ^ 3 := by
      have := Subgroup.card_dvd_of_le hZFC
      rwa [hCx27] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    interval_cases k
    · rw [hk'] at h1; norm_num at h1
    · rw [hk'] at h1; norm_num at h1
    · exact absurd (Subgroup.eq_of_le_of_card_ge hWZF (by rw [hk', hW9]; norm_num)).symm hZ
    · rw [hk']; norm_num
  have hZFeq : centerOf F = P ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hZFC (by rw [hCx27, hZF27])
  have hxZ : x ∈ centerOf F := by
    rw [hZFeq]
    exact ⟨hxP, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hFeq : F = P ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_antisymm (fun f hf => Subgroup.mem_inf.2 ⟨hF.1 hf, ?_⟩)
      (hZFeq ▸ Subgroup.map_subtype_le _)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Claims135.mem_centerOf_iff.1 hxZ).2 f hf
  refine ⟨x, hxF, hxB, hFeq, fun a ha b hb => ?_, hFeq.trans hCx⟩
  have ha' : a ∈ centerOf F := by rw [hZFeq, ← hFeq]; exact ha
  exact ((Claims135.mem_centerOf_iff.1 ha').2 b hb).symm

theorem Wreath.card_normalizer_ge {P B : Subgroup G} {d : G} (w : Wreath P B d) {x : G}
    (hxP : x ∈ P) (hxB : x ∉ B) {F : Subgroup G} (hFsup : F = Subgroup.zpowers x ⊔ centerOf P) :
    3 ^ 5 ≤ Nat.card ↥(P ⊓ Subgroup.normalizer (F : Set G)) := by
  have hcB := comm_of_isElemAbelian w.elem
  have hW := w.centerOf_eq hxP hxB
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := w.norm hxP
  have hx3B : x ^ 3 ∈ B := w.pow_three_mem hxP
  have hcj : ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun b hb => (Subgroup.mem_normalizer_iff.1 hxN b).1 hb
  let σ : ↥B →* ↥B := MonoidHom.mk'
    (fun b => ⟨x * b * x⁻¹, hcj b b.2⟩) (by
      intro a b
      apply Subtype.ext
      show x * ((a : G) * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
      group)
  have hσ : ∀ b : ↥B, ((σ b : ↥B) : G) = x * b * x⁻¹ := fun b => rfl
  let Nm : ↥B →* ↥B := MonoidHom.mk' (fun b => b * σ b * σ (σ b)) (by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]
    set A2 := ((σ a : ↥B) : G)
    set A3 := ((σ (σ a) : ↥B) : G)
    set B2 := ((σ b : ↥B) : G)
    set B3 := ((σ (σ b) : ↥B) : G)
    have c1 : (b : G) * A2 = A2 * b := hcB _ b.2 _ (σ a).2
    have c2 : (b : G) * A3 = A3 * b := hcB _ b.2 _ (σ (σ a)).2
    have c3 : B2 * A3 = A3 * B2 := hcB _ (σ b).2 _ (σ (σ a)).2
    calc (a : G) * b * (A2 * B2) * (A3 * B3) = a * (b * A2) * B2 * A3 * B3 := by group
      _ = a * (A2 * b) * B2 * A3 * B3 := by rw [c1]
      _ = a * A2 * b * (B2 * A3) * B3 := by group
      _ = a * A2 * b * (A3 * B2) * B3 := by rw [c3]
      _ = a * A2 * (b * A3) * B2 * B3 := by group
      _ = a * A2 * (A3 * b) * B2 * B3 := by rw [c2]
      _ = a * A2 * A3 * (b * B2 * B3) := by group)
  have hNm : ∀ b : ↥B, ((Nm b : ↥B) : G) =
      (b : G) * (x * b * x⁻¹) * (x * x * b * x⁻¹ * x⁻¹) := by
    intro b
    show (b : G) * (x * b * x⁻¹) * (x * (x * b * x⁻¹) * x⁻¹) = _
    group
  have hrange : Nat.card Nm.range ≤ 9 := by
    have hle : Nm.range.map B.subtype ≤ B ⊓ Subgroup.centralizer ({x} : Set G) := by
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      show ((Nm b : ↥B) : G) ∈ _
      rw [hNm]
      exact norm_mem w.elem hxN hx3B b.2
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective B.subtype_injective, w.card_inf_centralizer hxP hxB]
      at this
  have hker : 3 ^ 4 ≤ Nat.card Nm.ker := by
    have h := card_eq_card_ker_mul_card_range Nm
    rw [w.cardB] at h
    have hpos : 0 < Nat.card Nm.ker := Nat.card_pos
    nlinarith
  have hcomm : ∀ b : ↥B, Nm b = 1 → (b : G) * x * (b : G)⁻¹ * x⁻¹ ∈ centerOf P := by
    intro b hb
    rw [hW]
    have hb' : (b : G) * (x * b * x⁻¹) * (x * (x * b * x⁻¹) * x⁻¹) = 1 := by
      have h1 : ((Nm b : ↥B) : G) = 1 := by rw [hb]; rfl
      rw [hNm] at h1
      rw [← h1]
      group
    set y := x * (b : G) * x⁻¹ with hy
    have hyB : y ∈ B := hcj b b.2
    have hy3 : y ^ 3 = 1 := w.elem.2 y hyB
    have hz : x * y * x⁻¹ = ((b : G) * y)⁻¹ := eq_inv_of_mul_eq_one_right hb'
    have hyinv : y⁻¹ = y * y := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_three, hy3]
    have hyb : y * b = b * y := hcB _ hyB _ b.2
    have hcB' : (b : G) * x * (b : G)⁻¹ * x⁻¹ = (b : G) * y⁻¹ := by rw [hy]; group
    have hfix : x * ((b : G) * y⁻¹) * x⁻¹ = (b : G) * y⁻¹ := by
      calc x * ((b : G) * y⁻¹) * x⁻¹ = y * (x * y * x⁻¹)⁻¹ := by rw [hy]; group
        _ = y * ((b : G) * y) := by rw [hz, inv_inv]
        _ = (b : G) * y * y := by rw [← mul_assoc, hyb]
        _ = (b : G) * y⁻¹ := by rw [hyinv, mul_assoc]
    rw [hcB']
    refine Subgroup.mem_inf.2 ⟨B.mul_mem b.2 (B.inv_mem hyB), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (b : G) * y⁻¹ * x = x * ((b : G) * y⁻¹) * x⁻¹ * x := by rw [hfix]
      _ = x * ((b : G) * y⁻¹) := by group
  have hnormF : ∀ b : ↥B, Nm b = 1 → (b : G) ∈ Subgroup.normalizer (F : Set G) := by
    have hmap : ∀ b : ↥B, Nm b = 1 → F.map (MulAut.conj (b : G)).toMonoidHom ≤ F := by
      intro b hb
      have hc := hcomm b hb
      rw [hFsup, Subgroup.map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · rw [Subgroup.zpowers_le]
        show (b : G) * x * (b : G)⁻¹ ∈ _
        rw [show (b : G) * x * (b : G)⁻¹ = ((b : G) * x * (b : G)⁻¹ * x⁻¹) * x by group]
        exact Subgroup.mul_mem _ ((le_sup_right : centerOf P ≤ _) hc)
          ((le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x))
      · rintro _ ⟨v, hv, rfl⟩
        show (b : G) * v * (b : G)⁻¹ ∈ _
        have hvB : v ∈ B := by rw [hW] at hv; exact (Subgroup.mem_inf.1 hv).1
        rw [hcB _ b.2 v hvB, mul_inv_cancel_right]
        exact (le_sup_right : centerOf P ≤ _) hv
    intro b hb
    refine mem_normalizer_of_map_le (hmap b hb) ?_
    have hb1 : Nm b⁻¹ = 1 := by rw [map_inv, hb]; exact inv_one
    have := hmap b⁻¹ hb1
    simpa using this
  have hK : Nm.ker.map B.subtype ≤ P ⊓ Subgroup.normalizer (F : Set G) ⊓ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨w.le b.2, hnormF b hb⟩, b.2⟩
  have h81 : 3 ^ 4 ≤ Nat.card ↥(P ⊓ Subgroup.normalizer (F : Set G) ⊓ B) := by
    have := Subgroup.card_le_of_le hK
    rw [Subgroup.card_map_of_injective B.subtype_injective] at this
    omega
  have hxNF : x ∈ Subgroup.normalizer (F : Set G) := by
    have hxF : x ∈ F := by
      rw [hFsup]
      exact (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
    exact Subgroup.le_normalizer hxF
  rw [w.card_of_not_le inf_le_left (fun h => hxB (h (Subgroup.mem_inf.2 ⟨hxP, hxNF⟩)))]
  omega

theorem Wreath.false_of_alperin {P B : Subgroup G} {d : G} (w : Wreath P B d) {F : Subgroup G}
    (hF : CFSG.RankTwoShapes.IsAlperinSubgroup 3 P F) (hFB : ¬ F ≤ B)
    (hZ : centerOf F ≠ centerOf P) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcB := comm_of_isElemAbelian w.elem
  obtain ⟨x, hxF, hxB, hFeq, hFab, hFsup⟩ := w.alperin_shape hF hFB hZ
  have hxP : x ∈ P := hF.1 hxF
  set W := centerOf P with hWdef
  have hW : W = B ⊓ Subgroup.centralizer ({x} : Set G) := w.centerOf_eq hxP hxB
  have hW9 : Nat.card ↥W = 9 := by rw [hW]; exact w.card_inf_centralizer hxP hxB
  have hWB : W ≤ B := hW ▸ inf_le_left
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => hcB a (hWB ha) b (hWB hb)
  have hWF : W ≤ F := by rw [hFsup]; exact le_sup_right
  have hF27 : Nat.card ↥F = 27 := by rw [hFeq]; exact (w.inf_centralizer_P hxP hxB).2
  have hFC : F ≤ Subgroup.centralizer (F : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hFab b hb a ha
  have hFBW : F ⊓ B ≤ W := by
    intro y hy
    obtain ⟨hyF, hyB⟩ := Subgroup.mem_inf.1 hy
    rw [hW]
    exact Subgroup.mem_inf.2 ⟨hyB, Subgroup.mem_centralizer_singleton_iff.2 (hFab y hyF x hxF)⟩
  have hx3 : x ^ 3 ∈ W := by
    rw [hW]
    exact Subgroup.mem_inf.2 ⟨w.pow_three_mem hxP,
      Subgroup.mem_centralizer_singleton_iff.2 (by group)⟩
  set Y := transv F W x with hYdef
  set φ := transvHom (F := F) (x := x) hWc with hφdef
  have hYcard := card_transv hFab hxF hWF hFsup hWc
  have hφW : φ.range ≤ W := by rintro _ ⟨y, rfl⟩; exact transvHom_mem hWc y
  have hφ9 : Nat.card φ.range ≤ 9 := hW9 ▸ Subgroup.card_le_of_le hφW
  have hYN : Y ≤ Subgroup.normalizer (F : Set G) := fun y hy => hy.1
  have hNPFY : P ⊓ Subgroup.normalizer (F : Set G) ≤ Y := by
    intro y hy
    obtain ⟨hyP, hyN⟩ := Subgroup.mem_inf.1 hy
    refine ⟨hyN, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Claims135.mem_centerOf_iff.1 hz).2 y hyP).symm
    · apply hFBW
      have h1 : y * x * y⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 hyN x).1 hxF
      exact Subgroup.mem_inf.2 ⟨F.mul_mem h1 (F.inv_mem hxF), w.commutator_mem hyP hxP⟩
  let ψ : ↥(P ⊓ Subgroup.normalizer (F : Set G)) →* G := φ.comp (Subgroup.inclusion hNPFY)
  have hψker : Nat.card ψ.ker = 27 := by
    rw [← hF27]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun f => ⟨⟨f.1, Subgroup.mem_inf.2 ⟨hF.1 f.2, Subgroup.le_normalizer f.2⟩⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun f => rfl }
    · have h1 : (y.1 : G) * x * (y.1 : G)⁻¹ * x⁻¹ = 1 := y.2
      refine hFeq.ge (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 y.1.2).1,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩)
      calc (y.1 : G) * x = ((y.1 : G) * x * (y.1 : G)⁻¹ * x⁻¹) * x * y.1 := by group
        _ = x * y.1 := by rw [h1, one_mul]
    · rw [MonoidHom.mem_ker]
      show (f : G) * x * (f : G)⁻¹ * x⁻¹ = 1
      rw [hFab f f.2 x hxF]
      group
  have hψrange : ψ.range ≤ φ.range := by rintro _ ⟨y, rfl⟩; exact ⟨_, rfl⟩
  have hNPF : Nat.card ↥(P ⊓ Subgroup.normalizer (F : Set G)) = 27 * Nat.card ψ.range := by
    rw [card_eq_card_ker_mul_card_range ψ, hψker]
  have hge := w.card_normalizer_ge hxP hxB hFsup
  have hψ9 : 9 ≤ Nat.card ψ.range := by rw [hNPF] at hge; omega
  have hφ9' : Nat.card φ.range = 9 := le_antisymm hφ9 (hψ9.trans (Subgroup.card_le_of_le hψrange))
  have hφeq : φ.range = W := Subgroup.eq_of_le_of_card_ge hφW (by rw [hW9, hφ9'])
  have hNPF243 : Nat.card ↥(P ⊓ Subgroup.normalizer (F : Set G)) = 3 ^ 5 := by
    have h2 := Subgroup.card_le_of_le hψrange
    rw [hφ9'] at h2
    rw [hNPF] at hge ⊢
    omega
  have hYcard' : Nat.card ↥Y = Nat.card ↥(Subgroup.centralizer (F : Set G)) * 9 := by
    rw [hYcard, hφ9']
  have h27 : 27 ∣ Nat.card ↥(Subgroup.centralizer (F : Set G)) :=
    hF27 ▸ Subgroup.card_dvd_of_le hFC
  have hnot : ¬ 3 ^ 6 ∣ Nat.card ↥(Subgroup.normalizer (F : Set G)) := by
    intro h6
    have hidx := hF.2.1
    have hmul := Subgroup.card_mul_index ((P ⊓ Subgroup.normalizer (F : Set G)).subgroupOf
      (Subgroup.normalizer (F : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hNPF243] at hmul
    rw [← hmul, show 3 ^ 6 = 3 ^ 5 * 3 by norm_num] at h6
    have h3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h6
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hidx h3
  have hWnorm : ∀ g ∈ Subgroup.normalizer (F : Set G), ∀ v ∈ W, g * v * g⁻¹ ∈ W := by
    intro g hg
    by_contra hcon
    push Not at hcon
    obtain ⟨v₀, hv₀W, hv₀⟩ := hcon
    set W' := W.map (MulAut.conj g).toMonoidHom with hW'def
    have hmemW' : ∀ z, z ∈ W' ↔ g⁻¹ * z * g ∈ W := fun z => mem_conj_map_iff g W z
    have hgi : g⁻¹ ∈ Subgroup.normalizer (F : Set G) := Subgroup.inv_mem _ hg
    have hW'F : W' ≤ F := by
      intro z hz
      rw [hmemW'] at hz
      have := (Subgroup.mem_normalizer_iff.1 hg _).1 (hWF hz)
      simpa [mul_assoc] using this
    have hW'9 : Nat.card ↥W' = 9 := by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hW9]
    have hWW' : ¬ W ≤ W' := by
      intro hle
      have heq : W = W' := Subgroup.eq_of_le_of_card_ge hle (by rw [hW'9, hW9])
      have : g * v₀ * g⁻¹ ∈ W' := ⟨v₀, hv₀W, rfl⟩
      rw [← heq] at this
      exact hv₀ this
    obtain ⟨w₁, hw₁W, hw₁W'⟩ := Set.not_subset.1 hWW'
    have hl : W ⊓ W' ≠ ⊥ := by
      intro hbot
      have hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a := fun a ha b hb =>
        hFab a (hWF ha) b (hW'F hb)
      have h1 := card_sup_of_commute hc hbot
      have h2 := Subgroup.card_le_of_le (sup_le hWF hW'F)
      rw [h1, hW9, hW'9, hF27] at h2
      norm_num at h2
    obtain ⟨⟨l, hlWW'⟩, hl1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hl
    have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
    obtain ⟨hlW, hlW'⟩ := Subgroup.mem_inf.1 hlWW'
    have hl' : g⁻¹ * l * g ∈ W := (hmemW' l).1 hlW'
    have hl3 : l ^ 3 = 1 := w.elem.2 l (hWB hlW)
    have hlo : orderOf l = 3 := orderOf_eq_prime hl3 hl1'
    obtain ⟨⟨y, hyY⟩, hyl⟩ : g⁻¹ * l * g ∈ φ.range := by rw [hφeq]; exact hl'
    have hyx : y * x * y⁻¹ * x⁻¹ = g⁻¹ * l * g := hyl
    obtain ⟨u, hu⟩ : ∃ u : G, u = g * y * g⁻¹ := ⟨_, rfl⟩
    have huF : u ∈ Subgroup.normalizer (F : Set G) := by
      rw [hu]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hyY.1) hgi
    have hconjl : ∀ k : ℤ, g * (g⁻¹ * l * g) ^ k * g⁻¹ = l ^ k := by
      intro k
      rw [show g⁻¹ * l * g = g⁻¹ * l * g⁻¹⁻¹ by rw [inv_inv], conj_zpow]
      group
    have hul : ∀ f ∈ F, ∃ k : ℤ, u * f * u⁻¹ = l ^ k * f := by
      intro f hf
      have hf' : g⁻¹ * f * g ∈ F := by
        have := (Subgroup.mem_normalizer_iff.1 hgi f).1 hf
        simpa using this
      obtain ⟨k, hk⟩ := transv_formula hFab hxF hWF hFsup hyY hf'
      refine ⟨k, ?_⟩
      have e : u * f * u⁻¹ * f⁻¹ = g * (y * (g⁻¹ * f * g) * y⁻¹ * (g⁻¹ * f * g)⁻¹) * g⁻¹ := by
        rw [hu]; group
      rw [hk, hyx, hconjl] at e
      calc u * f * u⁻¹ = u * f * u⁻¹ * f⁻¹ * f := by group
        _ = l ^ k * f := by rw [e]
    have huW' : ∀ v ∈ W', u * v * u⁻¹ = v := by
      intro v hv
      have h1 := Subgroup.mem_centralizer_iff.1 hyY.2.1 _ ((hmemW' v).1 hv)
      calc u * v * u⁻¹ = g * (y * (g⁻¹ * v * g) * y⁻¹) * g⁻¹ := by rw [hu]; group
        _ = g * ((g⁻¹ * v * g) * y * y⁻¹) * g⁻¹ := by rw [← h1]
        _ = v := by group
    have hulk : ∀ k : ℤ, u * l ^ k * u⁻¹ = l ^ k := by
      intro k
      rw [← conj_zpow, huW' l hlW']
    have hu3 : u ^ 3 ∈ Y := by
      apply centralizer_le_transv hFab hxF hWF hFsup
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      obtain ⟨k, hk⟩ := hul f hf
      have h2 : u * (l ^ k * f) * u⁻¹ = l ^ k * (l ^ k * f) := by
        calc u * (l ^ k * f) * u⁻¹ = (u * l ^ k * u⁻¹) * (u * f * u⁻¹) := by group
          _ = l ^ k * (l ^ k * f) := by rw [hulk, hk]
      have h3 : u * (l ^ k * (l ^ k * f)) * u⁻¹ = l ^ k * (l ^ k * (l ^ k * f)) := by
        calc u * (l ^ k * (l ^ k * f)) * u⁻¹ =
            (u * l ^ k * u⁻¹) * ((u * l ^ k * u⁻¹) * (u * f * u⁻¹)) := by group
          _ = l ^ k * (l ^ k * (l ^ k * f)) := by rw [hulk, hk]
      have hl3k : l ^ k * (l ^ k * (l ^ k * f)) = f := by
        rw [← mul_assoc, ← mul_assoc, ← zpow_add, ← zpow_add,
          show k + k + k = 3 * k by ring, zpow_mul]
        rw [show l ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; exact hl3, one_zpow, one_mul]
      have h4 : u ^ 3 * f * (u ^ 3)⁻¹ = f := by
        calc u ^ 3 * f * (u ^ 3)⁻¹ = u * (u * (u * f * u⁻¹) * u⁻¹) * u⁻¹ := by
              rw [pow_three]; group
          _ = f := by rw [hk, h2, h3, hl3k]
      calc f * u ^ 3 = u ^ 3 * f * (u ^ 3)⁻¹ * u ^ 3 := by rw [h4]
        _ = u ^ 3 * f := by group
    have huW : ∀ v ∈ W, u * v * u⁻¹ ∈ W := by
      intro v hv
      obtain ⟨k, hk⟩ := hul v (hWF hv)
      rw [hk]
      exact W.mul_mem (W.zpow_mem hlW k) hv
    have huW'' : ∀ v ∈ W, u⁻¹ * v * u ∈ W := by
      intro v hv
      have hv' : u⁻¹ * v * u ∈ F := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ huF) v).1 (hWF hv)
        simpa using this
      obtain ⟨k, hk⟩ := hul _ hv'
      have e : u * (u⁻¹ * v * u) * u⁻¹ = v := by group
      rw [e] at hk
      have : u⁻¹ * v * u = (l ^ k)⁻¹ * v := by
        calc u⁻¹ * v * u = (l ^ k)⁻¹ * (l ^ k * (u⁻¹ * v * u)) := by group
          _ = (l ^ k)⁻¹ * v := by rw [← hk]
      rw [this]
      exact W.mul_mem (W.inv_mem (W.zpow_mem hlW k)) hv
    have huY : u ∉ Y := by
      intro huY'
      have hc := Subgroup.mem_centralizer_iff.1 huY'.2.1 w₁ hw₁W
      have hw₁' : g⁻¹ * w₁ * g ∈ F := by
        have := (Subgroup.mem_normalizer_iff.1 hgi w₁).1 (hWF hw₁W)
        simpa using this
      obtain ⟨k, v, hv, hkv⟩ := exists_zpow_mul hFab hxF hWF hFsup hw₁'
      have hform := transv_formula' hFab hxF hWF hFsup hyY k hv
      rw [← hkv, hyx] at hform
      have e : u * w₁ * u⁻¹ * w₁⁻¹ = l ^ k := by
        rw [← hconjl k, ← hform, hu]
        group
      have h1 : l ^ k = 1 := by
        rw [← e]
        calc u * w₁ * u⁻¹ * w₁⁻¹ = (w₁ * u) * u⁻¹ * w₁⁻¹ := by rw [hc]
          _ = 1 := by group
      have h3k : (3 : ℤ) ∣ k := by
        have := (orderOf_dvd_iff_zpow_eq_one).2 h1
        rwa [hlo] at this
      obtain ⟨j, rfl⟩ := h3k
      have hxk : x ^ (3 * j) ∈ W := by
        rw [zpow_mul]
        exact W.zpow_mem (by rw [zpow_ofNat]; exact hx3) j
      apply hw₁W'
      rw [SetLike.mem_coe, hmemW', hkv]
      exact W.mul_mem hxk hv
    have hnY : ∀ z : G, z ∈ Subgroup.normalizer (F : Set G) → (∀ v ∈ W, z * v * z⁻¹ ∈ W) →
        (∀ v ∈ W, z⁻¹ * v * z ∈ W) → z ∈ Subgroup.normalizer (Y : Set G) := by
      intro z hzF hz1 hz2
      rw [Subgroup.mem_normalizer_iff]
      intro y'
      constructor
      · exact conj_mem_transv hFab hxF hWF hFsup hzF hz1 hz2
      · intro hy'
        have := conj_mem_transv hFab hxF hWF hFsup (Subgroup.inv_mem _ hzF)
          (fun v hv => by simpa using hz2 v hv) (fun v hv => by simpa using hz1 v hv) hy'
        simpa [mul_assoc] using this
    have huN : u ∈ Subgroup.normalizer (Y : Set G) := hnY u huF huW huW''
    set Z := Y ⊔ Subgroup.zpowers u with hZdef
    have hZN : Z ≤ Subgroup.normalizer (Y : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 huN)
    haveI : (Y.subgroupOf Z).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hZN
    have huZ : u ∈ Z := (le_sup_right : Subgroup.zpowers u ≤ Z) (Subgroup.mem_zpowers u)
    set ū := QuotientGroup.mk' (Y.subgroupOf Z) ⟨u, huZ⟩ with hū
    have hū3 : ū ^ 3 = 1 := by
      rw [hū, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu3)
    have hū1 : ū ≠ 1 := by
      intro h1
      exact huY (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1))
    have h3 : 3 ∣ Nat.card (↥Z ⧸ Y.subgroupOf Z) :=
      orderOf_eq_prime hū3 hū1 ▸ orderOf_dvd_natCard ū
    have hZcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf Z)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hYcard'] at hZcard
    have h729 : 3 ^ 6 ∣ Nat.card ↥Z := by
      rw [hZcard, show 3 ^ 6 = 3 * (27 * 9) by norm_num]
      exact Nat.mul_dvd_mul h3 (Nat.mul_dvd_mul_right h27 9)
    exact hnot (h729.trans (Subgroup.card_dvd_of_le
      (sup_le hYN (Subgroup.zpowers_le.2 huF))))
  have hYn : Subgroup.normalizer (F : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    have hgi : g⁻¹ ∈ Subgroup.normalizer (F : Set G) := Subgroup.inv_mem _ hg
    have h1 : ∀ v ∈ W, g⁻¹ * v * g ∈ W := fun v hv => by simpa using hWnorm g⁻¹ hgi v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    constructor
    · exact conj_mem_transv hFab hxF hWF hFsup hg (hWnorm g hg) h1
    · intro hy'
      have := conj_mem_transv hFab hxF hWF hFsup hgi (fun v hv => by simpa using hWnorm g⁻¹ hgi v hv)
        (fun v hv => by simpa using hWnorm g hg v hv) hy'
      simpa [mul_assoc] using this
  have hFCF : F ⊔ Subgroup.centralizer (F : Set G) = Subgroup.centralizer (F : Set G) :=
    sup_eq_right.2 hFC
  have hCY : F ⊔ Subgroup.centralizer (F : Set G) ≤ Y :=
    hFCF.le.trans (centralizer_le_transv hFab hxF hWF hFsup)
  have hidx : ((F ⊔ Subgroup.centralizer (F : Set G)).subgroupOf Y).index = 3 ^ 2 := by
    have hmul := Subgroup.card_mul_index ((F ⊔ Subgroup.centralizer (F : Set G)).subgroupOf Y)
    have hcardFC : Nat.card ↥(F ⊔ Subgroup.centralizer (F : Set G)) =
        Nat.card ↥(Subgroup.centralizer (F : Set G)) := by rw [hFCF]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv, hcardFC, hYcard'] at hmul
    have hpos : 0 < Nat.card ↥(Subgroup.centralizer (F : Set G)) := Nat.card_pos
    have : ((F ⊔ Subgroup.centralizer (F : Set G)).subgroupOf Y).index = 9 :=
      Nat.eq_of_mul_eq_mul_left hpos hmul
    rw [this]
    norm_num
  have hrad := hF.2.2.2 Y hCY hYN hYn ⟨2, hidx⟩
  rw [hFCF] at hrad
  have hc : Nat.card ↥Y = Nat.card ↥(Subgroup.centralizer (F : Set G)) := by rw [hrad]
  rw [hYcard'] at hc
  have hpos : 0 < Nat.card ↥(Subgroup.centralizer (F : Set G)) := Nat.card_pos
  omega

end FamilyCore

theorem familyCoreInput_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement) :
    Claims135.FamilyCoreInput := by
  intro G _ _ m B M E A D T L h hcent P hPM hBDP _ F hF hFB hZ
  obtain ⟨d, -, w, -⟩ := wreath_of_cex hP95 h111 h121 hcomp h133 h hcent hPM hBDP
  exact (w.false_of_alperin hF hFB hZ).elim

section Centralizer

variable {G : Type} [Group G] [Finite G]

@[expose] def CentralizerGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
    ∀ Q P₁ B₀ : Subgroup G, IsElemAbelian 3 Q → Nat.card ↥Q = 9 →
      Subgroup.centralizer (Q : Set G) ≠ ⊤ →
      IsSylowIn 3 (Subgroup.centralizer (Q : Set G)) P₁ →
      (∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a) → Nat.card ↥P₁ = 27 →
      B₀ ≤ Subgroup.normalizer (Q : Set G) → IsElemAbelian 3 B₀ → Nat.card ↥B₀ = 27 →
      Subgroup.centralizer (Q : Set G) ≤ Subgroup.normalizer (P₁ : Set G) ⊔
        ⨆ (E : Subgroup G) (_ : E ≤ B₀ ∧ Nat.card ↥E = 9), Subgroup.centralizer (E : Set G)

theorem Wreath.inf_centralizer_plane {P B : Subgroup G} {d : G} (w : Wreath P B d)
    {Q : Subgroup G} (hQP : Q ≤ P) (hQe : IsElemAbelian 3 Q) {q : G} (hqQ : q ∈ Q)
    (hqB : q ∉ B) :
    P ⊓ Subgroup.centralizer (Q : Set G) = P ⊓ Subgroup.centralizer ({q} : Set G) := by
  have hqP := hQP hqQ
  obtain ⟨hCx, -⟩ := w.inf_centralizer_P hqP hqB
  apply le_antisymm
  · intro y hy
    obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨hyP, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hyC q hqQ).symm⟩
  · rw [hCx]
    refine le_inf (sup_le (Subgroup.zpowers_le.2 hqP) (Subgroup.map_subtype_le _)) ?_
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · exact Subgroup.mem_centralizer_iff.2 fun y hy => comm_of_isElemAbelian hQe y hy q hqQ
    · intro z hz
      exact Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Claims135.mem_centerOf_iff.1 hz).2 y (hQP hy)

theorem strong_closure {P B M : Subgroup G}
    (hfus : ∀ X : Subgroup G, X ≤ P → ∀ g : G, GLBConj g X ≤ P →
      ∃ c ∈ Subgroup.centralizer (X : Set G), ∃ k ∈ M, g = c * k)
    (hcl : ∀ b ∈ B, ∀ g ∈ M, g * b * g⁻¹ ∈ P → g * b * g⁻¹ ∈ B) (hBP : B ≤ P)
    {b : G} (hb : b ∈ B) {g : G} (hg : g⁻¹ * b * g ∈ P) : g⁻¹ * b * g ∈ B := by
  have hX : Subgroup.zpowers b ≤ P := Subgroup.zpowers_le.2 (hBP hb)
  have hXg : GLBConj g (Subgroup.zpowers b) ≤ P := by
    unfold GLBConj
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hg
  obtain ⟨c, hc, k, hk, rfl⟩ := hfus _ hX g hXg
  have hcb : c⁻¹ * b * c = b := by
    have := Subgroup.mem_centralizer_iff.1 hc b (Subgroup.mem_zpowers b)
    calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = c⁻¹ * (c * b) := by rw [this]
      _ = b := by group
  have e : (c * k)⁻¹ * b * (c * k) = k⁻¹ * b * k⁻¹⁻¹ := by
    rw [show (c * k)⁻¹ * b * (c * k) = k⁻¹ * (c⁻¹ * b * c) * k by group, hcb, inv_inv]
  rw [e] at hg ⊢
  exact hcl b hb k⁻¹ (M.inv_mem hk) hg

theorem Wreath.sylow_centralizer_plane {P B : Subgroup G} {d : G} (w : Wreath P B d)
    (hPS : IsSylowIn 3 ⊤ P) (hsc : ∀ b ∈ B, ∀ g : G, g⁻¹ * b * g ∈ P → g⁻¹ * b * g ∈ B)
    {Q : Subgroup G} (hQP : Q ≤ P) (hQe : IsElemAbelian 3 Q) (hQB : ¬ Q ≤ B) :
    IsSylowIn 3 (Subgroup.centralizer (Q : Set G)) (P ⊓ Subgroup.centralizer (Q : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ∀ {Q' : Subgroup G}, Q' ≤ P → IsElemAbelian 3 Q' → ¬ Q' ≤ B →
      Nat.card ↥(P ⊓ Subgroup.centralizer (Q' : Set G)) = 27 := by
    intro Q' hQ'P hQ'e hQ'B
    obtain ⟨q, hqQ, hqB⟩ := Set.not_subset.1 hQ'B
    rw [w.inf_centralizer_plane hQ'P hQ'e hqQ hqB]
    exact (w.inf_centralizer_P (hQ'P hqQ) hqB).2
  refine ⟨inf_le_right, hPS.2.1.to_le inf_le_left, fun R hRC hRp hP₁R => ?_⟩
  let PS : Sylow 3 G := ⟨P, hPS.2.1, fun {R} hR hPR => hPS.2.2 R le_top hR hPR⟩
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS S
  have hSP : (S : Subgroup G) = GLBConj g⁻¹ P := by
    rw [← hg]
    unfold GLBConj
    rw [inv_inv]
    rfl
  have hmemS : ∀ y ∈ R, g⁻¹ * y * g ∈ P := by
    intro y hy
    have := hRS hy
    rw [hSP, mem_gLBConj] at this
    simpa using this
  have hQR : Q ≤ R := le_trans (fun y hy => Subgroup.mem_inf.2 ⟨hQP hy,
    Subgroup.mem_centralizer_iff.2 fun z hz => comm_of_isElemAbelian hQe z hz y hy⟩) hP₁R
  set Q' := GLBConj g Q with hQ'
  have hmemQ' : ∀ y, y ∈ Q' ↔ g * y * g⁻¹ ∈ Q := fun y => mem_gLBConj
  have hQ'P : Q' ≤ P := by
    intro y hy
    have := hmemS _ (hQR ((hmemQ' y).1 hy))
    simpa [mul_assoc] using this
  have hQ'e : IsElemAbelian 3 Q' := by
    have := CFSG.LocalAnalysis.GLTheoremB.MovingAround.isElemAbelian_map
      (MulAut.conj g⁻¹).toMonoidHom hQe
    exact this
  have hQ'B : ¬ Q' ≤ B := by
    intro hle
    apply hQB
    intro y hy
    have h1 : g⁻¹ * y * g ∈ B := hle ((hmemQ' _).2 (by simpa [mul_assoc] using hy))
    have h2 := hsc _ h1 g⁻¹ (by simpa [mul_assoc] using hQP hy)
    simpa [mul_assoc] using h2
  have hR' : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ P ⊓ Subgroup.centralizer (Q' : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨by simpa using hmemS y hy, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' := (hmemQ' z).1 hz
    have hc := Subgroup.mem_centralizer_iff.1 (hRC hy) _ hz'
    show z * (g⁻¹ * y * g⁻¹⁻¹) = (g⁻¹ * y * g⁻¹⁻¹) * z
    calc z * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * y * g⁻¹⁻¹) * z := by group
  have hRle : Nat.card ↥R ≤ 27 := by
    have := Subgroup.card_le_of_le hR'
    rwa [Subgroup.card_map_of_injective (MulEquiv.injective _), hcard hQ'P hQ'e hQ'B] at this
  exact (Subgroup.eq_of_le_of_card_ge hP₁R (by rw [hcard hQP hQe hQB]; exact hRle)).symm

theorem Wreath.exists_B0 {P B : Subgroup G} {d : G} (w : Wreath P B d) {Q : Subgroup G}
    (hQP : Q ≤ P) (hQe : IsElemAbelian 3 Q) (hQc : Nat.card ↥Q = 9) (hQB : ¬ Q ≤ B) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ B₀ ≤ Subgroup.normalizer (Q : Set G) ∧ Nat.card ↥B₀ = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcB := comm_of_isElemAbelian w.elem
  obtain ⟨q, hqQ, hqB⟩ := Set.not_subset.1 hQB
  have hqP := hQP hqQ
  set Z := centerOf P with hZdef
  have hZ : Z = B ⊓ Subgroup.centralizer ({q} : Set G) := w.centerOf_eq hqP hqB
  have hZ9 : Nat.card ↥Z = 9 := by rw [hZ]; exact w.card_inf_centralizer hqP hqB
  have hZB : Z ≤ B := hZ ▸ inf_le_left
  obtain ⟨hCq, -⟩ := w.inf_centralizer_P hqP hqB
  have hqN : q ∈ Subgroup.normalizer (B : Set G) := w.norm hqP
  set F₁ := Subgroup.zpowers q ⊔ Z with hF₁
  have hqF : q ∈ F₁ := (le_sup_left : Subgroup.zpowers q ≤ F₁) (Subgroup.mem_zpowers q)
  have hge := w.card_normalizer_ge hqP hqB (F := F₁) rfl
  have hqNF : q ∈ P ⊓ Subgroup.normalizer (F₁ : Set G) :=
    Subgroup.mem_inf.2 ⟨hqP, Subgroup.le_normalizer hqF⟩
  have h81 : 3 ^ 4 ≤ Nat.card ↥(P ⊓ Subgroup.normalizer (F₁ : Set G) ⊓ B) := by
    rw [w.card_of_not_le inf_le_left (fun h => hqB (h hqNF))] at hge
    omega
  set N₁ := P ⊓ Subgroup.normalizer (F₁ : Set G) ⊓ B with hN₁
  have hcm : ∀ b ∈ B, b * q * b⁻¹ * q⁻¹ ∈ B := by
    intro b hb
    rw [show b * q * b⁻¹ * q⁻¹ = b * (q * b⁻¹ * q⁻¹) by group]
    exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.1 hqN _).1 (B.inv_mem hb))
  let cq : ↥N₁ →* G := MonoidHom.mk' (fun b => (b : G) * q * (b : G)⁻¹ * q⁻¹) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have haB : a ∈ B := (Subgroup.mem_inf.1 ha).2
    have hbB : b ∈ B := (Subgroup.mem_inf.1 hb).2
    show a * b * q * (a * b)⁻¹ * q⁻¹ = a * q * a⁻¹ * q⁻¹ * (b * q * b⁻¹ * q⁻¹)
    have h1 := hcB a haB _ (hcm b hbB)
    calc a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹ * q⁻¹)) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) := by group
      _ = (b * q * b⁻¹ * q⁻¹) * (a * q * a⁻¹ * q⁻¹) := by rw [h1]; group
      _ = a * q * a⁻¹ * q⁻¹ * (b * q * b⁻¹ * q⁻¹) := hcB _ (hcm b hbB) _ (hcm a haB))
  have hcqZ : cq.range ≤ Z := by
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨⟨-, hbN⟩, hbB⟩ := Subgroup.mem_inf.1 hb
    have h1 : b * q * b⁻¹ * q⁻¹ ∈ F₁ :=
      F₁.mul_mem ((Subgroup.mem_normalizer_iff.1 hbN q).1 hqF) (F₁.inv_mem hqF)
    have h2 : b * q * b⁻¹ * q⁻¹ ∈ P ⊓ Subgroup.centralizer ({q} : Set G) := by
      rw [hCq]
      exact h1
    show b * q * b⁻¹ * q⁻¹ ∈ Z
    rw [hZ]
    exact Subgroup.mem_inf.2 ⟨hcm b hbB, (Subgroup.mem_inf.1 h2).2⟩
  have hker : Nat.card cq.ker ≤ 9 := by
    rw [← hZ9]
    refine Nat.card_le_card_of_injective (fun b => ⟨b.1.1, ?_⟩) (fun a b h => ?_)
    · have h1 : (b.1 : G) * q * (b.1 : G)⁻¹ * q⁻¹ = 1 := b.2
      rw [hZ]
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 b.1.2).2,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (b.1 : G) * q = ((b.1 : G) * q * (b.1 : G)⁻¹ * q⁻¹) * q * b.1 := by group
        _ = q * b.1 := by rw [h1, one_mul]
    · have h' : ((a : ↥N₁) : G) = ((b : ↥N₁) : G) := congrArg (fun x : ↥Z => (x : G)) h
      exact Subtype.ext (Subtype.ext h')
  have hrange : cq.range = Z := by
    refine Subgroup.eq_of_le_of_card_ge hcqZ ?_
    have h := card_eq_card_ker_mul_card_range cq
    rw [hZ9]
    have hpos : 0 < Nat.card cq.ker := Nat.card_pos
    nlinarith
  have hQB3 : Nat.card ↥(Q ⊓ B) = 3 := by
    have := w.card_of_not_le hQP hQB
    omega
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Q ⊓ B)).1
    (fun h => by rw [h, Subgroup.card_bot] at hQB3; norm_num at hQB3)
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext (by simpa using h))
  obtain ⟨hz₀Q, hz₀B⟩ := Subgroup.mem_inf.1 hz₀
  have hz₀Z : z₀ ∈ Z := by
    rw [hZ]
    exact Subgroup.mem_inf.2 ⟨hz₀B, Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_isElemAbelian hQe z₀ hz₀Q q hqQ)⟩
  obtain ⟨⟨b, hbN⟩, hbz⟩ : z₀ ∈ cq.range := by rw [hrange]; exact hz₀Z
  have hbz' : b * q * b⁻¹ * q⁻¹ = z₀ := hbz
  have hbB : b ∈ B := (Subgroup.mem_inf.1 hbN).2
  have hbZ : b ∉ Z := by
    intro hbZ
    rw [hZ] at hbZ
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hbZ).2
    apply hz₀1'
    rw [← hbz', hc]
    group
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Z.one_mem)
  have hbo : orderOf b = 3 := orderOf_eq_prime (w.elem.2 b hbB) hb1
  refine ⟨Z ⊔ Subgroup.zpowers b, sup_le hZB (Subgroup.zpowers_le.2 hbB), ?_, ?_⟩
  ·
    have hQeq : Q = Subgroup.zpowers q ⊔ Q ⊓ B := by
      have hle : Subgroup.zpowers q ⊔ Q ⊓ B ≤ Q := sup_le (Subgroup.zpowers_le.2 hqQ) inf_le_left
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      have hq' : q ∈ Subgroup.zpowers q ⊔ Q ⊓ B :=
        (le_sup_left : Subgroup.zpowers q ≤ _) (Subgroup.mem_zpowers q)
      rw [w.card_of_not_le (hle.trans hQP) (fun h => hqB (h hq')), hQc]
      have : Q ⊓ B ≤ (Subgroup.zpowers q ⊔ Q ⊓ B) ⊓ B :=
        le_inf le_sup_right inf_le_right
      have := Subgroup.card_le_of_le this
      omega
    have hmapb : ∀ y : G, y ∈ B → y * q * y⁻¹ * q⁻¹ ∈ Q →
        Q.map (MulAut.conj y).toMonoidHom ≤ Q := by
      intro y hyB hyq
      conv_lhs => rw [hQeq]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · rw [Subgroup.zpowers_le]
        show y * q * y⁻¹ ∈ Q
        rw [show y * q * y⁻¹ = (y * q * y⁻¹ * q⁻¹) * q by group]
        exact Q.mul_mem hyq hqQ
      · rintro _ ⟨v, hv, rfl⟩
        obtain ⟨hvQ, hvB⟩ := Subgroup.mem_inf.1 hv
        show y * v * y⁻¹ ∈ Q
        rw [hcB y hyB v hvB, mul_inv_cancel_right]
        exact hvQ
    have hbN' : b ∈ Subgroup.normalizer (Q : Set G) := by
      refine mem_normalizer_of_map_le (hmapb b hbB (hbz' ▸ hz₀Q)) (hmapb b⁻¹ (B.inv_mem hbB) ?_)
      have e : b⁻¹ * q * b⁻¹⁻¹ * q⁻¹ = z₀⁻¹ := by
        have hzc : z₀⁻¹ * b = b * z₀⁻¹ := hcB _ (B.inv_mem hz₀B) _ hbB
        calc b⁻¹ * q * b⁻¹⁻¹ * q⁻¹ = b⁻¹ * (b * q * b⁻¹ * q⁻¹)⁻¹ * b := by group
          _ = b⁻¹ * (z₀⁻¹ * b) := by rw [hbz', mul_assoc]
          _ = z₀⁻¹ := by rw [hzc]; group
      rw [e]
      exact Q.inv_mem hz₀Q
    refine sup_le ?_ (Subgroup.zpowers_le.2 hbN')
    intro z hz
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    exact (Claims135.mem_centerOf_iff.1 hz).2 y (hQP hy)
  ·
    have hi : Z ⊓ Subgroup.zpowers b = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro y ⟨hyZ, hyb⟩
      by_contra hy1
      apply hbZ
      have hyy : Subgroup.zpowers y = Subgroup.zpowers b := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyb)
        rw [Nat.card_zpowers, Nat.card_zpowers, hbo,
          orderOf_eq_prime (w.elem.2 y (hZB hyZ)) hy1]
      have : b ∈ Subgroup.zpowers y := hyy ▸ Subgroup.mem_zpowers b
      exact (Subgroup.zpowers_le.2 hyZ) this
    have hc : ∀ a ∈ Z, ∀ c ∈ Subgroup.zpowers b, a * c = c * a := fun a ha c hc =>
      hcB a (hZB ha) c ((Subgroup.zpowers_le.2 hbB) hc)
    rw [card_sup_of_commute hc hi, hZ9, Nat.card_zpowers, hbo]

theorem centralizerInput_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    (hgen : CentralizerGenInput) : Claims135.CentralizerInput := by
  intro G _ _ m B M E A D T L h hcent P hPM hBDP hPS hfus Q hQP hQe hQc hQB
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, -, w, hcl⟩ := wreath_of_cex hP95 h111 h121 hcomp h133 h hcent hPM hBDP
  have hsc : ∀ b ∈ B, ∀ g : G, g⁻¹ * b * g ∈ P → g⁻¹ * b * g ∈ B :=
    fun b hb g hg => strong_closure hfus hcl w.le hb hg
  obtain ⟨q, hqQ, hqB⟩ := Set.not_subset.1 hQB
  have hqP := hQP hqQ
  have hP₁eq := w.inf_centralizer_plane hQP hQe hqQ hqB
  obtain ⟨hCq, hCq27⟩ := w.inf_centralizer_P hqP hqB
  have hZ := w.centerOf_eq hqP hqB
  have hZB : centerOf P ≤ B := hZ ▸ inf_le_left
  have hP₁27 : Nat.card ↥(P ⊓ Subgroup.centralizer (Q : Set G)) = 27 := by
    rw [hP₁eq]; exact hCq27
  have hP₁ab : ∀ a ∈ P ⊓ Subgroup.centralizer (Q : Set G),
      ∀ b ∈ P ⊓ Subgroup.centralizer (Q : Set G), a * b = b * a := by
    rw [hP₁eq, hCq, Subgroup.sup_eq_closure]
    apply commute_closure_of_pairwise
    rintro a (ha | ha) b (hb | hb)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · exact ((Claims135.mem_centerOf_iff.1 hb).2 a ((Subgroup.zpowers_le.2 hqP) ha))
    · exact ((Claims135.mem_centerOf_iff.1 ha).2 b ((Subgroup.zpowers_le.2 hqP) hb)).symm
    · exact ((Claims135.mem_centerOf_iff.1 hb).2 a (Subgroup.map_subtype_le _ ha))
  have hsyl := w.sylow_centralizer_plane hPS hsc hQP hQe hQB
  have hZP₁ : centerOf P ≤ P ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [hP₁eq, hZ]
    exact le_inf (inf_le_left.trans w.le) inf_le_right
  have hP₁B : ∀ z, z ∈ P ⊓ Subgroup.centralizer (Q : Set G) → z ∈ B → z ∈ centerOf P := by
    intro z hz hzB
    rw [hP₁eq] at hz
    rw [hZ]
    exact Subgroup.mem_inf.2 ⟨hzB, (Subgroup.mem_inf.1 hz).2⟩
  have hNP₁ : Subgroup.normalizer ((P ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) ≤
      M := by
    have fwd : ∀ g ∈ Subgroup.normalizer
        ((P ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G),
        ∀ z ∈ centerOf P, g * z * g⁻¹ ∈ centerOf P := by
      intro g hg z hz
      have h1 : g * z * g⁻¹ ∈ P ⊓ Subgroup.centralizer (Q : Set G) :=
        (Subgroup.mem_normalizer_iff.1 hg z).1 (hZP₁ hz)
      refine hP₁B _ h1 ?_
      have := hsc z (hZB hz) g⁻¹ (by simpa using (Subgroup.mem_inf.1 h1).1)
      simpa using this
    intro g hg
    apply Claims135.normalizer_le_of_le_B h hZB
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_of_le w.elem hZB)
        (by rw [hZ, w.card_inf_centralizer hqP hqB]; norm_num))
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fwd g hg z, fun h1 => ?_⟩
    have := fwd g⁻¹ (Subgroup.inv_mem _ hg) _ h1
    simpa [mul_assoc] using this
  obtain ⟨B₀, hB₀B, hB₀N, hB₀c⟩ := w.exists_B0 hQP hQe hQc hQB
  have hE : ∀ E : Subgroup G, E ≤ B₀ ∧ Nat.card ↥E = 9 →
      Subgroup.centralizer (E : Set G) ≤ M := by
    rintro E ⟨hEB₀, hEc⟩
    exact (Subgroup.centralizer_le_normalizer _).trans (Claims135.normalizer_le_of_le_B h
      (hEB₀.trans hB₀B) (CFSG.SectionRank.le_pRank (by norm_num) le_rfl
        (isElemAbelian_of_le w.elem (hEB₀.trans hB₀B)) (by rw [hEc]; norm_num)))
  have hCtop : Subgroup.centralizer (Q : Set G) ≠ ⊤ := by
    intro htop
    haveI := h.standing.simple
    have hQZ : Q ≤ Subgroup.center G := fun y hy => Subgroup.mem_center_iff.2 fun g => by
      have hg : g ∈ Subgroup.centralizer (Q : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg y hy).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc] at hQZ
      have := Subgroup.card_le_of_le hQZ
      rw [hQc, Subgroup.card_bot] at this
      norm_num at this
    · obtain ⟨a, b, hab⟩ := h.standing.nonabelian
      exact hab (Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top b) a)
  exact (hgen G h.standing.kProper Q _ B₀ hQe hQc hCtop hsyl hP₁ab hP₁27 hB₀N
    (isElemAbelian_of_le w.elem hB₀B) hB₀c).trans (sup_le hNP₁ (iSup₂_le fun E hE' => hE E hE'))

end Centralizer

theorem lemma135_i_of_gen (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    (hgen : CentralizerGenInput) : Lemma135_iStatement :=
  Claims135.lemma135_i_of_inputs'' hP95 h111 h121 hcomp h133
    (centerInput_of_inputs hP95 h111 h121 hcomp h133)
    (familyCoreInput_of_inputs hP95 h111 h121 hcomp h133)
    (centralizerInput_of_inputs hP95 h111 h121 hcomp h133 hgen)

@[expose] def CentralizerLayerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
    ∀ Q P₁ B₀ : Subgroup G, IsElemAbelian 3 Q → Nat.card ↥Q = 9 →
      Subgroup.centralizer (Q : Set G) ≠ ⊤ →
      IsSylowIn 3 (Subgroup.centralizer (Q : Set G)) P₁ →
      (∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a) → Nat.card ↥P₁ = 27 →
      B₀ ≤ Subgroup.normalizer (Q : Set G) → IsElemAbelian 3 B₀ → Nat.card ↥B₀ = 27 →
      Subgroup.centralizer (Q : Set G) ≤
        GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set G)) ⊔ Subgroup.normalizer (P₁ : Set G) ⊔
          ⨆ (E : Subgroup G) (_ : E ≤ B₀ ∧ Nat.card ↥E = 9), Subgroup.centralizer (E : Set G)

theorem centralizerGenInput_of_layer (hL : CentralizerLayerInput) : CentralizerGenInput := by
  intro G _ _ hK Q P₁ B₀ hQe hQc hCtop hsyl hab h27 hB₀N hB₀e hB₀c
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (hL G hK Q P₁ B₀ hQe hQc hCtop hsyl hab h27 hB₀N hB₀e hB₀c).trans
    (sup_le (sup_le ?_ le_sup_left) le_sup_right)
  have hB₀C : B₀ ≤ Subgroup.normalizer
      (GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set G)) : Set G) :=
    (hB₀N.trans (Lemma135.le_normalizer_centralizer_of_le le_rfl)).trans
      (CFSG.HardMathSupport.Solomon.LocalBalance.normalizer_le_normalizer_glaPPrimeCoreOf 3 _)
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set G)))) := by
    have e : Nat.card ↥(GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set G))) =
        Nat.card ↥(GLAPPrimeCore 3 ↥(Subgroup.centralizer (Q : Set G))) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [e]
    exact CFSG.pPrimeCore_coprime_card
  rw [← CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.generation_hyperplanes Nat.prime_three
    hB₀e (by rw [hB₀c]; norm_num) hB₀C hcop]
  refine iSup₂_le fun E hE => ?_
  obtain ⟨hEB, hEc⟩ := hE
  refine inf_le_right.trans (le_sup_of_le_right (le_iSup₂_of_le
    (f := fun E (_ : E ≤ B₀ ∧ Nat.card ↥E = 9) => Subgroup.centralizer (E : Set G)) E
    ⟨hEB, by omega⟩ le_rfl))

theorem lemma135_i_of_layer (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    (hL : CentralizerLayerInput) : Lemma135_iStatement :=
  lemma135_i_of_gen hP95 h111 h121 hcomp h133 (centralizerGenInput_of_layer hL)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims135b
