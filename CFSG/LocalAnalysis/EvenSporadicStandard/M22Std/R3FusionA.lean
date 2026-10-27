module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_abelian_of_lt_card {L1 A : Subgroup G} {w : G}
    (hL1c : ∀ a ∈ L1, ∀ b ∈ L1, a * b = b * a) (hw2 : w * w = 1)
    (hwN : ∀ a, a ∈ L1 ↔ w * a * w⁻¹ ∈ L1) (hAK : A ≤ L1 ⊔ zpowers w)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 * Nat.card ↥(centralizer ({w} : Set G) ⊓ L1) < Nat.card A) : A ≤ L1 := by
  classical
  by_contra hA
  obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.1 hA
  obtain ⟨l, hl, hal⟩ : ∃ l ∈ L1, a = w * l := by
    rcases mem_sup_zpowers_invol hw2 hwN (hAK haA) with h | h
    · exact absurd h haL
    · exact h
  have hBU : A ⊓ L1 ≤ centralizer ({w} : Set G) ⊓ L1 := by
    intro x hx
    obtain ⟨hxA, hxL⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, hxL⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hAc a haA x hxA
    rw [hal] at h1
    have h2 := hL1c l hl x hxL
    have h3 : w * (x * l) = x * w * l := by
      calc w * (x * l) = w * (l * x) := by rw [h2]
        _ = w * l * x := by rw [mul_assoc]
        _ = x * (w * l) := h1
        _ = x * w * l := by rw [mul_assoc]
    rw [← mul_assoc] at h3
    exact (mul_right_cancel h3).symm
  have hcases : ∀ x ∈ A, x ∈ L1 ∨ a⁻¹ * x ∈ L1 := by
    intro x hx
    rcases mem_sup_zpowers_invol hw2 hwN (hAK hx) with h | ⟨l', hl', hxl⟩
    · exact Or.inl h
    · right
      have : a⁻¹ * x = l⁻¹ * l' := by rw [hal, hxl]; group
      rw [this]
      exact L1.mul_mem (L1.inv_mem hl) hl'
  let f : ↥A → ↥(A ⊓ L1) × Bool := fun x =>
    if hx : (x : G) ∈ L1 then (⟨x, Subgroup.mem_inf.2 ⟨x.2, hx⟩⟩, false)
    else (⟨a⁻¹ * x, Subgroup.mem_inf.2 ⟨A.mul_mem (A.inv_mem haA) x.2,
      (hcases x x.2).resolve_left hx⟩⟩, true)
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : G) ∈ L1 <;> by_cases hy : (y : G) ∈ L1
    · simp only [f, hx, hy, dite_true, Prod.mk.injEq] at hxy
      exact Subtype.ext (Subtype.mk.inj hxy.1)
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · simp only [f, hx, hy, dite_false, Prod.mk.injEq, and_true] at hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (mul_left_cancel this)
  have hle : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L1) := by
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  have hle2 := Subgroup.card_le_of_le hBU
  omega

theorem exists_normalizer_conj_mem_coset {L1 F : Subgroup G} {z y g : G}
    (hL1c : ∀ a ∈ L1, ∀ b ∈ L1, a * b = b * a) (hL1card : Nat.card L1 = 256)
    (hz2 : z * z = 1) (hy2 : y * y = 1)
    (hzN : ∀ a, a ∈ L1 ↔ z * a * z⁻¹ ∈ L1) (hyN : ∀ a, a ∈ L1 ↔ y * a * y⁻¹ ∈ L1)
    (hzL : z ∉ L1) (hyL : y ∉ L1) (hFL : F ≤ L1) (hzF : ∀ x ∈ F, z * x = x * z)
    (hKp : IsPGroup 2 ↥(L1 ⊔ zpowers z))
    (hKs : ¬ 2 ∣ (L1 ⊔ zpowers z).relIndex (centralizer (F : Set G)))
    (hU : centralizer ({y} : Set G) ⊓ L1 = F.map (MulAut.conj g).toMonoidHom)
    (hU16 : Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) = 16) :
    ∃ k ∈ normalizer (L1 : Set G), ∃ l ∈ L1, k * z * k⁻¹ = y * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := L1 ⊔ zpowers z with hK
  set K' := L1 ⊔ zpowers y with hK'
  have hKcard : Nat.card K = 512 := by
    rw [hK, card_sup_zpowers_invol hz2 hzN hzL, hL1card]
  have hK'card : Nat.card K' = 512 := by
    rw [hK', card_sup_zpowers_invol hy2 hyN hyL, hL1card]
  have hK'p : IsPGroup 2 K' := IsPGroup.of_card (n := 9) (by rw [hK'card]; norm_num)
  have hKC : K ≤ centralizer (F : Set G) := by
    refine sup_le (fun x hx => mem_centralizer_iff.2 fun f hf => hL1c f (hFL hf) x hx) ?_
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 fun f hf => (hzF f hf).symm
  set U : Subgroup G := centralizer ({y} : Set G) ⊓ L1 with hUdef
  have hUL : U ≤ L1 := inf_le_right
  have hK'U : ∀ x ∈ K', ∀ u ∈ U, u * x = x * u := by
    intro x hx u hu
    have hs : K' ≤ centralizer (U : Set G) := by
      refine sup_le (fun x hx => mem_centralizer_iff.2 fun u hu => hL1c u (hUL hu) x hx) ?_
      rw [Subgroup.zpowers_le]
      exact mem_centralizer_iff.2 fun u hu =>
        (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).1)
    exact mem_centralizer_iff.1 (hs hx) u hu
  set K'' : Subgroup G := K'.map (MulAut.conj g⁻¹).toMonoidHom with hK''
  have hmemK'' : ∀ x, x ∈ K'' ↔ g * x * g⁻¹ ∈ K' := by
    intro x
    rw [hK'', Subgroup.mem_map_equiv]
    simp
  have hK''C : K'' ≤ centralizer (F : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro f hf
    have hgf : g * f * g⁻¹ ∈ U := by
      rw [hU]
      exact ⟨f, hf, rfl⟩
    have := hK'U (g * x * g⁻¹) ((hmemK'' x).1 hx) _ hgf
    have h2 : f * x = x * f := by
      calc f * x = g⁻¹ * ((g * f * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * f * g⁻¹)) * g := by rw [this]
        _ = x * f := by group
    exact h2
  have hK''card : Nat.card K'' = 512 := by
    rw [hK'', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hK'card]
  have hK''p : IsPGroup 2 K'' := IsPGroup.of_card (n := 9) (by rw [hK''card]; norm_num)
  have hKidx := Subgroup.relIndex_mul_card K (centralizer (F : Set G))
  have hK''idx := Subgroup.relIndex_mul_card K'' (centralizer (F : Set G))
  rw [inf_of_le_left hKC, hKcard] at hKidx
  rw [inf_of_le_left hK''C, hK''card] at hK''idx
  have hK''s : ¬ 2 ∣ K''.relIndex (centralizer (F : Set G)) := by
    have : K''.relIndex (centralizer (F : Set G)) = K.relIndex (centralizer (F : Set G)) := by
      have := hKidx.trans hK''idx.symm
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 512) this).symm
    rw [this]
    exact hKs
  obtain ⟨h, -, hh⟩ := exists_conj_sylow_two ⟨hKC, hKp, hKs⟩ ⟨hK''C, hK''p, hK''s⟩
  set k : G := g * h with hk
  have hkK : ∀ x ∈ K, k * x * k⁻¹ ∈ K' := by
    intro x hx
    have h1 : h * x * h⁻¹ ∈ K'' := (hh _).2 (by
      rw [show h⁻¹ * (h * x * h⁻¹) * h = x by group]
      exact hx)
    have h2 := (hmemK'' _).1 h1
    have : g * (h * x * h⁻¹) * g⁻¹ = k * x * k⁻¹ := by rw [hk]; group
    rwa [this] at h2
  have hAK : L1.map (MulAut.conj k).toMonoidHom ≤ K' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hkK x (Subgroup.mem_sup_left hx)
  have hAc : ∀ a ∈ L1.map (MulAut.conj k).toMonoidHom, ∀ b ∈ L1.map (MulAut.conj k).toMonoidHom,
      a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    show k * x * k⁻¹ * (k * x' * k⁻¹) = k * x' * k⁻¹ * (k * x * k⁻¹)
    calc k * x * k⁻¹ * (k * x' * k⁻¹) = k * (x * x') * k⁻¹ := by group
      _ = k * (x' * x) * k⁻¹ := by rw [hL1c x hx x' hx']
      _ = k * x' * k⁻¹ * (k * x * k⁻¹) := by group
  have hAcard : Nat.card ↥(L1.map (MulAut.conj k).toMonoidHom) = 256 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hL1card]
  have hAL := le_of_abelian_of_lt_card hL1c hy2 hyN (by rw [hK'] at hAK; exact hAK) hAc
    (by rw [hAcard, hU16]; norm_num)
  have hAeq : L1.map (MulAut.conj k).toMonoidHom = L1 :=
    Subgroup.eq_of_le_of_card_ge hAL (by rw [hAcard, hL1card])
  have hkN : k ∈ normalizer (L1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hAeq]
      exact ⟨a, ha, rfl⟩
    · intro ha
      rw [← hAeq] at ha
      obtain ⟨a', ha', haa'⟩ := ha
      have : a' = a := by
        have h1 : k * a' * k⁻¹ = k * a * k⁻¹ := haa'
        simpa using h1
      rwa [← this]
  refine ⟨k, hkN, ?_⟩
  have hzK : k * z * k⁻¹ ∈ K' := hkK z (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  rcases mem_sup_zpowers_invol hy2 hyN hzK with h1 | ⟨l, hl, hl'⟩
  · exact absurd ((Subgroup.mem_normalizer_iff.1 hkN z).2 h1) hzL
  · exact ⟨l, hl, hl'⟩

end CFSG.EvenSporadicStandard.M22Std
