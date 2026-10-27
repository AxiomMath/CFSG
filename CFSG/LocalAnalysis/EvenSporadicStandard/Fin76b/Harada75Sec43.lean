module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Cfg
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec42

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Complement

variable {S : Type} [Group S] [Finite S]

theorem exists_complement_E8 {A : Subgroup S} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    {z : S} (hzA : z ∈ A) (hz1 : z ≠ 1) :
    ∃ F : Subgroup S, F ≤ A ∧ Nat.card F = 4 ∧ z ∉ F ∧ ∀ x ∈ A, x ∈ F ∨ x * z ∈ F := by
  classical
  have hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  have hne : Set.Nonempty {H : Subgroup S | H ≤ A ∧ z ∉ H} :=
    ⟨⊥, bot_le, fun h => hz1 ((Subgroup.mem_bot).mp h)⟩
  obtain ⟨F, ⟨hFA, hzF⟩, hmax⟩ := (Set.toFinite {H : Subgroup S | H ≤ A ∧ z ∉ H}).exists_maximal hne
  have hcover : ∀ x ∈ A, x ∈ F ∨ x * z ∈ F := by
    intro x hxA
    by_contra hcon
    push Not at hcon
    obtain ⟨hxF, hxzF⟩ := hcon
    have hLE : Subgroup.zpowers x ≤ Subgroup.normalizer (F : Set S) := by
      refine (Subgroup.zpowers_le).mpr ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hxh : x * h * x⁻¹ = h ∨ h ∉ A := by
        by_cases hhA : h ∈ A
        · left
          rw [hab x hxA h hhA]
          group
        · right; exact hhA
      constructor
      · intro hh
        rcases hxh with e | e
        · rw [e]; exact hh
        · exact absurd (hFA hh) e
      · intro hh
        have hhA : h ∈ A := by
          by_contra hn
          have : x * h * x⁻¹ ∈ A := hFA hh
          apply hn
          have h2 : h = x⁻¹ * (x * h * x⁻¹) * x := by group
          rw [h2]
          exact A.mul_mem (A.mul_mem (A.inv_mem hxA) this) hxA
        have : x * h * x⁻¹ = h := by rw [hab x hxA h hhA]; group
        rw [this] at hh
        exact hh
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x) F hLE
    have hF' : Subgroup.zpowers x ⊔ F ≤ A :=
      sup_le ((Subgroup.zpowers_le).mpr hxA) hFA
    have hzF' : z ∉ Subgroup.zpowers x ⊔ F := by
      intro hz
      have hz' : z ∈ (↑(Subgroup.zpowers x ⊔ F) : Set S) := hz
      rw [hcoe] at hz'
      obtain ⟨y, hy, f, hf, hyf⟩ := hz'
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hyf' : x ^ n * f = z := hyf
      rcases zpow_eq_one_or_self x (hsq x hxA) n with h1 | h1
      · rw [h1, one_mul] at hyf'
        exact hzF (hyf' ▸ hf)
      · rw [h1] at hyf'
        apply hxzF
        have : x * z = f := by rw [← hyf', ← mul_assoc, hsq x hxA, one_mul]
        rw [this]; exact hf
    have hle := hmax (y := Subgroup.zpowers x ⊔ F) ⟨hF', hzF'⟩ le_sup_right
    exact hxF (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
  have hFlt : Nat.card F < Nat.card A := by
    apply Nat.lt_of_le_of_ne (Subgroup.card_le_of_le hFA)
    intro h
    have : F = A := Subgroup.eq_of_le_of_card_ge hFA h.ge
    exact hzF (this ▸ hzA)
  have hFdvd : Nat.card F ∣ 8 := hA8 ▸ Subgroup.card_dvd_of_le hFA
  have hF4le : Nat.card F ≤ 4 := by
    have hc : Nat.card F ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hFdvd, by norm_num⟩
    have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [this] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h | h | h | h <;> omega
  have hA2 : Nat.card A ≤ 2 * Nat.card F := by
    have hsub : (A : Set S) ⊆ (F : Set S) ∪ ((fun x => x * z) '' (F : Set S)) := by
      intro x hxA
      rcases hcover x hxA with h | h
      · exact Or.inl h
      · right
        refine ⟨x * z, h, ?_⟩
        have := hsq z hzA
        calc x * z * z = x * (z * z) := by group
          _ = x := by rw [this, mul_one]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (F : Set S) ((fun x => x * z) '' (F : Set S))
    have h3 : ((fun x => x * z) '' (F : Set S)).ncard = (F : Set S).ncard :=
      Set.ncard_image_of_injective _ (mul_left_injective z)
    have h4 : Nat.card A = (A : Set S).ncard := Nat.card_coe_set_eq (A : Set S)
    have h5 : Nat.card F = (F : Set S).ncard := Nat.card_coe_set_eq (F : Set S)
    omega
  have hF4 : Nat.card F = 4 := by omega
  exact ⟨F, hFA, hF4, hzF, hcover⟩

theorem card_finset_le_of_forall_mem (H : Subgroup S) (T : Finset S) (hT : ∀ t ∈ T, t ∈ H) :
    T.card ≤ Nat.card H := by
  classical
  have hsub : (T : Set S) ⊆ (H : Set S) := fun t ht => hT t ht
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h4 : Nat.card H = (H : Set S).ncard := Nat.card_coe_set_eq (H : Set S)
  omega

theorem eq_one_or_of_card_two {H : Subgroup S} (h : Nat.card H = 2) {z : S} (hz : z ∈ H)
    (hz1 : z ≠ 1) : ∀ x ∈ H, x = 1 ∨ x = z := by
  classical
  intro x hx
  by_contra hcon
  push Not at hcon
  have hcard := card_finset_le_of_forall_mem H {1, z, x} (by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact H.one_mem
    · exact hz
    · exact hx)
  have h3 : ({1, z, x} : Finset S).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hcon.2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hz1.symm, hcon.1.symm⟩
  omega

theorem commutes_of_cover {A F : Subgroup S} {z : S} (hzz : z * z = 1)
    (hcover : ∀ x ∈ A, x ∈ F ∨ x * z ∈ F) {y : S} (hyF : ∀ f ∈ F, y * f = f * y)
    (hyz : y * z = z * y) : ∀ x ∈ A, y * x = x * y := by
  intro x hx
  rcases hcover x hx with h | h
  · exact hyF x h
  · have h1 := hyF (x * z) h
    have hxz : x * z * z = x := by rw [mul_assoc, hzz, mul_one]
    calc y * x = y * (x * z * z) := by rw [hxz]
      _ = (y * (x * z)) * z := by group
      _ = ((x * z) * y) * z := by rw [h1]
      _ = x * (z * y) * z := by group
      _ = x * (y * z) * z := by rw [← hyz]
      _ = x * y * (z * z) := by group
      _ = x * y := by rw [hzz, mul_one]

theorem cfg2_of_AE (hS : IsPGroup 2 S) {A E : Subgroup S} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hEn : E.Normal) (hAE2 : Nat.card (A ⊓ E : Subgroup S) = 2) :
    ∃ (F : Subgroup S) (z : S), Cfg2 S E F z := by
  classical
  have hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  obtain ⟨z, hzAE, hz1⟩ : ∃ z ∈ (A ⊓ E : Subgroup S), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (A ⊓ E : Subgroup S) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hAE2
    omega
  have hZ := eq_one_or_of_card_two hAE2 hzAE hz1
  obtain ⟨F, hFA, hF4, hzF, hcover⟩ := exists_complement_E8 hA hA8 hzAE.1 hz1
  have hzz : z * z = 1 := hAsq z hzAE.1
  have hAE_mem : ∀ x : S, x ∈ A → x ∈ E → x = 1 ∨ x = z := fun x hxA hxE => hZ x ⟨hxA, hxE⟩
  refine ⟨F, z, ?_⟩
  refine ⟨hEn, hE, hE8, ⟨⟨⟨fun a b => Subtype.ext (hab a.1 (hFA a.2) b.1 (hFA b.2))⟩⟩,
    fun x hx => hA.2 x (hFA hx)⟩, hF4, hzAE.2, hz1, ?_, ?_, ?_, ?_⟩
  · intro f hf
    exact hab f (hFA hf) z hzAE.1
  · intro f hf hfE
    have hfE' : f ∈ E := mem_of_centralizes_of_card_two hS hA hA8 hCA hE hE8 hEn hAE2
      f (hFA hf) hfE
    rcases hAE_mem f (hFA hf) hfE' with h | h
    · exact h
    · exact absurd (h ▸ hf) hzF
  · intro e he hF
    have hcomm : ∀ x ∈ A, e * x = x * e :=
      commutes_of_cover hzz hcover (fun f hf => (hF f hf).symm) (hEab e he z hzAE.2)
    have heA : e ∈ A := hCA (Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcomm x hx).symm))
    exact hAE_mem e heA he
  · intro k hkE hkF
    have hkz : k * z = z * k := hkE z hzAE.2
    have hcomm : ∀ x ∈ A, k * x = x * k := commutes_of_cover hzz hcover hkF hkz
    have hkA : k ∈ A := hCA (Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcomm x hx).symm))
    have hkE' : k ∈ E := mem_of_centralizes_of_card_two hS hA hA8 hCA hE hE8 hEn hAE2
      k hkA hkE
    exact hAE_mem k hkA hkE'

end Complement

end CFSG.EvenSporadicStandard.Fin76b
