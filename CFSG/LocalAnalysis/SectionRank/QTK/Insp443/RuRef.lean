module

public import CFSG.Quasithin.Vol2.KGFactC31Ru

public section

namespace CFSG.SectionRank.QTK.Insp443.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Ru

variable {A : Type} [Group A] [Finite A]

theorem exists_ref_of
    {L V : Subgroup A}
    (hper : ⁅L, L⁆ = L) (hLV : L ≤ Subgroup.normalizer (V : Set A)) (hne : ⁅V, L⁆ ≠ ⊥)
    (hV : IsElemAbelian 2 V) (e : G₀ ≃* A) :
    ∃ e' : G₀ ≃* A, ∃ τ' < 5, ∃ y' : G₀, img e' (refU τ') ≤ V ∧ e' y' ∈ L ∧
      (y' : Equiv.Perm (Fin 4060)) ∈
        Subgroup.normalizer (refU τ' : Set (Equiv.Perm (Fin 4060))) ∧ y' ≠ 1 ∧
      ((refPrime τ' = 5 ∧ y' ^ 5 ^ 3 = 1) ∨ (refPrime τ' = 7 ∧ y' ^ 7 ^ 1 = 1)) := by
  have V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  have V_sq : ∀ a ∈ V, a * a = 1 := fun a ha => by
    have := hV.2 a ha
    rwa [sq] at this
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ := exists_pElement_not_comm hper hLV hne
  set y₀ := e.symm y with hy₀
  set t₀ := e.symm t with ht₀
  have hey : e y₀ = y := by simp [hy₀]
  have het : e t₀ = t := by simp [ht₀]
  have ht2 : orderOf (t₀ : Equiv.Perm (Fin 4060)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => hyt ?_
    · have h2 := V_sq t ht
      rw [← het, ← map_mul, ← map_one e] at h2
      rw [sq]
      exact congrArg Subtype.val (e.injective h2)
    · have : t₀ = 1 := Subtype.ext h1
      rw [← het, this, map_one, mul_one, mul_inv_cancel]
  have hinv : (t₀ : Equiv.Perm (Fin 4060)) ∈ ruZP ∪ ruAP := by
    rw [← ruInvolutions_eq]
    exact ⟨t₀.2, ht2⟩
  obtain ⟨τ, hτ, g, hg, hgt⟩ : ∃ τ, (τ = ruZ ∨ τ = ruA0) ∧ ∃ g ∈ ruP,
      g * τ * g⁻¹ = (t₀ : Equiv.Perm (Fin 4060)) := by
    rcases hinv with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
    · exact ⟨ruZ, Or.inl rfl, g, hg, hgt⟩
    · exact ⟨ruA0, Or.inr rfl, g, hg, hgt⟩
  have hτP : τ ∈ ruP := by rcases hτ with rfl | rfl; exacts [ruZ_mem, ruA0_mem]
  set e₁ := conjE e ⟨g, hg⟩ with he₁
  set τ₀ : G₀ := ⟨τ, hτP⟩
  set y₁ : G₀ := (⟨g, hg⟩ : G₀)⁻¹ * y₀ * ⟨g, hg⟩ with hy₁
  have he₁τ : e₁ τ₀ = t := by
    rw [he₁, conjE_apply, ← het]
    congr 1
    exact Subtype.ext hgt
  have he₁y : e₁ y₁ = y := by
    rw [he₁, conjE_apply, hy₁, ← hey]
    congr 1
    group
  set Y : Equiv.Perm (Fin 4060) := (y₁ : Equiv.Perm (Fin 4060)) with hY
  have hYP : Y ∈ ruP := y₁.2
  have hmove : Y * τ * Y⁻¹ ≠ τ := by
    intro hm
    apply hyt
    have : y₁ * τ₀ * y₁⁻¹ = τ₀ := Subtype.ext hm
    rw [← he₁y, ← he₁τ, ← map_inv, ← map_mul, ← map_mul, this]
  have hV₁ : ∀ a ∈ pb e₁ V, ∀ b ∈ pb e₁ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haP, haV⟩ := (mem_pb e₁).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e₁).mp hb
    have := V_comm _ haV _ hbV
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e₁.injective this)
  have hτV : τ ∈ pb e₁ V := (apply_mem_iff_mem_pb e₁ (g := τ₀)).mp (he₁τ ▸ ht)
  have hYN : Y ∈ Subgroup.normalizer (pb e₁ V : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e₁ hLV ((apply_mem_iff_mem_pb e₁ (g := y₁)).mp (he₁y ▸ hy))
  have hcomm : ∀ j : ℕ, τ * (Y ^ j * τ * (Y ^ j)⁻¹) = Y ^ j * τ * (Y ^ j)⁻¹ * τ := by
    intro j
    have hc : Y ^ j * τ * (Y ^ j)⁻¹ ∈ pb e₁ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hYN j) τ).mp hτV
    exact hV₁ τ hτV _ hc
  have hY1 : y₁ ≠ 1 := by
    intro h1
    apply hmove
    rw [hY, h1]
    simp
  have hYk : y₁ ^ p ^ k = 1 := by
    apply e₁.injective
    rw [map_pow, he₁y, hyk, map_one]
  have hpd : p ∣ 145926144000 := by
    by_contra hpd
    have h1 := pow_eq_one_of_not_dvd hp hYk (m := 0) (by rw [card_G₀, zero_add, pow_one]; exact hpd)
    rw [pow_zero, pow_one] at h1
    exact hY1 h1
  have hZA := hτ
  obtain ⟨hs5, hs7, hs13⟩ :
      ([125], 5) ∈ ruGroups ∧ ([7], 7) ∈ ruGroups ∧ ([13, 29], 0) ∈ ruGroups := by
    simp [ruGroups]
  have hbad : ∀ {es : List ℕ} {q : ℕ}, (es, q) ∈ ruGroups →
      (∃ e ∈ es, Y ^ e = 1) → BadConcl Y τ q := by
    intro es q hs he
    rcases hZA with rfl | rfl
    · exact classifyZ hYP hmove hs he hcomm
    · exact classifyA hYP hmove hs he hcomm
  have key : ∀ {q : ℕ}, BadConcl Y τ q → ∃ e' : G₀ ≃* A, ∃ τ' < 5, ∃ y' : G₀,
      refPrime τ' = q ∧ img e' (refU τ') ≤ V ∧ e' y' ∈ L ∧
      (y' : Equiv.Perm (Fin 4060)) ∈
        Subgroup.normalizer (refU τ' : Set (Equiv.Perm (Fin 4060))) ∧ y' ≠ 1 ∧
      ∀ m : ℕ, y₁ ^ m = 1 → y' ^ m = 1 := by
    intro q hb
    obtain ⟨g', hg', c, hc, hq, hle, hn⟩ := hb
    refine ⟨conjE e₁ ⟨g', hg'⟩, c.1, candData_lt c hc, (⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩, hq,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [img_conjE]
      refine (img_mono e₁ hle).trans ?_
      rw [show Y = ((y₁ : G₀) : Equiv.Perm (Fin 4060)) from rfl,
        show τ = ((τ₀ : G₀) : Equiv.Perm (Fin 4060)) from rfl, img_orbSub, he₁y, he₁τ]
      exact orbSub_le (hLV hy) ht
    · rw [conjE_apply, show (⟨g', hg'⟩ : G₀) * ((⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩) *
        (⟨g', hg'⟩ : G₀)⁻¹ = y₁ by group, he₁y]
      exact hy
    · simpa using hn
    · intro h1
      apply hY1
      have : y₁ = ⟨g', hg'⟩ * ((⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩) * (⟨g', hg'⟩ : G₀)⁻¹ := by
        group
      rw [this, h1]
      group
    · intro m hm
      have e1 : (⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩ =
          (⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ((⟨g', hg'⟩ : G₀)⁻¹)⁻¹ := by rw [inv_inv]
      rw [e1, conj_pow, hm]
      group
  rcases prime_dvd_ru hp hp5 hpd with rfl | rfl | rfl | rfl
  ·
    have h5 : y₁ ^ 5 ^ 3 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 3)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, hUV, hyM, hyN, hy1, hpow⟩ :=
      key (hbad hs5 ⟨125, List.mem_singleton_self _, by simpa using congrArg Subtype.val h5⟩)
    exact ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, Or.inl ⟨hq, hpow _ h5⟩⟩
  ·
    have h7 : y₁ ^ 7 ^ 1 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 1)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, hUV, hyM, hyN, hy1, hpow⟩ :=
      key (hbad hs7 ⟨7, List.mem_singleton_self _, by simpa using congrArg Subtype.val h7⟩)
    exact ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, Or.inr ⟨hq, hpow _ h7⟩⟩
  ·
    have h13 : y₁ ^ 13 ^ 1 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 1)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, -⟩ :=
      key (hbad hs13 ⟨13, by simp, by simpa using congrArg Subtype.val h13⟩)
    exfalso
    unfold refPrime at hq
    split_ifs at hq
  ·
    have h29 : y₁ ^ 29 ^ 1 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 1)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, -⟩ :=
      key (hbad hs13 ⟨29, by simp, by simpa using congrArg Subtype.val h29⟩)
    exfalso
    unfold refPrime at hq
    split_ifs at hq

end CFSG.SectionRank.QTK.Insp443.Ru

end
