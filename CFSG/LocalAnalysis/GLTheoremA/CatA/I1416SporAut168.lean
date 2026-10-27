module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow
public import CFSG.LocalAnalysis.GLTheoremA.S8.I2014Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open Pointwise MulAction

variable {T : Type} [Group T] [Finite T]

theorem sylow7_facts_168 [IsSimpleGroup T] (hT : Nat.card T = 168) :
    Nat.card (Sylow 7 T) = 8 ∧ ∀ P : Sylow 7 T, Nat.card (P : Subgroup T) = 7 ∧
      Subgroup.normalizer ((P : Subgroup T) : Set T) ≠ ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcardP : ∀ P : Sylow 7 T, Nat.card (P : Subgroup T) = 7 := by
    intro P
    rw [P.card_eq_multiplicity, hT, show (168 : ℕ) = 7 ^ 1 * 24 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num), Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 24 by norm_num)]
    norm_num
  have hPn : ∀ P : Sylow 7 T, Subgroup.normalizer ((P : Subgroup T) : Set T) ≠ ⊤ := by
    intro P hN
    have : (P : Subgroup T).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup T) with hb | ht
    · have h := hcardP P
      rw [hb, Subgroup.card_bot] at h
      norm_num at h
    · have h := hcardP P
      rw [ht, Subgroup.card_top, hT] at h
      norm_num at h
  obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
  set n := Nat.card (Sylow 7 T) with hn
  have hn1 : n ≡ 1 [MOD 7] := card_sylow_modEq_one 7 T
  have hnidx : n = (Subgroup.normalizer ((P : Subgroup T) : Set T)).index :=
    Sylow.card_eq_index_normalizer P
  have hidx : (Subgroup.normalizer ((P : Subgroup T) : Set T)).index ∣ (P : Subgroup T).index :=
    Subgroup.index_dvd_of_le Subgroup.le_normalizer
  have hidx24 : (P : Subgroup T).index ∣ 24 := by
    have h1 := Subgroup.index_mul_card (P : Subgroup T)
    rw [hcardP P, hT] at h1
    exact ⟨1, by omega⟩
  have hn24 : n ∣ 24 := hnidx ▸ hidx.trans hidx24
  have hn8 : n = 8 := by
    have hle := Nat.le_of_dvd (by norm_num) hn24
    have h1 : n % 7 = 1 := hn1
    have hne1 : n ≠ 1 := by
      intro h1'
      apply hPn P
      rw [← Subgroup.index_eq_one, ← hnidx, h1']
    interval_cases n <;> omega
  exact ⟨hn8, fun P => ⟨hcardP P, hPn P⟩⟩

theorem not_sq_three_dvd_card_mulAut_of_card_168 [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hT : Nat.card T = 168) :
    ¬ 3 ^ 2 ∣ Nat.card (MulAut T) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  classical
  obtain ⟨h8, hP⟩ := sylow7_facts_168 hT
  obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
  obtain ⟨hP7, hPn⟩ := hP P
  have hinj := toPermHom_mulAut_injective hPn
  have hPcomm : ∀ g ∈ (P : Subgroup T), ∀ h ∈ (P : Subgroup T), g * h = h * g := by
    haveI : IsCyclic (P : Subgroup T) := isCyclic_of_prime_card hP7
    intro g hg h hh
    have := (IsCyclic.commGroup (α := (P : Subgroup T))).mul_comm ⟨g, hg⟩ ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hPP : ∀ g ∈ (P : Subgroup T), g • P = P := fun g hg =>
    Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hg)
  have hfree : ∀ Q : Sylow 7 T, Q ≠ P → ∀ g ∈ (P : Subgroup T), g • Q = Q → g = 1 := by
    intro Q hQ g hg hgQ
    by_contra hg1
    have hgN : g ∈ Subgroup.normalizer ((Q : Subgroup T) : Set T) :=
      Sylow.smul_eq_iff_mem_normalizer.1 hgQ
    have hgo : orderOf g = 7 := by
      have hd : orderOf g ∣ 7 := hP7 ▸ Subgroup.orderOf_dvd_natCard _ hg
      rcases (Nat.dvd_prime (by norm_num)).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hg1
      · exact h
    have hQ7 := (hP Q).1
    have hgQm : g ∈ (Q : Subgroup T) := by
      by_contra hn
      have hN : Subgroup.zpowers g ≤ Subgroup.normalizer ((Q : Subgroup T) : Set T) :=
        Subgroup.zpowers_le.2 hgN
      have hb : Subgroup.zpowers g ⊓ (Q : Subgroup T) = ⊥ := by
        have hd : Nat.card ↥(Subgroup.zpowers g ⊓ (Q : Subgroup T)) ∣ 7 := by
          have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers g ⊓ (Q : Subgroup T) ≤ _)
          rwa [Nat.card_zpowers, hgo] at this
        rcases (Nat.dvd_prime (by norm_num)).1 hd with h | h
        · exact Subgroup.card_eq_one.1 h
        · exfalso
          have heq : Subgroup.zpowers g ⊓ (Q : Subgroup T) = Subgroup.zpowers g :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hgo, h])
          exact hn ((heq ▸ inf_le_right : Subgroup.zpowers g ≤ (Q : Subgroup T))
            (Subgroup.mem_zpowers g))
      have hc := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.card_sup_of_inf_bot hN hb
      rw [Nat.card_zpowers, hgo, hQ7] at hc
      have hd := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers g ⊔ (Q : Subgroup T))
      rw [hc, hT] at hd
      norm_num at hd
    have h1 : Subgroup.zpowers g = (P : Subgroup T) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg) (by rw [Nat.card_zpowers, hgo, hP7])
    have h2 : Subgroup.zpowers g = (Q : Subgroup T) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgQm)
        (by rw [Nat.card_zpowers, hgo, hQ7])
    exact hQ (Sylow.ext (h2.symm.trans h1))
  obtain ⟨Q0, hQ0⟩ : ∃ Q : Sylow 7 T, Q ≠ P := by
    by_contra h
    push Not at h
    have : Nat.card (Sylow 7 T) ≤ 1 := Finite.card_le_one_iff_subsingleton.2
      ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  have htrans : ∀ Q : Sylow 7 T, Q ≠ P → ∃ h ∈ (P : Subgroup T), h • Q0 = Q := by
    set O : Set (Sylow 7 T) := (fun g : (P : Subgroup T) => (g : T) • Q0) '' Set.univ
    have hOsub : O ⊆ {Q | Q ≠ P} := by
      rintro _ ⟨g, -, rfl⟩ hgP
      apply hQ0
      have hgP' : (g : T) • Q0 = P := hgP
      have := congrArg (fun R => (g : T)⁻¹ • R) hgP'
      simp only [inv_smul_smul] at this
      rw [this, hPP _ (P.inv_mem g.2)]
    have hOcard : O.ncard = 7 := by
      rw [Set.ncard_image_of_injective _ (fun a b hab => ?_), Set.ncard_univ, hP7]
      have hab' : (a : T) • Q0 = (b : T) • Q0 := hab
      have h1 : ((b : T)⁻¹ * a) • Q0 = Q0 := by
        rw [mul_smul, hab', inv_smul_smul]
      have h2 := hfree Q0 hQ0 _ (P.mul_mem (P.inv_mem b.2) a.2) h1
      apply Subtype.ext
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    have hset : {Q : Sylow 7 T | Q ≠ P}.ncard = 7 := by
      have : {Q : Sylow 7 T | Q ≠ P} = Set.univ \ {P} := by ext; simp
      rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, h8]
    have heq : O = {Q | Q ≠ P} :=
      Set.eq_of_subset_of_ncard_le hOsub (by rw [hset, hOcard])
    intro Q hQ
    have hm : Q ∈ O := heq ▸ hQ
    obtain ⟨g, -, hg⟩ := hm
    exact ⟨g, g.2, hg⟩
  set M : Subgroup (MulAut T) := (P : Subgroup T).map (MulAut.conj : T →* MulAut T) with hM
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut T => φ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    have hZ : Subgroup.center T = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnab
        exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
    rw [hZ] at hgZ
    exact hgZ
  have hMcard : Nat.card M = 7 := by
    rw [hM, Subgroup.card_map_of_injective hconj_inj, hP7]
  have hkey : ∀ α : MulAut T, (∀ g ∈ (P : Subgroup T), α g = g) → α ∈ M := by
    intro α hα
    have hαP : α • P = P := by
      apply Sylow.ext
      rw [Sylow.pointwise_smul_def]
      ext y
      constructor
      · intro hy
        rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        show α z ∈ (P : Subgroup T)
        rw [hα z hz]
        exact hz
      · intro hy
        rw [Subgroup.mem_smul_pointwise_iff_exists]
        exact ⟨y, hy, by show α y = y; exact hα y hy⟩
    have hαQ0 : α • Q0 ≠ P := by
      intro h
      apply hQ0
      have := congrArg (fun R => α⁻¹ • R) h
      simp only [inv_smul_smul] at this
      rw [this]
      conv_lhs => rw [← hαP]
      rw [inv_smul_smul]
    obtain ⟨h, hhP, hh⟩ := htrans (α • Q0) hαQ0
    have hcomm : ∀ g : T, α * MulAut.conj g = MulAut.conj (α g) * α := by
      intro g
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    have hagree : ∀ Q : Sylow 7 T, α • Q = MulAut.conj h • Q := by
      intro Q
      by_cases hQ : Q = P
      · rw [hQ, hαP, ← Sylow.smul_def, hPP h hhP]
      · obtain ⟨g, hgP, rfl⟩ := htrans Q hQ
        rw [Sylow.smul_def (g := g), ← mul_smul, hcomm, hα g hgP, mul_smul, ← hh,
          Sylow.smul_def (g := h), ← mul_smul, ← mul_smul, ← map_mul, ← map_mul, hPcomm g hgP h hhP]
    have h1 : (MulAut.conj h)⁻¹ * α = 1 := by
      apply hinj
      rw [map_one]
      ext Q
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
      rw [mul_smul, hagree Q, inv_smul_smul]
    rw [inv_mul_eq_one] at h1
    exact ⟨h, hhP, h1⟩
  set S := stabilizer (MulAut T) P with hS
  have horbit : (orbit (MulAut T) P).ncard = 8 := by
    have : orbit (MulAut T) P = Set.univ := by
      ext Q
      simp only [Set.mem_univ, iff_true]
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T P Q
      exact ⟨MulAut.conj g, by rw [← hg, Sylow.smul_def]⟩
    rw [this, Set.ncard_univ, h8]
  have hSidx : S.index = 8 := by rw [hS, MulAction.index_stabilizer, horbit]
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ (P : Subgroup T), x ≠ 1 := by
    by_contra h
    push Not at h
    have : (P : Subgroup T) = ⊥ := eq_bot_iff.2 fun y hy => h y hy
    rw [this, Subgroup.card_bot] at hP7
    norm_num at hP7
  have hxo : orderOf x = 7 := by
    have hd : orderOf x ∣ 7 := hP7 ▸ Subgroup.orderOf_dvd_natCard _ hxP
    rcases (Nat.dvd_prime (by norm_num)).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hxgen : Subgroup.zpowers x = (P : Subgroup T) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxP) (by rw [Nat.card_zpowers, hxo, hP7])
  have hSx : ∀ α ∈ S, α x ∈ (P : Subgroup T) ∧ α x ≠ 1 := by
    intro α hα
    refine ⟨?_, fun h => hx1 (α.injective (by rw [h, map_one]))⟩
    have hαP : α • P = P := hα
    have h1 : α • x ∈ α • (P : Subgroup T) := Subgroup.smul_mem_pointwise_smul x α _ hxP
    rw [← Sylow.pointwise_smul_def, hαP] at h1
    exact h1
  set S2 := stabilizer S x with hS2
  have hS2idx : S2.index ≤ 6 := by
    rw [hS2, MulAction.index_stabilizer]
    have hsub : orbit S x ⊆ ((P : Subgroup T) : Set T) \ {1} := by
      rintro _ ⟨α, rfl⟩
      exact ⟨(hSx α α.2).1, (hSx α α.2).2⟩
    have hcard : (((P : Subgroup T) : Set T) \ {1}).ncard = 6 := by
      have h7 : ((P : Subgroup T) : Set T).ncard = 7 := by
        rw [← Nat.card_coe_set_eq]; exact hP7
      rw [Set.ncard_diff_singleton_of_mem (P : Subgroup T).one_mem, h7]
    exact hcard ▸ Set.ncard_le_ncard hsub
  have hS2card : Nat.card S2 ∣ 7 := by
    have hle : S2.map S.subtype ≤ M := by
      rintro _ ⟨α, hα, rfl⟩
      apply hkey
      intro g hg
      rw [← hxgen] at hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have hαx : (α : MulAut T) x = x := hα
      simp only [Subgroup.coe_subtype]
      rw [map_zpow, hαx]
    have := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective S.subtype_injective, hMcard] at this
    exact this
  have h1 := Subgroup.index_mul_card S
  have h2 := Subgroup.index_mul_card S2
  rw [hSidx] at h1
  have hS2pos : 0 < S2.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  intro h9
  rw [← h1, ← h2] at h9
  rcases (Nat.dvd_prime (by norm_num)).1 hS2card with hc | hc <;> rw [hc] at h9 <;>
    interval_cases (S2.index) <;> omega

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
