module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63QCen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Idx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Def

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {D : Data} {k : ℕ} {G : Type} [Group G] {P Q : Subgroup G} {Θ : ℕ → G}

theorem y63_U (hΘ : Y63Model D k P Q Θ) (hC : D.CenSpec k) (hU : D.USpec k) :
    ∃ U : Subgroup G, U ≤ Q ∧ Y63ZE64 (cen Q) U ∧
      (∀ U' : Subgroup G, U' ≤ Q → Y63ZE64 (cen Q) U' → U' = U) ∧
      ∀ g : G, g ∈ U ↔ ∃ a ∈ D.u0 k, Θ a = g := by
  classical
  have hU' := hU
  obtain ⟨hu_nd, hu_len, hu_lt, hu0, huz, hucl, huinv, husq, hucz, -⟩ := hU'
  have hz_lt : D.z < 1024 := hC.1
  have hmul' : ∀ i < 1024, ∀ j < 1024, Θ i * Θ j = Θ (D.mq k i j) :=
    fun i hi j hj => (hΘ.mul i hi j hj).symm
  let U : Subgroup G :=
    { carrier := {g | ∃ a ∈ D.u0 k, Θ a = g}
      one_mem' := ⟨0, hu0, hΘ.one⟩
      mul_mem' := by
        rintro g hg h hh
        obtain ⟨a, ha, rfl⟩ := h
        obtain ⟨b, hb, rfl⟩ := hh
        exact ⟨D.mq k a b, hucl a ha b hb, (hmul' a (hu_lt a ha) b (hu_lt b hb)).symm⟩
      inv_mem' := by
        rintro g ⟨a, ha, rfl⟩
        obtain ⟨b, hb, hb0⟩ := huinv a ha
        refine ⟨b, hb, ?_⟩
        exact eq_inv_of_mul_eq_one_right (by
          rw [hmul' a (hu_lt a ha) b (hu_lt b hb), hb0, hΘ.one]) }
  have hUmem : ∀ g : G, g ∈ U ↔ ∃ a ∈ D.u0 k, Θ a = g := fun _ => Iff.rfl
  have hcardU : Nat.card ↥U = 128 := by
    let f : {a // a ∈ D.u0 k} → ↥U := fun a => ⟨Θ a.1, ⟨a.1, a.2, rfl⟩⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      have hval : Θ a.1 = Θ b.1 := congrArg Subtype.val hab
      exact Subtype.ext (hΘ.inj a.1 (hu_lt a.1 a.2) b.1 (hu_lt b.1 b.2) hval)
    have hf_surj : Function.Surjective f := by
      intro g
      obtain ⟨a, ha, hg⟩ := g.2
      exact ⟨⟨a, ha⟩, Subtype.ext hg⟩
    have h1 : Nat.card {a // a ∈ D.u0 k} = Nat.card ↥U :=
      Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
    have h2 : Nat.card {a // a ∈ D.u0 k} = Nat.card ↥((D.u0 k).toFinset) :=
      Nat.card_congr
        { toFun := fun a => ⟨a.1, List.mem_toFinset.mpr a.2⟩
          invFun := fun a => ⟨a.1, List.mem_toFinset.mp a.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [← h1, h2, Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup hu_nd, hu_len]
  have hZcard : Nat.card ↥U = 2 ^ 7 := by rw [hcardU]; norm_num
  refine ⟨U, ?_, ⟨?_, hZcard, ?_, ?_⟩, ?_, hUmem⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact hΘ.mem a (hu_lt a ha)
  · intro g hg
    rcases (y63_mem_cen hΘ hC g).mp hg with rfl | rfl
    · exact ⟨0, hu0, hΘ.one⟩
    · exact ⟨D.z, huz, rfl⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [pow_two, hmul' a (hu_lt a ha) a (hu_lt a ha)]
    have hsq := husq a ha
    unfold Data.sqz at hsq
    rcases hsq with h | h
    · rw [h, hΘ.one]
      exact (y63_mem_cen hΘ hC 1).mpr (Or.inl rfl)
    · rw [h]
      exact (y63_mem_cen hΘ hC (Θ D.z)).mpr (Or.inr rfl)
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have halt : a < 1024 := hu_lt a ha
    have hblt : b < 1024 := hu_lt b hb
    have hcz := hucz a ha b hb
    unfold Data.cz at hcz
    rcases hcz with h | h
    · refine (y63_mem_cen hΘ hC ⁅Θ a, Θ b⁆).mpr (Or.inl ?_)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (by
        rw [hmul' a halt b hblt, hmul' b hblt a halt, h])
    · refine (y63_mem_cen hΘ hC ⁅Θ a, Θ b⁆).mpr (Or.inr ?_)
      have hxy : Θ a * Θ b = Θ D.z * (Θ b * Θ a) := by
        rw [hmul' a halt b hblt, h,
          ← hmul' D.z hz_lt (D.mq k b a) (hΘ.mq_lt b hblt a halt),
          hmul' b hblt a halt]
      rw [commutatorElement_def]
      calc Θ a * Θ b * (Θ a)⁻¹ * (Θ b)⁻¹
          = Θ D.z * (Θ b * Θ a) * (Θ a)⁻¹ * (Θ b)⁻¹ := by rw [hxy]
        _ = Θ D.z := by group
  · intro U' hU'Q hZ'
    obtain ⟨-, hZ'card, hZ'sq, hZ'comm⟩ := hZ'
    let A : Finset ℕ := (Finset.range 1024).filter (fun i => Θ i ∈ U')
    have hAcard : A.card = 128 := by
      let f : ↥A → ↥U' := fun i => ⟨Θ i.1, (Finset.mem_filter.mp i.2).2⟩
      have hf_inj : Function.Injective f := by
        intro i j hij
        have hval : Θ i.1 = Θ j.1 := congrArg Subtype.val hij
        exact Subtype.ext (hΘ.inj i.1 (Finset.mem_range.mp (Finset.mem_filter.mp i.2).1)
          j.1 (Finset.mem_range.mp (Finset.mem_filter.mp j.2).1) hval)
      have hf_surj : Function.Surjective f := by
        intro g
        obtain ⟨i, hi, hig⟩ := hΘ.surj g.1 (hU'Q g.2)
        refine ⟨⟨i, ?_⟩, Subtype.ext hig⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, by rw [hig]; exact g.2⟩
      have h1 : Nat.card ↥A = A.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      have h2 : Nat.card ↥A = Nat.card ↥U' :=
        Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
      have h3 : Nat.card ↥U' = 128 := by rw [hZ'card]; norm_num
      rw [← h1, h2, h3]
    have hltA : ∀ a ∈ A, a < 1024 :=
      fun a ha => Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hsqA : ∀ a ∈ A, D.sqz k a := by
      intro a ha
      have halt : a < 1024 := hltA a ha
      have ha' : Θ a ∈ U' := (Finset.mem_filter.mp ha).2
      have hs : (Θ a) ^ 2 ∈ cen Q := hZ'sq (Θ a) ha'
      have h2 : (Θ a) ^ 2 = Θ (D.mq k a a) := by rw [pow_two, hmul' a halt a halt]
      unfold Data.sqz
      rcases (y63_mem_cen hΘ hC ((Θ a) ^ 2)).mp hs with h | h
      · left
        exact hΘ.inj (D.mq k a a) (hΘ.mq_lt a halt a halt) 0 (by norm_num)
          (by rw [← h2, h, hΘ.one])
      · right
        exact hΘ.inj (D.mq k a a) (hΘ.mq_lt a halt a halt) D.z hz_lt (by rw [← h2, h])
    have hcA : ∀ a ∈ A, ∀ b ∈ A, D.cz k a b := by
      intro a ha b hb
      have halt : a < 1024 := hltA a ha
      have hblt : b < 1024 := hltA b hb
      have ha' : Θ a ∈ U' := (Finset.mem_filter.mp ha).2
      have hb' : Θ b ∈ U' := (Finset.mem_filter.mp hb).2
      have hmem : ⁅Θ a, Θ b⁆ ∈ cen Q := hZ'comm (commutator_mem_commutator ha' hb')
      unfold Data.cz
      rcases (y63_mem_cen hΘ hC ⁅Θ a, Θ b⁆).mp hmem with h | h
      · left
        refine hΘ.inj (D.mq k a b) (hΘ.mq_lt a halt b hblt) (D.mq k b a)
          (hΘ.mq_lt b hblt a halt) ?_
        rw [← hmul' a halt b hblt, ← hmul' b hblt a halt]
        exact commutatorElement_eq_one_iff_mul_comm.mp h
      · right
        have hxy : Θ a * Θ b = Θ D.z * (Θ b * Θ a) := by
          rw [commutatorElement_def] at h
          calc Θ a * Θ b = Θ a * Θ b * (Θ a)⁻¹ * (Θ b)⁻¹ * (Θ b * Θ a) := by group
            _ = Θ D.z * (Θ b * Θ a) := by rw [h]
        refine hΘ.inj (D.mq k a b) (hΘ.mq_lt a halt b hblt)
          (D.mq k D.z (D.mq k b a)) (hΘ.mq_lt D.z hz_lt (D.mq k b a)
            (hΘ.mq_lt b hblt a halt)) ?_
        rw [← hmul' a halt b hblt, hxy,
          ← hmul' D.z hz_lt (D.mq k b a) (hΘ.mq_lt b hblt a halt),
          ← hmul' b hblt a halt]
    have hA_u0 : ∀ a ∈ A, a ∈ D.u0 k := y63_idx_U D hU hAcard hltA hsqA hcA
    have hle : U' ≤ U := by
      intro g hg
      obtain ⟨i, hi, hig⟩ := hΘ.surj g (hU'Q hg)
      exact ⟨i, hA_u0 i (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hi, by rw [hig]; exact hg⟩), hig⟩
    haveI : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, hZ'card])

end CFSG.OddStandard.HigherRank.YamadaG23
