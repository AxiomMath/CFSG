module

public import CFSG.GH74.GLS.C3.Layer1.Back91Core
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

theorem isFM9_odd {q : ℕ} (h : IsFM9 q) : Odd q := by
  rcases h with rfl | ⟨hp, ⟨k, hk⟩ | ⟨n, hn⟩⟩
  · decide
  · subst hk
    have : Even (2 ^ 2 ^ k) := (Nat.even_pow.2 ⟨even_two, by positivity⟩)
    exact this.add_one
  · have hn0 : n ≠ 0 := by
      rintro rfl
      have : q = 0 := by omega
      exact hp.ne_zero this
    have : Even (q + 1) := by rw [hn]; exact (Nat.even_pow.2 ⟨even_two, hn0⟩)
    exact Nat.odd_iff.2 (by obtain ⟨r, hr⟩ := this; omega)

variable {G : Type} [Group G] [Finite G]

theorem hasL2Model_mono {K : Type} [Group K] {P P' : ℕ → Prop} (hPP : ∀ q, P q → P' q)
    (h : HasL2Model K P) : HasL2Model K P' := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  exact ⟨p, f, hp, hf, hPP _ hP, hL⟩

theorem isSimpleGroup_of_hasL2Model
    {K : Type} [Group K] {P : ℕ → Prop} (h : HasL2Model K P) :
    IsSimpleGroup K := by
  obtain ⟨p, f, -, -, -, hL⟩ := h
  exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL

theorem isSimpleGroup_of_alt7 {K : Type} [Group K] (h : Nonempty (K ≃* alternatingGroup (Fin 7))) :
    IsSimpleGroup K := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

theorem nonab_of_quasisimple {K : Type} [Group K] (h : IsQuasisimple K) : ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, -, a', b', hab'⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  refine ⟨a, b, fun h => hab' ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]


theorem hasL2Model_kBar_of_B2
    {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q)
    (hB2 : Hyp9B2 x K M T Q) : HasL2Model (kBar K) Odd := by
  have hqs : IsQuasisimple (kBar K) := TwoThin.isQuasisimple_hat hh.twoTerminal.1.2.2
  have hnon := nonab_of_quasisimple hqs
  have hK := hB2.isL2
  have hKs : IsSimpleGroup ↥K := isSimpleGroup_of_hasL2Model hK
  have hbot : pPrimeCore 2 ↥K = ⊥ := by
    rcases hKs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnon
      apply hab
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [h]; exact Subgroup.mem_top _
  have e : ↥K ≃* kBar K :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm))
  exact hasL2Model_mono (fun q hq => isFM9_odd hq) (TwoThin.hasL2Model_of_mulEquiv e hK)

theorem kBar_facts
    {x : G} {K L M T Q : Subgroup G} (hG : C3Hyp G) (hh : Hyp9 x K L M T Q)
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) :
    (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) ∧
      IsSimpleGroup (kBar K) ∧ ∃ a b : kBar K, a * b ≠ b * a := by
  have hqs : IsQuasisimple (kBar K) := TwoThin.isQuasisimple_hat hh.a.twoTerminal.1.2.2
  have hnon := nonab_of_quasisimple hqs
  have hlist : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
    rcases hh.b with hB1 | hB2
    · obtain ⟨y, hy⟩ := hB1.v2star
      have hlu : IsLocallyUnbalancing x y K := hy.1.1.1.1.1
      obtain ⟨-, hU⟩ := h102 G hG x y K hlu
      rcases hU with h | h | ⟨h34, hab, hcard⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ⟨h34, hab, hcard⟩
          (hL34 G hG.gen4 x K hh.a.orderOf_x hh.a.twoTerminal.1.2.2)
    · exact Or.inl (hasL2Model_kBar_of_B2 hh.a hB2)
  have hsimple : IsSimpleGroup (kBar K) := by
    rcases hlist with h | h
    · exact isSimpleGroup_of_hasL2Model h
    · exact isSimpleGroup_of_alt7 h
  exact ⟨hlist, hsimple, hnon⟩

theorem s_prop91_of
    (h81 : B_iv2_8_1) (h92 : B_lemma92) (h102 : B_ivk_10_2) (h102a : B_ivk_10_2a)
    (hL34 : B_gen4_noL34_elem) (hPGL : B_prop91_PGL) : S_prop91 := by
  intro G _ _ hG x K L M T Q hh
  obtain ⟨hlistK, hsK, hnK⟩ := kBar_facts hG hh h102 hL34
  obtain ⟨eKL⟩ := hh.a.kBar_equiv
  have hsL : IsSimpleGroup (kBar L) := (MulEquiv.isSimpleGroup_congr eKL).1 hsK
  have hnL : ∃ a b : kBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnK
    refine ⟨eKL a, eKL b, fun h => hab ?_⟩
    apply eKL.injective
    rw [map_mul, map_mul]; exact h
  have hlistL : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)) := by
    rcases hlistK with h | h
    · exact Or.inl (TwoThin.hasL2Model_of_mulEquiv eKL h)
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨eKL.symm.trans e⟩
  obtain ⟨hR, hcomm, hPQ⟩ := hh.a.R_eq hsL hnL
  obtain ⟨hQ, ⟨g, hgM, hgQM, hLg, hgR, hgQ⟩, hq⟩ :=
    prop91_ab_core hh.a hG.kproper.1 hG.kproper.2.1 hG.kproper hsL hnL hlistL hR hcomm hPQ h81 h92
  have hqK : HasL2Model (kBar K) Odd →
      ∃ q ∈ ({5, 7, 9} : Finset ℕ), HasL2Model (kBar K) (fun r => r = q) := by
    intro h
    obtain ⟨q, hq5, hqm⟩ := hq (TwoThin.hasL2Model_of_mulEquiv eKL h)
    exact ⟨q, hq5, TwoThin.hasL2Model_of_mulEquiv eKL.symm hqm⟩
  have hQc : CFSG.IsElementaryAbelian 2 ↥(conjugate Q g) ∧ Nat.card ↥(conjugate Q g) = 4 :=
    ⟨isElementaryAbelian_conjugate hQ.1 g, by rw [card_conjugate']; exact hQ.2⟩
  refine ⟨hQ, ⟨g, hgM, hgR, hgQ⟩, ?_, ?_⟩
  ·
    intro hno
    rcases hh.b with hB1 | hB2
    · obtain ⟨y, hy⟩ := hB1.v2star
      exact absurd ⟨x, y, K, hy.1.1.1.1⟩ hno
    · exact hqK (hasL2Model_kBar_of_B2 hh.a hB2)
  ·
    intro hex
    rcases hh.b with hB1 | hB2
    · obtain ⟨y, hy⟩ := hB1.v2star
      have hV2 : IsV2Triple x y K := hy.1.1.1.1
      rcases hlistK with h | h
      · obtain ⟨q, hq5, hqm⟩ := hqK h
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq5
        rcases hq5 with rfl | rfl | rfl
        · exact Or.inl hqm
        · have hout := h102a G hG x y K hV2 (hasL2Model_mono (fun r hr => by
            subst hr; exact Or.inr ⟨by norm_num, Or.inr ⟨3, by norm_num⟩⟩) hqm)
          exact (hPGL G hG x y K L M T Q g hh.a hV2 hout
            (hasL2Model_mono (fun r hr => Or.inl hr) hqm) hgM hgQM hLg hQc hgR hgQ).elim
        · have hout := h102a G hG x y K hV2 (hasL2Model_mono (fun r hr => by
            subst hr; exact Or.inl rfl) hqm)
          exact (hPGL G hG x y K L M T Q g hh.a hV2 hout
            (hasL2Model_mono (fun r hr => Or.inr hr) hqm) hgM hgQM hLg hQc hgR hgQ).elim
      · exact Or.inr h
    · obtain ⟨x', y', K', h'⟩ := hex
      exact absurd ⟨x', y', K', h'⟩ hB2.noV2

end CFSG.GH74.GLS.C3.Layer1.Back
