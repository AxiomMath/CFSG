module

public import CFSG.GH74.GLS.C3.Layer1.BkP34N
public import CFSG.GH74.GLS.C3.Layer1.BkL113aK
public import CFSG.GH74.GLS.C3.Layer1.BkS4Hyp
public import CFSG.GH74.GLS.C3.Layer1.Back113

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem exists_noncomm_of_equiv_A7 {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 7)) :
    ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : IsMulCommutative (alternatingGroup (Fin 7)) := ⟨⟨fun a b => by
    have h := congrArg e (hcon (e.symm a) (e.symm b))
    simpa using h⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc
  simp at h3

theorem lemma113a_alt67
    (h112 : S_lemma112) {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x : G}
    {K M T Q : Subgroup G} (hh : Hyp9 x K K M T Q) (p91 : Prop91Concl K M T Q)
    (hn : Nonempty (kBar K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hT : IsSylowOf 2 T ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hh.a
  have hLn : ∀ m ∈ M, ∀ l ∈ K, m * l * m⁻¹ ∈ K := hA.L_normal.2
  have hTC : T ≤ centralizer ({x} : Set G) := hA.sylowT.le
  have hT2 : IsPGroup 2 ↥T := hA.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hA
  have hsn : IsSimpleGroup (kBar K) ∧ ∃ a b : kBar K, a * b ≠ b * a := by
    rcases hn with h6 | h7
    · obtain ⟨e⟩ := h6
      have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ⟨e.isSimpleGroup, exists_noncomm_of_equiv_A6 e⟩
    · obtain ⟨e⟩ := h7
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact ⟨e.isSimpleGroup, exists_noncomm_of_equiv_A7 e⟩
  obtain ⟨hs, hnab⟩ := hsn
  obtain ⟨hR, hPQcomm, hPQ⟩ := hA.R_eq hs hnab
  have hnoV2 : Nonempty (kBar K ≃* alternatingGroup (Fin 6)) →
      ¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' := by
    rintro ⟨e6⟩ ⟨x', y', K', hex⟩
    have h360 : Nat.card (kBar K) = 360 := by
      rw [Nat.card_congr e6.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rcases p91.2.2.2 ⟨x', y', K', hex⟩ with h5 | h7
    · have := card_eq_of_hasL2Model_five h5
      omega
    · obtain ⟨e7⟩ := h7
      have h2520 : Nat.card (kBar K) = 2520 := by
        rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
  have hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
    rcases hn with h6 | h7
    · left
      obtain ⟨q, hq, hqm⟩ := p91.2.2.1 (hnoV2 h6)
      refine hasL2Model_mono (fun r hr => ?_) hqm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      subst hr
      rcases hq with rfl | rfl | rfl <;> decide
    · exact Or.inr h7
  have hidx : ¬ 2 ∣ T.index := by
    have h := (isSylowOf_iff.1 hT).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hx2 : orderOf x = 2 := hA.orderOf_x
  have hxT : x ∈ T := hQT hA.x_mem_Q
  have hyp : Prop34HypN G x K :=
    { simple := hG.kproper.1
      nonab := hG.kproper.2.1
      central := ⟨hx2, hT2.toSylow hidx, by
        rw [IsPGroup.toSylow_coe hT2 hidx]; exact hxT,
        fun s hs => by
          rw [IsPGroup.toSylow_coe hT2 hidx] at hs
          exact mem_centralizer_singleton_iff.1 (hTC hs)⟩
      comp := hA.twoTerminal.1.2.2
      normal := fun c hc k hk => hLn c (hA.centralizer_le hc) k hk
      shape := hshape
      sylowQ := ⟨Q, by
        refine hA.sylowQ.of_le (fun q hq => ⟨hTC (hQT hq), (hA.sylowQ.le hq).2⟩) ?_
        exact fun g hg => ⟨hA.centralizer_le hg.1, hg.2⟩,
        Or.inr (isMaximalClassTwoGroup_of_four p91.1.1 p91.1.2)⟩ }
  have hinvR : ∀ u ∈ T, u * u = 1 → u ∈ (T ⊓ K) ⊔ Q := by
    intro u huT hu2
    by_contra hnot
    have hu1 : u ≠ 1 := fun h => hnot (h ▸ one_mem _)
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
    have huC : u ∈ centralizer ({x} : Set G) := hTC huT
    have huM : u ∈ M := hA.centralizer_le huC
    have hρ2 : (Back.actHom hLn ⟨u, huM⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨u, huM⟩ : ↥M) ^ 2 = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [← hu2']
        exact pow_orderOf_eq_one u
      rw [this, map_one]
    have hρout : Back.actHom hLn ⟨u, huM⟩ ∉
        (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
      intro h
      apply hnot
      rw [← hR]
      exact ⟨huT, mem_sup_of_actHom_mem_range hA.L_normal.1 hLn huM h⟩
    have hind : P34.InducesFAutL2A7 u K := by
      refine ⟨U1a.mem_normalizer_of_norm hLn huM, ?_⟩
      show P34.IsFAutL2A7 (kBar K) (Back.actHom hLn ⟨u, huM⟩)
      rcases hn with h6 | h7
      · obtain ⟨e6⟩ := h6
        rcases involution_trichotomy_alt6 e6 hρ2 with h | ⟨h3, hodd⟩ | h
        · exact absurd h hρout
        · exfalso
          have hne : IVK.xu (Back.actHom hLn ⟨u, huM⟩) ≠ ⊥ := by
            intro h0
            rw [h0, Subgroup.card_bot] at h3
            omega
          have h360 : Nat.card (kBar K) = 360 := by
            rw [Nat.card_congr e6.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
            simp [Nat.factorial]
          have hL34 : ¬ IsL34Quotient (kBar K) :=
            not_isL34Quotient_of_card_lt (by rw [h360]; norm_num)
          exact hnoV2 ⟨e6⟩ ⟨x, u, K, isV2Triple_of_xu hA hs hL34 huC hu2' ⟨hne, hodd⟩⟩
        · exact h
      · exact ⟨fun h1 => hρout (h1 ▸ Subgroup.one_mem _), Or.inr ⟨h7, hρout⟩⟩
    exact prop34N_false hyp huC hu2' hind
  have hcomm : ∀ q ∈ Q, ∀ t ∈ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q := by
    intro q hq t ht
    have hR' : (T ⊓ K) ⊔ Q ≤ centralizer ({q} : Set G) :=
      sup_le (fun p hp => mem_centralizer_singleton_iff.2 (hPQcomm p hp q hq))
        (fun q' hq' => mem_centralizer_singleton_iff.2
          ((forall_of_isElementaryAbelian p91.1.1).1 q' hq' q hq))
    have hle : Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} ≤ centralizer ({q} : Set G) := by
      rw [Subgroup.closure_le]
      intro u hu
      exact hR' (hinvR u hu.1 hu.2)
    exact (mem_centralizer_singleton_iff.1 (hle ht)).symm
  rcases h112 G hG x K K M T Q hh p91 rfl hcomm with ⟨-, u, huT, hu2, hind⟩ | ⟨⟨e5⟩, -, -⟩
  · exact prop34N_false hyp (hTC huT) hu2 hind
  · rcases hn with h6 | h7
    · obtain ⟨e6⟩ := h6
      exact card_alt_five_ne_six (e5.symm.trans e6)
    · obtain ⟨e7⟩ := h7
      have h := Nat.card_congr (e5.symm.trans e7).toEquiv
      have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
      have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
      omega

end CFSG.GH74.GLS.C3.Layer1.Bk
