module

public import CFSG.GH74.GLS.C3.Layer1.Bk113aGen
public import CFSG.GH74.GLS.C3.Layer1.BkL113aSix

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem lemma113a_A7L
    (h81 : B_iv2_8_1) (h92 : B_lemma92) {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x : G}
    {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q) (p91 : Prop91Concl K M T Q)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hT : IsSylowOf 2 T ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T ≤ centralizer ({x} : Set G) := hh.sylowT.le
  have hT2 : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hh
  have hsK : IsSimpleGroup (kBar K) := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e7.isSimpleGroup
  have hnK : ∃ a b : kBar K, a * b ≠ b * a := exists_noncomm_of_equiv_A7 e7
  obtain ⟨eKL⟩ := hh.kBar_equiv
  have hsL : IsSimpleGroup (kBar L) := by
    have := hsK
    exact eKL.symm.isSimpleGroup
  have hnL : ∃ a b : kBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnK
    exact ⟨eKL a, eKL b, fun h => hab (eKL.injective (by rw [map_mul, map_mul]; exact h))⟩
  have heven : 2 ∣ Nat.card ↥K := by
    have h2520 : Nat.card (kBar K) = 2520 := by
      rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)]
    exact Dvd.dvd.mul_right (by rw [h2520]; norm_num) _
  have hKN := hh.K_normal hsL hnL heven
  obtain ⟨hR, hPQcomm, hPQ⟩ := hh.R_eq hsL hnL
  have hidx : ¬ 2 ∣ T.index := by
    have h := (isSylowOf_iff.1 hT).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hx2 : orderOf x = 2 := hh.orderOf_x
  have hxT : x ∈ T := hQT hh.x_mem_Q
  have hQCx : Q ≤ CxK x K := fun q hq => mem_CxK_of_mem_Q hh hq
  have hyp : Prop34HypN G x K :=
    { simple := hG.kproper.1
      nonab := hG.kproper.2.1
      central := ⟨hx2, hT2.toSylow hidx, by
        rw [IsPGroup.toSylow_coe hT2 hidx]; exact hxT,
        fun s hs => by
          rw [IsPGroup.toSylow_coe hT2 hidx] at hs
          exact mem_centralizer_singleton_iff.1 (hTC hs)⟩
      comp := hh.twoTerminal.1.2.2
      normal := hKN
      shape := Or.inr ⟨e7⟩
      sylowQ := ⟨Q, hh.sylowQ.of_le hQCx (CxK_le_CMK hh),
        Or.inr (isMaximalClassTwoGroup_of_four p91.1.1 p91.1.2)⟩ }
  have hinvR : ∀ u ∈ T, u * u = 1 → u ∈ (T ⊓ K) ⊔ Q := by
    intro u huT hu2
    by_contra hnot
    have hu1 : u ≠ 1 := fun h => hnot (h ▸ one_mem _)
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
    have huC : u ∈ centralizer ({x} : Set G) := hTC huT
    have hρ2 : (Back.actHom hKN ⟨u, huC⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨u, huC⟩ : ↥(centralizer ({x} : Set G))) ^ 2 = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [← hu2']
        exact pow_orderOf_eq_one u
      rw [this, map_one]
    have hρout : Back.actHom hKN ⟨u, huC⟩ ∉
        (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
      intro h
      apply hnot
      rw [← hR]
      exact ⟨huT, sup_le_sup hh.K_le_L (CxK_le_CMK hh)
        (mem_sup_of_actHom_mem_range hh.K_le_centralizer hKN huC h)⟩
    have hind : P34.InducesFAutL2A7 u K := by
      refine ⟨U1a.mem_normalizer_of_norm hKN huC, ?_⟩
      show P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨u, huC⟩)
      exact ⟨fun h1 => hρout (h1 ▸ Subgroup.one_mem _), Or.inr ⟨⟨e7⟩, hρout⟩⟩
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
  obtain ⟨⟨e5⟩, -⟩ := lemma112L h81 h92 hG hh p91 hcomm
  have h := Nat.card_congr (e5.symm.trans e7).toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  omega

end CFSG.GH74.GLS.C3.Layer1.Bk
