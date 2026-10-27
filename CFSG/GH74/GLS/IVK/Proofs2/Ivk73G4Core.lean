module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Cfg
public import CFSG.GH74.Generic.S45.LAltL2

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

omit [Finite N] in
theorem center_kbar_eq_bot
    (hc : HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) Odd ∨
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7))) :
    center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ := by
  rcases hc with hL2 | he
  · obtain ⟨hs, hnc, -⟩ := Generic.S45.LAlt.hasL2Model_data hL2
    have := hs
    exact LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have hncA : ∃ a b : ↥(alternatingGroup (Fin 7)), a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      exact C3.Layer1.Bk.alt_not_isSolvable 7 (Or.inr rfl)
        ((IsSimpleGroup.comm_iff_isSolvable (G := ↥(alternatingGroup (Fin 7)))).1 hc)
    have hcenA : center (alternatingGroup (Fin 7)) = ⊥ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncA).2
    have h1 := Subgroup.map_center_eq e
    rw [hcenA] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _
      (show Function.Injective e.toMonoidHom from e.injective)).1 h1

theorem Ivk73Cfg.kbar_cases
    (h : Ivk73Cfg N L K Q) :
    HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) Odd ∨
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨-, hU⟩ := h.K_u2
  rcases hU with h1 | h2 | ⟨hl, hel, hcard⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    obtain ⟨u, huQ, -, -, hu2, -, -, -⟩ := C3.Layer1.U1a.exists_commuting_involutions h.Q_rank
    have huC : u ∈ centralizer (K : Set N) := h.Q_sylow.le huQ
    have hcomp := h.terminal u hu2 huC
    have hev : 2 ∣ Nat.card ↥K := by
      have hc1 : Nat.card ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) = 20160 :=
        card_eq_of_lieModel_L34 hl
      have hd1 : Nat.card ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) ∣
          Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := Subgroup.card_quotient_dvd_card _
      have hd2 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
      have := hd1.trans hd2
      rw [hc1] at this
      exact (by norm_num : 2 ∣ 20160).trans this
    exact C3.Layer1.Bk.b_gen4_noL34_elem_proof N h.gen4 u K hu2
      (C3.Layer1.Bk.isPCompIn_two_of_isCompIn_of_even hcomp hev) ⟨hl, hel, hcard⟩

theorem odd_center_K
    (hc : HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) Odd ∨
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7))) :
    Odd (Nat.card (center ↥K)) := by
  have hZ := center_kbar_eq_bot hc
  have hle : center ↥K ≤ pPrimeCore 2 ↥K := by
    intro z hz
    have : (QuotientGroup.mk z : ↥K ⧸ pPrimeCore 2 ↥K) ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hz g']
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
    exact this
  exact Odd.of_dvd_nat (GLS.TwoThin.odd_card_pPrimeCore ↥K) (Subgroup.card_dvd_of_le hle)

theorem Ivk73Cfg.exists_V (h : Ivk73Cfg N L K Q) (hodd : Odd (Nat.card (center ↥K))) :
    ∃ V : Subgroup N, V ≤ K ∧ IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 4 := by
  obtain ⟨A, hA, hcard⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center h.K_quasi hodd)
  have hA' : IsElementaryAbelian 2 ↥A := (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).2 hA
  refine ⟨A.map K.subtype, fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨a, -, rfl⟩ := hx
    exact a.2
  · have := hA'
    exact IsElementaryAbelian.map K.subtype
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hcard

theorem Ivk73Cfg.exists_E (h : Ivk73Cfg N L K Q) :
    ∃ E : Subgroup N, E ≤ Q ∧ IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 := by
  obtain ⟨A, hA, hcard⟩ :=
    CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank (G := ↥Q) h.Q_rank
  refine ⟨A.map Q.subtype, fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨a, -, rfl⟩ := hx
    exact a.2
  · have := hA
    exact IsElementaryAbelian.map Q.subtype
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hcard]
    norm_num

theorem Ivk73Cfg.exists_rank_four
    (h : Ivk73Cfg N L K Q) : ∃ A : Subgroup N, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 16 := by
  have hc := h.kbar_cases
  have hodd := odd_center_K hc
  obtain ⟨V, hVK, hV, hVc⟩ := h.exists_V hodd
  obtain ⟨E, hEQ, hE, hEc⟩ := h.exists_E
  have hQ2 : IsPGroup 2 ↥Q := h.Q_sylow.isPGroup
  have hcd : Th2.CommDisj K Q := by
    refine ⟨fun p hp q hq => Subgroup.mem_centralizer_iff.1 (h.Q_sylow.le hq) p hp, ?_⟩
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxQ⟩
    have hxZ : (⟨x, hxK⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (h.Q_sylow.le hxQ) g g.2)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ2) ⟨x, hxQ⟩
    have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_mk x hxQ).symm.trans hk
    have hd : orderOf x ∣ Nat.card (center ↥K) := by
      have := orderOf_dvd_natCard (⟨⟨x, hxK⟩, hxZ⟩ : ↥(center ↥K))
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
    rw [hk'] at hd
    have hodd2 : Odd (2 ^ k) := Odd.of_dvd_nat hodd hd
    have hk0 : k = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.2 hodd2) (by simpa [Nat.even_pow] using hne)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
    rw [Subgroup.mem_bot]
    exact hk'
  refine ⟨V ⊔ E, hcd.isElementaryAbelian_sup' hV hE hVK hEQ, ?_⟩
  rw [hcd.card_sup hVK hEQ, hVc, hEc]

theorem Ivk73Cfg.exists_aut_rank_four
    (h : Ivk73Cfg N L K Q) :
    ∃ E : Subgroup (MulAut ↥L), (∀ e ∈ E, e * e = 1) ∧ Nat.card ↥E = 16 := by
  have := h.normal
  obtain ⟨A, hA, hcard⟩ := h.exists_rank_four
  let φ : N →* MulAut ↥L := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    apply h.cent_trivial n
    intro l hl
    have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨l, hl⟩ : ↥L) : N)) hn
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc n * l = n * l * n⁻¹ * n := by group
      _ = l * n := by rw [h1]
  have hsq : ∀ a : ↥A, a * a = 1 := fun a => by
    rw [← pow_two]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hA.exponent_dvd_p) a
  refine ⟨A.map φ, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have := congrArg Subtype.val (hsq ⟨a, ha⟩)
    rw [← map_mul]
    have h2 : a * a = 1 := this
    rw [h2, map_one]
  · rw [Subgroup.card_map_of_injective hφ]
    exact hcard

theorem Ivk73Cfg.false_of_autRank
    (h : Ivk73Cfg N L K Q)
    (hrank : ∀ E : Subgroup (MulAut ↥L), (∀ e ∈ E, e * e = 1) → Nat.card ↥E ≤ 8) : False := by
  obtain ⟨E, hE, hc⟩ := h.exists_aut_rank_four
  have := hrank E hE
  omega

end CFSG.GH74.GLS.IVK
