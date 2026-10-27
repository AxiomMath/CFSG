module

public import CFSG.LargeExtraspecial.S12DWCount
public import CFSG.LargeExtraspecial.S8FiveC
public import CFSG.LargeExtraspecial.S9GenB
public import CFSG.LargeExtraspecial.S9GenD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem card_omegaGroup_of_finrank_eight {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (h8 : finrank (ZMod 2) V = 8) :
    Nat.card (omegaGroup Q hQ) = 174182400 ∨ Nat.card (omegaGroup Q hQ) = 197406720 := by
  have hfin : finrank (ZMod 2) V = 2 * 4 := by rw [h8]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq hQ (m := 4) hfin
  have h2 := S12DW.card_orthogonalGroup_eq hQ
  have hc := S12DW.natCard_eq_four_pow (V := V) hfin
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have h3 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (S12DW.polar_eq_zero_imp hQ) hc
  have h4 := S12DW.ncard_eq_zero_eq Q
  have hP : 2 ^ (4 ^ 2) * ∏ j ∈ Finset.Icc 1 4, (2 ^ (2 * j) - 1) = 47377612800 := by decide
  rw [hP, h2] at h1
  rw [hc] at h4
  rcases h3 with h3 | h3
  · have hn : {v | Q v = 0}.ncard = 136 := by omega
    rw [hn] at h1
    left
    omega
  · have hn : {v | Q v = 0}.ncard = 120 := by omega
    rw [hn] at h1
    right
    omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem isPGroup_Nbar_of_nqHyp (H : Hyp4 S g) (ht : t ∈ S.Lbar g) [hN : NQHyp S g t] :
    IsPGroup 2 (Nbar S g t) := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  have hx := hN.sq x x.2
  have h4 : ((x : S.O) * x) * ((x : S.O) * x) = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers htt hx with h | h <;> rw [h]
    · exact one_mul 1
    · exact htt
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
  calc (x : S.O) ^ 4 = ((x : S.O) * x) * ((x : S.O) * x) := by
        rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc ((x : S.O) * x)]
    _ = 1 := h4

theorem not_thirtyone_dvd_card_Rbar (H : Hyp4 S g) (ht : t ∈ S.Lbar g) [NQHyp S g t]
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ) (h8 : finrank (ZMod 2) (Vt S g t) = 8) :
    ¬ 31 ∣ Nat.card (Rbar S g t) := by
  have haQ := H.conj_mem
  have hP := isPGroup_Nbar_of_nqHyp H ht (t := t)
  have hPk : IsPGroup 2 (resV haQ t).ker := fun x => by
    obtain ⟨k, hk⟩ := hP ⟨_, (resV_eq_one_iff haQ x.1).mp x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨a, ha⟩ := hPk.exists_card_eq
  have hrange : Nat.card (resV haQ t).range = Nat.card (omegaGroup Q hQ) := by
    rw [range_resV, hX]
  have hcard := Subgroup.card_mul_index (resV haQ t).ker
  rw [Subgroup.index_ker, hrange, ha] at hcard
  rw [← hcard]
  intro h31
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 31)).mp h31 with h | h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 31) h) (by norm_num)
  · rcases card_omegaGroup_of_finrank_eight hQ h8 with e | e <;> rw [e] at h <;>
      exact absurd h (by norm_num)

theorem exists_Rbar_normalizer_of_fix_aV (H : Hyp4 S g) (ht : t ∈ S.Lbar g)
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (heR : e ∈ RmodN S g t) (he : e (aV ht) = aV ht) :
    ∃ r : Rbar S g t, e = resV H.conj_mem t r ∧
      (r : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
  have haQ := H.conj_mem
  rw [← range_resV haQ t] at heR
  obtain ⟨r, hr⟩ := heR
  refine ⟨r, hr.symm, ?_⟩
  have hfix : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((1 : S.M) * g * S.z * ((1 : S.M) * g)⁻¹))
      = S.cl ((1 : S.M) * g * S.z * ((1 : S.M) * g)⁻¹) := by
    have h1 := congrArg Subtype.val (congrArg (fun φ => φ (aV ht)) hr)
    simp only [coe_resV_apply, he] at h1
    simpa [aV] using h1
  have := mem_normalizer_of_fix haQ H.conj_ne (h := 1) (Rbar_le_Mbar r.2) hfix
  simpa using this

theorem exists_move_Fbar (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m) [NQHyp S g t]
    (hFN : S9.conjL S g t ⊆ Nbar S g t) {f : S.O} (hf : f ∈ S9.Fbar S g t)
    (hft : f ∉ zpowers t) :
    ∃ r ∈ Rbar S g t ⊓ normalizer (S9.Fbar S g t : Set S.O), ∃ f' ∈ S9.Fbar S g t,
      (r * f' * r⁻¹)⁻¹ * f' ∉ zpowers t := by
  by_contra hcon
  push Not at hcon
  have haQ := H.conj_mem
  have hfN : f ∈ Nbar S g t := S9.Fbar_le_of_subset hFN hf
  obtain ⟨u, hu⟩ : ∃ u : NQ S g t, u = nqMk ⟨f, hfN⟩ := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := fun h => hft ((nqMk_eq_zero_iff _).mp (hu ▸ h))
  obtain ⟨U, hU⟩ : ∃ U : Submodule (ZMod 2) (NQ S g t), U = (ZMod 2) ∙ u := ⟨_, rfl⟩
  have hD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ D.hN0 D.hh D.hb D.hX D.hE
  have hUA : U ≤ ⊤ ⊓ S2.fixOf (nqRep S g t D.hX)
      (S2.radFix D.Q ⊥ (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
    rw [top_inf_eq, fixOf_nqRep_radFix_eq hNo D, hU, Submodule.span_singleton_le_iff_mem]
    exact ⟨⟨f, hfN⟩, S9.Fbar_le_Lbar hf, hu.symm⟩
  have hUinv : ∀ e : omegaGroup D.Q D.hQ, (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ S2.fixGroup ⊥ →
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (aV ht) = aV ht → ∀ v ∈ U, nqRep S g t D.hX e v ∈ U := by
    intro e _ he v hv
    have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by rw [D.hX]; exact e.2
    have hex := exists_Rbar_normalizer_of_fix_aV (t := t) H ht
      (e := (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t)) heR he
    obtain ⟨r, her, hrN⟩ := hex
    have hrF : (r : S.O) ∈ normalizer (S9.Fbar S g t : Set S.O) :=
      S9.mem_normalizer_Fbar_of_mem t (Rbar_le_Mbar r.2) hrN
    have hfix : nqRep S g t D.hX e u = u := by
      rw [hu, nqRep_apply D.hX her, nqMk_eq_iff, coe_nConj]
      exact hcon r ⟨r.2, hrF⟩ f hf
    rw [hU] at hv ⊢
    refine (S9.eq_zero_or_eq_of_mem_span_singleton hv).elim (fun h0 => ?_) (fun h0 => ?_)
    · rw [h0, map_zero]
      exact Submodule.zero_mem _
    · rw [h0, hfix]
      exact Submodule.mem_span_singleton_self u
  have hg₀R : resV haQ t ⟨S.ρ D.h, D.hh⟩ ∈ omegaGroup D.Q D.hQ := by
    rw [← D.hX, ← range_resV haQ t]; exact ⟨_, rfl⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : omegaGroup D.Q D.hQ, g₀ = ⟨_, hg₀R⟩ := ⟨_, rfl⟩
  have hg₀a : (g₀ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (aV ht) = bV (mem_Lbar_of_pair H ht D.hh) := by
    rw [hg₀]
    exact resV_aV haQ ht D.hh (mem_Lbar_of_pair H ht D.hh)
  have hF : (⊥ : Submodule (ZMod 2) (Vt S g t)) ⊓ S2.perp D.Q ⊥ = ⊥ := bot_inf_eq _
  have hdim : finrank (ZMod 2) (S2.perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t))) = 2 * D.m := by
    rw [S2.perp_bot, finrank_top, D.hdim]
  have hmem : ∀ v : Vt S g t, v ∈ S2.perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t)) := fun v => by
    rw [S2.perp_bot]; exact Submodule.mem_top
  have htop : S2.OmegaInvariant (nqRep S g t D.hX) ⊥ (⊤ : Submodule (ZMod 2) (NQ S g t)) :=
    fun _ _ _ _ => Submodule.mem_top
  have hfg : ∀ e : omegaGroup D.Q D.hQ,
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ S2.fixGroup (⊥ : Submodule (ZMod 2) (Vt S g t)) :=
    fun e => by rw [S2.fixGroup_bot]; exact mem_top _
  have h21c := S2.timmesfeld_2_1_c (nqRep S g t D.hX) hF D.hm hdim (Or.inl hm3) htop (hmem _)
    (hmem _) (aV_ne_zero H ht) D.hQa D.Q_bV D.polar_aV_bV hD hUA hUinv g₀ (hfg g₀) hg₀a
  obtain ⟨hdvd, -, -⟩ := dvd_and_two_mul_of_invariant (nqRep S g t D.hX) D.hm D.hdim
    (aV_ne_zero H ht) D.hQa D.Q_bV D.polar_aV_bV hD
    (N' := U ⊔ U.map (nqRep S g t D.hX g₀ : NQ S g t →ₗ[ZMod 2] NQ S g t))
    (fun e v hv => h21c e (hfg e) v hv)
  have hU1 : finrank (ZMod 2) U = 1 := by rw [hU]; exact finrank_span_singleton hu0
  have hU2 : finrank (ZMod 2) (U.map (nqRep S g t D.hX g₀ : NQ S g t →ₗ[ZMod 2] NQ S g t)) ≤ 1 :=
    (Submodule.finrank_map_le _ U).trans hU1.le
  have hle := Submodule.finrank_add_le_finrank_add_finrank U
    (U.map (nqRep S g t D.hX g₀ : NQ S g t →ₗ[ZMod 2] NQ S g t))
  have hpos : 0 < finrank (ZMod 2) ↥(U ⊔ U.map (nqRep S g t D.hX g₀ :
      NQ S g t →ₗ[ZMod 2] NQ S g t)) :=
    lt_of_lt_of_le (by omega) (Submodule.finrank_mono le_sup_left)
  have h4 : 4 ≤ 2 ^ (D.m - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (D.m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.LargeExtraspecial.S8
