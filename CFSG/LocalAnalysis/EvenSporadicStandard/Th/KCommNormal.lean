module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommFun
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommAbelian
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.actFn_invariant_conj (q : ↥(normalizer ((W5 A t : Subgroup G) : Set G)))
    (f : ↥(Fnl A Aa t)) (h : actFn H W W2 q f = f) (y : G) :
    f.1 ((q : G) * y * (q : G)⁻¹) = f.1 y := by
  have := congrArg (fun g : ↥(Fnl A Aa t) => g.1 ((q : G) * y * (q : G)⁻¹)) h
  simp only [actFn_apply] at this
  have e : (q : G)⁻¹ * ((q : G) * y * (q : G)⁻¹) * q = y := by group
  rw [e] at this
  exact this.symm

theorem ThCyc.exists_invariant_functional :
    ∃ f : G → ZMod 2, f ∈ Fnl A Aa t ∧ f t = 1 ∧
      ∀ q ∈ normalizer ((W5 A t : Subgroup G) : Set G), ∀ y, f (q * y * q⁻¹) = f y := by
  classical
  obtain ⟨k, c, j, hkL, hkA, hodd, hfix, hj, hcmul, hcinj, hconto, hck⟩ :=
    exists_singer_coord (L := L) W.A_comm W.A_sq W.A_card W.surj
  have hc : IsCoord A c := ⟨hcmul, hcinj, hconto⟩
  have hNA : ∀ q ∈ normalizer ((W5 A t : Subgroup G) : Set G), ∀ a ∈ A, q * a * q⁻¹ ∈ A :=
    fun q hq a ha => H.normalizer_W5_conj_mem W hq ha
  obtain ⟨m, hm⟩ := hc.exists_matHom (normalizer ((W5 A t : Subgroup G) : Set G)) hNA
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (singerMat ^ j) ^ i = singerMat := by
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨8, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨2, by decide⟩
  have hkiA : ∀ x ∈ A, k ^ i * x * (k ^ i)⁻¹ ∈ A := conj_pow_mem (C := A) hkA i
  have hrepk : IsRep A c (k ^ i) singerMat := by
    have := (show IsRep A c k (singerMat ^ j) from hck).pow hkA i
    rwa [hi] at this
  have hkiN : k ^ i ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_L W (pow_mem hkL i) hkiA
  let kS : ↥(normalizer ((W5 A t : Subgroup G) : Set G)) := ⟨k ^ i, hkiN⟩
  have hkS : m kS = singerMat := hc.rep_unique (hm kS) hrepk
  have hkSodd : Odd (orderOf kS) := by
    have h1 : orderOf kS = orderOf (k ^ i) := (Subgroup.orderOf_coe kS).symm
    rw [h1]
    exact hodd.of_dvd_nat (orderOf_pow_dvd i)
  obtain ⟨nT, hnTL, hnTA, hrepT⟩ := hc.exists_lift W.surj (M := gl4T) gl4T_mulVec_injective
  obtain ⟨nN, hnNL, hnNA, hrepN⟩ := hc.exists_lift W.surj (M := gl4N) gl4N_mulVec_injective
  let qT : ↥(normalizer ((W5 A t : Subgroup G) : Set G)) :=
    ⟨nT, H.mem_normalizer_W5_of_L W hnTL hnTA⟩
  let qn : ↥(normalizer ((W5 A t : Subgroup G) : Set G)) :=
    ⟨nN, H.mem_normalizer_W5_of_L W hnNL hnNA⟩
  have hqT : m qT = gl4T := hc.rep_unique (hm qT) hrepT
  have hqn : m qn = gl4N := hc.rep_unique (hm qn) hrepN
  have hker : ∀ q q' : ↥(normalizer ((W5 A t : Subgroup G) : Set G)), m q = m q' →
      ∀ f, actFn H W W2 q f = actFn H W W2 q' f := by
    intro q q' hqq f
    have hr : (q : G)⁻¹ * q' ∈ Bp A t := by
      refine ⟨mem_centralizer_iff.2 fun a ha => ?_,
        (normalizer _).mul_mem ((normalizer _).inv_mem q.2) q'.2⟩
      have h' : IsRep A c (q' : G) (m q) := by
        rw [hqq]
        exact hm q'
      have h1 := (hm q).conj_mem hc (hNA q q.2) (hNA q' q'.2) h' ha
      calc a * ((q : G)⁻¹ * q') = (q : G)⁻¹ * ((q : G) * a * (q : G)⁻¹) * q' := by group
        _ = (q : G)⁻¹ * ((q' : G) * a * (q' : G)⁻¹) * q' := by rw [h1]
        _ = (q : G)⁻¹ * q' * a := by group
    have hr0 : actFn H W W2 (q⁻¹ * q') f = f :=
      Subtype.ext (funext fun y => H.fn_conj_Bp W W2 hr f.2 y)
    calc actFn H W W2 q f = actFn H W W2 q (actFn H W W2 (q⁻¹ * q') f) := by rw [hr0]
      _ = actFn H W W2 (q * (q⁻¹ * q')) f := (actFn_mul H W W2 _ _ _).symm
      _ = actFn H W W2 q' f := by rw [mul_inv_cancel_left]
  let ev : ↥(Fnl A Aa t) →+ ZMod 2 := AddMonoidHom.mk' (fun f => f.1 t) (fun f g => rfl)
  have hev : ∀ q v, ev (actFn H W W2 q v) = ev v := fun q v => H.fn_conj_t W W2 q.2 v.2
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ↥(Fnl A Aa t), ev v₀ = 1 := by
    have hN := H.Aa_subgroupOf_normal W W2
    obtain ⟨ψ, hψ⟩ := exists_hom_tauE_ne_one H W W2
    let f : G → ZMod 2 := fun x =>
      if h : x ∈ Csub A Aa t then Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨x, h⟩)) else 0
    have hf : f ∈ Fnl A Aa t := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · simp only [f, dite_eq_left hx, dite_eq_left hy,
          dite_eq_left ((Csub A Aa t).mul_mem hx hy)]
        have : (QuotientGroup.mk ⟨x * y, (Csub A Aa t).mul_mem hx hy⟩ : Equot A Aa t) =
            QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hy⟩ := rfl
        rw [this, map_mul, toAdd_mul]
      · simp only [f, dite_eq_right hx]
      · have hxC : x ∈ Csub A Aa t := H.Aa_le_inf_centralizer_Aa W W2 hx
        simp only [f, dite_eq_left hxC]
        have : (QuotientGroup.mk ⟨x, hxC⟩ : Equot A Aa t) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hx)
        rw [this, map_one]
        rfl
    refine ⟨⟨f, hf⟩, ?_⟩
    show f t = 1
    simp only [f, dite_eq_left (H.t_mem_inf_centralizer_Aa W W2)]
    have h0 : Multiplicative.toAdd (ψ (tauE H W W2)) ≠ 0 := fun h =>
      hψ (Multiplicative.toAdd.injective (by simpa using h))
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ h0
  have hunique : ∀ v : ↥(Fnl A Aa t), ev v = 0 → actFn H W W2 (kS ^ 5) v = v → v = 0 := by
    intro v hv hinv
    have hk5L : (k ^ i) ^ 5 ∈ L := pow_mem (pow_mem hkL i) 5
    have hk5A : ∀ x ∈ A, (k ^ i) ^ 5 * x * ((k ^ i) ^ 5)⁻¹ ∈ A := conj_pow_mem (C := A) hkiA 5
    have hrep5 : IsRep A c ((k ^ i) ^ 5) (singerMat ^ 5) := hrepk.pow hkiA 5
    have hinv' := H.actFn_invariant_conj W W2 (kS ^ 5) v hinv
    exact Subtype.ext (H.fn_eq_zero_of_invariant W W2 hc hk5L hk5A hrep5 v.2 hv
      (fun y => hinv' y))
  obtain ⟨v, hv1, hvfix⟩ := exists_fixed_of_gl4 (actFn H W W2) (actFn_one H W W2)
    (actFn_mul H W W2) (actFn_add H W W2) m hker ev hev hv₀ kS qT qn hkSodd hkS hqT hqn hunique
  exact ⟨v.1, v.2, hv1, fun q hq y => H.actFn_invariant_conj W W2 ⟨q, hq⟩ v (hvfix ⟨q, hq⟩) y⟩

theorem ThCyc.exists_kCommutator_normal :
    ∃ k ∈ L, (∀ x ∈ A, k * x * k⁻¹ ∈ A) ∧ Odd (orderOf k) ∧
      (∀ x ∈ A, k * x * k⁻¹ = x → x = 1) ∧
      (∀ x ∈ kCommutator (Csub A Aa t) k, ∀ y ∈ kCommutator (Csub A Aa t) k, x * y = y * x) ∧
      Aa ≤ kCommutator (Csub A Aa t) k ∧
      kCommutator (Csub A Aa t) k ⊔ zpowers t = Csub A Aa t ∧
      Disjoint (kCommutator (Csub A Aa t) k) (zpowers t) ∧
      Nat.card (kCommutator (Csub A Aa t) k) = 2 ^ 12 ∧
      ∀ n ∈ normalizer ((W5 A t : Subgroup G) : Set G), ∀ x ∈ kCommutator (Csub A Aa t) k,
        n * x * n⁻¹ ∈ kCommutator (Csub A Aa t) k := by
  obtain ⟨k, hkL, hkA, hodd, hfix, hab, hAa, hsup, hdisj, hcard⟩ :=
    H.exists_kCommutator_abelian W W2
  refine ⟨k, hkL, hkA, hodd, hfix, hab, hAa, hsup, hdisj, hcard, ?_⟩
  obtain ⟨f, hf, hft, hfN⟩ := H.exists_invariant_functional W W2
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hDC, -⟩ := H.kCommutator_factorization W W2 (C := Csub A Aa t) rfl hkL hkA hodd hfix
  have hf0 : f 1 = 0 := by
    have := hf1 1 (Csub A Aa t).one_mem 1 (Csub A Aa t).one_mem
    rw [mul_one] at this
    exact (add_eq_left.1 this.symm)
  let D' : Subgroup G :=
    { carrier := {x | x ∈ Csub A Aa t ∧ f x = 0}
      mul_mem' := by
        rintro x y ⟨hx, hfx⟩ ⟨hy, hfy⟩
        exact ⟨(Csub A Aa t).mul_mem hx hy, by rw [hf1 x hx y hy, hfx, hfy, add_zero]⟩
      one_mem' := ⟨(Csub A Aa t).one_mem, hf0⟩
      inv_mem' := by
        rintro x ⟨hx, hfx⟩
        refine ⟨(Csub A Aa t).inv_mem hx, ?_⟩
        have := hf1 x hx x⁻¹ ((Csub A Aa t).inv_mem hx)
        rw [mul_inv_cancel, hf0, hfx, zero_add] at this
        exact this.symm }
  have hD'C : D' ≤ Csub A Aa t := fun x hx => hx.1
  have hkD' : kCommutator (Csub A Aa t) k ≤ D' := by
    refine (closure_le _).2 ?_
    rintro _ ⟨c, hc, a, ha, rfl⟩
    have hkN : k ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
      H.mem_normalizer_W5_of_L W hkL hkA
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have haN : k ^ j ∈ normalizer ((W5 A t : Subgroup G) : Set G) := zpow_mem hkN j
    have hacC : k ^ j * c * (k ^ j)⁻¹ ∈ Csub A Aa t :=
      H.conj_mem_inf_centralizer_Aa W W2 haN hc
    refine ⟨(Csub A Aa t).mul_mem ((Csub A Aa t).inv_mem hc) hacC, ?_⟩
    have hinv0 : f c + f c⁻¹ = 0 := by
      have := hf1 c hc c⁻¹ ((Csub A Aa t).inv_mem hc)
      rw [mul_inv_cancel, hf0] at this
      exact this.symm
    rw [hf1 _ ((Csub A Aa t).inv_mem hc) _ hacC, hfN _ haN c, add_comm]
    exact hinv0
  have htD' : t ∉ D' := fun h => by
    have := h.2
    rw [hft] at this
    exact one_ne_zero this
  have hcardC : Nat.card (Csub A Aa t) = 2 ^ 13 := H.natCard_Bp_inf_centralizer_Aa W W2
  have hD'le : Nat.card D' ≤ 2 ^ 12 := by
    obtain ⟨e, he, hee⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (hcardC ▸ Subgroup.card_dvd_of_le hD'C : Nat.card D' ∣ 2 ^ 13)
    rw [hee]
    by_contra hcon
    have h13 : e = 13 := by
      by_contra h13
      have : e ≤ 12 := by omega
      exact hcon (Nat.pow_le_pow_right (by norm_num) this)
    rw [h13, ← hcardC] at hee
    have heq : D' = Csub A Aa t :=
      Subgroup.eq_of_le_of_card_ge hD'C (by rw [hee])
    exact htD' (heq ▸ H.t_mem_inf_centralizer_Aa W W2)
  have hDeq : kCommutator (Csub A Aa t) k = D' :=
    Subgroup.eq_of_le_of_card_ge hkD' (by rw [hcard]; exact hD'le)
  intro n hn x hx
  rw [hDeq] at hx ⊢
  exact ⟨H.conj_mem_inf_centralizer_Aa W W2 hn hx.1, by rw [hfN n hn x, hx.2]⟩

theorem ThCyc.exists_D :
    ∃ D : Subgroup G, D ≤ Csub A Aa t ∧ (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧ Aa ≤ D ∧
      D ⊔ zpowers t = Csub A Aa t ∧ Disjoint D (zpowers t) ∧ Nat.card D = 2 ^ 12 ∧
      (∀ n ∈ normalizer ((W5 A t : Subgroup G) : Set G), ∀ x ∈ D, n * x * n⁻¹ ∈ D) ∧
      ∀ r ∈ Bp A t, ∀ c ∈ Csub A Aa t, r * c * r⁻¹ * c⁻¹ ∈ Aa := by
  obtain ⟨k, hkL, hkA, hodd, hfix, hab, hAa, hsup, hdisj, hcard, hnorm⟩ :=
    H.exists_kCommutator_normal W W2
  obtain ⟨hDC, -⟩ := H.kCommutator_factorization W W2 (C := Csub A Aa t) rfl hkL hkA hodd hfix
  exact ⟨kCommutator (Csub A Aa t) k, hDC, hab, hAa, hsup, hdisj, hcard, hnorm,
    fun r hr c hc => H.Bp_comm_mem_Aa W W2 hr hc⟩

end

end CFSG.EvenSporadicStandard.ThStd
