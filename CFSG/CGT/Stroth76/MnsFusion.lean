module

public import CFSG.CGT.Stroth76.TFacts
public import CFSG.CGT.Stroth77.NonSplit.StrothTInputs
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76 Equiv

theorem isEc_tmul : ∀ p : Tc, IsEc p → ∀ q : Tc, IsEc q → IsEc (tmul p q) := by
  decide +kernel

theorem isEc_tinv : ∀ p : Tc, IsEc p → IsEc (tinv p) := by
  decide +kernel

@[expose] def tconj (r p : Tc) : Tc := tmul (tmul r p) (tinv r)

@[expose] def IsInvc (p : Tc) : Prop := tmul p p = (0, 0) ∧ p ≠ (0, 0)

instance : DecidablePred IsInvc := fun p => by unfold IsInvc; infer_instance

@[expose] def TConjIn (L : List Tc) (p : Tc) : Prop := ∃ r : Tc, tconj r p ∈ L

instance (L : List Tc) : DecidablePred (TConjIn L) := fun p => by unfold TConjIn; infer_instance

theorem isEc_tconj_gens : ∀ r ∈ ([((1, 0, 0), 0), ((0, 1, 0), 0), ((0, 0, 1), 0), (0, (1, 0, 0)),
    (0, (0, 1, 0)), (0, (0, 0, 1))] : List Tc), ∀ q : Tc, IsEc q → IsEc (tconj r q) := by
  decide +kernel

theorem tc_E_classes : ∀ p : Tc, IsEc p → p ≠ (0, 0) →
    TConjIn [(0, (0, 1, 0)), (0, (1, 0, 0)), ((0, 0, 2), 0), ((0, 2, 2), 0)] p := by
  decide +kernel

theorem tc_U_classes : ∀ p : Tc, IsUc p → IsInvc p →
    IsEc p ∨ TConjIn [xyuvC, ((1, 0, 0), (0, 0, 1)), ((0, 0, 1), (1, 1, 0))] p := by
  decide +kernel

theorem tc_wE_classes : ∀ q : Tc, IsEc q → IsInvc (tmul ((1, 0, 0), 0) q) →
    TConjIn [((1, 0, 0), 0)] (tmul ((1, 0, 0), 0) q) := by
  decide +kernel

theorem tc_xyE_classes : ∀ q : Tc, IsEc q → IsInvc (tmul ((0, 1, 1), 0) q) →
    TConjIn [xyuvC] (tmul ((0, 1, 1), 0) q) := by
  decide +kernel

section Elements

variable {X : Type*} [Group X] (K : Config X)

theorem tElt_tconj (r p : Tc) : tElt K (tconj r p) = tElt K r * tElt K p * (tElt K r)⁻¹ := by
  rw [tconj, tElt_mul, tElt_mul, tElt_tinv]

theorem isConj_of_tConjIn {L : List Tc} {p : Tc} (h : TConjIn L p) :
    ∃ q ∈ L, IsConj (tElt K p) (tElt K q) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨_, hr, isConj_iff.2 ⟨tElt K r, (tElt_tconj K r p).symm⟩⟩

theorem orderOf_tElt_eq_two_iff (p : Tc) : orderOf (tElt K p) = 2 ↔ IsInvc p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, pow_two, ← tElt_mul, ← tElt_zero K, (tElt_injective K).eq_iff,
    (tElt_injective K).ne_iff]
  rfl

theorem y_sq_eq : K.y ^ 2 = tElt K ((0, 0, 2), 0) := by
  rw [← tElt_y, pow_two, ← tElt_mul]
  rfl

theorem xy_sq_eq : (K.x * K.y) ^ 2 = tElt K ((0, 2, 2), 0) := by
  rw [xy_eq, pow_two, ← tElt_mul]
  rfl

@[expose] def Esub : Subgroup X :=
  tSub K IsEc (by decide) (fun hp hq => isEc_tmul _ hp _ hq) (fun hp => isEc_tinv _ hp)

theorem closure_E_eq : Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} = Esub K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨_, by decide, (x_sq_eq K).symm⟩
    · exact ⟨_, by decide, (y_sq_eq K).symm⟩
    · exact ⟨_, by decide, tElt_gen_uv K⟩
    · exact ⟨_, by decide, tElt_gen_t K⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact tElt_mem_E_of_isEc K hp

theorem mem_normalizer_E_of_tElt_eq {r : Tc} {g : X} (hg : tElt K r = g)
    (h : ∀ q : Tc, IsEc q → IsEc (tconj r q)) :
    g ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) := by
  rw [← hg, closure_E_eq]
  haveI : Finite ((Esub K : Subgroup X) : Set X) :=
    ((Set.toFinite {p : Tc | IsEc p}).image (tElt K)).to_subtype
  refine Subgroup.mem_normalizer_fintype ?_
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨tconj r q, h q hq, tElt_tconj K r q⟩

theorem Tsub_le_normalizer_E :
    Tsub K ≤ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) := by
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [K.hA, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_normalizer_E_of_tElt_eq K (tElt_w K) (isEc_tconj_gens _ (by decide))
    · exact mem_normalizer_E_of_tElt_eq K (tElt_x K) (isEc_tconj_gens _ (by decide))
    · exact mem_normalizer_E_of_tElt_eq K (tElt_y K) (isEc_tconj_gens _ (by decide))
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_normalizer_E_of_tElt_eq K (tElt_gen_uv K) (isEc_tconj_gens _ (by decide))
    · exact mem_normalizer_E_of_tElt_eq K (tElt_gen_t K) (isEc_tconj_gens _ (by decide))
    · exact mem_normalizer_E_of_tElt_eq K (tElt_gen_u K) (isEc_tconj_gens _ (by decide))

theorem w_mem_NE : K.w ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (Subgroup.mem_sup_left K.w_mem)

theorem x_mem_NE : K.x ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (Subgroup.mem_sup_left K.x_mem)

theorem y_mem_NE : K.y ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (Subgroup.mem_sup_left K.y_mem)

theorem uv_mem_NE : K.uv ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (Subgroup.mem_sup_right (uv_mem_D K))

theorem t_mem_NE : K.t ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (Subgroup.mem_sup_right (t_mem_D K))

theorem u_mem_NE : K.u ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (Subgroup.mem_sup_right (u_mem_D K))

theorem tElt_mem_NE (p : Tc) : tElt K p ∈ Subgroup.normalizer
    ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) :=
  Tsub_le_normalizer_E K (tElt_mem K p)

theorem isConj_w_mul_of_mem_E {e : X} (he : e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t})
    (h2 : orderOf (K.w * e) = 2) : IsConj (K.w * e) K.w := by
  rw [closure_E_eq] at he
  obtain ⟨q, hq, rfl⟩ := he
  rw [← tElt_w K, ← tElt_mul] at h2 ⊢
  rw [orderOf_tElt_eq_two_iff] at h2
  obtain ⟨q', hq', h⟩ := isConj_of_tConjIn K (tc_wE_classes q hq h2)
  rw [List.mem_singleton] at hq'
  rwa [hq'] at h

theorem isConj_xy_mul_of_mem_E {e : X}
    (he : e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t})
    (h2 : orderOf (K.x * K.y * e) = 2) : IsConj (K.x * K.y * e) (K.x * K.y * K.uv) := by
  rw [closure_E_eq] at he
  obtain ⟨q, hq, rfl⟩ := he
  rw [← tElt_xyuvC K]
  rw [xy_eq K, ← tElt_mul] at h2 ⊢
  rw [orderOf_tElt_eq_two_iff] at h2
  obtain ⟨q', hq', h⟩ := isConj_of_tConjIn K (tc_xyE_classes q hq h2)
  rw [List.mem_singleton] at hq'
  rwa [hq'] at h

end Elements

@[expose] def mnsEv (v : Co) : Mns := mnsW ^ v.1.val * mnsX ^ v.2.1.val * mnsY ^ v.2.2.val

@[expose] def mnsD (d : Dc) : Mns := mnsUV ^ d.1.val * mnsT ^ d.2.1.val * mnsU ^ d.2.2.val

@[expose] def mnsTElt (p : Tc) : Mns := mnsEv p.1 * mnsD p.2

theorem mns_isConj_t : IsConj (mnsTElt (0, (0, 1, 0))) (mnsTElt ((0, 2, 2), 0)) :=
  isConj_iff.2 ⟨mnsElt ![0, 0, 0, 0, 1, 0] (swap 1 3) (by decide), by decide +kernel⟩

theorem mns_isConj_uv : IsConj (mnsTElt (0, (1, 0, 0))) (mnsTElt ((0, 2, 2), 0)) :=
  isConj_iff.2 ⟨mnsElt ![0, 0, 0, 0, 0, 0] (swap 0 5 * swap 1 4) (by decide), by decide +kernel⟩

theorem mns_isConj_y_sq : IsConj (mnsTElt ((0, 0, 2), 0)) (mnsTElt ((0, 2, 2), 0)) :=
  isConj_iff.2 ⟨mnsElt ![0, 0, 0, 0, 0, 0] (swap 0 5 * swap 1 3) (by decide), by decide +kernel⟩

theorem mns_isConj_u : IsConj (mnsTElt (0, (0, 0, 1))) (mnsTElt ((1, 0, 0), 0)) :=
  isConj_iff.2 ⟨mnsElt ![0, 1, 0, 0, 0, 0] (swap 3 4) (by decide), by decide +kernel⟩

theorem mns_isConj_wu : IsConj (mnsTElt ((1, 0, 0), (0, 0, 1))) (mnsTElt xyuvC) :=
  isConj_iff.2 ⟨mnsElt ![0, 0, 0, 1, 0, 0] (swap 4 5) (by decide), by decide +kernel⟩

theorem mns_isConj_yuvt : IsConj (mnsTElt ((0, 0, 1), (1, 1, 0))) (mnsTElt xyuvC) :=
  isConj_iff.2 ⟨mnsElt ![0, 0, 0, 0, 0, 0] (swap 0 5 * swap 1 3) (by decide), by decide +kernel⟩

private theorem odd_card_ker_of_eq_oddCore {N M : Type*} [Group N] [Finite N] [Group M]
    {f : N →* M} (h : f.ker = CFSG.oddCore N) : Odd (Nat.card f.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he : CFSG.oddCore N = CFSG.pPrimeCore 2 N := by
    unfold CFSG.oddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp [Nat.coprime_two_left]
  rw [h, he]
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

theorem isConj_of_isConj_map {N M : Type*} [Group N] [Finite N] [Group M] (f : N →* M)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) {a b : N} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (h : IsConj (f a) (f b)) : IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hf c
  have hga : orderOf (g * a * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ha]
  have hq : ((g * a * g⁻¹ : N) : N ⧸ f.ker) = b := by
    rw [QuotientGroup.eq, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc, inv_mul_cancel]
  obtain ⟨m, -, hm⟩ := CFSG.RankThree.OddKernel.isConj_of_mk_eq f.ker hker hga hb hq
  exact isConj_iff.2 ⟨m * g, by rw [← hm]; group⟩

section Model

variable {G : Type*} [Group G] (K : Config G)

theorem map_tElt
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφw : φ ⟨K.w, w_mem_NE K⟩ = mnsW) (hφx : φ ⟨K.x, x_mem_NE K⟩ = mnsX)
    (hφy : φ ⟨K.y, y_mem_NE K⟩ = mnsY) (hφuv : φ ⟨K.uv, uv_mem_NE K⟩ = mnsUV)
    (hφt : φ ⟨K.t, t_mem_NE K⟩ = mnsT) (hφu : φ ⟨K.u, u_mem_NE K⟩ = mnsU) (p : Tc) :
    φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p := by
  have h : (⟨tElt K p, tElt_mem_NE K p⟩ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G))) =
      ⟨K.w, w_mem_NE K⟩ ^ p.1.1.val * ⟨K.x, x_mem_NE K⟩ ^ p.1.2.1.val *
        ⟨K.y, y_mem_NE K⟩ ^ p.1.2.2.val *
      (⟨K.uv, uv_mem_NE K⟩ ^ p.2.1.val * ⟨K.t, t_mem_NE K⟩ ^ p.2.2.1.val *
        ⟨K.u, u_mem_NE K⟩ ^ p.2.2.2.val) :=
    Subtype.ext (by simp [tElt, Config.ev, dElt])
  rw [h]
  simp only [map_mul, map_pow, hφw, hφx, hφy, hφuv, hφt, hφu]
  rfl

variable [Finite G]

theorem isConj_tElt_of_isConj_mns
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hT : ∀ p, φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p) {p q : Tc} (hp : IsInvc p)
    (hq : IsInvc q) (h : IsConj (mnsTElt p) (mnsTElt q)) : IsConj (tElt K p) (tElt K q) := by
  have hc := isConj_of_isConj_map φ hφ (odd_card_ker_of_eq_oddCore hker)
    (a := ⟨tElt K p, tElt_mem_NE K p⟩) (b := ⟨tElt K q, tElt_mem_NE K q⟩)
    (by rw [Subgroup.orderOf_mk, orderOf_tElt_eq_two_iff]; exact hp)
    (by rw [Subgroup.orderOf_mk, orderOf_tElt_eq_two_iff]; exact hq) (by rw [hT, hT]; exact h)
  exact (Subgroup.subtype _).map_isConj hc

theorem isConj_xy_sq_of_isEc
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hT : ∀ p, φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p) {p : Tc} (hp : IsEc p)
    (hp0 : p ≠ (0, 0)) : IsConj (tElt K p) (tElt K ((0, 2, 2), 0)) := by
  obtain ⟨q, hq, hpq⟩ := isConj_of_tConjIn K (tc_E_classes p hp hp0)
  refine hpq.trans ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_t
  · exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_uv
  · exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_y_sq
  · exact IsConj.refl _

theorem isConj_xy_sq_of_mem_E
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hT : ∀ p, φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p) {e : G}
    (he : e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}) (h1 : e ≠ 1) :
    IsConj e ((K.x * K.y) ^ 2) := by
  rw [closure_E_eq] at he
  obtain ⟨p, hp, rfl⟩ := he
  have hp0 : p ≠ (0, 0) := by
    rintro rfl
    exact h1 (tElt_zero K)
  rw [xy_sq_eq]
  exact isConj_xy_sq_of_isEc K φ hφ hker hT hp hp0

theorem isConj_u_w
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hT : ∀ p, φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p) : IsConj K.u K.w := by
  rw [← tElt_gen_u K, ← tElt_w K]
  exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_u

theorem isConj_wu_xyuv
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hT : ∀ p, φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p) :
    IsConj (K.w * K.u) (K.x * K.y * K.uv) := by
  rw [← tElt_wu K, ← tElt_xyuvC K]
  exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_wu

theorem isConj_of_mem_closure_wu
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hT : ∀ p, φ ⟨tElt K p, tElt_mem_NE K p⟩ = mnsTElt p) {g : G}
    (hg : g ∈ Subgroup.closure {K.x, K.y, K.uv, K.t, K.w * K.u}) (h2 : orderOf g = 2) :
    IsConj g ((K.x * K.y) ^ 2) ∨ IsConj g (K.x * K.y * K.uv) := by
  rw [closure_wu_eq] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  rw [orderOf_tElt_eq_two_iff] at h2
  rcases tc_U_classes p hp h2 with hE | hc
  · left
    rw [xy_sq_eq]
    exact isConj_xy_sq_of_isEc K φ hφ hker hT hE h2.2
  · right
    obtain ⟨q, hq, hpq⟩ := isConj_of_tConjIn K hc
    rw [← tElt_xyuvC K]
    refine hpq.trans ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact IsConj.refl _
    · exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_wu
    · exact isConj_tElt_of_isConj_mns K φ hφ hker hT (by decide) (by decide) mns_isConj_yuvt

theorem arch76_fusion_of_model (K : Config G)
    (φ : ↥(Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup G) : Set G)) →* Mns)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.oddCore _)
    (hφw : φ ⟨K.w, w_mem_NE K⟩ = mnsW) (hφx : φ ⟨K.x, x_mem_NE K⟩ = mnsX)
    (hφy : φ ⟨K.y, y_mem_NE K⟩ = mnsY) (hφuv : φ ⟨K.uv, uv_mem_NE K⟩ = mnsUV)
    (hφt : φ ⟨K.t, t_mem_NE K⟩ = mnsT) (hφu : φ ⟨K.u, u_mem_NE K⟩ = mnsU) :
    (∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2)) ∧
    IsConj K.u K.w ∧ IsConj (K.w * K.u) (K.x * K.y * K.uv) ∧
    (∀ g ∈ Subgroup.closure {K.x, K.y, K.uv, K.t, K.w * K.u}, orderOf g = 2 →
      IsConj g ((K.x * K.y) ^ 2) ∨ IsConj g (K.x * K.y * K.uv)) ∧
    (∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, orderOf (K.w * e) = 2 →
      IsConj (K.w * e) K.w) ∧
    (∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, orderOf (K.x * K.y * e) = 2 →
      IsConj (K.x * K.y * e) (K.x * K.y * K.uv)) := by
  have hT := map_tElt K φ hφw hφx hφy hφuv hφt hφu
  exact ⟨fun e he h1 => isConj_xy_sq_of_mem_E K φ hφ hker hT he h1,
    isConj_u_w K φ hφ hker hT, isConj_wu_xyuv K φ hφ hker hT,
    fun g hg h2 => isConj_of_mem_closure_wu K φ hφ hker hT hg h2,
    fun e he h2 => isConj_w_mul_of_mem_E K he h2, fun e he h2 => isConj_xy_mul_of_mem_E K he h2⟩

end Model

end CFSG.CGT.Stroth76
