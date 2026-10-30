module

public import CFSG.FeitThompson.Local.PrimeFixedSectionOrderDerivedAction
public import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
public import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
public import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
public import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement
public import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
public import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
public import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
public import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

section General

variable {L : Type*} [Group L]

theorem mem_chiefActionKer_conj_iff (H H0 U : Subgroup L) [H.Normal] [H0.Normal] {u : L} :
    u ∈ chiefActionKer H H0 U ↔
      u ∈ U ∧ ∀ x ∈ H, ((u * x * u⁻¹ : L) : L ⧸ H0) = (x : L ⧸ H0) := by
  rw [← Subgroup.inv_mem_iff (H := chiefActionKer H H0 U), mem_chiefActionKer_iff]
  simp only [inv_inv, Subgroup.inv_mem_iff]

theorem centralizer_le_ker_conjQuotientAut (H H0 : Subgroup L) [H.Normal] [H0.Normal] :
    centralizer (H : Set L) ≤ (conjQuotientAut H H0).ker := by
  intro x hx
  rw [mem_ker_conjQuotientAut]
  intro y hy
  have hc := mem_centralizer_iff.1 hx y hy
  rw [show x⁻¹ * y * x = y by
    calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x * y) := by rw [hc]
      _ = y := by group]
  simp

variable [Finite L]

theorem le_of_isPGroup_of_normal_of_natCard_eq {q : ℕ} (hq : q.Prime) {Q : Subgroup L} [Q.Normal]
    (hQ : Nat.card ↥Q = q ^ (Nat.card L).factorization q) {T : Subgroup L}
    (hT : IsPGroup q ↥T) : T ≤ Q := by
  have := Fact.mk hq
  exact le_sylow_of_isPGroup_of_le_normalizer (Sylow.ofCard Q hQ) hT
    (by rw [show ((Sylow.ofCard Q hQ : Sylow q L) : Subgroup L) = Q from rfl,
      Subgroup.normalizer_eq_top]; exact le_top)

theorem fittingRaw_le_sup_centralizer {q : ℕ} (hq : q.Prime) {Q : Subgroup L} [Q.Normal]
    (hQcard : Nat.card ↥Q = q ^ (Nat.card L).factorization q) :
    fittingRaw L ≤ Q ⊔ centralizer (Q : Set L) := by
  have := Fact.mk hq
  set F := fittingRaw L with hF
  have hQF : Q ≤ F := le_fittingRaw_of_isPGroup hq ‹Q.Normal› (IsPGroup.of_card hQcard)
  have hmap : Subgroup.map F.subtype (pCore q ↥F) ⊔ Subgroup.map F.subtype (pComplCore q ↥F)
      = F := by
    rw [← Subgroup.map_sup, pCore_sup_pComplCore_eq_top hq ↥F, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hmap]
  refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
  · exact le_of_isPGroup_of_normal_of_natCard_eq hq hQcard
      ((isPGroup_pCore hq ↥F).map F.subtype)
  · have hcop : (Nat.card ↥(Subgroup.map F.subtype (pComplCore q ↥F))).Coprime (Nat.card ↥Q) := by
      rw [hQcard]
      refine Nat.Coprime.pow_right _ ?_
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd hq).2 ?_
      rw [Subgroup.card_map_of_injective F.subtype_injective]
      exact not_dvd_natCard_pComplCore hq ↥F
    exact le_centralizer_of_coprime_natCard_of_isNilpotent F inferInstance
      (Subgroup.map_subtype_le _) hQF hcop

theorem inf_ne_bot_of_dvd_natCard_of_sylow {p : ℕ} (hp : p.Prime) (C K : Subgroup L) [C.Normal]
    (hK : Nat.card ↥K = p ^ (Nat.card L).factorization p) (hpC : p ∣ Nat.card ↥C) :
    C ⊓ K ≠ ⊥ := by
  have := Fact.mk hp
  obtain ⟨c, hcC, hc⟩ := exists_mem_orderOf_eq_of_dvd hp hpC
  have hc1 : c ≠ 1 := fun hcon => by rw [hcon, orderOf_one] at hc; exact hp.one_lt.ne' hc.symm
  have hpg : IsPGroup p ↥(zpowers c) := IsPGroup.of_card (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P (Sylow.ofCard K hK)
  have hKeq : MulAut.conj g • (P : Subgroup L) = K := by
    rw [← Sylow.coe_subgroup_smul, hg]; rfl
  have hmem : g * c * g⁻¹ ∈ K := by
    rw [← hKeq]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP (mem_zpowers c))
  intro hbot
  have h1 : g * c * g⁻¹ = 1 :=
    Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨‹C.Normal›.conj_mem c hcC g, hmem⟩)
  exact hc1 (by calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group)

omit [Finite L] in
theorem le_of_index_eq_prime_of_not_dvd {S C : Subgroup L} [S.Normal] {p : ℕ} (hp : p.Prime)
    (hidx : S.index = p) (hC : ¬ p ∣ Nat.card ↥C) : C ≤ S := by
  have hdvd : Nat.card ↥(C.map (mk' S)) ∣ p := by
    rw [← hidx, Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd' : Nat.card ↥(C.map (mk' S)) ∣ Nat.card ↥C := Subgroup.card_map_dvd C _
  have h1 : Nat.card ↥(C.map (mk' S)) = 1 :=
    (hp.eq_one_or_self_of_dvd _ hdvd).resolve_right fun h => hC (h ▸ hdvd')
  have h2 := Subgroup.card_eq_one.1 h1
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
  exact h2

end General

variable {X : Type*} [Group X] {q : ℕ} {Q D K Z : Subgroup X}

namespace IsPrimeFixedSectionSetup

section Orders

variable (h : IsPrimeFixedSectionSetup X q Q D K Z)

include h

theorem natCard_eq_natCard_Q_mul_natCard_sup :
    Nat.card X = Nat.card ↥Q * Nat.card ↥(D ⊔ K) := by
  have h1 : ((Q : Set X)) * ((D ⊔ K : Subgroup X) : Set X) = ((⊤ : Subgroup X) : Set X) := by
    rw [h.coe_mul_coe, Subgroup.coe_top]
  have h2 := natCard_eq_mul_of_mul_eq_of_inf_eq_bot h1 h.inf_Q_sup
  rwa [Subgroup.card_top] at h2

theorem natCard_sup_eq : Nat.card ↥(D ⊔ K) = Nat.card ↥D * Nat.card ↥K :=
  natCard_eq_mul_of_mul_eq_of_inf_eq_bot h.coe_sup_D_K.symm h.inf_D_K

theorem natCard_eq_mul_mul : Nat.card X = Nat.card ↥Q * (Nat.card ↥D * Nat.card ↥K) := by
  rw [h.natCard_eq_natCard_Q_mul_natCard_sup, h.natCard_sup_eq]

theorem inf_Q_D_eq_bot : Q ⊓ D = ⊥ :=
  le_bot_iff.1 (h.inf_Q_sup ▸ inf_le_inf_left Q (le_sup_left : D ≤ D ⊔ K))

theorem coe_sup_Q_right (B : Subgroup X) :
    ((Q ⊔ B : Subgroup X) : Set X) = (Q : Set X) * (B : Set X) :=
  haveI := h.normal_Q
  Subgroup.coe_mul_of_right_le_normalizer_left Q B
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)

theorem coe_sup_Q_D : ((Q ⊔ D : Subgroup X) : Set X) = (Q : Set X) * (D : Set X) :=
  h.coe_sup_Q_right D

theorem inf_Q_eq_bot_of_le_D {B : Subgroup X} (hBD : B ≤ D) : Q ⊓ B = ⊥ :=
  le_bot_iff.1 (h.inf_Q_D_eq_bot ▸ inf_le_inf_left Q hBD)

theorem natCard_sup_Q_of_le_D {B : Subgroup X} (hBD : B ≤ D) :
    Nat.card ↥(Q ⊔ B : Subgroup X) = Nat.card ↥Q * Nat.card ↥B :=
  natCard_eq_mul_of_mul_eq_of_inf_eq_bot (h.coe_sup_Q_right B).symm (h.inf_Q_eq_bot_of_le_D hBD)

theorem natCard_sup_Q_D : Nat.card ↥(Q ⊔ D : Subgroup X) = Nat.card ↥Q * Nat.card ↥D :=
  h.natCard_sup_Q_of_le_D le_rfl

theorem eq_D_of_sup_eq {B : Subgroup X} (hBD : B ≤ D) (heq : (Q ⊔ B : Subgroup X) = Q ⊔ D) :
    B = D := by
  have hfin : Finite X := h.finite
  refine Subgroup.eq_of_le_of_card_ge hBD (le_of_eq ?_)
  have h1 := h.natCard_sup_Q_of_le_D hBD
  rw [heq, h.natCard_sup_Q_D] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem isNilpotent_sup_Q_of_le_centralizer (hD : Group.IsNilpotent ↥D) {B : Subgroup X}
    (hBD : B ≤ D) (hBC : B ≤ centralizer (Q : Set X)) :
    Group.IsNilpotent ↥(Q ⊔ B : Subgroup X) := by
  have hfin : Finite X := h.finite
  have := Fact.mk h.prime
  have hQnil : Group.IsNilpotent ↥Q := h.isPGroup_Q.isNilpotent
  have hBnil : Group.IsNilpotent ↥B :=
    Group.nilpotent_of_mulEquiv (G := (B.subgroupOf D : Subgroup ↥D))
      (Subgroup.subgroupOfEquivOfLe hBD)
  exact Group.nilpotent_of_mulEquiv
    (mulEquivProdOfCoeEqMul (h.coe_sup_Q_right B) (h.inf_Q_eq_bot_of_le_D hBD)
      fun x hx y hy => mem_centralizer_iff.1 (hBC hy) x hx)

theorem normal_sup_Q_D : (Q ⊔ D : Subgroup X).Normal := by
  have := h.normal_Q
  have := h.normal_D
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h.sup_eq_top]
  refine sup_le (le_trans le_sup_left Subgroup.le_normalizer)
    (sup_le (le_trans le_sup_right Subgroup.le_normalizer) ?_)
  refine le_normalizer_sup (by rw [Subgroup.normalizer_eq_top]; exact le_top) ?_
  exact le_trans le_sup_right (Subgroup.le_normalizer_of_normal_subgroupOf
    (H := D) (K := D ⊔ K) le_sup_left)

theorem index_sup_Q_D : (Q ⊔ D : Subgroup X).index = Nat.card ↥K := by
  have hfin : Finite X := h.finite
  have h1 := Subgroup.card_mul_index (Q ⊔ D : Subgroup X)
  rw [h.natCard_sup_Q_D, h.natCard_eq_mul_mul, ← mul_assoc] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos Nat.card_pos Nat.card_pos) h1

theorem natCard_Q_eq_pow_factorization (hQ : Q ≠ ⊥) :
    Nat.card ↥Q = q ^ (Nat.card X).factorization q := by
  have hfin : Finite X := h.finite
  have := Fact.mk h.prime
  obtain ⟨n, hn⟩ := (h.isPGroup_Q).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hQ (Subgroup.card_eq_one.1 (by simpa using hn))
  have hqQ : q ∣ Nat.card ↥Q := by rw [hn]; exact dvd_pow_self q hn0
  have hnotdvd : ¬ q ∣ Nat.card ↥(D ⊔ K) := fun hdvd =>
    h.prime.one_lt.ne' (Nat.eq_one_of_dvd_one (h.coprime_Q ▸ Nat.dvd_gcd hqQ hdvd))
  rw [h.natCard_eq_natCard_Q_mul_natCard_sup, Nat.factorization_mul Nat.card_pos.ne'
    Nat.card_pos.ne', hn]
  simp [Nat.Prime.factorization_pow h.prime, Nat.factorization_eq_zero_of_not_dvd hnotdvd]

theorem not_dvd_natCard_Q_of_dvd_natCard_K {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    ¬ p ∣ Nat.card ↥Q := fun hdvd =>
  hp.one_lt.ne' (Nat.eq_one_of_dvd_one (h.coprime_Q ▸
    Nat.dvd_gcd hdvd (hpK.trans (Subgroup.card_dvd_of_le le_sup_right))))

theorem not_dvd_natCard_D_of_dvd_natCard_K {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    ¬ p ∣ Nat.card ↥D := fun hdvd =>
  hp.one_lt.ne' (Nat.eq_one_of_dvd_one (h.coprime_D_K ▸ Nat.dvd_gcd hdvd hpK))

theorem natCard_K_eq_pow_factorization (hp : (Nat.card ↥K).Prime) :
    Nat.card ↥K = Nat.card ↥K ^ (Nat.card X).factorization (Nat.card ↥K) := by
  have hfin : Finite X := h.finite
  have h1 : (Nat.card X).factorization (Nat.card ↥K) = 1 := by
    rw [h.natCard_eq_mul_mul, Nat.factorization_mul Nat.card_pos.ne'
      (Nat.mul_pos Nat.card_pos Nat.card_pos).ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd
        (h.not_dvd_natCard_Q_of_dvd_natCard_K hp dvd_rfl),
      Nat.factorization_eq_zero_of_not_dvd (h.not_dvd_natCard_D_of_dvd_natCard_K hp dvd_rfl),
      hp.factorization_self]
  rw [h1, pow_one]

end Orders

section Node

variable (h : IsPrimeFixedSectionSetup X q Q D K Z)
  (hQ0 : Q ⊓ centralizer (D : Set X) < Q)

include h hQ0

omit h in
theorem Q_ne_bot : Q ≠ ⊥ := by
  intro hb
  rw [hb] at hQ0
  simp at hQ0

theorem natCard_Q_eq_pow_factorization_of_lt :
    Nat.card ↥Q = q ^ (Nat.card X).factorization q :=
  h.natCard_Q_eq_pow_factorization (Q_ne_bot hQ0)

omit hQ0 in
theorem Q_le_fittingRaw :
    haveI := h.finite
    Q ≤ fittingRaw X := by
  have := h.finite
  exact le_fittingRaw_of_isPGroup h.prime h.normal_Q h.isPGroup_Q

theorem fittingRaw_le_sup_centralizer_Q :
    haveI := h.finite
    fittingRaw X ≤ Q ⊔ centralizer (Q : Set X) := by
  have := h.finite
  have := h.normal_Q
  exact fittingRaw_le_sup_centralizer h.prime (natCard_Q_eq_pow_factorization_of_lt h hQ0)

theorem not_dvd_natCard_centralizer_Q :
    ¬ Nat.card ↥K ∣ Nat.card ↥(centralizer (Q : Set X)) := by
  have hfin : Finite X := h.finite
  have := h.normal_Q
  have hQ0n := normal_inf_centralizer h hQ0
  have hp : (Nat.card ↥K).Prime := prime_natCard_K h hQ0
  intro hdvd
  have hne := inf_ne_bot_of_dvd_natCard_of_sylow hp (centralizer (Q : Set X)) K
    (h.natCard_K_eq_pow_factorization hp) hdvd
  rw [Ne, Subgroup.eq_bot_iff_forall] at hne
  push Not at hne
  obtain ⟨k, hk, hk1⟩ := hne
  have hQZ : Q = Z := by
    rw [← h.inf_centralizer_Q k hk.2 hk1]
    refine le_antisymm (le_inf le_rfl fun y hy => mem_centralizer_iff.2 ?_) inf_le_left
    rintro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (mem_centralizer_iff.1 hk.1 y hy).symm
  have hQcard : Nat.card ↥Q = q := by rw [hQZ, h.natCard_Z]
  have hVdvd : q ^ Nat.card ↥K ∣ Nat.card ↥Q := by
    rw [← natCard_map_mk'_Q h hQ0]
    exact Subgroup.card_map_dvd Q _
  rw [hQcard] at hVdvd
  have hle : q ^ Nat.card ↥K ≤ q := Nat.le_of_dvd h.prime.pos hVdvd
  have h2 : q ^ 2 ≤ q ^ Nat.card ↥K := Nat.pow_le_pow_right h.prime.pos hp.two_le
  have := h.prime.two_le
  nlinarith [hle, h2]

theorem centralizer_Q_le_sup_Q_D : centralizer (Q : Set X) ≤ Q ⊔ D := by
  have hfin : Finite X := h.finite
  have := h.normal_sup_Q_D
  exact le_of_index_eq_prime_of_not_dvd (S := (Q ⊔ D : Subgroup X)) (prime_natCard_K h hQ0)
    h.index_sup_Q_D (not_dvd_natCard_centralizer_Q h hQ0)

theorem Q_le_ker_conjQuotientAut :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    Q ≤ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker := by
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  intro u hu
  rw [mem_ker_conjQuotientAut]
  intro x hx
  have hab := isElementaryAbelian_map_mk' h hQ0
  have h1 : (QuotientGroup.mk x : X ⧸ (Q ⊓ centralizer (D : Set X))) * (QuotientGroup.mk u)
      = (QuotientGroup.mk u) * (QuotientGroup.mk x) :=
    hab.mul_comm ⟨x, hx, rfl⟩ ⟨u, hu, rfl⟩
  rw [← QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk (x⁻¹ * (u⁻¹ * x * u)) : X ⧸ (Q ⊓ centralizer (D : Set X)))
      = (QuotientGroup.mk x)⁻¹ * ((QuotientGroup.mk u)⁻¹ * (QuotientGroup.mk x)
        * (QuotientGroup.mk u)) := by
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
  rw [h2]
  calc (QuotientGroup.mk x : X ⧸ (Q ⊓ centralizer (D : Set X)))⁻¹
        * ((QuotientGroup.mk u)⁻¹ * (QuotientGroup.mk x) * (QuotientGroup.mk u))
      = (QuotientGroup.mk x)⁻¹ * ((QuotientGroup.mk u)⁻¹
        * ((QuotientGroup.mk x) * (QuotientGroup.mk u))) := by group
    _ = 1 := by rw [h1]; group

theorem chiefActionKer_eq_sup :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    chiefActionKer Q (Q ⊓ centralizer (D : Set X)) (Q ⊔ D)
      = Q ⊔ (D ⊓ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker) := by
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  have hQW : Q ≤ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker :=
    Q_le_ker_conjQuotientAut h hQ0
  rw [chiefActionKer_eq_inf]
  refine le_antisymm (fun s hs => ?_) (sup_le (le_inf le_sup_left hQW)
    (le_inf (le_trans inf_le_left le_sup_right) inf_le_right))
  obtain ⟨hsS, hsW⟩ := hs
  have hsS' : s ∈ (Q : Set X) * (D : Set X) := by rw [← h.coe_sup_Q_D]; exact hsS
  obtain ⟨x, hx, d, hd, rfl⟩ := hsS'
  have hdW : d ∈ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker := by
    have hh : x⁻¹ * (x * d) ∈ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQW hx)) hsW
    simpa using hh
  exact Subgroup.mul_mem _ ((le_sup_left : Q ≤ _) hx)
    ((le_sup_right : (D ⊓ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker) ≤ _)
      ⟨hd, hdW⟩)

theorem inf_ker_D_le_centralizer_Q :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    D ⊓ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker ≤ centralizer (Q : Set X) := by
  have hfin : Finite X := h.finite
  have hsolv : Group.IsSolvable X := h.isSolvable
  have := h.normal_Q
  have hQ0n := normal_inf_centralizer h hQ0
  set Q0 : Subgroup X := Q ⊓ centralizer (D : Set X) with hQ0def
  set B : Subgroup X := D ⊓ (conjQuotientAut Q Q0).ker with hB
  have hBD : B ≤ D := inf_le_left
  have hkey : Q ≤ centralizer (B : Set X) := by
    intro x hx
    have hfix : ∀ r ∈ B, x⁻¹ * (r * x * r⁻¹) ∈ Q0 := by
      intro r hr
      have hr' : r⁻¹ ∈ (conjQuotientAut Q Q0).ker := Subgroup.inv_mem _ hr.2
      simpa using (mem_ker_conjQuotientAut Q Q0).1 hr' x hx
    obtain ⟨z, hz, n, hn, hxzn⟩ :=
      exists_mem_inf_centralizer_mul_eq (T := Q) (I := Q0) (R := B)
        (h.coprime_natCard_Q_of_le_sup (le_trans hBD (le_sup_left : D ≤ D ⊔ K)))
        (le_normalizer_of_normal Q Q0) (le_normalizer_of_normal B Q)
        (le_normalizer_of_normal B Q0) hx hfix
    have hnc : (n : X) ∈ centralizer (B : Set X) :=
      Subgroup.centralizer_le (by exact_mod_cast hBD) hn.1.2
    rw [hxzn]
    exact Subgroup.mul_mem _ hz.2 hnc
  rw [← Subgroup.le_centralizer_iff]
  exact hkey

theorem sup_centralizer_Q_eq_chiefActionKer :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    Q ⊔ centralizer (Q : Set X)
      = chiefActionKer Q (Q ⊓ centralizer (D : Set X)) (Q ⊔ D) := by
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  rw [chiefActionKer_eq_sup h hQ0]
  refine le_antisymm (sup_le le_sup_left ?_)
    (sup_le le_sup_left (le_sup_of_le_right (inf_ker_D_le_centralizer_Q h hQ0)))
  refine le_trans (le_inf (centralizer_Q_le_sup_Q_D h hQ0)
    (centralizer_le_ker_conjQuotientAut Q (Q ⊓ centralizer (D : Set X)))) ?_
  rw [← chiefActionKer_eq_inf, chiefActionKer_eq_sup h hQ0]

variable (hD : Group.IsNilpotent ↥D)

include hD

theorem isNilpotent_sup_centralizer_Q :
    Group.IsNilpotent ↥(Q ⊔ centralizer (Q : Set X) : Subgroup X) := by
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  rw [sup_centralizer_Q_eq_chiefActionKer h hQ0, chiefActionKer_eq_sup h hQ0]
  exact h.isNilpotent_sup_Q_of_le_centralizer hD inf_le_left (inf_ker_D_le_centralizer_Q h hQ0)

theorem fittingRaw_eq_sup_centralizer_Q :
    haveI := h.finite
    fittingRaw X = Q ⊔ centralizer (Q : Set X) := by
  have := h.finite
  have := h.normal_Q
  refine le_antisymm (fittingRaw_le_sup_centralizer_Q h hQ0) ?_
  exact le_fittingRaw_of_normal_of_isNilpotent (Subgroup.sup_normal _ _)
    (isNilpotent_sup_centralizer_Q h hQ0 hD)

theorem fittingRaw_eq_chiefActionKer :
    haveI := h.finite
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    fittingRaw X = chiefActionKer Q (Q ⊓ centralizer (D : Set X)) (Q ⊔ D) := by
  have := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  rw [fittingRaw_eq_sup_centralizer_Q h hQ0 hD, sup_centralizer_Q_eq_chiefActionKer h hQ0]

omit hD in
theorem chiefActionKer_lt_sup_Q_D :
    haveI := h.normal_Q
    haveI := normal_inf_centralizer h hQ0
    chiefActionKer Q (Q ⊓ centralizer (D : Set X)) (Q ⊔ D) < Q ⊔ D := by
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  refine lt_of_le_of_ne (chiefActionKer_le _ _ _) fun heq => ?_
  rw [chiefActionKer_eq_sup h hQ0] at heq
  have hBD : (D ⊓ (conjQuotientAut Q (Q ⊓ centralizer (D : Set X))).ker) = D :=
    h.eq_D_of_sup_eq inf_le_left heq
  have hDC : D ≤ centralizer (Q : Set X) := hBD ▸ inf_ker_D_le_centralizer_Q h hQ0
  have hQQ0 : Q ≤ Q ⊓ centralizer (D : Set X) :=
    le_inf le_rfl (Subgroup.le_centralizer_iff.1 hDC)
  exact hQ0.ne (le_antisymm hQ0.le hQQ0)

theorem fittingRaw_le_sup_Q_D :
    haveI := h.finite
    fittingRaw X ≤ Q ⊔ D := by
  have := h.finite
  have := h.normal_Q
  have := normal_inf_centralizer h hQ0
  rw [fittingRaw_eq_chiefActionKer h hQ0 hD]
  exact chiefActionKer_le _ _ _

end Node

end IsPrimeFixedSectionSetup

end CFSG.FeitThompson
