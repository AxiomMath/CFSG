module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110m
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot autCenterQuot_injective_of_perfect)

open CFSG.LocalAnalysis.ComponentInitial

section Orders

open CFSG.OrderReductions.LinearOrders
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_centralQuotient_mulEquiv)

theorem coprime_self_sub_one_d4cls {Q : ℕ} (hQ : 1 ≤ Q) : Nat.Coprime Q (Q - 1) :=
  (Nat.coprime_self_sub_right hQ).2 (Nat.coprime_one_right Q)

theorem coprime_self_add_one_d4cls (Q : ℕ) : Nat.Coprime Q (Q + 1) :=
  Nat.coprime_self_add_right.2 (Nat.coprime_one_right Q)

theorem sl_card_false_d4cls {E : Type} [Field E] [Finite E] {b : ℕ} (hEb : Nat.card E = 2 ^ b)
    {m : ℕ} (hm : 2 ≤ m) {T : Type*} [Group T] (f : Matrix.SpecialLinearGroup (Fin m) E →* T)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _)
    (hT : Nat.card (T ⧸ Subgroup.center T) = 174182400) : False := by
  haveI : Finite T := Finite.of_surjective f hf
  have hSL := card_specialLinear E m (by omega)
  have hZ := card_specialLinear_center E m (by omega)
  have hb1 : 1 ≤ b := by
    rcases b with _ | b
    · haveI : Fintype E := Fintype.ofFinite E
      have h1 : 1 < Fintype.card E := Fintype.one_lt_card
      rw [Fintype.card_eq_nat_card, hEb] at h1
      norm_num at h1
    · omega
  have hN : 174182400 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := by
    rw [← hT]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_surjective hf)
  have hperf : 3 ≤ m ∨ 4 ≤ Nat.card E := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hm3, hE4⟩ := hcon
    obtain rfl : m = 2 := by omega
    have hb : b = 1 := by
      by_contra hb
      have h4 : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hSL, hEb, hb] at hN
    revert hN
    decide
  have hq := CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm hperf
  have hcomm : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ := hq.1.commutator_eq_top
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hcomm f hf hker
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) =
      174182400 * Nat.gcd m (Nat.card E - 1) := by
    rw [(Subgroup.center
        (Matrix.SpecialLinearGroup (Fin m) E)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e.toEquiv, hT, hZ]
  have hdvd : Nat.card E ^ (m * (m - 1) / 2) ∣ 174182400 * Nat.gcd m (Nat.card E - 1) := by
    rw [← hcard, hSL]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (Nat.card E ^ (m * (m - 1) / 2)) (Nat.gcd m (Nat.card E - 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_self_sub_one_d4cls (by rw [hEb]; exact Nat.one_le_two_pow)))
  have h1 : Nat.card E ^ (m * (m - 1) / 2) ∣ 174182400 := hcop.dvd_of_dvd_mul_right hdvd
  rw [hEb, ← pow_mul] at h1
  have h12 : b * (m * (m - 1) / 2) ≤ 12 := by
    by_contra hlt
    push Not at hlt
    have h13 : 2 ^ 13 ∣ 174182400 := (pow_dvd_pow 2 hlt).trans h1
    norm_num at h13
  have hm5 : m ≤ 5 := by
    by_contra h6
    push Not at h6
    have h30 : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h15 : 15 ≤ m * (m - 1) / 2 := by omega
    have : 15 ≤ b * (m * (m - 1) / 2) := le_trans h15 (Nat.le_mul_of_pos_left _ hb1)
    omega
  rw [hSL, hEb] at hcard
  rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 by omega) with rfl | rfl | rfl | rfl
  · have hb' : b ≤ 12 := by norm_num at h12; omega
    interval_cases b <;> revert hcard <;> decide
  · have hb' : b ≤ 4 := by norm_num at h12; omega
    interval_cases b <;> revert hcard <;> decide
  · have hb' : b ≤ 2 := by norm_num at h12; omega
    interval_cases b <;> revert hcard <;> decide
  · have hb' : b ≤ 1 := by norm_num at h12; omega
    interval_cases b <;> revert hcard <;> decide

theorem su_card_false_d4cls {E : Type} [Field E] {ℓ e m : ℕ} (hE : UnitaryFieldData ℓ e E)
    (hℓ : ℓ = 2) (hm : 3 ≤ m) {T : Type*} [Group T]
    (g : ↥(StatedSU m (ℓ ^ e) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _)
    (hT : Nat.card (T ⧸ Subgroup.center T) = 174182400) : False := by
  haveI := hE.finite
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  have he : 1 ≤ e := hE.one_le
  have hF : Nat.card E = (ℓ ^ e) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
  haveI : Finite T := Finite.of_surjective g hg
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hE (n := m) (by omega)
  have hN : 174182400 ∣ Nat.card ↥(StatedSU m (ℓ ^ e) E) := by
    rw [← hT]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_surjective hg)
  by_cases hnq : (m, ℓ ^ e) = (3, 2)
  ·
    have h1 := congrArg Prod.fst hnq
    have h2 := congrArg Prod.snd hnq
    simp only at h1 h2
    subst h1
    have h216 : (Nat.card ↥(StatedSU 3 (ℓ ^ e) E) : ℤ) = 216 := by
      rw [hint, h2]
      decide
    have h216' : Nat.card ↥(StatedSU 3 (ℓ ^ e) E) = 216 := by exact_mod_cast h216
    rw [h216'] at hN
    norm_num at hN
  · obtain ⟨hqs, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hm hnq
    have hcomm : commutator ↥(StatedSU m (ℓ ^ e) E) = ⊤ := hqs.1.commutator_eq_top
    obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hcomm g hg hker
    have hZ : Nat.card ↥(Subgroup.center ↥(StatedSU m (ℓ ^ e) E)) = Nat.gcd m (ℓ ^ e + 1) := by
      have h1 := CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hE (n := m) (by omega)
      rw [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hE (by omega)] at h1
      rw [hcen]
      exact h1
    have hcard : Nat.card ↥(StatedSU m (ℓ ^ e) E) = 174182400 * Nat.gcd m (ℓ ^ e + 1) := by
      rw [(Subgroup.center ↥(StatedSU m (ℓ ^ e) E)).card_eq_card_quotient_mul_card_subgroup,
        Nat.card_congr eq.toEquiv, hT, hZ]
    have hdvdZ : (((ℓ ^ e) ^ (m * (m - 1) / 2) : ℕ) : ℤ) ∣
        (Nat.card ↥(StatedSU m (ℓ ^ e) E) : ℤ) := by
      rw [hint]
      push_cast
      exact Dvd.intro _ rfl
    have hdvd : (ℓ ^ e) ^ (m * (m - 1) / 2) ∣ 174182400 * Nat.gcd m (ℓ ^ e + 1) := by
      rw [← hcard]
      exact Int.natCast_dvd_natCast.mp hdvdZ
    have hcop : Nat.Coprime ((ℓ ^ e) ^ (m * (m - 1) / 2)) (Nat.gcd m (ℓ ^ e + 1)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
        (coprime_self_add_one_d4cls _))
    have h1 : (ℓ ^ e) ^ (m * (m - 1) / 2) ∣ 174182400 := hcop.dvd_of_dvd_mul_right hdvd
    subst hℓ
    rw [← pow_mul] at h1
    have h12 : e * (m * (m - 1) / 2) ≤ 12 := by
      by_contra hlt
      push Not at hlt
      have h13 : 2 ^ 13 ∣ 174182400 := (pow_dvd_pow 2 hlt).trans h1
      norm_num at h13
    have hm5 : m ≤ 5 := by
      by_contra h6
      push Not at h6
      have h30 : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
      have h15 : 15 ≤ m * (m - 1) / 2 := by omega
      have : 15 ≤ e * (m * (m - 1) / 2) := le_trans h15 (Nat.le_mul_of_pos_left _ he)
      omega
    have hint' : ((174182400 * Nat.gcd m (2 ^ e + 1) : ℕ) : ℤ) =
        ((2 ^ e : ℕ) : ℤ) ^ (m * (m - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 m, (((2 ^ e : ℕ) : ℤ) ^ i - (-1) ^ i) := by
      rw [← hcard]
      exact hint
    rcases (show m = 3 ∨ m = 4 ∨ m = 5 by omega) with rfl | rfl | rfl
    · have he' : e ≤ 4 := by norm_num at h12; omega
      interval_cases e <;> revert hint' <;> decide
    · have he' : e ≤ 2 := by norm_num at h12; omega
      interval_cases e <;> revert hint' <;> decide
    · have he' : e ≤ 1 := by norm_num at h12; omega
      interval_cases e <;> revert hint' <;> decide

end Orders

theorem sl_card_false_of_char_d4cls {E : Type} [Field E] [Finite E] (hE : ringChar E = 2)
    {m : ℕ} (hm : 2 ≤ m) {T : Type*} [Group T] (f : Matrix.SpecialLinearGroup (Fin m) E →* T)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _)
    (hT : Nat.card (T ⧸ Subgroup.center T) = 174182400) : False := by
  obtain ⟨b, -, -, hb⟩ := InputsL33.exists_card_eq_pow_ringChar (K := E)
  rw [hE] at hb
  exact sl_card_false_d4cls hb hm f hf hker hT

section Descent

theorem nonempty_centerQuot_equiv_of_surjective_d4cls {G A : Type*} [Group G] [Group A]
    (ψ : G →* A) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    (hA : Subgroup.center A = ⊥) : Nonempty ((G ⧸ Subgroup.center G) ≃* A) := by
  have hZ : Subgroup.center G ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have h1 : ψ z ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨g, rfl⟩ := hψ a
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) g]
    rw [hA] at h1
    exact Subgroup.mem_bot.1 h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hZ hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem exists_d4_component_d4cls {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {x : MulAut K} (hx : Lemma1314.PumpupVia 5 D K x)
    (hlay : PerfectInLayer (autCenterQuot K x)) :
    ∃ T : Subgroup (K ⧸ Subgroup.center K),
      IsComponentOf T (fixSubgroup (autCenterQuot K x)) ∧
        Nat.card (↥T ⧸ Subgroup.center ↥T) = 174182400 := by
  obtain ⟨-, J1, hJ1, ⟨eA⟩⟩ := hx
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center K := by rw [hπ, QuotientGroup.ker_mk']
  have hαβ : ∀ k, π (x k) = autCenterQuot K x (π k) := fun k => rfl
  have hfix : Lemma1314.fixSub x = fixSubgroup x := by
    ext y
    exact Iff.rfl
  have hJ1' : GLAPComponent 5 (fixSubgroup x) J1 := hfix ▸ hJ1
  have hT := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π hker x
    (autCenterQuot K x) hαβ hπs Nat.prime_five hJ1'
  have hTperf := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hT
  obtain ⟨hTc, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hT (hlay _ hT.1 hTperf)
  refine ⟨J1.map π, hTc, ?_⟩
  have hJperf : ⁅J1, J1⁆ = J1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ1'
  have hJcomm : commutator J1 = ⊤ := by
    apply Subgroup.map_injective J1.subtype_injective
    rw [Subgroup.map_subtype_commutator, hJperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set ψ : J1 →* J1.map π := π.subgroupMap J1 with hψ
  have hψs : Function.Surjective ψ := π.subgroupMap_surjective J1
  have hψk : ψ.ker ≤ Subgroup.center J1 := by
    intro y hy
    have h1 : π (y : K) = 1 := congrArg Subtype.val hy
    have h2 : (y : K) ∈ Subgroup.center K := hker h1
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (z : K))
  obtain ⟨eJ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hJcomm ψ hψs hψk
  have hJs : IsSimpleGroup (↥J1 ⧸ Subgroup.center ↥J1) := by
    haveI : IsSimpleGroup (↥(J1.map π) ⧸ Subgroup.center ↥(J1.map π)) := hTc.2.2.2
    exact eJ.isSimpleGroup
  have hJq : CFSG.Open.IsQuasisimple ↥J1 := ⟨hJcomm, hJs⟩
  have hDc := Claims1110l.card_of_lieModel_D4_two hD
  have hne : GLAPPrimeCore 5 ↥J1 ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (barOf 5 J1) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _)
    have h1 : Nat.card (barOf 5 J1) = 1 := Nat.card_unique
    rw [Nat.card_congr eA.toEquiv, hDc] at h1
    norm_num at h1
  have hO : GLAPPrimeCore 5 ↥J1 ≤ Subgroup.center ↥J1 :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJq
      (GLAPPrimeCore.normal 5 ↥J1) hne
  set χ : ↥J1 →* D := eA.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J1)) with hχ
  have hχs : Function.Surjective χ := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hχk : χ.ker ≤ Subgroup.center ↥J1 := by
    intro y hy
    apply hO
    have h1 : eA (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J1) y) = 1 := hy
    rw [map_eq_one_iff _ eA.injective] at h1
    exact (QuotientGroup.eq_one_iff y).1 h1
  obtain ⟨eZ⟩ := nonempty_centerQuot_equiv_of_surjective_d4cls χ hχs hχk
    (Claims1110l.center_eq_bot_of_lieModel_D4 hD)
  rw [← Nat.card_congr (eJ.symm.trans eZ).symm.toEquiv, hDc]

theorem card_centerQuot_map_d4cls {S T : Type*} [Group S] [Group T] (e : S ≃* T) {K : Subgroup S}
    {N : ℕ} (h : Nat.card (↥K ⧸ Subgroup.center ↥K) = N) :
    Nat.card (↥(K.map (e : S →* T)) ⧸ Subgroup.center ↥(K.map (e : S →* T))) = N := by
  rw [← h]
  exact (Nat.card_congr
    (InputsL33.centerQuotCongr (K.equivMapOfInjective (e : S →* T) e.injective)).toEquiv).symm

end Descent

section Linear

open Polynomial CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem linear_inner_d4_false {n : ℕ} {k : Type} [Field k] [Finite k] (hk : ringChar k = 2)
    {A : GL (Fin n) k} {c : kˣ} (hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)))
    (hL : Nat.card (↥K ⧸ Subgroup.center ↥K) = 174182400) : False := by
  have hpk : ((5 : ℕ) : k) ≠ 0 := by
    rw [Ne, ringChar.spec, hk]
    decide
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hA K hK
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : Fact (Irreducible h.1.1) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  haveI : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite k
  obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor hsq h.1.2
  obtain ⟨f, hf, hker⟩ := InputsL33.exists_surjective_ker_le_center_map_proj e
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 := by
    rcases h.2 with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hE : ringChar (AdjoinRoot h.1.1) = 2 := by
    rw [← Algebra.ringChar_eq k (AdjoinRoot h.1.1), hk]
  exact sl_card_false_of_char_d4cls hE hm f hf hker hL

theorem linear_field_d4_false {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    (hk : ringChar k = 2) (σ : k ≃+* k) (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.fieldAut n k σ)))
    (hL : Nat.card (↥K ⧸ Subgroup.center ↥K) = 174182400) : False := by
  obtain ⟨-, f, hf, hker⟩ := linearFieldAut_components hn σ K hK
  have hE : ringChar (CFSG.GH74.GLS.IVK.fixedField σ) = 2 := by
    rw [Algebra.ringChar_eq (CFSG.GH74.GLS.IVK.fixedField σ) k, hk]
  exact sl_card_false_of_char_d4cls hE hn f hf hker hL

theorem linear_d4_false {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq2 : q.p = 2)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 5 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hL : Nat.card (↥K ⧸ Subgroup.center ↥K) = 174182400) : False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 := by
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p, hq2]
  have hβ' : MulAut.congr e' α ^ 5 = 1 := by rw [← map_pow, hα, map_one]
  have hK' := InputsL33.isComponentOf_map_congr e' hK
  have hL' := card_centerQuot_map_d4cls e' hL
  have hcases := (Nat.lt_or_ge r 2).elim
    (fun hr2 => by
      obtain rfl : r = 1 := by simp only at hr; omega
      exact InputsL33.linear_cases_two Nat.prime_five (MulAut.congr e' α) hβ')
    (fun hr2 => InputsL33.linear_cases_of_three_le Nat.prime_five (by norm_num) (by omega)
      (MulAut.congr e' α) hβ')
  rcases hcases with ⟨A, c, hA, hβA⟩ | ⟨h, σ, -, hβh⟩
  · rw [hβA] at hK'
    exact linear_inner_d4_false hchar hA _ hK' hL'
  · have hβφ : MulAut.congr (h⁻¹ : MulAut _) (MulAut.congr e' α) =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by
      rw [InputsL33.congr_self_eq, hβh]
      group
    have hK'' := InputsL33.isComponentOf_map_congr (h⁻¹ : MulAut _) hK'
    rw [hβφ] at hK''
    exact linear_field_d4_false (by simp only at hr; omega) hchar σ _ hK''
      (card_centerQuot_map_d4cls (h⁻¹ : MulAut _) hL')

end Linear

section Unitary

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ClassicalGroups.UnitaryFlag

theorem unitary_inner_d4_false {ℓ f n : ℕ} (hℓ : ℓ = 2) {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (T : Subgroup (primeFormP h (idGram K n)))
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A)))
    (hL : Nat.card (↥T ⧸ Subgroup.center ↥T) = 174182400) : False := by
  obtain ⟨d, hd, hcases⟩ := exists_field_factor_of_component_primeFormConjHom Nat.prime_five
    (by rw [hℓ]; norm_num) A hA T hT
  rcases hcases with ⟨F, _, _, hchar, -, -, g, hg, hgk⟩ |
      ⟨E, _, _, m, -, hcard, hm, -, g, hg, hgk⟩ | ⟨E, _, _, m, hchar, -, hm, -, g, hg, hgk⟩
  · exact sl_card_false_of_char_d4cls (hchar.trans hℓ) le_rfl g hg hgk hL
  · have hfd : 1 ≤ f * d := Nat.mul_pos h.one_le hd
    have hE : UnitaryFieldData ℓ (f * d) E :=
      ⟨h.prime, hfd, by rw [Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm]⟩
    exact su_card_false_d4cls hE hℓ hm g hg hgk hL
  · exact sl_card_false_of_char_d4cls (hchar.trans hℓ) hm g hg hgk hL

theorem unitary_d4_false {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq2 : q.p = 2)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 5 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hL : Nat.card (↥K ⧸ Subgroup.center ↥K) = 174182400) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp5 : (5 : ℕ).Prime := Nat.prime_five
  obtain ⟨e⟩ := he
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := F))
  let e' : S ≃* primeFormP h (idGram F (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) F) := isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' α ^ 5 = 1 := by rw [← map_pow, hα, map_one]
  have hK1 := InputsL33.isComponentOf_map_congr e' hK
  have hL1 := card_centerQuot_map_d4cls e' hL
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' α) = 1
  ·
    have hβD : MulAut.congr e' α ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ 5, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) F) ^ 5 =
        Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA] at hK1
    exact unitary_inner_d4_false hq2 A hAp _ hK1 hL1
  ·
    have hne : MulAut.congr e' α ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact (5 : ℕ).Prime := ⟨hp5⟩
    have hord : orderOf (MulAut.congr e' α) = 5 := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' α)) = 5 :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp5
        (by norm_num) (MulAut.congr e' α) hord _ rfl hσp
    have hK2 := InputsL33.isComponentOf_map_congr
      ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hK1
    rw [InputsL33.congr_self_eq, inv_inv, hM] at hK2
    have hL2 := card_centerQuot_map_d4cls
      ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hL1
    obtain ⟨-, g, hg, hgk⟩ :=
      unitary_fieldAut_components h hn3 hC hp5 (by norm_num) hσp _ hK2
    exact su_card_false_d4cls (CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp5
      (by norm_num) hσp) hq2 hn3 g hg hgk hL2

end Unitary

section Families

theorem autCenterQuot_facts_d4cls {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    {x : MulAut K} (hx : orderOf x = 5) :
    autCenterQuot K x ^ 5 = 1 ∧ autCenterQuot K x ≠ 1 := by
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨by rw [← map_pow, hx5, map_one], fun h1 => ?_⟩
  have h2 : x = 1 := autCenterQuot_injective_of_perfect hK.1 (by rw [h1, map_one])
  rw [h2, orderOf_one] at hx
  norm_num at hx

@[expose] def D4UpLinearIdx (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .A r q ∧ q.p = 2

@[expose] def D4UpUnitaryIdx (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .twistedA r q ∧ q.p = 2

theorem noD4UpOn_linear_d4cls : NoD4UpOn D4UpLinearIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  obtain ⟨hβ5, hβ1⟩ := autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl, hq2⟩ := hd
  have hp5 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar
      (TauCeti.LieTypeIndex.A r q) ≠ 5 := by
    show q.p ≠ 5
    rw [hq2]
    norm_num
  have hlay := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_linearUnitary
    Nat.prime_five (by norm_num) (K ⧸ Subgroup.center K) hK.1.2 hna ⟨.A r q, hv⟩ rfl he
    (autCenterQuot K x) hβ5 hβ1 (Or.inl hp5)).layer
  obtain ⟨T, hT, hTc⟩ := exists_d4_component_d4cls hD hK.1 hx hlay
  exact linear_d4_false r q hv hq2 he hβ5 hT hTc

theorem noD4UpOn_unitary_d4cls : NoD4UpOn D4UpUnitaryIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  obtain ⟨hβ5, hβ1⟩ := autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl, hq2⟩ := hd
  have hp5 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar
      (TauCeti.LieTypeIndex.twistedA r q) ≠ 5 := by
    show q.p ≠ 5
    rw [hq2]
    norm_num
  have hlay := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_linearUnitary
    Nat.prime_five (by norm_num) (K ⧸ Subgroup.center K) hK.1.2 hna ⟨.twistedA r q, hv⟩ rfl he
    (autCenterQuot K x) hβ5 hβ1 (Or.inl hp5)).layer
  obtain ⟨T, hT, hTc⟩ := exists_d4_component_d4cls hD hK.1 hx hlay
  exact unitary_d4_false r q hv hq2 he hβ5 hT hTc

end Families

section SympOrders

theorem center_eq_bot_of_simple_perfect_d4cls {G : Type*} [Group G] [IsSimpleGroup G]
    (hp : commutator G = ⊤) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hc : commutator G = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a
    rw [hp] at hc
    exact (top_ne_bot (α := Subgroup G)) hc

theorem sp_centerQuot_card_ne_d4cls {F : Type} [Field F] [Finite F] {c : ℕ}
    (hF : Nat.card F = 2 ^ c) {s : ℕ} (hs : 2 ≤ s) (hne : ¬ (s = 2 ∧ Nat.card F = 2)) :
    Nat.card (↥(StatedSp s F) ⧸ Subgroup.center ↥(StatedSp s F)) ≠ 174182400 := by
  intro hN
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : 1 ≤ c := by
    rcases c with _ | c
    · have h1 : 1 < Fintype.card F := Fintype.one_lt_card
      rw [Fintype.card_eq_nat_card, hF] at h1
      norm_num at h1
    · omega
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := c) (by rw [Fintype.card_eq_nat_card, hF])
  obtain ⟨hsimp, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := F) hs hne
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := s) (K := F)
  let e : ↥(StatedSp s F) ≃* StatedProj (StatedSp s F) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  haveI : IsSimpleGroup ↥(StatedSp s F) := (MulEquiv.isSimpleGroup_congr e).2 hsimp
  have hperf' : commutator ↥(StatedSp s F) = ⊤ := by
    have h1 : commutator (StatedProj (StatedSp s F)) = ⊤ := hperf.commutator_eq_top
    have h2 : (commutator ↥(StatedSp s F)).map e.toMonoidHom =
        commutator (StatedProj (StatedSp s F)) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h2, h1, Subgroup.map_top_of_surjective _ e.surjective]
  have hZ := center_eq_bot_of_simple_perfect_d4cls hperf'
  have hcard : Nat.card ↥(StatedSp s F) = 174182400 := by
    rw [← hN, hZ]
    exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF] at hcard
  have h1 : (2 ^ c) ^ (s ^ 2) ∣ 174182400 := by
    rw [← hcard]
    exact Dvd.intro _ rfl
  rw [← pow_mul] at h1
  have h12 : c * s ^ 2 ≤ 12 := by
    by_contra hlt
    push Not at hlt
    have h13 : 2 ^ 13 ∣ 174182400 := (pow_dvd_pow 2 hlt).trans h1
    norm_num at h13
  have hs3 : s ≤ 3 := by
    by_contra h4
    push Not at h4
    have : 16 ≤ s ^ 2 := by nlinarith
    nlinarith
  rcases (show s = 2 ∨ s = 3 by omega) with rfl | rfl
  · have hc3 : c ≤ 3 := by norm_num at h12; omega
    interval_cases c <;> revert hcard <;> decide
  · have hc3 : c ≤ 1 := by norm_num at h12; omega
    interval_cases c <;> revert hcard <;> decide

end SympOrders

section SympInner

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

def GoodD4Sp (H : Subgroup (StatedSp r K)) : Prop :=
  ∃ (X : Type) (_ : Group X) (_ : Finite X) (ψ : X →* StatedSp r K), Function.Injective ψ ∧
    ψ.range = H ∧ commutator X = ⊤ ∧ Nat.card (X ⧸ Subgroup.center X) ≠ 174182400

theorem goodD4_sp_d4cls [Finite K] {c : ℕ} (hKc : Nat.card K = 2 ^ c)
    {A : Subgroup (StatedSp r K)} {s : ℕ} (hs : 1 ≤ s) (φ : A ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodD4Sp ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite K
  by_cases hs1 : s = 1
  · subst hs1
    let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSp 1 K :=
      CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
    have h4 : 4 ≤ Fintype.card K := four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
    have hX := slFactorFacts_holds K 2 le_rfl (fun _ => h4)
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) K, inferInstance, inferInstance,
      A.subtype.comp (φ.symm.toMonoidHom.comp e1.toMonoidHom), ?_,
      range_comp_eq_commutator φ _ (range_equiv_eq_commutator e1 hX.perfect), hX.perfect,
      fun h => ?_⟩
    · exact Subtype.val_injective.comp (φ.symm.injective.comp e1.injective)
    · refine sl_card_false_d4cls hKc le_rfl (MonoidHom.id _) Function.surjective_id ?_ h
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hy
      rw [hy]
      exact Subgroup.one_mem _
  · have hs2 : 2 ≤ s := by omega
    by_cases hspecial : s = 2 ∧ Fintype.card K = 2
    · obtain ⟨rfl, hc2⟩ := hspecial
      have hX := spFourTwoFacts_holds K hc2
      refine ⟨↥(commutator ↥(StatedSp 2 K)), inferInstance, inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (commutator ↥(StatedSp 2 K)).subtype), ?_,
        range_comp_eq_commutator φ _ (Subgroup.range_subtype _), hX.perfect, fun h => ?_⟩
      · exact Subtype.val_injective.comp (φ.symm.injective.comp Subtype.val_injective)
      · have hle : Nat.card (↥(commutator ↥(StatedSp 2 K)) ⧸
            Subgroup.center ↥(commutator ↥(StatedSp 2 K))) ≤ Nat.card ↥(StatedSp 2 K) :=
          (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)).trans
            (Subgroup.card_le_card_group _)
        have hSp := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2
        have hK2' : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card]; exact hc2
        rw [hK2'] at hSp
        rw [hSp, h] at hle
        revert hle
        decide
    · have hne : (s, Fintype.card K) ≠ (2, 2) := fun h =>
        hspecial ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      have hX := spFactorFacts_holds K s hs2 hne
      have hθ : (MonoidHom.id ↥(StatedSp s K)).range = commutator ↥(StatedSp s K) := by
        rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
      refine ⟨↥(StatedSp s K), inferInstance, inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _)), ?_,
        range_comp_eq_commutator φ _ hθ, hX.perfect,
        sp_centerQuot_card_ne_d4cls hKc hs2 fun h => hspecial ⟨h.1, by
          rw [Fintype.card_eq_nat_card]; exact h.2⟩⟩
      exact Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id)

theorem goodD4_gl_d4cls {E : Type} [Field E] [Fintype E] (hE2 : ringChar E = 2)
    (h4 : 4 ≤ Fintype.card E) {m : ℕ} {A : Subgroup (StatedSp r K)}
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodD4Sp ⁅A, A⁆ := by
  classical
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := isSolvable_gl_of_le_one (E := E) (not_le.1 hlt |> Nat.lt_succ_iff.1)
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have hX := slFactorFacts_holds E m hm (fun _ => h4)
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine range_eq_commutator_of_perfect θ hX.perfect
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  refine ⟨Matrix.SpecialLinearGroup (Fin m) E, inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp θ), ?_, range_comp_eq_commutator φ θ hθ,
    hX.perfect, fun h => ?_⟩
  · exact Subtype.val_injective.comp
      (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective)
  · refine sl_card_false_of_char_d4cls hE2 hm (MonoidHom.id _) Function.surjective_id ?_ h
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hy
    rw [hy]
    exact Subgroup.one_mem _

open CFSG.RankThree.CentralLift CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag in
theorem goodD4_gu_d4cls {ℓ g : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData ℓ g E) (hℓ : ℓ = 2)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ}
    (b : Module.Basis (Fin m) E V) (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    {A : Subgroup (StatedSp r K)} (φ : A ≃* sesqUnitaryGroup Hf)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodD4Sp ⁅A, A⁆ := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsolv : ¬ (Module.finrank E V ≤ 1 ∨ ¬ ((Module.finrank E V = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E V = 3 → 3 ≤ ℓ ^ g))) := fun h => by
    haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl h
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [hfin] at hsolv
  push Not at hsolv
  obtain ⟨hm, hq2, hq3⟩ := hsolv
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  haveI : CharP E ℓ := hE.charP
  have hEcard : Fintype.card E = (ℓ ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
    haveI : Finite ↥hE.fixedField := inferInstance
    haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
    have hFcard : Fintype.card ↥hE.fixedField = ℓ ^ g := by
      rw [Fintype.card_eq_nat_card]
      exact hE.card_fixedField
    haveI : CharP ↥hE.fixedField ℓ := charP_of_card_eq_prime_pow (f := g) hFcard
    have hFℓ : ringChar ↥hE.fixedField = ℓ := ringChar.eq _ ℓ
    have hX := slFactorFacts_holds ↥hE.fixedField 2 le_rfl (fun _ => by rw [hFcard]; exact hq2 rfl)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField, inferInstance, inferInstance, ψ,
      hψi, hψ, hX.perfect, fun h => ?_⟩
    refine sl_card_false_of_char_d4cls (hFℓ.trans hℓ) le_rfl (MonoidHom.id _)
      Function.surjective_id ?_ h
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hy
    rw [hy]
    exact Subgroup.one_mem _
  · have hnq : (m, ℓ ^ g) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := hq3 h1
      omega
    have hX := suFactorFacts_holds E m (ℓ ^ g) hEcard hm3 hnq
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
    have hSUeq : StatedSU m (ℓ ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
      unitarySU_eq_gramSU hE m
    let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (ℓ ^ g) E) :=
      e.trans (MulEquiv.subgroupCongr hSUeq.symm)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e'
    refine ⟨↥(StatedSU m (ℓ ^ g) E), inferInstance, inferInstance, ψ, hψi, hψ, hX.perfect,
      fun h => ?_⟩
    refine su_card_false_d4cls hE hℓ hm3 (MonoidHom.id _) Function.surjective_id ?_ h
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hy
    rw [hy]
    exact Subgroup.one_mem _

theorem goodD4_spSupported_of_factor_d4cls [Finite K] {f p : ℕ} (hp3 : 3 ≤ p)
    (hK2 : Nat.card K = 2 ^ f) (hq : 2 ≤ 2 ^ f) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks 2 f p x a) (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆) :
    GoodD4Sp ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  have hKℓ : ringChar K = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK2])
    exact ringChar.eq K 2
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ ⊢
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact goodD4_sp_d4cls hK2 hs1 (φ.trans e) hQ
    · obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact goodD4_gu_d4cls hE rfl hHf hHfl e he φ hQ
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    haveI := Fintype.ofFinite (AdjoinRoot (h : K[X]))
    have hEℓ : ringChar (AdjoinRoot (h : K[X])) = 2 :=
      (Algebra.ringChar_eq K (AdjoinRoot (h : K[X]))).symm.trans hKℓ
    have h4 : 4 ≤ Fintype.card (AdjoinRoot (h : K[X])) := by
      have hdeg : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      have hN : 2 ^ f ≤ (2 ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
      have hle := Nat.le_of_dvd (by omega) hP.dvd
      rw [Fintype.card_eq_nat_card, hP.card_field]
      omega
    exact goodD4_gl_d4cls hEℓ h4 φ hQ

theorem sp_inner_d4_false {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    (x : StatedSp r K) (hx : x ^ 5 = 1) (K' : Subgroup (StatedProj (StatedSp r K)))
    (hK' : IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))))
    (hL : Nat.card (↥K' ⧸ Subgroup.center ↥K') = 174182400) : False := by
  classical
  have hq0 : 2 ^ f ≠ 0 := pow_ne_zero f (by norm_num)
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = 2 := ringChar.eq K 2
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hcov : ∀ {ι : Type} [Finite ι] (A : ι → Subgroup (StatedSp r K)),
      (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) →
      ⨆ i, A i = Subgroup.centralizer ({x} : Set (StatedSp r K)) →
      (∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i)) →
      (∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ → GoodD4Sp ⁅A i, A i⁆) → False := by
    intro ι _ A hc hjoin htame hgood
    have hcomp := components_conj_of_orbit_family (SymplecticFlag.proj r K)
      SymplecticHigher.proj_surjective hZc x A hc hjoin htame
    obtain ⟨i, hi, rfl⟩ := hcomp K' hK'
    obtain ⟨X, _, _, ψ, hψ, hrange, hXp, hXc⟩ := hgood i hi
    obtain ⟨g, hg, hgk⟩ := exists_cover_of_range (SymplecticFlag.proj r K) hZc ψ hψ hrange
    obtain ⟨eX⟩ := nonempty_centralQuotient_mulEquiv hXp g hg hgk
    exact hXc ((Nat.card_congr eX.toEquiv).trans hL)
  by_cases hx1 : x = 1
  · subst hx1
    refine hcov (fun _ : Unit => (⊤ : Subgroup (StatedSp r K)))
      (fun i j hij => absurd (Subsingleton.elim i j) hij)
      (by ext g; simp [Subgroup.mem_centralizer_iff]) (fun _ => tame_top_statedSp hr)
      (fun _ hQ => goodD4_sp_d4cls hK hr Subgroup.topEquiv hQ)
  · have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) 5 := by
      rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _) (by norm_num)
    have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
      hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
        (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
        (by rw [h, map_one]))
    have ha : orderOf (SymplecticFlag.proj r K x) = 5 :=
      orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
    have hxp : orderOf x = 5 := orderOf_eq_prime hx hx1
    have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK
      Nat.prime_five (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
    have hpK : ((5 : ℕ) : K) ≠ 0 := by
      intro h
      rw [CharP.cast_eq_zero_iff K 2] at h
      norm_num at h
    have hsq := (altPrimaryData_spLin hpK hx).squarefree
    haveI : Finite (reciprocalOrbits (spEnd x)) :=
      (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
    obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
    exact hcov (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num) hq hsq
        blocks O)
      (fun O hQ => by
        obtain ⟨O, h, hh, rfl⟩ := O
        exact goodD4_spSupported_of_factor_d4cls (by norm_num) hK hq hsq blocks ⟨h, hh⟩ hQ)

end SympInner

section SympFamily

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem exists_card_eq_two_pow_d4cls {E : Type} [Field E] [Finite E] (hE : ringChar E = 2) :
    ∃ c : ℕ, Nat.card E = 2 ^ c := by
  obtain ⟨c, -, -, hc⟩ := InputsL33.exists_card_eq_pow_ringChar (K := E)
  rw [hE] at hc
  exact ⟨c, hc⟩

theorem symplectic_d4_false {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p = 2)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group))
    {β : MulAut S} (hβ : β ^ 5 = 1) {T : Subgroup S} (hT : IsComponentOf T (fixSubgroup β))
    (hL : Nat.card (↥T ⧸ Subgroup.center ↥T) = 174182400) : False := by
  haveI := hs
  obtain ⟨e⟩ := he
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hmod : StatedClassicalModel S .PSp r q.p q.exponent := by
    rcases (show r = 2 ∨ 3 ≤ r by simp only at hr; omega) with rfl | hr3
    · exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr3 e
  rw [hq2] at hmod
  obtain ⟨⟨-, hf, hr', -⟩, K, _, _, hK, ⟨e'⟩⟩ := hmod
  have hβ' : MulAut.congr e' β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two hf hr' hK
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (show Odd 5 by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hT' := InputsL33.isComponentOf_map_congr e' hT
  have hL' := card_centerQuot_map_d4cls e' hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [Fintype.card_eq_nat_card, hK])
  by_cases hD : MulAut.congr e' β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_five (by norm_num) hD hβ'
    have hcen : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
      haveI : IsSimpleGroup (StatedProj (StatedSp r K)) := (MulEquiv.isSimpleGroup_congr e').1 hs
      have hna' : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hna
        refine ⟨e' a, e' b, fun h => hab (e'.injective ?_)⟩
        rw [map_mul, map_mul, h]
      exact CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hna'
    have ht5 : t ^ 5 = 1 := by
      have h1 : MulAut.conj (t ^ 5) = 1 := by rw [map_pow, ht, hβ']
      have h2 : t ^ 5 ∈ Subgroup.center (StatedProj (StatedSp r K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h3 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc g * t ^ 5 = t ^ 5 * g * (t ^ 5)⁻¹ * t ^ 5 := by rw [h3]
          _ = t ^ 5 * g := by group
      rw [hcen, Subgroup.mem_bot] at h2
      exact h2
    obtain ⟨x, hx, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (by omega) Nat.prime_five (by norm_num) ht5
    rw [← ht, ← hx] at hT'
    exact sp_inner_d4_false hf hK (by omega) x hxp _ hT' hL'
  ·
    have hne1 : MulAut.congr e' β ≠ 1 := fun h1 => hD (h1 ▸ one_mem _)
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hord : orderOf (MulAut.congr e' β) = 5 := orderOf_eq_prime hβ' hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 5 Nat.prime_five _ hE hD hord
    have hT'' := InputsL33.isComponentOf_map_congr (h⁻¹ : MulAut _) hT'
    have hφ : MulAut.congr (h⁻¹ : MulAut _) (MulAut.congr e' β) = fieldAut r K σ := by
      rw [InputsL33.congr_self_eq, hβeq]
      group
    rw [hφ] at hT''
    have hL'' := card_centerQuot_map_d4cls (h⁻¹ : MulAut _) hL'
    have hσ5 : σ ^ 5 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have hodd5 : Odd 5 := by decide
    haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
    have hchar : ringChar ↥(descentField σ) = 2 := by
      rw [Algebra.ringChar_eq (descentField σ) K]
      exact ringChar.eq K 2
    obtain ⟨c, hc⟩ := exists_card_eq_two_pow_d4cls hchar
    by_cases hex : r = 2 ∧ Nat.card ↥(descentField σ) = 2
    · obtain ⟨rfl, hk2⟩ := hex
      obtain ⟨hLF, hcover⟩ := sp_fieldAut_comp_two spFourTwoFacts_holds hodd5 σ hσ5 hk2
      obtain ⟨g, hg, hgk⟩ := hcover _ hT''
      obtain ⟨eX⟩ := nonempty_centralQuotient_mulEquiv hLF.perfect g hg hgk
      have hle : Nat.card (↥(commutator ↥(StatedSp 2 (descentField σ))) ⧸
          Subgroup.center ↥(commutator ↥(StatedSp 2 (descentField σ)))) ≤
            Nat.card ↥(StatedSp 2 (descentField σ)) :=
        (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)).trans
          (Subgroup.card_le_card_group _)
      have hSp := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp
        (K := ↥(descentField σ)) 2
      rw [hk2] at hSp
      rw [hSp, Nat.card_congr eX.toEquiv, hL''] at hle
      revert hle
      decide
    · obtain ⟨hLF, hcover⟩ := sp_fieldAut_comp_generic spFactorFacts_holds hodd5 (by omega) σ hσ5
        hex
      obtain ⟨g, hg, hgk⟩ := hcover _ hT''
      obtain ⟨eX⟩ := nonempty_centralQuotient_mulEquiv hLF.perfect g hg hgk
      exact sp_centerQuot_card_ne_d4cls hc (by omega) hex
        ((Nat.card_congr eX.toEquiv).trans hL'')

@[expose] def D4UpSympIdx (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ q.p = 2

theorem noD4UpOn_symplectic_d4cls : NoD4UpOn D4UpSympIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  obtain ⟨hβ5, hβ1⟩ := autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl, hq2⟩ := hd
  have hp5 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar
      (TauCeti.LieTypeIndex.B r q) ≠ 5 := by
    show q.p ≠ 5
    rw [hq2]
    norm_num
  have hlay := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_symplecticOrthogonal
    Nat.prime_five le_rfl (K ⧸ Subgroup.center K) hK.1.2 hna ⟨.B r q, hv⟩ rfl he
    (autCenterQuot K x) hβ5 hβ1 (Or.inl hp5)).layer
  obtain ⟨T, hT, hTc⟩ := exists_d4_component_d4cls hD hK.1 hx hlay
  exact symplectic_d4_false hK.1.2 hna r q hv hq2 he hβ5 hT hTc

end SympFamily

section OmegaInner

open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.LowTwoRank

theorem ker_le_center_of_injective_d4cls {X H : Type*} [Group X] [Group H] (f : X →* H)
    (hf : Function.Injective f) : f.ker ≤ Subgroup.center X := by
  intro y hy
  have : y = 1 := hf (by rw [MonoidHom.mem_ker.mp hy, map_one])
  rw [this]
  exact one_mem _

theorem card_centerQuot_orthDerived_ne_d4cls {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h7 : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nat.card (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) ≠ 174182400 := by
  classical
  intro hcard
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  have hcardΩ : Nat.card ↥(orthDerived Q) = 174182400 := by
    rw [← hcard, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot)).toEquiv]
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hk4 : 4 ≤ k := by omega
  have hdim : Module.finrank K V = 2 * ((k - 1) + 1) := by omega
  have hΩle := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  have hdvd : ((Nat.card K ^ ((k - 1) * ((k - 1) + 1)) : ℕ) : ℤ) ∣
      (Nat.card ↥(orthDerived Q) : ℤ) := by
    rw [Nat.cast_pow]
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · rw [CFSG.StandardType.card_orthDerived_of_type Q hQ hdim hΩle (Or.inl ⟨rfl, hp⟩)]
      exact (dvd_mul_right _ _).mul_right _
    · rw [CFSG.StandardType.card_orthDerived_of_type Q hQ hdim hΩle (Or.inr ⟨rfl, hp⟩)]
      exact (dvd_mul_right _ _).mul_right _
  rw [hcardΩ] at hdvd
  have hdvd' : Nat.card K ^ ((k - 1) * ((k - 1) + 1)) ∣ 174182400 := by exact_mod_cast hdvd
  obtain ⟨c, -, hc⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hc, ← pow_mul] at hdvd'
  have hc2 : 2 ≤ (c : ℕ) := by
    by_contra hlt
    have h1 : (c : ℕ) ≤ 1 := by omega
    have : 2 ^ (c : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    rw [Nat.card_eq_fintype_card, hc] at hK4
    omega
  have h13 : 13 ≤ (c : ℕ) * ((k - 1) * ((k - 1) + 1)) := by
    have h12 : 12 ≤ (k - 1) * ((k - 1) + 1) := by
      have : 3 ≤ k - 1 := by omega
      nlinarith
    nlinarith
  have := (pow_dvd_pow 2 h13).trans hdvd'
  norm_num at this

theorem orthFactorOver_card_ne_d4cls {f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (hX : OrthFactorOver 2 (2 ^ f) X) : Nat.card (X ⧸ Subgroup.center X) ≠ 174182400 := by
  intro hcard
  rcases hX with ⟨m, j, E, _, _, hm, hj, hE, hcardE, -, ⟨e⟩⟩ |
    ⟨m, j, q', E, _, _, hm, hj, hE, hq', hcardE, -, ⟨e⟩⟩ |
    ⟨K', _, _, hK', hK'c, s, hs, hne, ⟨e⟩⟩ |
    ⟨K', _, _, V, _, _, _, Q, hK', hK'c, hQ, h7, hT, ⟨e⟩⟩
  · exact sl_card_false_of_char_d4cls hE hm e.symm.toMonoidHom e.symm.surjective
      (ker_le_center_of_injective_d4cls _ e.symm.injective) hcard
  · subst hq'
    have hpow : (2 ^ f) ^ j = 2 ^ (f * j) := (pow_mul 2 f j).symm
    rw [hpow] at e hcardE
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * j) E :=
      ⟨Nat.prime_two, by nlinarith, by
        rw [Nat.card_eq_fintype_card, hcardE, ← pow_mul]
        congr 1
        ring⟩
    exact su_card_false_d4cls hU rfl hm e.symm.toMonoidHom e.symm.surjective
      (ker_le_center_of_injective_d4cls _ e.symm.injective) hcard
  · refine sp_centerQuot_card_ne_d4cls hK' hs (fun h => hne (Prod.ext h.1 h.2)) ?_
    rw [← hcard]
    exact Nat.card_congr (InputsL33.centerQuotCongr e).symm.toEquiv
  · haveI : CharP K' 2 := ringChar.of_eq hK'c
    have hK4 : 4 ≤ Nat.card K' := by
      rw [hK']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    refine card_centerQuot_orthDerived_ne_d4cls hK4 Q hQ h7 hT ?_
    rw [← hcard]
    exact Nat.card_congr (InputsL33.centerQuotCongr e).symm.toEquiv

theorem omega_inner_d4_false {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] {n f : ℕ} (hG : StatedClassicalModel G t n 2 f) (hf : 2 ≤ f) (a : G)
    (ha : a ^ 5 = 1) (J : Subgroup G) (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)))
    (hL : Nat.card (↥J ⧸ Subgroup.center ↥J) = 174182400) : False := by
  obtain ⟨X, _, _, hX, hfac, -, g, hg, hgk⟩ :=
    exists_lieFactor_of_component_conj_omega_card slFactorFacts_holds suFactorFacts_holds
      omegaFactorField_holds Nat.prime_five (by norm_num) (Or.inr ht) hG (by norm_num) a ha J hJ
  obtain ⟨eX⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hgk
  exact orthFactorOver_card_ne_d4cls hf hfac ((Nat.card_congr eX.toEquiv).trans hL)

end OmegaInner

section OmegaOuter

open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth (outer_order_prime
  mem_E_of_pow_eq_one_of_three_lt)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.Assembly.LowTwoRank

theorem omega_card_eq_d4_arith {a n : ℕ} (ha : 1 ≤ a) (hn : 4 ≤ n) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1)
    (h : (174182400 : ℤ) = ((2 : ℤ) ^ a) ^ (n * (n - 1)) * (((2 : ℤ) ^ a) ^ n - ε) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (((2 : ℤ) ^ a) ^ (2 * i) - 1)) :
    a = 1 ∧ n = 4 ∧ ε = 1 := by
  have hdvdZ : ((2 ^ (a * (n * (n - 1))) : ℕ) : ℤ) ∣ (174182400 : ℤ) := by
    rw [h]
    push_cast
    rw [pow_mul]
    exact (dvd_mul_right _ _).mul_right _
  have hdvd : 2 ^ (a * (n * (n - 1))) ∣ 174182400 := by exact_mod_cast hdvdZ
  have h12 : a * (n * (n - 1)) ≤ 12 := by
    by_contra hlt
    push Not at hlt
    have h13 : 2 ^ 13 ∣ 174182400 := (pow_dvd_pow 2 hlt).trans hdvd
    norm_num at h13
  have hnn : 12 ≤ n * (n - 1) := by
    have : 3 ≤ n - 1 := by omega
    nlinarith
  have ha1 : a = 1 := by nlinarith
  subst ha1
  have hn4 : n = 4 := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · exact h4
    · exfalso
      have : 4 ≤ n - 1 := by omega
      nlinarith
  subst hn4
  refine ⟨rfl, rfl, ?_⟩
  have hprod : ∏ i ∈ Finset.Icc 1 (4 - 1), (((2 : ℤ) ^ 1) ^ (2 * i) - 1) = 2835 := by decide
  rw [hprod] at h
  rcases hε with rfl | rfl
  · rfl
  · norm_num at h

theorem congr_eq_fieldAutT_d4cls {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {k : Subfield K} {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} {σ : K ≃+* K} {p : ℕ} (S : SubfieldSetup k Q₀' Q' σ p)
    (e : G ≃* matrixProjectiveDerived Q) (β : MulAut G) (U : similarityPairs Q)
    (hUβ : matrixProjectiveConjugationHom Q U = MulAut.congr e β)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x)) :
    MulAut.congr (e.trans Θ) β = fieldAutT Q' σ S.hQσ := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr (e.trans Θ) β) x = Θ ((MulAut.congr e β) (Θ.symm x)) := rfl
  rw [h1, ← hUβ, hΘ, MulEquiv.apply_symm_apply, hg']
  rfl

theorem card_centerQuot_fieldAutT_component_d4cls {K : Type} [Field K] [Finite K]
    {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    {σ : K ≃+* K} {p : ℕ} (S : SubfieldSetup k Q₀ Q σ p) {G : Type} [Group G] [Finite G]
    (E : G ≃* matrixProjectiveDerived Q) {β : MulAut G}
    (hβ : MulAut.congr E β = fieldAutT Q σ S.hQσ) {J : Subgroup G}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card (matrixProjectiveDerived Q₀) := by
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hd0 : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨-, hK⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fieldAutT_layer_and_eq S hd0
  have hfix : fixSubgroup (MulAut.congr E β) =
      (fixSubgroup β).map (E : G →* matrixProjectiveDerived Q) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := E)).symm
    rw [mem_fixSubgroup]
    show E (β (E.symm x)) = x ↔ β (E.symm x) = E.symm x
    exact E.eq_symm_apply.symm
  have hJ' : CFSG.Open.IsComponentOf (J.map (E : G →* matrixProjectiveDerived Q))
      (fixSubgroup (fieldAutT Q σ S.hQσ)) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map E hJ
    rw [← hfix, hβ] at h1
    exact h1
  have hJeq := hK _ hJ'
  obtain ⟨hsimp, a, b, hab⟩ := matrix_simple_nonabelian hd0 S.hnd₀ S.hT₀
  let ι := inclEquiv k S.hext hd0
  haveI := hsimp
  haveI : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) := ι.symm.isSimpleGroup
  have hZ : Subgroup.center ↥(subfieldDerivedImage k S.hext) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup
      ⟨ι a, ι b, fun h => hab (ι.injective (by rw [map_mul, map_mul, h]))⟩
  have h1 := (card_centerQuot_map_d4cls E (K := J) rfl).symm
  have h2 := congrArg (fun A : Subgroup (matrixProjectiveDerived Q) =>
    Nat.card (↥A ⧸ Subgroup.center ↥A)) hJeq
  rw [h1, h2, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv, Nat.card_congr ι.symm.toEquiv]

theorem omega_outer_plus_d4_false {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n 2 f) (hD4 : n = 4 → f ≠ 5) (β : MulAut G)
    (hβ : β ^ 5 = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) {J : Subgroup G}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hL : Nat.card (↥J ⧸ Subgroup.center ↥J) = 174182400) : False := by
  have hp : (5 : ℕ).Prime := Nat.prime_five
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hout' : β ∉ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut G := by
    rintro ⟨a, ha⟩
    exact hout a ha
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hG K hK e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinatePlusWitnessEquiv K e) hgates hp hp2 hβ hout'
  have hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K) := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · exact mem_E_of_pow_eq_one_of_three_lt hgates hp (by omega) (by rw [← map_pow, hβ, map_one])
    · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n h5]
      exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f 5 hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = 5 := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 5) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord''
    (by omega : 3 ≤ n)
  have hc := card_centerQuot_fieldAutT_component_d4cls S _
    (congr_eq_fieldAutT_d4cls S (coordinatePlusWitnessEquiv K e) β U hUκ Θ g' hg'l hg'r hΘ) hJ
  let e3 : CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadPlus n (semilinearFixedSubfield U.val.right))) ≃*
      matrixProjectiveDerived (coordinateQuadPlus n (semilinearFixedSubfield U.val.right)) :=
    statedProjectiveReindexEquiv (plusIndexEquiv n)
      (CFSG.LieType.Universal.Spin.quadPlus n (semilinearFixedSubfield U.val.right))
      (CFSG.LieType.Universal.Spin.coe_quadPlus n _)
  rw [hL, ← Nat.card_congr e3.toEquiv] at hc
  haveI : Finite (semilinearFixedSubfield U.val.right) := Subtype.finite
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  haveI : CharP (semilinearFixedSubfield U.val.right) 2 :=
    ringChar.of_eq ((Algebra.ringChar_eq (semilinearFixedSubfield U.val.right) K).trans
      (ringChar.eq K 2))
  have hord2 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
    (K := semilinearFixedSubfield U.val.right) hn4
  rw [← hc, hcard'] at hord2
  push_cast at hord2
  have hf5 : 1 ≤ f / 5 := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  obtain ⟨h1, h4, -⟩ := omega_card_eq_d4_arith hf5 hn4 (Or.inl rfl) hord2
  obtain ⟨m, rfl⟩ := hpf
  have hm : m = 1 := by
    rw [Nat.mul_div_cancel_left m (by norm_num)] at h1
    exact h1
  subst hm
  exact hD4 h4 rfl

theorem omega_outer_minus_d4_false {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n 2 f) (β : MulAut G) (hβ : β ^ 5 = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) {J : Subgroup G}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hL : Nat.card (↥J ⧸ Subgroup.center ↥J) = 174182400) : False := by
  have hp : (5 : ℕ).Prime := Nat.prime_five
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hout' : β ∉ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut G := by
    rintro ⟨a, ha⟩
    exact hout a ha
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hG hn1 K hK b c hirr e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2
    hβ hout'
  have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  have hE : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f 5 hG hp hp2 hn1 K hK b c hirr e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = 5 := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 5) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / 5 := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 5 = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  have hcardm : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ m := by
    rw [hcard', hdiv]
  have hm1 : 1 ≤ m := by
    rw [hdiv] at hfp
    exact hfp
  have hK' : Nat.card K = 2 ^ (m * 5) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) Nat.prime_two hm1 hcardm
    hK'
  have S := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn4 hdeg b'
    c' hirr'
  have hc := card_centerQuot_fieldAutT_component_d4cls S _
    (congr_eq_fieldAutT_d4cls S (coordinateMinusWitnessEquiv K hn1 b c e) β U hUκ Θ g' hg'l hg'r
      hΘ) hJ
  let e3 : CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadMinus n (semilinearFixedSubfield U.val.right) b' c')) ≃*
      matrixProjectiveDerived (coordinateQuadMinus n (semilinearFixedSubfield U.val.right) hn1 b'
        c') :=
    statedProjectiveReindexEquiv (minusIndexEquiv n hn1)
      (CFSG.LieType.Universal.Spin.quadMinus n (semilinearFixedSubfield U.val.right) b' c')
      (CFSG.LieType.Universal.Spin.coe_quadMinus n _ b' c')
  rw [hL, ← Nat.card_congr e3.toEquiv] at hc
  haveI : Finite (semilinearFixedSubfield U.val.right) := Subtype.finite
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  haveI : CharP (semilinearFixedSubfield U.val.right) 2 :=
    ringChar.of_eq ((Algebra.ringChar_eq (semilinearFixedSubfield U.val.right) K).trans
      (ringChar.eq K 2))
  have hord2 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
    (K := semilinearFixedSubfield U.val.right) hn4 hirr'
  rw [← hc, hcardm] at hord2
  push_cast at hord2
  rw [show ((2 : ℤ) ^ m) ^ n + 1 = ((2 : ℤ) ^ m) ^ n - (-1) by ring] at hord2
  obtain ⟨-, -, h⟩ := omega_card_eq_d4_arith hm1 hn4 (Or.inr rfl) hord2
  norm_num at h

end OmegaOuter

section OrthFamily

open CFSG.Assembly.LowTwoRank

theorem pow_eq_one_of_conj_pow_d4cls {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) {p : ℕ}
    {a : S} (h : MulAut.conj a ^ p = 1) : a ^ p = 1 := by
  have hc : a ^ p ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g)
      (show MulAut.conj (a ^ p) = 1 by rw [map_pow]; exact h)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h1]
      _ = a ^ p * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

@[expose] def D4UpOrthIdx (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .D r q ∧ q.p = 2 ∧ q.card ≠ 2 ∧
      ¬ (r = 4 ∧ q.card = 32)) ∨
    ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .twistedD r q ∧ q.p = 2 ∧ q.card ≠ 2

theorem orthogonal_d4_false {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex) (hd : D4UpOrthIdx d.1)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) {β : MulAut S} (hβ : β ^ 5 = 1)
    {T : Subgroup S} (hT : CFSG.Open.IsComponentOf T (fixSubgroup β))
    (hL : Nat.card (↥T ⧸ Subgroup.center ↥T) = 174182400) : False := by
  haveI := hs
  obtain ⟨d, hv⟩ := d
  obtain ⟨e⟩ := he
  obtain ⟨t, n, f, ht, hG, hf2, hD4⟩ : ∃ (t : StatedLieTag) (n f : ℕ),
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ StatedClassicalModel S t n 2 f ∧ 2 ≤ f ∧
        (t = .POmegaPlus → n = 4 → f ≠ 5) := by
    have hexp : ∀ q : TauCeti.PrimePower, q.p = 2 → q.card ≠ 2 → 2 ≤ q.exponent := by
      intro q hq2 hq
      have h1 := q.exponent_pos
      by_contra hlt
      have h2 : q.exponent = 1 := by omega
      exact hq (by rw [TauCeti.PrimePower.card_def, hq2, h2]; norm_num)
    rcases hd with ⟨r, q, rfl, hq2, hq, h432⟩ | ⟨r, q, rfl, hq2, hq⟩
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
      rw [hq2] at hm
      refine ⟨_, r, q.exponent, Or.inl rfl, hm, hexp q hq2 hq, fun _ hr hf5 => h432 ⟨hr, ?_⟩⟩
      rw [TauCeti.PrimePower.card_def, hq2, hf5]
      norm_num
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
      rw [hq2] at hm
      exact ⟨_, r, q.exponent, Or.inr rfl, hm, hexp q hq2 hq, fun h => absurd h (by decide)⟩
  by_cases hin : ∃ a : S, MulAut.conj a = β
  · obtain ⟨a, rfl⟩ := hin
    have hZ : Subgroup.center S = ⊥ :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hna
    exact omega_inner_d4_false ht hG hf2 a (pow_eq_one_of_conj_pow_d4cls hZ hβ) T hT hL
  · have hout : ∀ a : S, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    rcases ht with rfl | rfl
    · exact omega_outer_plus_d4_false hG (hD4 rfl) β hβ hout hT hL
    · exact omega_outer_minus_d4_false hG β hβ hout hT hL

theorem noD4UpOn_orthogonal_d4cls : NoD4UpOn D4UpOrthIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  obtain ⟨hβ5, hβ1⟩ := autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  have hp5 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d.1 ≠ 5 := by
    rcases hd with ⟨r, q, hrq, hq2, -⟩ | ⟨r, q, hrq, hq2, -⟩
    · rw [hrq]
      show q.p ≠ 5
      rw [hq2]
      norm_num
    · rw [hrq]
      show q.p ≠ 5
      rw [hq2]
      norm_num
  have hF : CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .symplecticOrthogonal := by
    rcases hd with ⟨r, q, hrq, -⟩ | ⟨r, q, hrq, -⟩
    · rw [hrq]
      rfl
    · rw [hrq]
      rfl
  have hlay := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_symplecticOrthogonal
    Nat.prime_five le_rfl (K ⧸ Subgroup.center K) hK.1.2 hna d hF he
    (autCenterQuot K x) hβ5 hβ1 (Or.inl hp5)).layer
  obtain ⟨T, hT, hTc⟩ := exists_d4_component_d4cls hD hK.1 hx hlay
  exact orthogonal_d4_false hK.1.2 hna d hd he hβ5 hT hTc

end OrthFamily

section ExcTwoArith

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem eq_one_of_pow_five_of_pow_d4cls {G : Type*} [Monoid G] {y : G} {m : ℕ} (h5 : y ^ 5 = 1)
    (hm : y ^ m = 1) (hcop : Nat.Coprime 5 m) : y = 1 :=
  orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one hm)))

theorem five_cube_dvd_card_of_conj_d4cls {S : Type} [Group S] [Finite S] {a : S} (ha : a ^ 5 = 1)
    (ha1 : a ≠ 1) {T : Subgroup S}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (MulAut.conj a)))
    (hL : Nat.card (↥T ⧸ Subgroup.center ↥T) = 174182400) : 5 ^ 3 ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hTC : T ≤ fixSubgroup (MulAut.conj a) := hT.1
  have hcomm : ∀ t ∈ T, a * t = t * a := fun t ht => by
    have h1 := hTC ht
    rw [mem_fixSubgroup, MulAut.conj_apply] at h1
    calc a * t = a * t * a⁻¹ * a := by group
      _ = t * a := by rw [h1]
  have hTcard : Nat.card T = 174182400 * Nat.card (Subgroup.center T) := by
    rw [(Subgroup.center T).card_eq_card_quotient_mul_card_subgroup, hL]
  have hao : orderOf a = 5 := orderOf_eq_prime ha ha1
  by_cases haT : a ∈ T
  · have hZ : (⟨a, haT⟩ : T) ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (hcomm t t.2).symm
    have h5 : 5 ∣ Nat.card (Subgroup.center T) := by
      have ho : orderOf (⟨⟨a, haT⟩, hZ⟩ : Subgroup.center T) = 5 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hao]
      exact ho ▸ orderOf_dvd_natCard _
    have hT3 : 5 ^ 3 ∣ Nat.card T := by
      rw [hTcard]
      exact (show 5 ^ 3 = 25 * 5 by norm_num) ▸ Nat.mul_dvd_mul (by norm_num) h5
    exact hT3.trans (Subgroup.card_subgroup_dvd_card T)
  · have hdisj : T ⊓ Subgroup.zpowers a = ⊥ := by
      have hcard : Nat.card (Subgroup.zpowers a) = 5 := by rw [Nat.card_zpowers, hao]
      haveI : Fact (Nat.card (Subgroup.zpowers a)).Prime := ⟨by rw [hcard]; exact Nat.prime_five⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card
          ((T ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a)) with h | h
      · rw [eq_bot_iff]
        intro g hg
        have hg' : (⟨g, (Subgroup.mem_inf.1 hg).2⟩ : Subgroup.zpowers a) ∈
            (T ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a) := Subgroup.mem_subgroupOf.2 hg
        rw [h, Subgroup.mem_bot] at hg'
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val hg'
      · exfalso
        apply haT
        have hmem : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) ∈
            (T ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a) := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
    let φ : ↥T × ↥(Subgroup.zpowers a) →* S :=
      MonoidHom.noncommCoprod T.subtype (Subgroup.zpowers a).subtype (fun t z => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
        show Commute (t : S) (z : S)
        rw [← hk]
        exact (Commute.zpow_right (hcomm t t.2).symm k))
    have hφ : Function.Injective φ := by
      rintro ⟨t, z⟩ ⟨t', z'⟩ h
      have h' : (t : S) * (z : S) = (t' : S) * (z' : S) := h
      have hmemT : (t' : S)⁻¹ * t ∈ T := T.mul_mem (T.inv_mem t'.2) t.2
      have hmemZ : (t' : S)⁻¹ * t ∈ Subgroup.zpowers a := by
        have : (t' : S)⁻¹ * t = (z' : S) * (z : S)⁻¹ := by
          calc (t' : S)⁻¹ * t = (t' : S)⁻¹ * (t * z) * (z : S)⁻¹ := by group
            _ = (t' : S)⁻¹ * (t' * z') * (z : S)⁻¹ := by rw [h']
            _ = (z' : S) * (z : S)⁻¹ := by group
        rw [this]
        exact (Subgroup.zpowers a).mul_mem z'.2 ((Subgroup.zpowers a).inv_mem z.2)
      have h1 : (t' : S)⁻¹ * t = 1 := by
        have : (t' : S)⁻¹ * t ∈ T ⊓ Subgroup.zpowers a := Subgroup.mem_inf.2 ⟨hmemT, hmemZ⟩
        rw [hdisj, Subgroup.mem_bot] at this
        exact this
      have htt : (t : S) = t' := by
        have := congrArg ((t' : S) * ·) h1
        simpa using this
      have hzz : (z : S) = z' := by
        rw [htt] at h'
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext htt) (Subtype.ext hzz)
    have hcardφ : Nat.card φ.range = Nat.card T * 5 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hφ).symm.toEquiv, Nat.card_prod, Nat.card_zpowers,
        hao]
    have h3 : 5 ^ 3 ∣ Nat.card φ.range := by
      rw [hcardφ, hTcard]
      exact (show 5 ^ 3 = 25 * 5 by norm_num) ▸
        Nat.mul_dvd_mul ((by norm_num : 25 ∣ 174182400).trans (Dvd.intro _ rfl)) dvd_rfl
    exact h3.trans (Subgroup.card_subgroup_dvd_card _)

end ExcTwoArith

section ExcTwoInner

theorem congr_conj_d4cls {S G : Type*} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_conj_of_congr_d4cls {S G : Type*} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    {g : G} (hg : MulAut.conj g = MulAut.congr e β) : ∃ a : S, MulAut.conj a = β :=
  ⟨e.symm g, (MulAut.congr e).injective (by rw [congr_conj_d4cls, MulEquiv.apply_symm_apply, hg])⟩

theorem false_of_inner_five_d4cls {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    {β : MulAut S} (hβ5 : β ^ 5 = 1) (hβ1 : β ≠ 1) (hin : ∃ a : S, MulAut.conj a = β)
    {T : Subgroup S} (hT : CFSG.Open.IsComponentOf T (fixSubgroup β))
    (hL : Nat.card (↥T ⧸ Subgroup.center ↥T) = 174182400) (hS : ¬ 5 ^ 3 ∣ Nat.card S) : False := by
  obtain ⟨a, rfl⟩ := hin
  have ha5 : a ^ 5 = 1 := pow_eq_one_of_conj_pow_d4cls hZ hβ5
  have ha1 : a ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  exact hS (five_cube_dvd_card_of_conj_d4cls ha5 ha1 hT hL)

@[expose] def D4UpExcTwoIdx : TauCeti.LieTypeIndex → Prop
  | .F4 q | .E6 q | .twistedE6 q | .E7 q | .trialityD4 q => q.card = 2
  | _ => False

end ExcTwoInner

section ExcTwo

open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic
  card_ringAut_and_isCyclic)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

set_option linter.unusedSectionVars false

theorem chevalleyExceptionalModel_of_catalog_d4cls {S : Type} [Group S] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) (d : TauCeti.ValidLieTypeIndex)
    (hadm : StatedLieAdmissible t 0 2 1) (hd : CFSG.Models.NamesTag d.1 t 2 1)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : ChevalleyExceptionalModel S t 2 1 :=
  (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag hadm d hd e)).chevalleyExceptionalModel ht

theorem exists_conj_of_pow_five_F4_two_d4cls {S : Type} [Group S]
    (h : ChevalleyExceptionalModel S .F4 2 1) (β : MulAut S) (hβ : β ^ 5 = 1) :
    ∃ a : S, MulAut.conj a = β := by
  obtain ⟨-, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag hm
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form le_rfl K hK
  have hβ' : MulAut.congr e β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have h2 : ∀ z : Multiplicative (ZMod (2 * 1)), z ^ 2 = 1 := by decide
  have h1 : Θ (MulAut.congr e β) = 1 :=
    eq_one_of_pow_five_of_pow_d4cls (by rw [← map_pow, hβ', map_one]) (h2 _) (by norm_num)
  have hmem : MulAut.congr e β ∈ Θ.ker := h1
  rw [hker] at hmem
  obtain ⟨g, hg⟩ := hmem
  exact exists_conj_of_congr_d4cls e hg

theorem exists_conj_of_pow_five_E_two_d4cls {S : Type} [Group S] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7) (hm : UntwistedChevalleyModel S τ (2 ^ 1)) (β : MulAut S)
    (hβ : β ^ 5 = 1) : ∃ a : S, MulAut.conj a = β := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) (τ := τ)
    (hτ.elim Or.inl fun h => Or.inr (Or.inl h))
  have hβ' : MulAut.congr e β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  set y : Outer (adjointGroup τ K) :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K))
      (MulAut.congr e β) with hy
  have hy5 : y ^ 5 = 1 := by rw [hy, ← map_pow, hβ', map_one]
  have hR : Nat.card (RingAut K) = 1 := (card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hE : exactE τ = 2 ∨ exactE τ = 1 := by
    rcases hτ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcardT : Nat.card (RingAut K × Multiplicative (ZMod (exactE τ))) = exactE τ := by
    rw [Nat.card_prod, hR, one_mul]
    rcases hE with h | h <;> rw [h] <;> simp
  have hΦ : Φ y = 1 :=
    eq_one_of_pow_five_of_pow_d4cls (by rw [← map_pow, hy5, map_one]) pow_card_eq_one'
      (by rw [hcardT]; rcases hE with h | h <;> rw [h] <;> norm_num)
  have hyker : y ∈ Φ.ker := hΦ
  have hdet : τ.cartan.det.natAbs = 3 ∨ τ.cartan.det.natAbs = 2 := by
    rcases hτ with rfl | rfl
    · left
      rw [det_cartan_E6]
      rfl
    · right
      rw [det_cartan_E7]
      rfl
  have hyk : y ^ Nat.card Φ.ker = 1 := by
    have hpow : (⟨y, hyker⟩ : Φ.ker) ^ Nat.card Φ.ker = 1 := pow_card_eq_one'
    have := congrArg Subtype.val hpow
    simpa using this
  have hcop : Nat.Coprime 5 (Nat.card Φ.ker) :=
    Nat.Coprime.coprime_dvd_right hdvd (by rcases hdet with h | h <;> rw [h] <;> norm_num)
  have hy1 : y = 1 := eq_one_of_pow_five_of_pow_d4cls hy5 hyk hcop
  have hinn : MulAut.congr e β ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K) :=
    (QuotientGroup.eq_one_iff _).1 hy1
  obtain ⟨g, hg⟩ := hinn
  exact exists_conj_of_congr_d4cls e hg

theorem exists_conj_of_pow_five_twistedE6_two_d4cls {S : Type} [Group S]
    (h : ChevalleyExceptionalModel S .twistedE6 2 1) (β : MulAut S) (hβ : β ^ 5 = 1) :
    ∃ a : S, MulAut.conj a = β := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel S .E6 (2 ^ 1) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 Nat.prime_two hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf1 K hcard σ' hσ'
  have hβ' : MulAut.congr (e.trans E) β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hcard]; rfl
  have hR : Nat.card (RingAut K) = 2 := (card_ringAut_and_isCyclic Nat.prime_two K hK2).1
  have hΘ : Θ (MulAut.congr (e.trans E) β) = 1 :=
    eq_one_of_pow_five_of_pow_d4cls (m := 2) (by rw [← map_pow, hβ', map_one])
      (by rw [← hR]; exact pow_card_eq_one') (by norm_num)
  have hmem : MulAut.congr (e.trans E) β ∈ Θ.ker := hΘ
  rw [hker] at hmem
  set H := twistedE6Inn K σ' ⊔ twistedE6Diag K σ' with hH
  set y := QuotientGroup.mk' ((twistedE6Inn K σ').subgroupOf H)
    (⟨MulAut.congr (e.trans E) β, hmem⟩ : H) with hy
  have hxp : (⟨MulAut.congr (e.trans E) β, hmem⟩ : H) ^ 5 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hβ')
  have hy5 : y ^ 5 = 1 := by rw [hy, ← map_pow, hxp, map_one]
  have hy1 : y = 1 := eq_one_of_pow_five_of_pow_d4cls hy5 (hcube y) (by norm_num)
  have h2 := (QuotientGroup.eq_one_iff (N := (twistedE6Inn K σ').subgroupOf H) _).1 hy1
  rw [Subgroup.mem_subgroupOf] at h2
  obtain ⟨g, hg⟩ := h2
  exact exists_conj_of_congr_d4cls (e.trans E) hg

theorem noD4UpOn_excTwo_d4cls : NoD4UpOn D4UpExcTwoIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  obtain ⟨hβ5, hβ1⟩ := autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  haveI := hK.1.2
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hna
  obtain ⟨dd, hv⟩ := d
  obtain ⟨e⟩ := he
  have hq : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ (dd = .F4 q ∨ dd = .E6 q ∨ dd = .twistedE6 q ∨
      dd = .E7 q ∨ dd = .trialityD4 q) := by
    cases dd with
    | F4 q => exact ⟨q, hd, Or.inl rfl⟩
    | E6 q => exact ⟨q, hd, Or.inr (Or.inl rfl)⟩
    | twistedE6 q => exact ⟨q, hd, Or.inr (Or.inr (Or.inl rfl))⟩
    | E7 q => exact ⟨q, hd, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    | trialityD4 q => exact ⟨q, hd, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    | _ => exact hd.elim
  obtain ⟨q, hq2, hdd⟩ := hq
  obtain ⟨hp, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 1)
    Nat.prime_two one_pos (hq2.trans (by norm_num))
  have hF : CFSG.Yardstones.Md42047359a2a.lieFamily dd = .exceptional := by
    rcases hdd with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hchar : dd.characteristic = 2 := by
    rcases hdd with rfl | rfl | rfl | rfl | rfl <;> simpa using hp
  have hlay : PerfectInLayer (autCenterQuot K x) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional
      (K ⧸ Subgroup.center K) hK.1.2 hna ⟨dd, hv⟩ hF ⟨e⟩ 5 Nat.prime_five (by norm_num)
      (by rw [hchar]; norm_num) _ hβ5 hβ1
  obtain ⟨T, hT, hTc⟩ := exists_d4_component_d4cls hD hK.1 hx hlay
  have hTdvd : 174182400 ∣ Nat.card (K ⧸ Subgroup.center K) :=
    (hTc ▸ Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card T)
  rcases hdd with rfl | rfl | rfl | rfl | rfl
  · have hc := chevalleyExceptionalModel_of_catalog_d4cls (t := .F4) (by decide) ⟨_, hv⟩
      ⟨Nat.prime_two, le_rfl, rfl⟩ ⟨hp, hf⟩ e
    have hcard : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordF4 (2 ^ 1) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
    exact false_of_inner_five_d4cls hZ hβ5 hβ1 (exists_conj_of_pow_five_F4_two_d4cls hc _ hβ5) hT hTc
      (by rw [hcard]; decide)
  · have hc := chevalleyExceptionalModel_of_catalog_d4cls (t := .E6) (by decide) ⟨_, hv⟩
      ⟨Nat.prime_two, le_rfl, rfl⟩ ⟨hp, hf⟩ e
    have hcard : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordE6 (2 ^ 1) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
    exact false_of_inner_five_d4cls hZ hβ5 hβ1
      (exists_conj_of_pow_five_E_two_d4cls (Or.inl rfl) hc.2 _ hβ5) hT hTc (by rw [hcard]; decide)
  · have hc := chevalleyExceptionalModel_of_catalog_d4cls (t := .twistedE6) (by decide) ⟨_, hv⟩
      ⟨Nat.prime_two, le_rfl, rfl⟩ ⟨hp, hf⟩ e
    have hcard : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordTwistedE6 (2 ^ 1) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
    exact false_of_inner_five_d4cls hZ hβ5 hβ1
      (exists_conj_of_pow_five_twistedE6_two_d4cls hc _ hβ5) hT hTc (by rw [hcard]; decide)
  · have hc := chevalleyExceptionalModel_of_catalog_d4cls (t := .E7) (by decide) ⟨_, hv⟩
      ⟨Nat.prime_two, le_rfl, rfl⟩ ⟨hp, hf⟩ e
    have hcard : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordE7 (2 ^ 1) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
    exact false_of_inner_five_d4cls hZ hβ5 hβ1
      (exists_conj_of_pow_five_E_two_d4cls (Or.inr rfl) hc.2 _ hβ5) hT hTc (by rw [hcard]; decide)
  · have hc := chevalleyExceptionalModel_of_catalog_d4cls (t := .trialityD4) (by decide) ⟨_, hv⟩
      ⟨Nat.prime_two, le_rfl, rfl⟩ ⟨hp, hf⟩ e
    have hcard : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordTrialityD4 (2 ^ 1) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
    rw [hcard] at hTdvd
    revert hTdvd
    decide

end ExcTwo

section Main

@[expose] def D4UpRestIdx : TauCeti.LieTypeIndex → Prop
  | .G2 q | .E8 q => q.p = 2
  | .trialityD4 q | .F4 q | .E6 q | .twistedE6 q | .E7 q => q.p = 2 ∧ q.card ≠ 2
  | .reeF4 _ => True
  | _ => False

theorem chev2Rest_cases_d4cls (d : TauCeti.ValidLieTypeIndex) (h : D4UpChev2RestIdx d.1) :
    D4UpLinearIdx d.1 ∨ D4UpUnitaryIdx d.1 ∨ D4UpSympIdx d.1 ∨ D4UpOrthIdx d.1 ∨
      D4UpExcTwoIdx d.1 ∨ D4UpSzTitsIdx d.1 ∨ D4UpRestIdx d.1 := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨h2, hfree⟩ := h
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hexc : ∀ q : TauCeti.PrimePower, q.p = 2 → (q.card = 2 ∨ (q.p = 2 ∧ q.card ≠ 2)) :=
    fun q hq => (em (q.card = 2)).imp id fun hne => ⟨hq, hne⟩
  cases d with
  | A r q => exact Or.inl ⟨r, q, rfl, by simpa using h2⟩
  | twistedA r q => exact Or.inr (Or.inl ⟨r, q, rfl, by simpa using h2⟩)
  | B r q => exact Or.inr (Or.inr (Or.inl ⟨r, q, rfl, by simpa using h2⟩))
  | C r q => exact absurd (by simpa using h2) hr.2
  | D r q =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨r, q, rfl, by simpa using h2,
      fun hq => hfree (Or.inl hq), fun h4 => hfree (Or.inr h4)⟩))))
  | twistedD r q =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨r, q, rfl, by simpa using h2,
      fun hq => hfree hq⟩))))
  | E6 q =>
    rcases hexc q (by simpa using h2) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  | E7 q =>
    rcases hexc q (by simpa using h2) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  | E8 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (show q.p = 2 by simpa using h2))))))
  | F4 q =>
    rcases hexc q (by simpa using h2) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  | G2 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (show q.p = 2 by simpa using h2))))))
  | twistedE6 q =>
    rcases hexc q (by simpa using h2) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  | trialityD4 q =>
    rcases hexc q (by simpa using h2) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  | suzuki m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨m, rfl⟩))))))
  | reeG2 m => exact absurd h2 (by simp)
  | reeF4 m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trivial)))))
  | tits => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr rfl))))))

end Main

section MainCerts

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables (SporTypes)

open CFSG.LocalAnalysis.GLTheoremA.Chev2Rows (CRow)

set_option linter.unusedSectionVars false

theorem noD4UpOn_chev2Rest_of_rest_d4cls
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (h : NoD4UpOn D4UpRestIdx) :
    NoD4UpOn D4UpChev2RestIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  rcases chev2Rest_cases_d4cls d hd with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact noD4UpOn_linear_d4cls K hK hO d h1 he D hD x hx
  · exact noD4UpOn_unitary_d4cls K hK hO d h1 he D hD x hx
  · exact noD4UpOn_symplectic_d4cls K hK hO d h1 he D hD x hx
  · exact noD4UpOn_orthogonal_d4cls K hK hO d h1 he D hD x hx
  · exact noD4UpOn_excTwo_d4cls K hK hO d h1 he D hD x hx
  · exact noD4UpOn_szTits_d4cls hb K hK hO d h1 he D hD x hx
  · exact h K hK hO d h1 he D hD x hx

end MainCerts

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m
