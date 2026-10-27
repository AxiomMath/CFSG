module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110f
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot autCenterQuot_injective_of_perfect)
open CFSG.LocalAnalysis.ComponentInitial

section Orders

open CFSG.OrderReductions.LinearOrders
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_centralQuotient_mulEquiv)

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem sixty_dvd_card {T : Type*} [Group T] [Finite T]
    (hA : Nonempty ((T ⧸ Subgroup.center T) ≃* alternatingGroup (Fin 5))) : 60 ∣ Nat.card T := by
  obtain ⟨e⟩ := hA
  have h := Subgroup.card_quotient_dvd_card (Subgroup.center T)
  rwa [Nat.card_congr e.toEquiv, card_alt_five] at h

theorem coprime_self_sub_one {Q : ℕ} (hQ : 1 ≤ Q) : Nat.Coprime Q (Q - 1) :=
  (Nat.coprime_self_sub_right hQ).2 (Nat.coprime_one_right Q)

theorem coprime_self_add_one (Q : ℕ) : Nat.Coprime Q (Q + 1) :=
  Nat.coprime_self_add_right.2 (Nat.coprime_one_right Q)

theorem sl_a5 {E : Type*} [Field E] [Finite E] {m : ℕ} (hm : 2 ≤ m)
    {T : Type*} [Group T] (f : Matrix.SpecialLinearGroup (Fin m) E →* T)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _)
    (hA : Nonempty ((T ⧸ Subgroup.center T) ≃* alternatingGroup (Fin 5))) :
    m = 2 ∧ (Nat.card E = 4 ∨ Nat.card E = 5) := by
  haveI : Finite T := Finite.of_surjective f hf
  obtain ⟨eA⟩ := hA
  have hSL := card_specialLinear E m (by omega)
  have hZ := card_specialLinear_center E m (by omega)
  have hQ2 : 2 ≤ Nat.card E := by
    haveI : Fintype E := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have h60 : 60 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) E) :=
    (sixty_dvd_card ⟨eA⟩).trans (Subgroup.card_dvd_of_surjective hf)
  have hSL2 : m = 2 → Nat.card (Matrix.SpecialLinearGroup (Fin m) E) =
      Nat.card E * (Nat.card E ^ 2 - 1) := by
    rintro rfl
    rw [hSL]
    simp
  have hperf : 3 ≤ m ∨ 4 ≤ Nat.card E := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hm3, hE4⟩ := hcon
    obtain rfl : m = 2 := by omega
    rw [hSL2 rfl] at h60
    obtain h | h : Nat.card E = 2 ∨ Nat.card E = 3 := by omega
    · rw [h] at h60
      norm_num at h60
    · rw [h] at h60
      norm_num at h60
  have hq := CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm hperf
  have hcomm : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ := hq.1.commutator_eq_top
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hcomm f hf hker
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) =
      60 * Nat.gcd m (Nat.card E - 1) := by
    rw [(Subgroup.center
        (Matrix.SpecialLinearGroup (Fin m) E)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (e.trans eA).toEquiv, card_alt_five, hZ]
  have hdvd : Nat.card E ^ (m * (m - 1) / 2) ∣ 60 * Nat.gcd m (Nat.card E - 1) := by
    rw [← hcard, hSL]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (Nat.card E ^ (m * (m - 1) / 2)) (Nat.gcd m (Nat.card E - 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_self_sub_one (by omega)))
  have h60' : Nat.card E ^ (m * (m - 1) / 2) ∣ 60 := hcop.dvd_of_dvd_mul_right hdvd
  have hm2 : m = 2 := by
    by_contra hne
    have h6 : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : 3 ≤ m * (m - 1) / 2 := by omega
    have hQ3 : Nat.card E ^ 3 ∣ 60 := (pow_dvd_pow _ h3).trans h60'
    have hle : Nat.card E ^ 3 ≤ 60 := Nat.le_of_dvd (by norm_num) hQ3
    have hQ : Nat.card E ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have : 4 ^ 3 ≤ Nat.card E ^ 3 := Nat.pow_le_pow_left hlt 3
      omega
    obtain h | h : Nat.card E = 2 ∨ Nat.card E = 3 := by omega
    · rw [h] at hQ3
      norm_num at hQ3
    · rw [h] at hQ3
      norm_num at hQ3
  subst hm2
  refine ⟨rfl, ?_⟩
  rw [hSL2 rfl] at hcard
  have hg : Nat.gcd 2 (Nat.card E - 1) = 1 ∨ Nat.gcd 2 (Nat.card E - 1) = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 (Nat.gcd_dvd_left _ _)
  have h120 : Nat.card E * (Nat.card E ^ 2 - 1) = 60 ∨
      Nat.card E * (Nat.card E ^ 2 - 1) = 120 := by
    rcases hg with h | h
    · left
      rw [hcard, h]
    · right
      rw [hcard, h]
  have hQ5 : Nat.card E ≤ 5 := by
    by_contra hlt
    push Not at hlt
    have h1 : 6 ^ 2 ≤ Nat.card E ^ 2 := Nat.pow_le_pow_left hlt 2
    have h2 : 6 * 35 ≤ Nat.card E * (Nat.card E ^ 2 - 1) := Nat.mul_le_mul hlt (by omega)
    omega
  obtain h | h | h | h : Nat.card E = 2 ∨ Nat.card E = 3 ∨ Nat.card E = 4 ∨ Nat.card E = 5 := by
    omega
  · rw [h] at h120
    norm_num at h120
  · rw [h] at h120
    norm_num at h120
  · exact Or.inl h
  · exact Or.inr h

theorem su_a5_false {E : Type} [Field E] {ℓ e m : ℕ} (hE : UnitaryFieldData ℓ e E)
    (hm : 3 ≤ m) {T : Type*} [Group T]
    (g : ↥(StatedSU m (ℓ ^ e) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _)
    (hA : Nonempty ((T ⧸ Subgroup.center T) ≃* alternatingGroup (Fin 5))) : False := by
  haveI := hE.finite
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  have he : 1 ≤ e := hE.one_le
  have hF : Nat.card E = (ℓ ^ e) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
  haveI : Finite T := Finite.of_surjective g hg
  obtain ⟨eA⟩ := hA
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hE (n := m) (by omega)
  have h60 : 60 ∣ Nat.card ↥(StatedSU m (ℓ ^ e) E) :=
    (sixty_dvd_card ⟨eA⟩).trans (Subgroup.card_dvd_of_surjective hg)
  have hQ2 : 2 ≤ ℓ ^ e := le_trans hE.prime.two_le (Nat.le_self_pow (by omega) ℓ)
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
    rw [h216'] at h60
    norm_num at h60
  · obtain ⟨hqs, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hm hnq
    have hcomm : commutator ↥(StatedSU m (ℓ ^ e) E) = ⊤ := hqs.1.commutator_eq_top
    obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hcomm g hg hker
    have hZ : Nat.card ↥(Subgroup.center ↥(StatedSU m (ℓ ^ e) E)) = Nat.gcd m (ℓ ^ e + 1) := by
      have h1 := CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hE (n := m) (by omega)
      rw [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hE (by omega)] at h1
      rw [hcen]
      exact h1
    have hcard : Nat.card ↥(StatedSU m (ℓ ^ e) E) = 60 * Nat.gcd m (ℓ ^ e + 1) := by
      rw [(Subgroup.center ↥(StatedSU m (ℓ ^ e) E)).card_eq_card_quotient_mul_card_subgroup,
        Nat.card_congr (eq.trans eA).toEquiv, card_alt_five, hZ]
    have hdvdZ : (((ℓ ^ e) ^ (m * (m - 1) / 2) : ℕ) : ℤ) ∣
        (Nat.card ↥(StatedSU m (ℓ ^ e) E) : ℤ) := by
      rw [hint]
      push_cast
      exact Dvd.intro _ rfl
    have hdvd : (ℓ ^ e) ^ (m * (m - 1) / 2) ∣ 60 * Nat.gcd m (ℓ ^ e + 1) := by
      rw [← hcard]
      exact Int.natCast_dvd_natCast.mp hdvdZ
    have hcop : Nat.Coprime ((ℓ ^ e) ^ (m * (m - 1) / 2)) (Nat.gcd m (ℓ ^ e + 1)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
        (coprime_self_add_one _))
    have h60' : (ℓ ^ e) ^ (m * (m - 1) / 2) ∣ 60 := hcop.dvd_of_dvd_mul_right hdvd
    have h6 : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    have h3 : 3 ≤ m * (m - 1) / 2 := by omega
    have hQ3 : (ℓ ^ e) ^ 3 ∣ 60 := (pow_dvd_pow _ h3).trans h60'
    have hle : (ℓ ^ e) ^ 3 ≤ 60 := Nat.le_of_dvd (by norm_num) hQ3
    have hQ : ℓ ^ e ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have : 4 ^ 3 ≤ (ℓ ^ e) ^ 3 := Nat.pow_le_pow_left hlt 3
      omega
    obtain h | h : ℓ ^ e = 2 ∨ ℓ ^ e = 3 := by omega
    · rw [h] at hQ3
      norm_num at hQ3
    · rw [h] at hQ3
      norm_num at hQ3

end Orders

section Descent

theorem nonempty_centerQuot_equiv_of_surjective {G A : Type*} [Group G] [Group A] (ψ : G →* A)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
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

theorem exists_a5_component {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    {x : MulAut K} (hx : Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x)
    (hlay : PerfectInLayer (autCenterQuot K x)) :
    ∃ T : Subgroup (K ⧸ Subgroup.center K),
      IsComponentOf T (fixSubgroup (autCenterQuot K x)) ∧
        Nonempty ((↥T ⧸ Subgroup.center ↥T) ≃* alternatingGroup (Fin 5)) := by
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
  have hne : GLAPPrimeCore 5 ↥J1 ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (barOf 5 J1) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _)
    have h1 : Nat.card (barOf 5 J1) = 1 := Nat.card_unique
    rw [Nat.card_congr eA.toEquiv, card_alt_five] at h1
    norm_num at h1
  have hO : GLAPPrimeCore 5 ↥J1 ≤ Subgroup.center ↥J1 :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJq
      (GLAPPrimeCore.normal 5 ↥J1) hne
  set χ : ↥J1 →* ↥(alternatingGroup (Fin 5)) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J1)) with hχ
  have hχs : Function.Surjective χ := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hχk : χ.ker ≤ Subgroup.center ↥J1 := by
    intro y hy
    apply hO
    have h1 : eA (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J1) y) = 1 := hy
    rw [map_eq_one_iff _ eA.injective] at h1
    exact (QuotientGroup.eq_one_iff y).1 h1
  have hZA : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊥ :=
    Claims1110e.center_eq_bot_of_isAltType_five ⟨MulEquiv.refl _⟩
  obtain ⟨eZ⟩ := nonempty_centerQuot_equiv_of_surjective χ hχs hχk hZA
  exact ⟨eJ.symm.trans eZ⟩

end Descent

section Linear

open Polynomial CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem a5Center_map {S T : Type*} [Group S] [Group T] (e : S ≃* T) {K : Subgroup S}
    (h : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) :
    Nonempty ((↥(K.map (e : S →* T)) ⧸ Subgroup.center ↥(K.map (e : S →* T))) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨f⟩ := h
  exact ⟨(InputsL33.centerQuotCongr (K.equivMapOfInjective (e : S →* T) e.injective)).symm.trans f⟩

theorem linear_inner_a5_false {n : ℕ} {k : Type} [Field k] [Finite k] (hk6 : 6 ≤ Nat.card k)
    (hpk : ((5 : ℕ) : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)))
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
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
  obtain ⟨-, hE⟩ := sl_a5 hm f hf hker hL
  have hle : Nat.card k ≤ Nat.card (AdjoinRoot h.1.1) :=
    Nat.card_le_card_of_injective (algebraMap k (AdjoinRoot h.1.1))
      (algebraMap k (AdjoinRoot h.1.1)).injective
  omega

theorem linear_field_a5_false {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k]
    (σ : k ≃+* k) (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.fieldAut n k σ)))
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨-, f, hf, hker⟩ := linearFieldAut_components (by omega) σ K hK
  obtain ⟨hn2, -⟩ := sl_a5 (by omega) f hf hker hL
  omega

theorem linear_a5_false {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (h5 : 5 ∣ q.card - 1) (hr : 2 ≤ r)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 5 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hq2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)
  have hk6 : 6 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcard]
    omega
  have hp5 : q.p ≠ 5 := by
    intro hp
    have h5q : 5 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hp]
      exact dvd_pow_self 5 q.exponent_pos.ne'
    omega
  have hpk : ((5 : ℕ) : GaloisField q.p q.exponent) ≠ 0 := by
    rw [Ne, ringChar.spec, ringChar.eq (GaloisField q.p q.exponent) q.p]
    intro hdvd
    exact hp5 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_five).1 hdvd)
  have hβ' : MulAut.congr e' α ^ 5 = 1 := by rw [← map_pow, hα, map_one]
  have hK' := InputsL33.isComponentOf_map_congr e' hK
  have hL' := a5Center_map e' hL
  rcases InputsL33.linear_cases_of_three_le Nat.prime_five (by norm_num) (by omega)
      (MulAut.congr e' α) hβ' with ⟨A, c, hA, hβA⟩ | ⟨h, σ, -, hβh⟩
  · rw [hβA] at hK'
    exact linear_inner_a5_false hk6 hpk hA _ hK' hL'
  · have hβφ : MulAut.congr (h⁻¹ : MulAut _) (MulAut.congr e' α) =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by
      rw [InputsL33.congr_self_eq, hβh]
      group
    have hK'' := InputsL33.isComponentOf_map_congr (h⁻¹ : MulAut _) hK'
    rw [hβφ] at hK''
    exact linear_field_a5_false (by omega) σ _ hK'' (a5Center_map (h⁻¹ : MulAut _) hL')

end Linear

section UnitaryFamily

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

section Factor

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem good_block_a5 (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {T : Type} [Group T] (g : ↥(specialBlock B x (a : K[X])) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _)
    (hL : Nonempty ((T ⧸ Subgroup.center T) ≃* alternatingGroup (Fin 5))) : ℓ ^ f ≤ 5 := by
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hℓ1 : 1 ≤ ℓ := hK.prime.one_lt.le
  have hfle : ℓ ^ f ≤ ℓ ^ (f * (a : K[X]).natDegree) :=
    Nat.pow_le_pow_right hℓ1 (Nat.le_mul_of_pos_right f hd)
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      have hcardF : Nat.card hE.fixedField = ℓ ^ (f * (a : K[X]).natDegree) := hE.card_fixedField
      have hφ := InputsL33.ker_comp_mulEquiv_le_center (e.trans e2).symm g hker
      obtain ⟨-, h45⟩ := sl_a5 le_rfl (g.comp (e.trans e2).symm.toMonoidHom)
        (hg.comp (e.trans e2).symm.surjective) hφ hL
      omega
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (e.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hφ := InputsL33.ker_comp_mulEquiv_le_center e4.symm g hker
      exact (su_a5_false (m := primaryMultiplicity (x : Module.End K V) (a : K[X])) hE hm
        (g.comp e4.symm.toMonoidHom) (hg.comp e4.symm.surjective) hφ hL).elim
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot hK
    have hφ := InputsL33.ker_comp_mulEquiv_le_center e.symm g hker
    obtain ⟨-, h45⟩ := sl_a5 hm2 (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective) hφ hL
    have h2 : ℓ ^ (f * (a : K[X]).natDegree) ≤ ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      Nat.pow_le_pow_right hℓ1 (by omega)
    omega

end Factor

section Assembly

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem unitary_inner_a5 {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (T : Subgroup (primeFormP h (idGram K n)))
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A)))
    (hL : Nonempty ((↥T ⧸ Subgroup.center ↥T) ≃* alternatingGroup (Fin 5))) : ℓ ^ f ≤ 5 := by
  classical
  haveI := h.finite
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have H := primaryData_toLin' h A.2 hp hpℓ hA
  obtain ⟨a, ha⟩ := exists_good_primaryFactor_of_component hq A rfl H T hT
  have hSle : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  let F : Subgroup ↥(gramSU h (idGram K n)) :=
    (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])).comap (toLinSU h n)
  have hFmap : F.map (toLinSU h n) = specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X]) :=
    Subgroup.map_comap_eq_self hSle
  let ε : ↥(specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])) ≃* ↥F :=
    ((Subgroup.equivMapOfInjective F (toLinSU h n) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)).symm
  let π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  haveI : Finite ↥F := inferInstance
  subst ha
  refine good_block_a5 H a.1 a.2 ((π.subgroupMap F).comp ε.toMonoidHom)
    ((MonoidHom.subgroupMap_surjective π F).comp ε.surjective) (fun u hu => ?_) hL
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
  have h1 : π (ε u : ↥(gramSU h (idGram K n))) = 1 := congrArg Subtype.val hu
  have h2 : ((ε u : ↥F) : ↥(gramSU h (idGram K n))) ∈
      normOneScalars h (gramSU h (idGram K n)) n := (QuotientGroup.eq_one_iff _).1 h1
  have h3 := normOneScalars_le_center h _ n h2
  rw [Subgroup.mem_center_iff]
  intro w
  apply ε.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 h3 _

end Assembly

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem unitary_a5 {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (h5 : 5 ∣ q.card + 1)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 5 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : q.card = 4 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp5 : (5 : ℕ).Prime := Nat.prime_five
  have hq2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)
  have hqp5 : q.p ≠ 5 := by
    intro hp
    have h5q : 5 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hp]
      exact dvd_pow_self 5 q.exponent_pos.ne'
    omega
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
  have hL1 := a5Center_map e' hL
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
    have hle := unitary_inner_a5 hp5 (Ne.symm hqp5) A hAp _ hK1 hL1
    rw [TauCeti.PrimePower.card_def] at h5 hq2 ⊢
    omega
  ·
    exfalso
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
    have hL2 := a5Center_map ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hL1
    obtain ⟨-, g, hg, hgk⟩ :=
      unitary_fieldAut_components h hn3 hC hp5 (by norm_num) hσp _ hK2
    exact su_a5_false (CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp5 (by norm_num)
      hσp) hn3 g hg hgk hL2

end Unitary

end UnitaryFamily

section Main

open CFSG.LocalAnalysis.GLTheoremA (IsKHat IsLnEps qEps isLnEps)
open CFSG.Yardstones.Md0ec50421ce4 (onLie)

theorem isLnEps_cases {S : Type} [Group S] {n q : ℕ} {lin : Bool} (h : IsLnEps S n q lin) :
    (lin = true ∧ ∃ (r : ℕ) (qq : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r qq).Valid),
      r + 1 = n ∧ qq.card = q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r qq, hv⟩).Group)) ∨
    (lin = false ∧ ∃ (r : ℕ) (qq : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedA r qq).Valid),
      r + 1 = n ∧ qq.card = q ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r qq, hv⟩).Group)) := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases lin <;> cases d <;> simp only [onLie, isLnEps] at hi
    · exact Or.inr ⟨rfl, _, _, hv, hi.1, hi.2, he⟩
    · exact Or.inl ⟨rfl, _, _, hv, hi.1, hi.2, he⟩
  | cyclic _ _ => exact (hi : False).elim
  | alternating _ _ => exact (hi : False).elim
  | sporadic _ => exact (hi : False).elim

theorem inputA5UpLn_holds : Claims1110f.InputA5UpLn := by
  intro K _ _ hK _ n q lin hL h5 x hx
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  have hx5 : x ^ 5 = 1 := by rw [← hx.1]; exact pow_orderOf_eq_one x
  have hβ5 : autCenterQuot K x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hβ1 : autCenterQuot K x ≠ 1 := by
    intro h1
    have h2 : x = 1 := autCenterQuot_injective_of_perfect hK.1.1 (by rw [h1, map_one])
    have h3 := hx.1
    rw [h2, orderOf_one] at h3
    norm_num at h3
  have h5n : 5 ∣ n := h5.trans (Nat.gcd_dvd_left _ _)
  have h5q : 5 ∣ qEps lin q := h5.trans (Nat.gcd_dvd_right _ _)
  rcases isLnEps_cases hL with ⟨rfl, r, qq, hv, hrn, hqq, he⟩ | ⟨rfl, r, qq, hv, hrn, hqq, he⟩
  ·
    exfalso
    subst hqq
    have h5q' : 5 ∣ qq.card - 1 := by simpa [qEps] using h5q
    have hq2 : 2 ≤ qq.card := by
      rw [TauCeti.PrimePower.card_def]
      exact le_trans qq.prime_p.two_le (Nat.le_self_pow qq.exponent_pos.ne' _)
    have hp5 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar
        (TauCeti.LieTypeIndex.A r qq) ≠ 5 := by
      show qq.p ≠ 5
      intro hp
      have h5c : 5 ∣ qq.card := by
        rw [TauCeti.PrimePower.card_def, hp]
        exact dvd_pow_self 5 qq.exponent_pos.ne'
      omega
    have hlay := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_linearUnitary
      Nat.prime_five (by norm_num) (K ⧸ Subgroup.center K) hK.1.2 hna ⟨.A r qq, hv⟩ rfl he
      (autCenterQuot K x) hβ5 hβ1 (Or.inl hp5)).layer
    obtain ⟨T, hT, hTA⟩ := exists_a5_component hK.1 hx hlay
    exact linear_a5_false r qq hv h5q' (by omega) he hβ5 hT hTA
  ·
    subst hqq
    have h5q' : 5 ∣ qq.card + 1 := by simpa [qEps] using h5q
    have hq2 : 2 ≤ qq.card := by
      rw [TauCeti.PrimePower.card_def]
      exact le_trans qq.prime_p.two_le (Nat.le_self_pow qq.exponent_pos.ne' _)
    have hp5 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar
        (TauCeti.LieTypeIndex.twistedA r qq) ≠ 5 := by
      show qq.p ≠ 5
      intro hp
      have h5c : 5 ∣ qq.card := by
        rw [TauCeti.PrimePower.card_def, hp]
        exact dvd_pow_self 5 qq.exponent_pos.ne'
      omega
    have hlay := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_linearUnitary
      Nat.prime_five (by norm_num) (K ⧸ Subgroup.center K) hK.1.2 hna ⟨.twistedA r qq, hv⟩ rfl
      he (autCenterQuot K x) hβ5 hβ1 (Or.inl hp5)).layer
    obtain ⟨T, hT, hTA⟩ := exists_a5_component hK.1 hx hlay
    have h4 : qq.card = 4 := unitary_a5 r qq hv h5q' he hβ5 hT hTA
    obtain ⟨e⟩ := he
    obtain ⟨-, F, _, _, hF, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r qq hv e
    have hq4 : qq.p ^ qq.exponent = 4 := by rw [← TauCeti.PrimePower.card_def]; exact h4
    have key : ∀ Q : ℕ, Q = 4 → Nat.card F = Q ^ 2 →
        (K ⧸ Subgroup.center K ≃* StatedProj (StatedSU (r + 1) Q F)) →
          IsUpType (r + 1) 4 (K ⧸ Subgroup.center K) := by
      rintro Q rfl hFQ eQ
      exact ⟨F, inferInstance, inferInstance, hFQ, ⟨eQ⟩⟩
    obtain ⟨k, hk⟩ := h5n
    refine ⟨k, by omega, ?_⟩
    rw [← hk, ← hrn]
    exact key _ hq4 hF eT

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h
