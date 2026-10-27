module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02SignSL2
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02QuatTensor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Top3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Layer

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedD4
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section Counting

variable {K : Type} [Group K] [Finite K]

theorem card_sup_mul_card_inf_of_comm (L R : Subgroup K)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup K) * Nat.card (L ⊓ R : Subgroup K) = Nat.card L * Nat.card R := by
  let μ : L × R →* K := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : K) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup K) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : K), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : K)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

theorem card_inf_eq_of_normal {A B N : Subgroup K} (hNB : N ≤ B)
    (hn : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N)
    (hAB : Nat.card ↥(A ⊓ B) = 2 ^ (Nat.card ↥B).factorization 2) :
    Nat.card ↥(A ⊓ N) = 2 ^ (Nat.card ↥N).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card ↥((A ⊓ B).subgroupOf B) = 2 ^ (Nat.card ↥B).factorization 2 := by
    rw [← hAB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  let S : Sylow 2 ↥B := Sylow.ofCard _ hS
  haveI : (N.subgroupOf B).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hn g g.2 x hx⟩
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal S (N := N.subgroupOf B)
  have hcard := Sylow.card_eq_multiplicity Q
  have h1 : Nat.card ↥(Q : Subgroup ↥(N.subgroupOf B)) = Nat.card ↥(A ⊓ N) := by
    rw [hQ]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans ?_
    have hSc : (S : Subgroup ↥B) = (A ⊓ B).subgroupOf B := rfl
    have : (S : Subgroup ↥B) ⊓ N.subgroupOf B = (A ⊓ N).subgroupOf B := by
      rw [hSc]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, x.2⟩, h3⟩⟩
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hNB)).toEquiv
  have h2 : Nat.card ↥(N.subgroupOf B) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  rw [← h1, hcard, h2]

end Counting

section Dat410

variable {K : Type} [Group K] [Finite K]

theorem card_sylow_inf_of_le (P : Sylow 2 K) {C : Subgroup K} (hPC : (P : Subgroup K) ≤ C) :
    Nat.card ↥((P : Subgroup K) ⊓ C) = 2 ^ (Nat.card ↥C).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inf_of_le_left hPC]
  have h := Sylow.card_eq_multiplicity (P.subtype hPC)
  rw [← h]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).symm

theorem quatIn_of_sylow_sl2 {q : ℕ} (hq : Odd q) {E₁ Q₁ : Subgroup K} {z : K}
    (hsl2 : HasSL2Model ↥E₁ (fun r => r = q)) (hQE : Q₁ ≤ E₁)
    (hQcard : Nat.card ↥Q₁ = 2 ^ (Nat.card ↥E₁).factorization 2) (hzQ : z ∈ Q₁)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : QuatIn z Q₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, iF, fF, hF, ⟨e⟩⟩ := hsl2
  have hFodd : Odd (Nat.card F) := by rw [show Nat.card F = q from hF]; exact hq
  let e' : ↥E₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hS : Nat.card ↥(Q₁.subgroupOf E₁) = 2 ^ (Nat.card ↥E₁).factorization 2 := by
    rw [← hQcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv
  let S₁ : Sylow 2 ↥E₁ := Sylow.ofCard _ hS
  have hS₁ : (S₁ : Subgroup ↥E₁) = Q₁.subgroupOf E₁ := rfl
  let P₂ : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    S₁.mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨n, hn3, ⟨eq⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hFodd P₂
  have hP₂ : (P₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (Q₁.subgroupOf E₁).map e'.toMonoidHom := by
    rw [← hS₁]
    exact Sylow.coe_mapSurjective _ _
  let eQ : ↥Q₁ ≃* ↥(P₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    ((Subgroup.subgroupOfEquivOfLe hQE).symm.trans
      (Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective)).trans
        (MulEquiv.subgroupCongr hP₂.symm)
  have hz2' : (⟨z, hzQ⟩ : ↥Q₁) * ⟨z, hzQ⟩ = 1 := Subtype.ext hz2
  have hz1' : (⟨z, hzQ⟩ : ↥Q₁) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hm : ∃ h, 2 ^ (n - 2) = 2 * h :=
    ⟨2 ^ (n - 3), by rw [show n - 2 = (n - 3) + 1 by omega, pow_succ, mul_comm]⟩
  exact QuatIn.of_quatData hzQ
    (QuatData.of_equiv_quaternion hm (pow_pos (by norm_num) _) (eQ.trans eq) hz2' hz1')

end Dat410


section OddData

theorem shape_ch6Rem_odd {M : Type} [Group M] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] {z : M} (S : Shape ↥(centralizer ({z} : Set M)) F₁ F₂) (hz : (S.z : M) = z)
    (h₁ : Odd (Nat.card F₁)) (h₂ : Odd (Nat.card F₂)) :
    ∃ (K₁ K₂ : Subgroup M) (t : M), (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂ ∧
      K₁ ⊓ K₂ = zpowers z ∧ Ch6Rem z K₁ K₂ F₁ F₂ t := by
  have hinj : Function.Injective (centralizer ({z} : Set M)).subtype := Subtype.val_injective
  have hO : oPrimeResidualOf 2 (centralizer ({z} : Set M)) = centralizer ({z} : Set M) := by
    rw [oPrimeResidualOf, S.oPrimeResidual_eq_top_of_odd h₁ h₂, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hgenC : S.I₁.map (centralizer ({z} : Set M)).subtype ⊔
      S.I₂.map (centralizer ({z} : Set M)).subtype ⊔ zpowers (S.t : M) =
        centralizer ({z} : Set M) := by
    have h := congrArg (Subgroup.map (centralizer ({z} : Set M)).subtype) S.gen
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hzC : (S.t : M) * z = z * (S.t : M) := Subgroup.mem_centralizer_singleton_iff.1 S.t.2
  refine ⟨S.I₁.map (centralizer ({z} : Set M)).subtype,
    S.I₂.map (centralizer ({z} : Set M)).subtype, (S.t : M), ?_, ⟨S.z, S.z_mem₁, hz⟩,
    ⟨S.z, S.z_mem₂, hz⟩, ?_, hzC, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (S.comm a ha b hb)
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, S.inter, MonoidHom.map_zpowers, Subgroup.coe_subtype, hz]
  · exact congrArg Subtype.val S.t_sq
  · rw [hgenC, hO]
  · exact ⟨(Subgroup.equivMapOfInjective S.I₁ (centralizer ({z} : Set M)).subtype hinj).symm.trans
      S.e₁, S.g₁, S.ns₁, actsAsConj_map _ hinj S.act₁⟩
  · exact ⟨(Subgroup.equivMapOfInjective S.I₂ (centralizer ({z} : Set M)).subtype hinj).symm.trans
      S.e₂, S.g₂, S.ns₂, actsAsConj_map _ hinj S.act₂⟩

theorem ivk_D4_ch6Rem_odd {p f : ℕ} [Fact p.Prime] {M : Type} [Group M] (hp2 : p ≠ 2)
    (hM : LieModel M .trialityD4 0 p f) (z : M) (hz : orderOf z = 2) :
    ∃ (K₁ K₂ : Subgroup M) (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁)
      (_ : Finite F₂) (t : M),
      Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f ∧ (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧
        z ∈ K₁ ∧ z ∈ K₂ ∧ K₁ ⊓ K₂ = Subgroup.zpowers z ∧ Ch6Rem z K₁ K₂ F₁ F₂ t := by
  have hf := one_le_of_lieModel_D4 hM
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hM
  have hD : D4Data (GaloisField p (3 * f)) (sig0 p f) (p ^ f) := d4Data_sig0 hp2 hf
  have hσ := hD.sigma3
  have hcardF : Nat.card (fixedField (sig0 p f)) = p ^ f :=
    card_fixedField_eq (Fact.out : p.Prime) hf hD.card hD.frob
  have hsq : φ z * φ z = 1 ∧ φ z ≠ 1 := by
    refine ⟨?_, ?_⟩
    · rw [← pow_two, ← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    · intro h
      have : z = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf
    hsq.1 (tauL_mul_self hσ) hsq.2 (tauL_ne_one hσ hD.neg_one)
  let ψ : M ≃* twistedGroup (sig0 p f) := φ.trans (MulAut.conj g)
  have hψz : ψ z = τL hσ := hg
  have hzz : ψ.symm (τL hσ) = z := by rw [← hψz, MulEquiv.symm_apply_apply]
  obtain ⟨S, hS⟩ := exists_native_shape_d4 hσ hD
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hodd₁ : Odd (Nat.card (GaloisField p (3 * f))) := by rw [hD.card]; exact hodd.pow
  have hodd₂ : Odd (Nat.card (fixedField (sig0 p f))) := by rw [hcardF]; exact hodd
  obtain ⟨K₁, K₂, t, hcomm, hz₁, hz₂, hinter, hRem⟩ :=
    shape_ch6Rem_odd (z := τL hσ) S (by rw [hS]; rfl) hodd₁ hodd₂
  have key := ch6Data_map ψ.symm ⟨hcomm, hz₁, hz₂, hinter, hRem⟩
  rw [hzz] at key
  exact ⟨K₁.map ψ.symm.toMonoidHom, K₂.map ψ.symm.toMonoidHom, GaloisField p (3 * f),
    fixedField (sig0 p f), inferInstance, inferInstance, inferInstance, inferInstance, ψ.symm t,
    hD.card, hcardF, key⟩

end OddData

section Fixed

variable {K : Type} [Group K]

theorem fixedPoints_card_even {α : Type} [Finite α] (T : α → α) (hT : ∀ x, T (T x) = x)
    (h : 2 ∣ Nat.card α) : 2 ∣ Nat.card {x // T x = x} := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (show Function.End α from T) ^ 2 ^ 1 = (1 : Function.End α) := by
    refine funext fun x => ?_
    exact hT x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hpow
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hfix : Nat.card (Function.fixedPoints (T : Function.End α)) = Nat.card {x // T x = x} := rfl
  rw [hfix] at hmod
  unfold Nat.ModEq at hmod
  omega


theorem two_ne_zero_of_odd_card (F : Type) [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  intro h2
  haveI := Fintype.ofFinite F
  have hdvd : ringChar F ∣ 2 :=
    (CharP.cast_eq_zero_iff F (ringChar F) 2).mp (by exact_mod_cast h2)
  have hne1 : ringChar F ≠ 1 := CharP.ringChar_ne_one
  have h2c : ringChar F = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hev := FiniteField.even_card_iff_char_two.mp h2c
  rw [Nat.card_eq_fintype_card] at h
  rw [Nat.odd_iff] at h
  omega

theorem four_dvd_card_of_quatIn [Finite K] {z : K} {Q : Subgroup K} (hQ : QuatIn z Q) :
    4 ∣ Nat.card Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, haz⟩ := hQ.exists_sq
  have h1 : ¬ a ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, haz]
    exact hQ.ne_one
  have hsq2 : a ^ 2 = z := by rw [pow_two, haz]
  have h4 : a ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq2, pow_two, hQ.sq]
  have h2 : a ^ 2 ^ (1 + 1) = 1 := by
    norm_num
    exact h4
  have hord : orderOf a = 4 := by
    rw [orderOf_eq_prime_pow h1 h2]
    norm_num
  have hcard : Nat.card (zpowers a) = 4 := by rw [Nat.card_zpowers, hord]
  have hd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ha)
  rwa [hcard] at hd

theorem conj_eq_of_quatIn {z : K} {Q : Subgroup K} (hQ : QuatIn z Q) {g : K} (hg : g ∈ Q) :
    g * z * g⁻¹ = z := by
  have hw : g * z * g⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hg hQ.mem) (Q.inv_mem hg)
  have hw2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hQ.sq]; group
  rcases hQ.unique _ hw hw2 with h | h
  · exfalso
    apply hQ.ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group
  · exact h

theorem exists_fixed_pair [Finite K] {Q : Subgroup K} {z f : K} (hQ : QuatIn z Q)
    (h4 : 4 ∣ Nat.card Q) (hf2 : f * f = 1) (hfz : f * z * f⁻¹ = z)
    (hfQ : ∀ g ∈ Q, f * g * f⁻¹ ∈ Q) (hnf : ∀ r ∈ Q, r * r = z → f * r * f⁻¹ ≠ r) :
    ∃ r ∈ Q, r * r = z ∧ f * r * f⁻¹ = r * z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨zQ, hzQdef⟩ : ∃ zQ : Q, zQ = ⟨z, hQ.mem⟩ := ⟨_, rfl⟩
  have hzQK : (zQ : K) = z := by rw [hzQdef]
  have hzQ2 : zQ * zQ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one, hzQK, hQ.sq]
  have hzQ1 : zQ ≠ 1 := fun h => hQ.ne_one (by rw [← hzQK, h, Subgroup.coe_one])
  have hzQ2' : zQ ^ 2 = 1 := by rw [pow_two]; exact hzQ2
  have hcen : zQ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hc := conj_eq_of_quatIn hQ g.2
    simp only [Subgroup.coe_mul, hzQK]
    calc (g : K) * z = (((g : K) * z * (g : K)⁻¹) * (g : K)) := by group
      _ = z * (g : K) := by rw [hc]
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Q, N = Subgroup.zpowers zQ := ⟨_, rfl⟩
  haveI : N.Normal := by
    rw [hN]
    exact Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcen)
  let φ : Q →* K := (MulAut.conj f).toMonoidHom.comp Q.subtype
  let σ : Q →* Q := φ.codRestrict Q (fun g => hfQ g.1 g.2)
  have hσ : ∀ g : Q, (σ g : K) = f * g * f⁻¹ := fun g => rfl
  have hσσ : ∀ g : Q, σ (σ g) = g := by
    intro g
    apply Subtype.ext
    rw [hσ, hσ]
    calc f * (f * (g : K) * f⁻¹) * f⁻¹ = (f * f) * (g : K) * (f * f)⁻¹ := by group
      _ = (g : K) := by rw [hf2]; group
  have hσz : σ zQ = zQ := by
    apply Subtype.ext
    rw [hσ, hzQK]
    exact hfz
  have hNσ : N ≤ N.comap σ := by
    rw [hN, Subgroup.zpowers_le, Subgroup.mem_comap, hσz]
    exact Subgroup.mem_zpowers zQ
  let σbar : Q ⧸ N →* Q ⧸ N := QuotientGroup.map N N σ hNσ
  have hσbar : ∀ x : Q ⧸ N, σbar (σbar x) = x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show QuotientGroup.map N N σ hNσ (QuotientGroup.map N N σ hNσ (QuotientGroup.mk g)) =
      QuotientGroup.mk g
    rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hσσ]
  have hcardN : Nat.card N = 2 := by
    rw [hN, Nat.card_zpowers, orderOf_eq_prime hzQ2' hzQ1]
  have hcardQ := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hcardN] at hcardQ
  have heven : 2 ∣ Nat.card (Q ⧸ N) := by omega
  have hpar : 2 ∣ Nat.card {x : Q ⧸ N // σbar x = x} :=
    fixedPoints_card_even σbar hσbar heven
  let C : Subgroup (Q ⧸ N) :=
    { carrier := {x | σbar x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one σbar
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hCcard : Nat.card C = Nat.card {x : Q ⧸ N // σbar x = x} := rfl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hCcard]; exact hpar : 2 ∣ Nat.card C)
  have hxb1 : (x : Q ⧸ N) ≠ 1 := by
    intro h
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  have hxb2 : (x : Q ⧸ N) * (x : Q ⧸ N) = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one x)
    rw [hx, Subgroup.coe_pow, pow_two] at h
    exact h
  have hxfix : σbar (x : Q ⧸ N) = x := x.2
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x : Q ⧸ N)
  have hgN : g ∉ N := by
    intro hgN
    apply hxb1
    rw [← hg]
    exact (QuotientGroup.eq_one_iff g).mpr hgN
  have hggN : g * g ∈ N := by
    apply (QuotientGroup.eq_one_iff (g * g)).mp
    rw [QuotientGroup.mk_mul, hg]
    exact hxb2
  have hgg : (g : K) * g = z := by
    rw [hN] at hggN
    by_cases h1 : g * g = 1
    · exfalso
      have hK1 : (g : K) * (g : K) = 1 := congrArg Subtype.val h1
      rcases hQ.unique (g : K) g.2 hK1 with h | h
      · apply hgN
        rw [hN]
        have : g = 1 := Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _
      · apply hgN
        rw [hN]
        have : g = zQ := Subtype.ext (by rw [hzQK]; exact h)
        rw [this]
        exact Subgroup.mem_zpowers zQ
    · have h2 := FooteLit.eq_of_mem_zpowers_of_sq hzQ2' h1 hggN
      have h2K : (g : K) * (g : K) = z := by
        have := congrArg Subtype.val h2
        rw [hzQK] at this
        exact this
      exact h2K
  have hfix : σbar (QuotientGroup.mk g) = QuotientGroup.mk g := by
    rw [hg]
    exact hxfix
  have hmem : (σ g)⁻¹ * g ∈ N := by
    have h : QuotientGroup.mk (σ g : Q) = QuotientGroup.mk g := hfix
    exact QuotientGroup.eq.mp h
  rw [hN] at hmem
  by_cases h1 : (σ g)⁻¹ * g = 1
  · exfalso
    have hσg : σ g = g := by
      rw [inv_mul_eq_one] at h1
      exact h1
    apply hnf (g : K) g.2 hgg
    rw [← hσ, hσg]
  · have h2 := FooteLit.eq_of_mem_zpowers_of_sq hzQ2' h1 hmem
    have h2K : ((σ g : Q) : K)⁻¹ * (g : K) = z := by
      have := congrArg Subtype.val h2
      rw [hzQK] at this
      exact this
    have h3 : (g : K) = ((σ g : Q) : K) * z := by
      rw [← h2K]
      group
    have hsg : ((σ g : Q) : K) = (g : K) * z := by
      calc ((σ g : Q) : K) = ((σ g : Q) : K) * z * z := by rw [mul_assoc, hQ.sq, mul_one]
        _ = (g : K) * z := by rw [← h3]
    refine ⟨(g : K), g.2, hgg, ?_⟩
    rw [← hσ, hsg]

end Fixed

section Pair

variable {K : Type} [Group K]

theorem actsAsConj_mem {t u : K} {A : Subgroup K} {F : Type} [Field F]
    {e : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) F} {g : GL (Fin 2) F}
    (h : ActsAsConj t A e g) (hu : u ∈ A) : t * u * t⁻¹ ∈ A := by
  obtain ⟨y, hy, -⟩ := h ⟨u, hu⟩
  rw [← hy]
  exact y.2

theorem normalizes_of_sq_one {t : K} (ht : t * t = 1) {A : Subgroup K}
    (hA : ∀ u ∈ A, t * u * t⁻¹ ∈ A) : t ∈ normalizer (A : Set K) := by
  rw [mem_normalizer_iff]
  intro h
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  constructor
  · intro hh
    exact hA h hh
  · intro hh
    have h2 := hA _ hh
    have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
      rw [ht']
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht]; group
    rwa [e] at h2

theorem normalizes_of_comm {A B : Subgroup K} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ normalizer (B : Set K) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 := hc a ha h hh
    have e : a * h * a⁻¹ = h := by rw [h1]; group
    rw [e]
    exact hh
  · intro hh
    have hc' := hc a⁻¹ (A.inv_mem ha) (a * h * a⁻¹) hh
    have e : h = a * h * a⁻¹ := by
      calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
        _ = (a * h * a⁻¹) * a⁻¹ * a := by rw [hc']
        _ = a * h * a⁻¹ := by group
    rw [e]
    exact hh

theorem matrix_conj_of_formula {A : Subgroup K} {F : Type} [Field F]
    {e : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) F} {t f k : K} {g : GL (Fin 2) F}
    (hact : ActsAsConj t A e g) (hk : k ∈ A)
    (hfA : ∀ u ∈ A, f * u * f⁻¹ = k * (t * u * t⁻¹) * k⁻¹)
    {u : K} (hu : u ∈ A) {X : K} (hX : X ∈ A) (hXu : X = f * u * f⁻¹) :
    ((e ⟨X, hX⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F)) =
    (((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F)) *
      ((e ⟨u, hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨y, hy, hymat⟩ := hact ⟨u, hu⟩
  have hy' : (y : K) = t * u * t⁻¹ := hy
  have hXk : (⟨X, hX⟩ : ↥A) * ⟨k, hk⟩ = ⟨k, hk⟩ * y := by
    apply Subtype.ext
    show X * k = k * (y : K)
    rw [hy', hXu, hfA u hu]
    group
  have hM : ((e ⟨X, hX⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((e y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg e hXk
    rw [map_mul, map_mul] at h
    have h' := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 2) F =>
      (s : Matrix (Fin 2) (Fin 2) F)) h
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h'
  have hginv : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)
      = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc _ = (((e ⟨X, hX⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (g : Matrix (Fin 2) (Fin 2) F) := (Matrix.mul_assoc _ _ _).symm
    _ = (((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((e y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (g : Matrix (Fin 2) (Fin 2) F) := by rw [hM]
    _ = ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((e y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (g : Matrix (Fin 2) (Fin 2) F)) := Matrix.mul_assoc _ _ _
    _ = ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((((g : Matrix (Fin 2) (Fin 2) F)) * ((e ⟨u, hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (g : Matrix (Fin 2) (Fin 2) F)) := by rw [hymat]
    _ = ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((g : Matrix (Fin 2) (Fin 2) F) * ((e ⟨u, hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)) := by
          simp only [Matrix.mul_assoc, hginv, Matrix.mul_one]
    _ = (((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F)) * ((e ⟨u, hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := (Matrix.mul_assoc _ _ _).symm

theorem sign_contra {A : Subgroup K} {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    {e : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) F} {g : GL (Fin 2) F}
    (hg : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F))
    {t f k : K} (hact : ActsAsConj t A e g) (hk : k ∈ A)
    (hfA : ∀ u ∈ A, f * u * f⁻¹ = k * (t * u * t⁻¹) * k⁻¹) (hf2 : f * f = 1)
    {z r : K} (hzA : z ∈ A) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hrA : r ∈ A) (hrr : r * r = z)
    (hfr : f * r * f⁻¹ = r) : False := by
  have hfmem : ∀ u ∈ A, f * u * f⁻¹ ∈ A := fun u hu => by
    rw [hfA u hu]
    exact A.mul_mem (A.mul_mem hk (actsAsConj_mem hact hu)) (A.inv_mem hk)
  set H : Matrix (Fin 2) (Fin 2) F :=
    ((e ⟨k, hk⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) with hH
  have hA : ∀ u (hu : u ∈ A), ((e ⟨f * u * f⁻¹, hfmem u hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) * H = H * ((e ⟨u, hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) :=
    fun u hu => matrix_conj_of_formula hact hk hfA hu (hfmem u hu) rfl
  have hB : ∀ u (hu : u ∈ A), ((e ⟨u, hu⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) * H = H * ((e ⟨f * u * f⁻¹, hfmem u hu⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro u hu
    have hfu : f * (f * u * f⁻¹) * f⁻¹ = u := by
      calc f * (f * u * f⁻¹) * f⁻¹ = (f * f) * u * (f * f)⁻¹ := by group
        _ = u := by rw [hf2]; group
    exact matrix_conj_of_formula hact hk hfA (hfmem u hu) hu hfu.symm
  have hscal : ∃ c : F, H * H = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    apply matrix_eq_smul_one_of_commute_sl2
    intro A' hA'
    obtain ⟨u, hu⟩ := e.surjective ⟨A', hA'⟩
    have hYA : ((e u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A' := by
      rw [hu]
    have h1 := hA u.1 u.2
    have h2 := hB u.1 u.2
    have e1 : ((e ⟨u.1, u.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        A' := by
      rw [← hYA]
    rw [e1] at h1 h2
    have key : (H * H) * A' = A' * (H * H) := by
      calc (H * H) * A' = H * (H * A') := Matrix.mul_assoc _ _ _
        _ = H * (((e ⟨f * u.1 * f⁻¹, hfmem u.1 u.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) * H) := by rw [← h1]
        _ = (H * ((e ⟨f * u.1 * f⁻¹, hfmem u.1 u.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)) * H := (Matrix.mul_assoc _ _ _).symm
        _ = (A' * H) * H := by rw [← h2]
        _ = A' * (H * H) := Matrix.mul_assoc _ _ _
    exact key.symm
  set zA : A := ⟨z, hzA⟩ with hzA'
  set rA : A := ⟨r, hrA⟩ with hrA'
  have hzsq : zA * zA = 1 := Subtype.ext hz2
  have hz1A : zA ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hEz : ((e zA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((e zA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h1 : e zA * e zA = 1 := by rw [← map_mul, hzsq, map_one]
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using
      congrArg Subtype.val h1
  have hEz1 : ((e zA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h
    apply hz1A
    apply e.injective
    apply Subtype.ext
    rw [map_one]
    exact h
  have hA2 : ((e zA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 :=
    neg_one_of_sq_eq_one_sl2 h2 (e zA).2 hEz hEz1
  have haa : ((e rA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((e rA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have hrr' : rA * rA = zA := Subtype.ext hrr
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, hrr', hA2]
  have hdet : ((e rA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
    (e rA).2
  have hcomm : H * ((e rA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((e rA : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * H := by
    have h := hA r hrA
    have hfr' : (⟨f * r * f⁻¹, hfmem r hrA⟩ : A) = rA := Subtype.ext hfr
    rw [hfr'] at h
    exact h.symm
  obtain ⟨c, hc⟩ := hscal
  have hsq := isSquare_det_of_commute_of_sq_eq_neg_one h2 hdet haa ⟨c, hc⟩ hcomm
  have hdetH : H.det = ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
    rw [hH, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul,
      Matrix.GeneralLinearGroup.val_det_apply]
  exact hg (by rw [← hdetH]; exact hsq)

end Pair

section Join

variable {K : Type} [Group K] [Finite K]

theorem reflTransGen_commFourAdj_of_inv {z : K} {P Q₁ Q₂ : Subgroup K} (h : QuatPair z P Q₁ Q₂)
    (hinv : ∀ f ∈ P, Inv2 z f → ∃ y ∈ Q₁ ⊔ Q₂, Inv2 z y ∧ f * y = y * f) {F G : Subgroup K}
    (hF : IsKleinFour F) (hFP : F ≤ P) (hG : IsKleinFour G) (hGP : G ≤ P) :
    Relation.ReflTransGen (Sig.CommFourAdj K) F G := by
  obtain ⟨a₁, ha₁, ha₁z⟩ := h.q₁.exists_sq
  obtain ⟨a₂, ha₂, ha₂z⟩ := h.q₂.exists_sq
  have hx₀ : Inv2 z (a₁ * a₂) := h.inv2_mul ha₁ ha₂ ha₁z ha₂z
  have hx₀m : a₁ * a₂ ∈ Q₁ ⊔ Q₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)
  have key : ∀ F : Subgroup K, IsKleinFour F → F ≤ P →
      Relation.ReflTransGen (Sig.CommFourAdj K) F (vz z (a₁ * a₂)) := by
    intro F hF hFP
    obtain ⟨f, hfF, hfi, hadj⟩ := commFourAdj_vz_of_le h.q₁.sq h.q₁.ne_one h.zc hF hFP
    refine Relation.ReflTransGen.head hadj ?_
    obtain ⟨y, hy, hyi, hfy⟩ := hinv f (hFP hfF) hfi
    exact (Relation.ReflTransGen.single
      (commFourAdj_vz h.q₁.sq h.q₁.ne_one hfi hyi hfy)).trans
        (h.reflTransGen_vz hy hx₀m hyi hx₀)
  exact (key F hF hFP).trans (reflTransGen_commFourAdj_symm (key G hG hGP))

end Join

section Main

variable {K : Type} [Group K] [Finite K]

theorem sylowFourJoined_of_ch6Rem (P : Sylow 2 K) {z t : K} {K₁ K₂ : Subgroup K} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hz₁ : z ∈ K₁) (hz₂ : z ∈ K₂)
    (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz : orderOf z = 2)
    (hzP : z ∈ (P : Subgroup K)) (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x)
    (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂)) : SylowFourJoined K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hz]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have ht2 : t * t = 1 := hRem.sq
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card F₁ hodd₁
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card F₂ hodd₂
  have htK₁ : ∀ u ∈ K₁, t * u * t⁻¹ ∈ K₁ := fun u hu => actsAsConj_mem hact₁ hu
  have htK₂ : ∀ u ∈ K₂, t * u * t⁻¹ ∈ K₂ := fun u hu => actsAsConj_mem hact₂ hu
  have hPH : (P : Subgroup K) ≤ K₁ ⊔ K₂ ⊔ Subgroup.zpowers t := by
    intro g hg
    rw [hRem.gen]
    have hgC : g ∈ Subgroup.centralizer ({z} : Set K) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hzc g hg)
    obtain ⟨k, hk⟩ := (P.isPGroup' : IsPGroup 2 (P : Subgroup K)) ⟨g, hg⟩
    have hk' : g ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subtype.coe_mk] using h
    exact CFSG.GH74.GLS.IVK.Proofs2.Ivk94.mem_oPrimeResidualOf_of_pow hgC hk'
  have hHN : K₁ ⊔ K₂ ⊔ Subgroup.zpowers t ≤
      normalizer (K₁ : Set K) ⊓ normalizer (K₂ : Set K) := by
    refine sup_le (sup_le (le_inf Subgroup.le_normalizer ?_) (le_inf ?_ Subgroup.le_normalizer))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨normalizes_of_sq_one ht2 htK₁,
        normalizes_of_sq_one ht2 htK₂⟩))
    all_goals first
      | exact normalizes_of_comm (fun a ha b hb => hcomm a ha b hb)
      | exact normalizes_of_comm (fun a ha b hb => (hcomm b hb a ha).symm)
  have hEnorm : ∀ g ∈ K₁ ⊔ K₂ ⊔ Subgroup.zpowers t, ∀ n ∈ K₁ ⊔ K₂,
      g * n * g⁻¹ ∈ K₁ ⊔ K₂ := by
    intro g hg n hn
    obtain ⟨hg₁, hg₂⟩ := hHN hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hn
    have hga : g * a * g⁻¹ ∈ K₁ := (mem_normalizer_iff.1 hg₁ a).1 ha
    have hgb : g * b * g⁻¹ ∈ K₂ := (mem_normalizer_iff.1 hg₂ b).1 hb
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hga) (Subgroup.mem_sup_right hgb)
  have hnorm₁ : ∀ b ∈ K₁ ⊔ K₂, ∀ n ∈ K₁, b * n * b⁻¹ ∈ K₁ := by
    intro b hb n hn
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hb
    have h1 : a₂ * n = n * a₂ := (hcomm n hn a₂ ha₂).symm
    have e : a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₁ * n * a₁⁻¹ := by
      calc a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₁ * (a₂ * n) * a₂⁻¹ * a₁⁻¹ := by group
        _ = a₁ * (n * a₂) * a₂⁻¹ * a₁⁻¹ := by rw [h1]
        _ = a₁ * n * a₁⁻¹ := by group
    rw [e]
    exact K₁.mul_mem (K₁.mul_mem ha₁ hn) (K₁.inv_mem ha₁)
  have hnorm₂ : ∀ b ∈ K₁ ⊔ K₂, ∀ n ∈ K₂, b * n * b⁻¹ ∈ K₂ := by
    intro b hb n hn
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hb
    have hc : a₁ * (a₂ * n * a₂⁻¹) = (a₂ * n * a₂⁻¹) * a₁ :=
      hcomm a₁ ha₁ _ (K₂.mul_mem (K₂.mul_mem ha₂ hn) (K₂.inv_mem ha₂))
    have e : a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₂ * n * a₂⁻¹ := by
      calc a₁ * a₂ * n * (a₁ * a₂)⁻¹ = (a₁ * (a₂ * n * a₂⁻¹)) * a₁⁻¹ := by group
        _ = ((a₂ * n * a₂⁻¹) * a₁) * a₁⁻¹ := by rw [hc]
        _ = a₂ * n * a₂⁻¹ := by group
    rw [e]
    exact K₂.mul_mem (K₂.mul_mem ha₂ hn) (K₂.inv_mem ha₂)
  have hcardH : Nat.card ↥((P : Subgroup K) ⊓ (K₁ ⊔ K₂ ⊔ Subgroup.zpowers t)) =
      2 ^ (Nat.card ↥(K₁ ⊔ K₂ ⊔ Subgroup.zpowers t)).factorization 2 :=
    card_sylow_inf_of_le P hPH
  have hcardE : Nat.card ↥((P : Subgroup K) ⊓ (K₁ ⊔ K₂)) =
      2 ^ (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 :=
    card_inf_eq_of_normal le_sup_left hEnorm hcardH
  have hcardK₁ : Nat.card ↥((P : Subgroup K) ⊓ K₁) = 2 ^ (Nat.card ↥K₁).factorization 2 :=
    card_inf_eq_of_normal le_sup_left hnorm₁ hcardE
  have hcardK₂ : Nat.card ↥((P : Subgroup K) ⊓ K₂) = 2 ^ (Nat.card ↥K₂).factorization 2 :=
    card_inf_eq_of_normal le_sup_right hnorm₂ hcardE
  have hQ₁₂ : ((P : Subgroup K) ⊓ K₁) ⊓ ((P : Subgroup K) ⊓ K₂) = Subgroup.zpowers z := by
    apply le_antisymm
    · intro g hg
      have : g ∈ K₁ ⊓ K₂ := ⟨hg.1.2, hg.2.2⟩
      rw [hinter] at this
      exact this
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨hzP, hz₁⟩, ⟨hzP, hz₂⟩⟩
  have hcardQ₁₂ : Nat.card ↥(((P : Subgroup K) ⊓ K₁) ⊓ ((P : Subgroup K) ⊓ K₂)) = 2 := by
    rw [hQ₁₂, Nat.card_zpowers, hz]
  have hE_card : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card ↥K₁ * Nat.card ↥K₂ := by
    have := card_sup_mul_card_inf_of_comm K₁ K₂ hcomm
    rw [hinter, Nat.card_zpowers, hz] at this
    exact this
  have hQ_card : Nat.card ↥(((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂)) * 2 =
      Nat.card ↥((P : Subgroup K) ⊓ K₁) * Nat.card ↥((P : Subgroup K) ⊓ K₂) := by
    have := card_sup_mul_card_inf_of_comm ((P : Subgroup K) ⊓ K₁) ((P : Subgroup K) ⊓ K₂)
      (fun x hx y hy => hcomm x hx.2 y hy.2)
    rw [hcardQ₁₂] at this
    exact this
  have hfac : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 + 1 =
      (Nat.card ↥K₁).factorization 2 + (Nat.card ↥K₂).factorization 2 := by
    have h : (Nat.card ↥(K₁ ⊔ K₂) * 2).factorization 2 =
        (Nat.card ↥K₁ * Nat.card ↥K₂).factorization 2 := by rw [hE_card]
    rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h
    simpa [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] using h
  have hQcard : Nat.card ↥(((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂)) =
      Nat.card ↥((P : Subgroup K) ⊓ (K₁ ⊔ K₂)) := by
    have h2 : Nat.card ↥(((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂)) * 2 =
        2 ^ ((Nat.card ↥(K₁ ⊔ K₂)).factorization 2) * 2 := by
      rw [hQ_card, hcardK₁, hcardK₂, ← pow_add, ← hfac, pow_succ]
    rw [hcardE]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hRle : ((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂) ≤
      (P : Subgroup K) ⊓ (K₁ ⊔ K₂) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hR : ((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂) = (P : Subgroup K) ⊓ (K₁ ⊔ K₂) :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hQcard])
  have hsl₁ : HasSL2Model ↥K₁ (fun r => r = Nat.card F₁) :=
    ⟨F₁, inferInstance, inferInstance, rfl, ⟨e₁.trans (specialLinearGroupEquivStatedSL 2 F₁)⟩⟩
  have hsl₂ : HasSL2Model ↥K₂ (fun r => r = Nat.card F₂) :=
    ⟨F₂, inferInstance, inferInstance, rfl, ⟨e₂.trans (specialLinearGroupEquivStatedSL 2 F₂)⟩⟩
  have hQ₁ : QuatIn z ((P : Subgroup K) ⊓ K₁) :=
    quatIn_of_sylow_sl2 hodd₁ hsl₁ inf_le_right hcardK₁ ⟨hzP, hz₁⟩ hz2 hz1
  have hQ₂ : QuatIn z ((P : Subgroup K) ⊓ K₂) :=
    quatIn_of_sylow_sl2 hodd₂ hsl₂ inf_le_right hcardK₂ ⟨hzP, hz₂⟩ hz2 hz1
  have hpair : QuatPair z (P : Subgroup K) ((P : Subgroup K) ⊓ K₁) ((P : Subgroup K) ⊓ K₂) :=
    { zc := hzc
      le₁ := inf_le_left
      le₂ := inf_le_left
      comm := fun a ha b hb => hcomm a ha.2 b hb.2
      inter := fun g hg₁ hg₂ => by
        have : g ∈ K₁ ⊓ K₂ := ⟨hg₁.2, hg₂.2⟩
        rw [hinter] at this
        by_cases hg1 : g = 1
        · exact Or.inl hg1
        · exact Or.inr (FooteLit.eq_of_mem_zpowers_of_sq hz2' hg1 this)
      q₁ := hQ₁
      q₂ := hQ₂ }
  have htN : Subgroup.zpowers t ≤ normalizer ((K₁ ⊔ K₂ : Subgroup K) : Set K) :=
    Subgroup.zpowers_le.mpr (normalizes_of_sq_one ht2 (fun u hu =>
      hEnorm t (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) u hu))
  have hfix : ∀ f ∈ (P : Subgroup K), Inv2 z f →
      ∃ y ∈ ((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂), Inv2 z y ∧ f * y = y * f := by
    intro f hfP hfi
    have hfH := hPH hfP
    rw [sup_comm, ← SetLike.mem_coe,
      coe_mul_of_left_le_normalizer_right (Subgroup.zpowers t) (K₁ ⊔ K₂) htN] at hfH
    obtain ⟨a, ha, r, hr, hfar⟩ := hfH
    subst hfar
    by_cases ha1 : a = 1
    ·
      subst ha1
      have hrP : r ∈ (P : Subgroup K) ⊓ (K₁ ⊔ K₂) := by
        refine ⟨?_, hr⟩
        have h1 : (1 : K) * r ∈ (P : Subgroup K) := hfP
        rw [one_mul] at h1
        exact h1
      rw [← hR] at hrP
      exact ⟨r, hrP, by simpa using hfi, by simp⟩
    · have hat : a = t := FooteLit.eq_of_mem_zpowers_of_sq ht2' ha1 ha
      subst a
      have he : t * r * t⁻¹ ∈ K₁ ⊔ K₂ :=
        hEnorm t (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) r hr
      obtain ⟨ka, hka, kb, hkb, hkab⟩ := mem_sup_of_commute hcomm he
      have hf_eq : t * r = ka * kb * t := by
        rw [hkab]
        group
      have hfA₁ : ∀ u ∈ K₁, (t * r) * u * (t * r)⁻¹ = ka * (t * u * t⁻¹) * ka⁻¹ := by
        intro u hu
        have hy := htK₁ u hu
        have hcb : kb * (t * u * t⁻¹) * kb⁻¹ = t * u * t⁻¹ := by
          rw [← hcomm _ hy kb hkb]
          group
        rw [hf_eq]
        calc ka * kb * t * u * (ka * kb * t)⁻¹ = ka * (kb * (t * u * t⁻¹) * kb⁻¹) * ka⁻¹ := by
              group
          _ = ka * (t * u * t⁻¹) * ka⁻¹ := by rw [hcb]
      have hfA₂ : ∀ w ∈ K₂, (t * r) * w * (t * r)⁻¹ = kb * (t * w * t⁻¹) * kb⁻¹ := by
        intro w hw
        have hy := htK₂ w hw
        have hca : ka * (kb * (t * w * t⁻¹) * kb⁻¹) * ka⁻¹ = kb * (t * w * t⁻¹) * kb⁻¹ := by
          have hc := hcomm ka hka (kb * (t * w * t⁻¹) * kb⁻¹)
            (K₂.mul_mem (K₂.mul_mem hkb hy) (K₂.inv_mem hkb))
          rw [hc]
          group
        rw [hf_eq]
        calc ka * kb * t * w * (ka * kb * t)⁻¹ = ka * (kb * (t * w * t⁻¹) * kb⁻¹) * ka⁻¹ := by
              group
          _ = kb * (t * w * t⁻¹) * kb⁻¹ := hca
      have hf2 : (t * r) * (t * r) = 1 := hfi.sq
      have hfz : (t * r) * z * (t * r)⁻¹ = z := by
        rw [hzc (t * r) hfP]
        group
      have hfQ₁ : ∀ g ∈ (P : Subgroup K) ⊓ K₁,
          (t * r) * g * (t * r)⁻¹ ∈ (P : Subgroup K) ⊓ K₁ := by
        intro g hg
        refine ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem hfP hg.1)
          ((P : Subgroup K).inv_mem hfP), ?_⟩
        rw [hfA₁ g hg.2]
        exact K₁.mul_mem (K₁.mul_mem hka (htK₁ g hg.2)) (K₁.inv_mem hka)
      have hfQ₂ : ∀ g ∈ (P : Subgroup K) ⊓ K₂,
          (t * r) * g * (t * r)⁻¹ ∈ (P : Subgroup K) ⊓ K₂ := by
        intro g hg
        refine ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem hfP hg.1)
          ((P : Subgroup K).inv_mem hfP), ?_⟩
        rw [hfA₂ g hg.2]
        exact K₂.mul_mem (K₂.mul_mem hkb (htK₂ g hg.2)) (K₂.inv_mem hkb)
      have hnf₁ : ∀ r' ∈ (P : Subgroup K) ⊓ K₁, r' * r' = z →
          (t * r) * r' * (t * r)⁻¹ ≠ r' := fun r' hr' hrr hfr' =>
        sign_contra h2₁ hns₁ hact₁ hka hfA₁ hf2 hz₁ hz2 hz1 hr'.2 hrr hfr'
      have hnf₂ : ∀ r' ∈ (P : Subgroup K) ⊓ K₂, r' * r' = z →
          (t * r) * r' * (t * r)⁻¹ ≠ r' := fun r' hr' hrr hfr' =>
        sign_contra h2₂ hns₂ hact₂ hkb hfA₂ hf2 hz₂ hz2 hz1 hr'.2 hrr hfr'
      obtain ⟨r₁, hr₁, hr₁sq, hfr₁⟩ :=
        exists_fixed_pair hQ₁ (four_dvd_card_of_quatIn hQ₁) hf2 hfz hfQ₁ hnf₁
      obtain ⟨r₂, hr₂, hr₂sq, hfr₂⟩ :=
        exists_fixed_pair hQ₂ (four_dvd_card_of_quatIn hQ₂) hf2 hfz hfQ₂ hnf₂
      have c12 : r₁ * r₂ = r₂ * r₁ := hcomm r₁ hr₁.2 r₂ hr₂.2
      have zr₁ : r₁ * z = z * r₁ := hcomm r₁ hr₁.2 z hz₂
      have zr₂ : z * r₂ = r₂ * z := hcomm z hz₁ r₂ hr₂.2
      have hy1 : r₁ * r₂ ∈ ((P : Subgroup K) ⊓ K₁) ⊔ ((P : Subgroup K) ⊓ K₂) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hr₁) (Subgroup.mem_sup_right hr₂)
      have hsq : (r₁ * r₂) * (r₁ * r₂) = 1 := by
        calc (r₁ * r₂) * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
          _ = r₁ * (r₁ * r₂) * r₂ := by rw [← c12]
          _ = (r₁ * r₁) * (r₂ * r₂) := by group
          _ = 1 := by rw [hr₁sq, hr₂sq, hz2]
      have hne1 : r₁ * r₂ ≠ 1 := by
        intro h
        have he' : r₁ = r₂⁻¹ := eq_inv_of_mul_eq_one_left h
        have hr₁' : r₁ ∈ (P : Subgroup K) ⊓ K₂ := by
          rw [he']
          exact Subgroup.inv_mem _ hr₂
        exact hpair.not_sq_mem hr₁ hr₁' hr₁sq
      have hnez : r₁ * r₂ ≠ z := by
        intro h
        have he' : r₁ = z * r₂⁻¹ := eq_mul_inv_of_mul_eq h
        have hr₁' : r₁ ∈ (P : Subgroup K) ⊓ K₂ := by
          rw [he']
          exact ⟨(P : Subgroup K).mul_mem hzP ((P : Subgroup K).inv_mem hr₂.1),
            K₂.mul_mem hz₂ (K₂.inv_mem hr₂.2)⟩
        exact hpair.not_sq_mem hr₁ hr₁' hr₁sq
      have hzy : (r₁ * r₂) * z = z * (r₁ * r₂) := by
        calc (r₁ * r₂) * z = r₁ * (r₂ * z) := by group
          _ = r₁ * (z * r₂) := by rw [← zr₂]
          _ = (r₁ * z) * r₂ := by group
          _ = (z * r₁) * r₂ := by rw [zr₁]
          _ = z * (r₁ * r₂) := by group
      have hfy : (t * r) * (r₁ * r₂) * (t * r)⁻¹ = r₁ * r₂ := by
        calc (t * r) * (r₁ * r₂) * (t * r)⁻¹
            = ((t * r) * r₁ * (t * r)⁻¹) * ((t * r) * r₂ * (t * r)⁻¹) := by group
          _ = (r₁ * z) * (r₂ * z) := by rw [hfr₁, hfr₂]
          _ = r₁ * (z * r₂) * z := by group
          _ = r₁ * (r₂ * z) * z := by rw [zr₂]
          _ = r₁ * r₂ * (z * z) := by group
          _ = r₁ * r₂ := by rw [hz2, mul_one]
      refine ⟨r₁ * r₂, hy1, ⟨hsq, hne1, hnez, hzy⟩, ?_⟩
      calc (t * r) * (r₁ * r₂) = ((t * r) * (r₁ * r₂) * (t * r)⁻¹) * (t * r) := by group
        _ = (r₁ * r₂) * (t * r) := by rw [hfy]
  refine sylowFourJoined_of_sylow P fun F G hF hFP hG hGP => ?_
  exact reflTransGen_commFourAdj_of_inv hpair hfix hF hFP hG hGP

end Main

section Leaf

theorem exists_sylow_central_involution (X : Type) [Group X] [Finite X] (h2 : 2 ∣ Nat.card X) :
    ∃ (P : Sylow 2 X) (z : X), z ∈ (P : Subgroup X) ∧ (∀ x ∈ (P : Subgroup X), x * z = z * x) ∧
      orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hfac : 0 < (Nat.card X).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  have hPcard := Sylow.card_eq_multiplicity P
  have hnt : Nontrivial (P : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPcard]
    have h2le : 2 ≤ 2 ^ (Nat.card X).factorization 2 := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.card X).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
    exact lt_of_lt_of_le (by norm_num) h2le
  obtain ⟨c, hcZ, hc1⟩ : ∃ c ∈ Subgroup.center (P : Subgroup X), c ≠ 1 := by
    obtain ⟨c, hc, hcn⟩ := SetLike.exists_of_lt (IsPGroup.bot_lt_center (P.isPGroup'))
    exact ⟨c, hc, fun h => hcn (by rw [Subgroup.mem_bot]; exact h)⟩
  have hdvd : 2 ∣ orderOf c := IsPGroup.dvd_orderOf (P.isPGroup') hc1
  have hZdvd : 2 ∣ Nat.card (Subgroup.center (P : Subgroup X)) := by
    have h1 : orderOf (⟨c, hcZ⟩ : Subgroup.center (P : Subgroup X)) = orderOf c :=
      (Subgroup.orderOf_coe ⟨c, hcZ⟩).symm
    have h2 := orderOf_dvd_natCard (⟨c, hcZ⟩ : Subgroup.center (P : Subgroup X))
    rw [h1] at h2
    exact dvd_trans hdvd h2
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hZdvd
  refine ⟨P, ((w : (P : Subgroup X)) : X), (w : (P : Subgroup X)).2, ?_, ?_⟩
  · intro x hx
    have := Subgroup.mem_center_iff.1 w.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  · exact (Subgroup.orderOf_coe w.1).trans ((Subgroup.orderOf_coe w).trans hw)

theorem two_dvd_card_of_three_le_twoRank (X : Type) [Group X] [Finite X]
    (h : 3 ≤ Open.twoRank X) : 2 ∣ Nat.card X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ : ∃ S : Set ℕ,
      S = {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := ⟨_, rfl⟩
  have h' : 3 ≤ sSup S := by
    rw [hS]
    exact h
  have hne : S.Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    rw [hem] at h'
    simp at h'
  have hbdd : BddAbove S := by
    refine ⟨Nat.card X, ?_⟩
    rintro k hk
    rw [hS] at hk
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
    have h2 : k < 2 ^ k := k.lt_two_pow_self
    omega
  obtain ⟨E, -, hEab, hE⟩ : ∃ E : Subgroup X, E ≤ ⊤ ∧ Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ sSup S := by
    have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
    rw [hS] at hmem ⊢
    exact hmem
  have h8 : 8 ≤ 2 ^ sSup S := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ sSup S := Nat.pow_le_pow_right (by norm_num) h'
  have hE8 : 1 < Nat.card E := by
    rw [hE]
    exact lt_of_lt_of_le (by norm_num) h8
  haveI : Nontrivial E := (Finite.one_lt_card_iff_nontrivial).mp hE8
  obtain ⟨x, hx1⟩ := exists_ne (1 : E)
  have hx2 : (x : X) ^ 2 = 1 :=
    (show IsMulCommutative E ∧ ∀ y ∈ E, y ^ 2 = 1 from hEab).2 x.1 x.2
  have hx1' : (x : X) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hord : orderOf (x : X) = 2 := orderOf_eq_prime hx2 hx1'
  have hdiv := orderOf_dvd_natCard (x : X)
  rw [hord] at hdiv
  exact hdiv

end Leaf

theorem leafD4_holds :
    LeafD4 := by
  intro X _ _ _ hr p f hp hp2 hf hM
  have : Fact p.Prime := ⟨hp⟩
  have h2 : 2 ∣ Nat.card X := two_dvd_card_of_three_le_twoRank X hr
  obtain ⟨P, z, hzP, hzc, hzo⟩ := exists_sylow_central_involution X h2
  obtain ⟨K₁, K₂, F₁, F₂, _, _, _, _, t, h₁, h₂, hcomm, hz₁, hz₂, hinter, hRem⟩ :=
    ivk_D4_ch6Rem_odd hp2 hM z hzo
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact sylowFourJoined_of_ch6Rem P hRem hcomm hz₁ hz₂ hinter hzo hzP hzc
    (by rw [h₁]; exact hodd.pow) (by rw [h₂]; exact hodd)

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
