module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Amb
import CFSG.GroupTheory.PLayer.CentralQuotient
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Cent

variable {Ω : Type} [Group Ω]

theorem commute_of_mem_centModSubgroup {p : ℕ} {S : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥)
    {g : Ω} (hg : g ∈ centModSubgroup p S) {s : Ω} (hs : s ∈ S) : s * g = g * s := by
  have h1 := hg.2 s hs
  have hcore : GLAPPrimeCoreOf p S = ⊥ := by
    change (GLAPPrimeCore p ↥S).map S.subtype = ⊥
    rw [hSp, Subgroup.map_bot]
  rw [hcore, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem le_centralizer_of_commute {p : ℕ} (hp : p.Prime) {S B D : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hCD : B ⊓ centModSubgroup p S ≤ D)
    (hrel : (B ⊓ centModSubgroup p S).relIndex D = p) {b : Ω} (hbD : b ∈ D)
    (hbC : b ∉ B ⊓ centModSubgroup p S) {s : Ω} (hs : s ∈ S) (hsb : s * b = b * s) :
    D ≤ Subgroup.centralizer ({s} : Set Ω) := by
  set C := B ⊓ centModSubgroup p S with hC
  set M : Subgroup Ω := (Subgroup.zpowers b ⊔ C) ⊓ D with hM
  have hCM : C ≤ M := le_inf le_sup_right hCD
  have hMD : M ≤ D := inf_le_right
  have hbM : b ∈ M := ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers b), hbD⟩
  have htower := Subgroup.relIndex_mul_relIndex C M D hCM hMD
  have hCM1 : C.relIndex M ≠ 1 := fun h1 => hbC (Subgroup.relIndex_eq_one.1 h1 hbM)
  have hMD1 : M.relIndex D = 1 := by
    rw [hrel] at htower
    rcases (Nat.dvd_prime hp).1 (Dvd.intro _ htower) with h | h
    · exact absurd h hCM1
    · rw [h] at htower
      exact Nat.mul_left_cancel hp.pos (by rw [mul_one]; exact htower)
  have hDM : D ≤ M := Subgroup.relIndex_eq_one.1 hMD1
  have hsup : Subgroup.zpowers b ⊔ C ≤ Subgroup.centralizer ({s} : Set Ω) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hsb.symm
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_centModSubgroup hSp hg.2 hs).symm
  exact hDM.trans (inf_le_left.trans hsup)

end Cent

section Transfer

variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] noncomputable def transAut {S : Subgroup Ω} [S.Normal] {G : Type} [Group G]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* G) (b : Ω) : MulAut G :=
  (e.symm.trans (actQuot S b)).trans e

theorem fixSubgroup_transAut {S : Subgroup Ω} [S.Normal] {G : Type} [Group G]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* G) (b : Ω) :
    fixSubgroup (transAut e b) = (fixSubgroup (actQuot S b)).map e.toMonoidHom := by
  ext g
  rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSubgroup]
  change e (actQuot S b (e.symm g)) = g ↔ _
  constructor
  · intro h
    have := congrArg e.symm h
    rwa [MulEquiv.symm_apply_apply] at this
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

@[expose] noncomputable def transAutHom {S : Subgroup Ω} [S.Normal] {G : Type} [Group G]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* G) : Ω →* MulAut G where
  toFun := transAut e
  map_one' := MulEquiv.ext fun g => by
    change e (actQuot S 1 (e.symm g)) = g
    rw [map_one, MulAut.one_apply, MulEquiv.apply_symm_apply]
  map_mul' x y := MulEquiv.ext fun g => by
    change e (actQuot S (x * y) (e.symm g)) = e (actQuot S x (e.symm (e (actQuot S y (e.symm g)))))
    rw [map_mul, MulAut.mul_apply, MulEquiv.symm_apply_apply]

theorem transAut_pow_eq_one {S : Subgroup Ω} [S.Normal] {G : Type} [Group G]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* G) {b : Ω} {p : ℕ} (hb : b ^ p = 1) : transAut e b ^ p = 1 := by
  have h := map_pow (transAutHom e) b p
  rw [hb, map_one] at h
  exact h.symm

theorem commutator_eq_bot_of_le_center {K : Type*} [Group K] {T J : Subgroup K}
    (hJ : ⁅J, J⁆ = J) (hTJ : ⁅T, J⁆ ≤ Subgroup.center K) : ⁅T, J⁆ = ⊥ := by
  have hZ : ∀ H : Subgroup K, H ≤ Subgroup.center K → ∀ L : Subgroup K, ⁅H, L⁆ = ⊥ := by
    intro H hH L
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro l _
    exact Subgroup.mem_center_iff.1 (hH hh) l
  have h1 : ⁅⁅T, J⁆, J⁆ = ⊥ := hZ _ hTJ J
  have h2 : ⁅⁅J, T⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm J T]; exact h1
  have h3 : ⁅⁅J, J⁆, T⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hJ] at h3
  rw [Subgroup.commutator_comm]
  exact h3

theorem s2019Omega_of_fixCentralizes {p : ℕ} (hp : p.Prime) {S B D J : Subgroup Ω}
    [hSn : S.Normal] (hSp : GLAPPrimeCore p ↥S = ⊥) {G : Type} [Group G]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* G)
    (hfix : ∀ b ∈ D, b ∈ B → b ∉ centModSubgroup p S → S2019FixCentralizes p (transAut e b)) :
    S2019Omega p S B D J := by
  classical
  intro _ hDB hCD hrel _ hJ _ _ T hTS hT2 hJT
  obtain ⟨b, hbD, hbC⟩ : ∃ b ∈ D, b ∉ B ⊓ centModSubgroup p S := by
    by_contra hcon
    push Not at hcon
    have h1 : (B ⊓ centModSubgroup p S).relIndex D = 1 := Subgroup.relIndex_eq_one.2 hcon
    rw [hrel] at h1
    exact hp.one_lt.ne' h1
  have hbB : b ∈ B := hDB hbD
  have hbC' : b ∉ centModSubgroup p S := fun h => hbC ⟨hbB, h⟩
  have hXeq : S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbD))
    · intro s hs'
      obtain ⟨hs, hsb⟩ := Subgroup.mem_inf.1 hs'
      refine Subgroup.mem_inf.2 ⟨hs, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hsb
      have hDs := le_centralizer_of_commute hp hSp hCD hrel hbD hbC hs hsb
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.1 (hDs hd)
  rw [hXeq] at hJ
  set α : MulAut ↥S := MulAut.conjNormal b with hα
  have hfixα : (fixSubgroup α).map S.subtype = S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.2 ⟨s.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ((α s : ↥S) : Ω) = s := congrArg Subtype.val hs
      rw [hα, MulAut.conjNormal_apply] at h1
      calc (s : Ω) * b = b * s * b⁻¹ * b := by rw [h1]
        _ = b * s := by group
    · intro hx
      obtain ⟨hxS, hxb⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩, ?_, rfl⟩
      rw [mem_fixSubgroup]
      apply Subtype.ext
      rw [hα, MulAut.conjNormal_apply]
      rw [Subgroup.mem_centralizer_singleton_iff] at hxb
      calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [hxb]
        _ = x := by group
  have hsub : ∀ y ∈ fixSubgroup α ⊓ S.subtype.ker, ∀ x ∈ fixSubgroup α, x * y = y * x := by
    intro y hy x _
    have hy' := (Subgroup.mem_inf.1 hy).2
    rw [Subgroup.ker_subtype, Subgroup.mem_bot] at hy'
    rw [hy', mul_one, one_mul]
  rw [← hfixα] at hJ
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp S.subtype
    hsub).2 J hJ
  set T₀ : Subgroup ↥S := T.subgroupOf S with hT₀
  have hT₀T : T₀.map S.subtype = T := by
    rw [hT₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hTS]
  have hJ₀N : J₀ ≤ Subgroup.normalizer (T₀ : Set ↥S) := by
    intro j hj
    have hjJ : (j : Ω) ∈ J := by
      rw [← hJ₀J]
      exact Subgroup.mem_map_of_mem _ hj
    have hjN := hJT hjJ
    rw [Subgroup.mem_normalizer_iff] at hjN ⊢
    intro t
    rw [hT₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hjN (t : Ω)
  set ψ : ↥S →* ↥S ⧸ Subgroup.center ↥S := QuotientGroup.mk' (Subgroup.center ↥S) with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hψk : ψ.ker ≤ Subgroup.center ↥S := (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ k, ψ (α k) = actQuot S b (ψ k) := fun k => (actQuot_mk S b k).symm
  have hJ₁ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup ψ hψk α
    (actQuot S b) hαβ hψs hp hJ₀
  have hsubG : ∀ y ∈ fixSubgroup (actQuot S b) ⊓ e.toMonoidHom.ker,
      ∀ x ∈ fixSubgroup (actQuot S b), x * y = y * x := by
    intro y hy x _
    have hy1 : y = 1 := e.injective (by rw [map_one]; exact (Subgroup.mem_inf.1 hy).2)
    rw [hy1, mul_one, one_mul]
  haveI : Finite G := Finite.of_equiv _ e.toEquiv
  have hJ₂ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.toMonoidHom hsubG).1 _ hJ₁
  rw [← fixSubgroup_transAut] at hJ₂
  have hT₂ : IsPGroup 2 ((T₀.map ψ).map e.toMonoidHom) := by
    have hT₀2 : IsPGroup 2 T₀ := fun t => by
      have htT : ((t : ↥S) : Ω) ∈ T := Subgroup.mem_subgroupOf.1 t.2
      obtain ⟨k, hk⟩ := hT2 ⟨((t : ↥S) : Ω), htT⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    exact (hT₀2.map ψ).map e.toMonoidHom
  have hN₂ : (J₀.map ψ).map e.toMonoidHom ≤
      Subgroup.normalizer (((T₀.map ψ).map e.toMonoidHom : Subgroup G) : Set G) := by
    refine (Subgroup.map_mono (Subgroup.map_mono hJ₀N |>.trans (Subgroup.le_normalizer_map ψ))).trans
      (Subgroup.le_normalizer_map _)
  have hcomm := hfix b hbD hbB hbC' _ hJ₂ _ hT₂ hN₂
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff_of_injective _ e.injective, Subgroup.map_eq_bot_iff] at hcomm
  have hTJ₀ : ⁅T₀, J₀⁆ ≤ Subgroup.center ↥S := hcomm.trans hψk
  have hJ₀perf : ⁅J₀, J₀⁆ = J₀ := glaPComponent_perfect hJ₀
  have h0 := commutator_eq_bot_of_le_center hJ₀perf hTJ₀
  rw [← hT₀T, ← hJ₀J, ← Subgroup.map_commutator, h0, Subgroup.map_bot]

@[expose] noncomputable def pSimpleEquivQuotCenter {p : ℕ} {S : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) : PSimple p S ≃* (↥S ⧸ Subgroup.center ↥S) :=
  let eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)

end Transfer

theorem s2019FactClassical_of_on (h : ∀ F, S2019FactClassicalOn F) : S2019FactClassical := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  obtain ⟨i, hi, he⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hcl, hA1⟩ := hi
  obtain ⟨F, hF⟩ : ∃ F, s2019Family d = some F := by
    cases d <;> first | exact ⟨_, rfl⟩ | exact absurd hcl id
  exact h F p q hp hp2 hq hq2 hqp Ω S B D J hSn hSq hSp
    ⟨.lie ⟨d, hv⟩, ⟨hchar, hF, hA1⟩, he⟩ hBel hSB hrank

theorem eq_three_or_five_le {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : q = 3 ∨ 5 ≤ q := by
  have h2 := hq.two_le
  have h4 : q ≠ 4 := by
    rintro rfl
    exact absurd hq (by norm_num)
  omega

theorem s2019FactClassicalOn_linear (hI5 : S2019LinInner (5 ≤ ·)) (hI3 : S2019LinInner (· = 3))
    (hO : S2019LinOuter) : S2019FactClassicalOn .linear := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hfam, hA1⟩ := hi
  obtain ⟨m, Q, rfl⟩ : ∃ m Q, d = .A m Q := by
    cases d <;> first | exact ⟨_, _, rfl⟩ | simp [s2019Family] at hfam
  have hQq : Q.p = q := by simpa using hchar
  subst hQq
  have hm : 2 ≤ m := by
    have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
    obtain ⟨⟨h1, -⟩, -⟩ := hv'
    have h2 : m ≠ 1 := by
      rintro rfl
      exact hA1 trivial
    omega
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI := hSn
  set F := GaloisField Q.p Q.exponent
  let e : ↥S ⧸ Subgroup.center ↥S ≃* LinearFlag.projectiveSL (m + 1) F :=
    (pSimpleEquivQuotCenter hSp).symm.trans (e₀.trans
      ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) F)))
  refine s2019Omega_of_fixCentralizes hp hSp e fun b _ hbB _ => ?_
  have hβp : transAut e b ^ p = 1 := transAut_pow_eq_one e (hBel.2 b hbB)
  by_cases hinn : ∃ A : GL (Fin (m + 1)) F, transAut e b = LinearFlag.conjAut (m + 1) F A
  · obtain ⟨A, hA⟩ := hinn
    have h1 : LinearFlag.conjAut (m + 1) F (A ^ p) * LinearFlag.fieldAut (m + 1) F 1 = 1 := by
      rw [map_one, mul_one, map_pow, ← hA, hβp]
    obtain ⟨-, c, hc⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by omega) (A ^ p) 1 h1
    rw [hA]
    rcases eq_three_or_five_le hq hq2 with h3 | h5
    · exact hI3 p Q.p hp hp2 hq hq2 hqp h3 F (m + 1) A c hc.symm
    · exact hI5 p Q.p hp hp2 hq hq2 hqp h5 F (m + 1) A c hc.symm
  · push Not at hinn
    exact hO p Q.p hp hp2 hq hq2 hqp F (m + 1) (by omega) _ hβp hinn

theorem s2019FactClassicalOn_unitary (hI5 : S2019UniInner (5 ≤ ·)) (hI3 : S2019UniInner (· = 3))
    (hO : S2019UniOuter) : S2019FactClassicalOn .unitary := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hfam, -⟩ := hi
  obtain ⟨m, Q, rfl⟩ : ∃ m Q, d = .twistedA m Q := by
    cases d <;> first | exact ⟨_, _, rfl⟩ | simp [s2019Family] at hfam
  have hQq : Q.p = q := by simpa using hchar
  subst hQq
  have hm : 2 ≤ m := by
    have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
    obtain ⟨⟨h1, -⟩, -⟩ := hv'
    exact h1
  haveI := hSn
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv e₀
  have h : UnitaryFieldData Q.p Q.exponent K :=
    ⟨Q.prime_p, Q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨e₂⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (K := K) (n := m + 1))
  let e : ↥S ⧸ Subgroup.center ↥S ≃* primeFormP h (idGram K (m + 1)) :=
    (pSimpleEquivQuotCenter hSp).symm.trans (e₁.trans
      ((CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm.trans e₂.symm))
  refine s2019Omega_of_fixCentralizes hp hSp e fun b _ hbB _ => ?_
  have hβp : transAut e b ^ p = 1 := transAut_pow_eq_one e (hBel.2 b hbB)
  by_cases hinn : ∃ A : primeFormUnitary h (idGram K (m + 1)),
      transAut e b = primeFormConjHom h (idGram K (m + 1)) A
  · obtain ⟨A, hA⟩ := hinn
    have hC : IsPrimeFormGram (1 : GL (Fin (m + 1)) K) := isPrimeFormGram_idGram
    obtain ⟨-, -, hker, -⟩ := unitary_prime_form_full_semilinear_realization h hC (by omega)
      (fun hh => by
        have h3 : Q.p ∣ Q.p ^ Q.exponent := dvd_pow_self _ Q.exponent_pos.ne'
        rw [hh.2] at h3
        exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h3))
    have hPsi : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, map_pow, ← hA, hβp]
    obtain ⟨-, c, -, hc⟩ := (hker ⟨A ^ p, 1⟩).1 hPsi
    have hc' : (A : GL (Fin (m + 1)) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
      rw [← hc, Subgroup.coe_pow]
    rw [hA]
    rcases eq_three_or_five_le hq hq2 with h3 | h5
    · exact hI3 p Q.p hp hp2 hq hq2 hqp h3 Q.exponent K h (m + 1) A c hc'
    · exact hI5 p Q.p hp hp2 hq hq2 hqp h5 Q.exponent K h (m + 1) A c hc'
  · push Not at hinn
    exact hO p Q.p hp hp2 hq hq2 hqp Q.exponent K h (m + 1) (by omega) _ hβp hinn

end CFSG.LocalAnalysis.GLTheoremA.S2019
