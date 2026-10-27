module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma34
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace L62

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem le_of_subnormal_comm_eq {K H J S : Subgroup G} (hKH : IsSubnormal K H) (hJK : J ≤ K)
    (hSH : S ≤ H) (hS : S ≤ ⁅S, J⁆) : S ≤ K := by
  induction hKH generalizing J S with
  | refl H => exact hSH
  | @step K M H hKM hKMn hMH ih =>
    have hSM : S ≤ M := ih (hJK.trans hKM) hSH hS
    refine hS.trans ?_
    rw [Subgroup.commutator_le]
    intro s hs j hj
    have hsM : s ∈ M := hSM hs
    have hjK : j ∈ K := hJK hj
    have hn := hKMn.conj_mem ⟨j, hKM hjK⟩ (by simpa [Subgroup.mem_subgroupOf] using hjK) ⟨s, hsM⟩
    have h1 : s * j * s⁻¹ ∈ K := by simpa [Subgroup.mem_subgroupOf] using hn
    rw [commutatorElement_def]
    exact K.mul_mem h1 (K.inv_mem hjK)

theorem le_normalizer_closureIn (I H : Subgroup G) :
    H ≤ Subgroup.normalizer (closureIn I H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_gLBConj_eq, closureIn_eq_iSup_gLBConj I H]
  have hsup : GLBConj h (⨆ g ∈ H, GLBConj g I) = ⨆ g ∈ H, GLBConj h (GLBConj g I) := by
    unfold GLBConj
    simp only [Subgroup.map_iSup]
  rw [hsup]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_biSup (fun g => GLBConj g I) (H.mul_mem hg hh)
  · refine iSup₂_le fun g hg => ?_
    have e : GLBConj g I = GLBConj h (GLBConj (g * h⁻¹) I) := by
      rw [gLBConj_gLBConj, inv_mul_cancel_right]
    rw [e]
    exact le_biSup (fun g' => GLBConj h (GLBConj g' I)) (H.mul_mem hg (H.inv_mem hh))

theorem le_normalizer_glaPLayer (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  have key : ∀ g ∈ X, GLBConj g (GLAPLayer p X) ≤ GLAPLayer p X := by
    intro g hg
    have hX : GLBConj g X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 := glaPComponent_gLBConj hL g
    rw [hX] at h1
    exact le_sSup h1
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key g hg) ?_
  have h2 := gLBConj_mono (g := g) (key g⁻¹ (X.inv_mem hg))
  rwa [gLBConj_gLBConj_inv] at h2

theorem exists_family_gen (hp : p.Prime) (hI : Input18_3_4) {X D J : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hDX : D ≤ X) (hDel : IsElemAbelian p D)
    (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer (D : Set G)) J) :
    ∃ 𝒞 : Set (Subgroup G), (∀ C ∈ 𝒞, GLAPComponent p X C) ∧
      (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer p X, GLBConj g J ∧ (∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞) ∧
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C') ∧
      J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J ∧ 𝒞.Nonempty := by
  obtain ⟨𝒞, hcomp, hsup, hcl, htr⟩ := hI G X hX p hp D hDX hDel J hJ
  have hJle : J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J := by
    have h : GLBConj (1 : G) J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J :=
      le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl
    rwa [gLBConj_one] at h
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  have hne : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hJne
    rw [← le_bot_iff]
    calc J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J := hJle
      _ = ⨆ L ∈ 𝒞, L := hsup.symm
      _ = ⊥ := by rw [h]; simp
  exact ⟨𝒞, hcomp, hsup, hcl, htr, hJle, hne⟩

theorem exists_family (hp : p.Prime) (hI : Input18_3_4) {A D J : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G))) (hAD : A ≤ D)
    (hDel : IsElemAbelian p D) (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) :
    ∃ 𝒞 : Set (Subgroup G),
      (∀ C ∈ 𝒞, GLAPComponent p (Subgroup.centralizer (A : Set G)) C) ∧
      (⨆ C ∈ 𝒞, C) = layerClosure p A J ∧ (∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞) ∧
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C') ∧ J ≤ layerClosure p A J ∧ 𝒞.Nonempty := by
  have hDX : D ≤ Subgroup.centralizer (A : Set G) := fun d hd => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hDel (hAD he) hd
  have hJ' : GLAPComponent p (Subgroup.centralizer (A : Set G) ⊓
      Subgroup.centralizer (D : Set G)) J := by
    have : Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer (D : Set G) :=
      inf_eq_right.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAD))
    rw [this]
    exact hJ
  exact exists_family_gen hp hI hX hDX hDel hJ'

theorem layerClosure_isSubnormal (hp : p.Prime) {A J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p (Subgroup.centralizer (A : Set G)) C)
    (hsup : (⨆ C ∈ 𝒞, C) = layerClosure p A J) :
    IsSubnormal (layerClosure p A J) (Subgroup.centralizer (A : Set G)) := by
  set X := Subgroup.centralizer (A : Set G) with hXdef
  have hKL : layerClosure p A J ≤ GLAPLayer p X := by
    rw [← hsup]
    exact iSup₂_le fun C hC => le_sSup (hcomp C hC)
  have hLX : GLAPLayer p X ≤ X := i183_glaPLayer_le p X
  have hKeq : layerClosure p A J = closureIn J (GLAPLayer p X) :=
    (closureIn_eq_iSup_gLBConj J (GLAPLayer p X)).symm
  have hKn : GLAPLayer p X ≤ Subgroup.normalizer (layerClosure p A J : Set G) := by
    rw [hKeq]
    exact le_normalizer_closureIn J (GLAPLayer p X)
  have h1 : ((layerClosure p A J).subgroupOf (GLAPLayer p X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hKn
  have h2 : ((GLAPLayer p X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 (le_normalizer_glaPLayer p X)
  exact IsSubnormal.step hKL h1 (IsSubnormal.step hLX h2 (IsSubnormal.refl X))

theorem layerClosure_facts (hp : p.Prime) (hI : Input18_3_4) {A D J : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G))) (hAD : A ≤ D)
    (hDel : IsElemAbelian p D) (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) :
    layerClosure p A J ≤ GLAPLayer p (Subgroup.centralizer (A : Set G)) ∧
      IsSubnormal (layerClosure p A J) (Subgroup.centralizer (A : Set G)) ∧ J ≤ layerClosure p A J := by
  obtain ⟨𝒞, hcomp, hsup, -, -, hJK, -⟩ := exists_family hp hI hX hAD hDel hJ
  refine ⟨?_, layerClosure_isSubnormal hp hcomp hsup, hJK⟩
  rw [← hsup]
  exact iSup₂_le fun C hC => le_sSup (hcomp C hC)

theorem x_mem_D {B : Subgroup G} {x : G} {L D J : Subgroup G} (hT : InT p B x L)
    (hD : InD p B x L D J) : x ∈ D := by
  obtain ⟨-, hxB, -, hLx, -, -⟩ := hT
  have hJL : J ≤ L ⊓ Subgroup.centralizer (D : Set G) := hD.2.1.1.1
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := (hJL.trans inf_le_left).trans hLx.1
  have hxJ : x ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have := Subgroup.mem_centralizer_iff.1 (hJx hj) x (Set.mem_singleton x)
    exact this.symm
  exact (hD.2.1.2.2 x hxB).1 (centMod_of_mem_centralizer hxJ)

theorem J_comp_centralizer (hp : p.Prime) {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hT : InT p B x L) (hD : InD p B x L D J) :
    GLAPComponent p (Subgroup.centralizer (D : Set G)) J := by
  have hxD := x_mem_D hT hD
  have hLx : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hT.2.2.2.1
  have hsn := isSubnormal_inf hLx.2.1 (Subgroup.centralizer (D : Set G))
  have heq : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (D : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD))
  rw [heq] at hsn
  exact glaPComponent_of_isSubnormal' hp hsn hD.2.1.1

theorem cover_layer (hp : p.Prime) {X J N : Subgroup G} (hJ : GLAPComponent p X J)
    (hcov : CoversMod p N J) : GLAPLayer p (J ⊓ N) ⊔ GLAPPrimeCoreOf p J = J := by
  set H := J ⊓ N with hH
  have hHJ : H ≤ J := inf_le_left
  have hsup : H ⊔ GLAPPrimeCoreOf p J = J := by
    have h : N ⊓ J = H := inf_comm _ _
    simpa only [CoversMod, h] using hcov
  obtain ⟨hcore, ⟨e⟩⟩ := cover_facts hp hHJ hsup
  have hJq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hHq : CFSG.Open.IsQuasisimple (PQuot p H) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hJq
  obtain ⟨-, -, hbar⟩ := glaPLayer_of_isQuasisimple hHq
  have h1 : GLAPLayer p H ⊔ GLAPPrimeCoreOf p H = H :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top (i183_glaPLayer_le p H) hbar
  have hOH : GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p J := hcore ▸ inf_le_right
  refine le_antisymm (sup_le ((i183_glaPLayer_le p H).trans hHJ) (Subgroup.map_subtype_le _)) ?_
  calc J = H ⊔ GLAPPrimeCoreOf p J := hsup.symm
    _ = (GLAPLayer p H ⊔ GLAPPrimeCoreOf p H) ⊔ GLAPPrimeCoreOf p J := by rw [h1]
    _ ≤ GLAPLayer p H ⊔ GLAPPrimeCoreOf p J := sup_le (sup_le le_sup_left (hOH.trans le_sup_right)) le_sup_right

theorem not_isPGroup_two_of_cover (hp : p.Prime) {X J J₀ : Subgroup G} (hJ : GLAPComponent p X J)
    (hJ₀ : J₀ ≤ J) (hcov : J₀ ⊔ GLAPPrimeCoreOf p J = J) : ¬ IsPGroup 2 J₀ := by
  intro h2
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  let f : ↥J₀ →* PQuot p J :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥J)).comp (Subgroup.inclusion hJ₀)
  have hfs : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : G) ∈ J₀ ⊔ GLAPPrimeCoreOf p J := hcov.symm ▸ y.2
      have hJO : J₀ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G) :=
        hJ₀.trans (le_normalizer_glaPPrimeCoreOf p J)
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right J₀ _ hJO] at hy
      obtain ⟨j, hj, o, ho, hjo⟩ := Set.mem_mul.mp hy
      refine ⟨⟨j, hj⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hJ₀ ⟨j, hj⟩) = QuotientGroup.mk y
      rw [QuotientGroup.eq]
      obtain ⟨o', ho', ho'eq⟩ := ho
      have : (Subgroup.inclusion hJ₀ ⟨j, hj⟩)⁻¹ * y = o' := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        calc j⁻¹ * (y : G) = j⁻¹ * (j * o) := by rw [hjo]
          _ = o := by group
          _ = (o' : G) := ho'eq.symm
      rw [this]
      exact ho'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (PQuot p J) := IsPGroup.of_surjective h2 f hfs
  haveI : Group.IsNilpotent (PQuot p J) := hQ2.isNilpotent
  haveI : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hq
  exact (IsSolvable.commutator_lt_top_of_nontrivial (PQuot p J)).ne hq.1

theorem partA (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L D J N : Subgroup G}
    (hT : InT p B x L) (hD : InD p B x L D J) (hN : IsTwoLocal N) (hDN : D ≤ N)
    (hcov : CoversMod p N J) :
    ∃ A J₀ S : Subgroup G, A ≤ D ∧ (A.subgroupOf D).index = p ∧ J₀ ≤ J ∧
      J₀ ⊔ GLAPPrimeCoreOf p J = J ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
      S ≤ Subgroup.centralizer (A : Set G) ∧ J₀ ≤ Subgroup.normalizer (S : Set G) ∧
      S ≤ ⁅S, J₀⁆ := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hDB : D ≤ B := hD.1.1
  have hDel : IsElemAbelian p D := isElemAbelian_mono hT.1.1 hDB
  have hJ : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) J := hD.2.1.1
  have hJL : J ≤ L ⊓ Subgroup.centralizer (D : Set G) := hJ.1
  have hD1 : D ≠ ⊥ := by
    intro h
    have h1 := hD.1.2.1
    rw [h, Subgroup.card_bot] at h1
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hJ₀le : GLAPLayer p (J ⊓ N) ≤ J ⊓ N := i183_glaPLayer_le p _
  have hJ₀J : GLAPLayer p (J ⊓ N) ≤ J := hJ₀le.trans inf_le_left
  have hJ₀cov := cover_layer hp hJ hcov
  have hnot2 := not_isPGroup_two_of_cover hp hJ hJ₀J hJ₀cov
  have hJ₀C : GLAPLayer p (J ⊓ N) ≤ N ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf (hJ₀le.trans inf_le_right) (hJ₀J.trans (hJL.trans inf_le_right))
  obtain ⟨A, hAD, hAidx, hne⟩ := GL83.I_33_3_proved G hc.charTwo p hp hp2 N D _ hN hD1 hDel hDN
    hJ₀C hnot2
  set J₀ := GLAPLayer p (J ⊓ N) with hJ₀def
  set R := pCoreOf 2 N ⊓ Subgroup.centralizer (A : Set G) with hRdef
  have hJ₀N : J₀ ≤ N := hJ₀le.trans inf_le_right
  have hJ₀A : J₀ ≤ Subgroup.centralizer (A : Set G) :=
    (hJ₀C.trans inf_le_right).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAD))
  have hJ₀R : J₀ ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer (pCoreOf 2 N : Set G) := le_normalizer_pCoreOf 2 N (hJ₀N hg)
    have h2 : g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
      Subgroup.le_normalizer (hJ₀A hg)
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    simp only [hRdef, Subgroup.mem_inf]
    exact and_congr (h1 y) (h2 y)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) inf_le_left
  have hSR : (⁅J₀, R⁆ : Subgroup G) ≤ R := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_normalizes hJ₀R
  have hcop : Nat.Coprime p (Nat.card R) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR2
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hres := layer_isOPrimeResidual hp (J ⊓ N)
  have key : (⁅⁅R, J₀⁆, J₀⁆ : Subgroup G) = ⁅R, J₀⁆ := i321UsedAt_holds p hp R J₀ hcop hJ₀R hres
  refine ⟨A, J₀, ⁅J₀, R⁆, hAD, hAidx, hJ₀J, hJ₀cov, hR2.to_le hSR, hne,
    hSR.trans inf_le_right, le_normalizer_commutator Subgroup.le_normalizer hJ₀R, ?_⟩
  rw [Subgroup.commutator_comm J₀ R]
  exact le_of_eq key.symm

theorem le_sup_of_perfect_cover {J J₀ O Ō : Subgroup G} (hperf : ⁅J, J⁆ = J) (hJ₀ : J₀ ≤ J)
    (hcov : J₀ ⊔ O = J) (hOJ : O ≤ J) (hJO : J ≤ Subgroup.normalizer (O : Set G))
    (hJŌ : J ≤ Subgroup.normalizer (Ō : Set G)) (hcomm : ⁅J, O⁆ ≤ Ō) : J ≤ J₀ ⊔ Ō := by
  have hJ₀N : J₀ ≤ Subgroup.normalizer (O : Set G) := hJ₀.trans hJO
  have hdec : ∀ y ∈ J, ∃ a ∈ J₀, ∃ o ∈ O, y = a * o := by
    intro y hy
    have h : y ∈ (J₀ ⊔ O : Subgroup G) := hcov ▸ hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right J₀ O hJ₀N] at h
    obtain ⟨a, ha, o, ho, hao⟩ := Set.mem_mul.mp h
    exact ⟨a, ha, o, ho, hao.symm⟩
  have hcO : ∀ z ∈ J, ∀ o ∈ O, ⁅z, o⁆ ∈ Ō := fun z hz o ho =>
    hcomm (Subgroup.commutator_mem_commutator hz ho)
  have hOc : ∀ o ∈ O, ∀ z ∈ J, ⁅o, z⁆ ∈ Ō := by
    intro o ho z hz
    have := Ō.inv_mem (hcO z hz o ho)
    rwa [commutatorElement_inv] at this
  have hconj : ∀ a ∈ J, ∀ x ∈ Ō, a * x * a⁻¹ ∈ Ō := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.1 (hJŌ ha) x).1 hx
  calc J = ⁅J, J⁆ := hperf.symm
    _ ≤ J₀ ⊔ Ō := by
      rw [Subgroup.commutator_le]
      intro y hy y' hy'
      obtain ⟨a, ha, o, ho, rfl⟩ := hdec y hy
      obtain ⟨a', ha', o', ho', rfl⟩ := hdec y' hy'
      have haJ : a ∈ J := hJ₀ ha
      have ha'J : a' ∈ J := hJ₀ ha'
      have e : ⁅a * o, a' * o'⁆ = (a * ⁅o, a' * o'⁆ * a⁻¹) * (⁅a, a'⁆ * (a' * ⁅a, o'⁆ * a'⁻¹)) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (hconj a haJ _
        (hOc o ho _ (J.mul_mem ha'J (hOJ ho'))))) (Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right
        (hconj a' ha'J _ (hcO a haJ o' ho'))))
      exact Subgroup.mem_sup_left (J₀.mul_mem (J₀.mul_mem (J₀.mul_mem ha ha') (J₀.inv_mem ha))
        (J₀.inv_mem ha'))

end L62

end CFSG.LocalAnalysis.GLTheoremA
