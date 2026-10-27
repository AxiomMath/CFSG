module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.RankThree.PartOne.KS.Lines

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped commutatorElement

theorem b3SporPair_of_model_prime {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo) (M : Type) [Group M] [Finite M]
    (hM : Nonempty (M ≃* (TauCeti.CFSGIndex.sporadic name).Group))
    (h : ∀ x : M, orderOf x = p → B3Phi p (Subgroup.centralizer ({x} : Set M))) :
    B3SporPair name p := by
  refine b3SporPair_of_centralizer_phi hp hp2 hOut ?_
  intro S _ _ _ he s hs
  let e : S ≃* M := he.some.trans hM.some.symm
  have ho : orderOf (e s) = p := by simp [hs]
  have h1 := h (e s) ho
  rw [← map_centralizer_mulEquiv e s] at h1
  exact (b3Phi_map_iff hp e.toMonoidHom e.injective).1 h1

section Ambient

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem b3Phi_centralizer_of_sub (hp : p.Prime) (P : Subgroup G)
    (h : ∀ x ∈ P, orderOf x = p → B3Phi p (Subgroup.centralizer ({x} : Set G) ⊓ P)) :
    ∀ x : P, orderOf x = p → B3Phi p (Subgroup.centralizer ({x} : Set P)) := by
  intro x hx
  rw [← b3Phi_map_iff hp P.subtype P.subtype_injective, map_centralizer_subtype]
  exact h x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)

theorem map_conj_centralizer_inf {P : Subgroup G} {k : G} (hk : ∀ q ∈ P, k * q * k⁻¹ ∈ P)
    (hk' : ∀ q ∈ P, k⁻¹ * q * k ∈ P) (x : G) :
    (Subgroup.centralizer ({x} : Set G) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * x * k⁻¹} : Set G) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
    refine ⟨?_, hk z hzP⟩
    calc k * z * k⁻¹ * (k * x * k⁻¹) = k * (z * x) * k⁻¹ := by group
      _ = k * (x * z) * k⁻¹ := by rw [hzc]
      _ = k * x * k⁻¹ * (k * z * k⁻¹) := by group
  · rintro ⟨hyc, hyP⟩
    refine ⟨k⁻¹ * y * k, ⟨?_, hk' y hyP⟩, by group⟩
    calc k⁻¹ * y * k * x = k⁻¹ * (y * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * x * k⁻¹) * y) * k := by rw [hyc]
      _ = x * (k⁻¹ * y * k) := by group

theorem b3Phi_conj_of_normalizes (hp : p.Prime) {P R : Subgroup G}
    (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {k : G} (hk : k ∈ R) {x : G}
    (h : B3Phi p (Subgroup.centralizer ({x} : Set G) ⊓ P)) :
    B3Phi p (Subgroup.centralizer ({k * x * k⁻¹} : Set G) ⊓ P) := by
  have hk' : ∀ q ∈ P, k⁻¹ * q * k ∈ P := fun q hq => by
    simpa using hR k⁻¹ (R.inv_mem hk) q hq
  rw [← map_conj_centralizer_inf (hR k hk) hk' x]
  exact (b3Phi_map_iff hp (MulAut.conj k).toMonoidHom (MulAut.conj k).injective).2 h

theorem centralizer_singleton_eq_of_zpowers {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have e : ∀ c : G, Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers c : Set G) := fun c => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [e a, e b, h]

theorem b3Phi_of_lines (hp : p.Prime) {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*} (line : ι → G)
    (hlines : ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j))
    (hline : ∀ j, B3Phi p (Subgroup.centralizer ({line j} : Set G) ⊓ P)) :
    ∀ y ∈ P, orderOf y = p → B3Phi p (Subgroup.centralizer ({y} : Set G) ⊓ P) := by
  have : Fact p.Prime := ⟨hp⟩
  intro y hyP hyo
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full hQP hQ hyP hyo
  set t := g⁻¹ * y * g with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj g⁻¹ : G ≃* G).orderOf_eq y
    simpa [MulAut.conj_apply, htdef, hyo] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have ht : B3Phi p (Subgroup.centralizer ({t} : Set G) ⊓ P) := by
    rw [centralizer_singleton_eq_of_zpowers hj]
    exact hline j
  have hy : y = g * t * g⁻¹ := by rw [htdef]; group
  rw [hy]
  exact b3Phi_conj_of_normalizes hp (fun r hr q hq => P.mul_mem (P.mul_mem hr hq) (P.inv_mem hr))
    hgP ht

theorem mem_normalizer_centralizer_inf {P R : Subgroup G}
    (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {x c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G) ⊓ R) :
    c ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) ⊓ P : Subgroup G) : Set G) := by
  obtain ⟨hcx, hcR⟩ := Subgroup.mem_inf.1 hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hcx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hyx, hyP⟩
    refine ⟨?_, hR c hcR y hyP⟩
    calc c * y * c⁻¹ * x = c * y * (c⁻¹ * x) := by group
      _ = c * y * (x * c⁻¹) := by
          rw [show c⁻¹ * x = x * c⁻¹ by
            calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
              _ = x * c⁻¹ := by group]
      _ = c * (y * x) * c⁻¹ := by group
      _ = c * (x * y) * c⁻¹ := by rw [hyx]
      _ = (c * x) * y * c⁻¹ := by group
      _ = (x * c) * y * c⁻¹ := by rw [hcx]
      _ = x * (c * y * c⁻¹) := by group
  · rintro ⟨hyx, hyP⟩
    have hyP' : y ∈ P := by
      have := hR c⁻¹ (R.inv_mem hcR) _ hyP
      rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at this
    refine ⟨?_, hyP'⟩
    have hxc : c⁻¹ * x * c = x := by
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [hcx]
        _ = x := by group
    have hx' : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [hcx]
        _ = x := by group
    calc y * x = c⁻¹ * ((c * y * c⁻¹) * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * x) * c := by rw [hx']
      _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [hyx]
      _ = (c⁻¹ * x * c) * y := by group
      _ = x * y := by rw [hxc]

theorem gLAPPrimeCoreOf_inf_le_of_ambient (hp : p.Prime) {P R : Subgroup G} (hPR : P ≤ R)
    (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) (x : G) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ R) := by
  refine le_GLAPPrimeCoreOf_of_normal ((GLAPPrimeCoreOf_le _).trans (inf_le_inf_left _ hPR))
    (fun c hc => GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp
      (mem_normalizer_centralizer_inf hR hc)) (coprime_card_GLAPPrimeCoreOf hp _)

theorem gLAPPrimeCoreOf_inf_eq_bot_of_ambient (hp : p.Prime) {P R : Subgroup G} (hPR : P ≤ R)
    (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {x : G}
    (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ R) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P) = ⊥ :=
  le_bot_iff.1 (h ▸ gLAPPrimeCoreOf_inf_le_of_ambient hp hPR hR x)

theorem gLAPPrimeCoreOf_le_inf_centralizer (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hpL : p ∣ Nat.card L) :
    GLAPPrimeCoreOf p C ≤ C ⊓ Subgroup.centralizer (L : Set G) := by
  intro r hr
  refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_le C hr, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  refine (commute_of_mem_gLAPPrimeCoreOf_of_perfect hp hLC hLn
    (commutator_eq_self_of_commutator_eq_top hL.1) ?_ hr l hl).symm
  intro M hML hMn hcop m hm l' hl'
  rcases commute_or_eq_of_isQuasisimple hL hML hMn with h | h
  · exact h m hm l' hl'
  · subst h
    exact absurd hpL ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)

theorem b3Phi_of_card_le_two {C : Subgroup G} (h : Nat.card (GLAPPrimeCoreOf p C) ≤ 2) :
    B3Phi p C := by
  refine b3Phi_of_comm fun J hJ g hg o ho => ?_
  have hgC : g ∈ C := hJ.1 hg
  have hconj : g * o * g⁻¹ ∈ GLAPPrimeCoreOf p C := GLAPPrimeCoreOf_conj_mem g hgC o ho
  by_cases ho1 : o = 1
  · rw [ho1, one_mul, mul_one]
  · have hne : (⟨g * o * g⁻¹, hconj⟩ : ↥(GLAPPrimeCoreOf p C)) ≠ 1 := by
      intro he
      apply ho1
      have he' : g * o * g⁻¹ = 1 := congrArg Subtype.val he
      calc o = g⁻¹ * (g * o * g⁻¹) * g := by group
        _ = 1 := by rw [he']; group
    have hne' : (⟨o, ho⟩ : ↥(GLAPPrimeCoreOf p C)) ≠ 1 := fun he =>
      ho1 (congrArg Subtype.val he)
    have heq := congrArg Subtype.val (eq_of_ne_one_of_card_le_two h hne hne')
    have heq' : g * o * g⁻¹ = o := heq
    calc o * g = (g * o * g⁻¹) * g := by rw [heq']
      _ = g * o := by group

theorem commutator_le_centralizer_of_isCyclic {C : Subgroup G}
    (h : IsCyclic ↥(GLAPPrimeCoreOf p C)) :
    ⁅C, C⁆ ≤ Subgroup.centralizer (GLAPPrimeCoreOf p C : Set G) := by
  set O := GLAPPrimeCoreOf p C with hO
  have hnorm : ∀ c ∈ C, c ∈ Subgroup.normalizer (O : Set G) := fun c hc =>
    Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => GLAPPrimeCoreOf_conj_mem c hc x hx,
      fun hx => by
        have := GLAPPrimeCoreOf_conj_mem c⁻¹ (C.inv_mem hc) _ hx
        rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this⟩
  have hcomm : ∀ α β : MulAut ↥O, α * β = β * α := fun α β => by
    apply (IsCyclic.mulAutMulEquiv (G := ↥O)).injective
    rw [map_mul, map_mul, mul_comm]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  set a' : ↥(Subgroup.normalizer (O : Set G)) := ⟨a, hnorm a ha⟩
  set b' : ↥(Subgroup.normalizer (O : Set G)) := ⟨b, hnorm b hb⟩
  have key : O.normalizerMonoidHom ⁅a', b'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have happ := congrArg (fun α : MulAut ↥O => ((α ⟨o, ho⟩ : ↥O) : G)) key
  have hval : ((⁅a', b'⁆ : ↥(Subgroup.normalizer (O : Set G))) : G) = ⁅a, b⁆ := rfl
  have h1 : ⁅a, b⁆ * o * ⁅a, b⁆⁻¹ = o := by
    rw [← hval]
    exact happ
  calc o * ⁅a, b⁆ = (⁅a, b⁆ * o * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [h1]
    _ = ⁅a, b⁆ * o := by group

theorem b3Phi_of_isCyclic {C : Subgroup G} (h : IsCyclic ↥(GLAPPrimeCoreOf p C)) :
    B3Phi p C := by
  refine b3Phi_of_comm fun J hJ g hg o ho => ?_
  have hJC : J ≤ C := hJ.1
  have hgJ : g ∈ ⁅J, J⁆ := by rw [glaPComponent_perfect hJ]; exact hg
  have hgC := commutator_le_centralizer_of_isCyclic h (Subgroup.commutator_mono hJC hJC hgJ)
  exact Subgroup.mem_centralizer_iff.1 hgC o ho

theorem b3Phi_inf_of_ambient_dvd_two_mul (hp : p.Prime) {P R : Subgroup G} (hPR : P ≤ R)
    (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {x : G} {K : Subgroup G}
    (hK : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ R) ≤ K)
    (hKcard : Nat.card K = 2 * p) :
    B3Phi p (Subgroup.centralizer ({x} : Set G) ⊓ P) := by
  refine b3Phi_of_card_le_two ?_
  set O := GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P) with hO
  have hOK : O ≤ K := (gLAPPrimeCoreOf_inf_le_of_ambient hp hPR hR x).trans hK
  have hdvd : Nat.card O ∣ 2 * p := hKcard ▸ Subgroup.card_dvd_of_le hOK
  have hcop : Nat.Coprime p (Nat.card O) := coprime_card_GLAPPrimeCoreOf hp _
  have h2 : Nat.card O ∣ 2 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm hcop) hdvd)
  exact Nat.le_of_dvd (by norm_num) h2

theorem card_eq_of_sylow_subgroupOf {P Q : Subgroup G} (hQP : Q ≤ P)
    (hS : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P) [Fact p.Prime] :
    Nat.card Q = p ^ (Nat.card P).factorization p := by
  obtain ⟨S, hS⟩ := hS
  rw [← S.card_eq_multiplicity, hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv]

theorem lines_of_eq {Q : Subgroup G} {ι : Type*} {line : ι → G}
    (h : {H : Subgroup G | H ≤ Q ∧ Nat.card H = p} = Set.range (fun j => Subgroup.zpowers (line j))) :
    ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j) := by
  intro H hHQ hHc
  have hmem : H ∈ {H : Subgroup G | H ≤ Q ∧ Nat.card H = p} := ⟨hHQ, hHc⟩
  rw [h] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, hj.symm⟩

theorem commutator_self_conj_mem {C : Subgroup G} {g : G} (hg : g ∈ C) {d : G}
    (hd : d ∈ ⁅C, C⁆) : g * d * g⁻¹ ∈ ⁅C, C⁆ := by
  have hC : C.map (MulAut.conj g).toMonoidHom = C := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact C.mul_mem (C.mul_mem hg hc) (C.inv_mem hg)
    · intro hy
      refine ⟨g⁻¹ * y * g, C.mul_mem (C.mul_mem (C.inv_mem hg) hy) hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hmap : (⁅C, C⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator, hC]
  rw [← hmap]
  exact ⟨d, hd, rfl⟩

theorem commutator_self_le' (C : Subgroup G) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)

theorem isQuasisimple_of_simple_subgroup {D : Subgroup G} (hDs : IsSimpleGroup ↥D)
    (hnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) : CFSG.Open.IsQuasisimple ↥D := by
  have := hDs
  obtain ⟨g, hg, h, hh, hne⟩ := hnab
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
    (CFSG.RankThree.PartOne.isQuasisimple_of_isSimpleGroup
      ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩)

theorem gLAPPrimeCoreOf_eq_bot_of_record_pgroup (hp : p.Prime) {C A : Subgroup G} (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hAp : IsPGroup p A)
    (hcent : Subgroup.centralizer (A : Set G) ⊓ C ≤ A) : GLAPPrimeCoreOf p C = ⊥ := by
  refine gLAPPrimeCoreOf_eq_bot_of_pConstrained hp hAC
    (fun g hg q hq => Subgroup.mem_subgroupOf.1
      (hAn.conj_mem ⟨q, hAC hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨g, hg⟩)) hAp ?_
  rw [inf_comm]
  exact hcent

theorem gLAPPrimeCoreOf_eq_bot_of_record_derived (hp : p.Prime) {C : Subgroup G}
    (hDs : IsSimpleGroup ↥(⁅C, C⁆ : Subgroup G))
    (hnab : ∃ g ∈ (⁅C, C⁆ : Subgroup G), ∃ h ∈ (⁅C, C⁆ : Subgroup G), g * h ≠ h * g)
    (hpD : p ∣ Nat.card ↥(⁅C, C⁆ : Subgroup G))
    (hcent : IsPGroup p ↥(Subgroup.centralizer ((⁅C, C⁆ : Subgroup G) : Set G) ⊓ C)) :
    GLAPPrimeCoreOf p C = ⊥ := by
  refine gLAPPrimeCoreOf_eq_bot_of_isQuasisimple hp (commutator_self_le' C)
    (fun g hg d hd => commutator_self_conj_mem hg hd) (isQuasisimple_of_simple_subgroup hDs hnab)
    hpD ?_
  rw [inf_comm]
  exact hcent

end Ambient

end CFSG.HardMathSupport.Solomon.Coordinator
