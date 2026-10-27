module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Lift
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement
open CFSG.ComponentClassification.CatalogueBCentralQuotient (derivedPreimage
  derivedPreimage_eq_commutator derivedPreimage_map derivedPreimage_perfect)

section Central

theorem glaPComponent_derivedPreimage {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {A : Subgroup G} (g : ↥A →* X) (hg : g.ker ≤ Subgroup.center ↥A)
    {M J : Subgroup X} (hgM : g.range ≤ M) (hJ : GLAPComponent p M J) (hJg : J ≤ g.range) :
    GLAPComponent p A ((derivedPreimage g J).map A.subtype) ∧ (derivedPreimage g J).map g = J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set f : ↥A →* ↥g.range := g.rangeRestrict with hfdef
  have hf : Function.Surjective f := g.rangeRestrict_surjective
  have hfker : f.ker ≤ Subgroup.center ↥A := by
    rw [hfdef, MonoidHom.ker_rangeRestrict]
    exact hg
  have hJ₁ : GLAPComponent p g.range J := glaPComponent_of_le hp hJ hJg hgM
  obtain ⟨-, hJP⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ₁
  have hL := CFSG.ComponentClassification.CatalogueBCentralQuotient.pComponent_derivedPreimage p
    f hf hfker (J.subgroupOf g.range) hJP
  have hcomap : (J.subgroupOf g.range).comap f = J.comap g := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  have heq : derivedPreimage f (J.subgroupOf g.range) = derivedPreimage g J := by
    rw [derivedPreimage_eq_commutator, derivedPreimage_eq_commutator, hcomap]
  have hmap := CFSG.ComponentClassification.CatalogueBCentralQuotient.pComponent_right_inverse p
    f hf (J.subgroupOf g.range) hJP
  rw [heq] at hL hmap
  refine ⟨(CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).2
    ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · have h1 : ((derivedPreimage g J).map A.subtype).subgroupOf A = derivedPreimage g J :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
    rw [h1]
    exact hL
  · have h2 := congrArg (Subgroup.map g.range.subtype) hmap
    rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJg] at h2
    exact h2

theorem glaPComponent_derivedPreimage_of_le {G X : Type*} [Group G] [Finite G] [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) {S A : Subgroup G} (hAS : A ≤ S) (π : ↥S →* X)
    (hπ : Function.Surjective π) (hπZ : π.ker ≤ Subgroup.center ↥S) {M J : Subgroup X}
    (hAM : ∀ a : ↥S, (a : G) ∈ A → π a ∈ M) (hJ : GLAPComponent p M J)
    (hJA : (derivedPreimage π J).map S.subtype ≤ A) :
    GLAPComponent p A ((derivedPreimage π J).map S.subtype) := by
  classical
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  have hmap : (derivedPreimage π J).map π = J := derivedPreimage_map π hπ J
  set g : ↥A →* X := π.comp (Subgroup.inclusion hAS)
  have hg : g.ker ≤ Subgroup.center ↥A := by
    intro a ha
    have ha' : Subgroup.inclusion hAS a ∈ π.ker := ha
    refine Subgroup.mem_center_iff.2 fun b => Subtype.ext ?_
    have h := Subgroup.mem_center_iff.1 (hπZ ha') (Subgroup.inclusion hAS b)
    exact congrArg (Subtype.val : ↥S → G) h
  have hgM : g.range ≤ M := by
    rintro _ ⟨a, rfl⟩
    exact hAM (Subgroup.inclusion hAS a) a.2
  have hJg : J ≤ g.range := by
    intro j hj
    rw [← hmap] at hj
    obtain ⟨s, hs, rfl⟩ := hj
    exact ⟨⟨s, hJA ⟨s, hs, rfl⟩⟩, rfl⟩
  obtain ⟨hcomp, -⟩ := glaPComponent_derivedPreimage hp g hg hgM hJ hJg
  have hP : (J.comap g).map A.subtype ≤ (J.comap π).map S.subtype := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨Subgroup.inclusion hAS a, ha, rfl⟩
  have hQ : (derivedPreimage π J).map S.subtype ≤ (J.comap g).map A.subtype := by
    rintro _ ⟨s, hs, rfl⟩
    have hsJ : π s ∈ J := by
      rw [← hmap]
      exact ⟨s, hs, rfl⟩
    exact ⟨⟨s, hJA ⟨s, hs, rfl⟩⟩, hsJ, rfl⟩
  have hperf : ⁅(derivedPreimage π J).map S.subtype, (derivedPreimage π J).map S.subtype⁆ =
      (derivedPreimage π J).map S.subtype := by
    haveI := derivedPreimage_perfect π hπ hπZ J
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have heq : (derivedPreimage π J).map S.subtype = (derivedPreimage g J).map A.subtype := by
    rw [derivedPreimage_eq_commutator g J, Subgroup.map_commutator]
    refine le_antisymm ?_ ?_
    · rw [← hperf]
      exact Subgroup.commutator_mono hQ hQ
    · rw [derivedPreimage_eq_commutator π J, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hP hP
  rw [heq]
  exact hcomp

end Central

section PullBack

theorem concA_of_actData_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S B : Subgroup Ω} (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {X : Type} [Group X] [Finite X]
    (π : ↥S →* X) (hπ : Function.Surjective π) (hπZ : π.ker ≤ Subgroup.center ↥S)
    (α : ↥B → MulAut X)
    (hα : ∀ (x : ↥B) (g : ↥S),
      π ⟨(x : Ω) * g * (x : Ω)⁻¹, hS.conj_mem _ g.2 _⟩ = α x (π g))
    (hW : ActData p B α) : S267ConcA p S B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hS
  obtain ⟨D, E, J, t, hDB, hEB, hDE, hDc, hDBc, hEc, hJ, hJB, hJD, hJE, ht1, ht2, htJ, htD⟩ := hW
  have hconj : ∀ (x : Ω) (hx : x ∈ B) (s : ↥S),
      π (MulAut.conjNormal x s) = α ⟨x, hx⟩ (π s) := by
    intro x hx s
    rw [← hα]
    exact congrArg π (Subtype.ext (MulAut.conjNormal_apply x s))
  have hcomm : ∀ (x : Ω) (u : ↥S), MulAut.conjNormal x u = u → x * (u : Ω) = (u : Ω) * x := by
    intro x u h
    have h' := congrArg Subtype.val h
    rw [MulAut.conjNormal_apply] at h'
    calc x * (u : Ω) = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [h']
  have hfix : ∀ {F : Subgroup Ω}, F ≤ B → ∀ s : ↥S,
      (s : Ω) ∈ Subgroup.centralizer (F : Set Ω) → π s ∈ actFix α F := by
    intro F hFB s hs
    refine mem_actFix.2 fun x hx => ?_
    obtain ⟨x, hxB⟩ := x
    rw [← hconj x hxB s]
    refine congrArg π (Subtype.ext ?_)
    rw [MulAut.conjNormal_apply, Subgroup.mem_centralizer_iff.1 hs x hx, mul_inv_cancel_right]
  have hcent : ∀ {F : Subgroup Ω}, F ≤ B → ∀ {M : Subgroup X}, M ≤ actFix α F →
      (derivedPreimage π M).map S.subtype ≤ Subgroup.centralizer (F : Set Ω) := by
    intro F hFB M hM
    rw [Subgroup.map_le_iff_le_comap, derivedPreimage_eq_commutator, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro f hf
    have hz : ∀ c ∈ M.comap π, c⁻¹ * MulAut.conjNormal f c ∈ Subgroup.center ↥S := by
      intro c hc
      refine hπZ ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hconj f (hFB hf) c,
        (mem_actFix.1 (hM (Subgroup.mem_comap.1 hc))) ⟨f, hFB hf⟩ hf, inv_mul_cancel]
    have key : MulAut.conjNormal f ⁅a, b⁆ = ⁅a, b⁆ := by
      rw [map_commutatorElement, ← mul_inv_cancel_left a (MulAut.conjNormal f a),
        ← mul_inv_cancel_left b (MulAut.conjNormal f b)]
      exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.commutatorElement_mul_central
        (hz a ha) (hz b hb)
    exact hcomm f _ key
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  have hJSmap : (derivedPreimage π J).map π = J := derivedPreimage_map π hπ J
  set Jt : Subgroup Ω := (derivedPreimage π J).map S.subtype with hJtdef
  have hJtS : Jt ≤ S := Subgroup.map_subtype_le _
  have hJtD : Jt ≤ Subgroup.centralizer (D : Set Ω) := hcent hDB hJ.1
  have hJtJ : ∀ s : ↥S, (s : Ω) ∈ Jt → π s ∈ J := by
    rintro s ⟨s', hs', he⟩
    obtain rfl : s' = s := Subtype.ext he
    rw [← hJSmap]
    exact ⟨s', hs', rfl⟩
  have hcomp : GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) Jt :=
    glaPComponent_derivedPreimage_of_le hp inf_le_left π hπ hπZ (fun a ha => hfix hDB a ha.2) hJ
      (le_inf hJtS hJtD)
  have hJtP : Jt = ⁅(J.comap π).map S.subtype, (J.comap π).map S.subtype⁆ := by
    rw [hJtdef, derivedPreimage_eq_commutator, Subgroup.map_commutator]
  have hconjJt : ∀ b ∈ B, ∀ h ∈ Jt, b * h * b⁻¹ ∈ Jt := by
    intro b hb h hh
    have hP : ((J.comap π).map S.subtype).map (MulAut.conj b).toMonoidHom ≤
        (J.comap π).map S.subtype := by
      rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal b s, ?_, MulAut.conjNormal_apply b s⟩
      show π (MulAut.conjNormal b s) ∈ J
      rw [hconj b hb s, ← hJB ⟨b, hb⟩]
      exact ⟨π s, hs, rfl⟩
    have hmem : b * h * b⁻¹ ∈ Jt.map (MulAut.conj b).toMonoidHom := ⟨h, hh, rfl⟩
    rw [hJtP, Subgroup.map_commutator] at hmem
    rw [hJtP]
    exact Subgroup.commutator_mono hP hP hmem
  have hBN : B ≤ Subgroup.normalizer (Jt : Set Ω) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconjJt b hb h, fun hh => ?_⟩
    have h' := hconjJt b⁻¹ (B.inv_mem hb) _ hh
    rwa [show b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h by group] at h'
  have hTle : ((GLAPPrimeCoreOf p Jt).comap S.subtype).map π ≤ GLAPPrimeCoreOf p J := by
    refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hJtJ w (CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le Jt
        (Subgroup.mem_comap.1 hw))
    · intro g hg x hx
      rw [← hJSmap] at hg
      obtain ⟨s, hs, rfl⟩ := hg
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨s * w * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have hw' : S.subtype w ∈ GLAPPrimeCoreOf p Jt := hw
      show S.subtype (s * w * s⁻¹) ∈ GLAPPrimeCoreOf p Jt
      rw [map_mul, map_mul, map_inv]
      have hsJt : (s : Ω) ∈ Jt := ⟨s, hs, rfl⟩
      exact CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem _ hsJt _ hw'
    · have h1 : Nat.card ((GLAPPrimeCoreOf p Jt).comap S.subtype) ∣
          Nat.card (GLAPPrimeCoreOf p Jt) := by
        rw [← Subgroup.card_subtype S ((GLAPPrimeCoreOf p Jt).comap S.subtype)]
        exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
      exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_map_dvd _ π).trans h1)
        (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Jt)
  have hcentD : ∀ b ∈ B, CentMod p Jt b ↔ b ∈ D := by
    intro b hb
    constructor
    · intro hc
      apply hJD ⟨b, hb⟩
      intro j hj
      rw [← hJSmap] at hj
      obtain ⟨s, hs, rfl⟩ := hj
      have hmem := (centMod_iff.1 hc).2 (s : Ω) ⟨s, hs, rfl⟩
      have e : ⁅(s : Ω), b⁆ = S.subtype (s * (MulAut.conjNormal b s)⁻¹) := by
        simp only [map_mul, map_inv, Subgroup.coe_subtype, MulAut.conjNormal_apply,
          commutatorElement_def]
        group
      rw [e, ← Subgroup.mem_comap] at hmem
      have hT := hTle (Subgroup.mem_map_of_mem π hmem)
      rwa [map_mul, map_inv, hconj b hb s] at hT
    · intro hbD
      refine centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
      exact (Subgroup.mem_centralizer_iff.1 (hJtD hh) b hbD).symm
  have hEcl : Nat.card D = p ^ 2 → ∃ E' : Subgroup Ω, E' ≤ B ∧ IsElemAbelian p E' ∧
      Nat.card E' = p ^ 3 ∧ D ≤ E' ∧
        GLAPLayer p (Jt ⊓ Subgroup.centralizer (E' : Set Ω)) ≠ ⊥ := by
    intro hD2
    refine ⟨E, hEB, hB.mono hEB, hEc hD2, hDE, ?_⟩
    obtain ⟨K, hK⟩ := (CFSG.LocalAnalysis.GLTheoremA.S267.glaPLayer_ne_bot_iff p _).1 (hJE hD2)
    have hKJ : K ≤ J := hK.1.trans inf_le_left
    have hKE : K ≤ actFix α E := hK.1.trans inf_le_right
    refine (CFSG.LocalAnalysis.GLTheoremA.S267.glaPLayer_ne_bot_iff p _).2
      ⟨_, glaPComponent_derivedPreimage_of_le hp (inf_le_left.trans hJtS) π hπ hπZ
        (M := J ⊓ actFix α E) (fun a ha => Subgroup.mem_inf.2 ⟨hJtJ a ha.1, hfix hEB a ha.2⟩)
        hK (le_inf ?_ (hcent hEB hKE))⟩
    refine Subgroup.map_mono ?_
    rw [derivedPreimage_eq_commutator, derivedPreimage_eq_commutator]
    exact Subgroup.commutator_mono (Subgroup.comap_mono hKJ) (Subgroup.comap_mono hKJ)
  have hZp : IsPGroup p (Subgroup.center ↥S) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
      hp hcore
  set n := Nat.card π.ker with hn
  have hodd : Odd n := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hZp.to_le hπZ)
    rw [hn, hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hzn : ∀ z ∈ π.ker, z ^ n = 1 := by
    intro z hz
    have h := congrArg Subtype.val (show (⟨z, hz⟩ : π.ker) ^ n = 1 from pow_card_eq_one')
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hpow : ∀ (x : Ω) (u : ↥S), π (MulAut.conjNormal x u) = π u →
      MulAut.conjNormal x (u ^ n) = u ^ n := by
    intro x u h
    have hz : u⁻¹ * MulAut.conjNormal x u ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hc : Commute u (u⁻¹ * MulAut.conjNormal x u) := Subgroup.mem_center_iff.1 (hπZ hz) u
    rw [map_pow, ← mul_inv_cancel_left u (MulAut.conjNormal x u), hc.mul_pow, hzn _ hz, mul_one]
  obtain ⟨s, hs⟩ := hπ t
  have hs2 : s ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hs, ht2]
  have hπn : π (s ^ n) = t := by
    obtain ⟨m, hm⟩ := hodd
    rw [map_pow, hs, hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hsn2 : (s ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2, pow_mul, hzn _ hs2]
  refine ⟨B, D, Jt, hB, ⟨⟨hDB, hDc, hDBc⟩, ⟨hcomp, hBN, hcentD⟩, hEcl⟩, Or.inl rfl, hBC,
    ((s ^ n : ↥S) : Ω), ?_, ?_, ?_, ?_⟩
  · intro h
    apply ht1
    rw [← hπn, show s ^ n = 1 from Subtype.ext h, map_one]
  · rw [← Subgroup.coe_pow, hsn2, Subgroup.coe_one]
  · intro d hd
    refine hcomm d _ (hpow d s ?_)
    rw [hconj d (hDB hd) s, hs, htD ⟨d, hDB hd⟩ hd]
  · rintro _ ⟨u, hu, rfl⟩
    have huJ : π u ∈ J := by
      rw [← hJSmap]
      exact ⟨u, hu, rfl⟩
    have hut : π u * t = t * π u := Subgroup.mem_centralizer_singleton_iff.1 (htJ huJ)
    refine hcomm (u : Ω) _ (hpow (u : Ω) s ?_)
    have e : MulAut.conjNormal (u : Ω) s = u * s * u⁻¹ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
    rw [e, map_mul, map_mul, map_inv, hs, hut, mul_inv_cancel_right]

end PullBack

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
