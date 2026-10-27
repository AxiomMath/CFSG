module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClPerf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Layer
public import Certificates.Data.A5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup RegularWreathProduct
open scoped commutatorElement

variable {D : Type} [Group D]

@[expose] def sec128PfSigma : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem sec128PfSigma_ne : sec128PfSigma ≠ 1 := by decide

theorem sec128PfSigma_inv : sec128PfSigma⁻¹ = sec128PfSigma := by decide

theorem sec128Pf_cases (q : Multiplicative (ZMod 2)) : q = 1 ∨ q = sec128PfSigma := by
  revert q
  decide

@[expose] noncomputable def sec128PfPair (a b : D) : WrZ2 D :=
  ⟨fun q => if q = 1 then a else b, 1⟩

theorem sec128PfPair_mul (a b a' b' : D) :
    sec128PfPair a b * sec128PfPair a' b' = sec128PfPair (a * a') (b * b') := by
  classical
  ext q
  · rcases sec128Pf_cases q with h | h <;> subst h <;>
      simp (config := {decide := true}) [sec128PfPair]
  · simp [sec128PfPair]

theorem sec128PfPair_one : sec128PfPair (1 : D) 1 = 1 := by
  classical
  ext q
  · simp [sec128PfPair]
  · simp [sec128PfPair]

@[expose] noncomputable def sec128PfPairHom : D × D →* WrZ2 D where
  toFun p := sec128PfPair p.1 p.2
  map_one' := sec128PfPair_one
  map_mul' p q := (sec128PfPair_mul p.1 p.2 q.1 q.2).symm

theorem sec128PfPairHom_injective : Function.Injective (sec128PfPairHom (D := D)) := by
  classical
  intro p q h
  have h1 := congrArg (fun w : WrZ2 D => w.left 1) h
  have h2 := congrArg (fun w : WrZ2 D => w.left sec128PfSigma) h
  simp only [sec128PfPairHom, MonoidHom.coe_mk, OneHom.coe_mk, sec128PfPair, if_true,
    if_neg sec128PfSigma_ne] at h1 h2
  exact Prod.ext h1 h2

theorem sec128Pf_eq_pair (w : WrZ2 D) (hw : w.right = 1) :
    w = sec128PfPair (w.left 1) (w.left sec128PfSigma) := by
  classical
  ext q
  · rcases sec128Pf_cases q with h | h
    · subst h
      simp [sec128PfPair]
    · subst h
      simp [sec128PfPair, sec128PfSigma_ne]
  · simp [sec128PfPair, hw]

theorem sec128PfPairHom_range :
    (sec128PfPairHom (D := D)).range = (rightHom : WrZ2 D →* Multiplicative (ZMod 2)).ker := by
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    exact rfl
  · intro hw
    exact ⟨(w.left 1, w.left sec128PfSigma), (sec128Pf_eq_pair w hw).symm⟩

theorem sec128Pf_swap (a b : D) :
    (inl sec128PfSigma : WrZ2 D) * sec128PfPair a b * (inl sec128PfSigma : WrZ2 D)⁻¹ =
      sec128PfPair b a := by
  classical
  ext q
  · rcases sec128Pf_cases q with h | h
    · subst h
      simp [sec128PfPair, sec128PfSigma_inv, sec128PfSigma_ne]
    · subst h
      simp [sec128PfPair, sec128PfSigma_inv, sec128PfSigma_ne]
  · simp [sec128PfPair]

theorem sec128_A5_perfect : _root_.commutator ↥(alternatingGroup (Fin 5)) = ⊤ := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (_root_.commutator ↥(alternatingGroup (Fin 5))) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := sec128_A5_noncomm
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · exact h

theorem sec128_A5_exists_noncomm {a : ↥(alternatingGroup (Fin 5))} (ha : a ≠ 1) :
    ∃ h : ↥(alternatingGroup (Fin 5)), h * a ≠ a * h := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  by_contra hcon
  push Not at hcon
  have hz : a ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := Subgroup.mem_center_iff.mpr hcon
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(alternatingGroup (Fin 5))) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact ha hz
  · obtain ⟨x, y, hxy⟩ := sec128_A5_noncomm
    have hy : y ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
      rw [h]
      exact Subgroup.mem_top y
    exact hxy (Subgroup.mem_center_iff.mp hy x)

theorem sec128_pf_wr_normal
    (N : Subgroup (WrZ2 ↥(alternatingGroup (Fin 5)))) [hNn : N.Normal]
    (hN : ⁅N, N⁆ = N) (hN1 : N ≠ ⊥) :
    N = (rightHom : WrZ2 ↥(alternatingGroup (Fin 5)) →* Multiplicative (ZMod 2)).ker := by
  classical
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hle : N ≤ (rightHom : WrZ2 ↥(alternatingGroup (Fin 5)) →*
      Multiplicative (ZMod 2)).ker :=
    sec128_perfect_le_ker (fun a b => mul_comm a b) N hN rightHom
  refine le_antisymm hle ?_
  have hswap : ∀ a b : ↥(alternatingGroup (Fin 5)),
      sec128PfPair a b ∈ N → sec128PfPair b a ∈ N := by
    intro a b hab
    rw [← sec128Pf_swap a b]
    exact hNn.conj_mem _ hab _
  have key : ∀ a b : ↥(alternatingGroup (Fin 5)), sec128PfPair a b ∈ N → a ≠ 1 →
      ∀ x : ↥(alternatingGroup (Fin 5)), sec128PfPair x 1 ∈ N := by
    intro a b hab ha
    obtain ⟨h, hh⟩ := sec128_A5_exists_noncomm ha
    have hc : sec128PfPair ⁅h, a⁆ 1 ∈ N := by
      have h1 := hNn.conj_mem _ hab (sec128PfPair h 1)
      have h2 := N.mul_mem h1 (N.inv_mem hab)
      have e : sec128PfPair h 1 * sec128PfPair a b * (sec128PfPair h 1)⁻¹ *
          (sec128PfPair a b)⁻¹ = sec128PfPair ⁅h, a⁆ 1 := by
        have e0 : ((h, 1) : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) * (a, b) *
            (h, 1)⁻¹ * (a, b)⁻¹ = (⁅h, a⁆, 1) := by
          simp [commutatorElement_def]
        have e1 := congrArg (sec128PfPairHom (D := ↥(alternatingGroup (Fin 5)))) e0
        simp only [map_mul, map_inv] at e1
        exact e1
      rwa [e] at h2
    let N₁ : Subgroup ↥(alternatingGroup (Fin 5)) :=
      N.comap (sec128PfPairHom.comp (MonoidHom.inl _ _))
    haveI : N₁.Normal := hNn.comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₁ with h0 | h0
    · exfalso
      have hmem : ⁅h, a⁆ ∈ N₁ := hc
      rw [h0, Subgroup.mem_bot] at hmem
      exact hh (commutatorElement_eq_one_iff_mul_comm.mp hmem)
    · intro x
      have : x ∈ N₁ := by rw [h0]; exact Subgroup.mem_top x
      exact this
  obtain ⟨p, hpN, hp1⟩ : ∃ p ∈ N, p ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hN1 ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  have hpr : p.right = 1 := MonoidHom.mem_ker.mp (hle hpN)
  have hp : p = sec128PfPair (p.left 1) (p.left sec128PfSigma) := sec128Pf_eq_pair p hpr
  rw [hp] at hpN
  have hfirst : ∀ x, sec128PfPair x 1 ∈ N := by
    by_cases ha : p.left 1 = 1
    · have hb : p.left sec128PfSigma ≠ 1 := by
        intro hb
        apply hp1
        rw [hp, ha, hb]
        exact sec128PfPair_one
      exact key _ _ (hswap _ _ hpN) hb
    · exact key _ _ hpN ha
  have hsecond : ∀ x, sec128PfPair 1 x ∈ N := fun x => hswap _ _ (hfirst x)
  intro w hw
  have hw' : w.right = 1 := hw
  rw [sec128Pf_eq_pair w hw']
  have e : sec128PfPair (w.left 1) (w.left sec128PfSigma) =
      sec128PfPair (w.left 1) 1 * sec128PfPair 1 (w.left sec128PfSigma) := by
    rw [sec128PfPair_mul, mul_one, one_mul]
  rw [e]
  exact N.mul_mem (hfirst _) (hsecond _)

theorem sec128_pf_wr_type (N : Subgroup (WrZ2 ↥(alternatingGroup (Fin 5)))) [N.Normal]
    (hN : ⁅N, N⁆ = N) (hN1 : N ≠ ⊥) :
    N.index = 2 ∧
      Nonempty (↥N ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))) := by
  have hN' := sec128_pf_wr_normal N hN hN1
  have hsurj : Function.Surjective
      (rightHom : WrZ2 ↥(alternatingGroup (Fin 5)) →* Multiplicative (ZMod 2)) :=
    fun q => ⟨inl q, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hN', Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
      Nat.card_zmod]
  · exact ⟨(MulEquiv.subgroupCongr (hN'.trans sec128PfPairHom_range.symm)).trans
      (MonoidHom.ofInjective sec128PfPairHom_injective).symm⟩

end CFSG.OddStandard.SmallF3.Omega
