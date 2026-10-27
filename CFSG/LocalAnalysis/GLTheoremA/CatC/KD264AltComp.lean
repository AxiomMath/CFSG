module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Comp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Inner
open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

section

variable {n : ℕ} (K : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n))
variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
variable (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ p = 1)

theorem comm_iff_psi (b : B) (k : K) :
    (b : Y) * (k : Y) = (k : Y) * (b : Y) ↔
      psiHom K hK e hp hp2 hn B hB b * e k = e k * psiHom K hK e hp hp2 hn B hB b := by
  have hc := psiHom_conj K hK e hp hp2 hn B hB b k
  set s : K := e.symm (psiHom K hK e hp hp2 hn B hB b) with hs
  have hpsi : psiHom K hK e hp hp2 hn B hB b = e s := by
    rw [hs, MulEquiv.apply_symm_apply]
  rw [hpsi]
  constructor
  · intro h
    have h1 : (b : Y) * (k : Y) * (b : Y)⁻¹ = (k : Y) := by rw [h]; simp
    have h2 : (s : Y) * (k : Y) * (s : Y)⁻¹ = (k : Y) := by rw [← hc, h1]
    have h3 : s * k * s⁻¹ = k := Subtype.ext (by simpa using h2)
    have h4 := congrArg e h3
    rw [map_mul, map_mul, map_inv] at h4
    exact mul_inv_eq_iff_eq_mul.1 h4
  · intro h
    have h1 : e (s * k * s⁻¹) = e k := by
      rw [map_mul, map_mul, map_inv, h]
      group
    have h2 : s * k * s⁻¹ = k := e.injective h1
    have h3 : (s : Y) * (k : Y) * (s : Y)⁻¹ = (k : Y) := by
      have := congrArg (fun z : K => (z : Y)) h2
      simpa using this
    have h4 : (b : Y) * (k : Y) * (b : Y)⁻¹ = (k : Y) := hc.trans h3
    calc (b : Y) * (k : Y) = ((b : Y) * (k : Y) * (b : Y)⁻¹) * (b : Y) := by group
      _ = (k : Y) * (b : Y) := by rw [h4]

@[expose] noncomputable def psiImage (E : Subgroup Y) : Subgroup (alternatingGroup (Fin n)) :=
  (E.subgroupOf B).map (psiHom K hK e hp hp2 hn B hB)

theorem centralizer_psiImage_map (E : Subgroup Y) (hEB : E ≤ B) :
    (Subgroup.centralizer ((psiImage K hK e hp hp2 hn B hB E : Subgroup _) :
        Set (alternatingGroup (Fin n)))).map (K.subtype.comp e.symm.toMonoidHom) =
      K ⊓ Subgroup.centralizer (E : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨(e.symm x).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwB : w ∈ B := hEB hw
    have hmem : psiHom K hK e hp hp2 hn B hB ⟨w, hwB⟩ ∈
        psiImage K hK e hp hp2 hn B hB E :=
      Subgroup.mem_map.2 ⟨⟨w, hwB⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
    have hk := (comm_iff_psi K hK e hp hp2 hn B hB ⟨w, hwB⟩ (e.symm x)).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_iff.1 hx _ hmem)
    exact hk
  · intro hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyK, hyc⟩ := hy
    refine ⟨e ⟨y, hyK⟩, Subgroup.mem_centralizer_iff.2 ?_, ?_⟩
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
      have hwE : (w : Y) ∈ E := Subgroup.mem_subgroupOf.1 hw
      rw [Subgroup.mem_centralizer_iff] at hyc
      have hc : (w : Y) * y = y * (w : Y) := hyc w hwE
      exact (comm_iff_psi K hK e hp hp2 hn B hB w ⟨y, hyK⟩).1 hc
    · show (e.symm (e ⟨y, hyK⟩) : Y) = y
      rw [MulEquiv.symm_apply_apply]

theorem glaPLayer_ne_bot_of_psi (E : Subgroup Y) (hEB : E ≤ B)
    (τ : alternatingGroup (Fin n)) (hτ : τ ∈ psiImage K hK e hp hp2 hn B hB E)
    (hsupp : ∀ g ∈ psiImage K hK e hp hp2 hn B hB E,
      (g : Equiv.Perm (Fin n)).support ⊆ (τ : Equiv.Perm (Fin n)).support)
    (h5 : 5 ≤ n - (τ : Equiv.Perm (Fin n)).support.card)
    (hpn : p ≤ n - (τ : Equiv.Perm (Fin n)).support.card) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
  classical
  set P := psiImage K hK e hp hp2 hn B hB E with hP
  set f : alternatingGroup (Fin n) →* Y := K.subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hcomp := altFix_isPComponent hp hp2 hτ hsupp h5 hpn
  have hker : Nat.Coprime p
      (Nat.card ↥((Subgroup.centralizer (P : Set (alternatingGroup (Fin n)))) ⊓ f.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hfinj, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hmap := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp f hker hcomp
  rw [centralizer_psiImage_map K hK e hp hp2 hn B hB E hEB] at hmap
  have hne : altFix (τ : Equiv.Perm (Fin n)) ≠ ⊥ := by
    intro hbot
    obtain ⟨φ⟩ := nonempty_altFix_equiv (m := n - (τ : Equiv.Perm (Fin n)).support.card)
      (τ : Equiv.Perm (Fin n)) rfl
    have h1 := Nat.card_congr φ.toEquiv
    rw [hbot, Subgroup.card_bot] at h1
    haveI : IsSimpleGroup (alternatingGroup (Fin (n - (τ : Equiv.Perm (Fin n)).support.card))) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5)
    have h2 := Finite.one_lt_card (α := alternatingGroup (Fin (n - (τ : Equiv.Perm (Fin n)).support.card)))
    omega
  have hne' : (altFix (τ : Equiv.Perm (Fin n))).map f ≠ ⊥ := by
    intro hb
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ hfinj).1 hb)
  intro hbot
  have hle : (altFix (τ : Equiv.Perm (Fin n))).map f ≤
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) := le_sSup hmap
  rw [hbot] at hle
  exact hne' (le_bot_iff.1 hle)

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Comp
