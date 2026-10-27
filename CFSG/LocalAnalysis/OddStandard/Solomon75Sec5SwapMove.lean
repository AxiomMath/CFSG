module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapB

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Basic

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem mem_centralizerSection_of_swap (h : Sec5Data X n z Z S) {s : X} (hs2 : s * s = 1)
    (hZs : Z ≤ centralizer ({s} : Set X)) {u : X} (huZ : u ∈ Z) (hu1 : u ≠ 1) {r : X}
    (hrZ : r ∈ Z) {B : Subgroup X} (hB : Sec5Comp X n (centralizer ({s} : Set X)) B)
    (hBu : B.map (MulAut.conj u).toMonoidHom ≠ B) (hrB : r ∈ normalizer (B : Set X)) :
    r ∈ centralizerSection B (pPrimeCoreOf 2 B) := by
  classical
  set Cs : Subgroup X := centralizer ({s} : Set X) with hCs
  have hs2' : s ^ 2 = 1 := by rw [sq]; exact hs2
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hu2' : u ^ 2 = 1 := by rw [sq]; exact hu2
  have hu2o : orderOf u = 2 := h.orderOf_eq_two_of_mem_Z huZ hu1
  have huN : u ∈ normalizer (Z : Set X) := Subgroup.le_normalizer huZ
  have hur : r * u = u * r := h.Z_comm hrZ huZ
  have huC : u ∈ Cs := hZs huZ
  have hrC : r ∈ Cs := hZs hrZ
  have hsu : s * u = u * s := (Subgroup.mem_centralizer_singleton_iff.1 huC).symm
  have hB' : Sec5Comp X n Cs (B.map (MulAut.conj u).toMonoidHom) :=
    hB.map_conj (Subgroup.le_normalizer huC)
  have hBCs : B ≤ Cs := hB.isPCompIn.1
  have hB'Cs : B.map (MulAut.conj u).toMonoidHom ≤ Cs := hB'.isPCompIn.1
  have hBc : IsPComponent 2 (B.subgroupOf Cs) := hB.isPCompIn.2
  have hZB := hB.isPGroup_center_quot
  set trc : ↥Cs := ⟨u, huC⟩ with htrc
  set twc : ↥Cs := ⟨r, hrC⟩ with htwc
  have htr : trc * trc = 1 := Subtype.ext hu2
  have hcomm : twc * trc = trc * twc := Subtype.ext hur
  have hne : (B.subgroupOf Cs).map (MulAut.conj trc).toMonoidHom ≠ B.subgroupOf Cs := by
    rw [map_conj_subgroupOf huC B]
    intro heq
    apply hBu
    have h1 := heq
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hB'Cs, inf_of_le_left hBCs] at h1
    exact h1
  have htw : ∀ b ∈ B.subgroupOf Cs, twc * b * twc⁻¹ ∈ B.subgroupOf Cs := by
    intro b hb
    exact (Subgroup.mem_normalizer_iff.1 hrB (b : X)).1 hb
  obtain ⟨Δ, hΔC, hΔpc, hΔn, hkey⟩ := exists_diag_lift hBc hZB htr hcomm hne htw
  set ΔX : Subgroup X := Δ.map Cs.subtype with hΔX
  have hΔXs : ΔX ≤ Cs := Subgroup.map_subtype_le Δ
  have hΔXu : ΔX ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hΔC hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcenmap : (centralizer ({trc} : Set ↥Cs)).map Cs.subtype =
      Cs ⊓ centralizer ({u} : Set X) := by
    rw [centralizer_singleton_subgroup huC, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hΔXpc : IsPCompIn 2 (Cs ⊓ centralizer ({u} : Set X)) ΔX := by
    refine ⟨le_inf hΔXs hΔXu, ?_⟩
    have h1 := (isPComponent_subgroupOf_map_iff 2 Cs.subtype Cs.subtype_injective hΔC).2 hΔpc
    rwa [hcenmap] at h1
  have hΔL : ΔX ≤ LPlusIn (centralizer ({u} : Set X)) :=
    le_LPlusIn_of_isPCompIn_inf hs2' hsu hΔXpc
  have hJ0 : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({u} : Set X)) ≠ ⊥ := by
    obtain ⟨A₀, hA₀, -⟩ := h.exists_comp
    have hscj : u ∈ centralizerSection A₀ (pPrimeCoreOf 2 A₀) := by
      refine normalizes_isPCompIn_of_comm_mem hA₀.isPCompIn (Subgroup.le_normalizer huN)
        (fun l hl => ?_)
      have hlK : l ∈ K0 X n (normalizer (Z : Set X)) := (le_sSup hA₀ : A₀ ≤ _) hl
      have : ⁅l, u⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (h.Z_le_center_K0 huZ hlK).symm
      rw [this]
      exact one_mem _
    exact K0_ne_bot_of_centralizerSection hu2' hA₀ hscj
  have hL34 := h.l52.c u huN hu2o hJ0
  set OO : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({u} : Set X))) with hOO
  set W₂ : Subgroup X := Z ⊓ centralizer ({u} : Set X) with hW₂
  have hCn : centralizer ({u} : Set X) ≤ normalizer (OO : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hOOodd : Odd (Nat.card OO) := odd_card_oddCoreOf _
  have hW₂p : IsPGroup 2 ↥W₂ := h.isPGroup_Z.to_le inf_le_left
  set OOc : Subgroup ↥Cs := OO.comap Cs.subtype with hOOc
  set W₂c : Subgroup ↥Cs := W₂.comap Cs.subtype with hW₂c
  have hOOcodd : Odd (Nat.card OOc) := by
    refine Odd.of_dvd_nat hOOodd (Subgroup.card_dvd_of_injective
      (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : OOc →* ↥OO) ?_)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥OO => (t : X)) hab))
  have hW₂cp : IsPGroup 2 ↥W₂c := by
    refine hW₂p.of_injective (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : W₂c →* ↥W₂) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥W₂ => (t : X)) hab))
  have hconjOO : ∀ y : ↥Cs, (y : X) ∈ centralizer ({u} : Set X) →
      y ∈ normalizer (OOc : Set ↥Cs) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro t
    exact mem_normalizer_iff.1 (hCn hy) (t : X)
  have hΔOO : Δ ≤ normalizer (OOc : Set ↥Cs) := fun x hx =>
    hconjOO x (hΔXu ⟨x, hx, rfl⟩)
  have hW₂OO : W₂c ≤ normalizer (OOc : Set ↥Cs) := fun x hx => hconjOO x hx.2
  have hV : ∀ x ∈ Δ, ⁅x, twc⁆ ∈ OOc ⊔ W₂c := by
    intro x hx
    have hxX : (x : X) ∈ LPlusIn (centralizer ({u} : Set X)) := hΔL ⟨x, hx, rfl⟩
    obtain ⟨o, ho, w', hw', hxw⟩ := commutator_decomp_of_mirror hrZ hur.symm hL34 hxX
    have hw'C : w' ∈ Cs := hZs hw'.1
    have hcx : (((⁅x, twc⁆ : ↥Cs)) : X) = ⁅(x : X), r⁆ := by
      simp [commutatorElement_def, htwc]
    have hoC : o ∈ Cs := by
      have : o = (((⁅x, twc⁆ : ↥Cs)) : X) * w'⁻¹ := by rw [hcx, hxw]; group
      rw [this]
      exact Cs.mul_mem (⁅x, twc⁆ : ↥Cs).2 (Cs.inv_mem hw'C)
    have hprod : ⁅x, twc⁆ = (⟨o, hoC⟩ : ↥Cs) * ⟨w', hw'C⟩ :=
      Subtype.ext (by rw [hcx, hxw]; rfl)
    rw [hprod]
    exact Subgroup.mul_mem_sup (show (⟨o, hoC⟩ : ↥Cs) ∈ OOc from ho)
      (show (⟨w', hw'C⟩ : ↥Cs) ∈ W₂c from hw')
  have hcommAll := hkey OOc W₂c hOOcodd hΔOO hW₂cp hW₂OO hV
  refine ⟨hrB, mem_normalizer_oddCoreOf_of_mem_normalizer hrB, fun b hb => ?_⟩
  have h1 := hcommAll ⟨b, hBCs hb⟩ hb
  have h2 : ⁅b, r⁆ ∈ oddCoreOf Cs := ⟨_, h1, by simp [commutatorElement_def, htwc]⟩
  have h3 : ⁅b, r⁆ ∈ B := by
    have e : ⁅b, r⁆ = b * (r * b⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.1 hrB b⁻¹).1 (B.inv_mem hb))
  exact inf_oddCoreOf_le hBCs ⟨h3, h2⟩

end Basic

end CFSG.OddStandard.Solomon75
