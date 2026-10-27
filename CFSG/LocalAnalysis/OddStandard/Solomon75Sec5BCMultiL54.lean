module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiBase
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracSw

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section L54

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem l54_a_prime (h : Sec5Data X n z Z S)
    (hk : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂) {t : X} (ht : IsSec5Inv X Z t)
    (hnorm : ∀ A', Sec5Comp X n (normalizer (Z : Set X)) A' → t ∈ normalizer (A' : Set X))
    (hnt : ∀ A', Sec5Comp X n (normalizer (Z : Set X)) A' → ¬ CentModOdd A' t)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {r : X} (hrA : r ∈ A)
    (hr1 : r ≠ 1) (hr2 : r * r = 1) (hrt : r * t = t * r) :
    K0 X n (K0 X n (centralizer ({t} : Set X)) ⊓ centralizer ({r} : Set X)) = ⊥ := by
  have hrN : r ∈ normalizer ((normalizer (Z : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_normalizer (hA.isPCompIn.1 hrA)
  obtain ⟨Aj, hAj, hne⟩ : ∃ Aj : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) Aj ∧
      Aj ≠ A := by
    obtain ⟨A₁, A₂, h₁, h₂, h12⟩ := hk
    by_cases h1A : A₁ = A
    · exact ⟨A₂, h₂, fun h => h12 (h1A.trans h.symm)⟩
    · exact ⟨A₁, h₁, h1A⟩
  exact lemmaB_core h ht hAj (hnorm Aj hAj) (hnt Aj hAj) hr1 hr2 hrt
    (normalizes_isPCompIn_of_comm_mem hAj.isPCompIn hrN (fun l hl =>
      commutator_mem_oddCoreOf_of_ne hAj.isPCompIn hA.isPCompIn hne hl hrA))

theorem l54_b_prime (h : Sec5Data X n z Z S)
    (hk : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂) {t : X} (ht : IsSec5Inv X Z t)
    (hZt : Z ≤ centralizer ({t} : Set X))
    (hw : ∀ L, Sec5Comp X n (centralizer ({t} : Set X)) L → z ∈ normalizer (L : Set X))
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {r : X} (hrA : r ∈ A)
    (hr1 : r ≠ 1) (hr2 : r * r = 1) (hrt : r * t = t * r) :
    ∀ L, Sec5Comp X n (centralizer ({t} : Set X)) L → r ∈ normalizer (L : Set X) := by
  classical
  intro B hB
  by_contra hrB
  set Cs : Subgroup X := centralizer ({t} : Set X) with hCs
  have hs2 : t ^ 2 = 1 := by rw [sq]; exact ht.sq
  have hr2' : r ^ 2 = 1 := by rw [sq]; exact hr2
  have hr2o : orderOf r = 2 := orderOf_eq_prime hr2' hr1
  have hrN : r ∈ normalizer (Z : Set X) := hA.isPCompIn.1 hrA
  have hrK0 : r ∈ K0 X n (normalizer (Z : Set X)) :=
    (le_sSup hA : A ≤ K0 X n (normalizer (Z : Set X))) hrA
  have hrC : r ∈ Cs := Subgroup.mem_centralizer_singleton_iff.2 hrt
  have hwZ : z ∈ Z := h.pair.mem
  have hw2 : z * z = 1 := h.Z_sq_eq_one hwZ
  have hw2' : z ^ 2 = 1 := by rw [sq]; exact hw2
  have hw1 : z ≠ 1 := by
    intro h1
    have := h.pair.orderOf_z
    rw [h1, orderOf_one] at this
    omega
  have hwC : z ∈ Cs := hZt hwZ
  have hws : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.1 hwC
  have hwr : z * r = r * z := h.Z_le_center_K0 hwZ hrK0
  have hwB : z ∈ normalizer (B : Set X) := hw B hB
  have ha' := sec5_K0_inf_eq_bot h ht hwZ hw1 hws
  have hB' : Sec5Comp X n Cs (B.map (MulAut.conj r).toMonoidHom) :=
    hB.map_conj (Subgroup.le_normalizer hrC)
  have hBCs : B ≤ Cs := hB.isPCompIn.1
  have hB'Cs : B.map (MulAut.conj r).toMonoidHom ≤ Cs := hB'.isPCompIn.1
  have hBc : IsPComponent 2 (B.subgroupOf Cs) := hB.isPCompIn.2
  have hZB : IsPGroup 2 ↥(center (↥(B.subgroupOf Cs) ⧸ pPrimeCore 2 ↥(B.subgroupOf Cs))) := by
    have hc : Nat.card (center (↥B ⧸ pPrimeCore 2 ↥B)) = 2 := hB.2.2.1
    have h0 : IsPGroup 2 ↥(center (↥B ⧸ pPrimeCore 2 ↥B)) :=
      IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hBCs)
    exact h0.of_equiv (centerCongr f).symm
  set trc : ↥Cs := ⟨r, hrC⟩ with htrc
  set twc : ↥Cs := ⟨z, hwC⟩ with htwc
  have htr : trc * trc = 1 := Subtype.ext hr2
  have hcomm : twc * trc = trc * twc := Subtype.ext hwr
  have hne : (B.subgroupOf Cs).map (MulAut.conj trc).toMonoidHom ≠ B.subgroupOf Cs := by
    rw [map_conj_subgroupOf hrC B]
    intro heq
    apply hrB
    have : B.map (MulAut.conj r).toMonoidHom = B := by
      have h1 := heq
      rw [Subgroup.subgroupOf_inj, inf_of_le_left hB'Cs, inf_of_le_left hBCs] at h1
      exact h1
    exact mem_normalizer_of_map_conj_eq this
  have htw : ∀ b ∈ B.subgroupOf Cs, twc * b * twc⁻¹ ∈ B.subgroupOf Cs := by
    intro b hb
    exact (Subgroup.mem_normalizer_iff.1 hwB (b : X)).1 hb
  obtain ⟨Δ, hΔC, hΔpc, hΔn, hkey⟩ := exists_diag_lift hBc hZB htr hcomm hne htw
  set ΔX : Subgroup X := Δ.map Cs.subtype with hΔX
  have hΔXs : ΔX ≤ Cs := Subgroup.map_subtype_le Δ
  have hΔXr : ΔX ≤ centralizer ({r} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hΔC hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcenmap : (centralizer ({trc} : Set ↥Cs)).map Cs.subtype =
      Cs ⊓ centralizer ({r} : Set X) := by
    rw [centralizer_singleton_subgroup hrC, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hΔXpc : IsPCompIn 2 (Cs ⊓ centralizer ({r} : Set X)) ΔX := by
    refine ⟨le_inf hΔXs hΔXr, ?_⟩
    have h1 := (isPComponent_subgroupOf_map_iff 2 Cs.subtype Cs.subtype_injective hΔC).2 hΔpc
    rwa [hcenmap] at h1
  have hΔL : ΔX ≤ LPlusIn (centralizer ({r} : Set X)) :=
    le_LPlusIn_of_isPCompIn_inf hs2 hrt.symm hΔXpc
  have hJ0 : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥ := by
    obtain ⟨Aj, hAj, hne'⟩ : ∃ Aj : Subgroup X,
        Sec5Comp X n (normalizer (Z : Set X)) Aj ∧ Aj ≠ A := by
      obtain ⟨A₁, A₂, h₁, h₂, h12⟩ := hk
      by_cases h1A : A₁ = A
      · exact ⟨A₂, h₂, fun h => h12 (h1A.trans h.symm)⟩
      · exact ⟨A₁, h₁, h1A⟩
    have hrN' : r ∈ normalizer ((normalizer (Z : Set X) : Subgroup X) : Set X) :=
      Subgroup.le_normalizer (hA.isPCompIn.1 hrA)
    have hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj) :=
      normalizes_isPCompIn_of_comm_mem hAj.isPCompIn hrN' (fun l hl =>
        commutator_mem_oddCoreOf_of_ne hAj.isPCompIn hA.isPCompIn hne' hl hrA)
    exact K0_ne_bot_of_centralizerSection hr2' hAj hscj
  have hL34 := h.l52.c r hrN hr2o hJ0
  set OO : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) with hOO
  set W₂ : Subgroup X := Z ⊓ centralizer ({r} : Set X) with hW₂
  have hCn : centralizer ({r} : Set X) ≤ normalizer (OO : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hOOodd : Odd (Nat.card OO) := odd_card_oddCoreOf _
  have hW₂p : IsPGroup 2 ↥W₂ := h.isPGroup_Z.to_le inf_le_left
  set OOc : Subgroup ↥Cs := OO.comap Cs.subtype with hOOc
  set W₂c : Subgroup ↥Cs := W₂.comap Cs.subtype with hW₂c
  have hOOcodd : Odd (Nat.card OOc) := by
    refine Odd.of_dvd_nat hOOodd (Subgroup.card_dvd_of_injective
      (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : OOc →* ↥OO) ?_)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun u : ↥OO => (u : X)) hab))
  have hW₂cp : IsPGroup 2 ↥W₂c := by
    refine hW₂p.of_injective (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : W₂c →* ↥W₂) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun u : ↥W₂ => (u : X)) hab))
  have hconjOO : ∀ y : ↥Cs, (y : X) ∈ centralizer ({r} : Set X) →
      y ∈ normalizer (OOc : Set ↥Cs) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro u
    exact mem_normalizer_iff.1 (hCn hy) (u : X)
  have hΔOO : Δ ≤ normalizer (OOc : Set ↥Cs) := fun x hx =>
    hconjOO x (hΔXr ⟨x, hx, rfl⟩)
  have hW₂OO : W₂c ≤ normalizer (OOc : Set ↥Cs) := fun x hx => hconjOO x hx.2
  have hV : ∀ x ∈ Δ, ⁅x, twc⁆ ∈ OOc ⊔ W₂c := by
    intro x hx
    have hxX : (x : X) ∈ LPlusIn (centralizer ({r} : Set X)) := hΔL ⟨x, hx, rfl⟩
    obtain ⟨o, ho, w', hw', hxw⟩ := commutator_decomp_of_mirror hwZ hwr.symm hL34 hxX
    have hw'C : w' ∈ Cs := hZt hw'.1
    have hcx : (((⁅x, twc⁆ : ↥Cs)) : X) = ⁅(x : X), z⁆ := by
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
  have hsc : z ∈ centralizerSection B (pPrimeCoreOf 2 B) := by
    refine ⟨hwB, mem_normalizer_oddCoreOf_of_mem_normalizer hwB, fun b hb => ?_⟩
    have h1 := hcommAll ⟨b, hBCs hb⟩ hb
    have h2 : ⁅b, z⁆ ∈ oddCoreOf Cs :=
      ⟨_, h1, by simp [commutatorElement_def, htwc]⟩
    have h3 : ⁅b, z⁆ ∈ B := by
      have e : ⁅b, z⁆ = b * (z * b⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.1 hwB b⁻¹).1 (B.inv_mem hb))
    exact inf_oddCoreOf_le hBCs ⟨h3, h2⟩
  exact K0_ne_bot_of_centralizerSection hw2' hB hsc ha'

end L54

end CFSG.OddStandard.Solomon75
