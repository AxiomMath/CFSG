module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightStrong

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

omit [Finite X] in
theorem rightConjugate_le_conjugateClosure {G Z : Subgroup X} {c : X} (hc : c ∈ G) :
    rightConjugate Z c ≤ conjugateClosure G Z :=
  le_iSup (fun x : G => rightConjugate Z (x : X)) ⟨c, hc⟩

omit [Finite X] in
theorem map_rightConjugate (Z : Subgroup X) (c x : X) :
    (rightConjugate Z c).map (MulAut.conj x).toMonoidHom = rightConjugate Z (c * x⁻¹) := by
  rw [rightConjugate, rightConjugate, Subgroup.map_map]
  congr 1
  ext u
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite X] in
theorem le_normalizer_conjugateClosure (G Z : Subgroup X) :
    G ≤ Subgroup.normalizer ((conjugateClosure G Z : Subgroup X) : Set X) := by
  refine le_normalizer_of_map_le fun x hx => ?_
  unfold conjugateClosure
  rw [Subgroup.map_iSup]
  refine iSup_le fun c => ?_
  rw [map_rightConjugate]
  exact rightConjugate_le_conjugateClosure (G.mul_mem c.2 (G.inv_mem hx))

omit [Finite X] in
theorem mem_normalizer_conjugateClosure {G Z : Subgroup X} {t : X}
    (htG : t ∈ Subgroup.normalizer (G : Set X)) (htZ : t ∈ Subgroup.normalizer (Z : Set X)) :
    t ∈ Subgroup.normalizer ((conjugateClosure G Z : Subgroup X) : Set X) := by
  have key : ∀ s ∈ Subgroup.normalizer (G : Set X), s ∈ Subgroup.normalizer (Z : Set X) →
      (conjugateClosure G Z).map (MulAut.conj s).toMonoidHom ≤ conjugateClosure G Z := by
    intro s hsG hsZ
    unfold conjugateClosure
    rw [Subgroup.map_iSup]
    refine iSup_le fun c => ?_
    rw [map_rightConjugate]
    have h1 : (c : X) * s⁻¹ = s⁻¹ * (s * c * s⁻¹) := by group
    rw [h1, ← rightConjugate_mul, (rightConjugate_eq_self_iff Z s⁻¹).mpr (Subgroup.inv_mem _ hsZ)]
    exact rightConjugate_le_conjugateClosure
      ((Subgroup.mem_normalizer_iff.mp hsG c).mp c.2)
  have h := le_normalizer_of_map_le (A := Subgroup.zpowers t) (K := conjugateClosure G Z)
    (fun s hs => key s (Subgroup.zpowers_le.mpr htG hs) (Subgroup.zpowers_le.mpr htZ hs))
  exact h (Subgroup.mem_zpowers t)

omit [Finite X] in
theorem conjugateClosure_le {G Z : Subgroup X} (hZG : Z ≤ G) : conjugateClosure G Z ≤ G := by
  refine iSup_le fun c => ?_
  intro u hu
  rw [mem_rightConjugate_iff] at hu
  have := G.mul_mem (G.mul_mem (G.inv_mem c.2) (hZG hu)) c.2
  simpa [mul_assoc] using this

namespace ElemCtx

theorem conjugateClosure_facts (c : ElemCtx G T S Q H g y) :
    conjugateClosure G ((T ⊔ rightConjugate T g) ⊓ G) ≤ G ∧
      G ⊔ T ≤ Subgroup.normalizer
        ((conjugateClosure G ((T ⊔ rightConjugate T g) ⊓ G) : Subgroup X) : Set X) ∧
      (T ⊔ rightConjugate T g) ⊓ G ≤ conjugateClosure G ((T ⊔ rightConjugate T g) ⊓ G) := by
  have e := c.elem
  refine ⟨conjugateClosure_le inf_le_right, sup_le (le_normalizer_conjugateClosure _ _) ?_,
    le_conjugateClosure _ _⟩
  intro t ht
  exact mem_normalizer_conjugateClosure (c.frame.le_normalizer ht)
    (S_le_normalizer_Z e (c.sylowFrame.le ht))

theorem normalClosure_eq_top (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs)
    {L : Subgroup X} (hLdef : L = conjugateClosure G ((T ⊔ rightConjugate T g) ⊓ G)) :
    Subgroup.normalClosure ((((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L : Subgroup L) :
      Set L) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLG, hLN, hZL⟩ := c.conjugateClosure_facts
  rw [← hLdef] at hLG hLN hZL
  set N := Subgroup.normalClosure ((((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L : Subgroup L) :
    Set L) with hNdef
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hPL : IsSylowOf 2 ((S ⊓ G) ⊓ L) L :=
    c.isSylowOf_P.inf_of_le_normalizer hLG (le_sup_left.trans hLN)
  have hle' : conjugateClosure G ((T ⊔ rightConjugate T g) ⊓ G) ≤ N.map L.subtype := by
    refine iSup_le fun x => ?_
    have hZx : rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) (x : X) ≤ L :=
      hLdef ▸ rightConjugate_le_conjugateClosure x.2
    have h2 : IsPGroup 2 (rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) (x : X)) :=
      (c.sylowFrame.sylow.isPGroup.to_le (c.Z_le_P.trans inf_le_left)).map _
    obtain ⟨m, hm, hmkey⟩ := isSylowOf_exists_conj_mem hPL hZx h2
    intro u hu
    have hmu := hmkey u hu
    have hz := (mem_rightConjugate_iff _ _ _).mp hu
    have h3 : m⁻¹ * u * m = ((x : X) * m)⁻¹ * ((x : X) * u * (x : X)⁻¹) * ((x : X) * m) := by
      group
    have hz' : m⁻¹ * u * m ∈ (T ⊔ rightConjugate T g) ⊓ G := by
      rw [h3] at hmu ⊢
      exact c.stronglyClosed_Z hin _ hz _ (G.mul_mem x.2 (hLG hm)) hmu.1
    have hmuL : m⁻¹ * u * m ∈ L := hZL hz'
    have hmem : (⟨m⁻¹ * u * m, hmuL⟩ : L) ∈ N :=
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hz')
    have h4 := hNn.conj_mem _ hmem ⟨m, hm⟩
    refine ⟨_, h4, ?_⟩
    simp [mul_assoc]
  have hle : L ≤ N.map L.subtype := (le_of_eq hLdef).trans hle'
  rw [eq_top_iff]
  intro l _
  obtain ⟨n, hn, hnl⟩ := hle l.2
  rwa [← Subtype.ext hnl]

theorem goldschmidt_L (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs) :
    ∃ L : Subgroup X, L ≤ G ∧ G ⊔ T ≤ Subgroup.normalizer (L : Set X) ∧
      (T ⊔ rightConjugate T g) ⊓ G ≤ L ∧
      CFSG.Open.pCore 2 L ⊔ goldschmidtLayer L = ⊤ ∧
      ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L = CFSG.Open.pCore 2 L ⊔
          Subgroup.closure {t | t ∈ (S ⊓ G).subgroupOf L ⊓ goldschmidtLayer L ∧ t ^ 2 = 1} ∧
      ∀ K : Subgroup L, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  obtain ⟨hLG, hLN, hZL⟩ := c.conjugateClosure_facts
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjugateClosure G ((T ⊔ rightConjugate T g) ⊓ G) := ⟨_, rfl⟩
  rw [← hLdef] at hLG hLN hZL
  have hPL : IsSylowOf 2 ((S ⊓ G) ⊓ L) L :=
    c.isSylowOf_P.inf_of_le_normalizer hLG (le_sup_left.trans hLN)
  obtain ⟨SY, hSY⟩ := hPL
  have hSYeq : (SY : Subgroup L) = (S ⊓ G).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hSY, Subgroup.subgroupOf_map_subtype]
  have hAS : ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L ≤ (SY : Subgroup L) := by
    rw [hSYeq]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (c.Z_le_P (Subgroup.mem_subgroupOf.mp hx))
  have hAab : IsMulCommutative (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L) :=
    CFSG.Goldschmidt.isMulCommutative_subgroupOf
      (isMulCommutative_of_le inf_le_left e.hyp45.facts.2.2.2) L
  have hcl : fusionStronglyClosed ((((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L : Subgroup L) :
      Set L) (SY : Subgroup L) := by
    intro a ha l hl
    rw [hSYeq] at hl
    have ha' := Subgroup.mem_subgroupOf.mp ha
    have hl' := Subgroup.mem_subgroupOf.mp hl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hl'
    have h := c.stronglyClosed_Z hin _ ha' _ (hLG l.2) hl'
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h)
  have hO : goldschmidtOddCore L = ⊥ :=
    oddCore_eq_bot_of_le_normalizer c.oddCore_eq_bot hLG (le_sup_left.trans hLN)
  have h := goldschmidt_core hin.goldschmidt L SY _ hAS hAab hcl
    (c.normalClosure_eq_top hin hLdef) hO
  rw [hSYeq] at h
  exact ⟨L, hLG, hLN, hZL, h⟩

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
