module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XInnerSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCentAbs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3

theorem card_cent_eq (T : ↥XP) :
    Nat.card ↥(centralizer ({T} : Set ↥XP)) =
      {g : Equiv.Perm (Fin 1408) | g ∈ XP ∧ g * (T : Equiv.Perm (Fin 1408)) = T * g}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨(x.1 : Equiv.Perm (Fin 1408)), x.1.2,
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext g.2.2)⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }

theorem size_filter_cent {Xl : Array Table}
    (hXl : IsEnumSet 1408 Xl (XP : Set (Equiv.Perm (Fin 1408)))) (hsize : Xl.size = Nat.card ↥XP)
    (hbase : IsBase01 XP) {τ : Table} {T : ↥XP} (hτ : Rep 1408 τ (T : Equiv.Perm (Fin 1408))) :
    (Xl.filter fun g => commB g τ).size = Nat.card ↥(centralizer ({T} : Set ↥XP)) := by
  have hs : Xl.size = (XP : Set (Equiv.Perm (Fin 1408))).ncard := by
    rw [hsize]
    exact Nat.card_coe_set_eq _
  rw [card_cent_eq]
  exact (IsEnumSet.ncard_filter_of_mem hXl hs (fun y => commB y τ)
    (fun g => g * (T : Equiv.Perm (Fin 1408)) = T * g)
    (fun x g hx hg => commB_iff hbase hx hτ hg T.2)).symm

structure XCentCtx (Xl Nl Zl : Array Table) (u1 u2 : Table) : Prop where
  facts : XNFacts
  xl : IsEnumSet 1408 Xl (XP : Set (Equiv.Perm (Fin 1408)))
  size : Xl.size = Nat.card ↥XP
  base : IsBase01 XP
  nl : IsEnumSet 1408 Nl
    (closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) : Set _)
  zl : IsEnumSet 1408 Zl
    {z | z ∈ (closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) : Set _) ∧
      (z * elemW xC1 = elemW xC1 * z ∧ z * elemW xC2 = elemW xC2 * z)}
  ru1 : Rep 1408 u1 (elemW xU1)
  ru2 : Rep 1408 u2 (elemW xU2)
  gen : closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))) = XP

theorem N_le_derived (F : XNFacts) :
    closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) ≤ derivedOf XP := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact F.c1_mem
  · exact F.c2_mem

theorem N_le_XP (F : XNFacts) :
    closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) ≤ XP :=
  (N_le_derived F).trans (derivedOf_le XP)

theorem central_of_Z (F : XNFacts) {z : Equiv.Perm (Fin 1408)}
    (h1 : z * elemW xC1 = elemW xC1 * z) (h2 : z * elemW xC2 = elemW xC2 * z) :
    ∀ x ∈ derivedOf XP, z * x = x * z := by
  intro x hx
  refine (commute_of_mem_closure (s := {elemW xC1, elemW xC2}) (a := z) ?_ (F.der_le hx)).symm
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact h1.symm
  · exact h2.symm

theorem hii_of_check {Xl Nl Zl : Array Table} {u1 u2 : Table} (C : XCentCtx Xl Nl Zl u1 u2)
    {τ : Table} {T : Equiv.Perm (Fin 1408)} (hT : T ∈ XP) (hτ : Rep 1408 τ T) (hT2 : T * T = 1)
    (h : Xl.all (fun g => !(Nl.filter fun m => commB m τ).all (fun m => commB g m) ||
      memT 1408 Zl g || memT 1408 Zl (compT 1408 g τ)) = true) :
    ∀ g ∈ XP, (∀ x ∈ derivedOf XP, x * T = T * x → g * x = x * g) →
      ∃ z₀ ∈ derivedOf XP, (∀ x ∈ derivedOf XP, z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T) := by
  have hNX := N_le_XP C.facts
  have hND := N_le_derived C.facts
  have hCN := IsEnumSet.filter_of_mem C.nl (fun m => commB m τ) (fun m => m * T = T * m)
    (fun x m hx hm => commB_iff C.base hx hτ (hNX hm) hT)
  intro g hg
  refine forall_of_all C.xl
    (fun x => !(Nl.filter fun m => commB m τ).all (fun m => commB x m) ||
      memT 1408 Zl x || memT 1408 Zl (compT 1408 x τ))
    (fun g => (∀ x ∈ derivedOf XP, x * T = T * x → g * x = x * g) →
      ∃ z₀ ∈ derivedOf XP, (∀ x ∈ derivedOf XP, z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T))
    ?_ h g hg
  intro x g' hx hg'X hb hcent
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hb
  rcases hb with (hb | hb) | hb
  · exfalso
    have hall : ((Nl.filter fun m => commB m τ).all fun m => commB x m) = true := by
      refine (forall_iff_of_mem hCN (fun y => commB x y) (fun m => g' * m = m * g') ?_).2 ?_
      · intro y m hy hm
        exact commB_iff C.base hx hy hg'X (hNX hm.1)
      · intro m hm
        exact hcent m (hND hm.1) hm.2
    rw [hall] at hb
    exact Bool.false_ne_true hb.symm
  · obtain ⟨hgN, hg1, hg2⟩ := (C.zl.memT_iff hx).1 hb
    exact ⟨g', hND hgN, central_of_Z C.facts hg1 hg2, Or.inl rfl⟩
  · obtain ⟨hgN, hg1, hg2⟩ := (C.zl.memT_iff (Rep.compT hx hτ)).1 hb
    refine ⟨g' * T, hND hgN, central_of_Z C.facts hg1 hg2, Or.inr ?_⟩
    rw [mul_assoc, hT2, mul_one]

theorem decomp_of_mul (F : XNFacts) {u T : Equiv.Perm (Fin 1408)} (hu : u ∈ XP)
    (hm : ∃ m ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      u * m * T = T * (u * m)) :
    ∃ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      ∃ c ∈ XP ⊓ centralizer ({T} : Set (Equiv.Perm (Fin 1408))), u = n * c := by
  obtain ⟨m, hm, hc⟩ := hm
  have hcX : u * m ∈ XP := XP.mul_mem hu (N_le_XP F hm)
  refine ⟨u * m * m⁻¹ * (u * m)⁻¹, F.norm_N _ hcX _ (inv_mem hm), u * m,
    mem_inf.2 ⟨hcX, mem_centralizer_singleton_iff.2 hc⟩, ?_⟩
  group

theorem ha1_of_check {Xl Nl Zl : Array Table} {u1 u2 : Table} (C : XCentCtx Xl Nl Zl u1 u2)
    {τ : Table} {T : Equiv.Perm (Fin 1408)} (hT : T ∈ XP) (hτ : Rep 1408 τ T)
    (h1 : Nl.any (fun m => commB3 u1 m τ) = true) (h2 : Nl.any (fun m => commB3 u2 m τ) = true) :
    ∀ y ∈ XP, ∃ n ∈ derivedOf XP, ∃ c ∈ XP, c * T = T * c ∧ y = n * c := by
  have hu1 : elemW xU1 ∈ XP := by rw [← C.gen]; exact subset_closure (by simp)
  have hu2 : elemW xU2 ∈ XP := by rw [← C.gen]; exact subset_closure (by simp)
  have e1 := (exists_iff_of_mem C.nl (fun m => commB3 u1 m τ)
    (fun m => elemW xU1 * m * T = T * (elemW xU1 * m))
    (fun x g hx hg => commB3_iff C.base C.ru1 hx hτ hu1 (N_le_XP C.facts hg) hT)).1 h1
  have e2 := (exists_iff_of_mem C.nl (fun m => commB3 u2 m τ)
    (fun m => elemW xU2 * m * T = T * (elemW xU2 * m))
    (fun x g hx hg => commB3_iff C.base C.ru2 hx hτ hu2 (N_le_XP C.facts hg) hT)).1 h2
  have hN : ∀ g ∈ closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))),
      ∀ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      g * n * g⁻¹ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) := by
    rw [C.gen]
    exact C.facts.norm_N
  have hC : XP ⊓ centralizer ({T} : Set (Equiv.Perm (Fin 1408))) ≤
      closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))) := by
    rw [C.gen]
    exact inf_le_left
  have hall := exists_mul_of_gen hN hC (decomp_of_mul C.facts hu1 e1) (decomp_of_mul C.facts hu2 e2)
  intro y hy
  rw [← C.gen] at hy
  obtain ⟨n, hn, c, hc, rfl⟩ := hall y hy
  exact ⟨n, N_le_derived C.facts hn, c, (mem_inf.1 hc).1,
    mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2, rfl⟩

theorem xCentTau_spec {Xl Nl Zl : Array Table} {u1 u2 : Table} (C : XCentCtx Xl Nl Zl u1 u2)
    {τ : Table} {T : ↥XP} (hτ : Rep 1408 τ (T : Equiv.Perm (Fin 1408))) (hT2 : T * T = 1)
    (h : xCentTauOK Xl Nl Zl u1 u2 τ = true) : XAutCent ↥XP T := by
  unfold xCentTauOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hi, h1⟩, h2⟩ := h
  have hT2' : (T : Equiv.Perm (Fin 1408)) * T = 1 := congrArg Subtype.val hT2
  have hAT : elemA * (T : Equiv.Perm (Fin 1408)) = T * elemA :=
    (C.facts.a_central T T.2).symm
  exact xAutCent_of_ambient XP C.facts.a_mem T.2 C.facts.inner hAT
    (hii_of_check C T.2 hτ hT2' hi) (ha1_of_check C T.2 hτ h1 h2)

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
