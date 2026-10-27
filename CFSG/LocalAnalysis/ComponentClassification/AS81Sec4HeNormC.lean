module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeNormX

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.Monster.B.Co2 CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.LargeExtraspecial
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem card_centralizer_eq (hM : HeModelFacts) {z : G}
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2))))) :
    Nat.card (centralizer ({z} : Set G)) = 21504 := by
  obtain ⟨θ₁⟩ := hC
  obtain ⟨θ₂⟩ := hM.bridge
  rw [← hM.card_PC]
  exact Nat.card_congr (θ₁.trans θ₂).toEquiv

theorem exists_normC (hM : HeModelFacts) {E F S₁ : Subgroup G} {z : G}
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))))
    (hz1 : z ≠ 1) (hS₁C : S₁ ≤ centralizer ({z} : Set G)) (hS₁ : Nat.card S₁ = 1024)
    (hN : S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G)) (hEFS : E ⊔ F ≤ S₁)
    (hEF : E ≠ F) (hIE : Nat.card (iX z E) = 3072) (hIF : Nat.card (iX z F) = 3072)
    (hE2 : ∀ x ∈ E, x * x = 1) (hE64 : Nat.card E = 64) (hF2 : ∀ x ∈ F, x * x = 1)
    (hF64 : Nat.card F = 64) :
    ∃ (s : Bool) (f : ↥hePC ≃* ↥(centralizer ({z} : Set G))),
      (∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) = heTC ↔ (f n : G) = z) ∧
      (∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heBC ↔ (f n : G) ∈ S₁) ∧
      (∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heP12C s ↔ (f n : G) ∈ iX z E) ∧
      (∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heP12C (!s) ↔ (f n : G) ∈ iX z F) ∧
      (∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heEC s ↔ (f n : G) ∈ E) ∧
      ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heEC (!s) ↔ (f n : G) ∈ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ₁⟩ := hC
  obtain ⟨θ₂⟩ := hM.bridge
  set C := centralizer ({z} : Set G) with hCdef
  set f₀ : ↥hePC ≃* ↥C := (θ₁.trans θ₂).symm with hf₀
  have hIEC : iX z E ≤ C := (oUpper_le' _).trans inf_le_left
  have hIFC : iX z F ≤ C := (oUpper_le' _).trans inf_le_left
  have hIEN : iX z E ≤ normalizer (E : Set G) := (oUpper_le' _).trans inf_le_right
  have hIFN : iX z F ≤ normalizer (F : Set G) := (oUpper_le' _).trans inf_le_right
  set P₁ : Subgroup (Equiv.Perm (Fin 32)) :=
    ((S₁.subgroupOf C).comap f₀.toMonoidHom).map hePC.subtype with hP₁
  have hP₁le : P₁ ≤ hePC := map_subtype_le _
  have hP₁c : Nat.card P₁ = 1024 := by rw [card_map_comap f₀ hS₁C, hS₁]
  have hsyl : ∀ {B : Subgroup (Equiv.Perm (Fin 32))}, B ≤ hePC → Nat.card B = 1024 →
      IsSylowOf 2 B hePC := by
    intro B hB hBc
    refine isSylowOf_iff.mpr ⟨hB, IsPGroup.of_card (n := 10) (by rw [hBc]; norm_num), ?_⟩
    have h := relIndex_mul_card B hePC
    rw [inf_eq_left.mpr hB, hBc, hM.card_PC] at h
    have h21 : B.relIndex hePC = 21 := by omega
    rw [h21]
    decide
  obtain ⟨c, hcC, hcP⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf
      (hsyl hM.BC_le hM.card_BC) (hsyl hP₁le hP₁c)
  set c' : ↥hePC := ⟨c, hcC⟩ with hc'
  set f := (MulAut.conj c').trans f₀ with hf
  have hfa : ∀ n : ↥hePC, f n = f₀ (c' * n * c'⁻¹) := fun n => rfl
  have hB : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heBC ↔ (f n : G) ∈ S₁ := by
    intro n
    rw [← hcP, mem_rightConjugate_iff, mem_map_comap_iff, hfa]
    constructor
    · rintro ⟨h, hS⟩
      have : (⟨c * n * c⁻¹, h⟩ : ↥hePC) = c' * n * c'⁻¹ := rfl
      rwa [this] at hS
    · intro hS
      exact ⟨(c' * n * c'⁻¹).2, hS⟩
  have hpre : ∀ {Y : Subgroup G}, Y ≤ C → ∀ n : ↥hePC,
      (n : Equiv.Perm (Fin 32)) ∈ ((Y.subgroupOf C).comap f.toMonoidHom).map hePC.subtype ↔
        (f n : G) ∈ Y := fun {Y} _ n => by
    rw [mem_map_comap_iff]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨n.2, h⟩⟩
  have hrad : ∀ {X : Subgroup G}, X ≤ S₁ → S₁ ≤ normalizer (X : Set G) →
      (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      ((X.subgroupOf C).comap f.toMonoidHom).map hePC.subtype = heEC false ∨
        ((X.subgroupOf C).comap f.toMonoidHom).map hePC.subtype = heEC true := by
    intro X hXS hSX hX2 hX64
    have hXC := hXS.trans hS₁C
    refine hM.normal_BC _ (fun p hp => ?_) (fun b hb x hx => ?_) (fun x hx => ?_)
      (by rw [card_map_comap f hXC, hX64])
    · obtain ⟨hpC, hpX⟩ := (mem_map_comap_iff f X p).mp hp
      exact (hB ⟨p, hpC⟩).mpr (hXS hpX)
    · obtain ⟨hxC, hxX⟩ := (mem_map_comap_iff f X x).mp hx
      have hbC := hM.BC_le hb
      have hbS : (f ⟨b, hbC⟩ : G) ∈ S₁ := (hB ⟨b, hbC⟩).mp hb
      refine (mem_map_comap_iff f X _).mpr ⟨mul_mem (mul_mem hbC hxC) (inv_mem hbC), ?_⟩
      have : (⟨b * x * b⁻¹, mul_mem (mul_mem hbC hxC) (inv_mem hbC)⟩ : ↥hePC) =
          ⟨b, hbC⟩ * ⟨x, hxC⟩ * (⟨b, hbC⟩ : ↥hePC)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      simp only [coe_mul, coe_inv]
      exact (mem_normalizer_iff.mp (hSX hbS) _).mp hxX
    · obtain ⟨hxC, hxX⟩ := (mem_map_comap_iff f X x).mp hx
      have h1 : f (⟨x, hxC⟩ * ⟨x, hxC⟩) = 1 := by
        rw [map_mul]
        exact Subtype.ext (hX2 _ hxX)
      have h2 : (⟨x, hxC⟩ : ↥hePC) * ⟨x, hxC⟩ = 1 := by
        rw [← map_one f] at h1
        exact f.injective h1
      exact congrArg Subtype.val h2
  have hES : E ≤ S₁ := le_sup_left.trans hEFS
  have hFS : F ≤ S₁ := le_sup_right.trans hEFS
  have hE₀ := hrad hES (hN.trans inf_le_left) hE2 hE64
  have hF₀ := hrad hFS (hN.trans inf_le_right) hF2 hF64
  have hne : ((E.subgroupOf C).comap f.toMonoidHom).map hePC.subtype ≠
      ((F.subgroupOf C).comap f.toMonoidHom).map hePC.subtype := by
    intro heq
    have hle : ∀ {X Y : Subgroup G}, X ≤ C → Y ≤ C →
        ((X.subgroupOf C).comap f.toMonoidHom).map hePC.subtype =
          ((Y.subgroupOf C).comap f.toMonoidHom).map hePC.subtype → X ≤ Y := by
      intro X Y hXC hYC h x hx
      have hn := f.apply_symm_apply ⟨x, hXC hx⟩
      have h1 := (hpre hXC (f.symm ⟨x, hXC hx⟩)).mpr (by rw [hn]; exact hx)
      rw [h] at h1
      have h2 := (hpre hYC _).mp h1
      rwa [hn] at h2
    exact hEF (le_antisymm (hle (hES.trans hS₁C) (hFS.trans hS₁C) heq)
      (hle (hFS.trans hS₁C) (hES.trans hS₁C) heq.symm))
  obtain ⟨s, hsE, hsF⟩ : ∃ s : Bool,
      ((E.subgroupOf C).comap f.toMonoidHom).map hePC.subtype = heEC s ∧
      ((F.subgroupOf C).comap f.toMonoidHom).map hePC.subtype = heEC (!s) := by
    rcases hE₀ with h1 | h1 <;> rcases hF₀ with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact ⟨false, h1, h2⟩
    · exact ⟨true, h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  have hpar : ∀ {X : Subgroup G} {t : Bool}, X ≤ C → iX z X ≤ C →
      iX z X ≤ normalizer (X : Set G) → Nat.card (iX z X) = 3072 →
      ((X.subgroupOf C).comap f.toMonoidHom).map hePC.subtype = heEC t →
      (((iX z X).subgroupOf C).comap f.toMonoidHom).map hePC.subtype = heP12C t := by
    intro X t hXC hIC hIN hIc hXt
    refine eq_of_le_of_card_ge (fun p hp => ?_) (by rw [card_map_comap f hIC, hIc, hM.card_P12C])
    obtain ⟨hpC, hpI⟩ := (mem_map_comap_iff f _ p).mp hp
    rw [← hM.norm_EC t, ← hXt]
    refine ⟨hpC, mem_normalizer_of_forall fun x hx => ?_⟩
    obtain ⟨hxC, hxX⟩ := (mem_map_comap_iff f X x).mp hx
    refine (mem_map_comap_iff f X _).mpr ⟨mul_mem (mul_mem hpC hxC) (inv_mem hpC), ?_⟩
    have : (⟨p * x * p⁻¹, mul_mem (mul_mem hpC hxC) (inv_mem hpC)⟩ : ↥hePC) =
        ⟨p, hpC⟩ * ⟨x, hxC⟩ * (⟨p, hpC⟩ : ↥hePC)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hIN hpI) _).mp hxX
  have hPE := hpar (hES.trans hS₁C) hIEC hIEN hIE hsE
  have hPF := hpar (hFS.trans hS₁C) hIFC hIFN hIF hsF
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr rfl
  set nz := f.symm ⟨z, hzC⟩ with hnz
  have hfnz : f nz = ⟨z, hzC⟩ := f.apply_symm_apply _
  have hcent : ∀ y ∈ hePC, (nz : Equiv.Perm (Fin 32)) * y = y * nz := by
    intro y hy
    have h1 : f (nz * ⟨y, hy⟩) = f (⟨y, hy⟩ * nz) := by
      rw [map_mul, map_mul, hfnz]
      apply Subtype.ext
      simp only [coe_mul]
      exact (mem_centralizer_singleton_iff.mp (f ⟨y, hy⟩).2).symm
    exact congrArg Subtype.val (f.injective h1)
  have hnzc : (nz : Equiv.Perm (Fin 32)) = heTC := by
    rcases hM.center_PC nz nz.2 hcent with h | h
    · exfalso
      apply hz1
      have h1 : nz = 1 := Subtype.ext h
      have h2 := congrArg Subtype.val hfnz
      rw [h1, map_one] at h2
      exact h2.symm
    · exact h
  refine ⟨s, f, fun n => ?_, hB, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · rw [← hnzc]
    constructor
    · intro h
      rw [show n = nz from Subtype.ext h, hfnz]
    · intro h
      have h1 : f n = f nz := by rw [hfnz]; exact Subtype.ext h
      rw [f.injective h1]
  · rw [← hPE]
    exact hpre hIEC n
  · rw [← hPF]
    exact hpre hIFC n
  · rw [← hsE]
    exact hpre (hES.trans hS₁C) n
  · rw [← hsF]
    exact hpre (hFS.trans hS₁C) n

end CFSG.ComponentClassification.AS81.HeTri
