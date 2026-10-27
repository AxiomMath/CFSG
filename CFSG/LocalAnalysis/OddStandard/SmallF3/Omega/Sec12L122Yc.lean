module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec122_L_le_cent (F : Sec12Frame t L S) : L ≤ centralizer ({t} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hht : h = t := by simpa using hh
  subst hht
  exact ((Subgroup.mem_centralizer_iff.mp F.htC) y hy).symm

theorem sec122_S_le_normalizer_L (F : Sec12Frame t L S)
    (hSc : S ≤ centralizer ({t} : Set G)) : S ≤ normalizer (L : Set G) := by
  intro s hs
  exact F.hCt (hSc hs)

theorem sec122_Yc_le_cent (F : Sec12Frame t L S) (hSc : S ≤ centralizer ({t} : Set G)) :
    (secM t S L ⊓ L) ⊔ S ≤ centralizer ({t} : Set G) := by
  exact sup_le (inf_le_right.trans (sec122_L_le_cent F)) hSc

theorem sec122_Yc_le_M (F : Sec12Frame t L S) : (secM t S L ⊓ L) ⊔ S ≤ secM t S L := by
  exact sup_le inf_le_left F.hSM

theorem sec122_Yc_le_normalizer_L (F : Sec12Frame t L S)
    (hSc : S ≤ centralizer ({t} : Set G)) :
    (secM t S L ⊓ L) ⊔ S ≤ normalizer (L : Set G) := by
  exact sup_le (inf_le_right.trans Subgroup.le_normalizer)
    (sec122_S_le_normalizer_L F hSc)

theorem sec122_M_le_normalizer_B (F : Sec12Frame t L S) :
    secM t S L ≤ normalizer (secB S L : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact F.normB m hm b hb
  · intro hb
    have h := F.normB m⁻¹ ((secM t S L).inv_mem hm) (m * b * m⁻¹) hb
    rwa [show m⁻¹ * (m * b * m⁻¹) * (m⁻¹)⁻¹ = b from by group] at h

theorem sec122_Yc_le_normalizer_B (F : Sec12Frame t L S) :
    (secM t S L ⊓ L) ⊔ S ≤ normalizer (secB S L : Set G) := by
  exact sup_le (inf_le_left.trans (sec122_M_le_normalizer_B F))
    (F.hSM.trans (sec122_M_le_normalizer_B F))

private theorem sec122_S_le_normalizer_inf (F : Sec12Frame t L S)
    (hSc : S ≤ centralizer ({t} : Set G)) :
    S ≤ normalizer (((secM t S L) ⊓ L : Subgroup G) : Set G) := by
  intro s hs
  have hM : s ∈ normalizer (secM t S L) := Subgroup.le_normalizer (F.hSM hs)
  have hL : s ∈ normalizer (L : Set G) := sec122_S_le_normalizer_L F hSc hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxM, hxL⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hM x).mp hxM,
       (Subgroup.mem_normalizer_iff.mp hL x).mp hxL⟩
  · intro hx
    obtain ⟨hxM, hxL⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hM x).mpr hxM,
       (Subgroup.mem_normalizer_iff.mp hL x).mpr hxL⟩

theorem sec122_Yc_le_normalizer_Y (F : Sec12Frame t L S)
    (hSc : S ≤ centralizer ({t} : Set G)) :
    (secM t S L ⊓ L) ⊔ S ≤ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) := by
  exact sup_le Subgroup.le_normalizer (sec122_S_le_normalizer_inf F hSc)

theorem sec122_A_le_Yc (htS : t ∈ S) : secA t S L ≤ (secM t S L ⊓ L) ⊔ S := by
  exact sup_le ((secB_le_S S L).trans le_sup_right)
    ((Subgroup.zpowers_le.mpr htS).trans le_sup_right)

theorem sec122_centralizer_inf_S (F : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (htS : t ∈ S) :
    centralizer (L : Set G) ⊓ S = zpowers t := by
  refine le_antisymm ?_ ?_
  · intro c hc
    obtain ⟨hcL, hcS⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨k, hk⟩ := hS.2.1 ⟨c, hcS⟩
    refine F.two c hcL (hS.1 hcS) ⟨k, ?_⟩
    simpa using congrArg Subtype.val hk
  · exact le_inf (Subgroup.zpowers_le.mpr F.htC) (Subgroup.zpowers_le.mpr htS)

private theorem sec122_B_le_centralizer_cent :
    secB S L ≤ centralizer (centralizer (L : Set G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact ((Subgroup.mem_centralizer_iff.mp hc) b (secB_le_L S L hb)).symm

private theorem sec122_B_le_normalizer_cent :
    secB S L ≤ normalizer (centralizer (L : Set G) : Set G) :=
  (sec122_B_le_centralizer_cent).trans
    (Subgroup.centralizer_le_normalizer (centralizer (L : Set G) : Set G))

theorem sec122_Yc_inf_centralizer (F : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) {c : G}
    (hc : c ∈ (secM t S L ⊓ L) ⊔ S) (hcL : c ∈ centralizer (L : Set G)) : c ∈ zpowers t := by
  have hSY : S ≤ normalizer (((secM t S L) ⊓ L : Subgroup G) : Set G) :=
    sec122_S_le_normalizer_inf F hS.1
  have hc' : c ∈ (((secM t S L) ⊓ L : Subgroup G) : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (secM t S L ⊓ L) S hSY]
    exact hc
  obtain ⟨y, hy, s, hs, hc_eq⟩ := Set.mem_mul.mp hc'
  obtain ⟨k, hsk⟩ := hS.2.1 ⟨s, hs⟩
  have hsk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hsk
  have hct : c ∈ centralizer ({t} : Set G) := sec122_Yc_le_cent F hS.1 hc
  have hcpowC : c ^ 2 ^ k ∈ centralizer (L : Set G) :=
    (centralizer (L : Set G)).pow_mem hcL _
  have hclaim : ∀ n, ∃ y' ∈ secM t S L ⊓ L, (y * s) ^ n = y' * s ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, (secM t S L ⊓ L).one_mem, by simp⟩
    | succ n ih =>
        obtain ⟨y', hy', hpow⟩ := ih
        refine ⟨y' * (s ^ n * y * (s ^ n)⁻¹), (secM t S L ⊓ L).mul_mem hy' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hSY (S.pow_mem hs n)) y).mp hy
        · rw [pow_succ, hpow]
          group
  obtain ⟨y', hy'Y, hy'eq⟩ := hclaim (2 ^ k)
  have hy'L : y' ∈ L := hy'Y.2
  have hy'C : y' ∈ centralizer (L : Set G) := by
    have h := hcpowC
    rw [← hc_eq, hy'eq, hsk', mul_one] at h
    exact h
  have hy'bot : y' ∈ (⊥ : Subgroup G) := by
    rw [← F.hLC]
    exact ⟨hy'L, hy'C⟩
  have hy'1 : y' = 1 := by simpa using hy'bot
  exact F.two c hcL hct ⟨k, by rw [← hc_eq, hy'eq, hsk', mul_one, hy'1]⟩

theorem sec122_ker (F : Sec12Frame t L S) (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (htS : t ∈ S) {X : Subgroup G} (hXYc : X ≤ (secM t S L ⊓ L) ⊔ S)
    (hXA : X ⊓ secA t S L = ⊥) {x : G} (hx : x ∈ X)
    (hcent : ∀ b ∈ secB S L, x * b = b * x) : x = 1 := by
  have hxYc : x ∈ (secM t S L ⊓ L) ⊔ S := hXYc hx
  have hxNL : x ∈ normalizer (L : Set G) := sec122_Yc_le_normalizer_L F hS.1 hxYc
  have hx' : x ∈ (secB S L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (secB S L) (centralizer (L : Set G))
      sec122_B_le_normalizer_cent]
    exact F.centB x hxNL hcent
  obtain ⟨b, hbB, cc, hcc, hbc_eq⟩ := Set.mem_mul.mp hx'
  have hbYc : b ∈ (secM t S L ⊓ L) ⊔ S :=
    Subgroup.mem_sup_right (secB_le_S S L hbB)
  have hcc_eq : cc = b⁻¹ * x := by rw [← hbc_eq]; group
  have hcYc : cc ∈ (secM t S L ⊓ L) ⊔ S := by
    rw [hcc_eq]
    exact ((secM t S L ⊓ L) ⊔ S).mul_mem (((secM t S L ⊓ L) ⊔ S).inv_mem hbYc) hxYc
  have hct : cc ∈ zpowers t := sec122_Yc_inf_centralizer F hS hcYc hcc
  have hbA : b ∈ secA t S L := Subgroup.mem_sup_left (T := zpowers t) hbB
  have hcA : cc ∈ secA t S L := Subgroup.mem_sup_right hct
  have hxA : x ∈ secA t S L := by rw [← hbc_eq]; exact (secA t S L).mul_mem hbA hcA
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hXA]
    exact ⟨hx, hxA⟩
  simpa using hxbot

theorem sec122_surj (F : Sec12Frame t L S) {X : Subgroup G}
    (hXsup : X ⊔ secA t S L = (secM t S L ⊓ L) ⊔ S) {φ : (Fin 5 → ZMod 2) → G}
    {y : G} (hy : y ∈ secM t S L ⊓ L) {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v))
    (hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L) :
    ∃ x ∈ X, ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) := by
  have hyYc : y ∈ (secM t S L ⊓ L) ⊔ S := Subgroup.mem_sup_left hy
  have hXYc : X ≤ (secM t S L ⊓ L) ⊔ S := by rw [← hXsup]; exact le_sup_left
  have hXM : X ≤ secM t S L := hXYc.trans (sec122_Yc_le_M F)
  have hyXA : y ∈ X ⊔ secA t S L := by rw [hXsup]; exact hyYc
  have hy' : y ∈ (X : Set G) * (secA t S L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X (secA t S L) hXM]
    exact hyXA
  obtain ⟨x, hxX, a, haA, hxa_eq⟩ := Set.mem_mul.mp hy'
  refine ⟨x, hxX, ?_⟩
  intro v hv
  have hcomm : a⁻¹ * φ v * a = φ v := by
    have hAB : a * φ v = φ v * a :=
      sec12E_A_comm F haA (Subgroup.mem_sup_left (T := zpowers t) (hφB v hv))
    rw [show a⁻¹ * φ v * a = a⁻¹ * (φ v * a) by group, ← hAB]
    group
  have hx_eq : x = y * a⁻¹ := by rw [← hxa_eq]; group
  rw [hx_eq]
  calc (y * a⁻¹) * φ v * (y * a⁻¹)⁻¹
      = y * (a⁻¹ * φ v * a) * y⁻¹ := by group
    _ = y * φ v * y⁻¹ := by rw [hcomm]
    _ = φ (permVec σ v) := hσ v hv

end CFSG.OddStandard.SmallF3.Omega
