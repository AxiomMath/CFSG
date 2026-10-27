module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NBt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NPure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec12N_not_mem_range {Γ : Type} [Group Γ] {φ : Sec12SL × Sec12SL →* Γ}
    (hinj : Function.Injective φ) {y : Γ} (hy2 : y * y = 1)
    (hcent : Nat.card (Subgroup.centralizer ({y} : Set Γ)) = 120) :
    y ∉ MonoidHom.range φ := by
  rintro ⟨⟨A, B⟩, rfl⟩
  have hAB : (A * A, B * B) = (1 : Sec12SL × Sec12SL) := by
    apply hinj
    show φ ((A, B) * (A, B)) = φ 1
    rw [map_mul, map_one]
    exact hy2
  have hA : A * A = 1 := congrArg Prod.fst hAB
  have hB : B * B = 1 := congrArg Prod.snd hAB
  let K : Subgroup (Sec12SL × Sec12SL) :=
    (Subgroup.centralizer ({A} : Set Sec12SL)).prod (Subgroup.centralizer ({B} : Set Sec12SL))
  have hKcard : Nat.card K = Nat.card (Subgroup.centralizer ({A} : Set Sec12SL)) *
      Nat.card (Subgroup.centralizer ({B} : Set Sec12SL)) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have hKle : K.map φ ≤ Subgroup.centralizer ({φ (A, B)} : Set Γ) := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have ha' : A * a = a * A := Subgroup.mem_centralizer_iff.mp ha A rfl
    have hb' : B * b = b * B := Subgroup.mem_centralizer_iff.mp hb B rfl
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Prod.ext ha' hb')
  have hdvd : Nat.card K ∣ 120 := by
    rw [← hcent, ← Subgroup.card_map_of_injective (K := K) hinj]
    exact Subgroup.card_dvd_of_le hKle
  rw [hKcard] at hdvd
  rcases sec12F4_cent_card A hA with h1 | h1 <;> rcases sec12F4_cent_card B hB with h2 | h2 <;>
    rw [h1, h2] at hdvd <;> revert hdvd <;> decide

theorem sec12N_alt2 [Finite G] {V : Subgroup G} (hΩ : Sec128Alt2 V) {t : G} (htN : t ∈ secN V)
    (ht2 : t * t = 1)
    (hcent : Nat.card ↥(secNb V ⊓ Subgroup.centralizer ({betaOf V t} : Set (MulAut ↥V))) = 120) :
    ∃ N0 : Subgroup G, N0 ≤ secN V ∧ (N0.subgroupOf (secN V)).Normal ∧
      N0.relIndex (secN V) = 2 ∧ t ∉ N0 := by
  obtain ⟨φ, hS, hE, hidx⟩ := sec12J_alt2_data hΩ
  haveI : (MonoidHom.range φ).Normal := hE
  set β : ↥(secN V) →* ↥(secNb V) := sec12J_beta V with hβ
  have hbsurj : Function.Surjective β := by
    intro x
    obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp x.2
    exact ⟨a, Subtype.ext ha⟩
  have hy2 : β ⟨t, htN⟩ * β ⟨t, htN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htN⟩ : ↥(secN V)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hnot : β ⟨t, htN⟩ ∉ MonoidHom.range φ :=
    sec12N_not_mem_range hS.inj hy2 (sec12N_cent_card htN hcent)
  obtain ⟨H0, hH0n, hH0idx, hH0y⟩ := sec12N_index_two hidx hy2 hnot
  haveI := hH0n
  exact sec12N_of_hom β hbsurj hH0idx htN hH0y

end CFSG.OddStandard.SmallF3.Omega
