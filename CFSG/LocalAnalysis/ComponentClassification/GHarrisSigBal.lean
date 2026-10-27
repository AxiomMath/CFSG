module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigV

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_oddCore_of_normal {I K : Subgroup G} (hKI : K ≤ I)
    (hn : ∀ i ∈ I, ∀ k ∈ K, i * k * i⁻¹ ∈ K) (hK : Nat.Coprime 2 (Nat.card K)) :
    K ≤ (pPrimeCore 2 ↥I).map I.subtype := by
  have hnorm : (K.subgroupOf I).Normal :=
    ⟨fun k hk i => mem_subgroupOf.mpr (hn i i.2 k (mem_subgroupOf.mp hk))⟩
  have hcard : Nat.Coprime 2 (Nat.card (K.subgroupOf I)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKI).toEquiv]
  have hle : K.subgroupOf I ≤ pPrimeCore 2 ↥I := le_sSup ⟨hnorm, hcard⟩
  intro k hk
  exact ⟨⟨k, hKI hk⟩, hle (mem_subgroupOf.mpr hk), rfl⟩

theorem oddCent_inf_le {u b : G} (hu : u * u = 1) (hub : u * b = b * u)
    (hch : CharTwoCent (zpowers b)) :
    oddCent (zpowers u) ⊓ centralizer ((zpowers b : Subgroup G) : Set G) ≤ oddCent (zpowers b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cu := centralizer ((zpowers u : Subgroup G) : Set G)
  set Cb := centralizer ((zpowers b : Subgroup G) : Set G)
  have hPH : zpowers u ≤ Cb := by
    rw [zpowers_le, mem_centralizer_iff]
    intro c hc
    exact comm_of_mem_zpowers hub.symm hc
  have hP : IsPGroup 2 (zpowers u) := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, sq, Subgroup.coe_mul]
    rcases eq_one_or_of_mem_zpowers hu g.2 with h | h <;> rw [h]
    · rw [one_mul]; rfl
    · rw [hu]; rfl)⟩
  have key := pPrimeCore_common_centralizer_eq G 2 Cb (zpowers u) hPH hP hch
  set I : Subgroup G := Cb ⊓ centralizer ((zpowers u : Subgroup G) : Set G) with hI
  have hle : oddCent (zpowers u) ⊓ Cb ≤ (pPrimeCore 2 ↥I).map I.subtype := by
    refine le_oddCore_of_normal ?_ ?_ ?_
    · intro w hw
      exact mem_inf.mpr ⟨(mem_inf.mp hw).2, oddCent_le _ (mem_inf.mp hw).1⟩
    · intro i hi k hk
      obtain ⟨hkO, hkb⟩ := mem_inf.mp hk
      refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (mem_inf.mp hi).1 hkb) (inv_mem (mem_inf.mp hi).1)⟩
      exact (mem_normalizer_iff.mp (centralizer_le_normalizer_oddCent _ (mem_inf.mp hi).2) k).mp
        hkO
    · exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (card_oddCent _)
  intro w hw
  have h := hle hw
  rw [key] at h
  exact (mem_inf.mp h).1

theorem oddCent_le_sigW4_of_comm {u : G} (hu : u * u = 1) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB4 : 4 ≤ Nat.card B) (hBu : ∀ b ∈ B, u * b = b * u)
    (hch : ∀ b ∈ B, b ≠ 1 → CharTwoCent (zpowers b)) : oddCent (zpowers u) ≤ sigW4 B := by
  have hBN : B ≤ normalizer (oddCent (zpowers u) : Set G) := by
    intro b hb
    refine centralizer_le_normalizer_oddCent _ ?_
    rw [mem_centralizer_iff]
    intro c hc
    exact comm_of_mem_zpowers (hBu b hb) hc
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hB (by simpa using hB4) hBN (card_oddCent _)
  rw [← hgen]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
  have h := oddCent_inf_le hu (hBu b hb) (hch b hb hb1)
  have e : centralizer ((zpowers b : Subgroup G) : Set G) = centralizer ({b} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [e] at h
  exact h.trans (oddCent_le_sigW4 hb hb1)

namespace GHSylow

variable (D : GHSylow G)

theorem oddCent_le_W (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0)
    {u : G} (hu : u * u = 1) (huz : u * D.z = D.z * u) (hut : u * D.t = D.t * u) :
    oddCent (zpowers u) ≤ sigW D.V := by
  set B := klein D.z D.t D.t_mul_t D.z_comm_t with hBdef
  have hBV : B ≤ D.V := klein_le D.z_mem_V D.t_mem_V
  have hB4 : 4 ≤ Nat.card B := (card_klein D.z_mul_z D.z_ne_one D.t_ne_one D.z_ne_t.symm).ge
  rw [D.sigW_V_eq hC h10 h20 hBV hB4]
  refine oddCent_le_sigW4_of_comm hu (isElemAbelian_klein D.z_mul_z) hB4 (fun b hb => ?_)
    fun b hb hb1 => D.charTwoAt_V hC h10 h20 _ ⟨zpowers_le.mpr (hBV hb), ?_⟩
  · have hle : B ≤ centralizer ({u} : Set G) := klein_le
      (mem_centralizer_singleton_iff.mpr huz.symm) (mem_centralizer_singleton_iff.mpr hut.symm)
    exact (mem_centralizer_singleton_iff.mp (hle hb)).symm
  · rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ hb1
    have := (isElemAbelian_klein (hb := D.t_mul_t) (hab := D.z_comm_t) D.z_mul_z).2 b hb
    exact this

end GHSylow

end CFSG.ComponentClassification.GHarris
