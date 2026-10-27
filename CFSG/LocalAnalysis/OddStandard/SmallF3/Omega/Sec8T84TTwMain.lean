module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TTwTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TTwModel

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

private theorem sec8t84tw_mem_sup {P B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ P) (h₂ : B₂ ≤ P)
    (hN : (B₁.subgroupOf P).Normal) {l : G} (hl : l ∈ B₁ ⊔ B₂) :
    ∃ b₁ ∈ B₁, ∃ b₂ ∈ B₂, l = b₁ * b₂ := by
  have hle : B₂ ≤ Subgroup.normalizer (B₁ : Set G) :=
    h₂.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h₁).mp hN)
  have hl' : l ∈ ((B₁ ⊔ B₂ : Subgroup G) : Set G) := hl
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B₁ B₂ hle] at hl'
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hl'
  exact ⟨b₁, hb₁, b₂, hb₂, rfl⟩

theorem sec8t84tw_main {hQ : Q.Nondegenerate} (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (hφ : OddCentralCover (ff6mPhi e)) {fr : NFrame Q (Fin 6) 1} {P B₁ B₂ : Subgroup G}
    (hPL : P ≤ L) (hP2 : IsPGroup 2 P) (hB₁ : IsNormalE16In P B₁) (hB₂ : IsNormalE16In P B₂)
    (hne : B₁ ≠ B₂) (hB₁fr : ffImg (ff6mPhi e) B₁ = ffB1 hQ fr)
    (hPfr : ffImg (ff6mPhi e) P = ffP1 hQ fr) {γ : G}
    (hγP : γ ∈ Subgroup.normalizer (P : Set G)) (hγγ : γ * γ = 1) {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e γ x) (hxx : x * x = 1) (hxG : ¬ SimInGStar x) :
    ∃ r ∈ P, (γ * r) * (γ * r) = 1 ∧
      (∃ y : ProjSim Q, InducesViaP L (Subgroup.center ↥L) hQ e (γ * r) y ∧ y * y = 1 ∧
        ¬ SimInGStar y) ∧
      Nat.card ↥((B₁ ⊔ B₂) ⊓ Subgroup.centralizer ({γ * r} : Set G)) = 4 ∧
      IsElemAb2 ((B₁ ⊔ B₂) ⊓ Subgroup.centralizer ({γ * r} : Set G)) 2 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  have hxN := sec8t84tw_mem_normalizer h2 hPL hPfr hγP hs
  obtain ⟨y, hy, hyP⟩ : ∃ y : ProjSim Q,
      (y = ffX0 fr ∨ y = ffX0 fr * ffM fr ffRhoPerm ffRhoSet) ∧ y⁻¹ * x ∈ ffPS hQ fr := by
    rcases sec8t84tw_coset hQ hdim hsgn fr hxN hxG hxx with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hrPS : x⁻¹ * y ∈ ffPS hQ fr := by
    have h := (ffPS hQ fr).inv_mem hyP
    rwa [mul_inv_rev, inv_inv] at h
  obtain ⟨r, hrP, hrφ⟩ := (sec8t84tw_mem_map_iff hPfr).mp hrPS
  obtain ⟨hyy, hyG⟩ := sec8t84tw_y_inv fr hy
  have hxr : x * ffOmegaToSim hQ (ff6mPhi e r) = y := by rw [hrφ]; group
  have hind : InducesViaP L (Subgroup.center ↥L) hQ e (γ * (r : G)) y := by
    have h := inducesViaP_mul hs (inducesViaP_of_mem e r)
    rw [← hxr]
    exact h
  have hgP : γ * (r : G) ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).mul_mem hγP (Subgroup.le_normalizer hrP)
  have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγγ
  have hconj : γ * (r : G) * γ⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hγP (r : G)).mp hrP
  have hsqP : γ * (r : G) * (γ * (r : G)) ∈ P := by
    have h : γ * (r : G) * (γ * (r : G)) = (γ * (r : G) * γ⁻¹) * (r : G) := by
      rw [hγinv]; group
    rw [h]
    exact P.mul_mem hconj hrP
  have hsq1 : γ * (r : G) * (γ * (r : G)) = 1 := by
    let m : ↥L := ⟨γ * (r : G) * (γ * (r : G)), hPL hsqP⟩
    have hm1 : InducesViaP L (Subgroup.center ↥L) hQ e (m : G) (y * y) :=
      inducesViaP_mul hind hind
    have hm2 := inducesViaP_of_mem e m
    have hu : (1 : ProjSim Q) = ffOmegaToSim hQ (ff6mPhi e m) := by
      rw [← hyy]
      exact ff_induces_unique hQ h5 e hm1 hm2
    have hφ1 : ff6mPhi e m = ff6mPhi e 1 := by
      apply ffOmegaToSim_injective hQ
      simp only [map_one]
      exact hu.symm
    have heq : m = 1 := ff_cover_eq_of_pGroup hφ hP2 (l := m) (l' := 1) hsqP P.one_mem hφ1
    have h := congrArg Subtype.val heq
    exact h
  have hB₂L : B₂ ≤ L := hB₂.1.trans hPL
  have hU₂ : ffImg (ff6mPhi e) B₂ ≤ ffP1 hQ fr := by
    rw [← hPfr]
    exact ffImg_mono hB₂.1
  have hE₂ : IsElemAb2 (ffImg (ff6mPhi e) B₂) 4 :=
    (ff_cover_elemAb2_iff hφ hB₂L (hP2.to_le hB₂.1) 4).mp hB₂.2.1
  have hne₂ : ffImg (ff6mPhi e) B₂ ≠ ffB1 hQ fr := by
    intro h
    exact hne (ff_cover_img_injective hφ hPL hP2 hB₁.1 hB₂.1 (hB₁fr.trans h.symm))
  have hshape := sec8t84tw_E16_shape hQ hdim hsgn fr hU₂ hE₂ hne₂
  have hBS : ∀ z : ProjSim Q, z ∈ ffBS hQ fr ↔
      ∃ l : ↥L, (l : G) ∈ B₁ ∧ ffOmegaToSim hQ (ff6mPhi e l) = z :=
    fun z => sec8t84tw_mem_map_iff hB₁fr
  have hshapeJ : ∀ l : ↥L, (l : G) ∈ B₁ ⊔ B₂ →
      ∃ σ ∈ ffK0, ∃ K : Finset (Fin 6), ffOmegaToSim hQ (ff6mPhi e l) = ffM fr σ K := by
    intro l hl
    obtain ⟨b₁, hb₁, b₂, hb₂, hlb⟩ := sec8t84tw_mem_sup hB₁.1 hB₂.1 hB₁.2.2 hl
    let l₁ : ↥L := ⟨b₁, hPL (hB₁.1 hb₁)⟩
    let l₂ : ↥L := ⟨b₂, hPL (hB₂.1 hb₂)⟩
    have hll : l = l₁ * l₂ := Subtype.ext hlb
    have h1 : ffOmegaToSim hQ (ff6mPhi e l₁) ∈ ffBS hQ fr := (hBS _).mpr ⟨l₁, hb₁, rfl⟩
    obtain ⟨K, -, hK⟩ := (mem_ffBS_iff hQ fr).mp h1
    have h2' : ff6mPhi e l₂ ∈ ffImg (ff6mPhi e) B₂ := mem_ffImg_iff.mpr ⟨l₂, hb₂, rfl⟩
    obtain ⟨σ, hσ, J, -, hJ⟩ := hshape _ h2'
    refine ⟨σ, hσ, symmDiff (K.map σ⁻¹.toEmbedding) J, ?_⟩
    rw [hll, map_mul, map_mul, hK, hJ, ffM_mul, one_mul]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥L →* ProjSim Q, ∀ l, ψ l = ffOmegaToSim hQ (ff6mPhi e l) :=
    ⟨(ffOmegaToSim hQ).comp (ff6mPhi e), fun l => rfl⟩
  have hinj : ∀ a b : ↥L, (a : G) ∈ P → (b : G) ∈ P → ψ a = ψ b → a = b := by
    intro a b ha hb hab
    rw [hψ, hψ] at hab
    exact ff_cover_eq_of_pGroup hφ hP2 ha hb (ffOmegaToSim_injective hQ hab)
  have hCP : (B₁ ⊔ B₂) ⊓ Subgroup.centralizer ({γ * (r : G)} : Set G) ≤ P :=
    inf_le_left.trans (sup_le hB₁.1 hB₂.1)
  have hK0 : (1 : Equiv.Perm (Fin 6)) ∈ ffK0 := by decide
  have hT : ∀ l : ↥L, (l : G) ∈ P →
      ((l : G) ∈ (B₁ ⊔ B₂) ⊓ Subgroup.centralizer ({γ * (r : G)} : Set G) ↔
        ψ l ∈ {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J}) := by
    intro l hlP
    have hcent := sec8t84tw_cent_model h2 hφ hPL hP2 hind hgP l hlP
    rw [Subgroup.mem_inf, hcent, hψ]
    constructor
    · rintro ⟨hlJ, hlc⟩
      obtain ⟨σ, hσ, K, hK⟩ := hshapeJ l hlJ
      rw [hK] at hlc ⊢
      obtain ⟨hσ1, hKF⟩ := (sec8t84tw_cent_iff fr hy hσ K).mp hlc
      subst hσ1
      exact ⟨K, hKF, rfl⟩
    · rintro ⟨J, hJ, hl⟩
      refine ⟨?_, ?_⟩
      · have hmem : ffOmegaToSim hQ (ff6mPhi e l) ∈ ffBS hQ fr :=
          (mem_ffBS_iff hQ fr).mpr ⟨J, sec8t84tw_F0_even J hJ, hl⟩
        obtain ⟨l', hl'B, hl'⟩ := (hBS _).mp hmem
        have hll' : l' = l :=
          ff_cover_eq_of_pGroup hφ hP2 (hB₁.1 hl'B) hlP (ffOmegaToSim_injective hQ hl')
        have hlB : (l : G) ∈ B₁ := by rw [← hll']; exact hl'B
        exact Subgroup.mem_sup_left hlB
      · rw [hl]
        exact (sec8t84tw_cent_iff fr hy hK0 J).mpr ⟨rfl, hJ⟩
  have hsurj : ∀ z ∈ {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J},
      ∃ l : ↥L, (l : G) ∈ P ∧ ψ l = z := by
    rintro z ⟨J, hJ, rfl⟩
    obtain ⟨l, hlB, hl⟩ := (hBS _).mp
      ((mem_ffBS_iff hQ fr).mpr ⟨J, sec8t84tw_F0_even J hJ, rfl⟩)
    exact ⟨l, hB₁.1 hlB, by rw [hψ]; exact hl⟩
  have hcomm : ∀ a ∈ {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J},
      ∀ b ∈ {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J}, a * b = b * a := by
    rintro _ ⟨J, -, rfl⟩ _ ⟨K, -, rfl⟩
    exact sec8t84tw_signChange_comm fr J K
  have hsq : ∀ a ∈ {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J}, a * a = 1 := by
    rintro _ ⟨J, -, rfl⟩
    exact sec8t84tw_signChange_sq fr J
  obtain ⟨hcard, hel⟩ := sec8t84tw_transfer ψ hPL hCP hinj hT hsurj hcomm hsq
  have hcard4 := hcard.trans (sec8t84tw_T4_card fr)
  refine ⟨(r : G), hrP, hsq1, ⟨y, hind, hyy, hyG⟩, hcard4, hel, ?_⟩
  rw [hcard4]
  norm_num

end CFSG.OddStandard.SmallF3.Omega
