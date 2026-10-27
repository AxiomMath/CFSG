module

public import CFSG.CGT.PushingUpLit.BHS.FourOneC
public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

namespace Hyp42

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem mem_setNormalizer_of_conjSub_le (h : Hyp42 P D T M) {y : MulAut V} (hy : y ∈ P)
    (hle : ∀ A ∈ dInter D T, conjSub y A ≤ T) : y ∈ setNormalizer P (dInter D T) := by
  have hsub : conjSub y '' dInter D T ⊆ dInter D T := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨h.conj_mem A hA.1 y hy, hle A hA⟩
  have h1 : dInter D T ⊆ conjSub y⁻¹ '' dInter D T := fun A hA =>
    ⟨conjSub y A, hsub ⟨A, hA, rfl⟩, FourTwoTools.conjSub_inv_conjSub y A⟩
  have heq := FourTwoTools.conjSub_image_eq_of_subset y⁻¹ h1
  refine ⟨hy, fun A => ⟨fun hA => hsub ⟨A, hA, rfl⟩, fun hA => ?_⟩⟩
  rw [← heq]
  exact ⟨conjSub y A, hA, FourTwoTools.conjSub_inv_conjSub y A⟩


theorem exists_mem_setNormalizer_conj_eq (h : Hyp42 P D T M) {U : Set (Subgroup (MulAut V))}
    (hU : U ⊆ dInter D T) {y : MulAut V} (hy : y ∈ P)
    (hyU : ∀ A ∈ U, conjSub y A ∈ dInter D T) :
    ∃ n ∈ setNormalizer P (dInter D T), ∀ A ∈ U, conjSub y A = conjSub n A := by
  set E : Subgroup (MulAut V) := ⨆ A ∈ dInter D T, A with hE
  set E₁ : Subgroup (MulAut V) := ⨆ A ∈ U, A with hE₁
  have hEab : IsElemAbelian2 E := h.toHyp41.four_seven_isElemAbelian2 h.syl
  have hET : E ≤ T := iSup₂_le fun A hA => hA.2
  have hEP : E ≤ P := hET.trans h.syl.1
  have hAE : ∀ A ∈ dInter D T, A ≤ E := fun A hA =>
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ dInter D T) => B) A hA le_rfl
  have hE₁E : E₁ ≤ E := iSup₂_le fun A hA => hAE A (hU hA)
  have hyE₁ : conjSub y E₁ ≤ E := by
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun A hA => ?_)
    exact Subgroup.map_le_iff_le_comap.1 (hAE _ (hyU A hA))
  set C : Subgroup (MulAut V) := P ⊓ Subgroup.centralizer (E₁ : Set (MulAut V)) with hC
  have hEC : E ≤ C := le_inf hEP fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hEab.1 x (hE₁E hx) e he
  have hE'P : conjSub y⁻¹ E ≤ P := Glauberman.map_conj_le (P.inv_mem hy) hEP
  have hE'C : conjSub y⁻¹ E ≤ C := le_inf hE'P fun e' he' => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have he'E : y * e' * y⁻¹ ∈ E := by
      have := mem_conjSub_iff.1 he'
      simpa using this
    have hxE : y * x * y⁻¹ ∈ E := hyE₁ (mem_conjSub_of_mem hx)
    have hcomm := hEab.1 _ hxE _ he'E
    calc x * e' = y⁻¹ * (y * x * y⁻¹ * (y * e' * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * e' * y⁻¹) * (y * x * y⁻¹)) * y := by rw [hcomm]
      _ = e' * x := by group
  have hE2 : IsPGroup 2 E := h.syl.2.1.to_le hET
  obtain ⟨S₁, hS₁, hES₁⟩ := Glauberman.exists_isSylowOf_ge hE2 hEC
  obtain ⟨c, hcC, hc⟩ := Glauberman.exists_conj_le_of_isSylowOf hS₁
    (isPGroup_conjSub hE2 y⁻¹) hE'C
  obtain ⟨t, htP, ht⟩ := FourTwoTools.exists_conjSub_ge h.syl hS₁.2.1 (hS₁.1.trans inf_le_left)
  have hcP : c ∈ P := hcC.1
  have htN : t ∈ setNormalizer P (dInter D T) := by
    have hle : ∀ A ∈ dInter D T, conjSub t⁻¹ A ≤ T := fun A hA => by
      have := conjSub_mono t⁻¹ ((hAE A hA).trans (hES₁.trans ht))
      rwa [FourTwoTools.conjSub_inv_conjSub] at this
    have := h.mem_setNormalizer_of_conjSub_le (P.inv_mem htP) hle
    simpa using Subgroup.inv_mem _ this
  have hn₀ : t⁻¹ * (c * y⁻¹) ∈ setNormalizer P (dInter D T) := by
    have hle : ∀ A ∈ dInter D T, conjSub (t⁻¹ * (c * y⁻¹)) A ≤ T := fun A hA => by
      have h1 : conjSub c (conjSub y⁻¹ E) ≤ conjSub t T := hc.trans ht
      have h2 := conjSub_mono t⁻¹ h1
      rw [FourTwoTools.conjSub_inv_conjSub, ← conjSub_mul, ← conjSub_mul] at h2
      exact (conjSub_mono _ (hAE A hA)).trans h2
    exact h.mem_setNormalizer_of_conjSub_le
      (P.mul_mem (P.inv_mem htP) (P.mul_mem hcP (P.inv_mem hy))) hle
  refine ⟨(t⁻¹ * (c * y⁻¹))⁻¹ * t⁻¹, Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₀)
    (Subgroup.inv_mem _ htN), fun A hA => ?_⟩
  have hcx : ∀ x ∈ A, c⁻¹ * x = x * c⁻¹ := fun x hx => by
    have hxE₁ : x ∈ E₁ :=
      le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ U) => B) A hA le_rfl hx
    have := Subgroup.mem_centralizer_iff.1 hcC.2 x hxE₁
    exact (Commute.inv_left (show Commute c x from this.symm)).eq
  have hn : (t⁻¹ * (c * y⁻¹))⁻¹ * t⁻¹ = y * c⁻¹ := by group
  rw [hn, conjSub_mul, FourOneTools.conjSub_eq_of_comm hcx]


omit [Finite V] in
theorem mem_setNormalizer_of_conjSub_eq (h : Hyp42 P D T M) {n : MulAut V} (hnP : n ∈ P)
    (hn : conjSub n T = T) : n ∈ setNormalizer P (dInter D T) := by
  refine ⟨hnP, fun A => ⟨fun hA => ⟨h.conj_mem A hA.1 n hnP, ?_⟩, fun hA => ⟨?_, ?_⟩⟩⟩
  · exact (conjSub_mono n hA.2).trans hn.le
  · have := h.conj_mem _ hA.1 n⁻¹ (P.inv_mem hnP)
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  · have h1 := conjSub_mono n⁻¹ hA.2
    have h2 : conjSub n⁻¹ T = T := by
      conv_lhs => rw [← hn]
      exact FourTwoTools.conjSub_inv_conjSub n T
    rwa [FourTwoTools.conjSub_inv_conjSub, h2] at h1

theorem mem_of_conjSub_eq (h : Hyp42 P D T M) {g : MulAut V} (hg : g ∈ P)
    (hgM : conjSub g M = M) : g ∈ M := by
  have hTM : IsSylowOf 2 T M := isSylowOf_of_le_of_le h.syl h.le_M h.M_le
  have hT'M : conjSub g T ≤ M := by
    have := conjSub_mono g h.le_M
    rwa [hgM] at this
  obtain ⟨k, hkM, hk⟩ := Glauberman.exists_conj_le_of_isSylowOf hTM
    (isPGroup_conjSub h.syl.2.1 g) hT'M
  have hk' : conjSub (k * g) T ≤ T := by
    rw [conjSub_mul]
    exact hk
  have heq : conjSub (k * g) T = T := conjSub_eq_of_conjSub_le hk'
  have := h.normSet_le (h.mem_setNormalizer_of_conjSub_eq (P.mul_mem (h.M_le hkM) hg) heq)
  have h2 := M.mul_mem (M.inv_mem hkM) this
  simpa using h2

theorem conjSub_eq_of_le_conjSub (h : Hyp42 P D T M) {U : Set (Subgroup (MulAut V))}
    (hU : U ⊆ dInter D T) (hN : setNormalizer P U ≤ M) {g : MulAut V} (hg : g ∈ P)
    (hAg : ∀ A ∈ U, A ≤ conjSub g M) : conjSub g M = M := by
  have hTM : IsSylowOf 2 T M := isSylowOf_of_le_of_le h.syl h.le_M h.M_le
  set E : Subgroup (MulAut V) := ⨆ A ∈ U, A with hE
  have hAE : ∀ A ∈ U, A ≤ E := fun A hA =>
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ U) => B) A hA le_rfl
  have hgA : ∀ A ∈ U, conjSub g⁻¹ A ≤ M := fun A hA => by
    have := conjSub_mono g⁻¹ (hAg A hA)
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  have hEg : conjSub g⁻¹ E ≤ M := by
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun A hA => ?_)
    exact Subgroup.map_le_iff_le_comap.1 (hgA A hA)
  have hE2 : IsPGroup 2 E := h.syl.2.1.to_le (iSup₂_le fun A hA => (hU hA).2)
  obtain ⟨m, hmM, hm⟩ := FourTwoTools.exists_conjSub_ge hTM (isPGroup_conjSub hE2 g⁻¹) hEg
  have hyP : m⁻¹ * g⁻¹ ∈ P := P.mul_mem (P.inv_mem (h.M_le hmM)) (P.inv_mem hg)
  have hyU : ∀ A ∈ U, conjSub (m⁻¹ * g⁻¹) A ∈ dInter D T := fun A hA => by
    refine ⟨h.conj_mem A (hU hA).1 _ hyP, ?_⟩
    have h1 := conjSub_mono m⁻¹ ((conjSub_mono g⁻¹ (hAE A hA)).trans hm)
    rw [FourTwoTools.conjSub_inv_conjSub] at h1
    rwa [conjSub_mul]
  obtain ⟨n, hn, hnU⟩ := h.exists_mem_setNormalizer_conj_eq hU hyP hyU
  have hzP : n⁻¹ * (m⁻¹ * g⁻¹) ∈ P := P.mul_mem (P.inv_mem hn.1) hyP
  have hz : n⁻¹ * (m⁻¹ * g⁻¹) ∈ setNormalizer P U := by
    have hfix : ∀ A ∈ U, conjSub (n⁻¹ * (m⁻¹ * g⁻¹)) A = A := fun A hA => by
      rw [conjSub_mul, hnU A hA, FourTwoTools.conjSub_inv_conjSub]
    refine ⟨hzP, fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩
    · rwa [hfix A hA]
    · have h1 : conjSub (n⁻¹ * (m⁻¹ * g⁻¹)) (conjSub (n⁻¹ * (m⁻¹ * g⁻¹)) A) =
          conjSub (n⁻¹ * (m⁻¹ * g⁻¹)) A := hfix _ hA
      have h2 := (conjSub_inj _).1 h1
      rw [← h2]
      exact hA
  have hzM : n⁻¹ * (m⁻¹ * g⁻¹) ∈ M := hN hz
  have hnM : n ∈ M := h.normSet_le hn
  have hgM : g ∈ M := by
    have h1 : m⁻¹ * g⁻¹ ∈ M := by
      have := M.mul_mem hnM hzM
      simpa using this
    have h2 : g⁻¹ ∈ M := by
      have := M.mul_mem hmM h1
      simpa using this
    simpa using M.inv_mem h2
  exact conjSub_self_of_mem hgM

end Hyp42

end CFSG.CGT.PushingUpLit.BHS
