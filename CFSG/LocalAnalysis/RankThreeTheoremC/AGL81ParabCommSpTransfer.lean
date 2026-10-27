module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped commutatorElement

namespace SpCover

variable {A : Type} [Group A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
  (C : SpCover Y P r K I)

@[expose] noncomputable def autHom :
    ↥(Subgroup.normalizer (Y : Set A)) →* MulAut (StatedSp r K) :=
  (MulAut.congr C.ρ).symm.toMonoidHom.comp Y.normalizerMonoidHom

theorem coe_ρ_autHom (b : ↥(Subgroup.normalizer (Y : Set A))) (g : StatedSp r K) :
    ((C.ρ (C.autHom b g) : ↥Y) : A) = (b : A) * ((C.ρ g : ↥Y) : A) * (b : A)⁻¹ := by
  have h : C.ρ (C.autHom b g) = Y.normalizerMonoidHom b (C.ρ g) := by
    simp [autHom, MulAut.congr_symm_apply]
  rw [h, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem autHom_pow_eq_one (b : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ}
    (hb : (b : A) ^ p ^ k = 1) : C.autHom b ^ p ^ k = 1 := by
  have h : b ^ p ^ k = 1 := Subtype.ext (by simpa using hb)
  rw [← map_pow, h, map_one]

theorem odd_orderOf_autHom (b : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ} (hp : Odd p)
    (hb : (b : A) ^ p ^ k = 1) : Odd (orderOf (C.autHom b)) :=
  (hp.pow (n := k)).of_dvd_nat (orderOf_dvd_of_pow_eq_one (C.autHom_pow_eq_one b hb))

theorem centralizes_of_autHom_eq_one (c : ↥(Subgroup.normalizer (Y : Set A)))
    (h : C.autHom c = 1) : ∀ y ∈ Y, (c : A) * y = y * c := by
  intro y hy
  obtain ⟨g, hg⟩ := C.ρ.surjective ⟨y, hy⟩
  have h1 := C.coe_ρ_autHom c g
  rw [h, MulAut.one_apply, hg] at h1
  have h2 : (y : A) = (c : A) * y * (c : A)⁻¹ := h1
  calc (c : A) * y = (c : A) * y * (c : A)⁻¹ * c := by group
    _ = y * c := by rw [← h2]

theorem autHom_mem_flagStabilizer (b : ↥(Subgroup.normalizer (Y : Set A)))
    (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A)) {x : StatedSp r K}
    (hx : x ∈ flagStabilizer r K I) : C.autHom b x ∈ flagStabilizer r K I := by
  rw [C.mem_flag_iff, C.coe_ρ_autHom]
  exact (Subgroup.mem_normalizer_iff.mp hbP _).mp ((C.mem_flag_iff x).mp hx)

variable [Finite A] [Finite K] [CharP K 2]

theorem exists_radical (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) (hPY : P ≤ Y) (b : ↥(Subgroup.normalizer (Y : Set A)))
    (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A)) (hW : WCent P (b : A))
    (x : flagStabilizer r K I) (hx : C.toHat x ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P)) :
    ∃ u : flagStabilizer r K I, spFlagLeviHom (fun i hi => (hI i hi).2) htI u = 1 ∧
      (u : StatedSp r K) = C.autHom b (x : StatedSp r K) * (x : StatedSp r K)⁻¹ := by
  have hxP : ((C.ρ (x : StatedSp r K) : ↥Y) : A) ∈ P := (C.mem_flag_iff _).mp x.2
  have hW' := hW _ hxP hx
  obtain ⟨z, hz, hzeq⟩ := hW'
  have hux : C.autHom b (x : StatedSp r K) ∈ flagStabilizer r K I :=
    C.autHom_mem_flagStabilizer b hbP x.2
  refine ⟨⟨_, mul_mem hux (inv_mem x.2)⟩, ?_, rfl⟩
  have e1 : ((C.ρ ((C.autHom b) (x : StatedSp r K) * (x : StatedSp r K)⁻¹) : ↥Y) : A) =
      (b : A) * ((C.ρ (x : StatedSp r K) : ↥Y) : A) * (b : A)⁻¹ *
        ((C.ρ (x : StatedSp r K) : ↥Y) : A)⁻¹ := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, C.coe_ρ_autHom]
  have htoP : C.toP ⟨_, mul_mem hux (inv_mem x.2)⟩ = z := by
    apply Subtype.ext
    rw [coe_toP]
    exact e1.trans hzeq.symm
  have hker : (⟨_, mul_mem hux (inv_mem x.2)⟩ : flagStabilizer r K I) ∈ C.toHat.ker := by
    rw [C.ker_toHat_eq, Subgroup.mem_comap, htoP]
    exact hz
  rw [C.ker_toHat hI htI hmax hPY] at hker
  exact hker

theorem spNormFix_autHom (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) (hPY : P ≤ Y)
    (b : ↥(Subgroup.normalizer (Y : Set A))) (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A))
    (hW : WCent P (b : A)) : SpNormFix (fun i hi => (hI i hi).2) htI (C.autHom b) := by
  refine ⟨fun x hx => C.autHom_mem_flagStabilizer b hbP hx, fun b' hb' s => ?_, fun c hc => ?_⟩
  · have hmem := toHat_cutLevi_mem_wSup C hI htI hmax hPY hb' s
    obtain ⟨u, hu, hue⟩ := C.exists_radical hI htI hmax hPY b hbP hW _ hmem
    exact ⟨u, hu, hue⟩
  · have hmem := toHat_resLevi_mem_wSup C hI htI hmax hPY hc
    obtain ⟨u, hu, hue⟩ := C.exists_radical hI htI hmax hPY b hbP hW _ hmem
    exact ⟨u, hu, hue⟩

include C in
theorem exists_big_block (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) (hPY : P ≤ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b := by
  by_contra hcon
  push Not at hcon
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  apply hxy
  obtain ⟨x', hx'⟩ := C.toP_surjective hPY ⟨x, hx⟩
  obtain ⟨y', hy'⟩ := C.toP_surjective hPY ⟨y, hy⟩
  have hsub : Subsingleton (StatedSp (r - t) K) := by
    have h0 : r - t = 0 := by omega
    rw [h0]
    exact subsingleton_statedSp_zero
  have hcomm : spFlagLeviHom hI₀ htI ⁅x', y'⁆ = 1 := by
    refine leviHom_eq_one_of_blocks hI₀ htI (fun b hb => ?_) ?_
    · have hk : b - spFlagPrev I b = 1 := by
        have h1 := spFlagPrev_le I b
        have h2 := (hI b hb).1
        have h3 := hcon.2 b hb
        omega
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact gl_mul_comm_of_eq_one hk _ _
    · exact Subsingleton.elim _ _
  have hker : ⁅x', y'⁆ ∈ C.toHat.ker := by
    rw [C.ker_toHat hI htI hmax hPY]
    exact hcomm
  rw [C.ker_toHat_eq, Subgroup.mem_comap, map_commutatorElement, hx', hy'] at hker
  refine ⟨_, hker, ?_⟩
  simp [commutatorElement_def]

end SpCover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
