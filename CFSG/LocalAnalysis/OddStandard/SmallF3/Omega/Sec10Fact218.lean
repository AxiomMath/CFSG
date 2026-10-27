module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkTA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypesClass

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

namespace Ty

theorem memB_iff {l : List P45} {x : P45} : memB l x = true ↔ x ∈ l := by
  simp [memB, List.any_eq_true]

theorem conjugate_eq_iff {u : P45} (huu : u * u = 1) {K K' : Subgroup P45} :
    CFSG.conjugate K u = K' ↔ (∀ k ∈ K, u * k * u⁻¹ ∈ K') ∧ ∀ k ∈ K', u * k * u⁻¹ ∈ K := by
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [← h, mem_conjugate_iff']
      have e : u * (u * k * u⁻¹) * u⁻¹ = k := by rw [hinv, ← mul_assoc, ← mul_assoc, huu, one_mul,
        mul_assoc, huu, mul_one]
      rw [e]
      exact hk
    · rw [← h, mem_conjugate_iff'] at hk
      exact hk
  · rintro ⟨h1, h2⟩
    ext y
    rw [mem_conjugate_iff']
    constructor
    · intro hy
      have := h1 _ hy
      rwa [show u * (u * y * u⁻¹) * u⁻¹ = y by rw [hinv, ← mul_assoc, ← mul_assoc, huu, one_mul,
        mul_assoc, huu, mul_one]] at this
    · intro hy
      exact h2 y hy

theorem swapChk_iff_KA {u : P45} (huu : u * u = 1) :
    Certificates.OmegaTypes.swapChk KAl KBl u = true ↔ CFSG.conjugate Pk.KA u = Pk.KB := by
  rw [conjugate_eq_iff huu, Certificates.OmegaTypes.swapChk, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true]
  simp only [memB_iff, mem_KAl, mem_KBl]

theorem swapChk_iff_KB {u : P45} (huu : u * u = 1) :
    Certificates.OmegaTypes.swapChk KAl KBl u = true ↔ CFSG.conjugate Pk.KB u = Pk.KA := by
  rw [conjugate_eq_iff huu, Certificates.OmegaTypes.swapChk, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true, and_comm]
  simp only [memB_iff, mem_KAl, mem_KBl]

theorem stabChk_iff {u : P45} (huu : u * u = 1) :
    Certificates.OmegaTypes.stabChk KAl KBl u = true ↔
      CFSG.conjugate Pk.KA u = Pk.KA ∧ CFSG.conjugate Pk.KB u = Pk.KB := by
  rw [conjugate_eq_iff huu, conjugate_eq_iff huu, Certificates.OmegaTypes.stabChk,
    Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  simp only [memB_iff, mem_KAl, mem_KBl]
  tauto

theorem pockets_cases {G : Type}
    [Group G] {L : Subgroup G} (F : PspFrame L) {z : G} (hzL : z ∈ L)
    (hψz : F.ψ ⟨z, hzL⟩ = Pk.tA) {K1 K2 : Subgroup G} (hK1 : Sl23PocketIn L z K1)
    (hK2 : Sl23PocketIn L z K2) (hne : K1 ≠ K2) :
    (F.img K1 = Pk.KA ∧ F.img K2 = Pk.KB) ∨ (F.img K1 = Pk.KB ∧ F.img K2 = Pk.KA) := by
  have hK1L := PspFrame.le_of_sl23PocketIn hK1
  have hK2L := PspFrame.le_of_sl23PocketIn hK2
  have hp1 := (F.sl23PocketIn_img_iff hzL hK1L).1 hK1
  have hp2 := (F.sl23PocketIn_img_iff hzL hK2L).1 hK2
  rw [hψz] at hp1 hp2
  have hne' : F.img K1 ≠ F.img K2 := fun h => hne ((F.img_inj hK1L hK2L).1 h)
  rcases Pk.pocket_tA_cases hp1 with h1 | h1 <;> rcases Pk.pocket_tA_cases hp2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne'
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne'

theorem model218d
    {u : P45} (huP : u ∈ QP45.originalSubgroup)
    (hu : InvCent 192 u) (hc : u * Pk.tA = Pk.tA * u) {X Y : Subgroup P45}
    (hXY : (X = Pk.KA ∧ Y = Pk.KB) ∨ (X = Pk.KB ∧ Y = Pk.KA)) :
    (CFSG.conjugate X u = X ∧ CFSG.conjugate Y u = Y ∧ ∃ k ∈ X, k * u * k⁻¹ = u * Pk.tA) ∨
      (CFSG.conjugate X u = Y ∧ IsI4PlusIn QP45.originalSubgroup (u * Pk.tA)) := by
  have huu := hu.2.1
  rcases card218d hu hc with ⟨hs1, hs2, ⟨k1, hk1, hk1'⟩, ⟨k2, hk2, hk2'⟩⟩ | ⟨hw1, hw2, h1152⟩
  · have hA := (conjugate_eq_iff huu).2 ⟨hs1, hs1⟩
    have hB := (conjugate_eq_iff huu).2 ⟨hs2, hs2⟩
    left
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hA, hB, k1, hk1, hk1'⟩
    · exact ⟨hB, hA, k2, hk2, hk2'⟩
  · right
    refine ⟨?_, isI4PlusIn_of_invCent (QP45.originalSubgroup.mul_mem huP Pk.tA_mem) h1152⟩
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (conjugate_eq_iff huu).2 ⟨hw1, hw2⟩
    · exact (conjugate_eq_iff huu).2 ⟨hw2, hw1⟩

theorem model218e
    {u : P45} (hu : InvCent 96 u) {X Y : Subgroup P45}
    (hXY : (X = Pk.KA ∧ Y = Pk.KB) ∨ (X = Pk.KB ∧ Y = Pk.KA)) (h : CFSG.conjugate X u = Y) :
    u * Pk.tA = Pk.tA * u ∧ InvCent 1440 (u * Pk.tA) := by
  rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := (conjugate_eq_iff hu.2.1).1 h
    exact card218e hu h1 h2
  · obtain ⟨h1, h2⟩ := (conjugate_eq_iff hu.2.1).1 h
    exact card218e hu h2 h1

end Ty

theorem asc82Fact218c_of_cert :
    Asc82Fact218c := by
  intro G _ _ L hL z u hz hu hne hcomm
  obtain ⟨F⟩ := exists_pspFrame hL
  have hzL : z ∈ L := PspFrame.mem_of_isI4PlusIn hz
  have huL : u ∈ L := PspFrame.mem_of_isI4PlusIn hu
  have ha := Ty.invCent_of_isI4PlusIn ((F.isI4PlusIn_img_iff hzL).1 hz)
  have hb := Ty.invCent_of_isI4PlusIn ((F.isI4PlusIn_img_iff huL).1 hu)
  have hab : F.ψ ⟨z, hzL⟩ ≠ F.ψ ⟨u, huL⟩ := fun h =>
    hne (congrArg Subtype.val (F.ψ_injective h))
  have hc : F.ψ ⟨z, hzL⟩ * F.ψ ⟨u, huL⟩ = F.ψ ⟨u, huL⟩ * F.ψ ⟨z, hzL⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg F.ψ (Subtype.ext hcomm)
  have h192 := Ty.card218c ha hb hab hc
  have huzL : u * z ∈ L := L.mul_mem huL hzL
  have hs : u * z ∈ normalizer (L : Set G) := Subgroup.le_normalizer huzL
  refine (TyDict.inducesTypeSome_two_minus_iff hL F (u * z)).2 ⟨hs, ?_⟩
  have h2 : F.φ ⟨u * z, hs⟩ = F.ψ ⟨u, huL⟩ * F.ψ ⟨z, hzL⟩ := by
    rw [← map_mul]
    rfl
  rw [h2]
  exact h192

theorem asc82Fact218d_of_cert :
    Asc82Fact218d := by
  intro G _ _ L hL z K1 K2 hz hK1 hK2 hne u huL _ huz hty
  obtain ⟨F, hzL, hψz⟩ := Pk.exists_frame_tA hL hz
  have hK1L := PspFrame.le_of_sl23PocketIn hK1
  have hK2L := PspFrame.le_of_sl23PocketIn hK2
  have hXY := Ty.pockets_cases F hzL hψz hK1 hK2 hne
  obtain ⟨huN, hinv⟩ := (TyDict.inducesTypeSome_two_minus_iff hL F u).1 hty
  have hφψ : F.φ ⟨u, huN⟩ = F.ψ ⟨u, huL⟩ := rfl
  rw [hφψ] at hinv
  have hc : F.ψ ⟨u, huL⟩ * Pk.tA = Pk.tA * F.ψ ⟨u, huL⟩ := by
    rw [← hψz, ← map_mul, ← map_mul]
    exact congrArg F.ψ (Subtype.ext huz)
  have huzL : u * z ∈ L := L.mul_mem huL hzL
  have hmul : F.ψ ⟨u * z, huzL⟩ = F.ψ ⟨u, huL⟩ * Pk.tA := by
    rw [← hψz, ← map_mul]
    rfl
  have hcj1 := F.img_conjugate_psi (X := K1) ⟨u, huL⟩
  have hcj2 := F.img_conjugate_psi (X := K2) ⟨u, huL⟩
  have hc1 := Pk.conjugate_le_of_le hK1L huL
  have hc2 := Pk.conjugate_le_of_le hK2L huL
  rcases Ty.model218d (F.ψ_mem ⟨u, huL⟩) hinv hc hXY with
    ⟨hs1, hs2, κ, hκ, hκu⟩ | ⟨hsw, hI⟩
  · left
    refine ⟨(F.img_inj hc1 hK1L).1 (by rw [hcj1]; exact hs1),
      (F.img_inj hc2 hK2L).1 (by rw [hcj2]; exact hs2), ?_⟩
    obtain ⟨k, hkK, rfl⟩ := F.mem_img.1 hκ
    refine ⟨(k : G), hkK, ?_⟩
    have h1 : F.ψ (k * ⟨u, huL⟩ * k⁻¹) = F.ψ ⟨u * z, huzL⟩ := by
      rw [map_mul, map_mul, map_inv, hmul]
      exact hκu
    exact congrArg Subtype.val (F.ψ_injective h1)
  · right
    refine ⟨(F.img_inj hc1 hK2L).1 (by rw [hcj1]; exact hsw), ?_⟩
    rw [← hmul] at hI
    exact (F.isI4PlusIn_img_iff huzL).2 hI

theorem asc82Fact218e_of_cert :
    Asc82Fact218e := by
  intro G _ _ L hL z K1 K2 hz hK1 hK2 hne u hty hconj
  obtain ⟨F, hzL, hψz⟩ := Pk.exists_frame_tA hL hz
  have hXY := Ty.pockets_cases F hzL hψz hK1 hK2 hne
  obtain ⟨huN, hinv⟩ := (TyDict.inducesTypeSome_two_plus_iff hL F u).1 hty
  have hconj' : CFSG.conjugate (F.img K1) (F.φ ⟨u, huN⟩) = F.img K2 := by
    rw [← F.img_conjugate_phi ⟨u, huN⟩]
    exact congrArg F.img hconj
  obtain ⟨-, h1440⟩ := Ty.model218e hinv hXY hconj'
  have huzN : u * z ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem huN (Subgroup.le_normalizer hzL)
  refine (TyDict.inducesTypeSome_four_minus_iff hL F (u * z)).2 ⟨huzN, ?_⟩
  have h2 : F.φ ⟨u * z, huzN⟩ = F.φ ⟨u, huN⟩ * Pk.tA := by
    have h3 : (⟨u * z, huzN⟩ : ↥(normalizer (L : Set G))) =
        ⟨u, huN⟩ * ⟨z, Subgroup.le_normalizer hzL⟩ := rfl
    rw [h3, map_mul, ← hψz]
    rfl
  rw [h2]
  exact h1440

theorem asc82Fact218f_of_cert :
    Asc82Fact218f := by
  intro G _ _ L hL s u hs hu hu2 hu3 hsu hY
  obtain ⟨F⟩ := exists_pspFrame hL
  obtain ⟨hsN, hsinv⟩ : ∃ hsN : s ∈ normalizer (L : Set G),
      InvCent 96 (F.φ ⟨s, hsN⟩) ∨ InvCent 192 (F.φ ⟨s, hsN⟩) := by
    rcases hs with h | h
    · obtain ⟨hsN, h96⟩ := (TyDict.inducesTypeSome_two_plus_iff hL F s).1 h
      exact ⟨hsN, Or.inl h96⟩
    · obtain ⟨hsN, h192⟩ := (TyDict.inducesTypeSome_two_minus_iff hL F s).1 h
      exact ⟨hsN, Or.inr h192⟩
  have huuN : u * u ∈ normalizer (L : Set G) := (normalizer (L : Set G)).mul_mem hu hu
  have huu : F.φ ⟨u, hu⟩ * F.φ ⟨u, hu⟩ = 1 := by
    have h2 : (⟨u * u, huuN⟩ : ↥(normalizer (L : Set G))) = ⟨u, hu⟩ * ⟨u, hu⟩ := rfl
    rw [← map_mul, ← h2]
    exact (F.ker_iff _).2 hu2
  have hu1 : F.φ ⟨u, hu⟩ ≠ 1 := fun h => hu3 ((F.ker_iff ⟨u, hu⟩).1 h)
  have hus : F.φ ⟨u, hu⟩ ≠ F.φ ⟨s, hsN⟩ := by
    intro h
    apply hsu
    have hsuN : s⁻¹ * u ∈ normalizer (L : Set G) :=
      (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hsN) hu
    have h1 : F.φ ⟨s⁻¹ * u, hsuN⟩ = 1 := by
      have h2 : (⟨s⁻¹ * u, hsuN⟩ : ↥(normalizer (L : Set G))) = ⟨s, hsN⟩⁻¹ * ⟨u, hu⟩ := rfl
      rw [h2, map_mul, map_inv, h, inv_mul_cancel]
    exact (F.ker_iff _).1 h1
  have hY' : ∀ g ∈ QP45.originalSubgroup, g * F.φ ⟨s, hsN⟩ = F.φ ⟨s, hsN⟩ * g → g ^ 405 = 1 →
      F.φ ⟨u, hu⟩ * g = g * F.φ ⟨u, hu⟩ := by
    intro g hg hgs hg405
    obtain ⟨l, rfl⟩ := F.ψ_surj hg
    have hls : (l : G) * s = s * l := ((F.comm_phi_psi_iff ⟨s, hsN⟩ l).1 hgs.symm).symm
    have hodd : Odd (orderOf (l : G)) := by
      rw [← F.orderOf_psi l]
      exact Odd.of_dvd_nat (by decide : Odd 405) (orderOf_dvd_of_pow_eq_one hg405)
    have hlmem : (l : G) ∈ oTwoRes (L ⊓ centralizer ({s} : Set G)) :=
      Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨l.2,
        Subgroup.mem_centralizer_singleton_iff.2 hls⟩, hodd⟩
    exact (F.comm_phi_psi_iff ⟨u, hu⟩ l).2 (hY l hlmem)
  rcases Ty.card218f hsinv (F.mem_A _) huu hu1 hus hY' with h | h
  · exact Or.inl ((TyDict.inducesTypeSome_four_plus_iff hL F u).2 ⟨hu, h⟩)
  · exact Or.inr ((TyDict.inducesTypeSome_four_minus_iff hL F u).2 ⟨hu, h⟩)

end CFSG.OddStandard.SmallF3.Omega
