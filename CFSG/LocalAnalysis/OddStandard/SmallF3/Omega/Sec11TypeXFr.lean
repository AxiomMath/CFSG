module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactsCInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FramePocket

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatFactsSmall.PSp43
  Certificates.OmegaInv

local notation "P45" => Equiv.Perm (Fin 45)

variable {G : Type} [Group G] {L : Subgroup G}

theorem t11_phi_mul (F : PspFrame L) {a b : G} (ha : a ∈ normalizer (L : Set G))
    (hb : b ∈ normalizer (L : Set G)) :
    F.φ ⟨a * b, (normalizer (L : Set G)).mul_mem ha hb⟩ = F.φ ⟨a, ha⟩ * F.φ ⟨b, hb⟩ :=
  map_mul F.φ ⟨a, ha⟩ ⟨b, hb⟩

theorem t11_psi_mul (F : PspFrame L) {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    F.ψ ⟨a * b, L.mul_mem ha hb⟩ = F.ψ ⟨a, ha⟩ * F.ψ ⟨b, hb⟩ :=
  map_mul F.ψ ⟨a, ha⟩ ⟨b, hb⟩

theorem t11_phi_comm (F : PspFrame L) {a b : G} (ha : a ∈ normalizer (L : Set G))
    (hb : b ∈ normalizer (L : Set G)) (h : a * b = b * a) :
    F.φ ⟨a, ha⟩ * F.φ ⟨b, hb⟩ = F.φ ⟨b, hb⟩ * F.φ ⟨a, ha⟩ := by
  rw [← map_mul, ← map_mul]
  exact congrArg F.φ (Subtype.ext h)

theorem t11_psi_comm (F : PspFrame L) {a b : G} (ha : a ∈ L) (hb : b ∈ L) (h : a * b = b * a) :
    F.ψ ⟨a, ha⟩ * F.ψ ⟨b, hb⟩ = F.ψ ⟨b, hb⟩ * F.ψ ⟨a, ha⟩ := by
  rw [← map_mul, ← map_mul]
  exact congrArg F.ψ (Subtype.ext h)

theorem t11_phi_pow3 (F : PspFrame L) {a : G} (ha : a ∈ normalizer (L : Set G))
    (h3 : a ^ 3 = 1) : F.φ ⟨a, ha⟩ ^ 3 = 1 := by
  have e : (⟨a, ha⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  rw [← map_pow, e, map_one]

theorem t11_eq_of_psi (F : PspFrame L) {a b : G} (ha : a ∈ L) (hb : b ∈ L)
    (h : F.ψ ⟨a, ha⟩ = F.ψ ⟨b, hb⟩) : a = b :=
  congrArg Subtype.val (F.ψ_injective h)

theorem t11_eq_one (F : PspFrame L) {x : G} (hx : x ∈ L) (hc : x ∈ centralizer (L : Set G)) :
    x = 1 := by
  have h1 : F.ψ ⟨x, hx⟩ = F.ψ ⟨1, L.one_mem⟩ := by
    rw [show (⟨1, L.one_mem⟩ : ↥L) = 1 from rfl, map_one]
    exact (F.ker_iff ⟨x, Subgroup.le_normalizer hx⟩).2 hc
  exact t11_eq_of_psi F hx L.one_mem h1

theorem t11_exists_frame_r3
    (hL : IsPSp43 L) {s : G} (hs : InducesTypeSome L s 5 1 2 1) :
    ∃ (F : PspFrame L) (hsN : s ∈ normalizer (L : Set G)), F.φ ⟨s, hsN⟩ = r3 () := by
  obtain ⟨F⟩ := exists_pspFrame hL
  obtain ⟨hsN, hI⟩ := (TyDict.inducesTypeSome_two_plus_iff hL F s).1 hs
  obtain ⟨g, hg, hge⟩ := MoInv.exists_conj_r3 hI
  exact ⟨F.conj g hg, hsN, hge⟩

theorem t11_conj_of_1152
    (F : PspFrame L) {a b : G} (ha : a ∈ L) (hb : b ∈ L) (hA : InvCent 1152 (F.ψ ⟨a, ha⟩))
    (hB : InvCent 1152 (F.ψ ⟨b, hb⟩)) : ∃ l ∈ L, l⁻¹ * a * l = b := by
  have key : ∀ {x : P45}, InvCent 1152 x →
      ∃ g ∈ QP45.originalSubgroup, g * x * g⁻¹ = Certificates.OmegaT0.z0 () := by
    intro x hx
    obtain ⟨hxA, hsq, hne, hc⟩ := hx
    rcases MoInv.class_cases hxA hsq hne with ⟨hg, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ |
      ⟨-, -, h1, -⟩
    · exact hg
    all_goals omega
  obtain ⟨g₁, hg₁, hg₁e⟩ := key hA
  obtain ⟨g₂, hg₂, hg₂e⟩ := key hB
  have hrel := FactsC.eq_conj_of_conj_eq hg₁e hg₂e
  obtain ⟨l0, hl0⟩ := F.ψ_surj
    (QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem hg₂) hg₁)
  refine ⟨((l0⁻¹ : ↥L) : G), (l0⁻¹).2, ?_⟩
  have key2 : F.ψ (l0 * ⟨a, ha⟩ * l0⁻¹) = F.ψ ⟨b, hb⟩ := by
    rw [map_mul, map_mul, map_inv, hl0]
    exact hrel.symm
  have h2 := congrArg Subtype.val (F.ψ_injective key2)
  simpa using h2

theorem t11_invCent_of_i4p
    (F : PspFrame L) {a : G} (ha : IsI4PlusIn L a) :
    InvCent 1152 (F.ψ ⟨a, PspFrame.mem_of_isI4PlusIn ha⟩) :=
  Ty.invCent_of_isI4PlusIn ((F.isI4PlusIn_img_iff (PspFrame.mem_of_isI4PlusIn ha)).1 ha)

end CFSG.OddStandard.SmallF3.Omega
