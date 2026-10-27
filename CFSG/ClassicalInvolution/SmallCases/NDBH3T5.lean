module

public import CFSG.ClassicalInvolution.SmallCases.NDBH3T4
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB.NDBH3

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}


theorem link_core (C : XCtx p f Ω z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ tqMembers Ω z) {r : G} (hr : IsClassicalMember p f R₀ r) (hrz : r ≠ z)
    {L : Subgroup G} (hL : L ∈ tqMembers Ω z) {w : G} (hw : IsClassicalMember p f L w) :
    ∃ h ∈ exactLayer Ω z, w = h * z * h⁻¹ ∨ w = h * r * h⁻¹ ∨ w = h * (z * r) * h⁻¹ := by
  by_cases hwz : w = z
  · exact ⟨1, one_mem _, Or.inl (by rw [hwz]; group)⟩
  have hwY : w ∈ exactLayer Ω z := exactCore_le_exactLayer hL (C.involution_mem_exactCore hL hw)
  have hrY : r ∈ exactLayer Ω z :=
    exactCore_le_exactLayer hR₀ (C.involution_mem_exactCore hR₀ hr)
  have hw2 : w * w = 1 := hw.isCentralInvolution.sq
  have hr2 : r * r = 1 := hr.isCentralInvolution.sq
  rcases NDBG.nbar_eq_or_mul_eq C hnoF hall hL hR₀ hw hr hwz hrz with h | h
  · obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hrY hw2 hr2 h
    exact ⟨o, oddCoreIn_le _ ho, Or.inr (Or.inl hwo)⟩
  · have hzrY : z * r ∈ exactLayer Ω z := mul_mem C.z_mem_exactLayer hrY
    have hrC : r ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hR₀ hr
    have hrz' : z * r = r * z := (Subgroup.mem_centralizer_singleton_iff.mp hrC).symm
    have hzr2 : z * r * (z * r) = 1 := by
      calc z * r * (z * r) = z * (r * z) * r := by group
        _ = z * (z * r) * r := by rw [← hrz']
        _ = (z * z) * (r * r) := by group
        _ = 1 := by rw [C.hKz.sq, hr2, one_mul]
    have hr2' : oddQuotMk z ⟨r, hrC⟩ * oddQuotMk z ⟨r, hrC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨r, hrC⟩ * ⟨r, hrC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext hr2
      rw [this, map_one]
    have heq : oddQuotMk z ⟨w, exactLayer_le_centralizer Ω z hwY⟩ =
        oddQuotMk z ⟨z * r, exactLayer_le_centralizer Ω z hzrY⟩ := by
      have e : (⟨z * r, exactLayer_le_centralizer Ω z hzrY⟩ :
          ↥(Subgroup.centralizer ({z} : Set G))) = ⟨z, XCtx.hzC z⟩ * ⟨r, hrC⟩ := rfl
      rw [e, map_mul, ← h, mul_assoc, hr2', mul_one]
    obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hzrY hw2 hzr2 heq
    exact ⟨o, oddCoreIn_le _ ho, Or.inr (Or.inr hwo)⟩

theorem link_at (C : XCtx p f Ω z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {c g : G} (hgz : g * z * g⁻¹ = c)
    {R₁ : Subgroup G} (hR₁ : R₁ ∈ tqMembers Ω c) {b : G} (hb : IsClassicalMember p f R₁ b)
    (hbc : b ≠ c) {L : Subgroup G} (hL : L ∈ tqMembers Ω c) {w : G}
    (hw : IsClassicalMember p f L w) :
    ∃ h ∈ exactLayer Ω c, w = h * c * h⁻¹ ∨ w = h * b * h⁻¹ ∨ w = h * (c * b) * h⁻¹ := by
  have hΩc := C.hΩ.conjInvariant
  have hz' : g⁻¹ * c * g⁻¹⁻¹ = z := by rw [← hgz]; group
  have hmemtq : ∀ {M : Subgroup G}, M ∈ tqMembers Ω c → conjSub g⁻¹ M ∈ tqMembers Ω z :=
    fun hM => ⟨hΩc g⁻¹ _ hM.1, by
      have h := trivialOnQuot_conjSub hM.2 g⁻¹
      rwa [hz'] at h⟩
  have hbz : g⁻¹ * b * g⁻¹⁻¹ ≠ z := fun h => hbc (by
    calc b = g * (g⁻¹ * b * g⁻¹⁻¹) * g⁻¹ := by group
      _ = c := by rw [h, hgz])
  obtain ⟨h, hh, hx⟩ := link_core C hnoF hall (hmemtq hR₁) (hb.conj g⁻¹) hbz (hmemtq hL)
    (hw.conj g⁻¹)
  have hh' : g * h * g⁻¹ ∈ exactLayer Ω c := by
    rw [← hgz, exactLayer_conj hΩc g z]
    exact conj_mem_conjSub hh
  refine ⟨g * h * g⁻¹, hh', ?_⟩
  rcases hx with e | e | e
  · left
    calc w = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * (h * z * h⁻¹) * g⁻¹ := by rw [e]
      _ = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
      _ = (g * h * g⁻¹) * c * (g * h * g⁻¹)⁻¹ := by rw [hgz]
  · right; left
    calc w = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * b * g⁻¹⁻¹) * h⁻¹) * g⁻¹ := by rw [e]
      _ = (g * h * g⁻¹) * b * (g * h * g⁻¹)⁻¹ := by group
  · right; right
    calc w = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * (h * (z * (g⁻¹ * b * g⁻¹⁻¹)) * h⁻¹) * g⁻¹ := by rw [e]
      _ = (g * h * g⁻¹) * ((g * z * g⁻¹) * b) * (g * h * g⁻¹)⁻¹ := by group
      _ = (g * h * g⁻¹) * (c * b) * (g * h * g⁻¹)⁻¹ := by rw [hgz]

theorem linkStar (C : XCtx p f Ω z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {B : Subgroup G} {S : Set (Subgroup G)}
    {c g : G} (hgz : g * z * g⁻¹ = c) {R₁ : Subgroup G} (hR₁ : R₁ ∈ tqMembers Ω c) {b : G}
    (hb : IsClassicalMember p f R₁ b) (hbc : b ≠ c)
    (hS : ∀ x : G, (x = c ∨ x = b ∨ x = c * b) → x ∈ B ∧
      ∀ M ∈ Ω, IsClassicalMember p f M x → ∃ M' ∈ S, IsClassicalMember p f M' x) :
    InvolutionLinkStar p f Ω B S c := by
  intro L hLΩ w hw hdisj
  have key : ActsTrivOnQuot L c ∨ w = c := by
    rcases hdisj with h | ⟨L', hL', hL'c, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq C.hp C.hq C.hΩ hLΩ hL' hw hL'c hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwc
  · have hLtq : L ∈ tqMembers Ω c := ⟨hLΩ, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩
    obtain ⟨h, hh, hx⟩ := link_at C hnoF hall hgz hR₁ hb hbc hLtq hw
    have hfin : ∀ x : G, (x = c ∨ x = b ∨ x = c * b) → w = h * x * h⁻¹ →
        ∃ K ∈ S, ∃ z' ∈ B, IsClassicalMember p f K z' ∧
          ∃ h ∈ exactLayer Ω c, w = h * z' * h⁻¹ := by
      intro x hxs hwx
      obtain ⟨hxB, hxS⟩ := hS x hxs
      have hcl : IsClassicalMember p f (conjSub h⁻¹ L) x := by
        have := hw.conj h⁻¹
        have e : h⁻¹ * w * h⁻¹⁻¹ = x := by rw [hwx]; group
        rwa [e] at this
      obtain ⟨M', hM'S, hM'x⟩ := hxS _ (C.hΩ.conjInvariant h⁻¹ L hLΩ) hcl
      exact ⟨M', hM'S, x, hxB, hM'x, h, hh, hwx⟩
    rcases hx with e | e | e
    · exact hfin c (Or.inl rfl) e
    · exact hfin b (Or.inr (Or.inl rfl)) e
    · exact hfin (c * b) (Or.inr (Or.inr rfl)) e
  · obtain ⟨hcB, hcS⟩ := hS c (Or.inl rfl)
    obtain ⟨M', hM'S, hM'c⟩ := hcS L hLΩ (hwc ▸ hw)
    exact ⟨M', hM'S, c, hcB, hM'c, 1, one_mem _, by rw [hwc]; group⟩

end CFSG.ClassicalInvolution.NDB.NDBH3
