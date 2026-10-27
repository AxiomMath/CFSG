module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Qc3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2C1a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem c1_twoPart_tbeta (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hVS : IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) :
    twoPart (centralizer ({t * β₀} : Set X)) < Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hWS, hST2⟩ := hc.qc_structure hKF hSV
  have hVS2 := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hs.le_V, hSV] at hVS2
  have hβc : twoPart (centralizer ({β₀} : Set X)) = Nat.card W := hc.card_eq.symm
  have hV : Nat.card V = twoPart (⊤ : Subgroup X) := hVS.card_eq
  have hTpos : 0 < Nat.card T₀ := Nat.card_pos
  by_cases hlt : Nat.card T₀ < twoPart (centralizer ({t * β₀} : Set X))
  · have h := hs.twoPart_le_of_fus hKF hKC (hs.fus_of_qc hKF hSV (hc.qc_S_ne hKF hSV))
      (beta_mem_X i j) hs.beta.not_mem hlt (by omega)
    omega
  · omega

theorem c1_conj_z (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hVS : IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) {g : X}
    (hg : g * z * g⁻¹ ∈ X₈) : g * z * g⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hWS, -⟩ := hc.qc_structure hKF hSV
  have hVS2 := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hs.le_V, hSV] at hVS2
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hβc : twoPart (centralizer ({β₀} : Set X)) = Nat.card W := hc.card_eq.symm
  have htc : twoPart (centralizer ({t} : Set X)) = Nat.card S := hs.sylow.card_eq.symm
  have htβ := hc.c1_twoPart_tbeta hKF hKC hVS hSV
  have hVz : V ≤ centralizer ({z} : Set X) := fun v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hs.z_mem_center_V.2 v hv)
  have hz := card_le_twoPart hs.sylow_V.isPGroup hVz
  rw [← L415.twoPart_centralizer_conj z g] at hz
  obtain ⟨v₁, hv₁, hv₁t⟩ := hc.qc_exists_v hKF hSV
  obtain ⟨s, hsS, hsβ⟩ := hc.qc_exists_s hKF hKC hSV
  have hst : s * t * s⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp (hs.sylow.le hsS)]
    group
  rcases hs.mem_X_cases hg with h | h | h | h | h | h | h | h
  · exfalso
    apply hs.setup.z_ne_one
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  · rw [h, hβc] at hz
    omega
  · exact h
  · rw [h, ← hsβ, L415.twoPart_centralizer_conj, hβc] at hz
    omega
  · rw [h, htc] at hz
    omega
  · rw [h] at hz
    omega
  · rw [h, ← hv₁t, L415.twoPart_centralizer_conj, htc] at hz
    omega
  · have e : t * (β₀ * z) = s * (t * β₀) * s⁻¹ := by
      rw [show s * (t * β₀) * s⁻¹ = (s * t * s⁻¹) * (s * β₀ * s⁻¹) by group, hst, hsβ]
    rw [h, e, L415.twoPart_centralizer_conj] at hz
    omega

theorem c1_mem_D (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hVS : IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) {g : X}
    (hgT : g * z * g⁻¹ ∈ T₀) : g * z * g⁻¹ ∈ S ⊓ L := by
  have hz2 : (g * z * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← hs.setup.z_order, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨h, hh, hhX⟩ := hs.setup.exists_conj_mem_X hKF hgT hz2
  have h1 : h * g * z * (h * g)⁻¹ = z := by
    have := hc.c1_conj_z hKF hKC hVS hSV (g := h * g) (by
      rw [show h * g * z * (h * g)⁻¹ = h * (g * z * g⁻¹) * h⁻¹ by group]
      exact hhX)
    exact this
  have e : g * z * g⁻¹ = h⁻¹ * z * h := by
    calc g * z * g⁻¹ = h⁻¹ * (h * g * z * (h * g)⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [h1]
  refine Subgroup.mem_inf.mpr ⟨hs.setup.T_le hgT, ?_⟩
  rw [e]
  have := (mem_normalizer_iff.mp (hs.standing.centralizer_le_normalizer (inv_mem hh)) z).mp
    hs.setup.z_mem.2
  rwa [inv_inv] at this

theorem c1_normal_D (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hVS : IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) {v d : X}
    (hv : v ∈ V) (hd : d ∈ S ⊓ L) : v * d * v⁻¹ ∈ S ⊓ L := by
  obtain ⟨m, -, ⟨e⟩⟩ := hs.setup.dihedral
  refine EndB.dih_conj_mem e (fun a ha ha2 => ?_) hd
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
    exact one_mem _
  obtain ⟨g, -, hg⟩ := hs.setup.exists_conj_eq_z hKF ha (by rw [sq, ha2]) ha1
  have e1 : v * a * v⁻¹ = (v * g⁻¹) * z * (v * g⁻¹)⁻¹ := by
    rw [← hg]
    group
  have hT : v * a * v⁻¹ ∈ T₀ :=
    (mem_normalizer_iff.mp (hs.sylow_V.le hv) a).mp (mem_sup_left (mem_sup_right ha))
  rw [e1] at hT ⊢
  exact hc.c1_mem_D hKF hKC hVS hSV hT

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
