module

public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTTr

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem false_of_conj_eq_t' (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V)
    {u : G} (huS : u ∈ (S : Subgroup G))
    (hW : ∀ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * u * d ∉ W) {g : G}
    (hgS : g⁻¹ * u * g ∈ (S : Subgroup G))
    (hgU : ∀ x ∈ K ⊓ W, g⁻¹ * x * g ∈ (S : Subgroup G) ∧
      g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * u * g * (g⁻¹ * x * g))
    (he : g⁻¹ * z * g = t) : False := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight htb
  have hcomm := S1911.comm_of_mem hd0
  have hIg : IsUniqueInvolution (conjSub g⁻¹ K) t := by
    have h := hI.conj g⁻¹
    rwa [inv_inv, he] at h
  have hKg : conjSub g⁻¹ K = L := S1911.eq_of_isUniqueInvolution_member htb
    (hΩ.conjInvariant g⁻¹ K (CoreAssembly.mem_conjClass_self K)) hd.memL hIg hd.invL
  have hle : conjSub g⁻¹ (K ⊓ W) ≤ V := by
    intro y hy
    rw [mem_conjSub_iff, inv_inv] at hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have h2 := (hgU _ hy).1
    rw [e] at h2
    have hyL : y ∈ L := by
      rw [← hKg, mem_conjSub_iff, inv_inv]
      exact hy.1
    rw [← S1911.inf_member_eq hd]
    exact ⟨h2, hyL⟩
  have hcard : Nat.card V ≤ Nat.card ↥(conjSub g⁻¹ (K ⊓ W)) := by
    rw [Asc77.natCard_conjSub, S1911.card_inf_eq_card hd]
  have heq : conjSub g⁻¹ (K ⊓ W) = V := Subgroup.eq_of_le_of_card_ge hle hcard
  have hu'V : ∀ v ∈ V, g⁻¹ * u * g * v = v * (g⁻¹ * u * g) := by
    intro v hv
    rw [← heq, mem_conjSub_iff, inv_inv] at hv
    have h := (hgU _ hv).2
    have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    rw [e] at h
    exact h.symm
  have hu't : g⁻¹ * u * g ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← he]
    have huz : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz huS)
    calc g⁻¹ * u * g * (g⁻¹ * z * g) = g⁻¹ * (u * z) * g := by group
      _ = g⁻¹ * (z * u) * g := by rw [huz]
      _ = g⁻¹ * z * g * (g⁻¹ * u * g) := by group
  have hu'W := S1911.mem_W_of_comm_U h11b hd hgS hu't (S19Q.comm_U_of_comm_V hd hgS hu't hu'V)
  have hzW : z ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun w hw => Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz (hd.hWS hw))
  have htW : g⁻¹ * z * g⁻¹⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    rw [inv_inv, he]
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => hcomm w hw t (S1911.mem_W hd)
  obtain ⟨n, hn, hnz⟩ := S19B.exists_normalizer_conj_eq hd hzW htW
  rw [inv_inv, he] at hnz
  have hdz : g * n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : g * n * z * (g * n)⁻¹ = z := by
      calc g * n * z * (g * n)⁻¹ = g * (n * z * n⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hnz, he]
        _ = z := by group
    calc g * n * z = g * n * z * (g * n)⁻¹ * (g * n) := by group
      _ = z * (g * n) := by rw [e]
  have hudW : (g * n)⁻¹ * u * (g * n) ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp hu'W
    have e : n⁻¹ * (g⁻¹ * u * g) * n⁻¹⁻¹ = (g * n)⁻¹ * u * (g * n) := by group
    rwa [e] at h
  exact hW _ hdz hudW

theorem false_of_transfer (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V)
    {H : Subgroup G}
    (hHn : ∀ s ∈ (S : Subgroup G), ∀ x ∈ (S : Subgroup G) ⊓ H, s * x * s⁻¹ ∈ H)
    (hidx : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a ∉ H → b ∉ H → a⁻¹ * b ∈ H)
    {u : G} (huS : u ∈ (S : Subgroup G)) (huH : u ∉ H) (hu2 : u * u = 1)
    (huU : ∀ x ∈ K ⊓ W, u * x = x * u)
    (hS : ∀ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * u * d ∈ (S : Subgroup G) →
      d⁻¹ * u * d ∉ H)
    (hW : ∀ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * u * d ∉ W) : False := by
  have hd0 := hd.toSec19Data
  obtain ⟨x₀, -, y₀, -, hxy⟩ := S1916.sd_noncomm_R hd0
  obtain ⟨g, hgQ, hgC⟩ := S19Q.exists_conj_mem_of_index_two ⟨x₀, y₀, hxy⟩ S hHn hidx huS huH hu2
  have hgU : ∀ x ∈ K ⊓ W, g⁻¹ * x * g ∈ (S : Subgroup G) ∧
      g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * u * g * (g⁻¹ * x * g) := by
    intro x hx
    have h := hgC x ⟨hd.hWS hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (huU x hx).symm⟩
    exact ⟨h.1, Subgroup.mem_centralizer_singleton_iff.mp h.2⟩
  rcases S19Q.conj_z_eq_or hd (fun x hx => (hgU x hx).1) with he | he | he
  ·
    have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * z = g * (g⁻¹ * z * g) := by rw [he]
        _ = z * g := by group
    exact hS g hgz hgQ.1 hgQ.2
  · exact false_of_conj_eq_t' h11b hd huS hW hgQ.1 hgU he
  ·
    obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hd
    have hrS := hrR.1
    have hconj : ∀ y ∈ (S : Subgroup G), r⁻¹ * y * r ∈ (S : Subgroup G) := fun y hy =>
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hrS) hy) hrS
    have e2 : (g * r)⁻¹ * u * (g * r) = r⁻¹ * (g⁻¹ * u * g) * r := by group
    refine false_of_conj_eq_t' h11b hd huS hW (g := g * r) ?_ (fun x hx => ?_) ?_
    · rw [e2]
      exact hconj _ hgQ.1
    · obtain ⟨hxS, hxc⟩ := hgU x hx
      have e1 : (g * r)⁻¹ * x * (g * r) = r⁻¹ * (g⁻¹ * x * g) * r := by group
      rw [e1, e2]
      refine ⟨hconj _ hxS, ?_⟩
      calc r⁻¹ * (g⁻¹ * x * g) * r * (r⁻¹ * (g⁻¹ * u * g) * r) =
          r⁻¹ * (g⁻¹ * x * g * (g⁻¹ * u * g)) * r := by group
        _ = r⁻¹ * (g⁻¹ * u * g * (g⁻¹ * x * g)) * r := by rw [hxc]
        _ = r⁻¹ * (g⁻¹ * u * g) * r * (r⁻¹ * (g⁻¹ * x * g) * r) := by group
    · calc (g * r)⁻¹ * z * (g * r) = r⁻¹ * (g⁻¹ * z * g) * r := by group
        _ = r⁻¹ * (t * z) * r := by rw [he]
        _ = t := by rw [← hrt]; group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
