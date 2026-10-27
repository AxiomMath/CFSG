module

public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTTr
public import CFSG.ClassicalInvolution.AschTight.S1916ZT
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTSign

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem false_of_conj_eq_t (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {ζ : G} (hζ : ζ ∈ W ⊓ sec19Y K z)
    (hζ2 : ζ * ζ = z) {u : G} (huS : u ∈ (S : Subgroup G))
    (huH : u ∉ signSub (oddCoreOf (sec19Y K z)) ζ) {g : G}
    (hgS : g⁻¹ * u * g ∈ (S : Subgroup G))
    (hgU : ∀ x ∈ K ⊓ W, g⁻¹ * x * g ∈ (S : Subgroup G) ∧
      g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * u * g * (g⁻¹ * x * g))
    (he : g⁻¹ * z * g = t) : False := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight htb
  have hcomm := S1911.comm_of_mem hd0
  have hP : ∀ x ∈ Subgroup.centralizer ({z} : Set G),
      x ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) ∧
        (ζ⁻¹ * (x * ζ * x⁻¹) ∈ oddCoreOf (sec19Y K z) ∨
          ζ * (x * ζ * x⁻¹) ∈ oddCoreOf (sec19Y K z)) := fun x hx =>
    sign_mem_or hd h1 hζ hζ2 hx
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
  have hu'W := S1911.mem_W_of_comm_U h11b hd hgS hu't (comm_U_of_comm_V hd hgS hu't hu'V)
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
  have hdinv : (g * n)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hdz
  have huC : u ∈ Subgroup.centralizer ({z} : Set G) := hd0.hSz huS
  have hudW : (g * n)⁻¹ * u * (g * n) ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp hu'W
    have e : n⁻¹ * (g⁻¹ * u * g) * n⁻¹⁻¹ = (g * n)⁻¹ * u * (g * n) := by group
    rwa [e] at h
  have hudH : (g * n)⁻¹ * u * (g * n) ∈ signSub (oddCoreOf (sec19Y K z)) ζ :=
    mem_signSub_of_comm (hP _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hdinv huC) hdz)).1
      (hcomm _ hudW ζ hζ.1)
  exact conj_not_mem_signSub hP hdinv huC huH (by rwa [inv_inv])

theorem inf_centralizer_le_centralizer_t (h11b : C19_11bTmp p f)
    (hd : Sec19DataT p f K z S W L t V) (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({t} : Set G) := by
  rintro c ⟨hcS, hcR⟩
  by_contra hct
  have hd0 := hd.toSec19Data
  have hSC := hd0.hSz
  have hcR' : ∀ r ∈ (S : Subgroup G) ⊓ K, c * r = r * c := fun r hr =>
    (Subgroup.mem_centralizer_iff.mp hcR r hr).symm
  have hctz : c * t * c⁻¹ = t * z := by
    rcases S1911.conj_t_eq_or hd h1 hcS with h | h
    · refine absurd (Subgroup.mem_centralizer_singleton_iff.mpr ?_) hct
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [h]
    · exact h
  obtain ⟨u, huS, hu2, huinv, huU⟩ := exists_involution_of_conj_eq_mul h11b hd hcS hcR' hctz
  obtain ⟨ζ, hζ, hζ2⟩ := exists_mul_self_eq_z hd
  have hP : ∀ x ∈ Subgroup.centralizer ({z} : Set G),
      x ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) ∧
        (ζ⁻¹ * (x * ζ * x⁻¹) ∈ oddCoreOf (sec19Y K z) ∨
          ζ * (x * ζ * x⁻¹) ∈ oddCoreOf (sec19Y K z)) := fun x hx =>
    sign_mem_or hd h1 hζ hζ2 hx
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hζO : ζ * ζ ∉ oddCoreOf (sec19Y K z) := by
    rw [hζ2]
    intro hz
    have hmem : z ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) := ⟨hzZ.mem, hz⟩
    rw [S1916.inf_oddCoreOf_eq_bot (S.isPGroup'.to_le (inf_le_left.trans hd.hWS)) _,
      Subgroup.mem_bot] at hmem
    exact hzZ.ne_one hmem
  have huH := not_mem_signSub_of_inv hζO (huinv ζ hζ)
  obtain ⟨x₀, -, y₀, -, hxy⟩ := S1916.sd_noncomm_R hd0
  obtain ⟨g, hgQ, hgC⟩ := exists_conj_mem_of_index_two ⟨x₀, y₀, hxy⟩ S
    (fun s hs q hq => conj_mem_signSub hP (hSC hs) (hSC hq.1) hq.2)
    (fun a ha b hb haH hbH => inv_mul_mem_signSub hP (hSC ha) (hSC hb) haH hbH) huS huH hu2
  have hgU : ∀ x ∈ K ⊓ W, g⁻¹ * x * g ∈ (S : Subgroup G) ∧
      g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * u * g * (g⁻¹ * x * g) := by
    intro x hx
    have h := hgC x ⟨hd.hWS hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (huU x hx).symm⟩
    exact ⟨h.1, Subgroup.mem_centralizer_singleton_iff.mp h.2⟩
  rcases conj_z_eq_or hd (fun x hx => (hgU x hx).1) with he | he | he
  ·
    have hgz : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * z = g⁻¹ * z * g * g⁻¹ := by group
        _ = z * g⁻¹ := by rw [he]
    exact conj_not_mem_signSub hP hgz (hSC huS) huH (by rw [inv_inv]; exact hgQ.2)
  · exact false_of_conj_eq_t h11b hd h1 hζ hζ2 huS huH hgQ.1 hgU he
  ·
    obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hd
    have hrS := hrR.1
    have hconj : ∀ y ∈ (S : Subgroup G), r⁻¹ * y * r ∈ (S : Subgroup G) := fun y hy =>
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hrS) hy) hrS
    have e2 : (g * r)⁻¹ * u * (g * r) = r⁻¹ * (g⁻¹ * u * g) * r := by group
    refine false_of_conj_eq_t h11b hd h1 hζ hζ2 huS huH (g := g * r) ?_ (fun x hx => ?_) ?_
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

variable (p f) in
theorem c19_14C_of (h11b : C19_11bTmp p f) : S1916.C19_14CTmp p f := by
  intro G _ _ _ K z S W hd h1 c hc
  obtain ⟨L, t, V, hdT⟩ := exists_sec19DataT hd
  have hcR := S1916.mem_centralizer_of_mem_cStar hd hc.1 hc.2
  have hcC : c ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun r hr => (hcR r hr).symm⟩
  have hct := Subgroup.mem_centralizer_singleton_iff.mp
    (inf_centralizer_le_centralizer_t h11b hdT h1 hcC)
  exact S1916.sec19Y_le_sec19X K z (S1916.mem_W_inf_of_mem_centralizer_t h11b hdT hc.1 hcR hct).2

variable (p f) in
theorem c19_14_of_c19_11b (h11b : C19_11bTmp p f) (hB3 : GoldschmidtB3Tmp) : C19_14Tmp p f :=
  S1916.c19_14_of_C p f (c19_14C_of p f h11b) hB3

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
