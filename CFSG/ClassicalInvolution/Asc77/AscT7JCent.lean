module

public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Z

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace T7J

section Frattini

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sq_mem_zpowers {x : G} (ho : Odd (orderOf x)) :
    ∃ y ∈ Subgroup.zpowers x, y * y = x := by
  refine ⟨x ^ ((orderOf x + 1) / 2), Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_⟩
  obtain ⟨m, hm⟩ := ho
  have h2 : (orderOf x + 1) / 2 + (orderOf x + 1) / 2 = orderOf x + 1 := by omega
  rw [← pow_add, h2, pow_succ, pow_orderOf_eq_one, one_mul]

omit [Finite G] in
theorem conj_inv_of_mem_zpowers {z x y : G} (hzx : z * x * z⁻¹ = x⁻¹)
    (hy : y ∈ Subgroup.zpowers x) : z * y * z⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, hzx, inv_zpow]

omit [Finite G] in
theorem le_sup_of_zstar {H N Y : Subgroup G} {z : G} (hz2 : z * z = 1) (hzH : z ∈ H)
    (hNH : N ≤ H) (hNodd : Odd (Nat.card N)) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hzs : ∀ g ∈ H, ⁅g, z⁆ ∈ N) (hY : ⁅N, Subgroup.zpowers z⁆ ≤ Y) :
    H ≤ Y ⊔ (H ⊓ Subgroup.centralizer ({z} : Set G)) := by
  intro g hg
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hodd : ∀ x ∈ N, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hx)
  obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : G, n₀ = g * z * g⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hn₀N : n₀ ∈ N := by
    have := hzs g hg
    rwa [commutatorElement_def, ← hn₀def] at this
  have hgz : g * z * g⁻¹ = n₀ * z := by rw [hn₀def]; group
  have hinv : z * n₀ * z⁻¹ = n₀⁻¹ := by
    have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rw [hgz] at hsq
    rw [hzi]
    calc z * n₀ * z = n₀⁻¹ * (n₀ * z * (n₀ * z)) := by group
      _ = n₀⁻¹ := by rw [hsq]; group
  obtain ⟨n, hn, hnn⟩ := exists_sq_mem_zpowers (hodd n₀ hn₀N)
  have hnN : n ∈ N := (Subgroup.zpowers_le.mpr hn₀N) hn
  have hzn : z * n * z⁻¹ = n⁻¹ := conj_inv_of_mem_zpowers hinv hn
  have hznz : n * z * n⁻¹ = g * z * g⁻¹ := by
    have h1 : z * n⁻¹ * z⁻¹ = n := by
      calc z * n⁻¹ * z⁻¹ = (z * n * z⁻¹)⁻¹ := by group
        _ = n := by rw [hzn]; exact inv_inv n
    have h2 : z * n⁻¹ = n * z := by
      calc z * n⁻¹ = (z * n⁻¹ * z⁻¹) * z := by group
        _ = n * z := by rw [h1]
    calc n * z * n⁻¹ = n * (z * n⁻¹) := by group
      _ = n * (n * z) := by rw [h2]
      _ = (n * n) * z := by group
      _ = n₀ * z := by rw [hnn]
      _ = g * z * g⁻¹ := hgz.symm
  have hhH : n⁻¹ * g ∈ H := H.mul_mem (H.inv_mem (hNH hnN)) hg
  have hhz : (n⁻¹ * g) * z = z * (n⁻¹ * g) := by
    have h1 : (n⁻¹ * g) * z * (n⁻¹ * g)⁻¹ = z := by
      calc (n⁻¹ * g) * z * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * z * g⁻¹) * n := by group
        _ = n⁻¹ * (n * z * n⁻¹) * n := by rw [hznz]
        _ = z := by group
    calc (n⁻¹ * g) * z = ((n⁻¹ * g) * z * (n⁻¹ * g)⁻¹) * (n⁻¹ * g) := by group
      _ = z * (n⁻¹ * g) := by rw [h1]
  obtain ⟨a, hadef⟩ : ∃ a : G, a = n * z * n⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hznN : z * n⁻¹ * z⁻¹ ∈ N := hNn z hzH n⁻¹ (N.inv_mem hnN)
  have haN : a ∈ N := by
    have : a = n * (z * n⁻¹ * z⁻¹) := by rw [hadef]; group
    rw [this]
    exact N.mul_mem hnN hznN
  have haY : a ∈ ⁅N, Subgroup.zpowers z⁆ := by
    have := Subgroup.commutator_mem_commutator hnN (Subgroup.mem_zpowers z)
    rwa [commutatorElement_def, ← hadef] at this
  have hza : z * a * z⁻¹ = a⁻¹ := by
    rw [hadef, hzi]
    calc z * (n * z * n⁻¹ * z) * z = z * (n * z * n⁻¹) * (z * z) := by group
      _ = z * n * z * n⁻¹ := by rw [hz2]; group
      _ = (n * z * n⁻¹ * z)⁻¹ := by
          have h3 : (n * z * n⁻¹ * z)⁻¹ = z⁻¹ * n * z⁻¹ * n⁻¹ := by group
          rw [h3, hzi]
  obtain ⟨b, hb, hbb⟩ := exists_sq_mem_zpowers (hodd a haN)
  have hbN : b ∈ N := (Subgroup.zpowers_le.mpr haN) hb
  have hbY : b ∈ ⁅N, Subgroup.zpowers z⁆ := (Subgroup.zpowers_le.mpr haY) hb
  have hzb : z * b * z⁻¹ = b⁻¹ := conj_inv_of_mem_zpowers hza hb
  have hcN : b⁻¹ * n ∈ N := N.mul_mem (N.inv_mem hbN) hnN
  have hcz : (b⁻¹ * n) * z = z * (b⁻¹ * n) := by
    have hzb' : z * b⁻¹ * z⁻¹ = b := by
      calc z * b⁻¹ * z⁻¹ = (z * b * z⁻¹)⁻¹ := by group
        _ = b := by rw [hzb]; exact inv_inv b
    have h1 : z * (b⁻¹ * n) * z⁻¹ = b⁻¹ * n := by
      calc z * (b⁻¹ * n) * z⁻¹ = (z * b⁻¹ * z⁻¹) * (z * n * z⁻¹) := by group
        _ = b * (z * n * z⁻¹) := by rw [hzb']
        _ = b⁻¹ * (b * b) * (z * n * z⁻¹) := by group
        _ = b⁻¹ * a * (z * n * z⁻¹) := by rw [hbb]
        _ = b⁻¹ * n := by rw [hadef]; group
    calc (b⁻¹ * n) * z = ((z * (b⁻¹ * n) * z⁻¹) * z) := by rw [h1]
      _ = z * (b⁻¹ * n) := by group
  have hgdec : g = b * ((b⁻¹ * n) * (n⁻¹ * g)) := by group
  have hmem : (b⁻¹ * n) * (n⁻¹ * g) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (b⁻¹ * n) * (n⁻¹ * g) * z = (b⁻¹ * n) * ((n⁻¹ * g) * z) := by group
      _ = (b⁻¹ * n) * (z * (n⁻¹ * g)) := by rw [hhz]
      _ = ((b⁻¹ * n) * z) * (n⁻¹ * g) := by group
      _ = (z * (b⁻¹ * n)) * (n⁻¹ * g) := by rw [hcz]
      _ = z * ((b⁻¹ * n) * (n⁻¹ * g)) := by group
  rw [hgdec]
  exact Subgroup.mul_mem_sup (hY hbY)
    (Subgroup.mem_inf.mpr ⟨H.mul_mem (hNH hcN) hhH, hmem⟩)

end Frattini

end T7J

section Cent

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Hyp22ZStarCu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, ¬ MuIsoWylD4 Ω W →
        z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G))

variable {p f}

theorem c22_4_cent_of_zstar (hZ : Hyp22ZStarCu p f) : C22_4_cent p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW hμ
  have hs := h.setting
  have hzs := hZ G Ω K K' K₃ z u₁ u₂ u₃ h W hW hμ
  have hu1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hs.stand.hyp hs.stand.mem hs.hK'.1 hs.hne.symm hs.hz hs.hu₁.1
      hs.hu₂.1 hs.hu₂.2).1
  have hz2 : z * z = 1 := hs.hz.sq
  obtain ⟨zh, hzh, hzhz⟩ := Subgroup.mem_map.mp hzs
  rw [Subgroup.mem_comap] at hzh
  have hzH : z ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) := by
    rw [← hzhz]
    exact zh.2
  refine T7J.le_sup_of_zstar hz2 hzH (oddCoreIn_le _) (oddCoreOf_odd_natCard _)
    (fun h' hh' n hn => conj_mem_oddCoreIn_of_mem_normalizer (Subgroup.le_normalizer hh') hn)
    (fun g hg => ?_) ?_
  ·
    have hc := Subgroup.mem_center_iff.mp hzh (QuotientGroup.mk' _ ⟨g, hg⟩)
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer
        ({u₁ * u₂} : Set G))) (⟨g, hg⟩ * zh * ⟨g, hg⟩⁻¹ * zh⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine ⟨_, h1, ?_⟩
    simp [commutatorElement_def, ← hzhz]
  ·
    have hu_mem : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hz_mem : z ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
      Subgroup.subset_closure (by simp)
    refine le_trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hz_mem)) ?_
    unfold alphaOf
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (u₁ * u₂) hu_mem
      (le_iSup (fun _ : u₁ * u₂ ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
        Subgroup.closure ({u₁ * u₂, z} : Set G)⁆) hu1)

end Cent

end CFSG.ClassicalInvolution.Asc77
