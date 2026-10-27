module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Ab1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem y7a_fpf_I {I F W : Subgroup G} {t k : G}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x) (hFI : F ≤ I) (hWF : W ≤ F)
    (hkt : k * t = t * k) (hFt : ∀ f ∈ F, f * t = t * f)
    (hxt : ∀ x ∈ I, ⁅x, t⁆ ∈ W) (hker : ∀ x ∈ I, x * t = t * x → x ∈ F)
    (hkI : ∀ x ∈ I, k * x * k⁻¹ ∈ I) (hkW : ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hfix : ∀ w ∈ W, k * w * k⁻¹ = w → w = 1) :
    ∀ x ∈ I, k * x * k⁻¹ * x⁻¹ ∈ F → x ∈ F := by
  intro x hx hxf
  have hw : ⁅x, t⁆ ∈ W := hxt x hx
  have hkx : k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
  have hkt' : k * t * k⁻¹ = t := by rw [hkt]; group
  have h1 : ⁅k * x * k⁻¹, t⁆ = k * ⁅x, t⁆ * k⁻¹ := by
    calc ⁅k * x * k⁻¹, t⁆ = ⁅k * x * k⁻¹, k * t * k⁻¹⁆ := by rw [hkt']
      _ = k * ⁅x, t⁆ * k⁻¹ := by simp only [commutatorElement_def]; group
  have hft : ⁅k * x * k⁻¹ * x⁻¹, t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hFt _ hxf)
  have hfw : (k * x * k⁻¹ * x⁻¹) * ⁅x, t⁆ = ⁅x, t⁆ * (k * x * k⁻¹ * x⁻¹) :=
    hI _ (hFI hxf) _ (hFI (hWF hw))
  have h2 : ⁅(k * x * k⁻¹ * x⁻¹) * x, t⁆ = ⁅x, t⁆ := by
    calc ⁅(k * x * k⁻¹ * x⁻¹) * x, t⁆
        = (k * x * k⁻¹ * x⁻¹) * ⁅x, t⁆ * (k * x * k⁻¹ * x⁻¹)⁻¹ * ⁅k * x * k⁻¹ * x⁻¹, t⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x, t⁆ := by rw [hft, hfw]; group
  have h3 : k * ⁅x, t⁆ * k⁻¹ = ⁅x, t⁆ := by
    rw [← h1, hkx, h2]
  exact hker x hx (commutatorElement_eq_one_iff_mul_comm.mp (hfix _ hw h3))

private lemma y7a_zpowers_sq {x v : G} (hx : x * x = 1) (hv : v ∈ zpowers x) :
    v = 1 ∨ v = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    have hn : n = 2 * (n / 2) := by omega
    rw [hn, zpow_mul, hx2, one_zpow]
  · right
    have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

private lemma y7a_conj_inv_mem {W : Subgroup G} {k : G} (hk3 : k ^ 3 = 1)
    (hkW : ∀ w ∈ W, k * w * k⁻¹ ∈ W) : ∀ w ∈ W, k⁻¹ * w * k ∈ W := by
  intro w hw
  have h1 : k * k = k⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hk3)).symm
  have h2 : k⁻¹ * k⁻¹ = k := by rw [← mul_inv_rev, h1, inv_inv]
  have h3 := hkW _ (hkW w hw)
  have h4 : k⁻¹ * w * k = k * (k * w * k⁻¹) * k⁻¹ := by
    calc k⁻¹ * w * k = (k * k) * w * (k⁻¹ * k⁻¹) := by rw [h1, h2]
      _ = k * (k * w * k⁻¹) * k⁻¹ := by group
  rw [h4]
  exact h3

theorem y7a_fpf_B {B F W : Subgroup G} {k f₀ : G}
    (hFB : F ≤ B) (hWF : W ≤ F) (hF : F = W ⊔ zpowers f₀)
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hFsq : ∀ f ∈ F, f * f = 1)
    (hf₀ : f₀ ∈ F) (hf₀W : f₀ ∉ W) (hWB : ∀ w ∈ W, ∀ b ∈ B, b * w = w * b)
    (hBB : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ W)
    (hcentF : ∀ b ∈ B, (∀ f ∈ F, b * f = f * b) → b ∈ F)
    (hkB : ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hkF : ∀ f ∈ F, k * f * k⁻¹ ∈ F)
    (hkW : ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hk3 : k ^ 3 = 1)
    (hfix : ∀ w ∈ W, k * w * k⁻¹ = w → w = 1) :
    ∀ b ∈ B, k * b * k⁻¹ * b⁻¹ ∈ F → b ∈ F := by
  intro b hb hu
  have hkW' := y7a_conj_inv_mem hk3 hkW
  have hf₀sq : f₀ * f₀ = 1 := hFsq f₀ hf₀
  have hWf₀ : ∀ w ∈ W, ∀ v ∈ zpowers f₀, w * v = v * w := by
    intro w hw v hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_right (hFab w (hWF hw) f₀ hf₀) n)).eq
  have hFelts : ∀ f ∈ F, ∃ w ∈ W, f = w ∨ f = w * f₀ := by
    intro f hf
    rw [hF] at hf
    obtain ⟨w, hw, v, hv, rfl⟩ := y7a_sup_elems hWf₀ f hf
    rcases y7a_zpowers_sq hf₀sq hv with rfl | rfl
    · exact ⟨w, hw, Or.inl (mul_one w)⟩
    · exact ⟨w, hw, Or.inr rfl⟩
  obtain ⟨w₀, hw₀, hg⟩ : ∃ w₀ ∈ W, k * f₀ * k⁻¹ = w₀ * f₀ := by
    obtain ⟨w, hw, h | h⟩ := hFelts _ (hkF f₀ hf₀)
    · exfalso
      apply hf₀W
      have : f₀ = k⁻¹ * (k * f₀ * k⁻¹) * k := by group
      rw [this, h]
      exact hkW' w hw
    · exact ⟨w, hw, h⟩
  have hu' : k * b * k⁻¹ = (k * b * k⁻¹ * b⁻¹) * b := by group
  set u := k * b * k⁻¹ * b⁻¹ with hudef
  have hc : ⁅b, f₀⁆ ∈ W := hBB b hb f₀ (hFB hf₀)
  have hg' : w₀ * f₀ ∈ F := mul_mem (hWF hw₀) hf₀
  have hbg : ⁅b, w₀ * f₀⁆ ∈ W := hBB b hb _ (hFB hg')
  have e1 : ⁅u * b, w₀ * f₀⁆ = ⁅b, w₀ * f₀⁆ := by
    have hcomm : ⁅u, w₀ * f₀⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hFab u hu _ hg')
    have hcomm' : u * ⁅b, w₀ * f₀⁆ = ⁅b, w₀ * f₀⁆ * u := hFab u hu _ (hWF hbg)
    calc ⁅u * b, w₀ * f₀⁆ = u * ⁅b, w₀ * f₀⁆ * u⁻¹ * ⁅u, w₀ * f₀⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅b, w₀ * f₀⁆ := by rw [hcomm, hcomm']; group
  have e2 : ⁅b, w₀ * f₀⁆ = ⁅b, f₀⁆ := by
    have hbw : ⁅b, w₀⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hWB w₀ hw₀ b hb)
    have hww : w₀ * ⁅b, f₀⁆ = ⁅b, f₀⁆ * w₀ := hFab w₀ (hWF hw₀) _ (hWF hc)
    calc ⁅b, w₀ * f₀⁆ = ⁅b, w₀⁆ * (w₀ * ⁅b, f₀⁆ * w₀⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅b, f₀⁆ := by rw [hbw, hww]; group
  have e3 : ⁅k * b * k⁻¹, k * f₀ * k⁻¹⁆ = k * ⁅b, f₀⁆ * k⁻¹ := by
    simp only [commutatorElement_def]; group
  have e4 : k * ⁅b, f₀⁆ * k⁻¹ = ⁅b, f₀⁆ := by
    rw [← e3, hg, hu', e1, e2]
  have e5 : ⁅b, f₀⁆ = 1 := hfix _ hc e4
  have hbf₀ : b * f₀ = f₀ * b := commutatorElement_eq_one_iff_mul_comm.mp e5
  apply hcentF b hb
  intro f hf
  obtain ⟨w, hw, h | h⟩ := hFelts f hf
  · rw [h]
    exact hWB w hw b hb
  · rw [h]
    calc b * (w * f₀) = (b * w) * f₀ := by rw [mul_assoc]
      _ = (w * b) * f₀ := by rw [hWB w hw b hb]
      _ = w * (b * f₀) := by rw [mul_assoc]
      _ = w * (f₀ * b) := by rw [hbf₀]
      _ = (w * f₀) * b := by rw [mul_assoc]

private lemma y7a_relIndex_two_mul_mem {H K : Subgroup G} (hidx : H.relIndex K = 2) {a b : G}
    (haK : a ∈ K) (hbK : b ∈ K) (haH : a ∉ H) (hbH : b ∉ H) : a * b ∈ H := by
  have h2 : (H.subgroupOf K).index = 2 := hidx
  have key := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) h2
    (a := ⟨a, haK⟩) (b := ⟨b, hbK⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  exact key.mpr ⟨fun h => absurd h haH, fun h => absurd h hbH⟩

theorem y7a_B_gen {B F E : Subgroup G} {k : G}
    (hcB : Nat.card ↥B = 32) (hcF : Nat.card ↥F = 8) (hFB : F ≤ B) (hEB : E ≤ B)
    (hEF : ¬ E ≤ F) (hFn : ∀ b ∈ B, ∀ f ∈ F, b * f * b⁻¹ ∈ F)
    (hkB : ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hkF : ∀ f ∈ F, k * f * k⁻¹ ∈ F) (hk3 : k ^ 3 = 1)
    (hfpf : ∀ b ∈ B, k * b * k⁻¹ * b⁻¹ ∈ F → b ∈ F) :
    B ≤ F ⊔ E ⊔ conjSub k E := by
  have hkF' := y7a_conj_inv_mem hk3 hkF
  have hEk : conjSub k E ≤ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub.mp hx
    exact hkB y (hEB hy)
  have hle : F ⊔ E ⊔ conjSub k E ≤ B := sup_le (sup_le hFB hEB) hEk
  obtain ⟨e₀, he₀E, he₀F⟩ := SetLike.not_le_iff_exists.mp hEF
  have he₀B' : e₀ ∈ F ⊔ E ⊔ conjSub k E :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right he₀E)
  have he₁B' : k * e₀ * k⁻¹ ∈ F ⊔ E ⊔ conjSub k E :=
    Subgroup.mem_sup_right (mem_conjSub.mpr ⟨e₀, he₀E, rfl⟩)
  have he₁F : k * e₀ * k⁻¹ ∉ F := by
    intro h
    apply he₀F
    have := hkF' _ h
    rwa [show k⁻¹ * (k * e₀ * k⁻¹) * k = e₀ by group] at this
  have hFB' : F ≤ F ⊔ E ⊔ conjSub k E := le_sup_left.trans le_sup_left
  have hdvd : Nat.card ↥(F ⊔ E ⊔ conjSub k E) ∣ 32 := hcB ▸ Subgroup.card_dvd_of_le hle
  have hdvdF : 8 ∣ Nat.card ↥(F ⊔ E ⊔ conjSub k E) := hcF ▸ Subgroup.card_dvd_of_le hFB'
  have hne : Nat.card ↥(F ⊔ E ⊔ conjSub k E) ≠ 8 := by
    intro h8
    have hFeq : F = F ⊔ E ⊔ conjSub k E := Subgroup.eq_of_le_of_card_ge hFB' (by omega)
    exact he₀F (hFeq ▸ he₀B')
  have h32 : Nat.card ↥(F ⊔ E ⊔ conjSub k E) = 32 := by
    by_contra h32
    have hle32 : Nat.card ↥(F ⊔ E ⊔ conjSub k E) ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(F ⊔ E ⊔ conjSub k E) := Nat.card_pos
    have hne24 : Nat.card ↥(F ⊔ E ⊔ conjSub k E) ≠ 24 := by
      intro h24
      rw [h24] at hdvd
      norm_num at hdvd
    have h16 : Nat.card ↥(F ⊔ E ⊔ conjSub k E) = 16 := by
      obtain ⟨m, hm⟩ := hdvdF
      omega
    have hidx : F.relIndex (F ⊔ E ⊔ conjSub k E) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := F) (K := F ⊔ E ⊔ conjSub k E)
      rw [inf_of_le_left hFB', hcF, h16] at h
      omega
    have hprod := y7a_relIndex_two_mul_mem hidx (Subgroup.inv_mem _ he₀B') he₁B'
      (fun h => he₀F (by simpa using Subgroup.inv_mem _ h)) he₁F
    apply he₀F
    apply hfpf e₀ (hEB he₀E)
    have := hFn e₀ (hEB he₀E) _ hprod
    rwa [show e₀ * (e₀⁻¹ * (k * e₀ * k⁻¹)) * e₀⁻¹ = k * e₀ * k⁻¹ * e₀⁻¹ by group] at this
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm.le

end CFSG.OddStandard.HigherRank.YamadaG23
