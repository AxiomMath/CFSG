module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45TwoChi
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Parts

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS

namespace TwoCfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem no_order_fifteen :
    ∀ c ∈ centralizer ({t} : Set G), c ^ 15 = 1 → c ^ 3 = 1 ∨ c ^ 5 = 1 := by
  intro c hc h15
  obtain ⟨e⟩ := h.hJ
  rw [h.hC] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute h.hcomm).1 hc
  have hab : Commute a b := h.hcomm a ha b hb
  have haa := h.mul_self_of_mem_fourGroup ha
  have ha15 : a ^ 15 = a := by
    have h2 : a ^ 2 = 1 := by rw [pow_two]; exact haa
    calc a ^ 15 = a ^ (2 * 7 + 1) := by norm_num
      _ = (a ^ 2) ^ 7 * a := by rw [pow_succ, pow_mul]
      _ = a := by rw [h2, one_pow, one_mul]
  have hab15 : a * b ^ 15 = 1 := by
    rw [hab.mul_pow, ha15] at h15
    exact h15
  have haJ : a ∈ J := by
    have : a = (b ^ 15)⁻¹ := eq_inv_of_mul_eq_one_left hab15
    rw [this]
    exact J.inv_mem (J.pow_mem hb 15)
  have ha1 : a = 1 := by
    have : a ∈ fourGroup t v ⊓ J := ⟨ha, haJ⟩
    rw [h.hdisj, Subgroup.mem_bot] at this
    exact this
  subst ha1
  rw [one_mul] at hab15 ⊢
  have h15' : (e ⟨b, hb⟩) ^ 15 = 1 := by
    rw [← map_pow]
    have : (⟨b, hb⟩ : ↥J) ^ 15 = 1 := Subtype.ext hab15
    rw [this, map_one]
  rcases perm_five_no_orders.2 _ h15' with h3 | h5
  · left
    have : (⟨b, hb⟩ : ↥J) ^ 3 = 1 := e.injective (by rw [map_pow, h3, map_one])
    simpa using congrArg Subtype.val this
  · right
    have : (⟨b, hb⟩ : ↥J) ^ 5 = 1 := e.injective (by rw [map_pow, h5, map_one])
    simpa using congrArg Subtype.val this

end TwoCfg

theorem noTwoCfgPSp45_holds :
    NoTwoCfgPSp45 := by
  intro G _ _ S hSn hS hcent t v J h _
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  have h480 := h.card_centralizer htop
  obtain ⟨ψ, hψ⟩ := exists_pgsp45Emb S hS hcent
  obtain ⟨hS4, hsimple⟩ := card_and_simple_of_lieModel hS
  have hker := ker_chiPG_le_range S hsimple hS4 hψ
  obtain ⟨g, hg⟩ := hψ.exists_conj_tau1 h.ht h.no_order_fifteen (by rw [h480]; norm_num)
    (by rw [h480]; norm_num)
  have hv : ∀ w ∈ centralizer ({t} : Set G), v * w = w * v := fun w hw =>
    h.fourGroup_central (h.mem_fourGroup.2 (Or.inr (Or.inr (Or.inl rfl)))) hw
  have hvt : ψ v * ψ t = ψ t * ψ v := by rw [← map_mul, ← map_mul, ← h.tv_comm]
  have hxx : g * ψ v * g⁻¹ * (g * ψ v * g⁻¹) = 1 := by
    calc g * ψ v * g⁻¹ * (g * ψ v * g⁻¹) = g * ψ (v * v) * g⁻¹ := by rw [map_mul]; group
      _ = 1 := by rw [h.hv, map_one]; group
  have h0 : g * ψ v * g⁻¹ * mkPG pgTau1 pgTau1_so = mkPG pgTau1 pgTau1_so * (g * ψ v * g⁻¹) := by
    rw [← hg]
    calc g * ψ v * g⁻¹ * (g * ψ t * g⁻¹) = g * (ψ v * ψ t) * g⁻¹ := by group
      _ = g * (ψ t * ψ v) * g⁻¹ := by rw [hvt]
      _ = g * ψ t * g⁻¹ * (g * ψ v * g⁻¹) := by group
  have τ1c : ∀ {z : PGSp45}, chiPG z = 1 →
      z * mkPG pgTau1 pgTau1_so = mkPG pgTau1 pgTau1_so * z →
      g * ψ v * g⁻¹ * z = z * (g * ψ v * g⁻¹) := fun hz hzτ =>
    commute_conj_of_central hψ hker hv hg hz hzτ
  have hx := eq_one_or_tau1_of_commute (g * ψ v * g⁻¹) hxx h0
    (τ1c chi_sf (pg_ext (by simpa only [pg_mul_val, mkPG_val] using pgSf0_comm)))
    (τ1c chi_yy (pg_ext (by simpa only [pg_mul_val, mkPG_val] using pgY_comm)))
    (τ1c chi_c5 (pg_ext (by simpa only [pg_mul_val, mkPG_val] using mC5_comm)))
  rcases hx with hx | hx
  · apply h.v_ne_one htop
    apply hψ.inj
    rw [map_one]
    have : ψ v = g⁻¹ * (g * ψ v * g⁻¹) * g := by group
    rw [this, hx]
    group
  · apply h.v_ne_t htop
    apply hψ.inj
    have h1 : g * ψ v * g⁻¹ = g * ψ t * g⁻¹ := hx.trans hg.symm
    exact mul_left_cancel (mul_right_cancel h1)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
