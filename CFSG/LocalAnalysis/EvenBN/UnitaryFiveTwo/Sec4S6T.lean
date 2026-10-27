module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6R
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3G
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6N

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem card_le_two_pow_six_of_dvd {X : Type*} [Group X] {T : Subgroup X} (hT : IsPGroup 2 ↥T)
    [Finite T] (hdvd : Nat.card ↥T ∣ 25920) : Nat.card ↥T ≤ 2 ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  rw [hn] at hdvd ⊢
  have hn6 : n ≤ 6 := by
    by_contra hlt
    have h7 : 2 ^ 7 ∣ 25920 := (pow_dvd_pow 2 (by omega : 7 ≤ n)).trans hdvd
    norm_num at h7
  exact Nat.pow_le_pow_right (by norm_num) hn6

section Q



@[expose] noncomputable def Data.Q₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) : Subgroup G :=
  ((d.X₂ ⊔ d.F).comap (Data.theta h hf)).map K₀.subtype

theorem Data.mem_Q₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) {x : G} :
    x ∈ Data.Q₀ h hf ↔ ∃ hx : x ∈ K₀, Data.theta h hf ⟨x, hx⟩ ∈ d.X₂ ⊔ d.F := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hx, hθ⟩
    exact ⟨⟨x, hx⟩, hθ, rfl⟩

theorem Data.Q₀_le_K₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) : Data.Q₀ h hf ≤ K₀ := by
  rintro _ ⟨k, -, rfl⟩
  exact k.2

theorem Data.U₁_le_Q₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) : Data.U₁ h hf ≤ Data.Q₀ h hf := by
  intro x hx
  obtain ⟨hx0, hθ⟩ := (Data.mem_U₁ h hf).1 hx
  exact (Data.mem_Q₀ h hf).2 ⟨hx0, mem_sup_left hθ⟩

section
variable (hKU : d.KUnitary)
include hKU

theorem Data.I_le_Q₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) : d.Y ⊓ K₀ ≤ Data.Q₀ h hf := by
  intro x hx
  refine (Data.mem_Q₀ h hf).2 ⟨hx.2, mem_sup_right ?_⟩
  exact (h.theta_mem_F_iff hKU hf ⟨x, hx.2⟩).1 hx.1

theorem Data.card_Q₀ (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) :
    Nat.card ↥(Data.Q₀ h hf) = 2 ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : d.X₂ ⊔ d.F ≤ (Data.theta h hf).range := by
    rw [Data.range_theta h hKU hf]
    exact d.X₂_sup_F_le_K₃
  have hmap : ((d.X₂ ⊔ d.F).comap (Data.theta h hf)).map (Data.theta h hf) = d.X₂ ⊔ d.F :=
    Subgroup.map_comap_eq_self hle
  have hc : Nat.card ↥((d.X₂ ⊔ d.F).comap (Data.theta h hf)) = Nat.card ↥(d.X₂ ⊔ d.F) := by
    rw [← Subgroup.card_map_of_injective (Data.theta_injective h hf), hmap]
  have hQ : Nat.card ↥(Data.Q₀ h hf) = Nat.card ↥(d.X₂ ⊔ d.F) := by
    rw [Data.Q₀, Subgroup.card_map_of_injective K₀.subtype_injective, hc]
  have hp : IsPGroup 2 ↥(d.X₂ ⊔ d.F) := (IsPGroup.of_card d.card_S).to_le d.X₂_sup_F_le_S
  have hdvd : Nat.card ↥(d.X₂ ⊔ d.F) ∣ 25920 := by
    have h1 : Nat.card ↥(d.X₂ ⊔ d.F) ∣ Nat.card ↥d.K₃ :=
      Subgroup.card_dvd_of_le d.X₂_sup_F_le_K₃
    have h2 : Nat.card ↥d.K₃ ∣ 25920 := by
      rw [Data.K₃, d.card_pull]
      exact card_K₃sub_dvd
    exact h1.trans h2
  have hup := card_le_two_pow_six_of_dvd hp hdvd
  have hlow := d.card_X₂_sup_F
  rw [hQ]
  omega

end

section
variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.card_Q₀_sup_tc : Nat.card ↥(Data.Q₀ h hf ⊔ d.tc (Data.Q₀ h hf)) = 2 ^ 12 := by
  have hc : ∀ a ∈ Data.Q₀ h hf, ∀ b ∈ d.tc (Data.Q₀ h hf), a * b = b * a := fun a ha b hb =>
    hf.comm_elem a (Data.Q₀_le_K₀ h hf ha) b (h.tc_mono (Data.Q₀_le_K₀ h hf) hb)
  have hi : Data.Q₀ h hf ⊓ d.tc (Data.Q₀ h hf) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf (Data.Q₀_le_K₀ h hf) (h.tc_mono (Data.Q₀_le_K₀ h hf))).trans
      hf.inf_tc.le)
  rw [← Nat.card_congr (KProd.prodEquivSup _ _ hc hi).toEquiv, Nat.card_prod, Data.card_tc,
    Data.card_Q₀ hKU h hf]
  norm_num

include h hKU in
theorem Data.Hyp.M_le_Q₀_sup :
    d.D₁ ⊓ centralizer ({d.e₂} : Set G) ≤ Data.Q₀ h hf ⊔ d.tc (Data.Q₀ h hf) := by
  have hf₁ := Data.IsUnitaryFactor.tc_factor h hf
  intro m hm
  have hmK : m ∈ d.K := h.M_le_K (h.Y_le_K' hKU) (Data.Hyp.K₃_le_K hKU) hm
  have hmK' : m ∈ K₀ ⊔ d.tc K₀ := by rw [← hf.K_eq_tc]; exact hmK
  obtain ⟨a, ha, b, hb, hmab⟩ := KProd.exists_mul_of_mem_sup_of_comm hf.comm_elem hmK'
  have hθa : a * (d.t * a * d.t) ∈ d.X₂ ⊔ d.F := h.theta_component_mem hKU hf hm ha hb hmab
  have hba : b * a = a * b := (hf.comm_elem a ha b hb).symm
  have hθb : b * (d.t * b * d.t) ∈ d.X₂ ⊔ d.F := by
    refine h.theta_component_mem hKU hf₁ hm hb ?_ (by rw [hmab, hba])
    rw [h.tc_tc]
    exact ha
  have haQ : a ∈ Data.Q₀ h hf :=
    (Data.mem_Q₀ h hf).2 ⟨ha, by rw [Data.theta_apply]; exact hθa⟩
  have hbQ : b ∈ d.tc (Data.Q₀ h hf) := by
    rw [h.mem_tc]
    have htb : d.t * b * d.t ∈ K₀ := (h.mem_tc).1 hb
    refine (Data.mem_Q₀ h hf).2 ⟨htb, ?_⟩
    rw [Data.theta_apply]
    show (d.t * b * d.t) * (d.t * (d.t * b * d.t) * d.t) ∈ d.X₂ ⊔ d.F
    rw [h.t_conj_conj b, hf.comm_elem _ htb b hb]
    exact hθb
  rw [hmab]
  exact mul_mem (mem_sup_left haQ) (mem_sup_right hbQ)

include h hKU in
theorem Data.Hyp.Y_le_Q₀_sup : d.Y ≤ Data.Q₀ h hf ⊔ d.tc (Data.Q₀ h hf) := by
  rw [h.Y_eq_I_sup hKU hf]
  exact sup_le (Data.I_le_Q₀ hKU h hf |>.trans le_sup_left)
    ((h.tc_mono (Data.I_le_Q₀ hKU h hf)).trans le_sup_right)

include h hKU in
theorem Data.Hyp.M_sup_Y_eq :
    d.M ⊔ d.Y = Data.Q₀ h hf ⊔ d.tc (Data.Q₀ h hf) := by
  have hle : d.M ⊔ d.Y ≤ Data.Q₀ h hf ⊔ d.tc (Data.Q₀ h hf) :=
    sup_le (h.M_le_Q₀_sup hKU hf) (h.Y_le_Q₀_sup hKU hf)
  have hN : d.M ≤ normalizer (d.Y : Set G) := h.M_le_normalizer_Y hKU
  have e := card_sup_mul_card_inf_of_le_normalizer d.Y d.M hN
  rw [sup_comm, inf_comm, h.M_inf_Y, h.card_V₂, h.card_Y, h.card_M] at e
  have hcard : Nat.card ↥(d.M ⊔ d.Y) = 2 ^ 12 := by
    have : Nat.card ↥(d.M ⊔ d.Y) * 2 ^ 6 = 2 ^ 12 * 2 ^ 6 := by rw [e]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Data.card_Q₀_sup_tc h hKU hf]

include h hKU in
theorem Data.Hyp.U₁_le_M_sup_Y : Data.U₁ h hf ≤ d.M ⊔ d.Y := by
  rw [h.M_sup_Y_eq hKU hf]
  exact (Data.U₁_le_Q₀ h hf).trans le_sup_left

include h hKU in
theorem Data.Hyp.tcU₁_le_M_sup_Y : d.tc (Data.U₁ h hf) ≤ d.M ⊔ d.Y := by
  rw [h.M_sup_Y_eq hKU hf]
  exact (h.tc_mono (Data.U₁_le_Q₀ h hf)).trans le_sup_right

end

end Q

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
