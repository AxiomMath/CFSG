module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N3

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace S56

theorem comm_cancel {G : Type*} [Group G] {p k u v : G} (hpv : p * v * p⁻¹ = u * v)
    (hkv : k * v * k⁻¹ = u * v) (hpu : p * u = u * p) (hku : k * u = u * k) :
    p * k⁻¹ * v = v * (p * k⁻¹) := by
  have hk' : k⁻¹ * u * k = u := by
    calc k⁻¹ * u * k = k⁻¹ * (u * k) := by group
      _ = k⁻¹ * (k * u) := by rw [hku]
      _ = u := by group
  have h1 : k⁻¹ * v * k = u⁻¹ * v := by
    calc k⁻¹ * v * k = u⁻¹ * (k⁻¹ * u * k) * (k⁻¹ * v * k) := by rw [hk']; group
      _ = u⁻¹ * (k⁻¹ * (u * v) * k) := by group
      _ = u⁻¹ * (k⁻¹ * (k * v * k⁻¹) * k) := by rw [hkv]
      _ = u⁻¹ * v := by group
  have hpu' : p * u⁻¹ * p⁻¹ = u⁻¹ := by
    calc p * u⁻¹ * p⁻¹ = (p * u * p⁻¹)⁻¹ := by group
      _ = u⁻¹ := by rw [hpu]; group
  have h2 : p * k⁻¹ * v * (p * k⁻¹)⁻¹ = v := by
    calc p * k⁻¹ * v * (p * k⁻¹)⁻¹ = p * (k⁻¹ * v * k) * p⁻¹ := by group
      _ = p * (u⁻¹ * v) * p⁻¹ := by rw [h1]
      _ = (p * u⁻¹ * p⁻¹) * (p * v * p⁻¹) := by group
      _ = u⁻¹ * (u * v) := by rw [hpu', hpv]
      _ = v := by group
  calc p * k⁻¹ * v = (p * k⁻¹ * v * (p * k⁻¹)⁻¹) * (p * k⁻¹) := by group
    _ = v * (p * k⁻¹) := by rw [h2]

theorem conj_mul {G : Type*} [Group G] {k k' u u' v : G} (hk : k * v * k⁻¹ = u * v)
    (hk' : k' * v * k'⁻¹ = u' * v) (hku' : k * u' = u' * k) :
    (k * k') * v * (k * k')⁻¹ = (u' * u) * v := by
  have h1 : k * u' * k⁻¹ = u' := by rw [hku']; group
  calc (k * k') * v * (k * k')⁻¹ = k * (k' * v * k'⁻¹) * k⁻¹ := by group
    _ = k * (u' * v) * k⁻¹ := by rw [hk']
    _ = (k * u' * k⁻¹) * (k * v * k⁻¹) := by group
    _ = u' * (u * v) := by rw [h1, hk]
    _ = (u' * u) * v := by group

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_P0_comm_F_le_U10 (h49 : d.Thm49Statement) (hd : d.Hyp) {p f : G}
    (hp : p ∈ d.s56P0) (hf : f ∈ d.F) : p * f * p⁻¹ * f⁻¹ ∈ d.s56U10 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyNC, -, -, -, -, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  set Ŵ := commSub d.s56P0 d.s56U10 d.F (fun _ ha _ hb => hd.s56_F_comm ha hb)
    (s56_U10_le_F d) with hŴ
  obtain ⟨f₀, hf₀F, hf₀U, hf₀c⟩ := exists_comm_mem_of_isPGroup (p := 2) (P := d.s56P0)
    (U := d.s56U10) (V := d.F) (s56_P0_isPGroup d) hd.s56_F_le_P0
    (fun x hx u hu => hd.s56_N_conj_U10 h49 (s56_P0_le_N d hx) hu)
    (fun x hx v hv => hd.s56_N_conj_F h49 (s56_P0_le_N d hx) hv) (s56_F_not_le_U10 d hd)
  have hf₀W : f₀ ∈ Ŵ := ⟨hf₀F, hf₀c⟩
  have hŴF : Ŵ ≤ d.F := fun _ h => h.1
  have hU10 : d.s56U10 ≤ Ŵ := fun u hu => ⟨s56_U10_le_F d hu, fun p hp =>
    mul_mem (hd.s56_N_conj_U10 h49 (s56_P0_le_N d hp) hu) (inv_mem hu)⟩
  have hf₁F : d.s56Y * f₀ * d.s56Y⁻¹ ∈ d.F := hd.s56_N_conj_F h49 hyN hf₀F
  have hf₁W : d.s56Y * f₀ * d.s56Y⁻¹ ∈ Ŵ := by
    refine ⟨hf₁F, fun x hx => ?_⟩
    have hx' : d.s56Y⁻¹ * x * d.s56Y⁻¹⁻¹ ∈ d.s56P0 := s56_N_conj_P0 d (inv_mem hyN) hx
    have h := hd.s56_N_conj_U10 h49 hyN (hf₀c _ hx')
    have e : d.s56Y * (d.s56Y⁻¹ * x * d.s56Y⁻¹⁻¹ * f₀ * (d.s56Y⁻¹ * x * d.s56Y⁻¹⁻¹)⁻¹ * f₀⁻¹) *
        d.s56Y⁻¹ = x * (d.s56Y * f₀ * d.s56Y⁻¹) * x⁻¹ * (d.s56Y * f₀ * d.s56Y⁻¹)⁻¹ := by
      group
    rwa [e] at h
  have hf₁U : d.s56Y * f₀ * d.s56Y⁻¹ ∉ d.s56U10 := fun h => hf₀U (by
    have := hd.s56_N_conj_U10 h49 (inv_mem hyN) h
    simpa [mul_assoc] using this)
  have hcomm : d.s56Y * f₀ * d.s56Y⁻¹ * f₀⁻¹ ∉ d.s56U10 := s56_Y_comm_not_mem hf₀F hf₀U
  have hd32 : Nat.card Ŵ ∣ 32 := by
    have := Subgroup.card_dvd_of_le hŴF
    rwa [hd.B_facts.1] at this
  have hd8 : 8 ∣ Nat.card Ŵ := by
    have := Subgroup.card_dvd_of_le hU10
    rwa [s56_card_U10] at this
  have hne8 : Nat.card Ŵ ≠ 8 := fun h8 => hf₀U (by
    have := Subgroup.eq_of_le_of_card_ge hU10 (by rw [h8, s56_card_U10])
    rw [this]; exact hf₀W)
  have hne16 : Nat.card Ŵ ≠ 16 := fun h16 => hcomm (by
    have := mul_inv_mem_of_card_eq_two_mul hU10 (by rw [h16, s56_card_U10]) hf₁W hf₀W hf₁U hf₀U
    exact this)
  have h32 : Nat.card Ŵ = 32 := by
    obtain ⟨m, hm⟩ := hd8
    rw [hm] at hd32 hne8 hne16 ⊢
    have hm4 : m ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8)
      (by simpa using hd32)
    have hle : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
    interval_cases m <;> simp_all
  have hŴ' : Ŵ = d.F := Subgroup.eq_of_le_of_card_ge hŴF (by rw [h32, hd.B_facts.1])
  have hfW : f ∈ Ŵ := by rw [hŴ']; exact hf
  exact hfW.2 p hp

theorem s56_P_le_P0 (d : Data G) : d.s56P ≤ d.s56P0 := by
  rw [s56P_def]
  exact inf_le_left

theorem Hyp.s56_B_le_P (hd : d.Hyp) : d.B ≤ d.s56P := fun b hb => by
  rw [s56P_def]
  exact mem_inf.2 ⟨hd.s56_B_le_P0 hb, mem_centralizer_iff.2 fun f hf =>
    congrArg Subtype.val (hd.B_facts.2.2.1.1.is_comm.comm ⟨f, s56_F_le_B d hf⟩ ⟨b, hb⟩)⟩

theorem s56_P10_le_P0 (d : Data G) : d.s56P10 ≤ d.s56P0 := by
  rw [s56P10_def]
  exact inf_le_left

theorem Hyp.s56_P0_comm_U10_mem_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {p f : G}
    (hp : p ∈ d.s56P0) (hf : f ∈ d.s56U10) : p * f * p⁻¹ * f⁻¹ ∈ d.s56U11 :=
  ((hd.s56_commSub_U11_eq_U10 h49 f).2 hf).2 p hp

theorem Hyp.s56_mem_P10_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G} (hp : p ∈ d.s56P0) :
    p ∈ d.s56P10 ↔ p * d.pv 10 = d.pv 10 * p := by
  rw [s56P10_def]
  constructor
  · intro h
    exact (mem_centralizer_iff.1 (mem_inf.1 h).2 _ (s56_pv10_mem_U10 d)).symm
  · intro h
    refine mem_inf.2 ⟨hp, mem_centralizer_iff.2 fun x hx => ?_⟩
    rcases s56_U10_cases hx with hx | ⟨u, hu, rfl⟩
    · exact (hd.s56_P0_comm_U11 h49 hp hx).symm
    · have hpu := hd.s56_P0_comm_U11 h49 hp hu
      calc d.pv 10 * u * p = d.pv 10 * (u * p) := by group
        _ = d.pv 10 * (p * u) := by rw [hpu]
        _ = (d.pv 10 * p) * u := by group
        _ = (p * d.pv 10) * u := by rw [h]
        _ = p * (d.pv 10 * u) := by group

theorem Hyp.s56_N_conj_P10 (h49 : d.Thm49Statement) (hd : d.Hyp) {n q : G} (hn : n ∈ d.N)
    (hq : q ∈ d.s56P10) : n * q * n⁻¹ ∈ d.s56P10 := by
  rw [s56P10_def] at hq ⊢
  obtain ⟨hqP, hqC⟩ := mem_inf.1 hq
  refine mem_inf.2 ⟨s56_N_conj_P0 d hn hqP, mem_centralizer_iff.2 fun u hu => ?_⟩
  have hu' : n⁻¹ * u * n⁻¹⁻¹ ∈ d.s56U10 := hd.s56_N_conj_U10 h49 (inv_mem hn) hu
  have h := mem_centralizer_iff.1 hqC _ hu'
  calc u * (n * q * n⁻¹) = n * ((n⁻¹ * u * n⁻¹⁻¹) * q) * n⁻¹ := by group
    _ = n * (q * (n⁻¹ * u * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = n * q * n⁻¹ * u := by group

theorem Hyp.s56_exists_K_comm (h49 : d.Thm49Statement) (hd : d.Hyp) {u : G}
    (hu : u ∈ d.s56U11) : ∃ k ∈ d.s56K, k * d.pv 10 * k⁻¹ = u * d.pv 10 := by
  obtain ⟨hk₁, hk₂, e₁, e₂⟩ := s56_kElt_facts (d := d)
  have hK := hd.s56_K_le_P0 h49
  rcases s56_mem_U11_iff.1 hu with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, by group⟩
  · exact ⟨_, hk₂, e₂⟩
  · exact ⟨_, hk₁, e₁⟩
  · refine ⟨_, mul_mem hk₂ hk₁, ?_⟩
    have hc := hd.s56_P0_comm_U11 h49 (hK hk₂) (s56_z_mem_U11 d)
    have hzv : d.z * d.pv 11 = d.pv 11 * d.z :=
      hd.s56_E_comm hd.s56_z_mem_E (s56_pv11_mem_E d)
    rw [S56.conj_mul e₂ e₁ hc, hzv]

theorem Hyp.s56_N_decomp_P10 (h49 : d.Thm49Statement) (hd : d.Hyp) {n : G} (hn : n ∈ d.N) :
    ∃ q ∈ d.s56P10, ∃ c ∈ d.N ⊓ centralizer ({d.t} : Set G), n = q * c := by
  obtain ⟨p, hp, c, hc, rfl⟩ := hd.s56_N_decomp h49 hn
  have hu := hd.s56_P0_comm_U10_mem_U11 h49 hp (s56_pv10_mem_U10 d)
  obtain ⟨u, hudef⟩ : ∃ u, u = p * d.pv 10 * p⁻¹ * (d.pv 10)⁻¹ := ⟨_, rfl⟩
  rw [← hudef] at hu
  obtain ⟨k, hkK, hk⟩ := hd.s56_exists_K_comm h49 hu
  have hkP := hd.s56_K_le_P0 h49 hkK
  have hpv : p * d.pv 10 * p⁻¹ = u * d.pv 10 := by rw [hudef]; group
  have hpu : p * u = u * p := hd.s56_P0_comm_U11 h49 hp hu
  have hku : k * u = u * k := hd.s56_P0_comm_U11 h49 hkP hu
  have hq : p * k⁻¹ * d.pv 10 = d.pv 10 * (p * k⁻¹) := S56.comm_cancel hpv hk hpu hku
  exact ⟨p * k⁻¹, (hd.s56_mem_P10_iff h49 (mul_mem hp (inv_mem hkP))).2 hq, k * c,
    mul_mem (hd.s56_K_le_CNt hkK) hc, by group⟩

@[expose] noncomputable def Hyp.s56Phi (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ↥d.s56P0 →* ↥d.s56U11 :=
  MonoidHom.mk' (fun p => ⟨p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹,
    hd.s56_P0_comm_U10_mem_U11 h49 p.2 (s56_pv10_mem_U10 d)⟩) fun p q => by
    apply Subtype.ext
    have hb := hd.s56_P0_comm_U10_mem_U11 h49 q.2 (s56_pv10_mem_U10 d)
    have ha := hd.s56_P0_comm_U10_mem_U11 h49 p.2 (s56_pv10_mem_U10 d)
    have hpb := hd.s56_P0_comm_U11 h49 p.2 hb
    have hba := hd.s56_F_comm (s56_U11_le_F d hb) (s56_U11_le_F d ha)
    show (p.1 * q.1) * d.pv 10 * (p.1 * q.1)⁻¹ * (d.pv 10)⁻¹ =
      (p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹) * (q.1 * d.pv 10 * q.1⁻¹ * (d.pv 10)⁻¹)
    calc (p.1 * q.1) * d.pv 10 * (p.1 * q.1)⁻¹ * (d.pv 10)⁻¹ =
        (p.1 * (q.1 * d.pv 10 * q.1⁻¹ * (d.pv 10)⁻¹) * p.1⁻¹) *
          (p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹) := by group
      _ = (q.1 * d.pv 10 * q.1⁻¹ * (d.pv 10)⁻¹) * (p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹) := by
          rw [show p.1 * (q.1 * d.pv 10 * q.1⁻¹ * (d.pv 10)⁻¹) * p.1⁻¹ =
            q.1 * d.pv 10 * q.1⁻¹ * (d.pv 10)⁻¹ by rw [hpb]; group]
      _ = _ := hba

theorem Hyp.s56Phi_apply (h49 : d.Thm49Statement) (hd : d.Hyp) (p : ↥d.s56P0) :
    ((hd.s56Phi h49 p : ↥d.s56U11) : G) = p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹ := rfl

theorem Hyp.s56_card_P0 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card d.s56P0 = 4 * Nat.card d.s56P10 := by
  have hsurj : (hd.s56Phi h49).range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨u, hu⟩ -
    obtain ⟨k, hkK, hk⟩ := hd.s56_exists_K_comm h49 hu
    refine ⟨⟨k, hd.s56_K_le_P0 h49 hkK⟩, Subtype.ext ?_⟩
    rw [hd.s56Phi_apply]
    calc k * d.pv 10 * k⁻¹ * (d.pv 10)⁻¹ = (k * d.pv 10 * k⁻¹) * (d.pv 10)⁻¹ := by group
      _ = u := by rw [hk]; group
  have hker : (hd.s56Phi h49).ker = d.s56P10.subgroupOf d.s56P0 := by
    ext p
    rw [MonoidHom.mem_ker, mem_subgroupOf, hd.s56_mem_P10_iff h49 p.2]
    constructor
    · intro h
      have h' : p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹ = 1 := congrArg Subtype.val h
      calc p.1 * d.pv 10 = (p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹) * (d.pv 10 * p.1) := by group
        _ = d.pv 10 * p.1 := by rw [h', one_mul]
    · intro h
      apply Subtype.ext
      show p.1 * d.pv 10 * p.1⁻¹ * (d.pv 10)⁻¹ = 1
      rw [h]; group
  have h := Subgroup.card_ker_mul_card_range (hd.s56Phi h49)
  rw [hsurj, hker, Subgroup.card_top] at h
  rw [Nat.card_congr (subgroupOfEquivOfLe (s56_P10_le_P0 d)).toEquiv] at h
  have hU : Nat.card ↥d.s56U11 = 4 := s56_card_U11 d
  rw [hU] at h
  rw [← h]; ring

theorem Hyp.s56_card_N_P0 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card d.N = 6 * Nat.card d.s56P0 := by
  obtain ⟨e⟩ := (hd.thm511 h49).2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥d.N)
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h1
  have h2 : Nat.card (CFSG.pCore 2 ↥d.N) = Nat.card d.s56P0 := (s56_card_P0_eq d).symm
  rw [h2] at h1
  rw [h1]
  norm_num [Nat.factorial]

theorem Hyp.s56_card_N (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card d.N = 24 * Nat.card d.s56P10 := by
  rw [hd.s56_card_N_P0 h49, hd.s56_card_P0 h49]; ring

theorem Hyp.s56_CN_U10_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.N ⊓ centralizer (d.s56U10 : Set G) = d.s56P10 := by
  rw [s56P10_def]
  apply le_antisymm
  · intro n hn
    obtain ⟨hnN, hnC⟩ := mem_inf.1 hn
    have hnC' : n ∈ d.N ⊓ centralizer (d.s56U11 : Set G) :=
      mem_inf.2 ⟨hnN, mem_centralizer_iff.2 fun u hu =>
        mem_centralizer_iff.1 hnC u (s56_U11_le_U10 d hu)⟩
    rw [hd.s56_CN_U11_eq h49] at hnC'
    exact mem_inf.2 ⟨hnC', hnC⟩
  · intro q hq
    obtain ⟨hqP, hqC⟩ := mem_inf.1 hq
    exact mem_inf.2 ⟨s56_P0_le_N d hqP, hqC⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
