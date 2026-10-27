module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56P11
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

section P09Reg

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem node09_pv9_mem_F (d : Data G) : d.pv 9 ∈ d.F :=
  Data.mem_liftSub.2 ⟨_, Model.parrottV_mem_parrottF (by simp), Model.parrottF_le_titsD
    (Model.parrottV_mem_parrottF (by simp)), rfl⟩

theorem node09_comm_F_of_gens (d : Data G) {g : G}
    (hg : ∀ i ∈ ({7, 9, 10, 11, 12} : Set ℕ), g * d.pv i = d.pv i * g) :
    ∀ f ∈ d.F, g * f = f * g := by
  intro f hf
  obtain ⟨x, hx, hxD, rfl⟩ := Data.mem_liftSub.1 hf
  have key : ∀ x : Equiv.Perm (Fin 1755),
      x ∈ Subgroup.closure (Model.parrottV '' ({7, 9, 10, 11, 12} : Set ℕ)) →
        g * d.lift x = d.lift x * g := by
    intro x hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact hg i hi
    | one => rw [d.lift_one]; simp
    | mul a b ha hb iha ihb =>
      have haD : a ∈ titsD := Model.parrottF_le_titsD ha
      have hbD : b ∈ titsD := Model.parrottF_le_titsD hb
      rw [d.lift_mul haD hbD, ← mul_assoc, iha, mul_assoc, ihb, mul_assoc]
    | inv a ha iha =>
      have haD : a ∈ titsD := Model.parrottF_le_titsD ha
      rw [d.lift_inv haD]
      exact (Commute.inv_right (show Commute g (d.lift a) from iha)).eq
  exact key x hx

theorem node09_P_le_P10 (d : Data G) : d.s56P ≤ d.s56P10 := by
  rw [d.s56P_def, d.s56P10_def]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (d.s56_U10_le_F))

theorem node09_comm_mul (h49 : d.Thm49Statement) (hd : d.Hyp)
    (h518 : ⁅d.s56P10, d.F⁆ ≤ d.s56U11) {p q f : G} (hp : p ∈ d.s56P10) (hq : q ∈ d.s56P10)
    (hf : f ∈ d.F) :
    (p * q) * f * (p * q)⁻¹ * f⁻¹ = (p * f * p⁻¹ * f⁻¹) * (q * f * q⁻¹ * f⁻¹) := by
  have hqU : q * f * q⁻¹ * f⁻¹ ∈ d.s56U11 := h518 (Subgroup.commutator_mem_commutator hq hf)
  have hpU : p * f * p⁻¹ * f⁻¹ ∈ d.s56U11 := h518 (Subgroup.commutator_mem_commutator hp hf)
  have hpc : p * (q * f * q⁻¹ * f⁻¹) = (q * f * q⁻¹ * f⁻¹) * p :=
    hd.s56_P0_comm_U11 h49 (d.s56_P10_le_P0 hp) hqU
  have hcomm : (p * f * p⁻¹ * f⁻¹) * (q * f * q⁻¹ * f⁻¹) =
      (q * f * q⁻¹ * f⁻¹) * (p * f * p⁻¹ * f⁻¹) :=
    hd.s56_F_comm (d.s56_U11_le_F hpU) (d.s56_U11_le_F hqU)
  calc (p * q) * f * (p * q)⁻¹ * f⁻¹
      = (p * (q * f * q⁻¹ * f⁻¹) * p⁻¹) * (p * f * p⁻¹ * f⁻¹) := by group
    _ = (q * f * q⁻¹ * f⁻¹) * (p * f * p⁻¹ * f⁻¹) := by rw [hpc]; group
    _ = _ := hcomm.symm

theorem node09_card_P10_le (h49 : d.Thm49Statement) (hd : d.Hyp)
    (h518 : ⁅d.s56P10, d.F⁆ ≤ d.s56U11) : Nat.card d.s56P10 ≤ 16 * Nat.card d.s56P := by
  have hcomm : ∀ p ∈ d.s56P10, ∀ f ∈ d.F, p * f * p⁻¹ * f⁻¹ ∈ d.s56U11 := fun p hp f hf =>
    h518 (Subgroup.commutator_mem_commutator hp hf)
  have h7 : d.pv 7 ∈ d.F := hd.s56_pv7_mem_F
  have h9 : d.pv 9 ∈ d.F := node09_pv9_mem_F d
  let Λ : ↥d.s56P10 →* ↥d.s56U11 × ↥d.s56U11 :=
    MonoidHom.mk' (fun p => (⟨p.1 * d.pv 7 * p.1⁻¹ * (d.pv 7)⁻¹, hcomm p.1 p.2 _ h7⟩,
        ⟨p.1 * d.pv 9 * p.1⁻¹ * (d.pv 9)⁻¹, hcomm p.1 p.2 _ h9⟩)) fun p q =>
      Prod.ext (Subtype.ext (node09_comm_mul h49 hd h518 p.2 q.2 h7))
        (Subtype.ext (node09_comm_mul h49 hd h518 p.2 q.2 h9))
  have hker : Λ.ker ≤ d.s56P.subgroupOf d.s56P10 := by
    intro p hp
    rw [MonoidHom.mem_ker, Prod.ext_iff] at hp
    obtain ⟨hp7, hp9⟩ := hp
    have hp7' : p.1 * d.pv 7 * p.1⁻¹ * (d.pv 7)⁻¹ = 1 := congrArg Subtype.val hp7
    have hp9' : p.1 * d.pv 9 * p.1⁻¹ * (d.pv 9)⁻¹ = 1 := congrArg Subtype.val hp9
    have hc : ∀ f ∈ d.F, p.1 * f = f * p.1 := by
      refine node09_comm_F_of_gens d fun i hi => ?_
      have hpC : p.1 ∈ d.s56P0 ⊓ centralizer (d.s56U10 : Set G) := by
        rw [← d.s56P10_def]
        exact p.2
      have hU : ∀ u ∈ d.s56U10, p.1 * u = u * p.1 := fun u hu =>
        (mem_centralizer_iff.1 (mem_inf.1 hpC).2 u hu).symm
      have hcm : ∀ a : G, p.1 * a * p.1⁻¹ * a⁻¹ = 1 → p.1 * a = a * p.1 := fun a h =>
        calc p.1 * a = (p.1 * a * p.1⁻¹ * a⁻¹) * (a * p.1) := by group
          _ = a * p.1 := by rw [h, one_mul]
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact hcm _ hp7'
      · exact hcm _ hp9'
      · exact hU _ (d.s56_pv10_mem_U10)
      · exact hU _ (d.s56_U11_le_U10 d.s56_pv11_mem_U11)
      · rw [d.s56_pv12]
        exact hU _ (d.s56_U11_le_U10 d.s56_z_mem_U11)
    rw [mem_subgroupOf, d.s56P_def, mem_inf]
    exact ⟨d.s56_P10_le_P0 p.2, mem_centralizer_iff.2 fun f hf => (hc f hf).symm⟩
  have h := Subgroup.card_ker_mul_card_range Λ
  have hrange : Nat.card Λ.range ≤ 16 := by
    calc Nat.card Λ.range ≤ Nat.card (↥d.s56U11 × ↥d.s56U11) := Subgroup.card_le_card_group _
      _ = 16 := by rw [Nat.card_prod, d.s56_card_U11]
  have hk : Nat.card Λ.ker ≤ Nat.card d.s56P := by
    calc Nat.card Λ.ker ≤ Nat.card (d.s56P.subgroupOf d.s56P10) := Subgroup.card_le_of_le hker
      _ = Nat.card d.s56P := Nat.card_congr (subgroupOfEquivOfLe (node09_P_le_P10 d)).toEquiv
  calc Nat.card d.s56P10 = Nat.card Λ.ker * Nat.card Λ.range := h.symm
    _ ≤ Nat.card d.s56P * 16 := Nat.mul_le_mul hk hrange
    _ = 16 * Nat.card d.s56P := by ring

theorem node09_card_P_ge (h49 : d.Thm49Statement) (hd : d.Hyp)
    (h518 : ⁅d.s56P10, d.F⁆ ≤ d.s56U11) : 1024 ≤ Nat.card d.s56P := by
  have h1 := node09_card_P10_le h49 hd h518
  have h2 := hd.s56_card_N h49
  rcases hd.card_M_N_values h49 with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega

theorem node09_eq_F_of_invariant (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G}
    (hSF : S ≤ d.F) (hinv : ∀ c ∈ d.N ⊓ centralizer ({d.t} : Set G), ∀ x ∈ S, c * x * c⁻¹ ∈ S)
    (hcard : 16 ≤ Nat.card S) : S = d.F := by
  have hF32 : Nat.card d.F = 32 := hd.B_facts.1
  obtain ⟨s, hsS, hsU⟩ : ∃ s ∈ S, s ∉ d.s56U10 := by
    by_contra hcon
    have hle : S ≤ d.s56U10 := fun s hs => by_contra fun h => hcon ⟨s, hs, h⟩
    have := Subgroup.card_le_of_le hle
    rw [d.s56_card_U10] at this
    omega
  have hsF : s ∈ d.F := hSF hsS
  obtain ⟨k, hkK, hk⟩ : ∃ k ∈ d.s56K, k * s * k⁻¹ * s⁻¹ ∉ d.s56U11 := by
    by_contra hcon
    refine hsU (Data.s56_comm_K_le_U10 hsF fun k hk => by_contra fun h => hcon ⟨k, hk, h⟩)
  have hkP0 := hd.s56_K_le_P0 h49 hkK
  have hkC := hd.s56_K_le_CNt hkK
  have hu₀10 : k * s * k⁻¹ * s⁻¹ ∈ d.s56U10 := hd.s56_P0_comm_F_le_U10 h49 hkP0 hsF
  have hu₀S : k * s * k⁻¹ * s⁻¹ ∈ S := mul_mem (hinv k hkC s hsS) (inv_mem hsS)
  obtain ⟨u', hu'U, hu'⟩ : ∃ u' ∈ d.s56U11, k * s * k⁻¹ * s⁻¹ = d.pv 10 * u' := by
    rcases Data.s56_U10_cases hu₀10 with h | ⟨u', hu', h⟩
    · exact absurd h hk
    · exact ⟨u', hu', h⟩
  have hU11S : ∀ u ∈ d.s56U11, u ∈ S := by
    intro u hu
    obtain ⟨k', hk'K, hk'⟩ := hd.s56_exists_K_comm h49 hu
    have hk'P0 := hd.s56_K_le_P0 h49 hk'K
    have hk'C := hd.s56_K_le_CNt hk'K
    have h1 : k' * (k * s * k⁻¹ * s⁻¹) * k'⁻¹ ∈ S := hinv k' hk'C _ hu₀S
    have hc' : k' * u' = u' * k' := hd.s56_P0_comm_U11 h49 hk'P0 hu'U
    have e2 : k' * u' * k'⁻¹ = u' := by rw [hc']; group
    have h2 : k' * (k * s * k⁻¹ * s⁻¹) * k'⁻¹ = u * (k * s * k⁻¹ * s⁻¹) := by
      rw [hu']
      calc k' * (d.pv 10 * u') * k'⁻¹ = (k' * d.pv 10 * k'⁻¹) * (k' * u' * k'⁻¹) := by group
        _ = (u * d.pv 10) * u' := by rw [hk', e2]
        _ = u * (d.pv 10 * u') := by group
    rw [h2] at h1
    have e : u = u * (k * s * k⁻¹ * s⁻¹) * (k * s * k⁻¹ * s⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hu₀S)
  have hU10S : d.s56U10 ≤ S := by
    intro x hx
    rcases Data.s56_U10_cases hx with h | ⟨u, hu, rfl⟩
    · exact hU11S x h
    · have hv10 : d.pv 10 ∈ S := by
        have : d.pv 10 = (k * s * k⁻¹ * s⁻¹) * u'⁻¹ := by rw [hu']; group
        rw [this]
        exact mul_mem hu₀S (inv_mem (hU11S u' hu'U))
      exact mul_mem hv10 (hU11S u hu)
  have hd32 : Nat.card S ∣ 32 := by
    have := Subgroup.card_dvd_of_le hSF
    rwa [hF32] at this
  have h1632 : Nat.card S = 16 ∨ Nat.card S = 32 := by
    have hle : Nat.card S ≤ 32 := Nat.le_of_dvd (by norm_num) hd32
    generalize Nat.card S = n at hd32 hcard hle ⊢
    interval_cases n <;> first | omega | (exfalso; revert hd32; decide)
  rcases h1632 with h16 | h32
  · exfalso
    obtain ⟨hyNC, -, -, -, -, -, -⟩ := hd.s56_Y_facts
    have hys : d.s56Y * s * d.s56Y⁻¹ ∈ S := hinv _ hyNC s hsS
    have hysU : d.s56Y * s * d.s56Y⁻¹ ∉ d.s56U10 := fun h => hsU (by
      have := hd.s56_N_conj_U10 h49 (inv_mem (mem_inf.1 hyNC).1) h
      simpa [mul_assoc] using this)
    have := mul_inv_mem_of_card_eq_two_mul hU10S (by rw [h16, d.s56_card_U10]) hys hsS hysU hsU
    exact Data.s56_Y_comm_not_mem hsF hsU this
  · exact Subgroup.eq_of_le_of_card_ge hSF (by rw [h32, hF32])

@[expose] noncomputable def node09Eps (h49 : d.Thm49Statement) (hd : d.Hyp) : ↥d.s56P →* G :=
  MonoidHom.mk' (fun p => d.s56Eps p.1) fun p q => hd.s56_eps_mul_P h49 p.2 q.2

theorem node09Eps_apply (h49 : d.Thm49Statement) (hd : d.Hyp) (p : ↥d.s56P) :
    node09Eps h49 hd p = d.s56Eps p.1 := rfl

theorem node09Eps_ker (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (node09Eps h49 hd).ker = d.B.subgroupOf d.s56P := by
  ext p
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    exact hd.s56_mem_B_of_eps_one h49 p.2 h
  · intro h
    exact hd.s56_eps_eq_one_of_mem_B h

theorem node09_eps_range (h49 : d.Thm49Statement) (hd : d.Hyp)
    (h518 : ⁅d.s56P10, d.F⁆ ≤ d.s56U11) : (node09Eps h49 hd).range = d.F := by
  have hF : (node09Eps h49 hd).range ≤ d.F := by
    rintro _ ⟨p, rfl⟩
    exact hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N p.2)
  refine node09_eq_F_of_invariant h49 hd hF ?_ ?_
  ·
    intro c hc x hx
    obtain ⟨p, rfl⟩ := hx
    have hcN : c ∈ d.N := (mem_inf.1 hc).1
    have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
    refine ⟨⟨c * p.1 * c⁻¹, hd.s56_N_conj_P h49 hcN p.2⟩, ?_⟩
    show d.s56Eps (c * p.1 * c⁻¹) = c * d.s56Eps p.1 * c⁻¹
    exact hd.s56_eps_conj hct p.1
  ·
    have h := Subgroup.card_ker_mul_card_range (node09Eps h49 hd)
    rw [node09Eps_ker h49 hd, Nat.card_congr (subgroupOfEquivOfLe (hd.s56_B_le_P)).toEquiv,
      hd.B_facts.2.2.2.1] at h
    have := node09_card_P_ge h49 hd h518
    omega

theorem node09_eps_surj (h49 : d.Thm49Statement) (hd : d.Hyp)
    (h518 : ⁅d.s56P10, d.F⁆ ≤ d.s56U11) {f : G} (hf : f ∈ d.F) :
    ∃ p ∈ d.s56P, d.s56Eps p = f := by
  have h : f ∈ (node09Eps h49 hd).range := by
    rw [node09_eps_range h49 hd h518]
    exact hf
  obtain ⟨p, hp⟩ := h
  exact ⟨p.1, p.2, hp⟩

theorem node09_519 (h49 : d.Thm49Statement) (hd : d.Hyp) (h518 : ⁅d.s56P10, d.F⁆ ≤ d.s56U11) :
    ((d.s56P : Set G) * ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) =
      (d.N : Set G)) ∧
    d.B ≤ d.s56P ∧ IsElemAbQuot d.s56P d.B 5 ∧ d.s56P ⊓ centralizer ({d.t} : Set G) = d.B ∧
    (∀ s ∈ (fun f => d.t * f) '' (d.F : Set G), ∃ p ∈ d.s56P, p * d.t * p⁻¹ = s) := by
  refine ⟨?_, hd.s56_B_le_P, ?_, ?_, ?_⟩
  ·
    ext n
    rw [Set.mem_mul]
    constructor
    · rintro ⟨p, hp, c, hc, rfl⟩
      exact mul_mem (d.s56_P_le_N hp) (mem_inf.1 hc).1
    · intro hn
      have hεF := hd.s56_eps_mem_F_of_N h49 hn
      obtain ⟨p, hp, hpε⟩ := node09_eps_surj h49 hd h518 hεF
      refine ⟨p, hp, p⁻¹ * n, ?_, by group⟩
      refine mem_inf.2 ⟨mul_mem (inv_mem (d.s56_P_le_N hp)) hn, mem_centralizer_singleton_iff.2 ?_⟩
      have hε1 : d.s56Eps (p⁻¹ * n) = 1 := by
        rw [hd.s56_eps_mul, hd.s56_eps_inv_P h49 hp, hpε, d.s56_P_conj_F (inv_mem hp) hεF]
        exact hd.s56_F_sq hεF
      have h1 := hd.s56_conj_t (p⁻¹ * n)
      rw [hε1, mul_one] at h1
      calc p⁻¹ * n * d.t = (p⁻¹ * n * d.t * (p⁻¹ * n)⁻¹) * (p⁻¹ * n) := by group
        _ = d.t * (p⁻¹ * n) := by rw [h1]
  ·
    have hεF : ∀ p ∈ d.s56P, d.s56Eps p ∈ d.F := fun p hp =>
      hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N hp)
    refine ⟨hd.s56_B_le_P, ?_, ?_, ?_, ?_⟩
    · rw [← node09Eps_ker h49 hd]
      exact (node09Eps h49 hd).normal_ker
    · intro k hk
      refine hd.s56_mem_B_of_eps_one h49 (mul_mem hk hk) ?_
      rw [hd.s56_eps_mul_P h49 hk hk]
      exact hd.s56_eps_sq_P h49 hk
    · intro a ha b hb
      have hab : d.s56Eps a * d.s56Eps b = d.s56Eps b * d.s56Eps a :=
        hd.s56_F_comm (hεF a ha) (hεF b hb)
      have hmem : ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ ∈ (node09Eps h49 hd).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
        show d.s56Eps a * d.s56Eps b * (d.s56Eps a)⁻¹ * (d.s56Eps b)⁻¹ = 1
        calc d.s56Eps a * d.s56Eps b * (d.s56Eps a)⁻¹ * (d.s56Eps b)⁻¹
            = d.s56Eps b * d.s56Eps a * (d.s56Eps a)⁻¹ * (d.s56Eps b)⁻¹ := by rw [hab]
          _ = 1 := by group
      rw [node09Eps_ker h49 hd] at hmem
      exact mem_subgroupOf.1 hmem
    · rw [Subgroup.relIndex, ← node09Eps_ker h49 hd, Subgroup.index_ker,
        node09_eps_range h49 hd h518, hd.B_facts.1]
      norm_num
  ·
    apply le_antisymm
    · intro p hp
      obtain ⟨hpP, hpC⟩ := mem_inf.1 hp
      refine hd.s56_mem_B_of_eps_one h49 hpP (hd.s56_eps_of_comm ?_)
      exact mem_centralizer_singleton_iff.1 hpC
    · intro b hb
      exact mem_inf.2 ⟨hd.s56_B_le_P hb, hd.B_facts.2.1 hb⟩
  ·
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨p, hp, hpf⟩ := node09_eps_surj h49 hd h518 hf
    exact ⟨p, hp, by rw [hd.s56_conj_t p, hpf]⟩

end P09Reg

end CFSG.LocalAnalysis.EvenBN.Tits.N
