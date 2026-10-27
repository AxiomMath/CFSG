module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem comm_zpowers_inf_cent_le {C Q : Subgroup G} {ρ : G} (hρ3 : ρ ^ 3 = 1)
    (hC2 : IsPGroup 2 C) (hQC : Q ≤ C) (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q) (hρC : ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C)
    (hab : ∀ c ∈ C, ∀ c' ∈ C, c * c' * c⁻¹ * c'⁻¹ ∈ Q) :
    ∀ x ∈ ⁅C, zpowers ρ⁆, x * ρ = ρ * x → x ∈ Q := by
  classical
  let N : Subgroup G := C ⊔ zpowers ρ
  have hCN : C ≤ N := le_sup_left
  have hzpN : zpowers ρ ≤ N := le_sup_right
  have hQN : Q ≤ N := hQC.trans hCN
  have hρN : ρ ∈ N := hzpN (Subgroup.mem_zpowers ρ)
  let CN : Subgroup N := C.subgroupOf N
  let PN : Subgroup N := Subgroup.zpowers (⟨ρ, hρN⟩ : N)
  let Q' : Subgroup N := Q.subgroupOf N
  have hNnorm : N ≤ Subgroup.normalizer (Q : Set G) := by
    change C ⊔ zpowers ρ ≤ Subgroup.normalizer (Q : Set G)
    apply sup_le
    · intro c hc
      exact Subgroup.mem_normalizer_fintype (S := (Q : Set G)) (fun q hq => hQn c hc q hq)
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_normalizer_fintype (S := (Q : Set G)) hρQ)
  have hQ'normal : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr hNnorm
  letI : Q'.Normal := hQ'normal
  let π : N →* N ⧸ Q' := QuotientGroup.mk' Q'
  let R : Subgroup (N ⧸ Q') := CN.map π
  let A : Subgroup (N ⧸ Q') := PN.map π
  have hPN_norm : PN ≤ Subgroup.normalizer (CN : Set N) := by
    change Subgroup.zpowers (⟨ρ, hρN⟩ : N) ≤ Subgroup.normalizer (CN : Set N)
    refine Subgroup.zpowers_le.mpr ?_
    refine Subgroup.mem_normalizer_fintype (S := (CN : Set N)) ?_
    intro n hn
    change ((⟨ρ, hρN⟩ * n * ⟨ρ, hρN⟩⁻¹ : N) : G) ∈ C
    change (n : G) ∈ C at hn
    simpa using hρC (n : G) hn
  have hAR : A ≤ Subgroup.normalizer (R : Set (N ⧸ Q')) := by
    have h1 : PN.map π ≤ (Subgroup.normalizer (CN : Set N)).map π :=
      Subgroup.map_mono hPN_norm
    have h2 : (Subgroup.normalizer (CN : Set N)).map π ≤
        Subgroup.normalizer (CN.map π : Set (N ⧸ Q')) := Subgroup.le_normalizer_map (H := CN) π
    exact h1.trans h2
  have hPN3 : IsPGroup 3 PN := by
    have h3 : (⟨ρ, hρN⟩ : N) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hρ3
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    change Nat.card (Subgroup.zpowers (⟨ρ, hρN⟩ : N)) ∣ 3 ^ 1
    rw [pow_one, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h3
  have hA3 : IsPGroup 3 A := hPN3.map π
  have hQ'map : Q'.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' Q').symm
  have hcomm_le : ⁅CN, CN⁆ ≤ Q' := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haC : (a : G) ∈ C := Subgroup.mem_subgroupOf.mp ha
    have hbC : (b : G) ∈ C := Subgroup.mem_subgroupOf.mp hb
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hab (a : G) haC (b : G) hbC
  have hRcomm : IsMulCommutative R := by
    refine Subgroup.commutator_self_eq_bot_iff.mp ?_
    rw [eq_bot_iff]
    have hRQ : ⁅R, R⁆ = (⁅CN, CN⁆).map π := by
      show ⁅CN.map π, CN.map π⁆ = (⁅CN, CN⁆).map π
      exact (Subgroup.map_commutator CN CN π).symm
    rw [hRQ]
    calc (⁅CN, CN⁆).map π ≤ Q'.map π := Subgroup.map_mono hcomm_le
      _ = ⊥ := hQ'map
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    have hdvd : Nat.card R ∣ Nat.card C := by
      calc Nat.card R ∣ Nat.card CN := Subgroup.card_map_dvd (H := CN) π
        _ = Nat.card C := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
    obtain ⟨k, hk⟩ := hC2.exists_card_eq
    rw [hk] at hdvd
    exact (show Nat.Coprime 3 (2 ^ k) from
      (by decide : Nat.Coprime 3 2).pow_right k).coprime_dvd_right hdvd
  haveI : IsMulCommutative R := hRcomm
  have hfit : ⁅R, A⁆ ⊓ Subgroup.centralizer (A : Set (N ⧸ Q')) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35.commutator_inf_centralizer_eq_bot
      (p := 3) (by decide) (A := A) (R := R) hA3 hAR hcop
  intro x hxmem hxρ
  have hxN : x ∈ N := (Subgroup.commutator_le_of_le hCN hzpN) hxmem
  have hmapcomm : (⁅CN, PN⁆).map (N.subtype) = ⁅C, zpowers ρ⁆ := by
    have h1 : CN.map (N.subtype) = C := Subgroup.map_subgroupOf_eq_of_le hCN
    have h2 : PN.map (N.subtype) = zpowers ρ := by
      change (Subgroup.zpowers (⟨ρ, hρN⟩ : N)).map (N.subtype) = zpowers ρ
      rw [MonoidHom.map_zpowers]
      rfl
    rw [Subgroup.map_commutator CN PN (N.subtype), h1, h2]
  have hxCNPN : (⟨x, hxN⟩ : N) ∈ ⁅CN, PN⁆ := by
    have hxmap : x ∈ (⁅CN, PN⁆).map (N.subtype) := by
      rw [hmapcomm]; exact hxmem
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
    have hyx' : y = ⟨x, hxN⟩ := Subtype.ext hyx
    simpa [hyx'] using hy
  have hxR : π ⟨x, hxN⟩ ∈ ⁅R, A⁆ := by
    change π ⟨x, hxN⟩ ∈ ⁅CN.map π, PN.map π⁆
    rw [← Subgroup.map_commutator CN PN π]
    exact Subgroup.mem_map_of_mem π hxCNPN
  have hAeq : A = Subgroup.zpowers (π ⟨ρ, hρN⟩) := by
    change PN.map π = Subgroup.zpowers (π ⟨ρ, hρN⟩)
    exact MonoidHom.map_zpowers π ⟨ρ, hρN⟩
  have hxcent : π ⟨x, hxN⟩ ∈ Subgroup.centralizer (A : Set (N ⧸ Q')) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hAeq] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcommN : Commute (⟨ρ, hρN⟩ : N) ⟨x, hxN⟩ := by
      rw [commute_iff_eq]
      exact Subtype.ext hxρ.symm
    have hmap := (hcommN.zpow_left k).map π
    simpa using hmap.eq
  have hxbot : π ⟨x, hxN⟩ ∈ ⁅R, A⁆ ⊓ Subgroup.centralizer (A : Set (N ⧸ Q')) :=
    ⟨hxR, hxcent⟩
  rw [hfit] at hxbot
  have hx1 : π ⟨x, hxN⟩ = 1 := Subgroup.mem_bot.mp hxbot
  have hxQ' : (⟨x, hxN⟩ : N) ∈ Q' := (QuotientGroup.eq_one_iff (⟨x, hxN⟩ : N)).mp hx1
  simpa using (Subgroup.mem_subgroupOf.mp hxQ')

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
