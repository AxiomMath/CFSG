module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bAbs
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N4
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P2b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem P11_le_P : P11 d ≤ d.s56P := fun _ hg => hg.1

theorem Pe11_le_P11 (h08 : Node08 d z₀) : Pe11 d ≤ P11 d := by
  rw [h08.2.2.1]
  exact le_sup_left

theorem t_mem_P11 (h08 : Node08 d z₀) : d.t ∈ P11 d := by
  rw [h08.2.2.1]
  exact mem_sup_right (mem_zpowers _)

theorem t_mem_normalizer_Pe11 (h08 : Node08 d z₀) :
    d.t ∈ normalizer ((Pe11 d : Subgroup G) : Set G) :=
  Subgroup.normalizer_commutator_ge_left (P11 d) d.N (t_mem_P11 h08)

theorem z0_mem_Pe11 (h07 : Node07 d) (h08 : Node08 d z₀) : z₀ ∈ Pe11 d := by
  obtain ⟨y, hy⟩ := h07.1
  rw [h08.2.2.2.1 y hy]
  exact mem_sup_right (subset_closure (by simp))

theorem Pe11_le_P1 (h08 : Node08 d z₀) : Pe11 d ≤ P1 d := fun x hx =>
  mem_inf.2 ⟨P11_le_P (Pe11_le_P11 h08 hx), mem_centralizer_iff.2 fun h hh =>
    elemAb_comm h08.2.2.2.2.1 hh hx⟩

theorem F_le_P1 (h08 : Node08 d z₀) : d.F ≤ P1 d := fun x hx => Pe11_le_P1 h08 (h08.2.1 hx)

theorem P1_le_P : P1 d ≤ d.s56P := fun _ hx => (mem_inf.1 hx).1

theorem mem_P_iff {p : G} : p ∈ d.s56P ↔ p ∈ d.s56P0 ∧ ∀ f ∈ d.F, f * p = p * f := by
  rw [s56P_def, mem_inf, mem_centralizer_iff]
  rfl

theorem P_le_N : d.s56P ≤ d.N := (s56_P_le_P0 d).trans (s56_P0_le_N d)

theorem P1_isPGroup : IsPGroup 2 (P1 d) :=
  IsPGroup.to_le (s56_P0_isPGroup d) (P1_le_P.trans (s56_P_le_P0 d))

theorem t_not_mem_P1 (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d) (h08 : Node08 d z₀) :
    d.t ∉ P1 d := by
  intro ht
  have hcomm : z₀ * d.t = d.t * z₀ :=
    mem_centralizer_iff.1 (mem_inf.1 ht).2 z₀ (z0_mem_Pe11 h07 h08)
  have h1 := hd.s56_conj_t z₀
  rw [hz.eps, hcomm] at h1
  have h2 : d.t * z₀ * z₀⁻¹ = d.t := by group
  rw [h2] at h1
  have hz1 : d.z = 1 := (mul_eq_left.1 h1.symm)
  have h2' := hd.s56_orderOf_z
  rw [hz1, orderOf_one] at h2'
  omega

theorem card_P1_prod :
    Nat.card (Multiplicative (Fin 6 → ZMod 2) × (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) =
      2 ^ 10 := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_multiplicative, ZMod.card]

theorem card_P1 (h11 : Node11 d z₀) : Nat.card (P1 d) = 2 ^ 10 := by
  rcases h11.2.2.2.2.2.2 with ⟨-, h⟩ | ⟨-, ⟨e⟩, -⟩
  · exact h
  · rw [Nat.card_congr e.toEquiv]
    exact card_P1_prod

theorem P1_inf_C_t (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d) (h08 : Node08 d z₀) :
    P1 d ⊓ centralizer ({d.t} : Set G) = d.F := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP1, hxC⟩ := mem_inf.1 hx
    have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 hxC
    have hxPc : ∀ f ∈ d.F, f * x = x * f := (mem_P_iff.1 (P1_le_P hxP1)).2
    have hle : d.B ≤ centralizer ({x} : Set G) :=
      sup_le (fun f hf => mem_centralizer_singleton_iff.2 (hxPc f hf))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hxt.symm))
    have hxB : x ∈ d.B := by
      have hxC' : x ∈ centralizer (d.B : Set G) :=
        mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)
      rwa [hd.centralizer_B] at hxC'
    rcases ((hd.tSup_facts (d.liftSub_le _ : d.F ≤ d.L)).1 x).1 hxB with h | h
    · exact h
    · exfalso
      apply t_not_mem_P1 hd hz h07 h08
      have h3 : d.t * x * x⁻¹ ∈ P1 d := mul_mem (F_le_P1 h08 h) (inv_mem hxP1)
      simpa using h3
  · intro f hf
    exact mem_inf.2 ⟨F_le_P1 h08 hf, hd.B_facts.2.1 (s56_F_le_B d hf)⟩

theorem conj_t_mem_tF (h49 : d.Thm49Statement) (hd : d.Hyp) {n : G} (hn : n ∈ d.N) :
    n * d.t * n⁻¹ ∈ (fun f => d.t * f) '' (d.F : Set G) := by
  have htB : d.t ∈ d.B := mem_sup_right (mem_zpowers _)
  have hnB : n * d.t * n⁻¹ ∈ d.B := (mem_normalizer_iff.1 hn d.t).1 htB
  have hmem : n * d.t * n⁻¹ ∈ d.tG ∩ (d.B : Set G) := ⟨⟨n, rfl⟩, hnB⟩
  rw [(hd.thm51 h49 (D := d.B) (Or.inr rfl)).1] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hd.B_facts.2.2.2.2 x (mem_inf.1 hx).1 (mem_inf.1 hx).2, hxe⟩

theorem ncard_tF (hd : d.Hyp) : ((fun f => d.t * f) '' (d.F : Set G)).ncard = 2 ^ 5 := by
  rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), ← Nat.card_coe_set_eq]
  change Nat.card d.F = 2 ^ 5
  rw [hd.B_facts.1]
  norm_num

theorem orbit_t_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h11 : Node11 d z₀) :
    {x | ∃ p ∈ P1 d, p * d.t * p⁻¹ = x} = (fun f => d.t * f) '' (d.F : Set G) := by
  have hsub : {x | ∃ p ∈ P1 d, p * d.t * p⁻¹ = x} ⊆ (fun f => d.t * f) '' (d.F : Set G) := by
    rintro x ⟨p, hp, rfl⟩
    exact conj_t_mem_tF h49 hd (P_le_N (P1_le_P hp))
  have hX := ncard_tF hd
  have hcard := CFSG.LocalAnalysis.EvenBN.Tits.card_eq_ncard_conj_mul (P1 d) d.t
  rw [P1_inf_C_t hd hz h07 h08, card_P1 h11, hd.B_facts.1] at hcard
  have hO : {x | ∃ p ∈ P1 d, p * d.t * p⁻¹ = x}.ncard = 2 ^ 5 := by
    norm_num at hcard ⊢
    omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hX, hO]) (Set.toFinite _)

theorem sq_eq_one_of_inv (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h11 : Node11 d z₀) {p : G} (hp : p ∈ P1 d)
    (htp : d.t * p * d.t = p⁻¹) : p * p = 1 := by
  rcases h11.2.2.2.2.2.2 with ⟨hab, -⟩ | ⟨-, -, hFr⟩
  · exact elemAb_mul_self hab hp
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (IsPGroup 2 ↥(P1 d)) := ⟨P1_isPGroup⟩
    have hsq : p * p ∈ d.s56U11 := by
      have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥(P1 d)) (p := 2) ⟨p, hp⟩
      have h2 : ((⟨p, hp⟩ : ↥(P1 d)) ^ 2 : ↥(P1 d)).1 ∈
          (frattini ↥(P1 d)).map (P1 d).subtype := ⟨_, h1, rfl⟩
      rw [hFr] at h2
      simpa [pow_two] using h2
    have hpP := P1_le_P hp
    have hpN : p ∈ d.N := P_le_N hpP
    have hpF : ∀ f ∈ d.F, f * p = p * f := (mem_P_iff.1 hpP).2
    have htp' : d.t * p⁻¹ * d.t⁻¹ = p := by
      have ht' : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_self
      rw [ht']
      have := congrArg (fun x => x⁻¹) htp
      simp only [mul_inv_rev, inv_inv] at this
      rw [ht'] at this
      calc d.t * p⁻¹ * d.t = d.t * p⁻¹ * d.t⁻¹ := by rw [ht']
        _ = p := by rw [ht']; simpa [mul_assoc] using this
    have hp11 : p ∈ P11 d := by
      refine ⟨hpP, mem_normalizer_iff.2 fun u => ⟨fun hu => hd.s56_N_conj_U11 h49 hpN hu, fun hu => ?_⟩,
        fun b hb => ?_⟩
      · have := hd.s56_N_conj_U11 h49 (inv_mem hpN) hu
        simpa [mul_assoc] using this
      · rcases ((hd.tSup_facts (d.liftSub_le _ : d.F ≤ d.L)).1 b).1 hb with hbF | htb
        · have : p * b * p⁻¹ * b⁻¹ = 1 := by
            calc p * b * p⁻¹ * b⁻¹ = (b * p) * p⁻¹ * b⁻¹ := by rw [hpF b hbF]
              _ = 1 := by group
          rw [this]
          exact one_mem _
        · obtain ⟨f, hf, hfb⟩ : ∃ f ∈ d.F, b = d.t * f :=
            ⟨d.t * b, htb, by rw [← mul_assoc, hd.t_mul_self, one_mul]⟩
          subst hfb
          have hfp : f * p⁻¹ = p⁻¹ * f := (Commute.inv_right (show Commute f p from hpF f hf)).eq
          have e : p * (d.t * f) * p⁻¹ * (d.t * f)⁻¹ = p * (d.t * p⁻¹ * d.t⁻¹) := by
            calc p * (d.t * f) * p⁻¹ * (d.t * f)⁻¹ = p * d.t * (f * p⁻¹) * f⁻¹ * d.t⁻¹ := by group
              _ = p * d.t * (p⁻¹ * f) * f⁻¹ * d.t⁻¹ := by rw [hfp]
              _ = p * (d.t * p⁻¹ * d.t⁻¹) := by group
          rw [e, htp']
          exact hsq
    have hp11' : p ∈ Pe11 d ⊔ zpowers d.t := by
      rw [← h08.2.2.1]
      exact hp11
    rcases mem_sup_zpowers_cases (t_mem_normalizer_Pe11 h08)
      (by rw [hd.t_mul_self]; exact one_mem _) hp11' with h | ⟨h, hh, rfl⟩
    · exact elemAb_mul_self h08.2.2.2.2.1 h
    · exfalso
      apply t_not_mem_P1 hd hz h07 h08
      have h3 : d.t * h * h⁻¹ ∈ P1 d := mul_mem hp (inv_mem (Pe11_le_P1 h08 hh))
      simpa using h3

theorem inv_P_not_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h11 : Node11 d z₀) :
    ∀ s ∈ d.s56P, s ∉ P1 d → s * s = 1 → s ∈ (fun f => d.t * f) '' (d.F : Set G) := by
  intro s hsP hsP1 hs2
  have hs : s ∈ (zpowers d.t : Set G) * (P1 d : Set G) := by
    rw [← h11.2.1]
    exact hsP
  obtain ⟨a, ha, p, hp, hap'⟩ := hs
  have hap : a * p = s := hap'
  rcases (Model.mem_zpowers_of_orderOf_two hd.t_two).1 ha with rfl | rfl
  · exfalso
    apply hsP1
    rw [← hap, one_mul]
    exact hp
  · subst hap
    have hinv : d.t * p * d.t = p⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      calc d.t * p * d.t * p = d.t * p * (d.t * p) := by group
        _ = 1 := hs2
    have hpp := sq_eq_one_of_inv h49 hd hz h07 h08 h11 hp hinv
    have hcomm : p * d.t = d.t * p := by
      have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
      rw [hpi] at hinv
      calc p * d.t = (d.t * p * d.t) * d.t := by rw [hinv]
        _ = d.t * p := by rw [mul_assoc, hd.t_mul_self, mul_one]
    have hpF : p ∈ d.F := by
      rw [← P1_inf_C_t hd hz h07 h08]
      exact mem_inf.2 ⟨hp, mem_centralizer_singleton_iff.2 hcomm⟩
    exact ⟨p, hpF, rfl⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P2b
