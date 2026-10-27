module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec7l78_twoRes_le (N : Subgroup G) : twoRes N ≤ N :=
  (Subgroup.closure_le _).mpr fun _ hg => hg.1

theorem sec7l78_twoRes_mono {H K : Subgroup G} (h : H ≤ K) : twoRes H ≤ twoRes K :=
  Subgroup.closure_mono fun _ hg => ⟨h hg.1, hg.2⟩

theorem sec7l78_odd_mem_twoRes {N : Subgroup G} {x : G} (hx : x ∈ N) (ho : Odd (orderOf x)) :
    x ∈ twoRes N :=
  Subgroup.subset_closure ⟨hx, ho⟩

theorem sec7l78_twoRes_eq_of_le {N H : Subgroup G} (h₁ : twoRes N ≤ H) (h₂ : H ≤ N) :
    twoRes H = twoRes N := by
  refine le_antisymm (sec7l78_twoRes_mono h₂) ((Subgroup.closure_le _).mpr fun g hg => ?_)
  exact sec7l78_odd_mem_twoRes (h₁ (sec7l78_odd_mem_twoRes hg.1 hg.2)) hg.2

private theorem sec7l78_odd_of_pow_three {x : G} (hx : x ^ 3 = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx)

private theorem sec7l78_mem_twoRes_of_pow_three {N : Subgroup G} {x : G} (hxN : x ∈ N)
    (hx : x ^ 3 = 1) : x ∈ twoRes N :=
  sec7l78_odd_mem_twoRes hxN (sec7l78_odd_of_pow_three hx)

private theorem sec7l78_pair_even :
    ∀ a b : Fin 5, ∑ i, (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) i = 0 := by
  decide +kernel

private theorem sec7l78_add_self : ∀ v p : Fin 5 → ZMod 2, v + p + p = v := by
  decide +kernel

variable {N B : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem Sec7E16Act.B_le_twoRes (h : Sec7E16Act N B φ) : B ≤ twoRes N := by
  have hpair : ∀ a b : Fin 5, a ≠ b →
      φ (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) ∈ twoRes N := by
    intro a b hab
    obtain ⟨τ, hτ, w, hw, hwτ⟩ := sec7l78_gen_pair a b hab
    obtain ⟨ν, hνN, hν3, hνact⟩ := h.exists_lift3 hτ
    have hwτ' : IsEvenVec (permVec τ w) := sec7l77_even_permVec τ hw
    have hc : φ w ∈ B := h.phi_mem hw
    have hcN : φ w ∈ N := h.le hc
    have hinv : (φ w)⁻¹ = φ w :=
      inv_eq_of_mul_eq_one_right (by simpa [sq] using h.elem.1.2 _ hc)
    have hform : φ (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) =
        (φ w * ν * (φ w)⁻¹) * ν⁻¹ := by
      rw [← hwτ, h.add hw hwτ', ← hνact w hw, hinv]
      group
    rw [hform]
    refine (twoRes N).mul_mem ?_ ?_
    · refine sec7l78_mem_twoRes_of_pow_three (N.mul_mem (N.mul_mem hcN hνN) (N.inv_mem hcN)) ?_
      rw [conj_pow, hν3]
      group
    · exact sec7l78_mem_twoRes_of_pow_three (N.inv_mem hνN) (by rw [inv_pow, hν3, inv_one])
  have key : ∀ n : ℕ, ∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = n → φ v ∈ twoRes N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hn
      by_cases hv0 : v = 0
      · rw [hv0, h.phi_zero]
        exact (twoRes N).one_mem
      · obtain ⟨a, b, hab, ha, hb⟩ := sec7l78_exists_pair v hv hv0
        obtain ⟨hlt, hpar⟩ := sec7l78_reduce v a b hab ha hb
        have hpe : IsEvenVec (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) :=
          sec7l78_pair_even a b
        have hv' : IsEvenVec (v + (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2)) := hpar hv
        have hrec := ih _ (hn ▸ hlt) _ hv' rfl
        have hsplit : v = (v + (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2)) +
            (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) := (sec7l78_add_self _ _).symm
        rw [hsplit, h.add hv' hpe]
        exact (twoRes N).mul_mem hrec (hpair a b hab)
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (h.mem_iff x).mp hx
  exact key _ v hv rfl

theorem Sec7E16Act.card_twoRes [Finite G] (h : Sec7E16Act N B φ) :
    Nat.card (twoRes N) = 960 := by
  let T : Subgroup ↥N := (alternatingGroup (Fin 5)).comap h.rho
  have hT : twoRes N = T.map N.subtype := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨hgN, hgo⟩
      refine ⟨⟨g, hgN⟩, ?_, rfl⟩
      show h.rho ⟨g, hgN⟩ ∈ alternatingGroup (Fin 5)
      rw [Equiv.Perm.mem_alternatingGroup]
      have hdvd : orderOf (h.rho ⟨g, hgN⟩) ∣ orderOf g := by
        have := orderOf_map_dvd h.rho (⟨g, hgN⟩ : ↥N)
        rwa [Subgroup.orderOf_mk] at this
      have hodd : Odd (orderOf (h.rho ⟨g, hgN⟩)) := Odd.of_dvd_nat hgo hdvd
      have hpow : (Equiv.Perm.sign (h.rho ⟨g, hgN⟩)) ^ orderOf (h.rho ⟨g, hgN⟩) = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (h.rho ⟨g, hgN⟩)) with h1 | h1
      · exact h1
      · rw [h1, Odd.neg_one_pow hodd] at hpow
        exact absurd hpow (by decide)
    · rintro _ ⟨x, hx, rfl⟩
      let W' : Subgroup ↥N := (twoRes N).comap N.subtype
      have hlift : ∀ τ : Equiv.Perm (Fin 5), τ.IsThreeCycle → τ ∈ W'.map h.rho := by
        intro τ hτ
        have hτ3 : τ ^ 3 = 1 := by
          rw [← hτ.orderOf]
          exact pow_orderOf_eq_one τ
        obtain ⟨ν, hνN, hν3, hνact⟩ := h.exists_lift3 hτ3
        refine ⟨⟨ν, hνN⟩, sec7l78_mem_twoRes_of_pow_three hνN hν3, ?_⟩
        exact h.act_unique (x := ν) (fun v hv => h.rho_spec ⟨ν, hνN⟩ hv) hνact
      have hA5 : alternatingGroup (Fin 5) ≤ W'.map h.rho := by
        rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
        exact (Subgroup.closure_le _).mpr fun τ hτ => hlift τ hτ
      obtain ⟨w, hw, hwx⟩ := hA5 (Subgroup.mem_comap.mp hx)
      have hkx : x * w⁻¹ ∈ h.rho.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, mul_inv_cancel]
      have hB' : ((x * w⁻¹ : ↥N) : G) ∈ B := (h.mem_ker_rho _).mp hkx
      have hmem : ((x * w⁻¹ : ↥N) : G) ∈ twoRes N := h.B_le_twoRes hB'
      have hw' : (w : G) ∈ twoRes N := hw
      have hxe : ((x : ↥N) : G) = ((x * w⁻¹ : ↥N) : G) * (w : G) := by simp
      rw [Subgroup.coe_subtype, hxe]
      exact (twoRes N).mul_mem hmem hw'
  have hcard : Nat.card (twoRes N) = Nat.card T := by
    rw [hT]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective T N.subtype N.subtype_injective).toEquiv.symm
  have hidx : T.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ h.rho_surjective]
    exact alternatingGroup.index_eq_two
  have h3 := Subgroup.index_mul_card T
  rw [hidx, h.card_N] at h3
  rw [hcard]
  omega

theorem Sec7E16Act.cent_twoRes (h : Sec7E16Act N B φ) {b : G} (hb : b ∈ B)
    (hc : ∀ x ∈ twoRes N, x * b = b * x) : b = 1 := by
  obtain ⟨τ₁, τ₂, h1, h2, hfix⟩ := sec7l78_two_cycles
  obtain ⟨ν₁, hν₁, hν₁3, hν₁act⟩ := h.exists_lift3 h1
  obtain ⟨ν₂, hν₂, hν₂3, hν₂act⟩ := h.exists_lift3 h2
  obtain ⟨v, hv, rfl⟩ := (h.mem_iff b).mp hb
  have hfix1 : ∀ (ν : G) (τ : Equiv.Perm (Fin 5)), ν ∈ twoRes N →
      (∀ w, IsEvenVec w → ν * φ w * ν⁻¹ = φ (permVec τ w)) → permVec τ v = v := by
    intro ν τ hν hact
    have h1 : ν * φ v * ν⁻¹ = φ v := by rw [hc ν hν]; group
    exact h.inj (sec7l77_even_permVec τ hv) hv ((hact v hv).symm.trans h1)
  have hv0 : v = 0 :=
    hfix v hv (hfix1 ν₁ τ₁ (sec7l78_mem_twoRes_of_pow_three hν₁ hν₁3) hν₁act)
      (hfix1 ν₂ τ₂ (sec7l78_mem_twoRes_of_pow_three hν₂ hν₂3) hν₂act)
  rw [hv0]
  exact h.phi_zero

theorem Sec7E16Act.stab_lifts [Finite G] (h : Sec7E16Act N B φ) {P : Subgroup G}
    (hP : IsSylow2Of P N) {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀1 : b₀ ≠ 1)
    (hPb : ∀ x ∈ P, x * b₀ = b₀ * x) :
    ∃ ν₁ ∈ N, ∃ ν₂ ∈ N, ν₁ ^ 3 = 1 ∧ ν₂ ^ 3 = 1 ∧ ν₁ * b₀ = b₀ * ν₁ ∧ ν₂ * b₀ = b₀ * ν₂ ∧
      ∀ b ∈ B, ν₁ * b = b * ν₁ → ν₂ * b = b * ν₂ → b = 1 ∨ b = b₀ := by
  obtain ⟨v₀, hv₀, rfl⟩ := (h.mem_iff b₀).mp hb₀
  have hv₀0 : v₀ ≠ 0 := fun h0 => hb₀1 (by rw [h0, h.phi_zero])
  let St : Subgroup (Equiv.Perm (Fin 5)) :=
    { carrier := {σ | permVec σ v₀ = v₀}
      mul_mem' := fun {σ τ} hσ hτ => by
        have hσ' : permVec σ v₀ = v₀ := hσ
        have hτ' : permVec τ v₀ = v₀ := hτ
        show permVec (σ * τ) v₀ = v₀
        rw [← sec7l77_permVec_mul, hτ', hσ']
      one_mem' := rfl
      inv_mem' := fun {σ} hσ => by
        have hσ' : permVec σ v₀ = v₀ := hσ
        show permVec σ⁻¹ v₀ = v₀
        calc permVec σ⁻¹ v₀ = permVec σ⁻¹ (permVec σ v₀) := by rw [hσ']
          _ = permVec (σ⁻¹ * σ) v₀ := sec7l77_permVec_mul _ _ _
          _ = v₀ := by rw [inv_mul_cancel, sec7l77_permVec_one] }
  let ψ : ↥P →* Equiv.Perm (Fin 5) := h.rho.comp (Subgroup.inclusion hP.1)
  have hrange : ψ.range ≤ St := by
    rintro _ ⟨x, rfl⟩
    show permVec (h.rho (Subgroup.inclusion hP.1 x)) v₀ = v₀
    have h1 := h.rho_spec (Subgroup.inclusion hP.1 x) hv₀
    have h2 : (x : G) * φ v₀ * (x : G)⁻¹ = φ v₀ := by rw [hPb x.1 x.2]; group
    exact h.inj (sec7l77_even_permVec _ hv₀) hv₀ (h1.symm.trans h2)
  have hker : Nat.card ψ.ker ∣ 16 := by
    have hle : ψ.ker.map P.subtype ≤ B := by
      rintro _ ⟨x, hx, rfl⟩
      exact (h.mem_ker_rho (Subgroup.inclusion hP.1 x)).mp hx
    have h1 : Nat.card (ψ.ker.map P.subtype) = Nat.card ψ.ker :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ P.subtype_injective).toEquiv.symm
    have h2 := Subgroup.card_dvd_of_le hle
    rw [h1, h.elem.2] at h2
    simpa using h2
  have hidx := Subgroup.index_mul_card ψ.ker
  rw [Subgroup.index_ker, h.card_sylow hP] at hidx
  have h8 : 8 ∣ Nat.card ψ.range := by
    obtain ⟨e, he⟩ := hker
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have h3 : Nat.card ψ.range * Nat.card ψ.ker = (8 * e) * Nat.card ψ.ker := by
      rw [hidx]
      calc 2 ^ 7 = 8 * 16 := by norm_num
        _ = 8 * (Nat.card ψ.ker * e) := by rw [he]
        _ = (8 * e) * Nat.card ψ.ker := by ring
    exact ⟨e, Nat.eq_of_mul_eq_mul_right hpos h3⟩
  have h8' : 8 ∣ Fintype.card {σ : Equiv.Perm (Fin 5) // permVec σ v₀ = v₀} := by
    have h1 : Nat.card ψ.range ∣ Nat.card St := Subgroup.card_dvd_of_le hrange
    have h2 : Nat.card St = Fintype.card {σ : Equiv.Perm (Fin 5) // permVec σ v₀ = v₀} := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => Iff.rfl)
    exact h8.trans (h2 ▸ h1)
  obtain ⟨τ₁, τ₂, h1, h2, hf1, hf2, hcomm⟩ := sec7l78_stab_eight v₀ hv₀ hv₀0 h8'
  obtain ⟨ν₁, hν₁, hν₁3, hν₁act⟩ := h.exists_lift3 h1
  obtain ⟨ν₂, hν₂, hν₂3, hν₂act⟩ := h.exists_lift3 h2
  have hcom : ∀ (ν : G) (τ : Equiv.Perm (Fin 5)),
      (∀ w, IsEvenVec w → ν * φ w * ν⁻¹ = φ (permVec τ w)) → permVec τ v₀ = v₀ →
      ν * φ v₀ = φ v₀ * ν := by
    intro ν τ hact hτ
    have h1 := hact v₀ hv₀
    rw [hτ] at h1
    calc ν * φ v₀ = (ν * φ v₀ * ν⁻¹) * ν := by group
      _ = φ v₀ * ν := by rw [h1]
  refine ⟨ν₁, hν₁, ν₂, hν₂, hν₁3, hν₂3, hcom ν₁ τ₁ hν₁act hf1, hcom ν₂ τ₂ hν₂act hf2, ?_⟩
  intro b hb hb1 hb2
  obtain ⟨w, hw, rfl⟩ := (h.mem_iff b).mp hb
  have hf : ∀ (ν : G) (τ : Equiv.Perm (Fin 5)),
      (∀ w, IsEvenVec w → ν * φ w * ν⁻¹ = φ (permVec τ w)) → ν * φ w = φ w * ν →
      permVec τ w = w := by
    intro ν τ hact hcm
    have h1 : ν * φ w * ν⁻¹ = φ w := by rw [hcm]; group
    exact h.inj (sec7l77_even_permVec τ hw) hw ((hact w hw).symm.trans h1)
  rcases hcomm w hw (hf ν₁ τ₁ hν₁act hb1) (hf ν₂ τ₂ hν₂act hb2) with h0 | h0
  · left
    rw [h0, h.phi_zero]
  · right
    rw [h0]

end CFSG.OddStandard.SmallF3.Omega
