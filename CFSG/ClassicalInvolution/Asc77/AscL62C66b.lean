module

public import CFSG.ClassicalInvolution.Asc77.AscL62C66a
public import CFSG.ClassicalInvolution.Asc77.AscSix66Cyc
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Asc77.AscL62Cent

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Algebra

variable {G : Type} [Group G] {x u u₁ u₂ : G}

theorem alg_u2 (hu₁ : u₁ = x * u * x⁻¹) (hu₂ : u₂ = x * u₁ * x⁻¹) (h01 : u * u₁ = u₁ * u)
    (hcx : x * (u⁻¹ * u₁) * x⁻¹ = u⁻¹ * u₁) : u₂ = u⁻¹ * (u₁ * u₁) := by
  have h1 : u₁⁻¹ * u₂ = u⁻¹ * u₁ := by
    have : x * (u⁻¹ * u₁) * x⁻¹ = u₁⁻¹ * u₂ := by
      rw [hu₂, hu₁]
      group
    rw [← this, hcx]
  have h2 : u₂ = u₁ * (u⁻¹ * u₁) := by
    calc u₂ = u₁ * (u₁⁻¹ * u₂) := by group
      _ = u₁ * (u⁻¹ * u₁) := by rw [h1]
  have h3 : u₁ * u⁻¹ = u⁻¹ * u₁ := (show Commute u u₁ from h01).inv_left.eq.symm
  calc u₂ = u₁ * (u⁻¹ * u₁) := h2
    _ = (u₁ * u⁻¹) * u₁ := by group
    _ = (u⁻¹ * u₁) * u₁ := by rw [h3]
    _ = u⁻¹ * (u₁ * u₁) := by group

theorem alg_u1_sq4 (hu₁ : u₁ = x * u * x⁻¹) (hu4 : (u * u) * (u * u) = 1) :
    (u₁ * u₁) * (u₁ * u₁) = 1 := by
  rw [hu₁]
  calc x * u * x⁻¹ * (x * u * x⁻¹) * (x * u * x⁻¹ * (x * u * x⁻¹))
      = x * ((u * u) * (u * u)) * x⁻¹ := by group
    _ = 1 := by rw [hu4]; group

theorem alg_u2_sq (hu2 : u₂ = u⁻¹ * (u₁ * u₁)) (h01 : u * u₁ = u₁ * u)
    (hu4 : (u * u) * (u * u) = 1) (hu1 : (u₁ * u₁) * (u₁ * u₁) = 1) : u₂ * u₂ = u * u := by
  have hc : Commute u⁻¹ u₁ := (show Commute u u₁ from h01).inv_left
  have hc' : (u₁ * u₁) * u⁻¹ = u⁻¹ * (u₁ * u₁) := (hc.mul_right hc).eq.symm
  have hinv : u⁻¹ * u⁻¹ = u * u := by
    have : (u * u)⁻¹ = u * u := inv_eq_of_mul_eq_one_right hu4
    rw [← this, mul_inv_rev]
  calc u₂ * u₂ = (u⁻¹ * (u₁ * u₁)) * (u⁻¹ * (u₁ * u₁)) := by rw [hu2]
    _ = u⁻¹ * ((u₁ * u₁) * u⁻¹) * (u₁ * u₁) := by group
    _ = u⁻¹ * (u⁻¹ * (u₁ * u₁)) * (u₁ * u₁) := by rw [hc']
    _ = (u⁻¹ * u⁻¹) * ((u₁ * u₁) * (u₁ * u₁)) := by group
    _ = u * u := by rw [hu1, hinv]; group

theorem alg_u3 (hu₁ : u₁ = x * u * x⁻¹) (hu₂ : u₂ = x * u₁ * x⁻¹)
    (hu2 : u₂ = u⁻¹ * (u₁ * u₁)) (hsq : u₂ * u₂ = u * u) :
    x * u₂ * x⁻¹ = u₁⁻¹ * (u * u) := by
  have e1 : x * u₂ * x⁻¹ = (x * u⁻¹ * x⁻¹) * (x * (u₁ * u₁) * x⁻¹) := by
    rw [hu2]
    group
  have e2 : x * u⁻¹ * x⁻¹ = u₁⁻¹ := by rw [hu₁]; group
  have e3 : x * (u₁ * u₁) * x⁻¹ = u₂ * u₂ := by rw [hu₂]; group
  rw [e1, e2, e3, hsq]

theorem alg_inv (hu₁ : u₁ = x * u * x⁻¹) (hu₂ : u₂ = x * u₁ * x⁻¹)
    (hu2 : u₂ = u⁻¹ * (u₁ * u₁)) (h01 : u * u₁ = u₁ * u) (hu1 : (u₁ * u₁) * (u₁ * u₁) = 1) :
    x * (u * u₁) * x⁻¹ = (u * u₁)⁻¹ := by
  have e1 : x * (u * u₁) * x⁻¹ = u₁ * u₂ := by
    rw [hu₂, hu₁]
    group
  have hc : Commute u⁻¹ u₁ := (show Commute u u₁ from h01).inv_left
  have h3 : u₁ * (u₁ * u₁) = u₁⁻¹ := by
    have : u₁ * (u₁ * (u₁ * u₁)) = 1 := by
      calc u₁ * (u₁ * (u₁ * u₁)) = (u₁ * u₁) * (u₁ * u₁) := by group
        _ = 1 := hu1
    exact eq_inv_of_mul_eq_one_right this
  have h4 : u₁⁻¹ * u⁻¹ = u⁻¹ * u₁⁻¹ := (hc.inv_right.eq).symm
  rw [e1, hu2]
  calc u₁ * (u⁻¹ * (u₁ * u₁)) = (u₁ * u⁻¹) * (u₁ * u₁) := by group
    _ = (u⁻¹ * u₁) * (u₁ * u₁) := by rw [← hc.eq]
    _ = u⁻¹ * (u₁ * (u₁ * u₁)) := by group
    _ = u⁻¹ * u₁⁻¹ := by rw [h3]
    _ = u₁⁻¹ * u⁻¹ := h4.symm
    _ = (u * u₁)⁻¹ := by rw [mul_inv_rev]

theorem alg_sq (h01 : u * u₁ = u₁ * u) : (u * u₁) * (u * u₁) = (u * u) * (u₁ * u₁) := by
  calc (u * u₁) * (u * u₁) = u * (u₁ * u) * u₁ := by group
    _ = u * (u * u₁) * u₁ := by rw [h01]
    _ = (u * u) * (u₁ * u₁) := by group

end Algebra

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem conjSub_zpowers_eq (x g : G) :
    conjSub x (Subgroup.zpowers g) = Subgroup.zpowers (x * g * x⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

theorem Pair.conjSub_eq_of_comm_z {K J : Subgroup G} {z t : G} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (h : Pair Ω K J z t) {x : G} (hxJ : x ∈ J) (hxo : orderOf x = 4)
    (hxz : x * z = z * x) : conjSub x K = K := by
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq h.hK h.hJ h.ne h.hz (Subgroup.zpowers_le.mpr hxJ)
      hV2 (by rw [Nat.card_zpowers, hxo]; norm_num)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxz))
  exact mem_normalizer_iff_conjSub_eq.mp (hle (Subgroup.mem_zpowers x))

namespace C66Data

variable {S : Subgroup G} {Δ : Set (Subgroup G)} {A B K J : Subgroup G} {z t : G}

theorem caseII (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (c : C66Data Ω S Δ A B K J z t) (hAt : ¬ conjSub t A = A) : False := by
  obtain ⟨u, huA, huo⟩ := exists_orderOf_four_of_cyclic c.hAc c.hA2 c.hA4
  obtain ⟨x, hxB, hxo⟩ := exists_orderOf_four_of_cyclic c.hBc c.hB2 c.hB4
  have huu : u * u = z := sq_eq_of_orderOf_four c.pair.hz (c.hAK huA) huo
  have hxx : x * x = t := sq_eq_of_orderOf_four c.pair.ht (c.hBJ hxB) hxo
  have huS : u ∈ S := c.hAS huA
  have hxS : x ∈ S := c.hBS hxB
  have hxA : ¬ conjSub x A = A := by
    intro h1
    apply hAt
    rw [← hxx, conjSub_mul, h1, h1]
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : G, u₁ = x * u * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : G, u₂ = x * u₁ * x⁻¹ := ⟨_, rfl⟩
  have hu4 : (u * u) * (u * u) = 1 := by rw [huu]; exact c.pair.hz.sq
  have h01 : u * u₁ = u₁ * u := by
    have := orbit_commute c.hAc c.hAorb S.one_mem hxS huA huA
    simp only [one_mul, inv_one, mul_one] at this
    rw [hu₁]
    exact this
  have hw : (u⁻¹ * x * u) * x = x * (u⁻¹ * x * u) := by
    have := orbit_commute c.hBc c.hBorb (S.inv_mem huS) S.one_mem hxB hxB
    simp only [inv_inv, one_mul, inv_one, mul_one] at this
    exact this
  have hcx : x * (u⁻¹ * u₁) * x⁻¹ = u⁻¹ * u₁ := by
    have e1 : u⁻¹ * u₁ = (u⁻¹ * x * u) * x⁻¹ := by rw [hu₁]; group
    rw [e1]
    calc x * ((u⁻¹ * x * u) * x⁻¹) * x⁻¹ = (x * (u⁻¹ * x * u)) * x⁻¹ * x⁻¹ := by group
      _ = ((u⁻¹ * x * u) * x) * x⁻¹ * x⁻¹ := by rw [← hw]
      _ = (u⁻¹ * x * u) * x⁻¹ := by group
  have hu2 : u₂ = u⁻¹ * (u₁ * u₁) := alg_u2 hu₁ hu₂ h01 hcx
  have hu1sq : (u₁ * u₁) * (u₁ * u₁) = 1 := alg_u1_sq4 hu₁ hu4
  have hu2sq : u₂ * u₂ = u * u := alg_u2_sq hu2 h01 hu4 hu1sq
  have hu3 : x * u₂ * x⁻¹ = u₁⁻¹ * (u * u) := alg_u3 hu₁ hu₂ hu2 hu2sq
  have hvinv : x * (u * u₁) * x⁻¹ = (u * u₁)⁻¹ := alg_inv hu₁ hu₂ hu2 h01 hu1sq
  have hvsq : (u * u₁) * (u * u₁) = (u * u) * (u₁ * u₁) := alg_sq h01
  have hzu2 : u * u₂ = u₁ * u₁ := by rw [hu2]; group
  have hzA : z ∈ A :=
    mem_of_uniqueInvolution_of_pGroup c.pair.hz c.hAK c.hA2 (by have := c.hA4; omega)
  obtain ⟨z₁, hz₁def⟩ : ∃ z₁ : G, z₁ = u₁ * u₁ := ⟨_, rfl⟩
  have hz₁eq : z₁ = x * z * x⁻¹ := by rw [hz₁def, hu₁, ← huu]; group
  have hK₁ : conjSub x K ∈ Ω := hΩ.conjInvariant x K c.pair.hK
  have hz₁ : IsUniqueInvolution (conjSub x K) z₁ := by
    rw [hz₁eq]
    exact c.pair.hz.conj x
  have hz₁ne : z₁ ≠ z := by
    intro h1
    have hxz : x * z = z * x := by
      have h2 : x * z * x⁻¹ = z := by rw [← hz₁eq]; exact h1
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [h2]
    have hxN : conjSub x K = K := c.pair.conjSub_eq_of_comm_z hp hq hΩ (c.hBJ hxB) hxo hxz
    have hA₁K : conjSub x A ≤ K := by
      have := conjSub_mono (n := x) c.hAK
      rwa [hxN] at this
    have hcomm : Commutes A (conjSub x A) :=
      c.hAorb A ⟨1, S.one_mem, (conjSub_one A).symm⟩ (conjSub x A) ⟨x, hxS, rfl⟩
        (fun h => hxA h.symm)
    have := eq_of_commutes_of_natCard_eq hp hΩ c.pair.hK c.pair.hz c.hAK hA₁K c.hAc
      (isCyclic_conjSub x c.hAc) c.hA2 (isPGroup_conjSub x c.hA2) c.hA4
      (natCard_conjSub x A).symm hcomm
    exact hxA this.symm
  have hu2conj : u₂ = (x * x) * u * (x * x)⁻¹ := by rw [hu₂, hu₁]; group
  have hzx : (x * x) * z * (x * x)⁻¹ = z := by
    calc (x * x) * z * (x * x)⁻¹
        = ((x * x) * u * (x * x)⁻¹) * ((x * x) * u * (x * x)⁻¹) := by rw [← huu]; group
      _ = u₂ * u₂ := by rw [hu2conj]
      _ = z := by rw [hu2sq, huu]
  have hK₂ : conjSub (x * x) K ∈ Ω := hΩ.conjInvariant _ K c.pair.hK
  have hz₂ : IsUniqueInvolution (conjSub (x * x) K) z := by
    have h1 := c.pair.hz.conj (x * x)
    rwa [hzx] at h1
  have hu₂K₂ : u₂ ∈ conjSub (x * x) K := by
    rw [hu2conj]
    exact conj_mem_conjSub (c.hAK huA)
  have hnc₁ : ¬ ∀ k ∈ K, ⁅z₁, k⁆ ∈ oddCoreOf K := by
    intro hz₁c
    by_cases hKK₂ : conjSub (x * x) K = K
    · have hu₂K : u₂ ∈ K := hKK₂ ▸ hu₂K₂
      have hz₁K : z₁ ∈ K := by
        rw [hz₁def, ← hzu2]
        exact K.mul_mem (c.hAK huA) hu₂K
      have hz₁sq : z₁ * z₁ = 1 := by rw [hz₁def]; exact hu1sq
      rcases c.pair.hz.unique z₁ hz₁K hz₁sq with h1 | h1
      · exact hz₁.ne_one h1
      · exact hz₁ne h1
    · have hcomm := hΩ.comm_le_oddCore_of_twin c.pair.hK hK₂ (Ne.symm hKK₂) c.pair.hz hz₂
      have hz₁uu : z₁ = u * u₂ := by rw [hz₁def, ← hzu2]
      have huc : ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K := by
        intro y hy
        have h1 : ⁅y, u₂⁆ ∈ oddCoreOf K :=
          (hcomm (Subgroup.commutator_mem_commutator hy hu₂K₂)).1
        have h2 : ⁅u₂, y⁆ ∈ oddCoreOf K := by
          rw [← commutatorElement_inv]
          exact (oddCoreOf K).inv_mem h1
        have h3 : u * ⁅u₂, y⁆ * u⁻¹ ∈ oddCoreOf K :=
          mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (c.hAK huA)) h2
        have h4 : ⁅z₁, y⁆ = (u * ⁅u₂, y⁆ * u⁻¹) * ⁅u, y⁆ := by
          rw [hz₁uu]
          simp only [commutatorElement_def]
          group
        have h5 : ⁅u, y⁆ = (u * ⁅u₂, y⁆ * u⁻¹)⁻¹ * ⁅z₁, y⁆ := by rw [h4]; group
        rw [h5]
        exact (oddCoreOf K).mul_mem ((oddCoreOf K).inv_mem h3) (hz₁c y hy)
      have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
        IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, huo]; norm_num)
      rcases hΩ.center_two hp hq c.pair.hK c.pair.hz u (c.hAK huA) hu2 huc with h1 | h1
      · rw [h1, orderOf_one] at huo
        omega
      · rw [h1] at huu
        have := c.pair.hz.sq
        rw [huu] at this
        exact c.pair.hz.ne_one this
  have hpair₁ : Pair Ω K (conjSub x K) z z₁ := ⟨c.pair.hK, hK₁, c.pair.hz, hz₁, hz₁ne.symm⟩
  have hu₁K₁ : u₁ ∈ conjSub x K := by
    rw [hu₁]
    exact conj_mem_conjSub (c.hAK huA)
  obtain ⟨r, hr1, hr2⟩ :=
    hpair₁.exists_swap hp hq hΩ (c.hAK huA) hu₁K₁ huu hz₁def.symm h01 hnc₁
  have hvK : ∃ Ke : Subgroup G, Ke ∈ Ω ∧ u * u₁ ∈ Ke := by
    rcases hr2 with h1 | h1
    · exact ⟨conjSub r (conjSub x K), hΩ.conjInvariant r _ hK₁, h1 ▸ conj_mem_conjSub hu₁K₁⟩
    · refine ⟨conjSub r (conjSub x (conjSub (x * x) K)),
        hΩ.conjInvariant r _ (hΩ.conjInvariant x _ hK₂), ?_⟩
      have hmem : r * (x * u₂ * x⁻¹) * r⁻¹ ∈ conjSub r (conjSub x (conjSub (x * x) K)) :=
        conj_mem_conjSub (conj_mem_conjSub hu₂K₂)
      have hval : r * (x * u₂ * x⁻¹) * r⁻¹ = (u * u₁)⁻¹ := by
        rw [hu3]
        have e1 : r * (u₁⁻¹ * (u * u)) * r⁻¹ =
            (r * u₁ * r⁻¹)⁻¹ * ((r * u * r⁻¹) * (r * u * r⁻¹)) := by group
        rw [e1, h1, hr1]
        group
      rw [hval] at hmem
      have := Subgroup.inv_mem _ hmem
      rwa [inv_inv] at this
  obtain ⟨Ke, hKe, hvKe⟩ := hvK
  obtain ⟨ze, hze⟩ := hΩ.exists_uniqueInvolution hp hq hKe
  have hvz : (u * u₁) * (u * u₁) = z * z₁ := by rw [hvsq, huu, hz₁def]
  have hzz₁ : z * z₁ ≠ 1 := by
    intro h1
    apply hz₁ne
    have h2 : z₁ = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right c.pair.hz.sq
  have hzz₁sq : (z * z₁) * (z * z₁) = 1 := by
    have hc : Commute u u₁ := h01
    have hcz : z * z₁ = z₁ * z := by
      rw [← huu, hz₁def]
      exact ((hc.mul_right hc).mul_left (hc.mul_right hc)).eq
    calc (z * z₁) * (z * z₁) = z * (z₁ * z) * z₁ := by group
      _ = z * (z * z₁) * z₁ := by rw [hcz]
      _ = (z * z) * (z₁ * z₁) := by group
      _ = 1 := by rw [c.pair.hz.sq, hz₁def, hu1sq]; group
  have hvKe2 : (u * u₁) * (u * u₁) ∈ Ke := Ke.mul_mem hvKe hvKe
  have hvze : (u * u₁) * (u * u₁) = ze := by
    rcases hze.unique _ hvKe2 (by rw [hvz]; exact hzz₁sq) with h1 | h1
    · exfalso
      rw [hvz] at h1
      exact hzz₁ h1
    · exact h1
  have hze_ne : ze ≠ t := by
    intro h1
    apply hAt
    apply conjSub_eq_of_centralizes
    intro a ha
    have hvt : t = z * z₁ := by rw [← h1, ← hvze, hvz]
    have h2 := orbit_commute c.hAc c.hAorb S.one_mem hxS ha hzA
    simp only [one_mul, inv_one, mul_one] at h2
    have h3 : a * z₁ = z₁ * a := by rw [hz₁eq]; exact h2
    have h4 : a * z = z * a := cyclic_comm c.hAc ha hzA
    rw [hvt]
    calc z * z₁ * a = z * (z₁ * a) := by group
      _ = z * (a * z₁) := by rw [h3]
      _ = (z * a) * z₁ := by group
      _ = (a * z) * z₁ := by rw [h4]
      _ = a * (z * z₁) := by group
  have hpairE : Pair Ω Ke J ze t := ⟨hKe, c.pair.hJ, hze, c.pair.ht, hze_ne⟩
  have hvo : orderOf (u * u₁) = 4 := by
    have hv4 : (u * u₁) ^ 4 = 1 := by
      have : (u * u₁) ^ 4 = ((u * u₁) * (u * u₁)) * ((u * u₁) * (u * u₁)) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [this, hvz]
      exact hzz₁sq
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u * u₁)
      (by simpa [pow_two, hvz] using hzz₁) (by simpa using hv4)
    simpa using this
  have hconjv : conjSub x (Subgroup.zpowers (u * u₁)) = Subgroup.zpowers (u * u₁) := by
    rw [conjSub_zpowers_eq, hvinv, Subgroup.zpowers_inv]
  have hv2 : IsPGroup 2 ↥(Subgroup.zpowers (u * u₁)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hvo]; norm_num)
  have hcent := hpairE.centralizes_of_normalizes hp hq hΩ (c.hBJ hxB) hxx
    (Subgroup.zpowers_le.mpr hvKe) inferInstance hv2 hconjv (u * u₁) (Subgroup.mem_zpowers _)
  have h5 : x * (u * u₁) * x⁻¹ = u * u₁ := by
    calc x * (u * u₁) * x⁻¹ = ((u * u₁) * x) * x⁻¹ := by rw [← hcent]
      _ = u * u₁ := by group
  rw [hvinv] at h5
  have h6 : (u * u₁) * (u * u₁) = 1 := by
    calc (u * u₁) * (u * u₁) = (u * u₁) * (u * u₁)⁻¹ := by rw [h5]
      _ = 1 := mul_inv_cancel _
  rw [hvz] at h6
  exact hzz₁ h6

end C66Data

theorem core66 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) : Core66 Ω := by
  intro S hS Δ hΔS hΔinv hcyc hpair A hA B hB hne hAorb hBorb
  by_contra hnc
  obtain ⟨K, hK, J, hJ, hKJ, hAK, hBJ⟩ := hpair A hA B hB hne
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hzt : z ≠ t := by
    intro hzt
    have hzJ : IsUniqueInvolution J z := by rw [hzt]; exact ht
    exact hnc (hΩ.commutes_of_twin_of_isPGroup hK hJ hKJ hz hzJ hAK hBJ
      (hS.to_le (sup_le (hΔS A hA) (hΔS B hB))))
  have c : C66Data Ω S Δ A B K J z t :=
    ⟨hS, hΔS, hΔinv, hcyc, hpair, hA, hB, hAorb, hBorb, hAK, hBJ, ⟨hK, hJ, hz, ht, hzt⟩, hnc⟩
  by_cases hAt : conjSub t A = A
  · exact c.caseI hp hq hΩ hAt
  · exact c.caseII hp hq hΩ hAt

end CFSG.ClassicalInvolution.Asc77.AscL62
