module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadNbhd
public import CFSG.ClassicalInvolution.SmallCases.NDB5dWC0

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Defs

variable {G : Type} [Group G]

structure Psp9Layer (Y : Subgroup G) (s a : G) (L : Subgroup G) : Prop where
  le : L ≤ Y
  mem : IsSectionMember 3 2 (Subgroup.centralizer ({s} : Set G)) L a
  norm : ∀ g ∈ Subgroup.centralizer ({a} : Set G), g ∈ Subgroup.centralizer ({s} : Set G) →
    conjSub g L = L
  oddCore : L ⊓ oddCoreIn (Subgroup.centralizer ({s} : Set G)) ≤
    oddCoreIn (Subgroup.centralizer ({a} : Set G))
  inv : ∀ x ∈ Y, x ∈ Subgroup.centralizer ({s} : Set G) → x * x = 1 →
    (∀ l ∈ L, x⁻¹ * l⁻¹ * x * l ∈ oddCoreIn Y) → x = 1 ∨ x * a ∈ oddCoreIn Y

end Defs

section Wrapper

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_of_commuting_conj {z s : G} {L₁ : Subgroup G} (hz2 : z * z = 1)
    (hz₁L : z ∈ L₁)
    (hL₁ : L₁ ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G))
    (hL₁n : ∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G),
      conjSub g L₁ = L₁)
    {h : G} (hh : h ∈ Subgroup.centralizer ({s} : Set G))
    (hR : ∀ x ∈ modOdd s (conjSub h L₁), ∀ y ∈ modOdd s L₁, x * y = y * x)
    (hne : modOdd s (conjSub h L₁) ≠ modOdd s L₁) :
    ∃ (u h' : G) (huC : u ∈ Subgroup.centralizer ({s} : Set G)), u ≠ z ∧ u * z = z * u ∧
      u = h' * z * h'⁻¹ ∧ u * u = 1 ∧ oddQuotMk s ⟨u, huC⟩ ∈ modOdd s (conjSub h L₁) ∧
      u ∈ conjSub h L₁ ⊔ oddCoreIn (Subgroup.centralizer ({s} : Set G)) := by
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  set Cz := Subgroup.centralizer ({z} : Set G) with hCz
  set O := oddCoreIn Cs with hO
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn Cs
  have hOs : O ≤ Cs := oddCoreIn_le Cs
  have hz₁s : z ∈ Cs := (hL₁ hz₁L).2
  have hz₁i : z⁻¹ = z := (eq_inv_of_mul_eq_one_left hz2).symm
  have hz₁O : ∀ o ∈ O, z * o * z ∈ O := fun o ho => by
    have := conj_mem_oddCoreIn hz₁s ho
    rwa [hz₁i] at this
  set M := conjSub h L₁ with hM
  have hMs : M ≤ Cs := by
    rintro _ ⟨l, hl, rfl⟩
    exact Cs.mul_mem (Cs.mul_mem hh (hL₁ hl).2) (Cs.inv_mem hh)
  have hcomm : ∀ m ∈ M, m⁻¹ * z⁻¹ * m * z ∈ O := fun m hm =>
    NDB.WC.comm_mem_oddCoreIn (hMs hm) hz₁s
      (hR _ (oddQuotMk_mem_modOdd hm (hMs hm)) _ (oddQuotMk_mem_modOdd hz₁L hz₁s))
  set u := h * z * h⁻¹ with hu
  have huM : u ∈ M := ⟨z, hz₁L, rfl⟩
  have hu2 : u * u = 1 := by
    calc u * u = h * (z * z) * h⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hz2]; group
  set c := u⁻¹ * z⁻¹ * u * z with hc
  have hcO : c ∈ O := hcomm u huM
  have huc : u * c = z⁻¹ * u * z := by rw [hc]; group
  have huc2 : u * c * (u * c) = 1 := by
    rw [huc]
    calc z⁻¹ * u * z * (z⁻¹ * u * z) = z⁻¹ * (u * u) * z := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨w₀, hw₀, hw₀u⟩ :=
    NDB.WC.inv_conj_of_odd hu2 (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hcO)) huc2
  have hw₀O : w₀ ∈ O := (Subgroup.zpowers_le.mpr hcO) hw₀
  have e₀ : z * u * z = w₀⁻¹ * u * w₀ := by
    have := huc.symm.trans hw₀u
    rwa [hz₁i] at this
  have hgu : w₀ * z * u = u * (w₀ * z) := by
    calc w₀ * z * u = w₀ * (z * u * z) * z⁻¹ := by group
      _ = w₀ * (w₀⁻¹ * u * w₀) * z⁻¹ := by rw [e₀]
      _ = u * (w₀ * z⁻¹) := by group
      _ = u * (w₀ * z) := by rw [hz₁i]
  have ho₀O : z * w₀ * z ∈ O := hz₁O w₀ hw₀O
  have hg : z * (z * w₀ * z) = w₀ * z := by
    calc z * (z * w₀ * z) = (z * z) * w₀ * z := by group
      _ = w₀ * z := by rw [hz2, one_mul]
  obtain ⟨w, hwO, hwz⟩ := NDB.WC.exists_conj_mem_zpowers hOodd hz2 hz₁O ho₀O
  rw [hg] at hwz
  have hwzu : w⁻¹ * z * w * u = u * (w⁻¹ * z * w) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hk]
    exact (Commute.zpow_left hgu k).eq
  set u' := w * u * w⁻¹ with hu'
  have hu'z : u' * z = z * u' := by
    calc u' * z = w * (u * (w⁻¹ * z * w)) * w⁻¹ := by rw [hu']; group
      _ = w * (w⁻¹ * z * w * u) * w⁻¹ := by rw [hwzu]
      _ = z * u' := by rw [hu']; group
  set h' := w * h with hh'
  have hh'C : h' ∈ Cs := Cs.mul_mem (hOs hwO) hh
  have hu'h : u' = h' * z * h'⁻¹ := by rw [hu', hu, hh']; group
  have hu'2 : u' * u' = 1 := by
    calc u' * u' = w * (u * u) * w⁻¹ := by rw [hu']; group
      _ = 1 := by rw [hu2]; group
  have hM' : modOdd s (conjSub h' L₁) = modOdd s M := by
    rw [hh', conjSub_mul]
    exact Asc77.modOdd_conjSub_of_mem_oddCoreIn hwO M
  have hu'L : u' ∈ conjSub h' L₁ := by
    rw [hu'h]
    exact ⟨z, hz₁L, rfl⟩
  have hu'ne : u' ≠ z := by
    intro heq
    apply hne
    have hh'z : h' ∈ Cz := by
      rw [hCz, Subgroup.mem_centralizer_singleton_iff]
      have e := hu'h.symm.trans heq
      calc h' * z = (h' * z * h'⁻¹) * h' := by group
        _ = z * h' := by rw [e]
    rw [← hM', hL₁n h' ⟨hh'z, hh'C⟩]
  have hu'C : u' ∈ Cs := by
    rw [hu'h]
    exact Cs.mul_mem (Cs.mul_mem hh'C hz₁s) (Cs.inv_mem hh'C)
  have hu'R : oddQuotMk s ⟨u', hu'C⟩ ∈ modOdd s M := hM' ▸ oddQuotMk_mem_modOdd hu'L hu'C
  have hu'MO : u' ∈ M ⊔ O := by
    rw [hu']
    exact (M ⊔ O).mul_mem ((M ⊔ O).mul_mem (Subgroup.mem_sup_right hwO)
      (Subgroup.mem_sup_left huM)) (Subgroup.mem_sup_right (O.inv_mem hwO))
  exact ⟨u', h', hu'C, hu'ne, hu'z, hu'h, hu'2, hu'R, hu'MO⟩

end Wrapper

section Core

open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CP


variable {G : Type} [Group G] [Finite G]

theorem weakClosure_of_layer [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hbad : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z) {s : G}
    {L : Subgroup G} (hL : Psp9Layer (nbrLayer Ω K z) s z L)
    (hD3 : ∀ {X : Subgroup G} {x a : G}, X ≤ Subgroup.normalizer (K : Set G) → x ∈ X →
      x * x = 1 → ∀ ha : a ∈ X, (⟨a, ha⟩ : X) ∈ derivedSeries X 3 →
        Odd (orderOf (a⁻¹ * x)) → x ∈ trivialOnQuot K)
    {h : G} (hh : h ∈ Subgroup.centralizer ({s} : Set G))
    (hR : ∀ x ∈ modOdd s (conjSub h L), ∀ y ∈ modOdd s L, x * y = y * x) :
    modOdd s (conjSub h L) = modOdd s L := by
  classical
  have hstd := hbad.std
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hstd.stand.hyp
  have hKΩ : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  have hz2 : z * z = 1 := hz.sq
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hCK : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hKΩ (hnt K hKΩ) hz hg)
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  set Cz := Subgroup.centralizer ({z} : Set G) with hCz
  set Y := nbrLayer Ω K z with hY
  have hYz : Y ≤ Cz := nbrLayer_le_centralizer Ω K z
  have hLY : L ≤ Y := hL.le
  have hLCz : L ≤ Cz ⊓ Cs := fun l hl => ⟨isSubnormal_le hL.mem.subnormal hl |>.1, hL.mem.le hl⟩
  by_contra hne
  have hLs : L ≤ Cs := hL.mem.le
  have hLp : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.mem.perfect
  have hz₁L : z ∈ L := hL.mem.mem
  have hz₁s : z ∈ Cs := hLs hz₁L
  have hLn : ∀ g ∈ Cz ⊓ Cs, conjSub g L = L := fun g hg => hL.norm g hg.1 hg.2
  obtain ⟨u, h', huC, hune, huz, huh, hu2, huR, huMO⟩ :=
    exists_involution_of_commuting_conj hz2 hz₁L hLCz hLn hh hR hne
  set O := oddCoreIn Cs with hO
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn Cs
  have hOs : O ≤ Cs := oddCoreIn_le Cs
  have hz₁i : z⁻¹ = z := (eq_inv_of_mul_eq_one_left hz2).symm
  set M := conjSub h L with hM
  have hMs : M ≤ Cs := by
    rintro _ ⟨l, hl, rfl⟩
    exact Cs.mul_mem (Cs.mul_mem hh (hLs hl)) (Cs.inv_mem hh)
  have hMp : ⁅M, M⁆ = M := by
    rw [hM, conjSub, ← Subgroup.map_commutator, hLp]
  set X := (M ⊔ O) ⊓ Cz with hX
  have hXs : X ≤ Cs := fun x hx => (sup_le hMs hOs) (Subgroup.mem_inf.mp hx).1
  have huX : u ∈ X := ⟨huMO, Subgroup.mem_centralizer_singleton_iff.mpr huz⟩
  set ψX : X →* OddQuot s := (oddQuotMk s).comp (Subgroup.inclusion hXs) with hψX
  have hz₁O : ∀ o ∈ O, z * o * z ∈ O := fun o ho => by
    have := conj_mem_oddCoreIn hz₁s ho
    rwa [hz₁i] at this
  have hRle : modOdd s M ≤ ψX.range := by
    rintro _ ⟨⟨m, hmC⟩, hm, rfl⟩
    have h1 : m⁻¹ * z * m * z ∈ O := by
      have := NDB.WC.comm_mem_oddCoreIn hmC hz₁s
        (hR _ ⟨⟨m, hmC⟩, hm, rfl⟩ _ (oddQuotMk_mem_modOdd hz₁L hz₁s))
      rwa [hz₁i] at this
    obtain ⟨w', hw'O, hw'⟩ := NDB.WC.exists_mul_mem_centralizer hOodd hz2 hz₁O h1
    have hmX : m * w'⁻¹ ∈ X := ⟨(M ⊔ O).mul_mem (Subgroup.mem_sup_left hm)
      (Subgroup.mem_sup_right (O.inv_mem hw'O)), hw'⟩
    refine ⟨⟨m * w'⁻¹, hmX⟩, ?_⟩
    have e : Subgroup.inclusion hXs ⟨m * w'⁻¹, hmX⟩ =
        (⟨m, hmC⟩ : Cs) * ⟨w'⁻¹, hOs (O.inv_mem hw'O)⟩ := rfl
    rw [hψX, MonoidHom.comp_apply, e, map_mul,
      oddQuotMk_eq_one_of_mem_oddCoreIn (O.inv_mem hw'O), mul_one]
  obtain ⟨a', ha'3, ha'⟩ :=
    NDB.WC.le_map_derivedSeries ψX hRle (NDB.WC.commutator_modOdd hMs hMp) 3 huR
  have hamem : (a' : G)⁻¹ * u ∈ O := by
    have h1 : oddQuotMk s ((Subgroup.inclusion hXs a')⁻¹ * ⟨u, huC⟩) = 1 := by
      have e : oddQuotMk s (Subgroup.inclusion hXs a') = oddQuotMk s ⟨u, huC⟩ := ha'
      rw [map_mul, map_inv, e, inv_mul_cancel]
    exact ⟨_, oddQuotMk_eq_one_iff.mp h1, rfl⟩
  have hnormK : X ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    NDB.WC.mem_normalizer_of_conjSub_eq (hCK x (Subgroup.mem_inf.mp hx).2)
  have hutq : u ∈ trivialOnQuot K :=
    hD3 hnormK huX hu2 a'.2 ha'3 (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hamem))
  have hNΩ : conjSub h' K ∈ Ω := hΩ.conjInvariant h' K hKΩ
  have hNu : IsUniqueInvolution (conjSub h' K) u := by
    rw [huh]
    exact hz.conj h'
  have hKN : K ≠ conjSub h' K := by
    intro heq
    have h1 : IsUniqueInvolution K u := heq ▸ hNu
    exact hune (hz.eq h1).symm
  have hKnbr : K ∈ omegaNbr Ω (conjSub h' K) :=
    Q3T6D.mem_omegaNbr_of_trivialOnQuotGen hΩ hNΩ hNu hKΩ hKN hutq
  have hNnbr : conjSub h' K ∈ omegaNbr Ω K :=
    mem_omegaNbr_symm hbad hint hNΩ hKnbr hNu hz
  have huY : u ∈ Y :=
    exactCore3_le_nbrLayer hNnbr ⟨hNu.mem, Subgroup.mem_centralizer_singleton_iff.mpr huz⟩
  have huCz : u ∈ Cz := Subgroup.mem_centralizer_singleton_iff.mpr huz
  have hubL : ∀ l ∈ L, u⁻¹ * l⁻¹ * u * l ∈ oddCoreIn Y := by
    intro l hl
    have hls : l ∈ Cs := hLs hl
    have h1 : u⁻¹ * l⁻¹ * u * l ∈ O :=
      NDB.WC.comm_mem_oddCoreIn huC hls (hR _ huR _ (oddQuotMk_mem_modOdd hl hls))
    have h2 : u⁻¹ * l⁻¹ * u * l ∈ L := by
      have hn := hLn u⁻¹ ⟨Cz.inv_mem huCz, Cs.inv_mem huC⟩
      have h3 : u⁻¹ * l⁻¹ * u ∈ L := by
        rw [← hn]
        refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
        show u⁻¹ * l⁻¹ * u⁻¹⁻¹ = u⁻¹ * l⁻¹ * u
        rw [inv_inv]
      exact L.mul_mem h3 hl
    have h4 : u⁻¹ * l⁻¹ * u * l ∈ oddCoreIn Cz := hL.oddCore ⟨h2, h1⟩
    have h5 : u⁻¹ * l⁻¹ * u * l ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem huY) (Y.inv_mem (hLY hl))) huY) (hLY hl)
    have hS : oddCoreIn Cz ⊓ Y ≤ oddCoreIn Y := by
      refine le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
      · intro y hy
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have hyC : y ∈ Cz := hYz hy
        constructor
        · rintro ⟨hx1, hx2⟩
          exact ⟨conj_mem_oddCoreIn hyC hx1, Y.mul_mem (Y.mul_mem hy hx2) (Y.inv_mem hy)⟩
        · rintro ⟨hx1, hx2⟩
          have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
          refine ⟨?_, ?_⟩
          · have h3 := conj_mem_oddCoreIn (Cz.inv_mem hyC) hx1
            rw [inv_inv] at h3
            rw [e]
            exact h3
          · rw [e]
            exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hx2) hy
      · exact (odd_card_oddCoreIn Cz).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    exact hS ⟨h4, h5⟩
  rcases hL.inv u huY huC hu2 hubL with h1 | h1
  · apply hz.ne_one
    calc z = h'⁻¹ * (h' * z * h'⁻¹) * h' := by group
      _ = 1 := by rw [← huh, h1]; group
  · have huz2 : (u * z) * (u * z) = 1 := by
      calc (u * z) * (u * z) = u * (z * u) * z := by group
        _ = u * (u * z) * z := by rw [← huz]
        _ = (u * u) * (z * z) := by group
        _ = 1 := by rw [hu2, hz2, one_mul]
    have hodd1 : Odd (orderOf (u * z)) := by
      have h2 := Subgroup.orderOf_dvd_natCard (oddCoreIn Y) (show u * z ∈ oddCoreIn Y from h1)
      exact (odd_card_oddCoreIn Y).of_dvd_nat h2
    have hdvd : orderOf (u * z) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact huz2)
    have hord : orderOf (u * z) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h2 | h2
      · exact h2
      · rw [h2] at hodd1
        exact absurd hodd1 (by decide)
    have huz1 : u * z = 1 := orderOf_eq_one_iff.mp hord
    exact hune (by
      calc u = u * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [huz1, one_mul])

end Core

end CFSG.ClassicalInvolution.Q3.Q3AM
