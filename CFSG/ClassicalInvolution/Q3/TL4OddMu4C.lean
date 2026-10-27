module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4W
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9WC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Quat

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem nonempty_quot_quat (hΩ : TypeRFam r Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nonempty (↥K ⧸ CFSG.oddCore ↥K ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := Disconnected.AschTight.Sec7.exists_isSylow2In K
  obtain ⟨eR⟩ := hΩ.quat K hK R hR
  let S : Sylow 2 ↥K :=
    { toSubgroup := R.subgroupOf K
      isPGroup' := hR.2.1.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hVQ : R ≤ Q.map K.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hR.1]
          exact Subgroup.map_mono hle
        have := hR.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
        rfl }
  let eS : (S : Subgroup ↥K) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.subgroupOfEquivOfLe hR.1).trans eR
  obtain ⟨P⟩ : Nonempty (Sylow 2 (↥K ⧸ CFSG.oddCore ↥K)) := inferInstance
  have h2 : IsPGroup 2 (↥K ⧸ CFSG.oddCore ↥K) := hΩ.twoGroup K hK
  have hPtop : (P : Subgroup (↥K ⧸ CFSG.oddCore ↥K)) = ⊤ :=
    (P.is_maximal' (IsPGroup.of_equiv h2 Subgroup.topEquiv.symm) le_top).symm
  obtain ⟨f⟩ := QuaternionStructure.sylow_oddCore_quotient_quaternion S eS P
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hPtop.symm)).trans f⟩

theorem exists_derived_trivialOnQuot (hΩ : TypeRFam r Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ n : ℕ, ∀ {X : Subgroup G} {x b : G}, X ≤ Subgroup.normalizer (K : Set G) → x ∈ X →
      x * x = 1 → ∀ hb : b ∈ X, (⟨b, hb⟩ : X) ∈ derivedSeries X n →
        Odd (orderOf (b⁻¹ * x)) → x ∈ trivialOnQuot K := by
  obtain ⟨e⟩ := nonempty_quot_quat hΩ hK
  obtain ⟨n, hn⟩ := (Group.isSolvable_def (G := MulAut (QuaternionGroup (2 ^ (r - 2))))).mp
    (ProperTwoGeneratedCore.quaternion_power_two_automorphism_solvable (r - 2))
  refine ⟨n, fun {X x b} hXK hx hx2 hb hb3 hodd => ?_⟩
  set ρ := (NDB.WC.autCongr e).comp (tl3Act K) with hρ
  set φ := ρ.comp (Subgroup.inclusion hXK) with hφ
  have hφb : φ ⟨b, hb⟩ = 1 := by
    have h1 : φ ⟨b, hb⟩ ∈ (derivedSeries X n).map φ := ⟨_, hb3, rfl⟩
    have h2 := map_derivedSeries_le_derivedSeries φ n h1
    rwa [hn, Subgroup.mem_bot] at h2
  set c : X := (⟨b, hb⟩ : X)⁻¹ * ⟨x, hx⟩ with hc
  have hφx : φ ⟨x, hx⟩ = φ c := by
    rw [hc, map_mul, map_inv, hφb, inv_one, one_mul]
  have hoc : Odd (orderOf (φ c)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd φ c)
    rw [← Subgroup.orderOf_coe]
    exact hodd
  have h2 : orderOf (φ ⟨x, hx⟩) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_two]
    have : (⟨x, hx⟩ : X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  rw [hφx] at h2
  have h1 : orderOf (φ c) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hoc
      exact absurd hoc (by decide)
  rw [orderOf_eq_one_iff, ← hφx] at h1
  have h3 : ρ ⟨x, hXK hx⟩ = 1 := h1
  rw [hρ, MonoidHom.comp_apply, NDB.WC.autCongr_eq_one_iff] at h3
  exact ⟨hXK hx, (tl3Act_eq_one_iff K _).mp h3⟩

end Quat

section WC

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem weakClosure_of_linkLayer (hΩ : TypeRFam r Ω) {K : Subgroup G} {z : G} (hKΩ : K ∈ Ω)
    (hz : IsUniqueInvolution K z) {s : G} {L : Subgroup G}
    (hL : Q3AM.Psp9Layer (linkLayerAt Ω K z) s z L) {h : G}
    (hh : h ∈ Subgroup.centralizer ({s} : Set G))
    (hR : ∀ x ∈ modOdd s (conjSub h L), ∀ y ∈ modOdd s L, x * y = y * x) :
    modOdd s (conjSub h L) = modOdd s L := by
  classical
  have hz2 : z * z = 1 := hz.sq
  have hCK : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K := fun g hg =>
    conjSub_eq_of_mem_normalizer (hΩ.tight K hKΩ z hz hg)
  obtain ⟨n, hD3⟩ := exists_derived_trivialOnQuot hΩ hKΩ
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  set Cz := Subgroup.centralizer ({z} : Set G) with hCz
  set Y := linkLayerAt Ω K z with hY
  have hYz : Y ≤ Cz := linkLayerAt_le_centralizer
  have hLY : L ≤ Y := hL.le
  have hLCz : L ≤ Cz ⊓ Cs := fun l hl => ⟨isSubnormal_le hL.mem.subnormal hl |>.1, hL.mem.le hl⟩
  by_contra hne
  have hLs : L ≤ Cs := hL.mem.le
  have hLp : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.mem.perfect
  have hz₁L : z ∈ L := hL.mem.mem
  have hz₁s : z ∈ Cs := hLs hz₁L
  have hLn : ∀ g ∈ Cz ⊓ Cs, conjSub g L = L := fun g hg => hL.norm g hg.1 hg.2
  obtain ⟨u, h', huC, hune, huz, huh, hu2, huR, huMO⟩ :=
    Q3AM.exists_involution_of_commuting_conj hz2 hz₁L hLCz hLn hh hR hne
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
    NDB.WC.le_map_derivedSeries ψX hRle (NDB.WC.commutator_modOdd hMs hMp) n huR
  have hamem : (a' : G)⁻¹ * u ∈ O := by
    have h1 : oddQuotMk s ((Subgroup.inclusion hXs a')⁻¹ * ⟨u, huC⟩) = 1 := by
      have e : oddQuotMk s (Subgroup.inclusion hXs a') = oddQuotMk s ⟨u, huC⟩ := ha'
      rw [map_mul, map_inv, e, inv_mul_cancel]
    exact ⟨_, oddQuotMk_eq_one_iff.mp h1, rfl⟩
  have hnormK : X ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    NDB.WC.mem_normalizer_of_conjSub_eq (hCK x (Subgroup.mem_inf.mp hx).2)
  have hutq : u ∈ trivialOnQuot K :=
    hD3 hnormK huX hu2 a'.2 ha'3 (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hamem))
  have hNΩ : conjSub h' K ∈ Ω := hΩ.hyp.conjInvariant h' K hKΩ
  have hNu : IsUniqueInvolution (conjSub h' K) u := by
    rw [huh]
    exact hz.conj h'
  have hKN : K ≠ conjSub h' K := by
    intro heq
    have h1 : IsUniqueInvolution K u := heq ▸ hNu
    exact hune (hz.eq h1).symm
  have hKnbr : K ∈ omegaNbr Ω (conjSub h' K) :=
    Q3T6D.mem_omegaNbr_of_trivialOnQuotGen hΩ.hyp hNΩ hNu hKΩ hKN hutq
  have hNnbr : conjSub h' K ∈ omegaNbr Ω K :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ.hyp hNΩ hKΩ hKnbr
  have huY : u ∈ Y :=
    coreAt_le_linkLayerAt hNnbr (mem_coreAt_of_sq_sq hNu.mem (by rw [hu2, one_mul]) huz)
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

end WC

end CFSG.ClassicalInvolution.Q3.TL4
