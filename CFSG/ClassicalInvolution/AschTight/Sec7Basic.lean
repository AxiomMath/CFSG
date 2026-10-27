module

public import CFSG.ClassicalInvolution.Asc77.AscSix69

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

@[expose] def WeaklyClosedIn (A S : Subgroup G) : Prop :=
  ∀ g : G, conjSub g A ≤ S → conjSub g A = A

theorem conjSub_eq_of_le_self [Finite G] {A : Subgroup G} {g : G} (h : conjSub g A ≤ A) :
    conjSub g A = A :=
  Subgroup.eq_of_le_of_card_ge h (by rw [natCard_conjSub])

theorem conjSub_eq_of_le_self' [Finite G] {A : Subgroup G} {g : G} (h : A ≤ conjSub g A) :
    conjSub g A = A :=
  (Subgroup.eq_of_le_of_card_ge h (by rw [natCard_conjSub])).symm

theorem conjSub_inv_eq {A : Subgroup G} {k : G} (h : conjSub k A = A) : conjSub k⁻¹ A = A := by
  conv_lhs => rw [← h]
  rw [conjSub_inv_conjSub]

theorem WeaklyClosedIn.of_sylow [Finite G] {A : Subgroup G} {S S' : Sylow 2 G}
    (h : WeaklyClosedIn A S) (hAS' : A ≤ S') : WeaklyClosedIn A S' := by
  obtain ⟨k, hk⟩ := exists_conjSub_eq_of_sylow S S'
  have h2 : conjSub k⁻¹ A = A := h _ (by rw [conjSub_le_iff, inv_inv, hk]; exact hAS')
  have h2' : conjSub k A = A := by simpa using conjSub_inv_eq h2
  intro g hg
  have h4 := h (k⁻¹ * g) (by rw [conjSub_mul, conjSub_le_iff, inv_inv, hk]; exact hg)
  rw [conjSub_mul] at h4
  have h5 := congrArg (conjSub k) h4
  rw [conjSub_conjSub_inv] at h5
  rw [h5, h2']

theorem WeaklyClosedIn.eq_of_le_of_isPGroup [Finite G] {A : Subgroup G} {S : Sylow 2 G}
    (h : WeaklyClosedIn A S) {P : Subgroup G} (hP : IsPGroup 2 P) (hAP : A ≤ P) {g : G}
    (hgP : conjSub g A ≤ P) : conjSub g A = A := by
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  exact (h.of_sylow (hAP.trans hS')) g (hgP.trans hS')

theorem exists_conj_le_of_isSylow2In [Finite G] {P Y U : Subgroup G} (hP : IsSylow2In P Y)
    (hU : IsPGroup 2 U) (hUY : U ≤ Y) : ∃ y ∈ Y, U ≤ conjSub y P := by
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (hP.2.1.comap_subtype (K := Y))
  have hPQ : (Q : Subgroup ↥Y).map Y.subtype = P :=
    hP.2.2 _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _) fun x hx =>
      ⟨⟨x, hP.1 hx⟩, hQ (show (⟨x, hP.1 hx⟩ : ↥Y) ∈ P.subgroupOf Y from
        Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow (hU.comap_subtype (K := Y))
  obtain ⟨y, hy⟩ := exists_conjSub_eq_of_sylow (G := ↥Y) Q Q'
  refine ⟨y, y.2, fun x hx => ?_⟩
  have hxQ' : (⟨x, hUY hx⟩ : ↥Y) ∈ (Q' : Subgroup ↥Y) :=
    hQ' (show (⟨x, hUY hx⟩ : ↥Y) ∈ U.subgroupOf Y from Subgroup.mem_subgroupOf.mpr hx)
  rw [← hy, mem_conjSub_iff] at hxQ'
  rw [mem_conjSub_iff, ← hPQ]
  exact ⟨_, hxQ', rfl⟩

theorem WeaklyClosedIn.exists_mem_mul [Finite G] {A : Subgroup G} {S : Sylow 2 G}
    (h : WeaklyClosedIn A S) (hA : IsPGroup 2 A) {H : Subgroup G} (hAH : A ≤ H) {g : G}
    (hgH : conjSub g A ≤ H) : ∃ c ∈ H, conjSub (c * g) A = A := by
  obtain ⟨P, hP, hAP⟩ := IsSylow2In.exists_ge hA hAH
  obtain ⟨c, hc, hcP⟩ := exists_conj_le_of_isSylow2In hP (isPGroup_conjSub g hA) hgH
  refine ⟨c⁻¹, H.inv_mem hc, h.eq_of_le_of_isPGroup hP.2.1 hAP ?_⟩
  rw [conjSub_mul, conjSub_le_iff, inv_inv]
  exact hcP

variable {Ω : Set (Subgroup G)}

theorem etaSet_conj (hΩ : ConjInvariant Ω) {S : Subgroup G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω S) (g : G) : conjSub g '' η ∈ etaSet Ω (conjSub g S) := by
  refine ⟨?_, inDistinctMembers_image_conj hΩ h.2.1 g, fun η' hη' hd => ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨USet.conj hΩ (h.1 hU).1 g, conjSub_mono (h.1 hU).2⟩
  · rw [Set.ncard_image_of_injective _ (conjSub_injective g)]
    exact ncard_le_of_mem_etaSet_conj hΩ rfl h hη' hd

theorem coe_smul_sylow (g : G) (S : Sylow 2 G) :
    ((g • S : Sylow 2 G) : Subgroup G) = conjSub g (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul]
  ext x
  simp [conjSub, Subgroup.pointwise_smul_def]

theorem etaG_conj (hΩ : ConjInvariant Ω) {η : Set (Subgroup G)} (h : η ∈ etaG Ω) (g : G) :
    conjSub g '' η ∈ etaG Ω := by
  obtain ⟨S, hS, hinv⟩ := h
  refine ⟨g • S, ?_, ?_⟩
  · rw [coe_smul_sylow]
    exact etaSet_conj hΩ hS g
  · rintro s hs _ ⟨U, hU, rfl⟩
    rw [coe_smul_sylow, mem_conjSub_iff] at hs
    refine ⟨conjSub (g⁻¹ * s * g) U, hinv _ hs U hU, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group

variable {p f : ℕ} [Fact p.Prime]

theorem natCard_eq_two_mul_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {U K R : Subgroup G} (hU : U ∈ USet Ω) (hK : K ∈ Ω) (hR : IsSylow2In R K) :
    Nat.card R = 2 * Nat.card U := by
  obtain ⟨R', -, J, hJ, hR'J, -, -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  rw [← hcard, hΩ.natCard_isSylow2In hK hR, hΩ.natCard_isSylow2In hJ hR'J]

theorem exists_isSylow2In [Finite G] (K : Subgroup G) : ∃ R : Subgroup G, IsSylow2In R K := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (P := K) (T := ⊥) IsPGroup.of_bot bot_le
  exact ⟨R, hR⟩

theorem isSylow2In_sup_of_ne [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K U V : Subgroup G} (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K)
    (hVK : V ≤ K) (hne : U ≠ V) (h2 : IsPGroup 2 ↥(U ⊔ V)) : IsSylow2In (U ⊔ V) K := by
  obtain ⟨R, hR⟩ := exists_isSylow2In K
  have hRU := natCard_eq_two_mul_of_mem_USet hp hΩ hU hK hR
  have hRV := natCard_eq_two_mul_of_mem_USet hp hΩ hV hK hR
  refine IsSylow2In.of_natCard_le hR h2 (sup_le hUK hVK) ?_
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ V)
  have hpos : 0 < Nat.card ↥(U ⊔ V) := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have hUe : U = U ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_left hk.le
    have hVU : V ≤ U := hUe ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hVU (by omega)).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  calc Nat.card R = 2 * Nat.card U := hRU
    _ ≤ Nat.card U * k := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk2
    _ = Nat.card ↥(U ⊔ V) := hk.symm

theorem _root_.CFSG.ClassicalInvolution.Generic.IsUniqueInvolution.mem_of_le [Finite G]
    {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (hAK : A ≤ K) (hA : IsPGroup 2 A)
    (hA2 : 2 ≤ Nat.card A) : z ∈ A := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hdvd : 2 ∣ Nat.card A := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : (x : G) * x = 1 := by
    rw [← pow_two, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  have := (hz.unique x (hAK x.2) hx2).resolve_left hx1
  rw [← this]
  exact x.2

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
