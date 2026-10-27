module

public import CFSG.ClassicalInvolution.Asc77.AscT7K1
public import CFSG.ClassicalInvolution.Asc77.AscT7BFuse23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T7K

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem exists_conj_xy (hs : Hyp23Setting p f Ω K K' z) {u : G} (hu : u ∈ K ⊔ K') (hu1 : u ≠ 1)
    (huz : u ≠ z) (hu2 : u * u = 1) {L L' : Subgroup G} (hL : L ∈ twinSet Ω K)
    (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G} (hR₁ : IsSylow2In R₁ L)
    (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G} (hx : x ∈ R₁) (hy : y ∈ R₂)
    (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ c ∈ K ⊔ K', c * u * c⁻¹ = x * y := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hp : p ≠ 2 := hs.stand.odd
  have hLΩ : L ∈ Ω := hL.1
  have hL'Ω : L' ∈ Ω := hL'.1
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hs.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet hs.hz hL'
  have hM : K ⊔ K' = L ⊔ L' := by
    have hLm : L ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL
    have hL'm : L' ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL'
    rcases hLm with rfl | rfl <;> rcases hL'm with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact sup_comm _ _
    · exact absurd rfl hne
  have huM : u ∈ L ⊔ L' := hM ▸ hu
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hΩ.le_normalizer_of_twin hLΩ hL'Ω hne.symm hzL hzL'
  have hLC : L ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({z} : Set G) := sup_le hLC hL'C
  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    T7A.isSylow2In_sup_of_twin hp hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2 hu1
  obtain ⟨V, hV, huV⟩ := IsSylow2In.exists_ge hu2' (Subgroup.zpowers_le.mpr huM)
  obtain ⟨m, hmM, hmV⟩ := exists_conjSub_eq_of_isSylow2In hV hQ
  have hu'mem : m * u * m⁻¹ ∈ R₁ ⊔ R₂ := by
    rw [← hmV]
    exact conj_mem_conjSub (huV (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc hu'mem
  have hmz : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * z * m⁻¹ = (z * m) * m⁻¹ := by rw [this]
      _ = z := by group
  have hu'2 : (a * b) * (a * b) = 1 := by
    rw [hab]
    calc m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu'2
  have haL : a ∈ L := hR₁.1 ha
  have hbL' : b ∈ L' := hR₂.1 hb
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hLΩ hL'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hzL.unique (a * a) (L.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hzL.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzL'.unique b hbL' hbb
      have hu'z : m * u * m⁻¹ = 1 ∨ m * u * m⁻¹ = z := by
        rw [← hab]
        rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
        · left; rw [h1, h2, one_mul]
        · right; rw [h1, h2, one_mul]
        · right; rw [h1, h2, mul_one]
        · left; rw [h1, h2]; exact hzL.sq
      have hu : u = m⁻¹ * (m * u * m⁻¹) * m := by group
      rcases hu'z with h' | h'
      · exact hu1 (by rw [hu, h']; group)
      · exact huz (by
          rw [hu, h']
          calc m⁻¹ * z * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
            _ = z := by group)
    · exact h
  have hbb : b * b = z := by
    have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hzL.sq
  have hx2 : x * x = z := T7B.mul_self_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hy2 : y * y = z := T7B.mul_self_eq_of_orderOf_four hzL' (hR₂.1 hy) oy
  obtain ⟨k, hkL, hk⟩ := T7B.exists_conj_of_sq_eq hp hΩ hLΩ hzL haL (hR₁.1 hx) haa hx2
  set b₁ := k * b * k⁻¹ with hb₁
  have hb₁L' : b₁ ∈ L' := (Subgroup.mem_normalizer_iff.mp (hLN hkL) b).mp hbL'
  have hb₁2 : b₁ * b₁ = z := by
    have e : b₁ * b₁ = k * (b * b) * k⁻¹ := by rw [hb₁]; group
    rw [e, hbb]
    have := hzL.commute_of_mem hkL
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [this]
      _ = z := by group
  have hxb₁ : x * b₁ = b₁ * x := by
    rw [← hk, hb₁]
    calc k * a * k⁻¹ * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
      _ = k * (b * a) * k⁻¹ := by rw [hcab]
      _ = k * b * k⁻¹ * (k * a * k⁻¹) := by group
  have hxy : x * y = y * x := hc x hx y hy
  obtain ⟨ℓ, hℓL', hℓ⟩ := T7B.exists_conj_of_sq_eq hp hΩ hL'Ω hzL' hb₁L' (hR₂.1 hy) hb₁2 hy2
  obtain ⟨ℓ', hℓ'L', hℓ'b, hℓ'x⟩ := T7B.exists_centralizing_conj hΩ hLΩ hL'Ω hne hzL hzL'
    (hR₁.1 hx) (T7B.isPGroup_zpowers_of_orderOf_four ox) hℓL' hxb₁ hxy hℓ
  have hLM : L ≤ K ⊔ K' := hM ▸ le_sup_left
  have hL'M : L' ≤ K ⊔ K' := hM ▸ le_sup_right
  refine ⟨ℓ' * k * m, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL'M hℓ'L') (hLM hkL))
    (hM ▸ hmM), ?_⟩
  have hℓ'x' : ℓ' * x * ℓ'⁻¹ = x := by
    rw [hℓ'x]
    group
  calc ℓ' * k * m * u * (ℓ' * k * m)⁻¹ = ℓ' * k * (m * u * m⁻¹) * k⁻¹ * ℓ'⁻¹ := by group
    _ = ℓ' * k * (a * b) * k⁻¹ * ℓ'⁻¹ := by rw [hab]
    _ = ℓ' * ((k * a * k⁻¹) * (k * b * k⁻¹)) * ℓ'⁻¹ := by group
    _ = ℓ' * (x * b₁) * ℓ'⁻¹ := by rw [hk]
    _ = (ℓ' * x * ℓ'⁻¹) * (ℓ' * b₁ * ℓ'⁻¹) := by group
    _ = x * y := by rw [hℓ'x', hℓ'b]

theorem exists_conj_of_involution (hs : Hyp23Setting p f Ω K K' z) {u₁ u₂ : G}
    (h₁ : u₁ ∈ K ⊔ K') (h₁1 : u₁ ≠ 1) (h₁z : u₁ ≠ z) (h₁2 : u₁ * u₁ = 1)
    (h₂ : u₂ ∈ K ⊔ K') (h₂1 : u₂ ≠ 1) (h₂z : u₂ ≠ z) (h₂2 : u₂ * u₂ = 1) :
    ∃ c ∈ K ⊔ K', c * u₁ * c⁻¹ = u₂ := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', hR, hR', hc, hu⟩ :=
    T7A.exists_sylow_pair_of_mem hp hΩ hK hK'Ω hs.hne hs.hz hzK' h₁ h₁2 h₁1
  obtain ⟨x, hx, ox⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨y, hy, oy⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp
    (mem_RSet_of_isSylow2In hK'Ω hR')
  have hKt : K ∈ twinSet Ω K := mem_twinSet_self hK hs.hz
  obtain ⟨c₁, hc₁, e₁⟩ := exists_conj_xy hs h₁ h₁1 h₁z h₁2 hKt hs.hK' hs.hne hR hR' hc hx hy ox oy
  obtain ⟨c₂, hc₂, e₂⟩ := exists_conj_xy hs h₂ h₂1 h₂z h₂2 hKt hs.hK' hs.hne hR hR' hc hx hy ox oy
  refine ⟨c₂⁻¹ * c₁, (K ⊔ K').mul_mem ((K ⊔ K').inv_mem hc₂) hc₁, ?_⟩
  calc c₂⁻¹ * c₁ * u₁ * (c₂⁻¹ * c₁)⁻¹ = c₂⁻¹ * (c₁ * u₁ * c₁⁻¹) * c₂ := by group
    _ = c₂⁻¹ * (c₂ * u₂ * c₂⁻¹) * c₂ := by rw [e₁, e₂]
    _ = u₂ := by group

theorem conj_mem_sup (hs : Hyp23Setting p f Ω K K' z) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G} (hx : x ∈ K ⊔ K') :
    c * x * c⁻¹ ∈ K ⊔ K' := by
  have hst := hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have htw : ∀ {L : Subgroup G}, L ∈ twinSet Ω K → conjSub c L ∈ ({K, K'} : Set (Subgroup G)) := by
    intro L hL
    have hzL := isUniqueInvolution_of_mem_twinSet hs.hz hL
    have h1 : conjSub c L ∈ twinSet Ω K := by
      refine ⟨hΩ.conjInvariant c L hL.1, z, hs.hz, ?_⟩
      have := hzL.conj c
      rwa [hcz] at this
    rwa [hs.twinSet_eq] at h1
  have hKK : conjSub c K ∈ ({K, K'} : Set (Subgroup G)) := htw (mem_twinSet_self hst.mem hs.hz)
  have hK'K : conjSub c K' ∈ ({K, K'} : Set (Subgroup G)) := htw hs.hK'
  have hne : conjSub c K ≠ conjSub c K' := fun h => hs.hne.symm (by
    have := congrArg (conjSub c⁻¹) h
    simpa [conjSub_inv_conjSub] using this)
  have hsup : conjSub c (K ⊔ K') = K ⊔ K' := by
    rw [T7A.conjSub_sup_eq]
    rcases hKK with h | h <;> rcases hK'K with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · rw [h, h']
    · rw [h, h', sup_comm]
    · exact absurd (h.trans h'.symm) hne
  rw [← hsup]
  exact conj_mem_conjSub hx

theorem centralizer_eq_sup_mul (hs : Hyp23Setting p f Ω K K' z) {u : G} (hu : u ∈ K ⊔ K')
    (hu1 : u ≠ 1) (huz : u ≠ z) (hu2 : u * u = 1) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ q ∈ K ⊔ K', ∃ c₀ ∈ Subgroup.centralizer ({z} : Set G),
      c₀ * u = u * c₀ ∧ c = q * c₀ := by
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hu' : c * u * c⁻¹ ∈ K ⊔ K' := conj_mem_sup hs hc hu
  have hu'1 : c * u * c⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have := congrArg (fun t => c⁻¹ * t * c) h
    simpa [mul_assoc] using this
  have hu'z : c * u * c⁻¹ ≠ z := by
    intro h
    apply huz
    have := congrArg (fun t => c⁻¹ * t * c) h
    have e1 : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
        _ = z := by group
    simpa [mul_assoc, e1] using this
  have hu'2 : (c * u * c⁻¹) * (c * u * c⁻¹) = 1 := by
    calc (c * u * c⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨q, hq, hqu⟩ := exists_conj_of_involution hs hu hu1 huz hu2 hu' hu'1 hu'z hu'2
  have hqz : q ∈ Subgroup.centralizer ({z} : Set G) := sup_le_centralizer hs hq
  refine ⟨q, hq, q⁻¹ * c, ?_, ?_, by group⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hqz) hc
  ·
    calc q⁻¹ * c * u = q⁻¹ * (c * u * c⁻¹) * c := by group
      _ = q⁻¹ * (q * u * q⁻¹) * c := by rw [← hqu]
      _ = u * (q⁻¹ * c) := by group

end T7K
