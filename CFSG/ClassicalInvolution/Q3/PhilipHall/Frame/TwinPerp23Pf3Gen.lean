module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7F0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame



section General

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_ab (hΩ : HypOmegaGen Ω) {L L' : Subgroup G} {t : G} (hLΩ : L ∈ Ω) (hL'Ω : L' ∈ Ω)
    (hne : L' ≠ L) (hzL : IsUniqueInvolution L t) (hzL' : IsUniqueInvolution L' t) {u : G}
    (huM : u ∈ L ⊔ L') (hu1 : u ≠ 1) (huz : u ≠ t) (hu2 : u * u = 1) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) :
    ∃ m ∈ L ⊔ L', ∃ a ∈ R₁, ∃ b ∈ R₂, a * a = t ∧ b * b = t ∧ m * u * m⁻¹ = a * b := by
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hLΩ hL'Ω hne.symm hzL hzL'
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({t} : Set G) := sup_le hLC hL'C

  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2 hu1
  obtain ⟨V, hV, huV⟩ := IsSylow2In.exists_ge hu2' (Subgroup.zpowers_le.mpr huM)
  obtain ⟨m, hmM, hmV⟩ := exists_conjSub_eq_of_isSylow2In hV hQ
  have hu'mem : m * u * m⁻¹ ∈ R₁ ⊔ R₂ := by
    rw [← hmV]
    exact conj_mem_conjSub (huV (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc hu'mem
  have hmz : m * t * m⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * t * m⁻¹ = (t * m) * m⁻¹ := by rw [this]
      _ = t := by group
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
    Sec6Gen.card_le_two_of_le_inf hΩ hLΩ hL'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
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
  have haa : a * a = t := by
    rcases hzL.unique (a * a) (L.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = t := hzL.unique a haL h
      have hb1 : b = 1 ∨ b = t := hzL'.unique b hbL' hbb
      have hu'z : m * u * m⁻¹ = 1 ∨ m * u * m⁻¹ = t := by
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
          calc m⁻¹ * t * m = m⁻¹ * (m * t * m⁻¹) * m := by rw [hmz]
            _ = t := by group)
    · exact h
  have hbb : b * b = t := by
    have h1 : b * b = t⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hzL.sq
  exact ⟨m, hmM, a, ha, b, hb, haa, hbb, hab.symm⟩

theorem fuse_general (hΩ : HypOmegaGen Ω) {L L' : Subgroup G} {t : G} (hLΩ : L ∈ Ω)
    (hL'Ω : L' ∈ Ω) (hne : L' ≠ L) (hzL : IsUniqueInvolution L t) (hzL' : IsUniqueInvolution L' t)
    {A A' : Subgroup G} (hA : IsSylow2In A L) (hA' : IsSylow2In A' L') (hAc : Commutes A A')
    (hstd : ∀ a ∈ A, ∀ x ∈ A, ∀ b ∈ A', ∀ y ∈ A', a * a = t → x * x = t → b * b = t →
      y * y = t → ∃ g ∈ Subgroup.centralizer ({t} : Set G), g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y)
    {u : G} (huM : u ∈ L ⊔ L') (hu1 : u ≠ 1) (huz : u ≠ t) (hu2 : u * u = 1)
    {R₁ R₂ : Subgroup G} (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂)
    {x y : G} (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * u * c⁻¹ = x * y := by
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hLΩ hL'Ω hne.symm hzL hzL'
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL'Ω hLΩ hne hzL' hzL
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({t} : Set G) := sup_le hLC hL'C
  have hMNL : L ⊔ L' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hL'N
  have hMNL' : L ⊔ L' ≤ Subgroup.normalizer (L' : Set G) := sup_le hLN Subgroup.le_normalizer
  obtain ⟨m₂, hm₂M, a, ha, b, hb, haa, hbb, hab⟩ :=
    exists_ab hΩ hLΩ hL'Ω hne hzL hzL' huM hu1 huz hu2 hR₁ hR₂ hc
  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hQs : IsSylow2In (A ⊔ A') (L ⊔ L') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hA hA' hAc
  obtain ⟨m₁, hm₁M, hm₁⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In hQs hQ
  have hz1 : m₁ * t * m₁⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hm₁M)
    calc m₁ * t * m₁⁻¹ = (t * m₁) * m₁⁻¹ := by rw [this]
      _ = t := by group
  have hm₁L : conjSub m₁ L = L := mem_normalizer_iff_conjSub_eq.mp (hMNL hm₁M)
  have hm₁L' : conjSub m₁ L' = L' := mem_normalizer_iff_conjSub_eq.mp (hMNL' hm₁M)
  have hQ2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hQ.2.1
  have hAeq : conjSub m₁ A = R₁ := by
    have h1 : conjSub m₁ A ≤ (R₁ ⊔ R₂) ⊓ L := by
      refine le_inf ?_ ?_
      · rw [← hm₁]; exact conjSub_mono le_sup_left
      · have := conjSub_mono (n := m₁) hA.1
        rwa [hm₁L] at this
    have h2 : (R₁ ⊔ R₂) ⊓ L = R₁ :=
      hR₁.2.2 _ inf_le_right (hQ2.to_le inf_le_left) (le_inf le_sup_left hR₁.1)
    rw [h2] at h1
    have hs : IsSylow2In (conjSub m₁ A) L := by
      have := hA.conj m₁
      rwa [hm₁L] at this
    exact (hs.eq_of_le hR₁.2.1 hR₁.1 h1).symm
  have hA'eq : conjSub m₁ A' = R₂ := by
    have h1 : conjSub m₁ A' ≤ (R₁ ⊔ R₂) ⊓ L' := by
      refine le_inf ?_ ?_
      · rw [← hm₁]; exact conjSub_mono le_sup_right
      · have := conjSub_mono (n := m₁) hA'.1
        rwa [hm₁L'] at this
    have h2 : (R₁ ⊔ R₂) ⊓ L' = R₂ :=
      hR₂.2.2 _ inf_le_right (hQ2.to_le inf_le_left) (le_inf le_sup_right hR₂.1)
    rw [h2] at h1
    have hs : IsSylow2In (conjSub m₁ A') L' := by
      have := hA'.conj m₁
      rwa [hm₁L'] at this
    exact (hs.eq_of_le hR₂.2.1 hR₂.1 h1).symm
  have hmem : ∀ {w : G} {B₀ B₁ : Subgroup G}, conjSub m₁ B₀ = B₁ → w ∈ B₁ → m₁⁻¹ * w * m₁ ∈ B₀ := by
    intro w B₀ B₁ h hw
    rw [← h] at hw
    exact mem_conjSub_iff.mp hw
  have hxx : x * x = t := TwinPerp.sq_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hyy : y * y = t := TwinPerp.sq_eq_of_orderOf_four hzL' (hR₂.1 hy) oy
  have hsq : ∀ {w : G}, w * w = t → (m₁⁻¹ * w * m₁) * (m₁⁻¹ * w * m₁) = t := by
    intro w hw
    calc (m₁⁻¹ * w * m₁) * (m₁⁻¹ * w * m₁) = m₁⁻¹ * (w * w) * m₁ := by group
      _ = m₁⁻¹ * t * m₁ := by rw [hw]
      _ = t := by
        calc m₁⁻¹ * t * m₁ = m₁⁻¹ * (m₁ * t * m₁⁻¹) * m₁ := by rw [hz1]
          _ = t := by group
  obtain ⟨c₀, hc₀t, hc₀a, hc₀b⟩ := hstd _ (hmem hAeq ha) _ (hmem hAeq hx) _ (hmem hA'eq hb) _
    (hmem hA'eq hy) (hsq haa) (hsq hxx) (hsq hbb) (hsq hyy)
  have hc₀t' : c₀ * t = t * c₀ := Subgroup.mem_centralizer_singleton_iff.mp hc₀t
  set c₁ := m₁ * c₀ * m₁⁻¹ with hc₁
  have hc₁t : c₁ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm₁t : m₁ * t = t * m₁ := Subgroup.mem_centralizer_singleton_iff.mp (hMC hm₁M)
    calc c₁ * t = m₁ * c₀ * m₁⁻¹ * t := rfl
      _ = m₁ * c₀ * (m₁⁻¹ * t) := by group
      _ = m₁ * c₀ * (t * m₁⁻¹) := by
          rw [show m₁⁻¹ * t = t * m₁⁻¹ by
            calc m₁⁻¹ * t = m₁⁻¹ * (t * m₁) * m₁⁻¹ := by group
              _ = m₁⁻¹ * (m₁ * t) * m₁⁻¹ := by rw [hm₁t]
              _ = t * m₁⁻¹ := by group]
      _ = m₁ * (c₀ * t) * m₁⁻¹ := by group
      _ = m₁ * (t * c₀) * m₁⁻¹ := by rw [hc₀t']
      _ = (m₁ * t) * c₀ * m₁⁻¹ := by group
      _ = (t * m₁) * c₀ * m₁⁻¹ := by rw [hm₁t]
      _ = t * c₁ := by rw [hc₁]; group
  have hm₂t : m₂ * t = t * m₂ := Subgroup.mem_centralizer_singleton_iff.mp (hMC hm₂M)
  refine ⟨c₁ * m₂, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c₁ * t = t * c₁ := Subgroup.mem_centralizer_singleton_iff.mp hc₁t
    calc c₁ * m₂ * t = c₁ * (m₂ * t) := by group
      _ = c₁ * (t * m₂) := by rw [hm₂t]
      _ = (c₁ * t) * m₂ := by group
      _ = (t * c₁) * m₂ := by rw [h1]
      _ = t * (c₁ * m₂) := by group
  · have hca : c₁ * a * c₁⁻¹ = x := by
      calc c₁ * a * c₁⁻¹ = m₁ * (c₀ * (m₁⁻¹ * a * m₁) * c₀⁻¹) * m₁⁻¹ := by rw [hc₁]; group
        _ = m₁ * (m₁⁻¹ * x * m₁) * m₁⁻¹ := by rw [hc₀a]
        _ = x := by group
    have hcb : c₁ * b * c₁⁻¹ = y := by
      calc c₁ * b * c₁⁻¹ = m₁ * (c₀ * (m₁⁻¹ * b * m₁) * c₀⁻¹) * m₁⁻¹ := by rw [hc₁]; group
        _ = m₁ * (m₁⁻¹ * y * m₁) * m₁⁻¹ := by rw [hc₀b]
        _ = y := by group
    calc c₁ * m₂ * u * (c₁ * m₂)⁻¹ = c₁ * (m₂ * u * m₂⁻¹) * c₁⁻¹ := by group
      _ = c₁ * (a * b) * c₁⁻¹ := by rw [hab]
      _ = (c₁ * a * c₁⁻¹) * (c₁ * b * c₁⁻¹) := by group
      _ = x * y := by rw [hca, hcb]

end General

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
