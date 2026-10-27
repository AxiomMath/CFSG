module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Si

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

namespace Model

variable {P H : Type*} [Group P] [Group H] {ι : P} {J : Subgroup P} {m : ℕ}

theorem map_mem_cent {ψ : P →* H} {x : P} (hx : x ∈ centralizer (J : Set P)) :
    ψ x ∈ centralizer ((J.map ψ : Subgroup H) : Set H) := by
  rw [mem_centralizer_iff] at hx ⊢
  rintro _ ⟨j, hj, rfl⟩
  rw [← map_mul, ← map_mul, hx j hj]

theorem mem_cent_of_map {ψ : P →* H} (hψ : Function.Injective ψ) {x : P}
    (hx : ψ x ∈ centralizer ((J.map ψ : Subgroup H) : Set H)) :
    x ∈ centralizer (J : Set P) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro j hj
  apply hψ
  rw [map_mul, map_mul]
  exact hx (ψ j) ⟨j, hj, rfl⟩

@[expose] noncomputable def map (M : Model ⊤ ι J m) (ψ : P →* H) (hψ : Function.Injective ψ)
    {L' : Subgroup H} {ι' : H} {J' : Subgroup H} (hL : ψ.range = L') (hι : ψ ι = ι')
    (hJ : J.map ψ = J') [Finite P] : Model L' ι' J' m where
  ρ := ψ.comp M.ρ
  t₀ := ψ M.t₀
  two_le := M.two_le
  inj := hψ.comp M.inj
  le_J x := hJ ▸ mem_map_of_mem ψ (M.le_J x)
  J_le_L := by
    rw [← hJ, ← hL]
    exact map_le_range ψ J
  t₀_mem := hL ▸ ⟨M.t₀, rfl⟩
  J_le := by
    rw [← hJ, ← hι]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (M.J_le hy)]
  normJ c hc x := by
    rw [← hι, ← hL] at hc
    rw [← hJ]
    obtain ⟨hc1, ⟨c', rfl⟩⟩ := hc
    have hc' : c' ∈ centralizer ({ι} : Set P) ⊓ ⊤ := by
      refine ⟨mem_centralizer_singleton_iff.mpr (hψ ?_), mem_top _⟩
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hc1
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c' * y * c'⁻¹, (M.normJ c' hc' y).mp hy, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨z, hz, hze⟩
      refine ⟨c'⁻¹ * z * c', ?_, ?_⟩
      · have := (M.normJ c'⁻¹ (inv_mem hc') z).mp hz
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hze]
        group
  inf_cent := by
    rw [← hJ, eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hc⟩
    have hy' : y ∈ J ⊓ centralizer (J : Set P) := ⟨hy, mem_cent_of_map hψ hc⟩
    rw [M.inf_cent, mem_bot] at hy'
    rw [hy', map_one]
    exact one_mem _
  comm x y := by
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg ψ (M.comm x y)
  gamma := by
    rw [← hJ]
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact map_mem_cent M.gamma
  sr_not := by
    rw [← hJ]
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    intro h
    apply M.sr_not
    set y := M.t₀⁻¹ * M.ρ (sr 0) * M.t₀
    have hN : centralizer ((J.map ψ : Subgroup H) : Set H) ≤ normalizer
        ((J.map ψ : Subgroup H) : Set H) := centralizer_le_normalizer _
    have hset := coe_mul_of_left_le_normalizer_right _ _ hN
    rw [sup_comm] at h
    have h' : ψ y ∈ ((centralizer ((J.map ψ : Subgroup H) : Set H) ⊔ J.map ψ : Subgroup H) :
        Set H) := h
    rw [hset] at h'
    obtain ⟨b, hb, a, ⟨a', ha', rfl⟩, hba⟩ := h'
    have hb' : b = ψ (y * a'⁻¹) := by rw [map_mul, map_inv, ← hba]; group
    rw [hb'] at hb
    have hyc := mem_cent_of_map hψ hb
    have : y = (y * a'⁻¹) * a' := by group
    rw [this, sup_comm]
    exact mul_mem (mem_sup_left hyc) (mem_sup_right ha')
  iota := by
    rw [← hι]
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, ← M.iota]
  sq := by
    rw [← hι]
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, M.sq]
  not_conj g hg := by
    rw [← hL] at hg
    obtain ⟨g', rfl⟩ := hg
    rw [← hι]
    simp only [MonoidHom.comp_apply]
    intro h
    apply M.not_conj g' (mem_top _)
    apply hψ
    rw [map_mul, map_mul, map_inv, map_mul]
    exact h
  dvd_L := by
    rw [← hL, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    have := M.dvd_L
    rwa [Subgroup.card_top] at this
  not_dvd_L := by
    rw [← hL, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    have := M.not_dvd_L
    rwa [Subgroup.card_top] at this
  not_dvd_J := by
    rw [← hJ, Subgroup.card_map_of_injective hψ]
    exact M.not_dvd_J

end Model

theorem prop29ConclCorr_of_map {H P : Type} [Group H] [Finite H] [Group P] [Finite P]
    [(generalizedFitting H).Normal] {ι₀ : P} {J : Subgroup P} {m : ℕ} (M : Model ⊤ ι₀ J m)
    (ψ : P →* H) (hψ : Function.Injective ψ) (hL : ψ.range = generalizedFitting H)
    {ι : H} (hι : ψ ι₀ = ι) {J₁ : Subgroup H} (hJ : J.map ψ = J₁) (hO : pPrimeCore 2 ↥J₁ = ⊥)
    {S₁ : Subgroup H} (hS : Seven.IsSylowIn S₁ (centralizer ({ι} : Set H))) :
    Prop29ConclCorr H ι J₁ S₁ :=
  prop29ConclCorr_of_model (M.map ψ hψ hL hι hJ) hO hS

end CFSG.ComponentClassification.GSThmB.P29
