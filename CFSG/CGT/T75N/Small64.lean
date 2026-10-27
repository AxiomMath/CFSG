module

public import CFSG.CGT.Timmesfeld75.Sec5Eleven
public import CFSG.CGT.T75N.BinIndex

public section

namespace CFSG.CGT.T75N

open CFSG.Open CFSG.Timmesfeld CFSG.Assembly.LowTwoRank

theorem index_stab_eq {Y V : Type} [Group Y] [Group V] [Finite V] (ρ : Y →* MulAut V) (v₀ : V)
    (hv₀ : v₀ ≠ 1) (htr : ∀ w : V, w ≠ 1 → ∃ y : Y, ρ y v₀ = w) :
    ∃ H : Subgroup Y, (∀ y, y ∈ H ↔ ρ y v₀ = v₀) ∧ H.index = Nat.card V - 1 := by
  let _ : MulAction Y V := MulAction.compHom V ρ
  refine ⟨MulAction.stabilizer Y v₀, fun y => Iff.rfl, ?_⟩
  rw [MulAction.index_stabilizer]
  have h : MulAction.orbit Y v₀ = ({1} : Set V)ᶜ := by
    ext w
    simp only [MulAction.mem_orbit_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl⟩ h1
      exact hv₀ ((ρ y).injective (h1.trans (map_one _).symm))
    · intro hw
      exact htr w hw
  rw [h, Set.ncard_compl, Set.ncard_singleton]

theorem center_eq_top_of_stab_sup {Y V : Type} [Group Y] [Group V] (ρ : Y →* MulAut V)
    (hker : ρ.ker ≤ Subgroup.center Y) (v₀ : V) (hv₀ : v₀ ≠ 1) (H : Subgroup Y)
    (hH : ∀ y, y ∈ H ↔ ρ y v₀ = v₀) (htr : ∀ w : V, w ≠ 1 → ∃ y : Y, ρ y v₀ = w)
    (hsup : H ⊔ Subgroup.center Y = ⊤) : Subgroup.center Y = ⊤ := by
  have hcomm : ∀ (y z : Y), z ∈ Subgroup.center Y → ∀ v : V, ρ y (ρ z v) = ρ z (ρ y v) := by
    intro y z hz v
    have h : y * z = z * y := Subgroup.mem_center_iff.1 hz y
    calc ρ y (ρ z v) = ρ (y * z) v := by rw [map_mul]; rfl
      _ = ρ (z * y) v := by rw [h]
      _ = ρ z (ρ y v) := by rw [map_mul]; rfl
  have hZ : ∀ w : V, w ≠ 1 → ∃ z ∈ Subgroup.center Y, ρ z v₀ = w := by
    intro w hw
    obtain ⟨y, rfl⟩ := htr w hw
    have hy : y ∈ H ⊔ Subgroup.center Y := hsup ▸ Subgroup.mem_top y
    obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
    refine ⟨z, hz, ?_⟩
    rw [map_mul]
    show ρ z v₀ = ρ h (ρ z v₀)
    rw [hcomm h z hz, (hH h).1 hh]
  rw [eq_top_iff]
  intro y _
  have hne : ρ y v₀ ≠ 1 := fun h =>
    hv₀ ((ρ y).injective (h.trans (map_one _).symm))
  obtain ⟨z₀, hz₀, hzy⟩ := hZ _ hne
  have hρ : ρ y = ρ z₀ := by
    ext w
    by_cases hw : w = 1
    · rw [hw, map_one, map_one]
    · obtain ⟨z, hz, rfl⟩ := hZ w hw
      rw [hcomm y z hz, ← hzy, hcomm z z₀ hz₀]
  have h1 : z₀⁻¹ * y ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel]
  have h2 : y = z₀ * (z₀⁻¹ * y) := by group
  rw [h2]
  exact Subgroup.mul_mem _ hz₀ (hker h1)

theorem small64Input : CFSG.CGT.Timmesfeld75.Small64Input := by
  intro a ha Y _ _ hY V _ _ hVc hVsq hV ρ hker htr
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by rw [hV]; norm_num)
  obtain ⟨v₀, hv₀⟩ := exists_ne (1 : V)
  have htr' : ∀ w : V, w ≠ 1 → ∃ y : Y, ρ y v₀ = w := fun w hw => htr v₀ w hv₀ hw
  obtain ⟨H, hH, hHidx⟩ := index_stab_eq ρ v₀ hv₀ htr'
  let ε : Y →* StatedProj (StatedSL a F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hε : Function.Surjective ε := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hεker : ε.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let π : Matrix.SpecialLinearGroup (Fin a) F →* StatedProj (StatedSL a F) :=
    (QuotientGroup.mk' _).comp (specialLinearGroupEquivStatedSL a F).toMonoidHom
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (specialLinearGroupEquivStatedSL a F).surjective
  let K : Subgroup Y := H ⊔ Subgroup.center Y
  have hKidx : K.index ∣ 63 := by
    refine (Subgroup.index_dvd_of_le (le_sup_left : H ≤ K)).trans ?_
    rw [hHidx, hV]
    norm_num
  have hS₁idx : ((K.map ε).comap π).index = K.index := by
    rw [Subgroup.index_comap_of_surjective _ hπ,
      Subgroup.index_map_eq _ hε (hεker ▸ le_sup_right)]
  have hS₁top : (K.map ε).comap π = ⊤ :=
    eq_top_of_index_dvd_sixtythree hF ha _ (hS₁idx ▸ hKidx)
  have hK1 : K.index = 1 := by rw [← hS₁idx, hS₁top, Subgroup.index_top]
  have hKtop : K = ⊤ := Subgroup.index_eq_one.1 hK1
  have hcenter := center_eq_top_of_stab_sup ρ hker v₀ hv₀ H hH htr' hKtop
  have hcard1 : Nat.card (StatedProj (StatedSL a F)) = 1 := by
    rw [← Nat.card_congr e.toEquiv]
    change (Subgroup.center Y).index = 1
    rw [hcenter, Subgroup.index_top]
  rw [ClassicalOrders.card_statedProj_statedSL (by omega), hF] at hcard1
  rcases ha with rfl | rfl <;> revert hcard1 <;> decide

end CFSG.CGT.T75N
