module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundComp
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hasSL2Model_of_bar
    {z : G} {K : Subgroup G} {L : Subgroup (CentralizerBar z)} {q : ℕ}
    (hKC : K ≤ Cen z) (hperf : ⁅K, K⁆ = K) (hbar : barOf z K = L)
    (hcen : ∀ (k : G) (hk : k ∈ K), toBar z ⟨k, hKC hk⟩ = 1 → ∀ k' ∈ K, k * k' = k' * k)
    (hL : HasSL2Model ↥L (fun r => r = q)) (hq5 : 5 ≤ q) (hq9 : q ≠ 9) :
    HasSL2Model ↥K (fun r => r = q) := by
  obtain ⟨F, iF, fF, hFq, ⟨eL⟩⟩ := hL
  have hFq' : Nat.card F = q := hFq
  let e' : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    eL.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hmem : ∀ k : ↥K, toBar z ⟨(k : G), hKC k.2⟩ ∈ L := by
    intro k
    rw [← hbar]
    exact ⟨⟨(k : G), hKC k.2⟩, k.2, rfl⟩
  let β : ↥K →* ↥L :=
    MonoidHom.codRestrict ((toBar z).comp (Subgroup.inclusion hKC)) L (fun k => hmem k)
  let π : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F := e'.toMonoidHom.comp β
  have hβsurj : Function.Surjective β := by
    intro l
    have hl : (l : CentralizerBar z) ∈ barOf z K := hbar ▸ l.2
    obtain ⟨y, hy, hyl⟩ := hl
    refine ⟨⟨(y : G), hy⟩, ?_⟩
    apply Subtype.ext
    exact hyl
  have hπsurj : Function.Surjective π := e'.surjective.comp hβsurj
  have hπcen : π.ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have h1 : β k = 1 := e'.injective (hk.trans (map_one e').symm)
    have h2 : toBar z ⟨(k : G), hKC k.2⟩ = 1 := congrArg Subtype.val h1
    rw [Subgroup.mem_center_iff]
    intro k'
    exact Subtype.ext (hcen (k : G) k.2 h2 (k' : G) k'.2).symm
  obtain ⟨σ, hσ⟩ := SL2Closed.sl2_exists_section_of_central (k := F) (by omega) (by omega) hπsurj hπcen
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have hker : π.ker = ⊥ := SL2Closed.ker_eq_bot_of_section π hπcen σ hσ
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  refine ⟨F, iF, fF, hFq', ⟨(MulEquiv.ofBijective π ⟨hinj, hπsurj⟩).trans
    (specialLinearGroupEquivStatedSL 2 F)⟩⟩

section Comp

variable {z : G} {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem compData_le_layer₁ (hK : CompData z K₁ K₂ L₁ L₂) : K₁ ≤ Em (Cen z) := hK.layer ▸ le_sup_left

theorem compData_le_layer₂ (hK : CompData z K₁ K₂ L₁ L₂) : K₂ ≤ Em (Cen z) := hK.layer ▸ le_sup_right

theorem compData_central_of_toBar₁ (hK : CompData z K₁ K₂ L₁ L₂) :
    ∀ (k : G) (hk : k ∈ K₁), toBar z ⟨k, hK.le₁ hk⟩ = 1 → ∀ k' ∈ K₁, k * k' = k' * k := by
  intro k hk h k' hk'
  have hmem : (⟨k, hK.le₁ hk⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]; exact h
  have hA : k ∈ OddCore z := ⟨_, hmem, rfl⟩
  exact hK.oddcomm k hA k' (compData_le_layer₁ hK hk')

theorem compData_central_of_toBar₂ (hK : CompData z K₁ K₂ L₁ L₂) :
    ∀ (k : G) (hk : k ∈ K₂), toBar z ⟨k, hK.le₂ hk⟩ = 1 → ∀ k' ∈ K₂, k * k' = k' * k := by
  intro k hk h k' hk'
  have hmem : (⟨k, hK.le₂ hk⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]; exact h
  have hA : k ∈ OddCore z := ⟨_, hmem, rfl⟩
  exact hK.oddcomm k hA k' (compData_le_layer₂ hK hk')

theorem compData_perf₂ {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂)
    (hK : CompData z K₁ K₂ L₁ L₂) : ⁅K₂, K₂⁆ = K₂ := by
  obtain ⟨s, -, hsw⟩ := hP.swap
  obtain ⟨hs, hcj⟩ := swaps_cj hsw
  obtain ⟨h1, h2⟩ := hK.swap s hs hcj
  have hle₁ : K₁.map (MulAut.conj s).toMonoidHom ≤ K₂ := by
    rintro _ ⟨a, ha, rfl⟩; exact h1 a ha
  have hle₂ : K₂.map (MulAut.conj s).toMonoidHom ≤ K₁ := by
    rintro _ ⟨a, ha, rfl⟩; exact h2 a ha
  have hc₁ : Nat.card ↥(K₁.map (MulAut.conj s).toMonoidHom) = Nat.card ↥K₁ :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hc₂ : Nat.card ↥(K₂.map (MulAut.conj s).toMonoidHom) = Nat.card ↥K₂ :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hcle₁ := Subgroup.card_le_of_le hle₁
  have hcle₂ := Subgroup.card_le_of_le hle₂
  have heq : K₁.map (MulAut.conj s).toMonoidHom = K₂ := by
    apply Subgroup.eq_of_le_of_card_ge hle₁
    omega
  conv_lhs => rw [← heq]
  rw [← Subgroup.map_commutator, hK.perf₁, heq]

theorem five_le_of_pair {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) : 5 ≤ q := by
  obtain ⟨m, hm⟩ := hP.odd
  have := hP.gt3
  omega

theorem hasSL2Model_comp₁
    {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) :
    HasSL2Model ↥K₁ (fun r => r = q) :=
  hasSL2Model_of_bar hK.le₁ hK.perf₁ hK.bar₁ (compData_central_of_toBar₁ hK) (hK.bar₁ ▸ hP.sl₁)
    (five_le_of_pair hP) hq9

theorem hasSL2Model_comp₂
    {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) :
    HasSL2Model ↥K₂ (fun r => r = q) :=
  hasSL2Model_of_bar hK.le₂ (compData_perf₂ hP hK) hK.bar₂ (compData_central_of_toBar₂ hK) (hK.bar₂ ▸ hP.sl₂)
    (five_le_of_pair hP) hq9

theorem eq_one_of_sq_odd {X : Type} [Group X] {y : X} (h2 : y * y = 1) (hodd : Odd (orderOf y)) : y = 1 := by
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite G] in
theorem sl2Equiv_of_model {K : Subgroup G} {q : ℕ} (h : HasSL2Model ↥K (fun r => r = q)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F), Nat.card F = q := by
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := h
  exact ⟨F, iF, fF, e.trans (specialLinearGroupEquivStatedSL 2 F).symm, hFq⟩

theorem compData_inj₁
    {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) :
    Function.Injective ((toBar z).comp (Subgroup.inclusion hK.le₁)) := by
  obtain ⟨F, iF, fF, e, hFq⟩ := sl2Equiv_of_model (hasSL2Model_comp₁ hP hK hq9)
  exact SL2Bound.toBar_inclusion_injective hK.le₁ e (hFq ▸ hP.odd) (hFq ▸ hP.gt3)

theorem compData_inj₂
    {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) :
    Function.Injective ((toBar z).comp (Subgroup.inclusion hK.le₂)) := by
  obtain ⟨F, iF, fF, e, hFq⟩ := sl2Equiv_of_model (hasSL2Model_comp₂ hP hK hq9)
  exact SL2Bound.toBar_inclusion_injective hK.le₂ e (hFq ▸ hP.odd) (hFq ▸ hP.gt3)

theorem compData_card_inf
    {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) :
    Nat.card ↥(K₁ ⊓ K₂) = 2 := by
  have hinj₁ := compData_inj₁ hP hK hq9
  have hinj₂ := compData_inj₂ hP hK hq9
  obtain ⟨-, -, hcard⟩ := hP.prod
  have hne : L₁ ⊓ L₂ ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxx : x * x = 1 := by
    have h1 : orderOf (⟨x, hx⟩ : ↥(L₁ ⊓ L₂)) ∣ Nat.card ↥(L₁ ⊓ L₂) := orderOf_dvd_natCard _
    rw [hcard] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
    simpa [sq] using congrArg Subtype.val h2
  have hxL₁ : x ∈ barOf z K₁ := hK.bar₁ ▸ hx.1
  have hxL₂ : x ∈ barOf z K₂ := hK.bar₂ ▸ hx.2
  obtain ⟨k₁, hk₁, hk₁x⟩ := (SL2Bound.mem_barOf_iff hK.le₁).1 hxL₁
  obtain ⟨k₂, hk₂, hk₂x⟩ := (SL2Bound.mem_barOf_iff hK.le₂).1 hxL₂
  have hk₁sq : k₁ * k₁ = 1 := by
    have := @hinj₁ (⟨k₁, hk₁⟩ * ⟨k₁, hk₁⟩) 1 (by
      simp only [MonoidHom.comp_apply, map_mul, map_one]
      show toBar z ⟨k₁, hK.le₁ hk₁⟩ * toBar z ⟨k₁, hK.le₁ hk₁⟩ = 1
      rw [hk₁x, hxx])
    simpa using congrArg Subtype.val this
  have hk₂sq : k₂ * k₂ = 1 := by
    have := @hinj₂ (⟨k₂, hk₂⟩ * ⟨k₂, hk₂⟩) 1 (by
      simp only [MonoidHom.comp_apply, map_mul, map_one]
      show toBar z ⟨k₂, hK.le₂ hk₂⟩ * toBar z ⟨k₂, hK.le₂ hk₂⟩ = 1
      rw [hk₂x, hxx])
    simpa using congrArg Subtype.val this
  have hcomm : k₁ * k₂ = k₂ * k₁ := hK.comm k₁ hk₁ k₂ hk₂
  have hAmem : (⟨k₁⁻¹ * k₂, (Cen z).mul_mem ((Cen z).inv_mem (hK.le₁ hk₁)) (hK.le₂ hk₂)⟩ : ↥(Cen z)) ∈
      pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]
    show toBar z ⟨k₁⁻¹ * k₂, _⟩ = 1
    have : (⟨k₁⁻¹ * k₂, (Cen z).mul_mem ((Cen z).inv_mem (hK.le₁ hk₁)) (hK.le₂ hk₂)⟩ : ↥(Cen z)) =
        (⟨k₁, hK.le₁ hk₁⟩ : ↥(Cen z))⁻¹ * ⟨k₂, hK.le₂ hk₂⟩ := rfl
    rw [this, map_mul, map_inv, hk₁x, hk₂x, inv_mul_cancel]
  have hodd : Odd (orderOf (k₁⁻¹ * k₂)) := by
    have := odd_orderOf_of_mem_pPrimeCore (X := ↥(Cen z)) hAmem
    rwa [Subgroup.orderOf_mk] at this
  have hsq : (k₁⁻¹ * k₂) * (k₁⁻¹ * k₂) = 1 := by
    have e1 : k₁⁻¹ * k₁⁻¹ = 1 := by
      rw [← mul_inv_rev, hk₁sq, inv_one]
    calc (k₁⁻¹ * k₂) * (k₁⁻¹ * k₂) = (k₁⁻¹ * k₁⁻¹) * (k₂ * k₂) := by
          have hc : Commute k₁⁻¹ k₂ := (show Commute k₁ k₂ from hcomm).inv_left
          calc (k₁⁻¹ * k₂) * (k₁⁻¹ * k₂) = k₁⁻¹ * (k₂ * k₁⁻¹) * k₂ := by group
            _ = k₁⁻¹ * (k₁⁻¹ * k₂) * k₂ := by rw [hc.eq]
            _ = (k₁⁻¹ * k₁⁻¹) * (k₂ * k₂) := by group
      _ = 1 := by rw [e1, hk₂sq, one_mul]
  have h1 : k₁⁻¹ * k₂ = 1 := eq_one_of_sq_odd hsq hodd
  have hkk : k₁ = k₂ := inv_mul_eq_one.1 h1
  have hkin : k₁ ∈ K₁ ⊓ K₂ := ⟨hk₁, hkk ▸ hk₂⟩
  have hk1 : k₁ ≠ 1 := by
    intro h
    apply hx1'
    rw [← hk₁x]
    have : (⟨k₁, hK.le₁ hk₁⟩ : ↥(Cen z)) = 1 := Subtype.ext h
    rw [this, map_one]
  obtain ⟨hZ, -⟩ := sl2_model_center_inv hP.odd (hasSL2Model_comp₁ hP hK hq9)
  have hle : (K₁ ⊓ K₂).subgroupOf K₁ ≤ center ↥K₁ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hK.comm g g.2 x (Subgroup.mem_subgroupOf.mp hx).2)
  have hfin : Finite ↥(center ↥K₁) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hle2 : Nat.card ↥(K₁ ⊓ K₂) ≤ 2 := by
    have h1 : Nat.card ↥((K₁ ⊓ K₂).subgroupOf K₁) = Nat.card ↥(K₁ ⊓ K₂) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K₁ ⊓ K₂ ≤ K₁)).toEquiv
    rw [← h1, ← hZ]
    exact Subgroup.card_le_of_le hle
  have hgt : 1 < Nat.card ↥(K₁ ⊓ K₂) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    have : k₁ ∈ (⊥ : Subgroup G) := h ▸ hkin
    exact hk1 (Subgroup.mem_bot.mp this)
  omega

theorem compData_isCentralProd
    {S : Subgroup G} {q : ℕ} (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9) :
    IsCentralProd K₁ K₂ (Em (Cen z)) :=
  ⟨hK.layer.symm, hK.comm, compData_card_inf hP hK hq9⟩

end Comp

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
