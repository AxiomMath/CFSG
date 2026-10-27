module

public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.CentralExt CFSG.SectionRank.EvenCover CFSG.LieType.Steinberg

theorem exists_factor {A B D : Type*} [Group A] [Group B] [Group D] (f : A →* B)
    (hf : Function.Surjective f) (g : A →* D) (hg : f.ker ≤ g.ker) :
    ∃ φ : B →* D, ∀ a, φ (f a) = g a :=
  ⟨f.liftOfSurjective hf ⟨g, hg⟩, fun a => f.liftOfRightInverse_comp_apply _ _ ⟨g, hg⟩ a⟩

@[expose] def HasCentralPSplit (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (π : E →* K), Function.Surjective π →
    π.ker ≤ Subgroup.center E → ¬ p ∣ Nat.card π.ker →
    ∃! s : K →* E, ∀ x, π (s x) = x

theorem HasCentralPSplit.existsUnique_lift {p : ℕ} {K : Type} [Group K] [Finite K]
    (h : HasCentralPSplit p K) {E G : Type} [Group E] [Finite E] [Group G] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ p ∣ Nat.card π.ker)
    (α : K →* G) : ∃! α' : K →* E, π.comp α' = α := by
  obtain ⟨σ, hσ, huniq⟩ := h (pullback π α) (pullbackFst π α) (pullbackFst_surjective hπ α)
    (pullbackFst_ker_le_center hcen α) (fun h => hC (h.trans (card_pullbackFst_ker_dvd π α)))
  refine ⟨_, comp_snd_section σ hσ, fun τ hτ => ?_⟩
  let τ' : K →* pullback π α :=
    { toFun := fun g => ⟨(g, τ g), by
        change α g = π (τ g)
        rw [← hτ, MonoidHom.comp_apply]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have h1 := huniq τ' fun g => rfl
  ext g
  exact congrArg (fun f : K →* pullback π α => ((f g : pullback π α) : K × E).2) h1

section Transport

variable {p : ℕ} {K X C : Type} [Group K] [Group X] [Group C]

theorem ker_factor_eq_center (θ : K →* X) (hθ : Function.Surjective θ) (π : K →* C)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center K)
    (hZC : Subgroup.center C = ⊥) (π' : X →* C) (hπ' : ∀ k, π' (θ k) = π k) :
    π'.ker = Subgroup.center X := by
  have hπ's : Function.Surjective π' := fun c => by
    obtain ⟨k, rfl⟩ := hπ c
    exact ⟨θ k, hπ' k⟩
  ext x
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := hθ x
    have hk : k ∈ π.ker := by rw [MonoidHom.mem_ker, ← hπ']; exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := hθ y
    have := Subgroup.mem_center_iff.1 (hcen hk) k'
    rw [← map_mul, ← map_mul, this]
  · intro hx
    have hc : π' x ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨y, rfl⟩ := hπ's c
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    rw [hZC, Subgroup.mem_bot] at hc
    exact hc

theorem not_dvd_card_ker_factor (θ : K →* X) (hθ : Function.Surjective θ) (π : K →* C)
    (π' : X →* C) (hπ' : ∀ k, π' (θ k) = π k) (hC : ¬ p ∣ Nat.card π.ker) :
    ¬ p ∣ Nat.card π'.ker := by
  have hmap : π.ker.map θ = π'.ker := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [MonoidHom.mem_ker, hπ']
      exact hk
    · intro hy
      obtain ⟨k, rfl⟩ := hθ y
      refine ⟨k, ?_, rfl⟩
      rw [MonoidHom.mem_ker] at hy
      show k ∈ π.ker
      rw [MonoidHom.mem_ker, ← hπ']
      exact hy
  intro hdvd
  apply hC
  refine hdvd.trans ?_
  rw [← hmap]
  exact Subgroup.card_dvd_of_surjective (f := θ.subgroupMap π.ker)
    (MonoidHom.subgroupMap_surjective θ π.ker)

theorem exists_mulEquiv_lift_of_centralQuotient [Fact p.Prime]
    (θ : K →* X) (hθ : Function.Surjective θ) (π : K →* C) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center K) (hC : ¬ p ∣ Nat.card π.ker)
    (hlift : ∀ ψ : K →* C, ∃! α : K →* K, π.comp α = ψ)
    (hZC : Subgroup.center C = ⊥) (hker : θ.ker ≤ π.ker)
    (hgen : Subgroup.closure {x : K | ∃ n : ℕ, orderOf x = p ^ n} = ⊤) (σ : X ≃* X) :
    ∃ (α : K ≃* K) (σ' : C ≃* C), (∀ x, θ (α x) = σ (θ x)) ∧ ∀ x, π (α x) = σ' (π x) := by
  obtain ⟨π', hπ'⟩ := exists_factor θ hθ π hker
  have hπ's : Function.Surjective π' := fun c => by
    obtain ⟨k, rfl⟩ := hπ c
    exact ⟨θ k, hπ' k⟩
  have hkerπ' := ker_factor_eq_center θ hθ π hπ hcen hZC π' hπ'
  have hCπ' := not_dvd_card_ker_factor θ hθ π π' hπ' hC
  have hcenπ' : π'.ker ≤ Subgroup.center X := hkerπ'.le
  have hσc : ∀ (τ : X ≃* X), π'.ker ≤ (π'.comp τ.toMonoidHom).ker := by
    intro τ x hx
    rw [hkerπ'] at hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : τ x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := τ.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
    have h2 : τ x ∈ π'.ker := by rw [hkerπ']; exact this
    exact h2
  obtain ⟨σ₁, hσ₁⟩ := exists_factor π' hπ's (π'.comp σ.toMonoidHom) (hσc σ)
  obtain ⟨σ₂, hσ₂⟩ := exists_factor π' hπ's (π'.comp σ.symm.toMonoidHom) (hσc σ.symm)
  have h12 : σ₂.comp σ₁ = MonoidHom.id C := by
    ext c
    obtain ⟨x, rfl⟩ := hπ's c
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [hσ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hσ₂, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have h21 : σ₁.comp σ₂ = MonoidHom.id C := by
    ext c
    obtain ⟨x, rfl⟩ := hπ's c
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [hσ₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hσ₁, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  let σ' : C ≃* C := σ₁.toMulEquiv σ₂ h12 h21
  have hσ'π' : ∀ x, σ' (π' x) = π' (σ x) := fun x => by
    show σ₁ (π' x) = π' (σ x)
    rw [hσ₁]
    rfl
  obtain ⟨α, hα, -⟩ := hlift (σ'.toMonoidHom.comp π)
  obtain ⟨α', hα', -⟩ := hlift (σ'.symm.toMonoidHom.comp π)
  obtain ⟨β, -, hβ⟩ := hlift π
  have hα1 : ∀ x, π (α x) = σ' (π x) := fun x => DFunLike.congr_fun hα x
  have hα1' : ∀ x, π (α' x) = σ'.symm (π x) := fun x => DFunLike.congr_fun hα' x
  have e1 : α.comp α' = MonoidHom.id K :=
    (hβ _ (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, hα1, hα1', MulEquiv.apply_symm_apply])).trans
      (hβ _ (MonoidHom.ext fun x => by simp)).symm
  have e2 : α'.comp α = MonoidHom.id K :=
    (hβ _ (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, hα1, hα1', MulEquiv.symm_apply_apply])).trans
      (hβ _ (MonoidHom.ext fun x => by simp)).symm
  let αe : K ≃* K := α.toMulEquiv α' e2 e1
  have hαe : ∀ x, αe x = α x := fun x => rfl
  refine ⟨αe, σ', ?_, fun x => hα1 x⟩
  have hcmp : θ.comp αe.toMonoidHom = σ.toMonoidHom.comp θ := by
    refine MonoidHom.eq_of_eqOn_dense hgen fun x hx => ?_
    obtain ⟨n, hn⟩ := hx
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    refine eq_of_pElement (π := π') hcenπ' hCπ' ?_ ?_ ?_
    · calc π' (θ (αe x)) = π (αe x) := hπ' _
        _ = σ' (π x) := hα1 x
        _ = σ' (π' (θ x)) := by rw [hπ']
        _ = π' (σ (θ x)) := hσ'π' _
    · exact exists_orderOf_map_eq_pow θ (exists_orderOf_map_eq_pow αe.toMonoidHom ⟨n, hn⟩)
    · exact exists_orderOf_map_eq_pow σ.toMonoidHom (exists_orderOf_map_eq_pow θ ⟨n, hn⟩)
  exact fun x => DFunLike.congr_fun hcmp x

end Transport

theorem closure_pElements_eq_top {K : Type*} [Group K] {ι : Type*} {X : ι → Subgroup K}
    {S : Set ι} {p : ℕ} [Fact p.Prime] (hgen : ⨆ γ ∈ S, X γ = ⊤)
    (hX : ∀ γ ∈ S, IsPGroup p (X γ)) :
    Subgroup.closure {y : K | ∃ n : ℕ, orderOf y = p ^ n} = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact iSup₂_le fun γ hγ y hy =>
    Subgroup.subset_closure (exists_orderOf_eq_pow_of_mem (hX γ hγ) ⟨y, hy⟩)

theorem not_dvd_card_of_forall_pow_card_sub_one {K : Type*} [Group K] {N : Subgroup K} [Finite N]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (h : ∀ z ∈ N, z ^ (Nat.card F - 1) = 1) : ¬ p ∣ Nat.card N := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : (x : K) ^ (Nat.card F - 1) = 1 := h x x.2
  have h2 : orderOf x ∣ Nat.card F - 1 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
  rw [hx] at h2
  have := Fintype.ofFinite F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have h3 : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have h4 : p ∣ 1 := by
    have h5 := Nat.dvd_sub h3 h2
    rwa [Nat.sub_sub_self (Nat.card_pos : 0 < Nat.card F)] at h5
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h4)

theorem center_le_ker_of_surjective {K C : Type*} [Group K] [Group C] {π : K →* C}
    (hπ : Function.Surjective π) (hZC : Subgroup.center C = ⊥) :
    Subgroup.center K ≤ π.ker := fun z hz => by
  have hc : π z ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨y, rfl⟩ := hπ c
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  rw [hZC, Subgroup.mem_bot] at hc
  exact hc

theorem pow_eq_one_of_mem_iSup {K : Type*} [Group K] {ι : Type*} {H : ι → Subgroup K}
    (hcomm : ∀ i j, ∀ h ∈ H i, ∀ h' ∈ H j, Commute h h') {m : ℕ}
    (hm : ∀ i, ∀ h ∈ H i, h ^ m = 1) : ∀ t ∈ ⨆ i, H i, t ^ m = 1 := by
  have h1 : ∀ j, ∀ h' ∈ H j, ∀ t ∈ ⨆ i, H i, Commute t h' := fun j h' hh' t ht =>
    Subgroup.iSup_induction H (C := fun t => Commute t h') ht
      (fun i x hx => hcomm i j x hx h' hh') (Commute.one_left _) (fun x y hx hy => hx.mul_left hy)
  have h2 : ∀ s ∈ ⨆ i, H i, ∀ t ∈ ⨆ i, H i, Commute t s := fun s hs t ht =>
    Subgroup.iSup_induction H (C := fun s => Commute t s) hs
      (fun j x hx => h1 j x hx t ht) (Commute.one_right _) (fun x y hx hy => hx.mul_right hy)
  intro t ht
  refine Subgroup.iSup_induction' H (C := fun t _ => t ^ m = 1)
    (fun i x hx => hm i x hx) (one_pow _) (fun x y hx hy hxm hym => ?_) ht
  rw [(h2 y hy x hx).mul_pow, hxm, hym, one_mul]

theorem exists_orderOf_param {ι : Type} [Fintype ι] [DecidableEq ι]
    {Φ : CFSG.LieType.Steinberg.RootSystem ι}
    {K : Type*} [Group K] {X : (ι → ℤ) → Subgroup K} {F : Type*} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] {x : (ι → ℤ) → F → K}
    (hx : IsParametrization (Φ := Φ) X x) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (c : F) :
    ∃ n : ℕ, orderOf (x γ c) = p ^ n := by
  have hmem : x γ c ∈ X γ := ((hx γ hγ).1 _).2 ⟨c, rfl⟩
  have := exists_orderOf_eq_pow_of_mem (isPGroup_of_isParametrization (p := p) hx hγ) ⟨_, hmem⟩
  simpa using this

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
