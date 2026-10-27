module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open CFSG.Open

noncomputable section

section Quot

variable {Ω : Type} [Group Ω] (Z : Subgroup Ω) [Z.Normal]

theorem commute_of_mk_commute (hZc : ∀ z ∈ Z, ∀ g : Ω, z * g = g * z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    {x y : Ω} (hy : y ^ 3 = 1)
    (hxy : (QuotientGroup.mk x : Ω ⧸ Z) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x) : x * y = y * x := by
  have hc : x * y * x⁻¹ * y⁻¹ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hxy]
    group
  have hc2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := hZ2 _ hc
  have hcy : Commute (x * y * x⁻¹ * y⁻¹) y := hZc _ hc y
  have h1 : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
  have hcube : (x * y * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy, mul_one, mul_inv_cancel]
  have hc3 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := by
    have h := hcube
    rw [h1, hcy.mul_pow, hy, mul_one] at h
    exact h
  have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    calc x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 3 * ((x * y * x⁻¹ * y⁻¹) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2, inv_one, mul_one]
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc1, one_mul]

theorem card_map_injOn {G H : Type} [Group G] [Group H] (f : G →* H) (P : Subgroup G)
    (hf : ∀ x ∈ P, f x = 1 → x = 1) : Nat.card (P.map f) = Nat.card P := by
  let g : P →* H := f.comp P.subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x.1 x.2 hx)
  have h1 : P.map f = g.range := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [h1]
  exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm

@[expose] def equivMapOfInjOn {G H : Type} [Group G] [Group H] (f : G →* H) (P : Subgroup G)
    (hf : ∀ x ∈ P, f x = 1 → x = 1) : P ≃* P.map f :=
  MulEquiv.ofBijective
    ((f.comp P.subtype).codRestrict (P.map f) (fun x => ⟨x, x.2, rfl⟩))
    ⟨by
      intro a b hab
      have h : f a.1 = f b.1 := congrArg Subtype.val hab
      have h2 : f (a.1 * b.1⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
      have h3 := hf _ (P.mul_mem a.2 (P.inv_mem b.2)) h2
      exact Subtype.ext (mul_inv_eq_one.1 h3),
     by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩⟩

theorem lift_exists [Finite Ω] (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (E : Subgroup (Ω ⧸ Z))
    (hc : Nat.card E = 27) :
    ∃ P : Subgroup Ω, (∀ x ∈ P, (QuotientGroup.mk x : Ω ⧸ Z) = 1 → x = 1) ∧
      P.map (QuotientGroup.mk' Z) = E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' Z with hπ
  set E' : Subgroup Ω := E.comap π with hE'
  let ρ' : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ' := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e : Ω ⧸ Z)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show π x ∈ E
      have hx' : π x = (e : Ω ⧸ Z) := hx
      rw [hx']
      exact e.2
    · apply Subtype.ext
      exact hx
  have hcardE' : Nat.card E' = 27 * Nat.card ρ'.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ'.ker
    have hq : Nat.card (E' ⧸ ρ'.ker) = Nat.card E :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ).toEquiv
    rw [hq, hc] at h1
    exact h1
  have exp_two' : ∀ y : E', ρ' y = 1 → y ^ 2 = 1 := by
    intro y hy
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    apply hZ2
    have h2 : π (y : Ω) = 1 := congrArg Subtype.val hy
    exact (QuotientGroup.eq_one_iff (y : Ω)).1 h2
  have hkerρ : ¬ 3 ∣ Nat.card ρ'.ker := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ρ'.ker) 3 hdvd
    have hx2 : (x : E') ^ 2 = 1 := exp_two' x.1 (MonoidHom.mem_ker.1 x.2)
    have hx3 : (x : E') ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (x : E')
      rwa [Subgroup.orderOf_coe, hx] at h
    have h1 : (x : E') = 1 := by
      calc (x : E') = (x : E') ^ 3 * ((x : E') ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2, inv_one, mul_one]
    have h2 : orderOf (x : E') = 3 := by rw [Subgroup.orderOf_coe, hx]
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have h27 : 3 ^ 3 ∣ Nat.card E' := ⟨Nat.card ρ'.ker, by rw [hcardE']; norm_num⟩
  obtain ⟨P0, hP0⟩ := Sylow.exists_subgroup_card_pow_prime (G := E') 3 h27
  have hinf : P0 ⊓ ρ'.ker = ⊥ := by
    have hd1 : Nat.card (P0 ⊓ ρ'.ker : Subgroup E') ∣ 3 ^ 3 := by
      rw [← hP0]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (P0 ⊓ ρ'.ker : Subgroup E') ∣ Nat.card ρ'.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd1
    have hcard1 : Nat.card (P0 ⊓ ρ'.ker : Subgroup E') = 1 := by
      rcases i with _ | i
      · simpa using hi
      · exfalso
        apply hkerρ
        have h3d : 3 ∣ Nat.card (P0 ⊓ ρ'.ker : Subgroup E') := by
          rw [hi]
          exact dvd_pow_self 3 (Nat.succ_ne_zero i)
        exact dvd_trans h3d hd2
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hΨinj : Function.Injective (ρ'.comp P0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyI : (y : E') ∈ P0 ⊓ ρ'.ker := ⟨y.2, hy⟩
    rw [hinf] at hyI
    exact Subtype.ext (Subgroup.mem_bot.1 hyI)
  have hΨbij : Function.Bijective (ρ'.comp P0.subtype) :=
    Function.Injective.bijective_of_nat_card_le hΨinj (by rw [hP0, hc]; norm_num)
  refine ⟨P0.map E'.subtype, ?_, ?_⟩
  · intro x hx hπx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hρy : ρ' y = 1 := by
      apply Subtype.ext
      exact hπx
    have hyI : y ∈ P0 ⊓ ρ'.ker := ⟨hy, hρy⟩
    rw [hinf] at hyI
    rw [Subgroup.mem_bot.1 hyI]
    rfl
  · ext e
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 he
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact (ρ' y).2
    · intro he
      obtain ⟨z, hz⟩ := hΨbij.2 ⟨e, he⟩
      refine Subgroup.mem_map.2 ⟨E'.subtype (z : E'), Subgroup.mem_map.2 ⟨(z : E'), z.2, rfl⟩, ?_⟩
      exact congrArg Subtype.val hz

theorem lift_props [Finite Ω] (hZc : ∀ z ∈ Z, ∀ g : Ω, z * g = g * z)
    (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (E : Subgroup (Ω ⧸ Z)) (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 27) :
    ∃ P : Subgroup Ω, Nat.card P = 27 ∧ (∀ x ∈ P, x ^ 3 = 1) ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      (∀ x ∈ P, (QuotientGroup.mk x : Ω ⧸ Z) = 1 → x = 1) ∧
      P.map (QuotientGroup.mk' Z) = E := by
  obtain ⟨P, hinj, himg⟩ := lift_exists Z hZ2 E hc
  have hmemE : ∀ x ∈ P, (QuotientGroup.mk x : Ω ⧸ Z) ∈ E := by
    intro x hx
    rw [← himg]
    exact Subgroup.mem_map_of_mem _ hx
  have hcard : Nat.card P = 27 := by
    rw [← hc, ← himg, card_map_injOn _ P hinj]
  have hexp : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (P.pow_mem hx 3)
    rw [QuotientGroup.mk_pow]
    exact hE.2 _ (hmemE x hx)
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    apply commute_of_mk_commute Z hZc hZ2 (hexp y hy)
    have := hE.1.is_comm.comm ⟨QuotientGroup.mk x, hmemE x hx⟩ ⟨QuotientGroup.mk y, hmemE y hy⟩
    exact congrArg Subtype.val this
  exact ⟨P, hcard, hexp, hcomm, hinj, himg⟩

theorem kerConcl_of_central_quotient [Finite Ω] (hZc : ∀ z ∈ Z, ∀ g : Ω, z * g = g * z)
    (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (geom : ∀ P : Subgroup Ω, Nat.card P = 27 → (∀ x ∈ P, x ^ 3 = 1) →
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
      ∃ F : Subgroup Ω, F ≤ P ∧ Nat.card F = 9 ∧ ∃ H : Subgroup Ω,
        (∀ h ∈ H, ∀ f ∈ F, h * f = f * h) ∧
        (∀ g : Ω, (∀ f ∈ F, g * f = f * g) → ∀ h ∈ H, g * h * g⁻¹ ∈ H) ∧
        CFSG.Open.IsQuasisimple H ∧ 3 ∣ Nat.card (H ⧸ Subgroup.center H) ∧
        (∀ h ∈ H, h ∈ Z → h = 1))
    (E : Subgroup (Ω ⧸ Z)) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  obtain ⟨P, hcard, hexp, hcomm, hinj, himg⟩ := lift_props Z hZc hZ2 E hE hc
  obtain ⟨F, hFP, hF9, H, hHF, hHnorm, hHq, hH3, hHZ⟩ := geom P hcard hexp hcomm
  set π := QuotientGroup.mk' Z with hπ
  have hπH : ∀ x ∈ H, π x = 1 → x = 1 := fun x hx h =>
    hHZ x hx ((QuotientGroup.eq_one_iff x).1 h)
  have hπF : ∀ x ∈ F, π x = 1 → x = 1 := fun x hx h => hinj x (hFP hx) h
  have hHC : H.map π ≤ Subgroup.centralizer ((F.map π : Subgroup (Ω ⧸ Z)) : Set (Ω ⧸ Z)) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (hHF h hh f hf).symm
  refine ⟨F.map π, ?_, ?_, H.map π, hHC, ?_, ?_, ?_⟩
  · rw [← himg]
    exact Subgroup.map_mono hFP
  · rw [card_map_injOn π F hπF, hF9]
  · refine CFSG.Open.IsSubnormal.step hHC ?_ (CFSG.Open.IsSubnormal.refl _)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨h, hh, hhn⟩ := Subgroup.mem_map.1 hn
    obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (g : Ω ⧸ Z)
    have hcg : ∀ f ∈ F, g' * f = f * g' := by
      intro f hf
      have h1 := Subgroup.mem_centralizer_iff.1 g.2 (π f) (Subgroup.mem_map_of_mem π hf)
      apply commute_of_mk_commute Z hZc hZ2 (hexp f (hFP hf))
      have h2 : (QuotientGroup.mk f : Ω ⧸ Z) * QuotientGroup.mk g' =
          QuotientGroup.mk g' * QuotientGroup.mk f := by
        rw [hg']
        exact h1
      exact h2.symm
    refine Subgroup.mem_map.2 ⟨g' * h * g'⁻¹, hHnorm g' hcg h hh, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have hπg : π g' = (g : Ω ⧸ Z) := hg'
    rw [hπg, hhn]
  · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv
      (equivMapOfInjOn π H hπH) hHq
  · rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv
      (equivMapOfInjOn π H hπH)]
    exact hH3

end Quot

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
