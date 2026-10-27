module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutAlt8Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutResidue
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Perm

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.M24Std

theorem multZMod_eq_of_ne_one : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by
  decide

theorem eq_one_or_eq_of_snd_eq_one {C : Type*} [Group C]
    (φ : C ≃* Multiplicative (ZMod 2) × Perm (Fin 6)) {w : C} (hw1 : w ≠ 1)
    (hwc : ∀ c : C, c * w = w * c) {c : C} (hc : (φ c).2 = 1) : c = 1 ∨ c = w := by
  have hw2 : (φ w).2 = 1 := by
    refine perm_six_eq_one_of_comm_alt fun t _ => ?_
    obtain ⟨u, hu⟩ := φ.surjective (1, t)
    have h := congrArg (fun x => (φ x).2) (hwc u)
    simp only [map_mul, Prod.snd_mul, hu] at h
    exact h
  by_cases hc1 : (φ c).1 = 1
  · left
    have h1 : φ c = 1 := Prod.ext hc1 hc
    exact φ.injective (h1.trans (map_one φ).symm)
  · right
    have hw1' : (φ w).1 ≠ 1 := fun h =>
      hw1 (φ.injective ((Prod.ext h hw2 : φ w = 1).trans (map_one φ).symm))
    exact φ.injective (Prod.ext (multZMod_eq_of_ne_one _ _ hc1 hw1') (hc.trans hw2.symm))

theorem comm_of_fixed_trivial {E : Type*} [Group E] [Finite E] (ζ : MulAut E) (hζ : ζ * ζ = 1)
    (hfix : ∀ x : E, ζ x = x → x = 1) : ∀ u v : E, u * v = v * u := by
  have hζζ : ∀ x : E, ζ (ζ x) = x := fun x => by
    have := congrArg (fun f : MulAut E => f x) hζ
    simpa using this
  have hinj : Function.Injective (fun x : E => x⁻¹ * ζ x) := by
    intro x y h
    have h1 : ζ (y * x⁻¹) = y * x⁻¹ := by
      have h' : x⁻¹ * ζ x = y⁻¹ * ζ y := h
      rw [map_mul, map_inv]
      calc ζ y * (ζ x)⁻¹ = y * (y⁻¹ * ζ y) * (x⁻¹ * ζ x)⁻¹ * x⁻¹ := by group
        _ = y * x⁻¹ := by rw [← h']; group
    have h2 := hfix _ h1
    exact (mul_inv_eq_one.1 h2).symm
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have hinv : ∀ w : E, ζ w = w⁻¹ := fun w => by
    obtain ⟨x, rfl⟩ := hsurj w
    simp only [map_mul, map_inv, hζζ]
    group
  intro u v
  have h := hinv (u * v)
  rw [map_mul, hinv, hinv, mul_inv_rev] at h
  have h3 := congrArg (fun x => x⁻¹) h
  simpa using h3.symm

theorem card_conjClass_mul_card_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card {h : G | IsConj g h} * Nat.card (centralizer {g}) = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert! MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  ext h
  simp only [Set.mem_ofPred_eq, ConjAct.mem_orbit_conjAct, isConj_comm]

theorem false_of_outerFusion_of_card_mulAut_lt {X : Type} [Group X] [Finite X] {z : X}
    (hz2 : z * z = 1)
    (hC : Nonempty (centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × Perm (Fin 6)))
    (hF : OuterFusion X z) {E : Subgroup X} [E.Normal] (hE : ∃ a b : E, a * b ≠ b * a)
    (hz : z ∉ E ⊔ centralizer (E : Set X)) (hA : Nat.card (MulAut E) < 66240) : False := by
  classical
  obtain ⟨φ⟩ := hC
  have hfinA : Finite (MulAut E) :=
    Finite.of_injective (fun f : MulAut E => (f : E → E)) DFunLike.coe_injective
  let σ : X →* MulAut E := MulAut.conjNormal
  have hker : ∀ x : X, σ x = 1 → x ∈ centralizer (E : Set X) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro h hh
    have h2 := congrArg (fun f : MulAut E => ((f ⟨h, hh⟩ : E) : X)) hx
    have h3 : x * h * x⁻¹ = h := h2
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hζ2 : σ z * σ z = 1 := by rw [← map_mul, hz2, map_one]
  have hσz : σ z ≠ 1 := fun h => hz (Subgroup.mem_sup_right (hker z h))
  have hz1 : z ≠ 1 := fun h => hσz (by rw [h, map_one])
  let C : Subgroup X := centralizer ({z} : Set X)
  let z' : C := ⟨z, mem_centralizer_singleton_iff.2 rfl⟩
  have hz'c : ∀ c : C, c * z' = z' * c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.1 c.2)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  let σC : C →* MulAut E := σ.comp C.subtype
  let ψ : C →* Perm (Fin 6) := (MonoidHom.snd _ _).comp φ.toMonoidHom
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨c, hc⟩ := φ.surjective (1, s)
    exact ⟨c, by simp [ψ, hc]⟩
  have hNnormal : ((σC.ker).map ψ).Normal := (MonoidHom.normal_ker σC).map ψ hψ
  have hK : σC.ker = ⊥ := by
    rcases perm_six_eq_bot_or_alt_le hNnormal with hN | hN
    · refine eq_bot_iff.2 fun k hk => ?_
      have hψk : ψ k = 1 := by
        have : ψ k ∈ (σC.ker).map ψ := mem_map_of_mem ψ hk
        rwa [hN, mem_bot] at this
      rcases eq_one_or_eq_of_snd_eq_one φ hz'1 hz'c hψk with h | h
      · exact h
      · exfalso
        apply hσz
        have : σC k = 1 := hk
        rwa [h] at this
    · exfalso
      have hfix : ∀ x : E, σ z x = x → x = 1 := by
        intro x hx
        have h3 : z * (x : X) * z⁻¹ = x := congrArg Subtype.val hx
        have hxz : (x : X) ∈ C :=
          mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h3).symm
        let c : C := ⟨x, hxz⟩
        have hψc : ψ c = 1 := by
          refine perm_six_eq_one_of_comm_alt fun t ht => ?_
          obtain ⟨k, hk, rfl⟩ := mem_map.1 (hN ht)
          have hkc : (k : X) ∈ centralizer (E : Set X) := hker k hk
          have hxk : (x : X) * k = k * x := mem_centralizer_iff.1 hkc x x.2
          have h4 := congrArg ψ (Subtype.ext hxk : c * k = k * c)
          rw [map_mul, map_mul] at h4
          exact h4.symm
        rcases eq_one_or_eq_of_snd_eq_one φ hz'1 hz'c hψc with h | h
        · have h' : (c : X) = 1 := congrArg Subtype.val h
          exact Subtype.ext h'
        · exfalso
          have : (x : X) = z := congrArg Subtype.val h
          exact hz (Subgroup.mem_sup_left (this ▸ x.2))
      exact hE.elim fun a ⟨b, hab⟩ => hab (comm_of_fixed_trivial (σ z) hζ2 hfix a b)
  have hinj : Function.Injective σC := (MonoidHom.ker_eq_bot_iff σC).1 hK
  have hC1440 : Nat.card C = 1440 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    have h720 : Nat.card (Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h2, h720]
  have hcomm : ∀ c : C, σ z * σC c = σC c * σ z := fun c => by
    have hc : (c : X) * z = z * c := mem_centralizer_singleton_iff.1 c.2
    show σ z * σ c = σ c * σ z
    rw [← map_mul, ← map_mul, hc]
  have hRle : σC.range ≤ centralizer ({σ z} : Set (MulAut E)) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact (hcomm c).symm
  have hRcard : Nat.card σC.range = 1440 := by
    rw [← hC1440]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hCA : 1440 ≤ Nat.card (centralizer ({σ z} : Set (MulAut E))) :=
    Nat.le_of_dvd Nat.card_pos (hRcard ▸ Subgroup.card_dvd_of_le hRle)
  obtain ⟨b, hbmem, hb2, hb1, hconj⟩ := hF
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hbmem
  have hφ1 : (φ c').1 = 1 :=
    Abelianization.commutator_subset_ker ((MonoidHom.fst _ _).comp φ.toMonoidHom) hc'
  have hsgn : sign (φ c').2 = 1 := by
    have h := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker
      (sign.comp ((MonoidHom.snd _ _).comp φ.toMonoidHom)) hc')
    simpa using h
  set s : Perm (Fin 6) := (φ c').2 with hs
  have hφc' : φ c' = (1, s) := Prod.ext hφ1 rfl
  have hc'1 : c' ≠ 1 := fun h => hb1 (by rw [h]; rfl)
  have hs1 : s ≠ 1 := fun h => hc'1 (φ.injective (by rw [hφc', h, map_one]; rfl))
  have hc'2 : c' * c' = 1 := Subtype.ext hb2
  have hs2 : s ^ 2 = 1 := by
    have h := congrArg (fun x => (φ x).2) hc'2
    simpa [sq, hs] using h
  obtain ⟨k, hcyc, hk6, hkcard, hksign⟩ := exists_cycleType_eq_replicate_two hs2
  rw [Fintype.card_fin] at hk6 hkcard
  have hk2 : k = 2 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hs1 (cycleType_eq_zero.1 (by simpa using hcyc))
    have hkeven : Even k := by
      by_contra h
      rw [Nat.not_even_iff_odd] at h
      rw [h.neg_one_pow, hsgn] at hksign
      exact absurd hksign (by decide)
    obtain ⟨m, hm⟩ := hkeven
    omega
  subst hk2
  have h16 : Nat.card (centralizer ({s} : Set (Perm (Fin 6)))) = 16 := by
    rw [hkcard]
    simp [Nat.factorial]
  have h720 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h45 := card_conjClass_mul_card_centralizer s
  rw [h16, h720] at h45
  have hT : Nat.card {h : Perm (Fin 6) | IsConj s h} = 45 := by omega
  let cOf : Perm (Fin 6) →* C := φ.symm.toMonoidHom.comp (MonoidHom.inr _ _)
  have hcOf_s : cOf s = c' := (MulEquiv.symm_apply_eq φ).2 hφc'.symm
  have hcOf_inj : Function.Injective cOf := fun t u h =>
    (Prod.ext_iff.1 (φ.symm.injective h)).2
  let Θ : Perm (Fin 6) → MulAut E := fun t => σ z * σC (cOf t)
  have hΘinj : Function.Injective Θ := fun t u h => hcOf_inj (hinj (mul_left_cancel h))
  have hΘ1 : Θ 1 = σ z := by simp [Θ]
  have hζb : IsConj (σ z) (σ z * σC c') := by
    obtain ⟨y, hy⟩ := isConj_iff.1 hconj
    refine isConj_iff.2 ⟨σ y, ?_⟩
    have := congrArg σ hy
    rw [map_mul, map_mul, map_inv, map_mul] at this
    exact this
  have hΘconj : ∀ t, IsConj s t → IsConj (σ z) (Θ t) := by
    intro t ht
    obtain ⟨u, hu⟩ := isConj_iff.1 ht
    have hct : cOf t = cOf u * c' * (cOf u)⁻¹ := by
      rw [← hu, map_mul, map_mul, map_inv, hcOf_s]
    have h1 : Θ t = σC (cOf u) * (σ z * σC c') * (σC (cOf u))⁻¹ := by
      simp only [Θ]
      rw [hct, map_mul, map_mul, map_inv]
      have hv := hcomm (cOf u)
      calc σ z * (σC (cOf u) * σC c' * (σC (cOf u))⁻¹)
          = (σ z * σC (cOf u)) * σC c' * (σC (cOf u))⁻¹ := by group
        _ = (σC (cOf u) * σ z) * σC c' * (σC (cOf u))⁻¹ := by rw [hv]
        _ = σC (cOf u) * (σ z * σC c') * (σC (cOf u))⁻¹ := by group
    exact hζb.trans (isConj_iff.2 ⟨σC (cOf u), h1.symm⟩)
  let g : Option {h : Perm (Fin 6) | IsConj s h} → {h : MulAut E | IsConj (σ z) h}
    | none => ⟨σ z, IsConj.refl _⟩
    | some t => ⟨Θ t, hΘconj t t.2⟩
  have hne : ∀ u : {h : Perm (Fin 6) | IsConj s h}, Θ u ≠ σ z := fun u h => by
    have h1 : (u : Perm (Fin 6)) = 1 := hΘinj (h.trans hΘ1.symm)
    have hu' : IsConj s (u : Perm (Fin 6)) := u.2
    rw [h1] at hu'
    exact hs1 (isConj_one_left.1 hu')
  have hg : Function.Injective g := by
    rintro (_ | t) (_ | u) h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hne u)
    · exact absurd (congrArg Subtype.val h) (hne t)
    · exact congrArg some (Subtype.ext (hΘinj (congrArg Subtype.val h)))
  have hle := Nat.card_le_card_of_injective g hg
  rw [Finite.card_option, hT] at hle
  have hclassA := card_conjClass_mul_card_centralizer (σ z)
  have := Nat.mul_le_mul hle hCA
  omega

end CFSG.EvenSporadicStandard.M22Std
