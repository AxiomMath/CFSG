module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Dih
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Lift
import CFSG.Adapters.StatedPSLTwoNine

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv

variable {G : Type} [Group G]

theorem mem_normalizer_layerIn [Finite G] {C : Subgroup G} {g : G}
    (hg : g ∈ normalizer (C : Set G)) : g ∈ normalizer (GSThmB.layerIn C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  refine Sol76.le_normalizer_of_forall_conj_mem (H := normalizer (C : Set G)) ?_ hg
  intro c hc y hy
  obtain ⟨k, hk, rfl⟩ := mem_map.mp hy
  let σ : ↥C ≃* ↥C :=
    { toFun := fun w => ⟨c * w * c⁻¹, (mem_normalizer_iff.mp hc w).mp w.2⟩
      invFun := fun w => ⟨c⁻¹ * w * c, by
        have h := (mem_normalizer_iff.mp (inv_mem hc) w).mp w.2
        rwa [inv_inv] at h⟩
      left_inv := fun w => by
        apply Subtype.ext
        change c⁻¹ * (c * (w : G) * c⁻¹) * c = w
        group
      right_inv := fun w => by
        apply Subtype.ext
        change c * (c⁻¹ * (w : G) * c) * c⁻¹ = w
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        change c * ((a : G) * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹)
        group }
  have hσk : σ k ∈ pLayer ↥C 2 := by
    rw [← Subgroup.characteristic_iff_map_eq.mp hchar σ]
    exact mem_map_of_mem _ hk
  exact ⟨σ k, hσk, rfl⟩

@[expose] noncomputable def phiHom (Q : Subgroup G) :
    ↥(normalizer (Q : Set G)) →* MulAut (↥Q ⧸ center ↥Q) where
  toFun g := C3.phi g.2 (MulEquiv.refl _)
  map_one' := Q81.phi_one _
  map_mul' g h := Q81.phi_mul _ g.2 h.2

theorem nonempty_equiv_alternating_six {X : Type} [Group X]
    (h : Blueprint.LieModel X .PSL 2 3 2) : Nonempty (X ≃* alternatingGroup (Fin 6)) :=
  CFSG.Blueprint.LieModel.nonempty_mulEquiv_alternating_six h

theorem lt_card_of_lieModel {S : Type} [Group S]
    (hP : Blueprint.LieModel S .PSL 4 3 1 ∨ Blueprint.LieModel S .PSU 4 3 1) :
    360 < Nat.card S := by
  rcases hP with h | h
  · rw [GH74.card_of_lieModel_PSL (by norm_num) h]
    decide
  · rw [GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) h]
    decide

theorem pgl_of_models (hM : P1Models) (G : Type) [Group G] [Finite G] (Q : Subgroup G)
    (hQ : IsQuasisimple ↥Q)
    (hP : Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 3 1)
    (_hZ : Nat.card ↥(center ↥Q) ∣ 2) (t : G) (D : Subgroup G) (ht : t ∈ normalizer (Q : Set G))
    (ht2 : orderOf t = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {t})) .PSL 2 3 2)
    (hDN : D ≤ normalizer (Q : Set G)) (hDt : D ≤ centralizer {t})
    (hDe : Nonempty (↥D ≃* DihedralGroup 8))
    (hDL : Nat.card ↥(D ⊓ GSThmB.layerIn (Q ⊓ centralizer {t})) = 8)
    (x : G) (hxD : x ∈ D) (hxL : x ∉ GSThmB.layerIn (Q ⊓ centralizer {t})) (hx2 : orderOf x = 2) :
    ∃ J : Subgroup G, J ≤ Q ⊓ centralizer {x} ∧
      IsPComponent 2 (J.subgroupOf (Q ⊓ centralizer {x})) ∧ IsOfType (HarrisF 3) ↥J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eD⟩ := hDe
  set S := ↥Q ⧸ center ↥Q
  set e₀ : S ≃* S := MulEquiv.refl S with he₀
  set L := GSThmB.layerIn (Q ⊓ centralizer {t}) with hLdef
  have : IsSimpleGroup ↥L := isSimpleGroup_of_lieModel_psl2 hL
  have hLnab := nonabelian_of_lieModel_psl2 hL
  have hLZ : center ↥L = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLnab
  have hLcard : Nat.card ↥L = 360 := by
    rw [GH74.card_of_lieModel_PSL (by norm_num) hL]
    decide
  obtain ⟨eA⟩ := nonempty_equiv_alternating_six hL
  have hL8 : ∀ g ∈ L, g ^ 8 = 1 → g ^ 4 = 1 := by
    intro g hg h8
    set gL : ↥L := ⟨g, hg⟩ with hgL
    have h1 : gL ^ 8 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h8)
    have h2 : ((eA gL : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 8 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
    have h3 := pow_four_of_pow_eight _ h2
    have h4 : eA (gL ^ 4) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by rw [Subgroup.coe_pow, h3, Subgroup.coe_one])
    have h5 : gL ^ 4 = 1 := eA.injective (by rw [h4, map_one])
    have h6 := congrArg Subtype.val h5
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h6
  obtain ⟨ℓ, ⟨hℓD, hℓL⟩, hℓ2, h8, h4L, h4ne⟩ := exists_reflection_mul eD hL8 hDL hxD hxL hx2
  have hLQ : L ≤ Q := C3.Lay_le.trans inf_le_left
  have hℓQ : ℓ ∈ Q := hLQ hℓL
  have hxN : x ∈ normalizer (Q : Set G) := hDN hxD
  have hℓN : ℓ ∈ normalizer (Q : Set G) := hDN hℓD
  have : IsSimpleGroup S := hQ.2.1
  have hSZ : center S = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hQ.2.2
  have hconj_inj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hc : y ∈ center S := by
      rw [mem_center_iff]
      intro z
      have h1 := congrArg (fun φ : MulAut S => φ z) hy
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * y = (y * z * y⁻¹) * y := by rw [h1]
        _ = y * z := by group
    rw [hSZ, mem_bot] at hc
    exact hc
  have hπL : ∀ {a : ↥Q}, (a : G) ∈ L → C3.piQ e₀ a = 1 → a = 1 := by
    intro a ha h1
    exact C3.eq_one_of_mem_Lay hLZ ha ((C3.piQ_eq_one_iff e₀ a).mp h1)
  set α := phiHom Q ⟨t, ht⟩ with hα
  set β := phiHom Q ⟨x, hxN⟩ with hβ
  set ℓb := C3.piQ e₀ ⟨ℓ, hℓQ⟩ with hℓb
  have hφℓ : phiHom Q ⟨ℓ, hℓN⟩ = MulAut.conj ℓb := Q81.phi_of_mem e₀ hℓQ
  have hr8 : orderOf (β * MulAut.conj ℓb) = 8 := by
    have key : β * MulAut.conj ℓb = phiHom Q (⟨x, hxN⟩ * ⟨ℓ, hℓN⟩) := by
      rw [map_mul, hφℓ]
    rw [key]
    set r : ↥(normalizer (Q : Set G)) := ⟨x, hxN⟩ * ⟨ℓ, hℓN⟩ with hr
    have h8' : phiHom Q r ^ 8 = 1 := by
      have hr8 : r ^ 8 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h8)
      rw [← map_pow, hr8, map_one]
    have h4' : ¬ phiHom Q r ^ 2 ^ 2 = 1 := by
      have hr4Q : ((r ^ 4 : ↥(normalizer (Q : Set G))) : G) ∈ Q := by
        rw [Subgroup.coe_pow]
        exact hLQ h4L
      have hr4L : ((r ^ 4 : ↥(normalizer (Q : Set G))) : G) ∈ L := by
        rw [Subgroup.coe_pow]
        exact h4L
      have he : phiHom Q (r ^ 4) = MulAut.conj (C3.piQ e₀ ⟨_, hr4Q⟩) :=
        Q81.phi_of_mem e₀ hr4Q
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← map_pow, he]
      intro h1
      have h2 := hconj_inj (h1.trans (map_one _).symm)
      have h3 := hπL (a := ⟨_, hr4Q⟩) hr4L h2
      apply h4ne
      have h5 := congrArg Subtype.val h3
      rw [Subgroup.coe_one, Subgroup.coe_pow] at h5
      exact h5
    have h8'' : phiHom Q r ^ 2 ^ (2 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]
      exact h8'
    rw [orderOf_eq_prime_pow h4' h8'']
    norm_num
  have hα2 : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact C3.phi_sq ht e₀ (by rw [← pow_two, ← ht2, pow_orderOf_eq_one])
    · show C3.phi ht e₀ ≠ 1
      refine C3.phi_ne_one ht e₀ hQ.1 fun htC => ?_
      have hQC : Q ⊓ centralizer {t} = Q := by
        refine inf_eq_left.mpr fun q hq => ?_
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp htC q hq
      have hLn : (L.subgroupOf Q).Normal := by
        have h := C3.le_normalizer_Lay (Q := Q) (x := t)
        rw [hQC] at h
        exact (normal_subgroupOf_iff_le_normalizer hLQ).mpr h
      rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hQ hLn with htop | hZL
      · have hQL : Q ≤ L := fun q hq => by
          have h := htop ▸ mem_top (⟨q, hq⟩ : ↥Q)
          exact h
        have h1 : Nat.card ↥Q ≤ 360 := hLcard ▸ card_le_of_le hQL
        have h2 : Nat.card S ≤ Nat.card ↥Q :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center ↥Q))
        have h3 : 360 < Nat.card S := lt_card_of_lieModel hP
        omega
      · obtain ⟨a, b, hab⟩ := hLnab
        apply hab
        have ha : (⟨a, hLQ a.2⟩ : ↥Q) ∈ center ↥Q := hZL (show (a : G) ∈ L from a.2)
        have h := mem_center_iff.mp ha ⟨b, hLQ b.2⟩
        exact Subtype.ext (congrArg Subtype.val h).symm
  have hℓb2 : orderOf ℓb = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (⟨ℓ, hℓQ⟩ : ↥Q) ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, ← hℓ2, pow_orderOf_eq_one])
      rw [hℓb, ← map_pow, h1, map_one]
    · intro h1
      have h2 := hπL (a := ⟨ℓ, hℓQ⟩) hℓL h1
      have h3 : ℓ = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hℓ2
      norm_num at hℓ2
  have hβ2 : orderOf β = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact C3.phi_sq hxN e₀ (by rw [← pow_two, ← hx2, pow_orderOf_eq_one])
    · intro h1
      rw [h1, one_mul, orderOf_injective _ hconj_inj ℓb, hℓb2] at hr8
      norm_num at hr8
  have hcomm : α * β = β * α := by
    rw [hα, hβ, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * x = x * t
    exact (mem_centralizer_singleton_iff.mp (hDt hxD)).symm
  have hJcard : Nat.card ↥(C3.Jp e₀ t) = 360 := by
    rw [← Nat.card_congr (C3.equivJp e₀ hLZ).toEquiv]
    exact hLcard
  have hJfix : ∀ y ∈ C3.Jp e₀ t, α y = y := fun y hy => mem_fixSub.mp (C3.Jp_le_fixSub ht e₀ hy)
  have hJnorm : ∀ c : S, α c = c → ∀ y ∈ C3.Jp e₀ t, c * y * c⁻¹ ∈ C3.Jp e₀ t := by
    intro c hc y hy
    obtain ⟨q, rfl⟩ := C3.piQ_surjective e₀ c
    obtain ⟨l, hl, rfl⟩ := hy
    have hqfix : C3.piQ e₀ q ∈ fixSub (C3.phi ht e₀) := mem_fixSub.mpr hc
    set H := ((fixSub (C3.phi ht e₀)).comap (C3.piQ e₀)).map Q.subtype with hH
    have hHN : H ≤ normalizer ((Q ⊓ centralizer {t} : Subgroup G) : Set G) := by
      refine Sol76.le_normalizer_of_forall_conj_mem ?_
      rintro _ ⟨q', hq', rfl⟩ p hp
      obtain ⟨hpQ, hpt⟩ := mem_inf.mp hp
      refine mem_inf.mpr ⟨Q.mul_mem (Q.mul_mem q'.2 hpQ) (Q.inv_mem q'.2), ?_⟩
      exact C3.conj_mem_centralizer ht e₀ (c := ⟨p, hpQ⟩) hq' hpt
    have hqL : (q : G) ∈ normalizer (L : Set G) := mem_normalizer_layerIn (hHN ⟨q, hqfix, rfl⟩)
    have hl' : (l : G) ∈ L := hl
    have hconjL : ((q * l * q⁻¹ : ↥Q) : G) ∈ L := (mem_normalizer_iff.mp hqL _).mp hl'
    exact ⟨q * l * q⁻¹, hconjL, by rw [map_mul, map_mul, map_inv]⟩
  have hℓmem : ℓb ∈ C3.Jp e₀ t := ⟨⟨ℓ, hℓQ⟩, hℓL, rfl⟩
  obtain ⟨M, hMβ, hMn, hMA⟩ := (hM S hP).aut α β (C3.Jp e₀ t) ℓb hα2 hβ2 hcomm hJcard hJfix
    hJnorm hℓmem hℓb2 hr8
  refine exists_component_of_fixed hxN e₀ (M := M) (fun y hy => mem_fixSub.mpr (hMβ y hy)) ?_ hMA
  exact Sol76.le_normalizer_of_forall_conj_mem fun c hc y hy => hMn c (mem_fixSub.mp hc) y hy

end CFSG.ComponentClassification.HarrisLit.P1
