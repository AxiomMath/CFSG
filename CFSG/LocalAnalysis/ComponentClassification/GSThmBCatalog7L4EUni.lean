module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAux
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ELin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdL4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedLayer CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal)

variable {H : Type} [Group H] [Finite H]

theorem false_of_psu4 (hsimp : IsSimpleGroup ↥(generalizedFitting H))
    (hC : centralizer (generalizedFitting H : Set H) = ⊥) {r e : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hm : Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 r e) {a b : H}
    (ha : orderOf a = 2) (hb : orderOf b = 2) {J K : Subgroup H}
    (hJF : J ≤ generalizedFitting H) (hKF : K ≤ generalizedFitting H)
    (hJa : J ≤ centralizer ({a} : Set H))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))))
    (hKb : K ≤ centralizer ({b} : Set H))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))))
    (hsyl : ∀ T : Subgroup H, IsPGroup 2 T →
      T ≤ centralizer ({b} : Set H) ⊓ coreActionKernel K → Nat.card T ≤ 2)
    (hbJ : b ∈ coreActionKernel J) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hKm : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p (2 * f)) : False := by
  classical
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨-, Kf, _, _, hKf, ⟨φ⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
  have hud : UnitaryFieldData r e Kf := ⟨hr, he, by rw [hKf, ← pow_mul, mul_comm]⟩
  have : Fact r.Prime := ⟨hr⟩
  let psi : ↥(generalizedFitting H) ≃* unitaryPSU hud 4 :=
    φ.trans (unitaryPSUEquiv hud (by norm_num)).symm
  have : Finite (unitaryPSU hud 4) := Finite.of_equiv _ psi.toEquiv
  have hJq : CFSG.IsQuasisimple J :=
    Catalog7Std.isQuasisimple_of_model hC ha hJa hJF hJ psi fun α hα2 hα1 L' hL' =>
      CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components hud hr2 (n := 4)
        (by norm_num) α (orderOf_eq_prime hα2 hα1) 2 Nat.prime_two L' hL'
  have : IsSimpleGroup (StatedProj (StatedSU 4 (r ^ e) Kf)) := φ.symm.isSimpleGroup
  have hnab : ∃ x y : StatedProj (StatedSU 4 (r ^ e) Kf), x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := hJq.2.2
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨φ ⟨u', hJF u'.2⟩, φ ⟨v', hJF v'.2⟩, fun h' => huv ?_⟩
    have h3 : (⟨u', hJF u'.2⟩ : ↥(generalizedFitting H)) * ⟨v', hJF v'.2⟩ =
        ⟨v', hJF v'.2⟩ * ⟨u', hJF u'.2⟩ := φ.injective (by rw [map_mul, map_mul]; exact h')
    have h1 : u' * v' = v' * u' := by
      apply Subtype.ext
      have h2 := congrArg Subtype.val h3
      simpa using h2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, hinj, hρW, -, hρg⟩ := OutcomeLocal.socle_extension hC φ hZ
  have hcj := OddClassSelector.conj_injective hZ
  have h5' : 5 ≤ p ^ (2 * f) := h5.trans (Nat.pow_le_pow_right hp.pos (by omega))
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have hq3 : 3 ≤ r ^ e := by
    have h3 : 3 ≤ r := by have := hr.two_le; omega
    exact h3.trans (Nat.le_self_pow (by omega) r)
  obtain ⟨hJO, -, Aa, ψa, hAau, hψa, hJt⟩ :=
    psu4_component_type hud hC hr2 φ hinj hρW hZ ha hJF hJa hJ hp hp2 h5 hJm
  obtain ⟨-, hKq, Ab, ψb, hAbu, hψb, hKt⟩ :=
    psu4_component_type hud hC hr2 φ hinj hρW hZ hb hKF hKb hK hp hp2 h5' hKm
  rcases hJt with ⟨hJq', -⟩ | ⟨hJq', -⟩ | ⟨hJq', hψaA, ⟨u, hu, hdetA⟩, φq, hφq, hφqJ⟩
  · rcases hKt with ⟨hKq', -⟩ | ⟨hKq', -⟩ | ⟨hKq', -⟩ <;>
      · rw [hpow, hJq'] at hKq'
        have h9 : 9 ≤ (r ^ e) ^ 2 := by nlinarith
        nlinarith
  · rcases hKt with ⟨hKq', -⟩ | ⟨hKq', -⟩ | ⟨hKq', -⟩ <;>
      · rw [hpow, hJq'] at hKq'
        have h9 : 9 ≤ (r ^ e) ^ 2 := by nlinarith
        nlinarith
  rcases hKt with ⟨hKq', hψbA, Q, l, hl0, hQ, hAQ⟩ | ⟨hKq', hψbA, hno⟩ | ⟨hKq', -⟩
  rotate_left
  ·
    have hJp : Group.IsPerfect J := hJq.1
    have hbJc := mem_centralizer_of_kernel hJp hJO hbJ
    set XJ := (J.subgroupOf (generalizedFitting H)).map φ.toMonoidHom with hXJ
    set θ : unitarySU r e Kf 4 →* StatedProj (StatedSU 4 (r ^ e) Kf) :=
      QuotientGroup.mk' (scal r e Kf) with hθ
    have hker : θ.ker ≤ center (unitarySU r e Kf 4) := by
      rw [hθ, QuotientGroup.ker_mk']
      intro z hz
      exact CatFactsL4U4.StabU.mem_center_of_mem_scal hz
    have hfix : ∀ y ∈ XJ, ρ b y = y := by
      rintro _ ⟨w, hw, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hρg]
      congr 1
      apply Subtype.ext
      change b * (w : H) * b⁻¹ = w
      rw [hbJc w (mem_subgroupOf.mp hw), mul_inv_cancel_right]
    have hψfix : ∀ g ∈ XJ.comap θ, θ (ψb g) = θ g := by
      intro g hg
      rw [hθ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← hψb]
      exact hfix _ hg
    have hXJp : ⁅XJ, XJ⁆ = XJ := by
      have : Group.IsPerfect (J.subgroupOf (generalizedFitting H)) :=
        Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJF).symm.toMonoidHom)
          (subgroupOfEquivOfLe hJF).symm.surjective
      have h1 := Subgroup.commutator_eq_self (H := J.subgroupOf (generalizedFitting H))
      rw [hXJ, ← Subgroup.map_commutator, h1]
    obtain ⟨hNp, -⟩ := commutator_comap_perfect θ (QuotientGroup.mk'_surjective _) hker hXJp
    have hfixN := eq_of_mem_commutator_comap θ hker ψb hψfix
    let φq' : QuaternionGroup 2 →* ↥(⁅XJ.comap θ, XJ.comap θ⁆ : Subgroup (unitarySU r e Kf 4)) :=
      φq.codRestrict _ hφqJ
    exact hno _ hNp hfixN φq' (fun x y hxy => hφq (congrArg Subtype.val hxy))
  ·
    rw [hpow, hJq'] at hKq'
    nlinarith
  have h5k : 5 ≤ Nat.card hud.fixedField := by rw [hud.card_fixedField, ← hJq']; exact h5
  obtain ⟨R, Y, hAR, hYY, -, ⟨s, hs⟩, hcomm, g₀, hg₀T, hg₀⟩ :=
    four_data hud hr2 h5k hAau hu hdetA hl0 hQ hAQ
  have hkey := mul_swap_of_conj hud hψaA hAR
  obtain ⟨x, hρx'⟩ : ∃ x : H, ρ x = ρ a * MulAut.conj (QuotientGroup.mk R) :=
    ⟨a * (φ.symm (QuotientGroup.mk R) : H), by rw [map_mul, hρW, MulEquiv.apply_symm_apply]⟩
  have hρx : ∀ g : unitarySU r e Kf 4,
      ρ x (QuotientGroup.mk g) = QuotientGroup.mk (ψa (R * g * R⁻¹)) := by
    intro g
    rw [hρx', MulAut.mul_apply, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hψa]
  have hext : ∀ α β : MulAut (StatedProj (StatedSU 4 (r ^ e) Kf)),
      (∀ g : unitarySU r e Kf 4, α (QuotientGroup.mk g) = β (QuotientGroup.mk g)) → α = β := by
    intro α β hαβ
    apply MulEquiv.ext
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact hαβ g
  have hx2 : x ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one, sq]
    apply hext
    intro g
    rw [MulAut.mul_apply, hρx, hρx, MulAut.one_apply]
    congr 1
    apply Catalog7U4.SU_ext
    exact eq_of_mul_swap_swap hYY (hkey g) (hkey _)
  have hxbc : x * b = b * x := by
    apply hinj
    refine (map_mul ρ x b).trans (Eq.trans ?_ (map_mul ρ b x).symm)
    apply hext
    intro g
    rw [MulAut.mul_apply, MulAut.mul_apply, hψb, hρx, hρx, hψb]
    congr 1
    apply Catalog7U4.SU_ext
    rw [hψbA]
    refine eq_of_mul_swap_conj hYY hs (hkey g) ?_
    rw [hkey, hψbA]
  have hKp : Group.IsPerfect K := hKq.1
  have hxK : ∀ z ∈ K, x * z = z * x := by
    set XK := (K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom with hXK
    have hXKp : ⁅XK, XK⁆ = XK := by
      have : Group.IsPerfect (K.subgroupOf (generalizedFitting H)) :=
        Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKF).symm.toMonoidHom)
          (subgroupOfEquivOfLe hKF).symm.surjective
      have h1 := Subgroup.commutator_eq_self (H := K.subgroupOf (generalizedFitting H))
      rw [hXK, ← Subgroup.map_commutator, h1]
    have hXKfix : ∀ g : unitarySU r e Kf 4,
        (QuotientGroup.mk g : StatedProj (StatedSU 4 (r ^ e) Kf)) ∈ XK →
        (QuotientGroup.mk (ψb g) : StatedProj (StatedSU 4 (r ^ e) Kf)) = QuotientGroup.mk g := by
      intro g hg
      rw [← hψb]
      obtain ⟨w', hw', hw'g⟩ := hg
      rw [← hw'g, MulEquiv.coe_toMonoidHom, hρg]
      congr 1
      apply Subtype.ext
      change b * (w' : H) * b⁻¹ = w'
      rw [show b * (w' : H) = (w' : H) * b from
        (mem_centralizer_singleton_iff.mp (hKb (mem_subgroupOf.mp hw'))).symm,
        mul_inv_cancel_right]
    have hgen := exists_mem_commutator_centT hψbA hXKp hXKfix
    intro z hz
    obtain ⟨g, hg, hgz⟩ := hgen (φ ⟨z, hKF hz⟩) ⟨⟨z, hKF hz⟩, mem_subgroupOf.mpr hz, rfl⟩
    have hfixz : ρ x (φ ⟨z, hKF hz⟩) = φ ⟨z, hKF hz⟩ := by
      rw [← hgz, hρx]
      congr 1
      apply Catalog7U4.SU_ext
      apply eq_of_mul_swap hYY
      rw [hkey, hcomm g hg]
    have h1 : ρ (x * z * x⁻¹) = ρ z := by
      have hz' : ρ z = MulAut.conj (φ ⟨z, hKF hz⟩) := hρW ⟨z, hKF hz⟩
      rw [map_mul, map_mul, map_inv, hz']
      ext t
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self,
        hfixz]
    have h2 := hinj h1
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h2]
  have hmove : ρ x (QuotientGroup.mk g₀) ≠ QuotientGroup.mk g₀ := by
    intro h1
    rw [hρx, QuotientGroup.eq] at h1
    obtain ⟨c, hc⟩ := CatFactsL4U4.StabU.val_of_mem_scal h1
    apply hg₀ (c : Kf)⁻¹
    have e : ((ψa (R * g₀ * R⁻¹) : GL (Fin 4) Kf) : Matrix (Fin 4) (Fin 4) Kf) *
        ((((ψa (R * g₀ * R⁻¹))⁻¹ * g₀ : unitarySU r e Kf 4) : GL (Fin 4) Kf) :
          Matrix (Fin 4) (Fin 4) Kf) = ((g₀ : GL (Fin 4) Kf) : Matrix (Fin 4) (Fin 4) Kf) := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [hc, Matrix.mul_smul, Matrix.mul_one] at e
    have e2 := hkey g₀
    rw [← e2]
    have hc0 : (c : Kf) ≠ 0 := c.ne_zero
    calc ((ψa (R * g₀ * R⁻¹) : GL (Fin 4) Kf) : Matrix (Fin 4) (Fin 4) Kf) * Y =
        (c : Kf)⁻¹ • (((g₀ : GL (Fin 4) Kf) : Matrix (Fin 4) (Fin 4) Kf) * Y) := by
          rw [← e, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = _ := rfl
  have hb1 : ρ b (QuotientGroup.mk g₀) = QuotientGroup.mk g₀ := by
    rw [hψb]
    congr 1
    apply Catalog7U4.SU_ext
    rw [hψbA]
    have hc' := congrArg (fun M : GL (Fin 4) Kf => (M : Matrix (Fin 4) (Fin 4) Kf))
      (mem_centT.mp hg₀T)
    simp only [Units.val_mul] at hc'
    rw [← hc', Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hmove
    rw [h1, map_one, MulAut.one_apply]
  have hxb : x ≠ b := by
    intro h1
    apply hmove
    rw [h1, hb1]
  exact Catalog7L4M.false_of_four_group hb hx2 hx1 hxb hxbc hKb hxK hsyl

end Catalog7L4EU

namespace Catalog7Std

theorem l4EpsInput : L4EpsInput := by
  intro H _ _ hsimp hC r e hr hr2 he hm a b ha hb _ J K hJF hKF hJa hJ hKb hK _ hsyl hbJ p f
    hp hp2 _ h5 hJm hKm
  rcases hm with hm | hm
  · exact Catalog7L4M.false_of_psl4 hC hr hr2 he hm ha hb hJF hKF hJa hJ hKb hK hsyl hbJ hp hp2
      h5 hJm hKm
  · exact Catalog7L4EU.false_of_psu4 hsimp hC hr hr2 he hm ha hb hJF hKF hJa hJ hKb hK hsyl hbJ
      hp hp2 h5 hJm hKm

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
