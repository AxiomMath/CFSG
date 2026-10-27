module

public import CFSG.CGT.Stroth77.Section43Gold
public import CFSG.CGT.Stroth77.Section43ZStar
public import CFSG.CGT.Stroth77.Section47ScGen
public import CFSG.CGT.Stroth77.Section47ScInvCore

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core

variable {G : Type} [Group G] [Finite G]

theorem H47GeneratorFusion_proved : H47GeneratorFusion := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel g hg hy
  obtain ⟨p, hrelp⟩ : ∃ p, Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p :=
    hrel.elim (fun h => ⟨1, h⟩) (fun h => ⟨3, h⟩)
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set X := Subgroup.centralizer ({z} : Set G) with hX
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDT : D ≤ H47C_S F dD := fun d hd => Subgroup.mem_inf.2
    ⟨h.le_S hd, Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)⟩
  have hTX : H47C_S F dD ≤ X := inf_le_right
  have hsq := t200inv_mul_self_mem dD hm hrelp
  have hJ := t200inv_conj_sq dD hm hrelp
  have hK := t200inv_conj_inv dD hm hrelp
  rw [← hS] at hsq hJ hK
  have hinD := H47ConjInD_of_normalizer H47Normalizer_proved (H47SylowControl_of_h9 H47H9_proved)
    (H47WeakClosure_of_h9 H47H9_proved) F hm dD h hSN hnc e he hS hrel
  have hext : ∀ g ∈ X, g⁻¹ * c₂ * g ∈ H47C_S F dD → ∃ k ∈ X,
      (k⁻¹ * (g⁻¹ * c₂ * g) * k = c₂ ∨ k⁻¹ * (g⁻¹ * c₂ * g) * k = c₂⁻¹) ∧
        ∀ s ∈ H47C_S F dD, s * (g⁻¹ * c₂ * g) = (g⁻¹ * c₂ * g) * s →
          k⁻¹ * s * k ∈ H47C_S F dD := by
    intro g hg hgT
    obtain ⟨k, hkX, hk1, hkS⟩ := H47Extremal_proved F hm dD h hSN hnc e he hS hrel g hg hgT
    exact ⟨k, hkX, hk1, fun s hs hsy => Subgroup.mem_inf.2
      ⟨hkS s hs hsy, X.mul_mem (X.mul_mem (X.inv_mem hkX) (hTX hs)) hkX⟩⟩
  have hgen := Stroth47Sc.conj_c₂_eq_of_extremal hTX hDT hc₂D (H47_c₂_sq dD hm)
    (Stroth47Fus.t200_c₁_mul_self dD hm1) (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx)
    hinD hext (fun s hs hsc => hsq s hs hsc) (fun y hy hyD hyc _ => hJ y hy hyD hyc)
    (fun y hy hyc _ => hK y hy hyc) g hg hy
  rcases hgen with h1 | h1
  · rw [h1]; exact Subgroup.mem_zpowers c₂
  · rw [h1]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c₂)

theorem H47StrongClosure_proved : H47StrongClosure :=
  H47StrongClosure_of_generator H47GeneratorFusion_proved

theorem stroth_4_7_inv_conj_notMem :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧ ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      g⁻¹ * e * g ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  intro G _ _ F D m hm dD h hN hnc e he hS hrel g hg hmem
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set X := Subgroup.centralizer ({z} : Set G) with hX
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDX : D ≤ X := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have he_sq : e * e = z := by rcases hrel with hrel | hrel <;> exact hrel.e_sq
  have hc_conj : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ := by
    rcases hrel with hrel | hrel <;> exact hrel.c_conj
  have heX : e ∈ X := by
    rw [hX]
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← he_sq, mul_assoc])
  obtain ⟨T, hT⟩ := Stroth43Gold.exists_sylow_centralizer_eq F.S (w := z)
    fun {Q} hQ hQz => H47SylowControl_of_h9 H47H9_proved F hm dD h hN hnc e he hS hrel Q hQ hQz
  set a : ↥X := ⟨c₂, hDX hc₂D⟩ with ha
  set e' : ↥X := ⟨e, heX⟩ with he'
  set g' : ↥X := ⟨g, hg⟩ with hg'
  have hc₂sq : c₂ * c₂ = z := H47_c₂_sq dD hm
  have hz2 : z * z = 1 := Stroth47Fus.t200_c₁_mul_self dD hm1
  have hz1 : z ≠ 1 := Stroth47Fus.t200_c₁_ne_one dD hm1
  have hc₂sq' : c₂ ^ 2 = z := by rw [pow_two]; exact hc₂sq
  have ha4 : a ^ 4 = 1 := by
    apply Subtype.ext
    change c₂ ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc₂sq', pow_two]
    exact hz2
  have ha2 : a ^ 2 ≠ 1 := by
    intro h1
    apply hz1
    have h2 := congrArg Subtype.val h1
    simpa [ha, Subgroup.coe_pow, hc₂sq, pow_two] using h2
  have hzc : ∀ x : ↥X, x * a ^ 2 = a ^ 2 * x := by
    intro x
    apply Subtype.ext
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    simpa [ha, hc₂sq'] using hx
  have hsc : ∀ g' : ↥X, g'⁻¹ * a * g' ∈ (T : Subgroup ↥X) →
      g'⁻¹ * a * g' ∈ Subgroup.zpowers a := by
    intro g' hg'T
    have hmemS : (g' : G)⁻¹ * c₂ * (g' : G) ∈ (F.S : Subgroup G) := by
      have h := (hT (g'⁻¹ * a * g')).1 hg'T
      simpa using h
    have hmemX : (g' : G)⁻¹ * c₂ * (g' : G) ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem g'.2) (hDX hc₂D)) g'.2
    have hscG := H47StrongClosure_proved F hm dD h hN hnc e he hS hrel c₂
      (Subgroup.mem_zpowers c₂) (g' : G) g'.2 (Subgroup.mem_inf.2 ⟨hmemS, hmemX⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hscG
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨j, Subtype.ext (by simpa [Subgroup.coe_zpow] using hj)⟩
  have hea : e'⁻¹ * a * e' = a⁻¹ := by
    apply Subtype.ext
    change e⁻¹ * c₂ * e = c₂⁻¹
    rw [hc₂, ← Stroth43Sc.conj_pow_eq, hc_conj, inv_pow]
  have hmem' : (g'⁻¹ * e' * g' : G) ∈
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓ X :=
    Subgroup.mem_inf.2 ⟨hmem, (g'⁻¹ * e' * g').2⟩
  obtain ⟨v, l, hv⟩ := Stroth47Core.t200_mem_CSc₁ dD hm1 hmem'
  have hofD : dD.ofTorus v ∈ D := dD.ofTorus_mem v
  have huc₂ : dD.u * c₂ = c₂ * dD.u := by
    rw [hc₂]
    exact (Commute.pow_right (Stroth47Core.t200_u_mul_c dD) _).eq
  have hcomm_c₂ : (g'⁻¹ * e' * g' : G) * c₂ = c₂ * (g'⁻¹ * e' * g' : G) := by
    rw [hv]
    cases l
    · simp only [dD.d8_fff, mul_one]
      exact hcommD _ hofD _ hc₂D
    · simp only [dD.d8_fft]
      calc (dD.ofTorus v * dD.u) * c₂ = dD.ofTorus v * (dD.u * c₂) := by group
        _ = dD.ofTorus v * (c₂ * dD.u) := by rw [huc₂]
        _ = (dD.ofTorus v * c₂) * dD.u := by group
        _ = (c₂ * dD.ofTorus v) * dD.u := by rw [hcommD _ hofD _ hc₂D]
        _ = c₂ * (dD.ofTorus v * dD.u) := by group
  have hg_comm : g'⁻¹ * e' * g' * a = a * (g'⁻¹ * e' * g') := by
    apply Subtype.ext
    change (g'⁻¹ * e' * g' : G) * c₂ = c₂ * (g'⁻¹ * e' * g' : G)
    exact hcomm_c₂
  exact Stroth43ZStar.false_of_cyclic_four_of_central T ha4 ha2 hzc hsc hea hg_comm

end CFSG.CGT.Stroth77
