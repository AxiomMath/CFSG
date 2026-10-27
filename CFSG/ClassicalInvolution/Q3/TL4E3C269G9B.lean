module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269G9A
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3C269G9

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem eq_m10_of_q8 {B : Subgroup P10} (hBA : B ≤ A6Models.autA6) (hpsl : A6Models.psl29 ≤ B)
    (hcard : Nat.card B ≤ 720) {a b z : P10} (ha : a ∈ B) (hb : b ∈ B)
    (hz : z ∈ A6Models.psl29) (hz2 : z * z = 1) (hz1 : z ≠ 1) (haa : a * a = z) (hbb : b * b = z)
    (hab : a * b * a = b) : B = A6Models.m10 := by
  obtain ⟨h, hh, hhz⟩ := psl29_conj_zb hz hz2 hz1
  have hconj : ∀ x ∈ B, h * x * h⁻¹ ∈ B := fun x hx =>
    mul_mem (mul_mem (hpsl hh) hx) (inv_mem (hpsl hh))
  have hsq : ∀ x : P10, x * x = z → h * x * h⁻¹ * (h * x * h⁻¹) = zb := fun x hx => by
    rw [← hhz, ← hx]
    group
  have hcomm : ∀ x : P10, x * x = z → h * x * h⁻¹ * zb = zb * (h * x * h⁻¹) := fun x hx => by
    rw [← hsq x hx]
    group
  have hP0 : ∀ x ∈ B, x * x = z → h * x * h⁻¹ ∈ P0 := fun x hx hxx =>
    centralizer_le_P0_of_central zb_mem_P0 zb_ne_one zb_central (hBA (hconj x hx))
      (hcomm x hxx)
  have hab' : h * a * h⁻¹ * (h * b * h⁻¹) * (h * a * h⁻¹) = h * b * h⁻¹ := by
    calc h * a * h⁻¹ * (h * b * h⁻¹) * (h * a * h⁻¹) = h * (a * b * a) * h⁻¹ := by group
      _ = h * b * h⁻¹ := by rw [hab]
  obtain ⟨hs6, hpgl⟩ := not_mem_s6_pgl29_of_q8 (hP0 a ha haa) (hP0 b hb hbb) (hsq a haa)
    (hsq b hbb) hab'
  have hσ : ∃ σ ∈ B, σ ∉ s6 := by
    by_cases has : h * a * h⁻¹ ∈ s6
    · exact ⟨h * b * h⁻¹, hconj b hb, fun hbs => hs6 ⟨has, hbs⟩⟩
    · exact ⟨h * a * h⁻¹, hconj a ha, has⟩
  rcases Unc25K1.A6Model.classify B hBA hpsl hσ with hB | hB | hB
  · exact (hpgl ⟨by rw [← hB]; exact hconj a ha, by rw [← hB]; exact hconj b hb⟩).elim
  · exact hB
  · rw [hB, card_autA6] at hcard
    omega

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem nonempty_mulEquiv_m10_of_quat (N : Subgroup X) [N.Normal]
    (hC : Subgroup.centralizer (N : Set X) ≤ N) (hidx : N.index ≤ 2)
    (φ : ↥N ≃* ↥A6Models.psl29) {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι)
    (htN : ι (QuaternionGroup.a 2) ∈ N) : Nonempty (X ≃* ↥A6Models.m10) := by
  classical
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hc : ∀ m ∈ N, x * m = m * x := by
      intro m hm
      have h := congrArg (fun f : MulAut N => ((f ⟨m, hm⟩ : N) : X)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc x * m = x * m * x⁻¹ * x := by group
        _ = m * x := by rw [h]
    have hxN : x ∈ N := hC (Subgroup.mem_centralizer_iff.mpr fun m hm => (hc m hm).symm)
    have h1 : ((φ ⟨x, hxN⟩ : A6Models.psl29) : P10) = 1 := by
      refine centralizer_psl29 (psl29_le_autA6 (φ _).2) fun y hy => ?_
      obtain ⟨m, hm⟩ := φ.surjective ⟨y, hy⟩
      have h2 : (⟨x, hxN⟩ : N) * m = m * ⟨x, hxN⟩ := Subtype.ext (hc m m.2)
      have h3 := congrArg (fun n : N => ((φ n : A6Models.psl29) : P10)) h2
      simp only [map_mul, Subgroup.coe_mul, hm] at h3
      exact h3
    have h4 : φ ⟨x, hxN⟩ = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ φ.injective] at h4
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h4)
  set Θ := Unc25K1.A6Model.thetaEquiv φ
  let θ : X →* A6Models.autA6 := Θ.toMonoidHom.comp MulAut.conjNormal
  have hθ : Function.Injective θ := Θ.injective.comp hinj
  have hθN : ∀ n : N, ((θ n : A6Models.autA6) : P10) = ((φ n : A6Models.psl29) : P10) := by
    intro n
    have h := Unc25K1.A6Model.thetaEquiv_eq φ (MulAut.conjNormal (n : X))
      ⟨φ n, psl29_le_autA6 (φ n).2⟩ (fun k => by
        have hk : (MulAut.conjNormal (n : X)) k = n * k * n⁻¹ :=
          Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
        rw [hk, map_mul, map_mul, map_inv]
        rfl)
    exact congrArg Subtype.val h
  let Bm : Subgroup P10 := θ.range.map A6Models.autA6.subtype
  have hBA : Bm ≤ A6Models.autA6 := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hmem : ∀ x : X, ((θ x : A6Models.autA6) : P10) ∈ Bm :=
    fun x => ⟨θ x, ⟨x, rfl⟩, rfl⟩
  have hpsl : A6Models.psl29 ≤ Bm := by
    intro y hy
    have h := hmem (φ.symm ⟨y, hy⟩ : X)
    rw [hθN, MulEquiv.apply_symm_apply] at h
    exact h
  have hcardB : Nat.card Bm ≤ 720 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      ← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, ← Subgroup.card_mul_index N,
      Nat.card_congr φ.toEquiv, card_psl29]
    omega
  have key : ∀ u v w : QuaternionGroup 2, u * v = w →
      ((θ (ι u) : A6Models.autA6) : P10) * ((θ (ι v) : A6Models.autA6) : P10) =
        ((θ (ι w) : A6Models.autA6) : P10) := by
    intro u v w h
    rw [← h, map_mul, map_mul, Subgroup.coe_mul]
  have hz : ((θ (ι (QuaternionGroup.a 2)) : A6Models.autA6) : P10) ∈ A6Models.psl29 := by
    show ((θ ((⟨_, htN⟩ : N) : X) : A6Models.autA6) : P10) ∈ A6Models.psl29
    rw [hθN]
    exact (φ _).2
  have hz1 : ((θ (ι (QuaternionGroup.a 2)) : A6Models.autA6) : P10) ≠ 1 := by
    intro h
    have h1 : θ (ι (QuaternionGroup.a 2)) = θ (ι 1) := by
      rw [map_one, map_one]
      exact Subtype.ext h
    exact absurd (hι (hθ h1)) (by decide)
  have hz2 := key _ _ _ (show QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2)
    by decide)
  rw [map_one, map_one, Subgroup.coe_one] at hz2
  have hBm : Bm = A6Models.m10 := eq_m10_of_q8 hBA hpsl hcardB
    (hmem (ι (QuaternionGroup.a 1))) (hmem (ι (QuaternionGroup.xa 0))) hz hz2 hz1
    (key _ _ _ (show QuaternionGroup.a 1 * QuaternionGroup.a 1 = QuaternionGroup.a (n := 2) 2
      by decide))
    (key _ _ _ (show QuaternionGroup.xa 0 * QuaternionGroup.xa 0 = QuaternionGroup.a (n := 2) 2
      by decide))
    (by rw [key _ _ _ (show QuaternionGroup.a 1 * QuaternionGroup.xa 0 = QuaternionGroup.xa
        (n := 2) 3 by decide), key _ _ _ (show QuaternionGroup.xa 3 * QuaternionGroup.a 1 =
          QuaternionGroup.xa (n := 2) 0 by decide)])
  exact ⟨((MonoidHom.ofInjective hθ).trans (Subgroup.equivMapOfInjective θ.range
    A6Models.autA6.subtype Subtype.val_injective)).trans (MulEquiv.subgroupCongr hBm)⟩

theorem sup_centralizer_m10 {T S : ↥A6Models.m10} (hT2 : T * T = 1) (hT1 : T ≠ 1)
    (hTS : T * S = S * T) (hST : S ≠ T) (hconj : ∃ g, S = g * T * g⁻¹) :
    Subgroup.centralizer ({T} : Set ↥A6Models.m10) ⊔
      Subgroup.centralizer ({S} : Set ↥A6Models.m10) = ⊤ := by
  have hTv2 : (T : P10) * T = 1 := congrArg Subtype.val hT2
  have hTv1 : (T : P10) ≠ 1 := fun h => hT1 (Subtype.ext h)
  obtain ⟨h, hh, hhT⟩ :=
    psl29_conj_zb (Out21.A6.m10_involution_mem_psl29 T.2 hTv2) hTv2 hTv1
  have hzm : zb ∈ A6Models.m10 := Out21.A6.psl29_le_m10 zb_mem_psl29
  set H : ↥A6Models.m10 := ⟨h, Out21.A6.psl29_le_m10 hh⟩ with hH
  have hHT : H * T * H⁻¹ = ⟨zb, hzm⟩ := Subtype.ext hhT
  refine E3C269G.sup_centralizer_eq_top_of_equiv (MulAut.conj H) ?_
  rw [MulAut.conj_apply, MulAut.conj_apply, hHT]
  obtain ⟨g, rfl⟩ := hconj
  have hS2 : H * (g * T * g⁻¹) * H⁻¹ * (H * (g * T * g⁻¹) * H⁻¹) = 1 := by
    calc H * (g * T * g⁻¹) * H⁻¹ * (H * (g * T * g⁻¹) * H⁻¹) = H * g * (T * T) * g⁻¹ * H⁻¹ := by
          group
      _ = 1 := by rw [hT2]; group
  have hS1 : H * (g * T * g⁻¹) * H⁻¹ ≠ 1 := fun h1 => hT1 (by
    calc T = g⁻¹ * H⁻¹ * (H * (g * T * g⁻¹) * H⁻¹) * H * g := by group
      _ = 1 := by rw [h1]; group)
  have hSz : H * (g * T * g⁻¹) * H⁻¹ ≠ ⟨zb, hzm⟩ := fun h1 => hST (by
    rw [← hHT] at h1
    calc g * T * g⁻¹ = H⁻¹ * (H * (g * T * g⁻¹) * H⁻¹) * H := by group
      _ = T := by rw [h1]; group)
  have hSc : H * (g * T * g⁻¹) * H⁻¹ * ⟨zb, hzm⟩ = ⟨zb, hzm⟩ * (H * (g * T * g⁻¹) * H⁻¹) := by
    rw [← hHT]
    calc H * (g * T * g⁻¹) * H⁻¹ * (H * T * H⁻¹) = H * ((g * T * g⁻¹) * T) * H⁻¹ := by group
      _ = H * (T * (g * T * g⁻¹)) * H⁻¹ := by rw [hTS]
      _ = H * T * H⁻¹ * (H * (g * T * g⁻¹) * H⁻¹) := by group
  set S₁ := H * (g * T * g⁻¹) * H⁻¹ with hS₁
  have hS₁P : (S₁ : P10) ∈ P0 :=
    centralizer_le_P0_of_central zb_mem_P0 zb_ne_one zb_central (m10_le_autA6 S₁.2)
      (congrArg Subtype.val hSc)
  obtain ⟨c, hc, hcS⟩ := exists_conj_s0 (Subgroup.mem_inf.mpr ⟨hS₁P, S₁.2⟩)
    (congrArg Subtype.val hS2)
    (fun h1 => hS1 (Subtype.ext h1)) (fun h1 => hSz (Subtype.ext h1))
  obtain ⟨hcP, hcm⟩ := Subgroup.mem_inf.mp hc
  have hcz : (⟨c, hcm⟩ : ↥A6Models.m10) * ⟨zb, hzm⟩ = ⟨zb, hzm⟩ * ⟨c, hcm⟩ :=
    Subtype.ext (zb_central c hcP).symm
  refine E3C269G.sup_centralizer_eq_top_of_conj hcz ?_
  have hcS' : (⟨c, hcm⟩ : ↥A6Models.m10) * S₁ * (⟨c, hcm⟩ : ↥A6Models.m10)⁻¹ =
      ⟨s0, s0_mem_m10⟩ := Subtype.ext hcS
  rw [hcS']
  exact sup_centralizer_zb_s0 hzm s0_mem_m10

end CFSG.ClassicalInvolution.Q3.TL4.E3C269G9
