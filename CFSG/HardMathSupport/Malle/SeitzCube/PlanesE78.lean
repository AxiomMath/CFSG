module

public import CFSG.HardMathSupport.Malle.SeitzCube.E8CubeAll
public import CFSG.HardMathSupport.Malle.SeitzCube.E7ThreeCube
public import CFSG.LieType.SeitzGeneration.ExcPlaneSplit
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge CFSG.HardMathSupport.Malle.Proving

theorem exists_innerPlane_of_cube {C : Type*} [Group C] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {E R : Subgroup C}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hN : ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R) :
    ∃ A : Subgroup (MulAut C), IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      A ≤ (MulAut.conj : C →* MulAut C).range ∧ ∀ ε ∈ A, R.map ε.toMonoidHom = R := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
    (by rw [hc]; exact pow_dvd_pow p (by norm_num))
  set E₀ : Subgroup C := K₀.map E.subtype with hE₀
  have hE₀E : E₀ ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE₀ab : IsElemAbelian p E₀ := by
    obtain ⟨hEc, hEp⟩ := hE
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hEp x (hE₀E hx)⟩
    show a.1 * b.1 = b.1 * a.1
    exact congrArg Subtype.val (hEc.is_comm.comm ⟨a.1, hE₀E a.2⟩ ⟨b.1, hE₀E b.2⟩)
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective Subtype.val_injective, hK₀]
  have hn : E₀ ≤ Subgroup.normalizer (R : Set C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' := hN x (hE₀E hx)
    constructor
    · intro hy
      rw [← hx']
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hx'] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by
        have h := congrArg (fun t => x⁻¹ * t * x) hzy
        simpa [MulAut.conj_apply, mul_assoc] using h
      rwa [← this]
  exact exists_plane_of_subgroup hinj hE₀ab hE₀c hn

theorem plane_of_cube {d : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (h : ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ NormalizesRSub d E) :
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ NormalizesRSubgroup d E := by
  obtain ⟨E, hE, hc, R, hR, hRp, hN⟩ := h
  obtain ⟨A, hA, hAc, hAin, hAN⟩ := exists_innerPlane_of_cube hp hinj hE hc hN
  exact ⟨A, hA, hAc, hAin, R, hR, hRp, hAN⟩

theorem ne_three_of_dvd_sq_add_add_one {p q : ℕ} (hnd : ¬ p ∣ q ^ 2 - 1)
    (h : p ∣ q ^ 2 + q + 1) : p ≠ 3 := by
  rintro rfl
  apply hnd
  have h3 : q % 3 = 1 := by
    have := (Nat.dvd_iff_mod_eq_zero ..).1 h
    have : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    · exfalso
      have : (q ^ 2 + q + 1) % 3 = 1 := by
        rw [Nat.add_mod, Nat.add_mod (q ^ 2), Nat.pow_mod, h0]
      omega
    · exact h1
    · exfalso
      have : (q ^ 2 + q + 1) % 3 = 1 := by
        rw [Nat.add_mod, Nat.add_mod (q ^ 2), Nat.pow_mod, h2]
      omega
  have hq : 1 ≤ q := by omega
  have : (q ^ 2 - 1) % 3 = 0 := by
    have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
    omega
  exact Nat.dvd_of_mod_eq_zero this

theorem ne_three_of_dvd_sq_sub_add_one {p q : ℕ} (hnd : ¬ p ∣ q ^ 2 - 1)
    (h : p ∣ q ^ 2 - q + 1) : p ≠ 3 := by
  rintro rfl
  apply hnd
  have hle : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have h3 : q % 3 = 2 := by
    have := (Nat.dvd_iff_mod_eq_zero ..).1 h
    have hq2 : q ^ 2 = q * q := by ring
    have : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    · exfalso
      have hsq : q ^ 2 % 3 = 0 := by rw [Nat.pow_mod, h0]
      omega
    · exfalso
      have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h1]
      omega
    · exact h2
  have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
  have hq : 1 ≤ q := by omega
  exact Nat.dvd_of_mod_eq_zero (by omega)

section Planes


theorem conj_injective_cat_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨TauCeti.LieTypeIndex.E8 q, hv⟩ →*
      MulAut (Cat ⟨TauCeti.LieTypeIndex.E8 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot)

theorem conj_injective_cat_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨TauCeti.LieTypeIndex.E7 q, hv⟩ →*
      MulAut (Cat ⟨TauCeti.LieTypeIndex.E7 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot)

theorem exists_cube_cat_E8_of_family {P : ℕ → ℕ → Prop} (hT : TwistedCubeE8 P)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime)
    (hP : P q.card p) :
    ∃ E : Subgroup (Cat ⟨TauCeti.LieTypeIndex.E8 q, hv⟩), IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧ NormalizesRSub ⟨TauCeti.LieTypeIndex.E8 q, hv⟩ E :=
  exists_cube_cat_E8_of_twisted q hv fun K _ _ hK hKc L _ _ _ Fr hFr => by
    have hT' := hT K L Fr (fun c => by rw [hFr, hK]) p hp (by rwa [hK])
    rwa [ringChar.eq K q.p] at hT'

theorem excPlaneE8E3_proved : ExcPlaneE8E3 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hnd, hdvd⟩ hr
  exact plane_of_cube hp (conj_injective_cat_E8 q hv) (exists_cube_cat_E8_of_family
    twistedCubeE8_three q hv hp ⟨ne_three_of_dvd_sq_add_add_one hnd hdvd, hdvd⟩)

theorem excPlaneE8E4_proved : ExcPlaneE8E4 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hnd, hdvd⟩ hr
  exact plane_of_cube hp (conj_injective_cat_E8 q hv)
    (exists_cube_cat_E8_of_family twistedCubeE8_four q hv hp ⟨hp2, hdvd⟩)

theorem excPlaneE8E6_proved : ExcPlaneE8E6 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hnd, hdvd⟩ hr
  exact plane_of_cube hp (conj_injective_cat_E8 q hv) (exists_cube_cat_E8_of_family
    twistedCubeE8_six q hv hp ⟨ne_three_of_dvd_sq_sub_add_one hnd hdvd, hdvd⟩)

theorem excPlaneE7E3_proved : ExcPlaneE7E3 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hnd, hdvd⟩ hr
  refine plane_of_cube hp (conj_injective_cat_E7 q hv)
    (exists_cube_cat_E7_of_twisted q hv hp hp2 fun K _ _ hK hKc L _ _ _ Fr hFr => ?_)
  have hT := twistedCubeE7_three K L Fr (fun c => by rw [hFr, hK]) p hp hp2
    (by rw [hK]; exact orderOf_eq_three_of_dvd hp (ne_three_of_dvd_sq_add_add_one hnd hdvd) hdvd)
  rwa [ringChar.eq K q.p] at hT

end Planes

end CFSG.HardMathSupport.Malle.SeitzCube
