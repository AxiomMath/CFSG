module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL7V8Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerDQuot
public import CFSG.LinearAlgebra.TransvectionFixedExtension
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerV

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private noncomputable def conjMulAut (K : Subgroup G) {n : G}
    (hn : n ∈ normalizer (K : Set G)) : MulAut ↥K where
  toFun k := ⟨n * (k : G) * n⁻¹, (mem_normalizer_iff.1 hn (k : G)).1 k.2⟩
  invFun k := ⟨n⁻¹ * (k : G) * n,
    by simpa using (mem_normalizer_iff.1 ((normalizer (K : Set G)).inv_mem hn) (k : G)).1 k.2⟩
  left_inv k := by ext; group
  right_inv k := by ext; group
  map_mul' k l := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

omit [Finite G] in
private theorem conjMulAut_apply (K : Subgroup G) {n : G}
    (hn : n ∈ normalizer (K : Set G)) (k : ↥K) :
    ((conjMulAut K hn k : ↥K) : G) = n * (k : G) * n⁻¹ := rfl

omit [Finite G] in
private theorem conjMulAut_mul (K : Subgroup G) {m n : G}
    (hm : m ∈ normalizer (K : Set G)) (hn : n ∈ normalizer (K : Set G)) :
    conjMulAut K hm * conjMulAut K hn = conjMulAut K (mul_mem hm hn) := by
  apply MulEquiv.ext
  intro k
  apply Subtype.ext
  rw [MulAut.mul_apply, conjMulAut_apply, conjMulAut_apply, conjMulAut_apply]
  group

private noncomputable def mulAutToLin (α : Type) [CommGroup α]
    [Module (ZMod 2) (Additive α)] (f : MulAut α) :
    Additive α ≃ₗ[ZMod 2] Additive α :=
  (MulEquiv.toAdditive f).toLinearEquiv fun c x => ZMod.map_smul (MulEquiv.toAdditive f) c x

private theorem mulAutToLin_mul (α : Type) [CommGroup α]
    [Module (ZMod 2) (Additive α)] (f g : MulAut α) :
    mulAutToLin α (f * g) = mulAutToLin α f * mulAutToLin α g := by
  apply LinearEquiv.ext
  intro x
  rfl

theorem ThCyc.card_omega1_inf_centralizer_of_transvection (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    (hfix : Nat.card ↥(A ⊓ centralizer ({n} : Set G)) = 8) :
    Nat.card ↥(omega1 D hD.comm ⊓ centralizer ({n} : Set G)) = 2 ^ 6 := by
  classical
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  set V : Subgroup G := omega1 D hD.comm with hV
  have hAcomm : ∀ x y : ↥A, x * y = y * x := fun x y => Subtype.ext (W.A_comm x x.2 y y.2)
  have hVcomm : ∀ x y : ↥V, x * y = y * x := fun x y =>
    Subtype.ext (H.omega1_comm W W2 hD x.2 y.2)
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hAcomm }
  letI : CommGroup ↥V := { (inferInstance : Group ↥V) with mul_comm := hVcomm }
  have hAsq : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (by
    simpa [pow_two] using W.A_sq a a.2)
  have hVsq : ∀ v : ↥V, v * v = 1 := fun v => Subtype.ext (H.omega1_mul_self W W2 hD v.2)
  have hsmulA : ∀ x : Additive ↥A, (2 : ℕ) • x = 0 := by
    intro x
    apply (Additive.toMul (α := ↥A)).injective
    simp [pow_two, hAsq (Additive.toMul x)]
  have hsmulV : ∀ x : Additive ↥V, (2 : ℕ) • x = 0 := by
    intro x
    apply (Additive.toMul (α := ↥V)).injective
    simp [pow_two, hVsq (Additive.toMul x)]
  letI : Module (ZMod 2) (Additive ↥A) := AddCommGroup.zmodModule (n := 2) hsmulA
  letI : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule (n := 2) hsmulV
  haveI : Finite (Additive ↥A) := inferInstance
  haveI : Finite (Additive ↥V) := inferInstance
  have hfinrankA : Module.finrank (ZMod 2) (Additive ↥A) = 4 := by
    have hcard : Nat.card (Additive ↥A) = 2 ^ 4 := by
      rw [Nat.card_congr Additive.toMul, W.A_card]
      norm_num
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥A)
    rw [Nat.card_zmod, hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  let iotaAdd : Additive ↥A →+ Additive ↥V :=
    AddMonoidHom.mk'
      (fun a => Additive.ofMul
        ⟨(Additive.toMul a).1, H.A_le_omega1 W W2 hD (Additive.toMul a).2⟩)
      (fun a b => by
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl)
  let iota : Additive ↥A →ₗ[ZMod 2] Additive ↥V := iotaAdd.toZModLinearMap 2
  have iota_eq : ∀ a : Additive ↥A, iota a =
      Additive.ofMul ⟨(Additive.toMul a).1, H.A_le_omega1 W W2 hD (Additive.toMul a).2⟩ :=
    fun a => rfl
  let thetaAdd : Additive ↥V →+ Additive ↥A :=
    AddMonoidHom.mk'
      (fun v => Additive.ofMul
        ⟨thV t (Additive.toMul v).1, H.thV_mem_A W W2 hD (Additive.toMul v).2⟩)
      (fun v w => by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact H.thV_mul W W2 hD (Additive.toMul v).2 (Additive.toMul w).2)
  let theta : Additive ↥V →ₗ[ZMod 2] Additive ↥A := thetaAdd.toZModLinearMap 2
  have theta_eq : ∀ v : Additive ↥V, theta v =
      Additive.ofMul ⟨thV t (Additive.toMul v).1, H.thV_mem_A W W2 hD (Additive.toMul v).2⟩ :=
    fun v => rfl
  have hinj : Function.Injective iota := by
    intro a b hab
    have h : Additive.toMul a = Additive.toMul b := by
      apply Subtype.ext
      have h' := congrArg (fun z : Additive ↥V => ((Additive.toMul z : ↥V) : G)) hab
      simpa [iota_eq] using h'
    exact Additive.ext h
  have hrange : LinearMap.range iota = LinearMap.ker theta := by
    ext v
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨a, rfl⟩
      have h1 : thV t (Additive.toMul a).1 = 1 :=
        (H.thV_eq_one_iff W W2 hD (H.A_le_omega1 W W2 hD (Additive.toMul a).2)).2
          (Additive.toMul a).2
      apply Additive.ext
      apply Subtype.ext
      rw [theta_eq, iota_eq]
      simp only [toMul_ofMul]
      exact h1
    · intro hv
      have hvA : (Additive.toMul v).1 ∈ A := by
        refine (H.thV_eq_one_iff W W2 hD (Additive.toMul v).2).1 ?_
        have h' : ((Additive.toMul (theta v) : ↥A) : G) =
            ((Additive.toMul (0 : Additive ↥A) : ↥A) : G) :=
          congrArg (fun z : Additive ↥A => ((Additive.toMul z : ↥A) : G)) hv
        rw [theta_eq] at h'
        exact h'
      refine ⟨Additive.ofMul ⟨(Additive.toMul v).1, hvA⟩, ?_⟩
      apply Additive.ext
      apply Subtype.ext
      rw [iota_eq]
      rfl
  have hsurjTheta : Function.Surjective theta := by
    intro a
    obtain ⟨v, hv, hva⟩ := H.thV_surj W W2 hD hsq (Additive.toMul a).1 (Additive.toMul a).2
    refine ⟨Additive.ofMul ⟨v, hv⟩, ?_⟩
    apply Additive.ext
    apply Subtype.ext
    rw [theta_eq]
    exact hva
  have hnormInL : ∀ γ : ↥(L ⊓ normalizer (A : Set G)), (γ : G) ∈ normInL L A :=
    fun γ => ⟨γ.2.1, fun x hx => (mem_normalizer_iff.1 γ.2.2 x).1 hx⟩
  have hnormV : ∀ γ : ↥(L ⊓ normalizer (A : Set G)), (γ : G) ∈ normalizer (V : Set G) := by
    intro γ
    have h1 : (γ : G) ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
      H.mem_normalizer_W5_of_mem_normInL W W2 hD (hnormInL γ)
    exact normalizer_le_normalizer_omega1_of_comm hD.comm
      (SylowEnd.le_normalizer_of_conj_mem hD.norm h1)
  let pi : ↥(L ⊓ normalizer (A : Set G)) →* (Additive ↥A ≃ₗ[ZMod 2] Additive ↥A) :=
    MonoidHom.mk' (fun γ => mulAutToLin ↥A (conjMulAut A γ.2.2)) (fun γ δ => by
      have h1 : conjMulAut A ((γ * δ).2.2) = conjMulAut A γ.2.2 * conjMulAut A δ.2.2 :=
        (conjMulAut_mul A γ.2.2 δ.2.2).symm
      rw [h1, mulAutToLin_mul])
  have pi_eq : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (a : Additive ↥A),
      pi γ a = Additive.ofMul (conjMulAut A γ.2.2 (Additive.toMul a)) := fun γ a => rfl
  have pi_coe : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (a : Additive ↥A),
      ((Additive.toMul (pi γ a) : ↥A) : G) =
        (γ : G) * ((Additive.toMul a : ↥A) : G) * (γ : G)⁻¹ := by
    intro γ a
    have h := conjMulAut_apply A γ.2.2 (Additive.toMul a)
    simpa [pi_eq] using h
  let rho : ↥(L ⊓ normalizer (A : Set G)) →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    MonoidHom.mk' (fun γ => mulAutToLin ↥V (conjMulAut V (hnormV γ))) (fun γ δ => by
      have h1 : conjMulAut V (hnormV (γ * δ)) =
          conjMulAut V (hnormV γ) * conjMulAut V (hnormV δ) :=
        (conjMulAut_mul V (hnormV γ) (hnormV δ)).symm
      rw [h1, mulAutToLin_mul])
  have rho_eq : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (v : Additive ↥V),
      rho γ v = Additive.ofMul (conjMulAut V (hnormV γ) (Additive.toMul v)) := fun γ v => rfl
  have rho_coe : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (v : Additive ↥V),
      ((Additive.toMul (rho γ v) : ↥V) : G) =
        (γ : G) * ((Additive.toMul v : ↥V) : G) * (γ : G)⁻¹ := by
    intro γ v
    have h := conjMulAut_apply V (hnormV γ) (Additive.toMul v)
    simpa [rho_eq] using h
  have rho_iota_coe : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (a : Additive ↥A),
      ((Additive.toMul (rho γ (iota a)) : ↥V) : G) =
        (γ : G) * ((Additive.toMul a : ↥A) : G) * (γ : G)⁻¹ := by
    intro γ a
    rw [rho_coe, iota_eq]
    simp only [toMul_ofMul]
  have iota_pi_coe : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (a : Additive ↥A),
      ((Additive.toMul (iota (pi γ a)) : ↥V) : G) =
        (γ : G) * ((Additive.toMul a : ↥A) : G) * (γ : G)⁻¹ := by
    intro γ a
    rw [iota_eq]
    simp only [toMul_ofMul]
    rw [pi_coe]
  have hρι : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (a : Additive ↥A),
      rho γ (iota a) = iota (pi γ a) := by
    intro γ a
    apply Additive.ext
    apply Subtype.ext
    calc ((Additive.toMul (rho γ (iota a)) : ↥V) : G)
        = (γ : G) * ((Additive.toMul a : ↥A) : G) * (γ : G)⁻¹ := rho_iota_coe γ a
      _ = ((Additive.toMul (iota (pi γ a)) : ↥V) : G) := (iota_pi_coe γ a).symm
  have theta_rho_coe : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (v : Additive ↥V),
      ((Additive.toMul (theta (rho γ v)) : ↥A) : G) =
        thV t ((γ : G) * ((Additive.toMul v : ↥V) : G) * (γ : G)⁻¹) := by
    intro γ v
    rw [theta_eq]
    simp only [toMul_ofMul]
    rw [rho_coe]
  have pi_theta_coe : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (v : Additive ↥V),
      ((Additive.toMul (pi γ (theta v)) : ↥A) : G) =
        (γ : G) * thV t ((Additive.toMul v : ↥V) : G) * (γ : G)⁻¹ := by
    intro γ v
    rw [pi_coe, theta_eq]
    simp only [toMul_ofMul]
  have hθρ : ∀ (γ : ↥(L ⊓ normalizer (A : Set G))) (v : Additive ↥V),
      theta (rho γ v) = pi γ (theta v) := by
    intro γ v
    apply Additive.ext
    apply Subtype.ext
    calc ((Additive.toMul (theta (rho γ v)) : ↥A) : G)
        = thV t ((γ : G) * ((Additive.toMul v : ↥V) : G) * (γ : G)⁻¹) := theta_rho_coe γ v
      _ = (γ : G) * thV t ((Additive.toMul v : ↥V) : G) * (γ : G)⁻¹ := H.thV_conj W W2 hD γ.2.1
      _ = ((Additive.toMul (pi γ (theta v)) : ↥A) : G) := (pi_theta_coe γ v).symm
  have hker : ∀ γ : ↥(L ⊓ normalizer (A : Set G)), pi γ = 1 → rho γ = 1 := by
    intro γ hγ
    have hfixA : ∀ a : ↥A, (γ : G) * (a : G) * (γ : G)⁻¹ = (a : G) := by
      intro a
      have h' : pi γ (Additive.ofMul a) = Additive.ofMul a := by
        rw [hγ]
        rfl
      have h2 : conjMulAut A γ.2.2 a = a := by
        have h3 := congrArg Additive.toMul h'
        simpa [pi_eq] using h3
      calc (γ : G) * (a : G) * (γ : G)⁻¹ = ((conjMulAut A γ.2.2 a : ↥A) : G) :=
            (conjMulAut_apply A γ.2.2 a).symm
        _ = (a : G) := congrArg Subtype.val h2
    have hγB : (γ : G) ∈ B := (W.mem_B_iff (γ : G) γ.2.1).2 fun a ha =>
      mul_inv_eq_iff_eq_mul.mp (hfixA ⟨a, ha⟩)
    apply LinearEquiv.ext
    intro v
    apply Additive.ext
    apply Subtype.ext
    calc ((Additive.toMul (rho γ v) : ↥V) : G)
        = (γ : G) * ((Additive.toMul v : ↥V) : G) * (γ : G)⁻¹ := rho_coe γ v
      _ = ((Additive.toMul v : ↥V) : G) :=
          H.comm_omega1_of_mem_B W W2 hD hb hγB (Additive.toMul v).2
  have hpi_surj : Function.Surjective pi := by
    intro e
    let eM : ↥A ≃* ↥A :=
      (MulEquiv.toAdditive (G := ↥A) (H := ↥A)).symm e.toAddEquiv
    have heM : ∀ a : ↥A, eM a = Additive.toMul (e (Additive.ofMul a)) := fun a => rfl
    let f : G → G := fun y => if hy : y ∈ A then ((eM ⟨y, hy⟩ : ↥A) : G) else 1
    have hf : ∀ (a : G) (ha : a ∈ A), f a = ((eM ⟨a, ha⟩ : ↥A) : G) := fun a ha => dif_pos ha
    have hfA : ∀ a ∈ A, f a ∈ A := by
      intro a ha
      rw [hf a ha]
      exact (eM ⟨a, ha⟩).2
    have hfM : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
      intro a ha b hb
      rw [hf (a * b) (A.mul_mem ha hb), hf a ha, hf b hb]
      rw [show (⟨a * b, A.mul_mem ha hb⟩ : ↥A) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
      rfl
    have hfI : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
      intro a ha b hb hab
      rw [hf a ha, hf b hb] at hab
      have h2 : eM ⟨a, ha⟩ = eM ⟨b, hb⟩ := Subtype.ext hab
      exact congrArg Subtype.val (eM.injective h2)
    obtain ⟨n', hn'L, hn'A⟩ := W.surj f hfA hfM hfI
    have hn'N : n' ∈ normalizer (A : Set G) := by
      have hle : A.map (MulAut.conj n').toMonoidHom ≤ A := by
        rintro - ⟨x, hx, rfl⟩
        change (MulAut.conj n') x ∈ A
        rw [MulAut.conj_apply, hn'A x hx]
        exact hfA x hx
      refine mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
      rw [Subgroup.card_map_of_injective (MulAut.conj n').injective]
    refine ⟨⟨n', hn'L, hn'N⟩, ?_⟩
    apply LinearEquiv.ext
    intro a
    apply Additive.ext
    apply Subtype.ext
    rw [pi_coe]
    rw [hn'A ↑(Additive.toMul a) (Additive.toMul a).2]
    rw [hf ↑(Additive.toMul a) (Additive.toMul a).2]
    exact congrArg Subtype.val (heM (Additive.toMul a)).symm
  have hker_card : Nat.card ↥(LinearMap.ker
      ((pi ⟨n, hn⟩).toLinearMap - LinearMap.id)) =
      Nat.card ↥(A ⊓ centralizer ({n} : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun a => ⟨(Additive.toMul a.1).1, ?_⟩
        invFun := fun a => ⟨Additive.ofMul ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · refine Subgroup.mem_inf.2 ⟨(Additive.toMul a.1).2, ?_⟩
      have hmem : ((pi ⟨n, hn⟩).toLinearMap -
          (LinearMap.id : Additive ↥A →ₗ[ZMod 2] Additive ↥A)) a.1 = 0 :=
        LinearMap.mem_ker.mp a.2
      have hfixpt : pi ⟨n, hn⟩ a.1 = a.1 := by
        rw [LinearMap.sub_apply, LinearMap.id_apply] at hmem
        exact sub_eq_zero.mp hmem
      have h2 : n * ((Additive.toMul a.1 : ↥A) : G) * n⁻¹ = ((Additive.toMul a.1 : ↥A) : G) := by
        calc n * ((Additive.toMul a.1 : ↥A) : G) * n⁻¹
            = ((Additive.toMul (pi ⟨n, hn⟩ a.1) : ↥A) : G) := (pi_coe ⟨n, hn⟩ a.1).symm
          _ = ((Additive.toMul a.1 : ↥A) : G) :=
              congrArg (fun z : Additive ↥A => ((Additive.toMul z : ↥A) : G)) hfixpt
      exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h2).symm
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      have hgoal : pi ⟨n, hn⟩ (Additive.ofMul ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩) =
          Additive.ofMul ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩ := by
        apply Additive.ext
        apply Subtype.ext
        calc ((Additive.toMul (pi ⟨n, hn⟩
                (Additive.ofMul ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩)) : ↥A) : G)
            = n * (a.1 : G) * n⁻¹ := pi_coe ⟨n, hn⟩ _
          _ = (a.1 : G) := mul_inv_eq_iff_eq_mul.mpr
              (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp a.2).2).symm
      exact sub_eq_zero.mpr hgoal
    · intro a
      apply Additive.ext
      apply Subtype.ext
      rfl
    · intro a
      apply Subtype.ext
      rfl
  have hkerfin : Module.finrank (ZMod 2) (LinearMap.ker
      ((pi ⟨n, hn⟩).toLinearMap - LinearMap.id)) = 3 := by
    haveI : Finite ↥(LinearMap.ker ((pi ⟨n, hn⟩).toLinearMap - LinearMap.id)) := Subtype.finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.ker ((pi ⟨n, hn⟩).toLinearMap - LinearMap.id))
    rw [Nat.card_zmod, hker_card, hfix, show (8 : ℕ) = 2 ^ 3 by norm_num] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have hmain := CFSG.LinearAlgebra.card_fixed_of_transvection (A := Additive ↥A)
    (V := Additive ↥V) hfinrankA iota hinj theta hsurjTheta hrange pi hpi_surj rho hker hρι hθρ
    ⟨n, hn⟩ hkerfin
  have hVfixed : Nat.card {v : Additive ↥V // rho ⟨n, hn⟩ v = v} =
      Nat.card ↥(V ⊓ centralizer ({n} : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun v => ⟨(Additive.toMul v.1).1, ?_⟩
        invFun := fun v => ⟨Additive.ofMul ⟨v.1, (Subgroup.mem_inf.mp v.2).1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · refine Subgroup.mem_inf.2 ⟨(Additive.toMul v.1).2, ?_⟩
      have hfixpt : rho ⟨n, hn⟩ v.1 = v.1 := v.2
      have h2 : n * ((Additive.toMul v.1 : ↥V) : G) * n⁻¹ = ((Additive.toMul v.1 : ↥V) : G) := by
        calc n * ((Additive.toMul v.1 : ↥V) : G) * n⁻¹
            = ((Additive.toMul (rho ⟨n, hn⟩ v.1) : ↥V) : G) := (rho_coe ⟨n, hn⟩ v.1).symm
          _ = ((Additive.toMul v.1 : ↥V) : G) :=
              congrArg (fun z : Additive ↥V => ((Additive.toMul z : ↥V) : G)) hfixpt
      exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h2).symm
    · apply Additive.ext
      apply Subtype.ext
      calc ((Additive.toMul (rho ⟨n, hn⟩
              (Additive.ofMul ⟨v.1, (Subgroup.mem_inf.mp v.2).1⟩)) : ↥V) : G)
          = n * (v.1 : G) * n⁻¹ := rho_coe ⟨n, hn⟩ _
        _ = (v.1 : G) := mul_inv_eq_iff_eq_mul.mpr
            (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp v.2).2).symm
    · intro v
      apply Additive.ext
      apply Subtype.ext
      rfl
    · intro v
      apply Subtype.ext
      rfl
  rw [← hmain]
  exact hVfixed.symm

theorem ThCyc.card_omega1_inf_centralizer_of_conj_eq (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {m n : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    (hmn : ∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = n * v * n⁻¹)
    (hfix : Nat.card ↥(A ⊓ centralizer ({m} : Set G)) = 8) :
    Nat.card ↥(omega1 D hD.comm ⊓ centralizer ({m} : Set G)) = 2 ^ 6 := by
  have hAsub : A ⊓ centralizer ({m} : Set G) = A ⊓ centralizer ({n} : Set G) := by
    ext a
    constructor
    · rintro ⟨haA, haC⟩
      have h1 : m * a * m⁻¹ = a :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp haC).symm
      have h2 : n * a * n⁻¹ = a := by
        rw [← hmn a (H.A_le_omega1 W W2 hD haA), h1]
      exact ⟨haA, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h2).symm⟩
    · rintro ⟨haA, haC⟩
      have h1 : n * a * n⁻¹ = a :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp haC).symm
      have h2 : m * a * m⁻¹ = a := by
        rw [hmn a (H.A_le_omega1 W W2 hD haA), h1]
      exact ⟨haA, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h2).symm⟩
  have hVsub : omega1 D hD.comm ⊓ centralizer ({m} : Set G) =
      omega1 D hD.comm ⊓ centralizer ({n} : Set G) := by
    ext v
    constructor
    · rintro ⟨hvV, hvC⟩
      have h1 : m * v * m⁻¹ = v :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hvC).symm
      have h2 : n * v * n⁻¹ = v := by
        rw [← hmn v hvV, h1]
      exact ⟨hvV, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h2).symm⟩
    · rintro ⟨hvV, hvC⟩
      have h1 : n * v * n⁻¹ = v :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hvC).symm
      have h2 : m * v * m⁻¹ = v := by
        rw [hmn v hvV, h1]
      exact ⟨hvV, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h2).symm⟩
  have hfixn : Nat.card ↥(A ⊓ centralizer ({n} : Set G)) = 8 := by
    rw [← hAsub]
    exact hfix
  rw [hVsub]
  exact H.card_omega1_inf_centralizer_of_transvection W W2 hD h4 hb hn hfixn

end CFSG.EvenSporadicStandard.ThStd
