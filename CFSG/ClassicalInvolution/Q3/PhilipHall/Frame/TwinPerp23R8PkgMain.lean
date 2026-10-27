module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZXThm2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Kappa
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6M
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoI1
import CFSG.ClassicalInvolution.Sp62Rec.CECentZ5b
import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6
import CFSG.ClassicalInvolution.Sp62Rec.OddB
import CFSG.ClassicalInvolution.Sp62Rec.SylowOfHatAll

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec.I1

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_eq_bot_of_selfCentralizing {A X : Subgroup G} (hAX : A ≤ X)
    (hXN : X ≤ Subgroup.normalizer (A : Set G)) (hCA : Subgroup.centralizer (A : Set G) = A)
    (hA : IsPGroup 2 A) : oddCoreIn X = ⊥ := by
  have hdisj : Disjoint A (oddCoreIn X) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_card_oddCoreIn X))
  refine eq_bot_iff.mpr fun o ho => ?_
  have hoX : o ∈ X := oddCoreIn_le X ho
  have hoC : o ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : o * a * o⁻¹ * a⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hoX) a).mp ha) (A.inv_mem ha)
    have h2 : o * a * o⁻¹ * a⁻¹ ∈ oddCoreIn X := by
      have := (oddCoreIn X).mul_mem ho
        (conj_mem_oddCoreIn (hAX ha) ((oddCoreIn X).inv_mem ho))
      simpa [mul_assoc] using this
    have h3 : o * a * o⁻¹ * a⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj h1 h2
    have h4 : o * a = a * o :=
      calc o * a = (o * a * o⁻¹ * a⁻¹) * (a * o) := by group
        _ = a * o := by rw [h3, one_mul]
    exact h4.symm
  rw [hCA] at hoC
  simpa using Subgroup.disjoint_def.mp hdisj hoC ho

end OddCore

section Reduction

variable
  {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
  {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}

theorem I1Action.exists_pkgNoHat (D : I1Action z e E B f Θ φ)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hze : z ≠ e) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hoddz : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (heO2 : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype)
    (hQ2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer (E : Set G) →
      Nat.card Q ≤ 2)
    (T : Sylow 2 G) (hTB : (T : Subgroup G) ≤ B) (hzT : z ∈ (T : Subgroup G))
    (hzc : ∀ x ∈ (T : Subgroup G), z * x = x * z)
    (hgen : ∀ n : G, E.map (MulAut.conj n).toMonoidHom ≠ E →
      E ⊔ E.map (MulAut.conj n).toMonoidHom = ⊤)
    (hX : I1Six z e E B → oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ →
      ∀ T A : Subgroup G, T ≤ B → Nat.card T = 512 → A ≤ T → IsE64 A →
        (∀ A' ≤ T, IsE64 A' → A' = A) →
          ∃ X : Subgroup G, X ≤ Subgroup.normalizer (A : Set G) ∧
            (∀ g ∈ Subgroup.normalizer (A : Set G), X.map (MulAut.conj g).toMonoidHom = X) ∧
            ∃ ν : ↥X →* ↥N0, Function.Surjective ν ∧ Nat.card ν.ker ≤ 2 ∧
              ν.ker ≤ Subgroup.center ↥X) :
    ∃ A X : Subgroup G, E8ZPkgNoHat z e E B T A X := by
  have P : I1Six z e E B := D.toI1Six
  have hzB : (⟨z, P.z_mem⟩ : ↥B) ∈ ((T.subtype hTB : Sylow 2 ↥B) : Subgroup ↥B) := by
    rw [Sylow.coe_subtype]
    exact hzT
  have hzcB : ∀ x ∈ ((T.subtype hTB : Sylow 2 ↥B) : Subgroup ↥B),
      (⟨z, P.z_mem⟩ : ↥B) * x = x * ⟨z, P.z_mem⟩ := by
    intro x hx
    rw [Sylow.coe_subtype] at hx
    exact Subtype.ext (hzc x.1 (Subgroup.mem_subgroupOf.mp hx))
  have hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ :=
    P.oddCoreIn_centralizer_eq_bot (T.subtype hTB) hzB hzcB hz2 hz1 hze he2 hoddz heO2 card_S0
      card_Hhat eq_of_mem_center_S0 Hhat_le_centralizer_alpha fun x hx => exists_four_conj hx
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e :=
    P.centralizer_eq_zpowers_of_Z5b hodd he2 he1 hQ2
  have hT512 : Nat.card (T : Subgroup G) = 512 := card_sylow_of_hat φ D.φ_surj D.φ_ker T hTB
  have hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) :=
    ⟨T, hTB.trans D.B_le⟩
  obtain ⟨A, θ, -, -, hEP, hAθ⟩ := D.exists_theta hodd hTB hT512
  obtain ⟨hCA, -, hN2⟩ := D.naCount_hyps hodd he2 he1 hCE hS hEP
  obtain ⟨X, hXN, hXn, ν, hsurj, hker, hcen⟩ :=
    hX P hodd (T : Subgroup G) A hTB hT512 hEP.A_le hEP.e64 hEP.uniq
  obtain ⟨hAX, -, hνinj, -⟩ :=
    naBridge (e := e) (T : Subgroup G) A X θ hEP.A_le hAθ hCA hN2 hXN hXn ν hsurj hker hcen
  have hOX : oddCoreIn X = ⊥ :=
    oddCoreIn_eq_bot_of_selfCentralizing hAX hXN hCA
      (IsPGroup.of_card (n := 6) (by rw [hEP.e64.2.2]; norm_num))
  refine ⟨A, X, ?_⟩
  exact
    { T_le := hTB, z_center := ⟨hzT, hzc⟩, z_sq := hz2, z_ne_one := hz1, z_ne_e := hze,
      A_le := hEP.A_le, e64 := hEP.e64, oddC_z := hoddz, e_mem_O2 := heO2, gen := hgen,
      X_le := hXN,
      thm2 := ⟨ν, hsurj, by
        rw [hOX, Subgroup.bot_subgroupOf]
        exact (MonoidHom.ker_eq_bot_iff ν).mpr hνinj⟩ }

end Reduction

end CFSG.ClassicalInvolution.Sp62Rec

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Balance

section E8ZPkgSteps



variable {n : ℕ}

theorem p23E8ZPkg_of_steps (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) (hZ2 : P23E8ZTwo n) (hCE : P23E8ZCE n) (hSix : P23E8ZSix n)
    (hGen : P23E8ZGen n) (hXS : P23E8ZXStrong n) : P23E8ZPkg n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZs hAE
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hte : t ≠ e := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  obtain ⟨Z, hI⟩ := exists_i1In_of_zTwo hZ2 hcit hP Y R S t K' W u e g hc hno hZs hAE
  obtain ⟨hoddt, heO2⟩ := p23E8Z_oddC_of_normT hE hT hα hN hcit hP hc hno hZs hAE
  obtain ⟨T, hTB, hzT, hzc⟩ := hSix hcit hP Y R S t K' W u e g hc hno hZs hAE Z hI hoddt
  obtain ⟨f, Θ, φ, D⟩ := i1_action_final hc.std.perp hAE hI
  obtain ⟨A, X, hpkg⟩ := D.exists_pkgNoHat hzt.sq hzt.ne_one hte hd.he2 hd.he1 hoddt heO2
    (hCE hcit hP Y R S t K' W u e g hc hno hZs hAE) T hTB hzT hzc
    (hGen hcit hP Y R S t K' W u e g hc hno hZs hAE)
    (hXS hcit hP Y R S t K' W u e g hc hno hZs hAE Z hI)
  exact ⟨Z, T, A, X, hI, hpkg⟩

section Leaves


theorem p23E8ZPkg_of_leaves (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n)
    (hα : P23Alpha n) (hN : P23E8ZNormT n) (hZ2 : P23E8ZTwo n) (hCE : P23E8ZCE n)
    (hGen : P23E8ZGen n) (hXS : P23E8ZXStrong n) : P23E8ZPkg n :=
  p23E8ZPkg_of_steps hE hT hα hN hZ2 hCE (p23E8ZSix_of_ce hT hTwo hα hCE) hGen hXS

end Leaves

end E8ZPkgSteps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
