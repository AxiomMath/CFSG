module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZO2
public import CFSG.ClassicalInvolution.Sp62Rec.I1.ActionData
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Kappa
import CFSG.ClassicalInvolution.Sp62Rec.CECentZ5b
import CFSG.ClassicalInvolution.Sp62Rec.I1.KappaCount
import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6
import CFSG.ClassicalInvolution.Sp62Rec.OddB
import CFSG.ClassicalInvolution.Sp62Rec.Rigid
import CFSG.ClassicalInvolution.Sp62Rec.SylowOfHat

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec.I1

section Reduction

variable
  {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
  {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}

theorem I1Action.exists_sylow_of_leaves (D : I1Action z e E B f Θ φ)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hze : z ≠ e) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hoddz : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (heO2 : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype)
    (hQ2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer (E : Set G) →
      Nat.card Q ≤ 2)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G))
    (hX : I1Six z e E B → oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ →
      ¬ Subgroup.centralizer ({e} : Set G) ≤ B →
        ∀ T A : Subgroup G, T ≤ B → Nat.card T = 512 → A ≤ T → IsE64 A →
          (∀ A' ≤ T, IsE64 A' → A' = A) →
            ∃ X : Subgroup G, X ≤ Subgroup.normalizer (A : Set G) ∧
              (∀ g ∈ Subgroup.normalizer (A : Set G), X.map (MulAut.conj g).toMonoidHom = X) ∧
              ∃ ν : ↥X →* ↥N0, Function.Surjective ν ∧ Nat.card ν.ker ≤ 2 ∧
                ν.ker ≤ Subgroup.center ↥X) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ B ∧ z ∈ (S : Subgroup G) ∧
      ∀ x ∈ (S : Subgroup G), z * x = x * z := by
  have P : I1Six z e E B := D.toI1Six
  obtain ⟨TB, hzT, hzc⟩ := P.exists_sylow_B hz2
  have hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ :=
    P.oddCoreIn_centralizer_eq_bot TB hzT hzc hz2 hz1 hze he2 hoddz heO2 card_S0 card_Hhat
      eq_of_mem_center_S0 Hhat_le_centralizer_alpha fun x hx => exists_four_conj hx
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e :=
    P.centralizer_eq_zpowers_of_Z5b hodd he2 he1 hQ2
  have hcardTB : Nat.card (TB : Subgroup ↥B) = 512 := by
    obtain ⟨T₀, hT₀B, -, hcard, ⟨P₀, hP₀⟩, -⟩ := exists_sylow_of_hat φ D.φ_surj D.φ_ker
    have h1 := Sylow.card_eq_multiplicity TB
    have h2 := Sylow.card_eq_multiplicity P₀
    rw [hP₀] at h2
    rw [h1, ← h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀B).toEquiv, hcard]
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup G, T = (TB : Subgroup ↥B).map B.subtype := ⟨_, rfl⟩
  have hTB : T ≤ B := hTdef ▸ Subgroup.map_subtype_le _
  have hT : Nat.card T = 512 := by
    rw [hTdef, Subgroup.card_map_of_injective B.subtype_injective, hcardTB]
  have hzTT : z ∈ T := hTdef ▸ ⟨⟨z, P.z_mem⟩, hzT, rfl⟩
  have hzcT : ∀ x ∈ T, z * x = x * z := by
    intro x hx
    rw [hTdef] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact congrArg Subtype.val (hzc y hy)
  have hTp : IsPGroup 2 T := hTdef ▸ TB.isPGroup'.map B.subtype
  obtain ⟨S, hTS⟩ := hTp.exists_le_sylow
  suffices hTeq : T = (S : Subgroup G) from
    ⟨S, hTeq ▸ hTB, hTeq ▸ hzTT, fun x hx => hzcT x (hTeq ▸ hx)⟩
  by_cases hgood : Subgroup.centralizer ({e} : Set G) ≤ B
  ·
    obtain ⟨S₀, hS₀⟩ := hS
    have hS₀B : (S₀ : Subgroup G) ≤ B := hS₀.trans hgood
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S₀.isPGroup'
    have hS₀p : IsPGroup 2 ((S₀ : Subgroup G).subgroupOf B) :=
      IsPGroup.of_card (n := k) (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀B).toEquiv, hk])
    obtain ⟨P₀, hP₀⟩ := hS₀p.exists_le_sylow
    have hS₀card : Nat.card (S₀ : Subgroup G) ≤ 512 := by
      calc Nat.card (S₀ : Subgroup G) = Nat.card ((S₀ : Subgroup G).subgroupOf B) :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀B).toEquiv).symm
        _ ≤ Nat.card (P₀ : Subgroup ↥B) := Subgroup.card_le_of_le hP₀
        _ = Nat.card (TB : Subgroup ↥B) := by
            rw [Sylow.card_eq_multiplicity P₀, Sylow.card_eq_multiplicity TB]
        _ = 512 := hcardTB
    have hSS₀ : Nat.card (S : Subgroup G) = Nat.card (S₀ : Subgroup G) := by
      rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity S₀]
    exact Subgroup.eq_of_le_of_card_ge hTS (by rw [hT, hSS₀]; exact hS₀card)
  ·
    obtain ⟨A, θ, heT, hθe, hEP, hAθ⟩ := D.exists_theta hodd hTB hT
    obtain ⟨hCA, -, hN2⟩ := D.naCount_hyps hodd he2 he1 hCE hS hEP
    obtain ⟨X, hXN, hXn, ν, hsurj, hker, hcen⟩ :=
      hX P hodd hgood T A hTB hT hEP.A_le hEP.e64 hEP.uniq
    obtain ⟨-, -, -, hmax⟩ :=
      naBridge (e := e) T A X θ hEP.A_le hAθ hCA hN2 hXN hXn ν hsurj hker hcen
    exact eq_of_maximal_in_centralizer S T hTS θ heT hθe hmax

end Reduction

end CFSG.ClassicalInvolution.Sp62Rec

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Balance

section E8ZSixLeaves



variable {n : ℕ}

theorem p23E8ZSix_of_leaves (hT : Thm4RTwinBelow 3 n) (hCE : P23E8ZCE n) (hX : P23E8ZX n) :
    P23E8ZSix n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZs hAE Z hI hoddt
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hte : t ≠ e := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  obtain ⟨f, Θ, φ, D⟩ := i1_action_final hc.std.perp hAE hI
  exact D.exists_sylow_of_leaves hzt.sq hzt.ne_one hte hd.he2 hd.he1 hoddt
    (p23E8Z_e_mem_pCore hT hcit hP hc hZs hoddt)
    (hCE hcit hP Y R S t K' W u e g hc hno hZs hAE)
    (exists_sylow_le_centralizer_e hc)
    (hX hcit hP Y R S t K' W u e g hc hno hZs hAE Z hI)

end E8ZSixLeaves

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
