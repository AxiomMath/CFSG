module

public import CFSG.Quasithin.H13.A6S1372EighteenB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372EighteenA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372FifteenB

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1376AltNat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H →
      (∀ n, 3 ≤ n → ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n 1) ∧
      ¬ SLExteriorTwo (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 5 ∧
      (∀ n, AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n →
        n = 6 ∧ ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H ∧ S.L1 ≤ K ∧ H = K ⊔ T ∧
          ∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
            (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
            ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
      ¬ SLExteriorTwo (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 4 ∧
      ¬ A7Four (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) ∧
      (∀ n, BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n → n = 1) ∧
      (∀ n, BinaryNaturalSp4 (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n → n = 1) ∧
      (∀ n, G2Natural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n → n = 1)

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in

theorem KData.lem13718_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4) (h51 : AsB51)
    (hAlt : Lem1376AltNat_F4) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) :
    BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 2 2 ∨
      (AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 6 ∧
        ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H ∧ S.L1 ≤ K ∧ H = K ⊔ T ∧
        ∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
          (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
          ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) := by
  have hKc : K ∈ cComp H := hK.2.2.1
  obtain ⟨h1, h2, h3, h3', h4, h5a, h5b, h5c⟩ := hAlt G T L V S hNS hNU hhat H hH hab K hKc
  set Kp := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hKp
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hVp := Bridge.sec_sq_eq_one hV' (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
  have hVs := Bridge.sec_sq_eq_one hVp (commV Kp) (fixV Kp ⊓ commV Kp)

  have hb51 := S.b51Hyp_J_F4 hNS h13315 h1356two hH hab hhat hNU hLem hK.1 hK.2.2.2.1 hK.2.2.2.2.1
    hK.2.2.2.2.2.1 hK.2.2.2.2.2.2.2.2.1
  have hn : ∀ g ∈ Kp, ∀ l ∈ Kp, g * l * g⁻¹ ∈ Kp := fun g hg l hl =>
    Kp.mul_mem (Kp.mul_mem hg hl) (Kp.inv_mem hg)
  have hLW := B5.le_stabSub_commV hn fun g hg => Kp.inv_mem hg
  have hLU := B5.le_stabSub_fixV_inf_commV hn fun g hg => Kp.inv_mem hg
  have hfaith := B5.L_inf_centSec_eq_bot hb51 hVp

  have trp := fun (D : FFModel) (hD : D.Realizes Kp (commV Kp) (fixV Kp ⊓ commV Kp)) =>
    hK.realizes_tilde_of_plus_F4 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51 hab hD
  have tr := fun (D : FFModel) (hD : D.Realizes (autSec Kp (commV Kp) (fixV Kp ⊓ commV Kp))
      (⊤ : Subgroup (Sec (commV Kp) (fixV Kp ⊓ commV Kp))) ⊥) =>
    trp D (B5.realizes_of_autSec inf_le_right hLW hLU hfaith hD)
  have one_le : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = 2 ^ n → 1 ≤ n := by
    intro F _ _ n hF
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := F)
    rw [hF, h0] at this
    norm_num at this
  rcases hK.2.2.2.2.2.2.2.2.2.2.1 with ⟨-, B', hB'B, hB'off, hb4, hres⟩ |
      ⟨-, n, hn45, I, π, -, -, hsup, hR⟩
  · rcases hres with ⟨-, hnat⟩ | ⟨⟨-, ⟨n, hsl⟩, -⟩, -⟩ | ⟨⟨⟨n, hsp, hJ⟩, -⟩, -⟩ |
        ⟨⟨n, hg2, -, hJ⟩, -⟩ | h5 | ⟨-, h6, -⟩ | ⟨-, -, h7, -⟩ | ⟨-, n, hn45, h9, -⟩ |
        ⟨h10, -⟩ | ⟨-, -, -, -, π, hR11, -⟩
    ·
      obtain ⟨F, _, _, hc, hRF⟩ := hnat
      exact Or.inl ⟨F, inferInstance, inferInstance, hc, tr _ hRF⟩
    ·
      obtain ⟨F, _, _, hc, hRF⟩ := hsl
      have hn1 := h5a n ⟨F, inferInstance, inferInstance, hc, tr _ hRF⟩
      subst hn1
      exact absurd ⟨F, inferInstance, inferInstance, hc, tr _ hRF⟩ (h1 3 le_rfl)
    ·
      rcases Nat.lt_or_ge 1 n with hn1 | hn1
      · rw [hJ hn1] at hsp
        obtain ⟨F, _, _, hc, hRF⟩ := hsp
        exact absurd (h5b n ⟨F, inferInstance, inferInstance, hc, tr _ hRF⟩) (by omega)
      · obtain ⟨F, _, _, hc, hRF⟩ := hsp
        have hn' : n = 1 := le_antisymm hn1 (one_le hc)
        subst hn'
        have hS6 := asSp4S6 _ _ _ _ ⟨F, inferInstance, inferInstance, hc, hRF⟩
        have halt := A6Eighteen.alternatingNatural_of_symmetricNatural hVs hb4 (by norm_num) hS6
        exact Or.inr ⟨tr _ halt, (h3 6 (tr _ halt)).2⟩
    ·
      rcases Nat.lt_or_ge 1 n with hn1 | hn1
      · rw [hJ hn1] at hg2
        obtain ⟨F, _, _, hc, hRF⟩ := hg2
        exact absurd (h5c n ⟨F, inferInstance, inferInstance, hc, tr _ hRF⟩) (by omega)
      · have hn' : n = 1 := by
          obtain ⟨F, _, _, hc, -⟩ := hg2
          exact le_antisymm hn1 (one_le hc)
        subst hn'
        have hlt := asB46ThirteenG2Two_holds _ hVs _ _ _ hb4 hB'off hg2
        have hle : Nat.card (commV B') ≤ 4 :=
          (Subgroup.card_le_of_le (G6.commV_mono hB'B)).trans
            ((A6FifteenB.card_commV_autSec_le B _ _).trans hK.2.2.2.2.2.2.2.2.2.1)
        exact absurd hlt (not_lt.mpr hle)
    ·
      obtain ⟨n, hn57, halt, -⟩ := InternalSec.alternatingNatural_of_b42Case5 hVs hb4 h5
      have := (h3 n (tr _ halt)).1
      omega
    ·
      exact Or.inr ⟨tr _ h6, (h3 6 (tr _ h6)).2⟩
    ·
      obtain ⟨α, hα⟩ := h7
      exact absurd ⟨α, tr _ hα⟩ h4
    ·
      obtain ⟨F, _, _, hc, hRF⟩ := h9
      exact absurd ⟨F, inferInstance, inferInstance, hc, tr _ hRF⟩ (h1 n (by omega))
    ·
      exact absurd (tr _ h10) h3'
    ·
      exact absurd (tr _ ⟨π, hR11⟩) h2
  ·
    have hI : I 0 = commV Kp := by
      rw [← hsup, bot_sup_eq, iSup_unique]
      rfl
    have hn2 : 2 ≤ n := by omega
    have hfix := B5.nat_fixed_eq_one hn2 (hR 0)
    rw [hI] at hfix
    have hbot : fixV Kp ⊓ commV Kp = ⊥ :=
      eq_bot_iff.2 fun u hu => Subgroup.mem_bot.2 (hfix u hu.2 fun l hl => hu.1 l hl)
    have hR0 := hR 0
    rw [hI, ← hbot] at hR0
    have hnat := trp _ ⟨π, hR0⟩
    exact absurd ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], hnat⟩
      (h1 n (by omega))

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
