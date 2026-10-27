module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdBarComp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.LocalCores

variable {G : Type} [Group G] [Finite G]

theorem isPComponent_two_of_isComponent {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) : IsPComponent 2 L := by
  refine CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hL ?_
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hL
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) hle

omit [Finite G] in
noncomputable def toBarIn {H : Subgroup G} {K : Subgroup G} (hKH : K ≤ H) :
    ↥K →* ↥(barIn H K) :=
  ((mkH H).comp (Subgroup.inclusion hKH)).codRestrict (barIn H K) (fun k =>
    ⟨⟨k, hKH k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩)

omit [Finite G] in
theorem toBarIn_surjective {H K : Subgroup G} (hKH : K ≤ H) :
    Function.Surjective (toBarIn hKH) := by
  rintro ⟨y, hy⟩
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨⟨h, Subgroup.mem_subgroupOf.1 hh⟩, Subtype.ext rfl⟩

noncomputable def quotBarInEquiv {H K : Subgroup G} (hKH : K ≤ H) :
    (↥K ⧸ pPrimeCore 2 ↥K) ≃* (↥(barIn H K) ⧸ pPrimeCore 2 ↥(barIn H K)) := by
  let ρ : ↥K →* (↥(barIn H K) ⧸ pPrimeCore 2 ↥(barIn H K)) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(barIn H K))).comp (toBarIn hKH)
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (toBarIn_surjective hKH)
  have hodd : ∀ k ∈ ρ.ker, Odd (orderOf k) := by
    intro k hk
    have h1 : toBarIn hKH k ∈ pPrimeCore 2 ↥(barIn H K) := (QuotientGroup.eq_one_iff _).1 hk
    have hm : Odd (orderOf (toBarIn hKH k)) := odd_orderOf_of_mem_pPrimeCore h1
    set m := orderOf (toBarIn hKH k) with hmdef
    have h2 : toBarIn hKH (k ^ m) = 1 := by rw [map_pow, hmdef, pow_orderOf_eq_one]
    have h3 : Subgroup.inclusion hKH (k ^ m) ∈ pPrimeCore 2 ↥H := by
      rw [← mkH_eq_one_iff]
      exact congrArg Subtype.val h2
    have h4 : Odd (orderOf (k ^ m)) := by
      have := odd_orderOf_of_mem_core H h3
      rwa [orderOf_injective _ (Subgroup.inclusion_injective hKH)] at this
    have h5 : orderOf k ∣ m * orderOf (k ^ m) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    exact Odd.of_dvd_nat (hm.mul h4) h5
  exact IVK.Proofs2.Ivk93Adapt.quotEquivOfHom ρ hρ hodd
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2)

theorem hasSL2Model_barIn {H K : Subgroup G} (hKH : K ≤ H) {P : ℕ → Prop}
    (h : HasSL2Model (↥K ⧸ pPrimeCore 2 ↥K) P) :
    HasSL2Model (↥(barIn H K) ⧸ pPrimeCore 2 ↥(barIn H K)) P := by
  obtain ⟨F, hF, hFin, hP, ⟨e⟩⟩ := h
  exact ⟨F, hF, hFin, hP, ⟨(quotBarInEquiv hKH).symm.trans e⟩⟩

theorem cfg_of_components {J : Subgroup G} {z : G}
    (hzJ : z ∈ J) (hz2 : orderOf z = 2) {K₁ K₂ : Subgroup G} {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK₁J : K₁ ≤ J) (hK₂J : K₂ ≤ J)
    (hK₁C : K₁ ≤ centralizer ({z} : Set G)) (hK₂C : K₂ ≤ centralizer ({z} : Set G))
    (hq₁ : IsQuasisimple ↥K₁) (hq₂ : IsQuasisimple ↥K₂)
    (hsub₁ : (K₁.subgroupOf (centralizer ({z} : Set G))).IsSubnormal)
    (hsub₂ : (K₂.subgroupOf (centralizer ({z} : Set G))).IsSubnormal)
    (hzK₁ : z ∈ K₁) (hzK₂ : z ∈ K₂) (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hsl₁ : HasSL2Model (↥K₁ ⧸ pPrimeCore 2 ↥K₁) (fun r => r = q))
    (hsl₂ : HasSL2Model (↥K₂ ⧸ pPrimeCore 2 ↥K₂) (fun r => r = q)) :
    IVK.Proofs2.Ivk93Cfg (mkH J ⟨z, hzJ⟩) q (barIn J K₁) (barIn J K₂) := by
  have hzJ2 : orderOf (⟨z, hzJ⟩ : ↥J) = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hx2 : orderOf (mkH J ⟨z, hzJ⟩) = 2 := orderOf_mk_eq_two J hzJ2
  have hcomp₁ := isComponent_barIn hzJ hz2 hK₁J hK₁C hq₁ hsub₁
  have hcomp₂ := isComponent_barIn hzJ hz2 hK₂J hK₂C hq₂ hsub₂
  have hle : ∀ {K : Subgroup G}, K ≤ Cen z →
      barIn J K ≤ centralizer ({mkH J ⟨z, hzJ⟩} : Set (HBar J)) := fun hKC => by
    rw [centralizer_mk_eq J hz2 hzJ]
    exact barIn_mono' hKC
  have hcomm' : ∀ a ∈ barIn J K₁, ∀ b ∈ barIn J K₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (mkH J) (Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.1 ha) b
      (Subgroup.mem_subgroupOf.1 hb)))
  refine ⟨hx2, hq, h5, ?_, ⟨hle hK₁C, isPComponent_two_of_isComponent hcomp₁⟩,
    ⟨hle hK₂C, isPComponent_two_of_isComponent hcomp₂⟩,
    ⟨⟨z, hzJ⟩, Subgroup.mem_subgroupOf.2 hzK₁, rfl⟩,
    ⟨⟨z, hzJ⟩, Subgroup.mem_subgroupOf.2 hzK₂, rfl⟩,
    hasSL2Model_barIn hK₁J hsl₁, hasSL2Model_barIn hK₂J hsl₂⟩
  intro heq
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_barIn hK₁J hq₁
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h := hcomm' (a : HBar J) a.2 (b : HBar J) (heq ▸ b.2)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
