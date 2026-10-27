module

public import CFSG.GH74.Generic.BProg.Stage2Defs
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.GH74.Generic.BProg.B1.PilotS4Facts

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem inU0_A (hs : Stage2Setup G x K A M P Q) : InU0 M A := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have hAe3 : IsE 3 ⊤ A := ⟨le_top, hAel, hr3.ge⟩
  have hbal := hs.reg.1
  have hAM : A ≤ M :=
    Subgroup.le_normalizer.trans ((normalizer_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2
      ⟨le_rfl, hAel, by omega⟩).trans hs.le_M)
  exact ⟨⟨hAM, hAel, by omega⟩, Or.inr hr3, by
    rw [hr3]
    exact (gammaK_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2).trans hs.le_M⟩

theorem x_mem_Q (hs : Stage2Setup G x K A M P Q) : x ∈ Q := by
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hKC : K ≤ centralizer ({x} : Set G) := hs.pair.1.1.1.2.2.1
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxP : x ∈ P := by
    obtain ⟨S, hS⟩ := hs.sylowP
    have hcent : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈
        Subgroup.center ↥(centralizer ({x} : Set G)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : G) ∈ centralizer ({x} : Set G) := g.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg)
    have hN : (zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))).Normal :=
      normal_of_le_center (zpowers_le.2 hcent)
    have hx'2 : orderOf (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
      rw [← orderOf_injective (centralizer ({x} : Set G)).subtype
        (centralizer ({x} : Set G)).subtype_injective ⟨x, hxC⟩]
      exact hx2
    have hp : IsPGroup 2 (zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx'2, pow_one]
    have hle := IsPGroup.le_sylow_of_normal hp S
    rw [← hS]
    exact ⟨⟨x, hxC⟩, hle (mem_zpowers _), rfl⟩
  rw [hs.Q_eq]
  exact ⟨hxP, mem_CxK_self hKC⟩

theorem isE_inf_K (hs : Stage2Setup G x K A M P Q) : IsE 2 A (A ⊓ K) := by
  obtain ⟨-, hAel, hAcard, hcase⟩ := hs.src
  have hB : CFSG.IsElementaryAbelian 2 ↥(A ⊓ K) :=
    Th2Sig6.isElementaryAbelian_of_le hAel inf_le_left
  refine ⟨inf_le_left, hB, ?_⟩
  rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -, -, hE4, -⟩
  · rw [inf_eq_left.2 hAK]
    have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
    omega
  · have hEA : E ≤ A := hAE ▸ le_sup_left
    have hle : Nat.card ↥E ≤ Nat.card ↥(A ⊓ K) := Subgroup.card_le_of_le (le_inf hEA hEK)
    rw [hE4, Th2Sig6.card_eq_two_pow_pRank hB] at hle
    by_contra hlt
    have : 2 ^ pRank 2 ↥(A ⊓ K) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

@[expose] def CenterlessS345 : Prop :=
  ∀ (Kt : Type) [Group Kt], IsQuasisimple Kt → (QShape3 Kt ∨ QShape4 Kt ∨ QShape5 Kt) →
    ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1

theorem centerlessS345 :
    CenterlessS345 := by
  intro Kt _ hq hshape
  rcases hshape with h3 | h4 | h5
  · exact B1.PilotS3.center_trivial_of_simple_of_quasisimple (B1.PilotS3.isSimpleGroup_of_qShape3 h3) hq
  · exact B1.PilotS4.center_of_qShape4 h4
  · exact B1.PilotS5.center_of_isSporadic h5

private theorem eq_one_of_two_pow_of_mem_pPrimeCoreOf {K : Subgroup G} {c : G}
    (hc : c ∈ pPrimeCoreOf 2 K) {n : ℕ} (hcn : c ^ (2 ^ n) = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, rfl⟩ := hc
  have hkn : k ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hcn)
  have h1 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hkn
  have h2 : orderOf k ∣ Nat.card (pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ hk
  have h3 : orderOf k = 1 :=
    Nat.eq_one_of_dvd_coprimes ((CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)).pow_left n) h1 h2
  rw [orderOf_eq_one_iff.1 h3]
  simp

theorem commute_Q_inf (hs : Stage2Setup G x K A M P Q) :
    ∀ q ∈ Q, ∀ a ∈ A ⊓ K, q * a = a * q := by
  intro q hq a ha
  have hqPC : q ∈ P ⊓ CxK x K := hs.Q_eq ▸ hq
  have hqS : q ∈ centralizerSection K (pPrimeCoreOf 2 K) := hqPC.2.2
  have hqP : q ∈ P := hqPC.1
  have haP : a ∈ P := hs.A_le ha.1
  have hc1 : ⁅a, q⁆ ∈ pPrimeCoreOf 2 K := hqS.2.2 a ha.2
  have hc2 : ⁅a, q⁆ ∈ P := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem haP hqP) (inv_mem haP)) (inv_mem hqP)
  obtain ⟨n, hn⟩ := hs.sylowP.isPGroup (⟨⁅a, q⁆, hc2⟩ : ↥P)
  have hn' : ⁅a, q⁆ ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have h1 : ⁅a, q⁆ = 1 := eq_one_of_two_pow_of_mem_pPrimeCoreOf hc1 hn'
  rw [commutatorElement_def] at h1
  have : a * q = q * a := by
    calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
      _ = q * a := by rw [h1, one_mul]
  exact this.symm

theorem Q_le_M (hs : Stage2Setup G x K A M P Q) : Q ≤ M := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have hAe3 : IsE 3 ⊤ A := ⟨le_top, hAel, hr3.ge⟩
  have hbal := hs.reg.1
  have hE : IsE 2 A (A ⊓ K) := isE_inf_K hs
  intro q hq
  have h1 : q ∈ normalizer ((A ⊓ K : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
      (commute_Q_inf hs q hq a ha).symm)
  have h2 : normalizer ((A ⊓ K : Subgroup G) : Set G) ≤ gammaK 2 A 2 :=
    le_iSup₂_of_le (A ⊓ K) inf_le_left (le_iSup_of_le hE.2.2 le_rfl)
  exact hs.le_M ((gammaK_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2) (h2 h1))

end CFSG.GH74.Generic.BProg.B2
