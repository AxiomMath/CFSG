module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189b

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Red


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem e189_comm_mod_odd_of_not_conj {n : ℕ} (hT4 : Thm4RTwinBelow r n) (hΩ : HypOmegaGen Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hA : ∀ L ∈ Ω, AEmpty Ω L)
    {Y₁ : Subgroup G} (hY₁ : Nat.card Y₁ < n) {Λ₀ : Set (Subgroup G)} (hΛ₀Ω : Λ₀ ⊆ Ω)
    (hΛ₀Y : ∀ J ∈ Λ₀, J ≤ Y₁) (hinv : ∀ y ∈ Y₁, ∀ J ∈ Λ₀, conjSub y J ∈ Λ₀)
    {J L : Subgroup G} (hJ : J ∈ Λ₀) (hL : L ∈ Λ₀) (hnot : ¬ ∃ y ∈ Y₁, conjSub y J = L) :
    ∀ a ∈ J, ∀ b ∈ L, ∃ m ∈ classicalInvolutionOddCore ↥Y₁, (m : G) = a * b * a⁻¹ * b⁻¹ := by
  classical
  set N₁ : Subgroup ↥Y₁ := classicalInvolutionOddCore ↥Y₁ with hN₁
  have hN₁odd : Odd (Nat.card N₁) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₁
  set mk := QuotientGroup.mk' N₁ with hmk
  set Λ₁ : Set (Subgroup ↥Y₁) := (fun M => M.subgroupOf Y₁) '' Λ₀ with hΛ₁def
  have hsub : Λ₁ ⊆ restrictFamily Ω Y₁ := by
    rintro _ ⟨M, hM, rfl⟩
    exact subgroupOf_mem_restrictFamily (hΛ₀Ω hM) (hΛ₀Y M hM)
  have hinvΛ : ConjInvariant Λ₁ := by
    intro g L hL
    obtain ⟨M, hM, rfl⟩ := hL
    rw [conjSub_subgroupOf]
    exact ⟨conjSub (g : G) M, hinv g g.2 M hM, rfl⟩
  have hΦ : HypOmegaGen (restrictFamily Ω Y₁) := hypOmegaGen_restrict hΩ Y₁
  have hΛ₁ : HypOmegaGen Λ₁ := TwinThmEW.hypOmegaGen_of_sub hΦ hsub hinvΛ
  have hΛ₁q := fun L (hL : L ∈ Λ₁) => quat_restrict hq Y₁ L (hsub hL)
  have hΛ₁2 := fun L (hL : L ∈ Λ₁) => TwinThmE.two_restrict h2 Y₁ L (hsub hL)
  have hΛ₁A : ∀ L ∈ Λ₁, AEmpty Λ₁ L :=
    TwinThmEW.aEmpty_of_sub hΦ hsub fun L hL => by
      obtain ⟨L₀, hL₀, hL₀Y, rfl⟩ := hL
      exact TwinThmEW.AEmpty.restrict hΩ hL₀Y (hA L₀ hL₀)
  have hΔ : HypOmegaGen (quotFamily Λ₁ N₁) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ₁ hN₁odd
  have hΔ2 := TwinThmE.two_quot_odd hΛ₁2 hN₁odd
  have hΔq : ∀ M ∈ quotFamily Λ₁ N₁, ∀ P : Subgroup (↥Y₁ ⧸ N₁), IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := fun M hM =>
    TwinDisc.forall_sylow_iso_of_exists (quat_quot_odd hN₁odd hΛ₁q M hM)
  have hΔA := TwinThmE.aEmpty_quot_odd hΛ₁ hN₁odd hΛ₁A
  have hOq : classicalInvolutionOddCore (↥Y₁ ⧸ N₁) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y₁
  have hlt : Nat.card (↥Y₁ ⧸ N₁) < n := by
    have h1 : Nat.card (↥Y₁ ⧸ N₁) ≤ Nat.card ↥Y₁ :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₁)
    omega
  have hJ₁ : J.subgroupOf Y₁ ∈ Λ₁ := ⟨J, hJ, rfl⟩
  have hL₁ : L.subgroupOf Y₁ ∈ Λ₁ := ⟨L, hL, rfl⟩
  have hnot' : ¬ ∃ g : ↥Y₁ ⧸ N₁, conjSub g ((J.subgroupOf Y₁).map mk) = (L.subgroupOf Y₁).map mk := by
    rintro ⟨gb, hgb⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective N₁ gb
    have h1 : (conjSub g' (J.subgroupOf Y₁)).map mk = (L.subgroupOf Y₁).map mk := by
      rw [AscQuot.map_conjSub]
      exact hgb
    have hJ' : conjSub g' (J.subgroupOf Y₁) ∈ Λ₁ := hΛ₁.conjInvariant g' _ hJ₁
    obtain ⟨n', hn'N, hn'⟩ := Q3T6.exists_conj_of_map_eq_gen hΛ₁ hN₁odd hJ' hL₁ h1
    apply hnot
    refine ⟨((n' * g' : ↥Y₁) : G), (n' * g').2, ?_⟩
    have h3 : conjSub (n' * g') (J.subgroupOf Y₁) = L.subgroupOf Y₁ := by
      rw [conjSub_mul]
      exact hn'.symm
    rw [conjSub_subgroupOf] at h3
    have hle : conjSub ((n' * g' : ↥Y₁) : G) J ≤ Y₁ := by
      have := conjSub_mono (n := ((n' * g' : ↥Y₁) : G)) (hΛ₀Y J hJ)
      rwa [conjSub_eq_self_of_mem (n' * g').2] at this
    have := Subgroup.subgroupOf_inj.mp h3
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr (hΛ₀Y L hL)] at this
  have hcomm := hT4 (↥Y₁ ⧸ N₁) hlt (quotFamily Λ₁ N₁) hΔ hΔ2 hΔq hΔA hOq
    ((J.subgroupOf Y₁).map mk) (map_mem_quotFamily hJ₁) ((L.subgroupOf Y₁).map mk)
    (map_mem_quotFamily hL₁) hnot'
  intro a ha b hb
  set aY : ↥Y₁ := ⟨a, hΛ₀Y J hJ ha⟩ with haY
  set bY : ↥Y₁ := ⟨b, hΛ₀Y L hL hb⟩ with hbY
  have hcab : mk aY * mk bY = mk bY * mk aY :=
    hcomm (mk aY) ⟨aY, Subgroup.mem_subgroupOf.mpr ha, rfl⟩ (mk bY)
      ⟨bY, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hmem : aY * bY * aY⁻¹ * bY⁻¹ ∈ N₁ := by
    apply (QuotientGroup.eq_one_iff _).mp
    show mk (aY * bY * aY⁻¹ * bY⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hcab]
    group
  exact ⟨_, hmem, rfl⟩

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.e189_exists_minimal (c : MinCex r Ω K S R W H) {z t k : G} (hz : IsUniqueInvolution K z)
    (htk : t = k * z * k⁻¹) (hkH : k ∈ H) (htS : t ∈ (S : Subgroup G)) (hne : conjSub t K ≠ K) :
    ∃ Y : Subgroup G, Y ≤ H ∧ K ≤ Y ∧ (∃ y ∈ Y, conjSub y K = conjSub k K) ∧
      (⨆ y : Y, conjSub (y : G) K) = Y := by
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have hKH : K ≤ H := fun w hw =>
    hzH (Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem hz hw).symm)
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3 G Ω K S R W H c) c.stand.aEmpty
  have hT4 : Thm4RTwinBelow r (Nat.card G) := c.stand.ih.t4
  have hHn : Nat.card H < Nat.card G := natCard_lt_of_ne_top c.proper
  let 𝒞 : Set (Subgroup G) := {Y' | Y' ≤ H ∧ K ≤ Y' ∧ ∃ y ∈ Y', conjSub y K = conjSub k K}
  have h𝒞 : H ∈ 𝒞 := ⟨le_rfl, hKH, k, hkH, rfl⟩
  obtain ⟨Y, hY𝒞, hYmin⟩ :=
    Set.exists_min_image 𝒞 (fun Y' : Subgroup G => Nat.card Y') (Set.toFinite 𝒞) ⟨H, h𝒞⟩
  obtain ⟨hYH, hKY, y₀, hy₀Y, hy₀⟩ := hY𝒞
  set Y₁ : Subgroup G := ⨆ y : Y, conjSub (y : G) K
  have hconjY : ∀ y : Y, conjSub (y : G) K ≤ Y := fun y => by
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  have hY₁Y : Y₁ ≤ Y := iSup_le hconjY
  have hKY₁ : K ≤ Y₁ := by
    have := le_iSup (fun y : Y => conjSub (y : G) K) 1
    simp only [Subgroup.coe_one, conjSub_one] at this
    exact this
  have hclaim : ∃ y₁ ∈ Y₁, conjSub y₁ K = conjSub k K := by
    by_contra hno
    push Not at hno
    set Λ₀ : Set (Subgroup G) := Set.range (fun y : Y => conjSub (y : G) K)
    have hΛ₀Ω : Λ₀ ⊆ Ω := by
      rintro _ ⟨y, rfl⟩
      exact hΩ.conjInvariant _ K hK
    have hΛ₀Y : ∀ J ∈ Λ₀, J ≤ Y₁ := by
      rintro _ ⟨y, rfl⟩
      exact le_iSup (fun y : Y => conjSub (y : G) K) y
    have hinv : ∀ y ∈ Y₁, ∀ J ∈ Λ₀, conjSub y J ∈ Λ₀ := by
      rintro y hy _ ⟨y', rfl⟩
      refine ⟨⟨y, hY₁Y hy⟩ * y', ?_⟩
      show conjSub (y * (y' : G)) K = conjSub y (conjSub (y' : G) K)
      exact conjSub_mul _ _ _
    have hY₁lt : Nat.card Y₁ < Nat.card G :=
      lt_of_le_of_lt (Subgroup.card_le_of_le (hY₁Y.trans hYH)) hHn
    have hKΛ : K ∈ Λ₀ := ⟨1, by simp⟩
    have hkΛ : conjSub k K ∈ Λ₀ := ⟨⟨y₀, hy₀Y⟩, hy₀⟩
    have hcomm := e189_comm_mod_odd_of_not_conj hT4 hΩ c.stand.quat c.stand.two hAΩ hY₁lt hΛ₀Ω
      hΛ₀Y hinv hKΛ hkΛ (fun ⟨y, hy, h⟩ => hno y hy h)
    obtain ⟨hRΩ, hRK, hRS⟩ := c.stand.hR
    set N₁ : Subgroup ↥Y₁ := classicalInvolutionOddCore ↥Y₁ with hN₁
    have hN₁odd : Odd (Nat.card N₁) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₁
    have htK : t ∈ conjSub k K := by
      rw [htk]
      exact conj_mem_conjSub hz.mem
    have heq1 : ∀ {x : G}, IsPGroup 2 (Subgroup.zpowers x) → Odd (orderOf x) → x = 1 := by
      intro x hx hodd
      obtain ⟨j, hj⟩ := hx.exists_card_eq
      rw [Nat.card_zpowers] at hj
      have hj0 : j = 0 := by
        by_contra hne'
        rw [hj] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne'⟩)
      exact orderOf_eq_one_iff.mp (by rw [hj, hj0, pow_zero])
    have hcR : ∀ x ∈ R, t * x * t⁻¹ = x := by
      intro x hxR
      obtain ⟨m, hmN, hm⟩ := hcomm x (hRK hxR) t htK
      have hcS : x * t * x⁻¹ * t⁻¹ ∈ (S : Subgroup G) :=
        S.mul_mem (S.mul_mem (S.mul_mem (hRS hxR) htS) (S.inv_mem (hRS hxR))) (S.inv_mem htS)
      have hodd : Odd (orderOf (m : G)) := by
        rw [Subgroup.orderOf_coe]
        exact hN₁odd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N₁ hmN)
      have h1 : (m : G) = 1 :=
        heq1 (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hm ▸ hcS))) hodd
      rw [hm] at h1
      have hxt : x * t = t * x := by
        calc x * t = (x * t * x⁻¹ * t⁻¹) * (t * x) := by group
          _ = t * x := by rw [h1, one_mul]
      rw [← hxt]
      group
    have hRt : R ≤ conjSub t K := fun x hx => by
      have := conj_mem_conjSub (n := t) (hRK hx)
      rwa [hcR x hx] at this
    have hKt : conjSub t K ∈ Ω := hΩ.conjInvariant t K hK
    have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
    have h8 := hΩ.eight_le_of_mem_RSet hRΩ
    obtain ⟨m', hm'⟩ := hRsyl.2.1.exists_card_eq
    have hm3 : 3 ≤ m' := by
      have h8' : 2 ^ 3 ≤ 2 ^ m' := by rw [← hm']; exact h8
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h8'
    have hdvd : 8 ∣ Nat.card ↥(K ⊓ conjSub t K) := by
      have h1 : Nat.card R ∣ Nat.card ↥(K ⊓ conjSub t K) :=
        Subgroup.card_dvd_of_le (le_inf hRK hRt)
      have h2 : 8 ∣ Nat.card R := by
        rw [hm']
        exact (pow_dvd_pow 2 hm3 : 2 ^ 3 ∣ 2 ^ m')
      exact h2.trans h1
    have h3 : 3 ≤ padicValNat 2 (Nat.card ↥(K ⊓ conjSub t K)) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (by simpa using hdvd)
    have h4 := (hΩ.omega4 K hK (conjSub t K) hKt (Ne.symm hne)).1
    omega
  have hY₁𝒞 : Y₁ ∈ 𝒞 := ⟨hY₁Y.trans hYH, hKY₁, hclaim⟩
  have hcard : Nat.card Y ≤ Nat.card Y₁ := hYmin Y₁ hY₁𝒞
  have hY₁eq : Y₁ = Y := Subgroup.eq_of_le_of_card_ge hY₁Y hcard
  exact ⟨Y, hYH, hKY, ⟨y₀, hy₀Y, hy₀⟩, hY₁eq⟩

end Red

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
