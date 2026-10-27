module

public import CFSG.GH74.Generic.BProg.B3.S3Rk2Rank
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Basic
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig6
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CommutingElementaryProduct
public import CFSG.GH74.KGroups.L34Tables
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace S3Rk2Basic

section Sup

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer {N H : Subgroup G} (hH : H ≤ normalizer (N : Set G))
    {g : G} (hg : g ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, g = n * h := by
  have hconj : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun h hh n hn =>
    (Subgroup.mem_normalizer_iff.1 (hH hh) n).1 hn
  let S : Subgroup G :=
    { carrier := {g | ∃ n ∈ N, ∃ h ∈ H, g = n * h}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, h₁, hh₁, rfl⟩ ⟨n₂, hn₂, h₂, hh₂, rfl⟩
        refine ⟨n₁ * (h₁ * n₂ * h₁⁻¹), mul_mem hn₁ (hconj h₁ hh₁ n₂ hn₂), h₁ * h₂, mul_mem hh₁ hh₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, h, hh, rfl⟩
        refine ⟨h⁻¹ * n⁻¹ * h⁻¹⁻¹, ?_, h⁻¹, inv_mem hh, ?_⟩
        · exact hconj h⁻¹ (inv_mem hh) n⁻¹ (inv_mem hn)
        · group }
  have hle : N ⊔ H ≤ S := sup_le (fun n hn => ⟨n, hn, 1, one_mem _, by simp⟩)
    (fun h hh => ⟨1, one_mem _, h, hh, by simp⟩)
  exact hle hg

theorem isElementaryAbelian_sup {H K : Subgroup G}
    (hH : CFSG.IsElementaryAbelian 2 ↥H)
    (hK : CFSG.IsElementaryAbelian 2 ↥K) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    CFSG.IsElementaryAbelian 2 ↥(H ⊔ K) := by
  have hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥H) ⟨b, hb⟩)
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥K) ⟨b, hb⟩)
  have hHs : ∀ a ∈ H, a * a = 1 := fun a ha => by
    rw [← sq]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := H) a ha
  have hKs : ∀ a ∈ K, a * a = 1 := fun a ha => by
    rw [← sq]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := K) a ha
  refine C3.Layer1.Back.isElementaryAbelian_of_forall ?_ ?_
  · intro u hu v hv
    obtain ⟨h, hh, k, hk, rfl⟩ := S3Rk1Basic.exists_mul_of_mem_sup hc hu
    obtain ⟨h', hh', k', hk', rfl⟩ := S3Rk1Basic.exists_mul_of_mem_sup hc hv
    calc h * k * (h' * k') = h * (k * h') * k' := by group
      _ = h * (h' * k) * k' := by rw [← hc h' hh' k hk]
      _ = h * h' * (k * k') := by group
      _ = h' * h * (k' * k) := by rw [hHc h hh h' hh', hKc k hk k' hk']
      _ = h' * (h * k') * k := by group
      _ = h' * (k' * h) * k := by rw [hc h hh k' hk']
      _ = h' * k' * (h * k) := by group
  · intro u hu
    obtain ⟨h, hh, k, hk, rfl⟩ := S3Rk1Basic.exists_mul_of_mem_sup hc hu
    calc h * k * (h * k) = h * (k * h) * k := by group
      _ = h * (h * k) * k := by rw [← hc h hh k hk]
      _ = (h * h) * (k * k) := by group
      _ = 1 := by rw [hHs h hh, hKs k hk, one_mul]

end Sup

structure KCData {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup G) : Prop where
  comp : IsPCompIn 2 (centralizer ({x} : Set G)) K
  ord : orderOf x = 2
  shape : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)
  rank1 : pRank 2 ↥(CxK x K) ≤ 1

namespace KCData

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem le_centralizer (d : KCData x K) : K ≤ centralizer ({x} : Set G) := d.comp.1

theorem center_trivial (d : KCData x K) :
    ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1 :=
  B1.PilotS3.center_trivial_of_shape3 d.comp d.shape

theorem x_mem_cxk (d : KCData x K) : x ∈ CxK x K := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, ?_⟩
  exact C3.Layer1.Back.mem_centralizerSection_of_centralizes
    (fun k hk => (Subgroup.mem_centralizer_singleton_iff.1 (d.le_centralizer hk)).symm)
    Th2Sig6.pPrimeCoreOf_le

omit [Finite G] in
theorem cxk_le_centralizer : CxK x K ≤ centralizer ({x} : Set G) := inf_le_left

omit [Finite G] in
theorem cxk_le_normalizer : CxK x K ≤ normalizer (K : Set G) := fun _ hc =>
  (Subgroup.mem_inf.1 hc).2.1

theorem inf_cxk_le (d : KCData x K) {c : G} (hcC : c ∈ CxK x K) (hcK : c ∈ K) :
    c ∈ pPrimeCoreOf 2 K := by
  have hcs : c ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.1 hcC).2
  set c' : ↥K := ⟨c, hcK⟩ with hc'
  have hcomm : ∀ g : ↥K ⧸ pPrimeCore 2 ↥K,
      g * (QuotientGroup.mk c' : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk c' * g := by
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : ⁅(k : G), c⁆ ∈ pPrimeCoreOf 2 K := hcs.2.2 (k : G) k.2
    obtain ⟨o, ho, hoe⟩ := h1
    have hoeq : o = ⁅k, c'⁆ := Subtype.ext hoe
    have h2 : (QuotientGroup.mk ⁅k, c'⁆ : ↥K ⧸ pPrimeCore 2 ↥K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hoeq ▸ ho)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have h3 : (QuotientGroup.mk (k * c') : ↥K ⧸ pPrimeCore 2 ↥K) =
        QuotientGroup.mk (c' * k) := by
      have h4 : ⁅k, c'⁆ = k * c' * k⁻¹ * c'⁻¹ := rfl
      have : k * c' = ⁅k, c'⁆ * (c' * k) := by rw [h4]; group
      rw [this, QuotientGroup.mk_mul, h2, one_mul]
    exact h3
  have hz := d.center_trivial _ hcomm
  have hc1 : c' ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 hz
  exact ⟨c', hc1, rfl⟩

theorem invol_cxk (d : KCData x K) {u : G} (hu : u ∈ CxK x K) (hu2 : u * u = 1) :
    u = 1 ∨ u = x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hu1, hux⟩ := hcon
  have hxC := d.x_mem_cxk
  have hu2' : orderOf u = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hcomm : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.1
    (cxk_le_centralizer (x := x) (K := K) hu)
  have hx2 := d.ord
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      (x := (⟨u, hu⟩ : ↥(CxK x K))) (y := ⟨x, hxC⟩) (by rw [Subgroup.orderOf_mk]; exact hu2')
      (by rw [Subgroup.orderOf_mk]; exact hx2) (Subtype.ext hcomm)
      (fun h => hux (congrArg Subtype.val h))
  have := CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two V hV (k := 2) (by rw [hVcard]; norm_num)
  have h1 := d.rank1
  omega

theorem decomp_cxk (d : KCData x K) {c : G} (hc : c ∈ CxK x K) (hc2 : c * c ∈ pPrimeCoreOf 2 K) :
    ∃ o ∈ pPrimeCoreOf 2 K, c = o ∨ c = o * x := by
  classical
  have hodd : Odd (Nat.card (pPrimeCoreOf 2 K)) := TwoThin.card_pPrimeCoreOf_odd K
  obtain ⟨j, hj⟩ := hodd
  have hpow : (c * c) ^ Nat.card (pPrimeCoreOf 2 K) = 1 := by
    have h := pow_card_eq_one' (G := ↥(pPrimeCoreOf 2 K)) (x := ⟨c * c, hc2⟩)
    have h2 := congrArg (fun z : ↥(pPrimeCoreOf 2 K) => (z : G)) h
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  set c₂ : G := c ^ Nat.card (pPrimeCoreOf 2 K) with hc₂
  have hc₂C : c₂ ∈ CxK x K := Subgroup.pow_mem _ hc _
  have hc₂sq : c₂ * c₂ = 1 := by
    rw [hc₂, ← pow_add, ← two_mul, pow_mul, sq]
    exact hpow
  have hcoc : c₂ = (c * c) ^ j * c := by
    rw [hc₂, hj, pow_succ, pow_mul, sq]
  refine ⟨((c * c) ^ j)⁻¹, inv_mem (Subgroup.pow_mem _ hc2 _), ?_⟩
  have hc' : c = ((c * c) ^ j)⁻¹ * c₂ := by
    rw [hcoc]; group
  rcases d.invol_cxk hc₂C hc₂sq with h1 | h1
  · left
    exact hc'.trans (by rw [h1, mul_one])
  · right
    exact hc'.trans (by rw [h1])

theorem invol_mem_sup (d : KCData x K) {b : G} (hb : b ∈ K ⊔ CxK x K) (hb2 : b * b = 1) :
    b ∈ K ∨ ∃ k ∈ K, b = k * x := by
  obtain ⟨k, hk, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (N := K) (H := CxK x K) cxk_le_normalizer hb
  have hcN : c ∈ normalizer (K : Set G) := cxk_le_normalizer hc
  have hc2K : c * c ∈ K := by
    have h1 : c * c = (c * k⁻¹ * c⁻¹) * k⁻¹ := by
      have : c * k * c = k⁻¹ := by
        have h2 : k * c * (k * c) = 1 := hb2
        calc c * k * c = k⁻¹ * (k * c * (k * c)) := by group
          _ = k⁻¹ := by rw [h2, mul_one]
      calc c * c = (c * k⁻¹ * c⁻¹) * (c * k * c) := by group
        _ = (c * k⁻¹ * c⁻¹) * k⁻¹ := by rw [this]
    rw [h1]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 hcN _).1 (K.inv_mem hk)) (K.inv_mem hk)
  have hc2C : c * c ∈ CxK x K := mul_mem hc hc
  have hc2O : c * c ∈ pPrimeCoreOf 2 K := d.inf_cxk_le hc2C hc2K
  obtain ⟨o, ho, hco | hco⟩ := decomp_cxk d hc hc2O
  · left
    rw [hco]
    exact K.mul_mem hk (Th2Sig6.pPrimeCoreOf_le ho)
  · right
    refine ⟨k * o, K.mul_mem hk (Th2Sig6.pPrimeCoreOf_le ho), ?_⟩
    rw [hco, mul_assoc]

theorem elemAb_le_sup (d : KCData x K) {B : Subgroup G} (hBM : B ≤ K ⊔ CxK x K)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB8 : Nat.card ↥B = 8) :
    x ∈ B ∧ CFSG.IsElementaryAbelian 2 ↥(B ⊓ K) ∧ Nat.card ↥(B ⊓ K) = 4 ∧
      B = (B ⊓ K) ⊔ zpowers x := by
  classical
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha c hc => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)
  have hBs : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
    rwa [sq] at this
  have hx2 := d.ord
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hKx : ∀ k ∈ K, k * x = x * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (d.le_centralizer hk)
  set F : Subgroup G := B ⊓ K with hF
  have hFel : CFSG.IsElementaryAbelian 2 ↥F := Th2Sig6.isElementaryAbelian_of_le hBel inf_le_left
  have hF4le : Nat.card ↥F ≤ 4 := S3Rk2Rank.card_le_four_of_le d.shape inf_le_right hFel
  have hdec : ∀ b ∈ B, b ∈ K ∨ ∃ k ∈ K, b = k * x := fun b hb =>
    invol_mem_sup d (hBM hb) (hBs b hb)
  obtain ⟨b₀, hb₀B, hb₀K⟩ : ∃ b₀ ∈ B, b₀ ∉ K := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ K := hcon
    have := S3Rk2Rank.card_le_four_of_le d.shape hle hBel
    omega
  obtain ⟨k₀, hk₀K, hb₀e⟩ := (hdec b₀ hb₀B).resolve_left hb₀K
  have hcover : ∀ b ∈ B, b ∈ F ∨ b₀⁻¹ * b ∈ F := by
    intro b hb
    rcases hdec b hb with hbK | ⟨k, hkK, hbe⟩
    · exact Or.inl ⟨hb, hbK⟩
    · refine Or.inr ⟨B.mul_mem (B.inv_mem hb₀B) hb, ?_⟩
      have h1 : b₀⁻¹ * b = k₀⁻¹ * k := by
        rw [hb₀e, hbe]
        have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
        calc (k₀ * x)⁻¹ * (k * x) = x⁻¹ * k₀⁻¹ * (k * x) := by group
          _ = x * (k₀⁻¹ * k) * x := by rw [hxi]; group
          _ = (k₀⁻¹ * k) * x * x := by
              rw [← hKx (k₀⁻¹ * k) (K.mul_mem (K.inv_mem hk₀K) hkK)]
          _ = k₀⁻¹ * k := by rw [mul_assoc, hxx, mul_one]
      rw [h1]
      exact K.mul_mem (K.inv_mem hk₀K) hkK
  have hcard8 : 8 ≤ 2 * Nat.card ↥F := by
    have hsub : (B : Set G) ⊆ (F : Set G) ∪ (fun f => b₀ * f) '' (F : Set G) := by
      intro b hb
      rcases hcover b hb with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨b₀⁻¹ * b, h1, by group⟩
    have hfin : ((F : Set G) ∪ (fun f => b₀ * f) '' (F : Set G)).Finite := Set.toFinite _
    have h1 : (B : Set G).ncard ≤ ((F : Set G) ∪ (fun f => b₀ * f) '' (F : Set G)).ncard :=
      Set.ncard_le_ncard hsub hfin
    have h2 := Set.ncard_union_le (F : Set G) ((fun f => b₀ * f) '' (F : Set G))
    have h3 : ((fun f => b₀ * f) '' (F : Set G)).ncard ≤ (F : Set G).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have e1 : Nat.card ↥B = (B : Set G).ncard := Nat.card_coe_set_eq (B : Set G)
    have e2 : Nat.card ↥F = (F : Set G).ncard := Nat.card_coe_set_eq (F : Set G)
    omega
  have hF4 : Nat.card ↥F = 4 := by omega
  have hk₀sq : k₀ * k₀ = 1 := by
    have h := hBs b₀ hb₀B
    rw [hb₀e] at h
    calc k₀ * k₀ = k₀ * k₀ * (x * x) := by rw [hxx, mul_one]
      _ = (k₀ * x) * (k₀ * x) := by
          rw [mul_assoc k₀ x (k₀ * x), ← mul_assoc x k₀ x, ← hKx k₀ hk₀K]; group
      _ = 1 := h
  have hk₀F : ∀ f ∈ F, f * k₀ = k₀ * f := by
    intro f hf
    have h1 := hBc b₀ hb₀B f hf.1
    rw [hb₀e] at h1
    have hfx := hKx f hf.2
    have h2 : k₀ * f * x = f * k₀ * x := by
      calc k₀ * f * x = k₀ * (f * x) := by group
        _ = k₀ * (x * f) := by rw [hfx]
        _ = k₀ * x * f := by group
        _ = f * (k₀ * x) := h1
        _ = f * k₀ * x := by group
    exact (mul_right_cancel h2).symm
  have hsup : CFSG.IsElementaryAbelian 2 ↥(F ⊔ zpowers k₀) :=
    isElementaryAbelian_sup hFel
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hk₀sq))
      (fun f hf k hk => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact (Commute.zpow_right (show Commute f k₀ from hk₀F f hf) n).eq)
  have hsupK : F ⊔ zpowers k₀ ≤ K :=
    sup_le inf_le_right ((Subgroup.zpowers_le).2 hk₀K)
  have hsupc := S3Rk2Rank.card_le_four_of_le d.shape hsupK hsup
  have hFeq : F ⊔ zpowers k₀ = F :=
    (Subgroup.eq_of_le_of_card_ge (le_sup_left) (by omega)).symm
  have hk₀F' : k₀ ∈ F := hFeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers k₀)
  have hxB : x ∈ B := by
    have h1 : x = k₀⁻¹ * b₀ := by rw [hb₀e]; group
    rw [h1]
    exact B.mul_mem (B.inv_mem hk₀F'.1) hb₀B
  refine ⟨hxB, hFel, hF4, le_antisymm ?_ (sup_le inf_le_left ((Subgroup.zpowers_le).2 hxB))⟩
  intro b hb
  rcases hdec b hb with hbK | ⟨k, hkK, hbe⟩
  · exact Subgroup.mem_sup_left ⟨hb, hbK⟩
  · have hbxK : b * x ∈ K := by
      rw [hbe, mul_assoc, hxx, mul_one]
      exact hkK
    have hbxF : b * x ∈ F := ⟨B.mul_mem hb hxB, hbxK⟩
    have : b = (b * x) * x := by rw [mul_assoc, hxx, mul_one]
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hbxF) (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

end KCData

end S3Rk2Basic

end CFSG.GH74.Generic.BProg.B3
