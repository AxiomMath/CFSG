module

public import CFSG.CGT.PushingUpLit.T2KSW.FieldAutHarada
import CFSG.CGT.PushingUpLit.T2KSW.FieldAutCount
import CFSG.CGT.PushingUpLit.LIT.A4.T211Proof

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KR CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.JonesParshall
open scoped commutatorElement
open Aux Syl

namespace NS

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem two_mul_card_le_of_not_wleVE (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) :
    2 * ((2 ^ n) ^ 2 * Nat.card ↥(Ec L T)) ≤ Nat.card ↥(oTwoIn L ⊔ Ec L T) := by
  have hlt : blockU L ⊔ Ec L T < oTwoIn L ⊔ Ec L T := by
    refine lt_of_le_of_ne (sup_le_sup_right (blockU_le_oTwoIn L) _) fun h => hNS ?_
    exact le_sup_left.trans h.ge
  have := two_mul_card_le_of_lt hlt
  rwa [card_sup_blockU_Ec hs hE1] at this

theorem two_mul_card_le_family (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsFamily L T A) :
    2 * ((2 ^ n) ^ 2 * Nat.card ↥(Ec L T)) ≤ Nat.card ↥A :=
  (two_mul_card_le_of_not_wleVE hs hE1 hNS).trans (Subgroup.card_le_of_le hA.WE_le)

theorem exists_two_roots (hT : IsSylowOf 2 T M) (H : CoordData G L M n) (hA : H.Adapted T)
    {X : Subgroup G} (hX : X ≤ Rl L T ⊔ Dc L T) (h3 : 3 ≤ (X ⊓ Dc L T).relIndex X) :
    ∃ (r₁ r₂ q₁ q₂ : G) (hr₁ : r₁ ∈ Rl L T) (hr₂ : r₂ ∈ Rl L T) (s₁ s₂ : Fq n),
      r₁ * q₁ ∈ X ∧ r₂ * q₂ ∈ X ∧ q₁ ∈ Dc L T ∧ q₂ ∈ Dc L T ∧
      H.D.φ ⟨r₁, hr₁.2⟩ = uMat s₁ ∧ H.D.φ ⟨r₂, hr₂.2⟩ = uMat s₂ ∧ s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      s₁ ≠ s₂ := by
  classical
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc H.normal hT.le)
  have hcard : 3 ≤ Nat.card (↥X ⧸ (X ⊓ Dc L T).subgroupOf X) := by
    rw [← Subgroup.index_eq_card]
    exact h3
  have : Fintype (↥X ⧸ (X ⊓ Dc L T).subgroupOf X) := Fintype.ofFinite _
  have h3' : 2 < Fintype.card (↥X ⧸ (X ⊓ Dc L T).subgroupOf X) := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3'
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨x₃, rfl⟩ := QuotientGroup.mk_surjective c
  have hq : ∀ x y : ↥X, (x : G)⁻¹ * (y : G) ∈ Dc L T →
      (QuotientGroup.mk x : ↥X ⧸ (X ⊓ Dc L T).subgroupOf X) = QuotientGroup.mk y := by
    intro x y hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact ⟨X.mul_mem (X.inv_mem x.2) y.2, hxy⟩
  have hdec : ∀ x : ↥X, ∃ r ∈ Rl L T, ∃ q ∈ Dc L T, (x : G) = r * q := fun x =>
    (mem_sup_iff_mul hRn).1 (hX x.2)
  choose r hr q hqD hxrq using hdec
  have hrL : ∀ x : ↥X, r x ∈ L := fun x => (hr x).2
  have hs : ∀ x : ↥X, ∃ s : Fq n, H.D.φ ⟨r x, hrL x⟩ = uMat s := fun x =>
    hA (r x) (hrL x) (hr x).1
  choose s hsφ using hs
  have hsne : ∀ x y : ↥X, (QuotientGroup.mk x : ↥X ⧸ (X ⊓ Dc L T).subgroupOf X) ≠
      QuotientGroup.mk y → s x ≠ s y := by
    intro x y hxy hss
    apply hxy
    apply hq
    have hφ : H.D.φ ⟨(r x)⁻¹ * r y, mul_mem (inv_mem (hrL x)) (hrL y)⟩ = 1 := by
      have e : (⟨(r x)⁻¹ * r y, mul_mem (inv_mem (hrL x)) (hrL y)⟩ : ↥L) =
          (⟨r x, hrL x⟩ : ↥L)⁻¹ * ⟨r y, hrL y⟩ := rfl
      rw [e, map_mul, map_inv, hsφ x, hsφ y, hss, inv_mul_cancel]
    have hW : (r x)⁻¹ * r y ∈ oTwoIn L := (H.D.φ_ker _).1 hφ
    have hWD : (r x)⁻¹ * r y ∈ Dc L T := oTwoIn_le_Dc H.nat H.le H.normal hT hW
    have hxy' : (x : G)⁻¹ * (y : G) = (q x)⁻¹ * ((r x)⁻¹ * r y) * q y := by
      rw [hxrq x, hxrq y]
      group
    rw [hxy']
    exact mul_mem (mul_mem (inv_mem (hqD x)) hWD) (hqD y)
  have hs12 := hsne x₁ x₂ hab
  have hs13 := hsne x₁ x₃ hac
  have hs23 := hsne x₂ x₃ hbc
  have hmem : ∀ x : ↥X, r x * q x ∈ X := fun x => by
    rw [← hxrq x]
    exact x.2
  by_cases h1 : s x₁ = 0
  · exact ⟨r x₂, r x₃, q x₂, q x₃, hr x₂, hr x₃, s x₂, s x₃, hmem x₂, hmem x₃, hqD x₂, hqD x₃,
      hsφ x₂, hsφ x₃, fun h => hs12 (h1.trans h.symm), fun h => hs13 (h1.trans h.symm), hs23⟩
  · by_cases h2 : s x₂ = 0
    · exact ⟨r x₁, r x₃, q x₁, q x₃, hr x₁, hr x₃, s x₁, s x₃, hmem x₁, hmem x₃, hqD x₁, hqD x₃,
        hsφ x₁, hsφ x₃, h1, fun h => hs23 (h2.trans h.symm), hs13⟩
    · exact ⟨r x₁, r x₂, q x₁, q x₂, hr x₁, hr x₂, s x₁, s x₂, hmem x₁, hmem x₂, hqD x₁, hqD x₂,
        hsφ x₁, hsφ x₂, h1, h2, hs12⟩


theorem false_of_three_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsFamily L T A)
    {B : Subgroup G} (hBT : B ≤ Rl L T ⊔ Dc L T) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = Nat.card A) (h3 : 3 ≤ (B ⊓ Dc L T).relIndex B) : False := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  obtain ⟨H, hAd⟩ := exists_utri_coord h hLM hMN hT
  obtain ⟨r₁, r₂, q₁, q₂, hr₁, hr₂, s₁, s₂, hx₁, hx₂, hq₁, hq₂, hφ₁, hφ₂, hs₁, hs₂, hs12⟩ :=
    exists_two_roots hT H hAd hBT h3
  set K : Subgroup G := B ⊓ Dc L T with hK
  have hKD : K ≤ Dc L T := inf_le_right
  have hKB : K ≤ B := inf_le_left
  have hKQ : K ≤ Qc L M := hKD.trans (Dc_le_Qc hT)
  have hKc₁ : ∀ u ∈ K, (r₁ * q₁) * u = u * (r₁ * q₁) := fun u hu => hcomm _ hx₁ u hu.1
  have hKc₂ : ∀ u ∈ K, (r₂ * q₂) * u = u * (r₂ * q₂) := fun u hu => hcomm _ hx₂ u hu.1
  have hθ0 : ∀ u ∈ K, thetaG H u = 0 := fun u hu =>
    (two_roots_algebra hs₁ hs₂ hs12 (rel_of_comm H hT (hKD hu) hr₁ hq₁ hφ₁ (hKc₁ u hu))
      (rel_of_comm H hT (hKD hu) hr₂ hq₂ hφ₂ (hKc₂ u hu))).2
  have hθ1 := card_thetaRange_eq_one_of K hKQ hθ0
  have hn0 : n ≠ 0 := by have := h.two_le; omega
  have hFcard : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n hn0
  have hq : Nat.card K ≤ Nat.card ↥(Ec L T) * 2 ^ n := by
    have hcnt : Nat.card K ≤ Nat.card ↥(K ⊓ Ec L T) *
        (Nat.card (Fq n) * Nat.card ↥(thetaHom H K hKQ).range) :=
      (count_comm H hT hr₁ hq₁ hφ₁ hs₁ hKD hKc₁).1
    rw [hθ1, hFcard, mul_one] at hcnt
    exact hcnt.trans (Nat.mul_le_mul_right _ (Subgroup.card_le_of_le inf_le_right))
  have hp : (B ⊓ Dc L T).relIndex B ≤ 2 ^ n := by
    rw [Subgroup.inf_relIndex_left, ← relIndex_Dc_Rl_sup_Dc hs hE1]
    exact Subgroup.relIndex_le_of_le_right hBT (by
      rw [relIndex_Dc_Rl_sup_Dc hs hE1]
      positivity)
  have hBK : (B ⊓ Dc L T).relIndex B * Nat.card K = Nat.card B := by
    have := Subgroup.relIndex_mul_card (H := K) (K := B)
    rwa [inf_of_le_left hKB] at this
  have hB : Nat.card B ≤ (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) :=
    calc Nat.card B = (B ⊓ Dc L T).relIndex B * Nat.card K := hBK.symm
      _ ≤ 2 ^ n * (Nat.card ↥(Ec L T) * 2 ^ n) := Nat.mul_le_mul hp hq
      _ = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by ring
  have hA2 := two_mul_card_le_family hs hE1 hNS hA
  have hepos : 0 < Nat.card ↥(Ec L T) := Nat.card_pos
  have hpos : 0 < (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by positivity
  omega


theorem thetaG_eq_zero_or_of_mem_sup (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (H : CoordData G L M n) {w₁ : G} (hw₁ : w₁ ∈ oTwoIn L) (hw₁V : w₁ ∉ blockU L) {y : G}
    (hy : y ∈ oTwoIn L ⊔ Ec L T) : thetaG H y = 0 ∨ thetaG H y = thetaG H w₁ := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  have hWQ : ∀ w ∈ oTwoIn L, w ∈ Qc L M := fun w hw => by
    have hwD := oTwoIn_le_Dc h hLM hMN hT hw
    exact ⟨hT.le hwD.1, hwD.2⟩
  have hWn : oTwoIn L ≤ Subgroup.normalizer (Ec L T : Set G) := fun w hw =>
    mem_normalizer_of_forall_comm fun e he => oTwoIn_Ec_comm hw he
  obtain ⟨w, hw, e, he, rfl⟩ := (mem_sup_iff_mul hWn).1 hy
  have heQ : e ∈ Qc L M := ⟨hT.le he.1, Subgroup.centralizer_le
    (SetLike.coe_subset_coe.2 (blockU_le L)) he.2⟩
  rw [thetaG_mul H (hWQ w hw) heQ, (coordsG_of_mem_Ec H hT he).2, add_zero]
  by_cases hwV : w ∈ blockU L
  · exact Or.inl (coordsG_blockU H hwV).2
  · refine Or.inr ?_
    have hlt : blockU L < oTwoIn L :=
      lt_of_le_of_ne (blockU_le_oTwoIn L) fun h' => hwV (h' ▸ hw)
    have hmem := mul_inv_mem_of_card_le_two_mul hlt (card_oTwoIn_le_two_mul h) hw hwV hw₁ hw₁V
    have h0 : thetaG H (w * w₁⁻¹) = 0 := (coordsG_blockU H hmem).2
    rw [thetaG_mul H (hWQ w hw) ((Qc L M).inv_mem (hWQ w₁ hw₁)), thetaG_inv H (hWQ w₁ hw₁)] at h0
    exact add_neg_eq_zero.1 h0

theorem mem_family_of_cent (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {A : Subgroup G}
    (hA : IsMaximalFamily L T A) (hAeq : A = oTwoIn L ⊔ Ec L T) {d : G} (hd : d ∈ Dc L T)
    (hdc : ∀ e ∈ Ec L T, d * e = e * d) : d ∈ A := by
  have hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := Dc_centralizes_oTwoIn hs hE1
  have hle : A ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hAeq]
    refine sup_le (fun w hw => ?_) (fun e he => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hWD w hw d hd
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hdc e he).symm
  rw [← family_Dc_inf_centralizer_eq hs hE1 hA]
  refine ⟨hd, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)

theorem false_of_le_two (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsMaximalFamily L T A)
    {B : Subgroup G} (hBT : B ≤ Rl L T ⊔ Dc L T) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = Nat.card A) (hBD : ¬ B ≤ Dc L T)
    (h2 : (B ⊓ Dc L T).relIndex B ≤ 2) : False := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  obtain ⟨H, hAd⟩ := exists_utri_coord h hLM hMN hT
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  obtain ⟨x, hxB, hxD⟩ := Set.not_subset.1 hBD
  obtain ⟨r, hr, q', hq', hxe⟩ := (mem_sup_iff_mul hRn).1 (hBT hxB)
  obtain ⟨s, hφ⟩ := hAd r hr.2 hr.1
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hxD
    have hφ1 : H.D.φ ⟨r, hr.2⟩ = 1 := by rw [hφ, uMat_zero]
    have hrW : r ∈ oTwoIn L := (H.D.φ_ker ⟨r, hr.2⟩).1 hφ1
    rw [hxe]
    exact (Dc L T).mul_mem (oTwoIn_le_Dc h hLM hMN hT hrW) hq'
  set K : Subgroup G := B ⊓ Dc L T with hK
  have hKD : K ≤ Dc L T := inf_le_right
  have hKB : K ≤ B := inf_le_left
  have hKQ : K ≤ Qc L M := hKD.trans (Dc_le_Qc hT)
  have hKc : ∀ u ∈ K, (r * q') * u = u * (r * q') := fun u hu => by
    rw [← hxe]
    exact hcomm x hxB u hu.1
  have hidx2 : K.relIndex B = 2 := by
    have h1 : K.relIndex B ≠ 1 := fun h' => hxD (((Subgroup.relIndex_eq_one.1 h') hxB).2)
    have h0 : K.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hBK : Nat.card B = 2 * Nat.card K := by
    have := Subgroup.relIndex_mul_card (H := K) (K := B)
    rw [hidx2, inf_of_le_left hKB] at this
    exact this.symm
  have hKE : K ⊓ Ec L T = B ⊓ Ec L T := by
    ext y
    simp only [Subgroup.mem_inf, hK]
    constructor
    · rintro ⟨⟨hyB, -⟩, hyE⟩
      exact ⟨hyB, hyE⟩
    · rintro ⟨hyB, hyE⟩
      exact ⟨⟨hyB, Ec_le_Dc hyE⟩, hyE⟩
  have hcnt := (count_comm H hT hr hq' hφ hs0 hKD hKc).1
  rw [hKE] at hcnt
  have hn0 : n ≠ 0 := by have := h.two_le; omega
  have hFcard : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n hn0
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hqpos : 0 < 2 ^ n := by omega
  have hepos : 0 < Nat.card ↥(Ec L T) := Nat.card_pos
  have hθk : Nat.card ↥(thetaHom H K hKQ).range ≤ 2 ^ n :=
    (card_thetaRange_le H K hKQ).trans hFcard.le
  have hEBle : Nat.card ↥(B ⊓ Ec L T) ≤ Nat.card ↥(Ec L T) :=
    Subgroup.card_le_of_le inf_le_right
  have hF1 : Nat.card K ≤ Nat.card ↥(B ⊓ Ec L T) *
      (2 ^ n * Nat.card ↥(thetaHom H K hKQ).range) := by
    rwa [hFcard] at hcnt
  have hA2 := two_mul_card_le_family hs hE1 hNS hA.1
  have hkm : 2 * Nat.card K = Nat.card A := by rw [← hcard, hBK]
  have hkupper : Nat.card K ≤ (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) :=
    calc Nat.card K ≤ Nat.card ↥(B ⊓ Ec L T) * (2 ^ n * Nat.card ↥(thetaHom H K hKQ).range) := hF1
      _ ≤ Nat.card ↥(Ec L T) * (2 ^ n * 2 ^ n) :=
        Nat.mul_le_mul hEBle (Nat.mul_le_mul_left _ hθk)
      _ = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by ring
  have hkP : Nat.card K = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by omega
  obtain ⟨hθ, heb, -⟩ := arith_two hqpos hepos hEBle hθk hF1 hkP
  have hAeq : A = oTwoIn L ⊔ Ec L T := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hA.1.WE_le ?_
    have := two_mul_card_le_of_not_wleVE hs hE1 hNS
    omega
  have hEB : B ⊓ Ec L T = Ec L T := Subgroup.eq_of_le_of_card_ge inf_le_right heb.ge
  have hall : ∀ t : Fq n, ∃ u ∈ K, thetaG H u = t :=
    exists_of_card_thetaRange_eq H K hKQ (hθ.trans hFcard.symm)
  obtain ⟨w₁, hw₁W, hw₁V⟩ := Set.not_subset.1 (fun h' : oTwoIn L ≤ blockU L =>
    hNS (h'.trans le_sup_left))
  have hKA : ∀ u ∈ K, u ∈ oTwoIn L ⊔ Ec L T := fun u hu => by
    rw [← hAeq]
    refine mem_family_of_cent hs hE1 hA hAeq (hKD hu) fun e he => ?_
    have heB : e ∈ B := (show e ∈ B ⊓ Ec L T by rw [hEB]; exact he).1
    exact hcomm u hu.1 e heB
  have h2v : ∀ t : Fq n, t = 0 ∨ t = thetaG H w₁ := fun t => by
    obtain ⟨u, hu, rfl⟩ := hall t
    exact thetaG_eq_zero_or_of_mem_sup hs hE1 H hw₁W hw₁V (hKA u hu)
  have hsurj : Function.Surjective (fun b : Bool => if b then (0 : Fq n) else thetaG H w₁) := by
    intro t
    rcases h2v t with h0 | h0
    · exact ⟨true, by simp [h0]⟩
    · exact ⟨false, by simp [h0]⟩
  have hle2 : Nat.card (Fq n) ≤ 2 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  omega


theorem le_Dc_of_card_eq (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsMaximalFamily L T A)
    {B : Subgroup G} (hBT : B ≤ Rl L T ⊔ Dc L T) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = Nat.card A) : B ≤ Dc L T := by
  by_contra hBD
  by_cases h3 : 3 ≤ (B ⊓ Dc L T).relIndex B
  · exact false_of_three_le hs hE1 hNS hA.1 hBT hcomm hcard h3
  · exact false_of_le_two hs hE1 hNS hA hBT hcomm hcard hBD (by omega)

theorem sylow_type_of_not_wleVE (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsMaximalFamily L T A)
    (hCNT : LemmaCNT L T A) {g : G} (hg : A.map (MulAut.conj g).toMonoidHom ≤ M) :
    ∃ m ∈ M, A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj m).toMonoidHom := by
  have hAT : A ≤ T := hA.1.le_Dc.trans Dc_le_T
  have hP : IsPGroup 2 ↥(A.map (MulAut.conj g).toMonoidHom) :=
    (hs.sylow.isPGroup.to_le hAT).map _
  obtain ⟨k, hkM, hkT⟩ := exists_conj_le_of_isPGroup hs.sylow hP hg
  set g' : G := k * g with hg'
  set B : Subgroup G := A.map (MulAut.conj g').toMonoidHom with hB
  have hBeq : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom = B := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [hg', MulAut.conj_apply, mul_assoc]
  have hBT : B ≤ T := hBeq ▸ hkT
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g' * a * g'⁻¹ * (g' * b * g'⁻¹) = g' * (a * b) * g'⁻¹ := by group
      _ = g' * (b * a) * g'⁻¹ := by rw [hA.1.comm a ha b hb]
      _ = g' * b * g'⁻¹ * (g' * a * g'⁻¹) := by group
  have hcard : Nat.card B = Nat.card A := card_map_conj A g'
  have hg'M : g' ∈ M := by
    by_cases hT1 : B ≤ Rl L T ⊔ Dc L T
    · exact mem_of_map_conj_le_Dc hs hE1 hA (le_Dc_of_card_eq hs hE1 hNS hA hT1 hcomm hcard)
    · exact absurd (hCNT B hBT hcomm hT1).1 (by rw [hcard]; exact lt_irrefl _)
  have hgM : g ∈ M := by
    have := M.mul_mem (M.inv_mem hkM) hg'M
    simpa [hg'] using this
  exact ⟨g, hgM, rfl⟩

end NS

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem t_le_rd_of_not_wleVE_of_cnt (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsMaximalFamily L T A)
    (hCNT : LemmaCNT L T A) : T ≤ Rl L T ⊔ Dc L T := by
  by_contra hTT
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  let H : CoordData G L M n := ⟨h.natData, h, hLM, hMN⟩
  let f : ↥M →* (GaloisField 2 n ≃ₐ[ZMod 2] GaloisField 2 n) :=
    (Har.toGalHom n).comp (WeakCl.chi H)
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  have hfT1 : ∀ y : ↥M, (y : G) ∈ Rl L T ⊔ Dc L T → f y = 1 := by
    intro y hy
    obtain ⟨r, hr, d, hd, hyrd⟩ := (mem_sup_iff_mul hRn).1 hy
    have hr1 : WeakCl.chi H ⟨r, hLM hr.2⟩ = 1 := WeakCl.chi_of_mem_L H hr.2
    have hdc : d ∈ cenW L M := by
      have := hd
      rw [Dc_eq_inf_cenW h hMN hT] at this
      exact this.2
    have hd1 : WeakCl.chi H ⟨d, hT.le hd.1⟩ = 1 := WeakCl.chi_of_mem_cenW H hdc
    have hy' : y = ⟨r, hLM hr.2⟩ * ⟨d, hT.le hd.1⟩ := Subtype.ext hyrd
    rw [MonoidHom.comp_apply, hy', map_mul, hr1, hd1, mul_one, map_one]
  have hf : ∃ x : ↥M, (x : G) ∈ T ∧ f x ≠ 1 := by
    obtain ⟨x, hxT, hxn⟩ := Set.not_subset.1 hTT
    refine ⟨⟨x, hT.le hxT⟩, hxT, fun h1 => hxn ?_⟩
    have hchi : WeakCl.chi H ⟨x, hT.le hxT⟩ = 1 := by
      apply toGal_injective n
      have := h1
      rw [MonoidHom.comp_apply] at this
      rw [toGal_one n]
      exact this
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨x, hxT⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hK := WeakCl.mem_K_of_chi_eq_one H (hT.le hxT) hk' hchi
    rw [← inf_sup_cenW h hLM hMN hT]
    exact ⟨hxT, hK⟩
  obtain ⟨M₁, hM₁M, hrel2, hM₁N, hker, -⟩ := Har.exists_index_two hT f hf
  have hT₁M₁ : Rl L T ⊔ Dc L T ≤ M₁ := fun y hy =>
    hker ⟨y, hT.le (sup_le Rl_le_T Dc_le_T hy)⟩ (hfT1 _ hy)
  have hAT : A ≤ T := hA.1.le_Dc.trans Dc_le_T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hidx, hnot⟩ := A4.haradaTransfer211 G (Har.noTwoQuotient_of_sec4 hs) M M₁ T A
    hM₁M hrel2 hT.le hT.isPGroup ((isSylowOf_iff.1 hT).2.2) hAT
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hAT).2 hA.1.normal) hA.1.comm
    (fun a ha => family_pow_four_eq_one hs hE1 hA.1 ha) (family_normalizer_le hs hE1 hA.1)
    (fun g hg => NS.sylow_type_of_not_wleVE hs hE1 hNS hA hCNT hg)
  exact Har.false_of_transfer hs hA.1 hCNT hM₁N hT₁M₁ hidx hnot

theorem t_le_rd_of_not_wleVE (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (_hA78 : Aschbacher78OneGen) (hE : Ec L T ≠ ⊥) (hNS : ¬ oTwoIn L ≤ blockU L ⊔ Ec L T) :
    T ≤ Rl L T ⊔ Dc L T := by
  obtain ⟨A, hA⟩ := exists_isMaximalFamily hs hE1
  exact t_le_rd_of_not_wleVE_of_cnt hs hE1 hNS hA (cnt_of_maximal hs hE1 hE hA)

theorem t_le_rd_all (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hA78 : Aschbacher78OneGen) (hE : Ec L T ≠ ⊥) : T ≤ Rl L T ⊔ Dc L T := by
  by_cases hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T
  · exact t_le_rd hs hE1 hA78 hE hWVE
  · exact t_le_rd_of_not_wleVE hs hE1 hA78 hE hWVE

end CFSG.CGT.PushingUpLit.T2KSW
