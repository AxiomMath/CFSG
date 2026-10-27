module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl5
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar
public import CFSG.GH74.Generic.S3.V1InnerLib

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

namespace L3Aut

variable {F : Type} [Field F] [Finite F]

theorem commutator_mem_linearAutGroup {n : ℕ} (hn : 3 ≤ n) {p f : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ f) (a b : MulAut (projectiveSL n F)) :
    a * b * a⁻¹ * b⁻¹ ∈ linearAutGroup n F := by
  have htrans := standard_automorphism_transport (K := F) (n := n)
  obtain ⟨hRtop, hgen⟩ := automorphism_generation (K := F) hn
  have hDn := (standard_outer_quotients (K := F) (n := n)).2.2.1
  have hDnorm : (linearAutGroup n F).Normal := by
    refine ⟨fun d hd α => ?_⟩
    have hαR : α ∈ standardAutGroup n F := by rw [hRtop]; exact Subgroup.mem_top _
    have hdR : d ∈ standardAutGroup n F := by rw [hRtop]; exact Subgroup.mem_top _
    have h1 := hDn.conj_mem ⟨d, hdR⟩ (by simpa [Subgroup.mem_subgroupOf] using hd) ⟨α, hαR⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  let mk := QuotientGroup.mk' (linearAutGroup n F)
  have hcA : ∀ C : GL (Fin n) F, mk (conjAut n F C) = 1 := fun C =>
    (QuotientGroup.eq_one_iff _).2 (conjAut_mem_linearAutGroup C)
  have hfield : ∀ σ τ : F ≃+* F, mk (fieldAut n F σ) * mk (fieldAut n F τ) =
      mk (fieldAut n F τ) * mk (fieldAut n F σ) := by
    intro σ τ
    have : IsCyclic (F ≃+* F) := (card_ringAut_and_isCyclic hp F hF).2
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, IsMulCommutative.is_comm.comm σ τ]
  have hδ : dualAut n F * dualAut n F = 1 := htrans.2.2.2.1
  have hδf : ∀ σ : F ≃+* F, mk (dualAut n F) * mk (fieldAut n F σ) =
      mk (fieldAut n F σ) * mk (dualAut n F) := by
    intro σ
    have h1 := htrans.2.2.2.2.2.1 σ
    have h2 : dualAut n F * fieldAut n F σ = fieldAut n F σ * dualAut n F := by
      calc dualAut n F * fieldAut n F σ = (dualAut n F * fieldAut n F σ * dualAut n F) * dualAut n F := by
            rw [mul_assoc (dualAut n F * fieldAut n F σ), hδ, mul_one]
        _ = fieldAut n F σ * dualAut n F := by rw [h1]
    rw [← map_mul, ← map_mul, h2]
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen a
  obtain ⟨B, τ, η, hη, rfl⟩ := hgen b
  have hmk : ∀ (C : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ),
      mk (conjAut n F C * fieldAut n F σ * dualAut n F ^ ε) =
        mk (fieldAut n F σ) * mk (dualAut n F) ^ ε := by
    intro C σ ε
    rw [map_mul, map_mul, hcA, one_mul, map_pow]
  have hcomm : Commute (mk (fieldAut n F σ) * mk (dualAut n F) ^ ε)
      (mk (fieldAut n F τ) * mk (dualAut n F) ^ η) := by
    have h1 : Commute (mk (fieldAut n F σ)) (mk (fieldAut n F τ)) := hfield σ τ
    have h2 : Commute (mk (fieldAut n F σ)) (mk (dualAut n F)) := (hδf σ).symm
    have h3 : Commute (mk (dualAut n F)) (mk (fieldAut n F τ)) := hδf τ
    exact (h1.mul_right (h2.pow_right η)).mul_left ((h3.pow_left ε).mul_right ((Commute.refl _).pow_pow ε η))
  have hmk' : mk (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε *
      (conjAut n F B * fieldAut n F τ * dualAut n F ^ η) *
      (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε)⁻¹ *
      (conjAut n F B * fieldAut n F τ * dualAut n F ^ η)⁻¹) =
      ⁅mk (fieldAut n F σ) * mk (dualAut n F) ^ ε, mk (fieldAut n F τ) * mk (dualAut n F) ^ η⁆ := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hmk, hmk]
  have key : mk (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε *
      (conjAut n F B * fieldAut n F τ * dualAut n F ^ η) *
      (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε)⁻¹ *
      (conjAut n F B * fieldAut n F τ * dualAut n F ^ η)⁻¹) = 1 := by
    rw [hmk']
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq
  exact (QuotientGroup.eq_one_iff _).1 key



open CFSG.GH74.KGroups.L3Eps in
theorem lin_star_data {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {K : Type} [Group K] [Finite K] (e : K ≃* projectiveSL 3 F) {x : K} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ S : Subgroup K, IsQuasisimple ↥S ∧ x ∈ S ∧ S ≤ Subgroup.centralizer ({x} : Set K) ∧
      (∀ z ∈ Subgroup.centralizer ({x} : Set K), ∀ s ∈ S, z * s * z⁻¹ ∈ S) ∧
      (∀ a ∈ Subgroup.centralizer ({x} : Set K), ∀ b ∈ Subgroup.centralizer ({x} : Set K), ⁅a, b⁆ ∈ S) := by
  have hex2 : e x * e x = 1 := by rw [← map_mul, hx2, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := Generic.S3.singleInv_projectiveSL h2 (e x) tInv hex2 hex1 tInv_mul_self
    (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have ht : e' x = tInv := by
    show MulAut.conj g (e x) = tInv
    rw [MulAut.conj_apply]
    exact hg
  have hcen : ∀ z : K, z ∈ Subgroup.centralizer ({x} : Set K) ↔
      e' z ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← ht, ← map_mul,
      ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e'.injective h⟩
  have hmem : ∀ z : K, z ∈ (blockSub : Subgroup (projectiveSL 3 F)).map (e'.symm : projectiveSL 3 F →* K) ↔
      e' z ∈ (blockSub : Subgroup (projectiveSL 3 F)) := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨e' z, h, by simp⟩
  refine ⟨(blockSub : Subgroup (projectiveSL 3 F)).map (e'.symm : projectiveSL 3 F →* K), ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e'.symm blockSub)
      (isQuasisimple_blockSub h4)
  · rw [hmem, ht]
    exact tInv_mem_blockSub
  · intro s hs
    rw [hmem] at hs
    rw [hcen]
    exact blockSub_le_centralizer hs
  · intro z hz s hs
    rw [hcen] at hz
    rw [hmem] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_blockSub h2 hz hs
  · intro a ha b hb
    rw [hcen] at ha hb
    rw [hmem, map_commutatorElement]
    exact commutator_mem_blockSub h2 ha hb

theorem lin_comp_mem {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {K : Type} [Group K] [Finite K] (e : K ≃* projectiveSL 3 F) :
    ∀ x : K, x * x = 1 → x ≠ 1 → ∀ B : Subgroup K,
      IsCompIn (Subgroup.centralizer ({x} : Set K)) B → x ∈ B := by
  intro x hx2 hx1 B hB
  obtain ⟨S, hS, hxS, hSC, hSn, hcomm⟩ := lin_star_data h2 h4 e hx2 hx1
  exact IVK.GHInv.mem_of_isCompIn_of_normal_quasisimple hS hxS hSC hSn hcomm hB

end L3Aut

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

open CFSG.GH74.KGroups.L3Eps in
theorem x_mem_L_of_lin {k : Type} [Field k] [Finite k] {p f : ℕ} (hp : p.Prime)
    (hk : Nat.card k = p ^ f) (h : Lem711Cfg X L K x y) (eL : ↥L ≃* projectiveSL 3 k) : x ∈ L := by
  have := h.normal
  obtain ⟨ρ, hρinj, hρW, -, -⟩ := CFSG.ComponentClassification.OutcomeLocal.socle_extension
    (W := L) h.centralizer_eq_bot eL center_projectiveSL_three_eq_bot
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have hD : ρ x ∈ linearAutGroup 3 k := by
    have h1 : ρ x ∈ (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map ρ := ⟨x, h.x_mem_commutator, rfl⟩
    rw [Subgroup.map_commutator] at h1
    have hle : ⁅(⊤ : Subgroup (MulAut (projectiveSL 3 k))), (⊤ : Subgroup (MulAut (projectiveSL 3 k)))⁆ ≤
        linearAutGroup 3 k := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def]
      exact L3Aut.commutator_mem_linearAutGroup (by norm_num) hp hk a b
    exact hle (Subgroup.commutator_mono le_top le_top h1)
  obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 hD
  have hsq : conjAut 3 k B ^ 2 ^ 1 = 1 := by
    rw [hB, pow_one, pow_two, ← map_mul, hxx, map_one]
  obtain ⟨s, hs⟩ := conj_pow_inner B hsq
  let w : ↥L := eL.symm (proj 3 k s)
  have hw : ρ (w : X) = ρ x := by
    rw [hρW w, ← hB, hs]
    simp [w]
  have := hρinj hw
  rw [← this]
  exact w.2

end Lem711Cfg

theorem lem711_l3_ge5 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    Lem711Empty (fun X _ => LieModel X .PSL 3 p f) := by
  intro X _ _ L K x y h hL
  obtain ⟨k, _, _, hk, ⟨eL⟩⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact hpodd.pow
  have h2 : (2 : k) ≠ 0 := Generic.S3.two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card k := by rw [hk]; omega
  have hxL : x ∈ L := h.x_mem_L_of_lin hp hk eL
  exact h.false_of_comp_mem_of_mem hxL fun u hu2 hu1 B hB => L3Aut.lin_comp_mem h2 h4 eL u hu2 hu1 B hB

namespace L3Aut

theorem cube_one_zmod3 : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide

theorem center_bot_zmod3 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h1 : r = 1 := cube_one_zmod3 r (by simpa using hr)
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

theorem card_psl_zmod3 :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [KGroups.PSLN.card_psl_of_center_bot center_bot_zmod3, Matrix.card_SL_field 3]
  norm_num [ZMod.card, Fin.prod_univ_three]

theorem odd_prime_pow_eq_three_or_five_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (p = 3 ∧ f = 1) ∨ 5 ≤ p ^ f := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := this
    omega
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  obtain ⟨k, hk⟩ := hodd
  by_cases h5 : 5 ≤ p ^ f
  · exact Or.inr h5
  · left
    have h3 : p ^ f = 3 := by omega
    have hpd : p ∣ 3 := by rw [← h3]; exact dvd_pow_self p (by omega)
    have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpd
    subst hp3'
    refine ⟨rfl, ?_⟩
    by_contra hne
    have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end L3Aut

theorem lem711_l33 : Lem711Empty (fun X _ => LieModel X .PSL 3 3 1) := by
  intro X _ _ L K x y h hL
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e⟩ := KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num)
    (by rw [Nat.card_zmod, pow_one]) hL
  have hcard : Nat.card ↥L = 5616 := by
    rw [Nat.card_congr e.toEquiv, L3Aut.card_psl_zmod3]
  exact h.false_of_card (by rw [hcard]; norm_num)

theorem lem711_l3 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSL 3 p f) := by
  rcases L3Aut.odd_prime_pow_eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
  · exact lem711_l33
  · exact lem711_l3_ge5 hp hp2 h5

end CFSG.GH74.GLS
