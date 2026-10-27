module

public import CFSG.ClassicalInvolution.Q3.Sec13End16C
public import CFSG.ClassicalInvolution.Q3.Sec13End15E
public import CFSG.ClassicalInvolution.Q3.Sec13End16L

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16d_card_sup_of_normal {N H : Subgroup G} [N.Normal] (hd : N ⊓ H = ⊥) :
    Nat.card ↥(N ⊔ H) = Nat.card N * Nat.card H := by
  have hinj : Function.Injective (fun p : N × H => (p.1 : G) * (p.2 : G)) :=
    Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hd)
  let f : N × H → ↥(N ⊔ H) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := fun p q hpq => hinj (congrArg Subtype.val hpq)
  have hs : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (↑(N ⊔ H) : Set G) := x.2
    rw [Subgroup.normal_mul] at hx
    obtain ⟨n, hn, k, hk, hnk⟩ := hx
    exact ⟨(⟨n, hn⟩, ⟨k, hk⟩), Subtype.ext hnk⟩
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)
  rw [Nat.card_prod] at hc
  exact hc.symm

private def e16d_ofPermHom : Equiv.Perm (Fin 6) →* AE.Wr 6 where
  toFun := AE.Wr.ofPerm
  map_one' := AE.Wr.ext rfl rfl
  map_mul' σ τ := AE.Wr.ext (funext fun i => by simp [AE.Wr.mul_vec, AE.Wr.ofPerm]) rfl

private theorem e16d_ofPerm_mem_aeSub {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ alternatingGroup (Fin 6)) : AE.Wr.ofPerm σ ∈ AE.aeSub 6 := by
  refine AE.mem_aeSub.mpr ⟨?_, ?_⟩
  · show ∑ i, (0 : Fin 6 → ZMod 2) i = 0
    simp
  · exact Equiv.Perm.mem_alternatingGroup.mp hσ

theorem exists_complement (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ H : Subgroup G, (zGroup Ω).IsComplement' H := by
  haveI hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  haveI hDc : IsMulCommutative ↥(zGroup Ω) :=
    ⟨⟨fun a b => Subtype.ext (h.zGroup_comm h9 a.1 a.2 b.1 b.2)⟩⟩
  have hD2 : IsPGroup 2 (zGroup Ω) := IsPGroup.to_le CFSG.pCore_isPGroup h.zGroup_le_pCore
  have hD64 := natCard_zGroup_eq_sixtyFour c h h9 h13
  have hG := natCard_eq c h h9 h13
  obtain ⟨-, ψ, -, -, -, -, hψD⟩ := exists_equiv_X c h h9 h13
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3) (by rw [hA6]; norm_num)
  let ζ : alternatingGroup (Fin 6) →* ↥(AE.aeSub 6) :=
    MonoidHom.codRestrict (e16d_ofPermHom.comp (alternatingGroup (Fin 6)).subtype)
      (AE.aeSub 6) (fun σ => e16d_ofPerm_mem_aeSub σ.2)
  let ξ : alternatingGroup (Fin 6) →* G :=
    (pSpan (centMembers Ω e)).subtype.comp (ψ.symm.toMonoidHom.comp ζ)
  have hξinj : Function.Injective ξ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : ψ.symm (ζ σ) = 1 := Subtype.ext hσ
    have h2 : ζ σ = 1 := by
      have h3 := congrArg ψ h1
      rwa [MulEquiv.apply_symm_apply, map_one] at h3
    have h4 : (σ : Equiv.Perm (Fin 6)) = 1 :=
      congrArg (fun w : ↥(AE.aeSub 6) => (w : AE.Wr 6).perm) h2
    exact Subtype.ext h4
  have hSD : zGroup Ω ⊓ (T.map ξ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxS⟩
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hxS
    have hp := (hψD (ψ.symm (ζ σ))).mp hxD
    rw [MulEquiv.apply_symm_apply] at hp
    have hσ1 : (σ : Equiv.Perm (Fin 6)) = 1 := hp
    have hσ : σ = 1 := Subtype.ext hσ1
    rw [Subgroup.mem_bot, hσ, map_one]
  have hcard_S : Nat.card (T.map ξ) = 8 := by
    rw [Subgroup.card_map_of_injective hξinj, hT]
    norm_num
  have hS2 : IsPGroup 2 (T.map ξ) := IsPGroup.iff_card.mpr ⟨3, by rw [hcard_S]; norm_num⟩
  have hsup_card : Nat.card ↥(zGroup Ω ⊔ T.map ξ) = 512 := by
    rw [e16d_card_sup_of_normal hSD, hD64, hcard_S]
  have hSN : T.map ξ ≤ Subgroup.normalizer (zGroup Ω : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hDS2 : IsPGroup 2 ↥(zGroup Ω ⊔ T.map ξ) := by
    rw [sup_comm]
    exact hS2.to_sup_of_normal_right' hD2 hSN
  obtain ⟨P, hDSP⟩ := hDS2.exists_le_sylow
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : 2 ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card _
  have hn9 : n ≤ 9 := by
    by_contra hcon
    have h1 : (2 : ℕ) ^ 10 ∣ Nat.card G := (pow_dvd_pow 2 (by omega)).trans hdvd
    rw [hG] at h1
    norm_num at h1
  have hPle : Nat.card (P : Subgroup G) ≤ 512 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hn9
      _ = 512 := by norm_num
  have hDSeq : zGroup Ω ⊔ T.map ξ = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hDSP (by rw [hsup_card]; omega)
  obtain ⟨H, hH⟩ :=
    (CFSG.Quasithin.gaschutz hD2 P).mpr ⟨T.map ξ, le_sup_right.trans hDSP, hSD, hDSeq⟩
  refine ⟨H, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hH.1) ?_⟩
  have hu := Subgroup.normal_mul (zGroup Ω) H
  rw [hH.2, Subgroup.coe_top] at hu
  exact hu.symm

theorem exists_member_seven (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {H : Subgroup G}
    {σ : H →* Equiv.Perm (Fin 7)} {β : Multiplicative (Fin 7 → ZMod 2) →* G}
    (hS : AESplitHyp (zGroup Ω) H σ β)
    (hA : σ.range = alternatingGroup (Fin 7))
    (hβ : ∀ i, ∃ x : G, β (Multiplicative.ofAdd (Pi.single i 1)) = x * e * x⁻¹) :
    ∃ K₀ ∈ Ω, ∃ (α : Finset (Fin 7)) (hα : α.card = 4) (b : Bool) (φ : G →* AE.AEQ 7),
      (∀ f : Multiplicative (Fin 7 → ZMod 2), ∑ i, f.toAdd i = 0 →
        φ (β f) = AE.mkQ 7 (AE.Wr.ofVec f.toAdd)) ∧
      (∀ x : H, φ x = AE.mkQ 7 (AE.Wr.ofPerm (σ x))) ∧ K₀.map φ = AE.memBar α hα b :=
  exists_member_seven_of_points c h h9 h13 hS hA hβ

theorem exists_aeRecog_seven (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) : Nonempty (AERecog Ω 7) := by
  obtain ⟨pt, hinj, hptD, -, hconj, hprod, hspan, hinv⟩ := exists_points c h h9 h13
  obtain ⟨H, hcompl⟩ := exists_complement c h h9 h13
  have hD64 := natCard_zGroup_eq_sixtyFour c h h9 h13
  have hG := natCard_eq c h h9 h13
  have hfaith : ∀ x ∈ H, (∀ i, x * pt i * x⁻¹ = pt i) → x = 1 := by
    intro x hxH hfix
    have hsub : zGroup Ω ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hspan]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h1 : x * pt i = pt i * x := by
        calc x * pt i = (x * pt i * x⁻¹) * x := by group
          _ = pt i * x := by rw [hfix i]
      exact h1.symm
    have hxC : x ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.mp (hsub hd)
    rw [EndHyp.centralizer_zGroup_eq_pCore h h9 c.twin h13, c.pCore_eq_zGroup h h9 h13] at hxC
    have hx1 : x ∈ zGroup Ω ⊓ H := ⟨hxC, hxH⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hx1
    exact hx1
  have hDcomm := h.zGroup_comm h9
  have hDsq := h.zGroup_mul_self h9
  obtain ⟨σ, β, hsplit, hβpt, hσpt⟩ := exists_aeSplitHyp_of_points (n := 7) ⟨3, by norm_num⟩
    hcompl hDcomm hDsq pt hinj hptD hprod hspan (by rw [hD64]; norm_num)
    (fun x _ i => hinv x i) hfaith
  have hβ7 : ∀ i, ∃ x : G, β (Multiplicative.ofAdd (Pi.single i 1)) = x * e * x⁻¹ := by
    intro i
    obtain ⟨x, hx⟩ := hconj i
    exact ⟨x, by rw [hβpt i]; exact hx⟩
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hfix : ∀ i, (x : G) * pt i * (x : G)⁻¹ = pt i := by
      intro i
      rw [hσpt x i, hx, Equiv.Perm.one_apply]
    exact Subtype.ext (hfaith x x.2 hfix)
  have hHcard : Nat.card H = 2520 := by
    have h1 := hcompl.card_mul_card
    rw [hD64, hG] at h1
    omega
  have hrange : Nat.card σ.range = 2520 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hσinj, Subgroup.card_top, hHcard]
  have hidx : σ.range.index = 2 := by
    have h1 := Subgroup.index_mul_card (H := σ.range)
    rw [hrange, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
    norm_num [Nat.factorial] at h1
    omega
  have hsurj : σ.range = alternatingGroup (Fin 7) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  obtain ⟨K₀, hK₀, α, hα, b, φ, h1, h2, h3⟩ := exists_member_seven c h h9 h13 hsplit hsurj hβ7
  exact ⟨⟨zGroup Ω, H, σ, β, hsplit, hsurj, ⟨K₀, hK₀, α, hα, b, φ, h1, h2, h3⟩⟩⟩

end Sit16

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem aeIdent_six (h : EndHyp Ω) (h9 : Perp9 Ω) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hV : twinSet Ω K = {K, K'}) (hne : K ≠ K') (h13 : zGroup Ω ≠ eGroup Ω K)
    (hE : eGroup Ω K ≤ K ⊔ K') : Nonempty (AEIdent Ω 6) := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  exact aeIdent_six_of_twinSit h h9 ⟨hK, hz, hV, hne⟩ h13 hE

section FrameCert

theorem aeIdent_seven_of_twinSit (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : ¬ eGroup Ω K ≤ K ⊔ K') : Nonempty (AEIdent Ω 7) := by
  obtain ⟨W, u, e, g, c⟩ := h.exists_sit16 h9 s h13 hE
  obtain ⟨R⟩ := Sit16.exists_aeRecog_seven c h h9 h13
  exact R.nonempty_aeIdent (by norm_num) h.thmD.hyp.conjInvariant h.thmD.trans h.thmD.gen

theorem aeIdent_seven (h : EndHyp Ω) (h9 : Perp9 Ω) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hV : twinSet Ω K = {K, K'}) (hne : K ≠ K') (h13 : zGroup Ω ≠ eGroup Ω K)
    (hE : ¬ eGroup Ω K ≤ K ⊔ K') : Nonempty (AEIdent Ω 7) := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  exact aeIdent_seven_of_twinSit h h9 ⟨hK, hz, hV, hne⟩ h13 hE

theorem false_of_twinSet_two (h : EndHyp Ω) (h9 : Perp9 Ω) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hV : twinSet Ω K = {K, K'}) (hne : K ≠ K') (h13 : zGroup Ω ≠ eGroup Ω K) : False := by
  by_cases hE : eGroup Ω K ≤ K ⊔ K'
  · obtain ⟨I⟩ := aeIdent_six h h9 hK hV hne h13 hE
    exact (h.no_aeIdent (by norm_num : 5 ≤ 6)).false I
  · obtain ⟨I⟩ := aeIdent_seven h h9 hK hV hne h13 hE
    exact (h.no_aeIdent (by norm_num : 5 ≤ 7)).false I

end FrameCert

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
