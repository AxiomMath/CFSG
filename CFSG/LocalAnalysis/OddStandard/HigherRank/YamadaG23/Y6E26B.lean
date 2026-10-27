module

public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem y6e_card_map_mul_card_ker {Γ : Type} [Group Γ] {V C K : Subgroup Γ} {Q : Type*}
    [Group Q] (hCV : C ≤ V) (hKC : K ≤ C) (ψ : ↥V →* Q) (hker : ψ.ker = K.subgroupOf V) :
    Nat.card ↥((C.subgroupOf V).map ψ) * Nat.card ↥K = Nat.card ↥C := by
  have hrange : (ψ.domRestrict (C.subgroupOf V)).range = (C.subgroupOf V).map ψ :=
    MonoidHom.domRestrict_range (C.subgroupOf V) ψ
  have hkerf : (ψ.domRestrict (C.subgroupOf V)).ker = ψ.ker.subgroupOf (C.subgroupOf V) := rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (ψ.domRestrict (C.subgroupOf V)).ker
  have h2 : Nat.card (↥(C.subgroupOf V) ⧸ (ψ.domRestrict (C.subgroupOf V)).ker) =
      Nat.card ↥(ψ.domRestrict (C.subgroupOf V)).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (ψ.domRestrict (C.subgroupOf V))).toEquiv
  have h3 : Nat.card ↥(ψ.domRestrict (C.subgroupOf V)).ker = Nat.card ↥K := by
    have hle : K.subgroupOf V ≤ C.subgroupOf V := fun x hx => hKC hx
    rw [hkerf, hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKC.trans hCV)).toEquiv)
  have h4 : Nat.card ↥(C.subgroupOf V) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV).toEquiv
  rw [← hrange, ← h3, ← h2, ← h4]
  exact h1.symm

theorem y6e_card_sup_mul_inf {Γ : Type} [Group Γ] [Finite Γ] {H N : Subgroup Γ}
    (hHN : H ≤ normalizer (N : Set Γ)) :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h3 : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv
  have h4 : Nat.card ↥(N.subgroupOf H) = Nat.card ↥(H ⊓ N) := by
    rw [← Subgroup.inf_subgroupOf_left N H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ N ≤ H)).toEquiv
  rw [← Nat.card_congr e.toEquiv, h3] at h1
  rw [h4] at h2
  rw [h1, h2]
  exact mul_right_comm _ _ _

theorem y6e_isElemAbelian_map {Γ : Type} [Group Γ] {V N D : Subgroup Γ}
    [hn : (N.subgroupOf V).Normal] (hsq : ∀ x ∈ D, x ^ 2 ∈ N)
    (hc : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ N) :
    IsElemAbelian 2 ((D.subgroupOf V).map (QuotientGroup.mk' (N.subgroupOf V))) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a0, ha0, ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b0, hb0, hb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : ↥V ⧸ N.subgroupOf V) * (b : ↥V ⧸ N.subgroupOf V) =
      (b : ↥V ⧸ N.subgroupOf V) * (a : ↥V ⧸ N.subgroupOf V)
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    show ((a0 * b0 : ↥V) : ↥V ⧸ N.subgroupOf V) = ((b0 * a0 : ↥V) : ↥V ⧸ N.subgroupOf V)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have ha0' : (a0 : Γ) ∈ D := Subgroup.mem_subgroupOf.mp ha0
    have hb0' : (b0 : Γ) ∈ D := Subgroup.mem_subgroupOf.mp hb0
    have h := hc _ (D.inv_mem hb0') _ (D.inv_mem ha0')
    rw [commutatorElement_def] at h
    convert h using 1
    simp [mul_assoc]
  · obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    have hx0' : (x0 : Γ) ∈ D := Subgroup.mem_subgroupOf.mp hx0
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq _ hx0'

theorem y6e_false_of_G23Type {Γ : Type} [Group Γ] [Finite Γ] {V N B W : Subgroup Γ}
    (hBV : B ≤ V) (hWV : W ≤ V) (hNB : N ≤ B) (hNW : N ≤ W) (hBW : B ⊓ W ≤ N)
    (hBsq : ∀ x ∈ B, x ^ 2 ∈ N) (hBc : ∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ N)
    (hWsq : ∀ x ∈ W, x ^ 2 ∈ N) (hWc : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ N)
    (hBWc : ∀ x ∈ B, ∀ y ∈ W, ⁅x, y⁆ ∈ N)
    (hcB : 4 * Nat.card ↥N ≤ Nat.card ↥B) (hcW : 4 * Nat.card ↥N ≤ Nat.card ↥W)
    {Q : Type} [Group Q] (hQ : HRG23 Q) (S' : Sylow 2 Q) (h3 : CFSG.pRank 2 ↥S' = 3)
    (hsec : SecProp V N (fun Y _ _ _ => Sec2.IsG23Type Y)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, hG⟩ := hsec
  haveI := hn
  obtain ⟨φ⟩ := hG Q hQ S'
  let ι : ↥V →* ↥V ⧸ N.subgroupOf V := QuotientGroup.mk' (N.subgroupOf V)
  let B' : Subgroup (↥V ⧸ N.subgroupOf V) := (B.subgroupOf V).map ι
  let W' : Subgroup (↥V ⧸ N.subgroupOf V) := (W.subgroupOf V).map ι
  have hker : ι.ker = N.subgroupOf V := QuotientGroup.ker_mk' _
  have hB'card : Nat.card ↥B' * Nat.card ↥N = Nat.card ↥B :=
    y6e_card_map_mul_card_ker hBV hNB ι hker
  have hW'card : Nat.card ↥W' * Nat.card ↥N = Nat.card ↥W :=
    y6e_card_map_mul_card_ker hWV hNW ι hker
  have hNpos : 0 < Nat.card ↥N := Nat.card_pos
  have hB4 : 4 ≤ Nat.card ↥B' :=
    Nat.le_of_mul_le_mul_right (by rw [hB'card]; exact hcB) hNpos
  have hW4 : 4 ≤ Nat.card ↥W' :=
    Nat.le_of_mul_le_mul_right (by rw [hW'card]; exact hcW) hNpos
  have hB'ea : IsElemAbelian 2 B' := y6e_isElemAbelian_map hBsq hBc
  have hW'ea : IsElemAbelian 2 W' := y6e_isElemAbelian_map hWsq hWc
  have hcomm : ∀ a ∈ B', ∀ b ∈ W', a * b = b * a := by
    intro a ha b hb
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
    have ha0' : (a0 : Γ) ∈ B := Subgroup.mem_subgroupOf.mp ha0
    have hb0' : (b0 : Γ) ∈ W := Subgroup.mem_subgroupOf.mp hb0
    rw [← map_mul, ← map_mul]
    symm
    show ((b0 * a0 : ↥V) : ↥V ⧸ N.subgroupOf V) = ((a0 * b0 : ↥V) : ↥V ⧸ N.subgroupOf V)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hBWc _ (B.inv_mem ha0') _ (W.inv_mem hb0')
    rw [commutatorElement_def] at h
    convert h using 1
    simp [mul_assoc]
  have hinf : B' ⊓ W' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    obtain ⟨hyB, hyW⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hyB
    obtain ⟨w0, hw0, hw⟩ := Subgroup.mem_map.mp hyW
    have hb0' : (b0 : Γ) ∈ B := Subgroup.mem_subgroupOf.mp hb0
    have hw0' : (w0 : Γ) ∈ W := Subgroup.mem_subgroupOf.mp hw0
    have hbw : ι w0 = ι b0 := hw
    have hmem : (w0⁻¹ * b0 : ↥V) ∈ N.subgroupOf V := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hbw, inv_mul_cancel]
    have hmem' : ((w0⁻¹ * b0 : ↥V) : Γ) ∈ N := Subgroup.mem_subgroupOf.mp hmem
    have hb_in_W : (b0 : Γ) ∈ W := by
      have : (b0 : Γ) = (w0 : Γ) * ((w0⁻¹ * b0 : ↥V) : Γ) := by simp
      rw [this]
      exact W.mul_mem hw0' (hNW hmem')
    have hbN : (b0 : Γ) ∈ N := hBW ⟨hb0', hb_in_W⟩
    have hb0K : b0 ∈ ι.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr hbN
    exact MonoidHom.mem_ker.mp hb0K
  have hBnorm : B' ≤ normalizer (W' : Set (↥V ⧸ N.subgroupOf V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hc := hcomm a ha
    constructor
    · intro hw
      have : a * w * a⁻¹ = w := by rw [hc w hw, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact hw
    · intro hw
      have h2 : a * (a * w * a⁻¹) = (a * w * a⁻¹) * a := hc _ hw
      have h3 : a * (a * w * a⁻¹) = a * w := by
        rw [h2]
        group
      have h4 : a * w * a⁻¹ = w := mul_left_cancel h3
      rw [← h4]
      exact hw
  have hprod := y6e_card_sup_mul_inf hBnorm
  rw [hinf, Subgroup.card_bot, mul_one] at hprod
  have hea : IsElemAbelian 2 (B' ⊔ W') := hB'ea.sup_of_commute hW'ea hcomm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hea.isPGroup
  have h16 : 16 ≤ 2 ^ k := by
    rw [← hk, hprod]
    nlinarith
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (↥V ⧸ N.subgroupOf V)) :=
    CFSG.SectionRank.le_pRank (p := 2) (by norm_num) le_top hea hk
  have heq : CFSG.pRank 2 (↥V ⧸ N.subgroupOf V) = 3 := by
    rw [CFSG.pRank_congr_of_mulEquiv φ 2]
    exact h3
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 (↥V ⧸ N.subgroupOf V)] at heq
  omega

theorem y6e_pRank_sylow_quotient {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hS : IsSylowIn 2 L S) (hZ : Subgroup.center ↥L = ⊥)
    (hr : CFSG.pRank 2 ↥S = 3) (S' : Sylow 2 (↥L ⧸ Subgroup.center ↥L)) :
    CFSG.pRank 2 ↥S' = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hSL : IsPGroup 2 ↥(S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let SL : Sylow 2 ↥L := hSL.toSylow hS.2.2
  let S'' : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := SL.mapSurjective hπ
  have e1 : ↥S'' ≃* ↥S' := Sylow.equiv S'' S'
  have e2 : ↥(SL : Subgroup ↥L) ≃* ↥(SL.map π) :=
    Subgroup.equivMapOfInjective (SL : Subgroup ↥L) π hinj
  have e3 : ↥(S.subgroupOf L) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS.1
  have e : ↥S' ≃* ↥S := e1.symm.trans (e2.symm.trans e3)
  rw [CFSG.pRank_congr_of_mulEquiv e 2]
  exact hr

theorem y6e_card_sqone :
    Nat.card {x : Fin 3 → Multiplicative (ZMod 4) // x ^ 2 = 1} = 8 := by
  have h : {x : Fin 3 → Multiplicative (ZMod 4) // x ^ 2 = 1} ≃
      (Fin 3 → {a : Multiplicative (ZMod 4) // a ^ 2 = 1}) :=
    (Equiv.subtypeEquivRight (fun x => by
      simp only [funext_iff, Pi.pow_apply, Pi.one_apply])).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr h, Nat.card_pi]
  have h2 : Nat.card {a : Multiplicative (ZMod 4) // a ^ 2 = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, h2]
  norm_num

theorem y6e_sqone_mem_of_card {G : Type} [Group G] [Finite G] {M F : Subgroup G} (hFM : F ≤ M)
    (e : ↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))
    (hFsq : ∀ x ∈ F, x ^ 2 = 1) (hFc : Nat.card ↥F = 8) {y : G} (hy : y ∈ M)
    (hy2 : y ^ 2 = 1) : y ∈ F := by
  let T : Set ↥M := {z | z ^ 2 = 1}
  let Fs : Set ↥M := {z | (z : G) ∈ F}
  have hFsT : Fs ⊆ T := fun z hz => Subtype.ext (by simpa using hFsq _ hz)
  have hTcard : T.ncard = 8 := by
    have h1 : T = e ⁻¹' {x : Fin 3 → Multiplicative (ZMod 4) | x ^ 2 = 1} := by
      ext z
      simp only [T, Set.mem_setOf_eq, Set.mem_preimage]
      rw [← map_pow, e.map_eq_one_iff]
    rw [h1, Set.ncard_preimage_of_injective_subset_range e.injective
      (fun x _ => ⟨e.symm x, e.apply_symm_apply x⟩)]
    rw [← Nat.card_coe_set_eq]
    exact y6e_card_sqone
  have hFscard : Fs.ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv).trans hFc
  have hTfin : T.Finite := Set.toFinite T
  have heq : Fs = T := Set.eq_of_subset_of_ncard_le hFsT (by rw [hTcard, hFscard]) hTfin
  have hyT : (⟨y, hy⟩ : ↥M) ∈ T := Subtype.ext (by simpa using hy2)
  rw [← heq] at hyT
  exact hyT

end CFSG.OddStandard.HigherRank.YamadaG23
