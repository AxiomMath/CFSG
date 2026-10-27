module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts
public import CFSG.Assembly.E6FourNeighbourFacts
public import CFSG.Assembly.StandardTypeRecognitionDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Assembly (E6FourOutInner E6FourSylowFive E6FourCentFive E6FourMark E6FourSubcompMark
  LargeEvenLabel standardTypeRecognitionMarking_mono standardTypeRecognitionRawDatum_mono)

private theorem conj_injective_of_center_eq_bot {S : Type} [Group S]
    (hZ : Subgroup.center S = ⊥) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut S => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

private theorem exists_lift_of_range_le {S B : Type} [Group S] [Group B]
    (hZ : Subgroup.center S = ⊥) (α : B →* MulAut S)
    (hle : α.range ≤ (MulAut.conj : S →* MulAut S).range) :
    ∃ β : B →* S, ∀ b, MulAut.conj (β b) = α b := by
  have hinj := conj_injective_of_center_eq_bot hZ
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (α.codRestrict _ fun b => hle ⟨b, rfl⟩), fun b => ?_⟩
  change MulAut.conj ((MonoidHom.ofInjective hinj).symm (α.codRestrict _ _ b)) = α b
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

private theorem comm_iff_conj_eq_self {G : Type*} [Group G] (g j : G) :
    j * g = g * j ↔ g * j * g⁻¹ = j := by
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

private theorem isComponentOf_subgroupOf_of_le {H : Type} [Group H] {J K X : Subgroup H}
    (hKJ : K ≤ J) (hK : IsComponentOf K X) : IsComponentOf (K.subgroupOf J) (X.subgroupOf J) :=
  ⟨fun _ hy => hK.1 hy, CFSG.Open.IsSubnormal.comap J.subtype hK.2.1,
    (CFSG.Open.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKJ)).2 hK.2.2⟩

private theorem eq_A_five_two_of {lab : LargeEvenLabel}
    (h : lab.n = 2 ∧ ((lab.tag = .twD ∧ lab.rank = 4) ∨ (lab.tag = .A ∧ lab.rank = 5)))
    (hne : lab ≠ ⟨.twD, 4, 2⟩) : lab = ⟨.A, 5, 2⟩ := by
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨hm, ⟨ht, hr⟩ | ⟨ht, hr⟩⟩ := h
  · simp only at hm ht hr
    subst hm ht hr
    exact (hne rfl).elim
  · simp only at hm ht hr
    subst hm ht hr
    rfl

private theorem labelOf_of_subcompMark {Γ : Type} [Group Γ] {K : Subgroup Γ} {X : Type*} [Group X]
    (e : X ≃* ↥K) (h : E6FourSubcompMark X) :
    LabelOf K ⟨.twD, 4, 2⟩ ∨ LabelOf K ⟨.A, 5, 2⟩ := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h
  haveI : Group.IsPerfect X := ⟨hcomm⟩
  have hK : commutator ↥K = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top
  let eZ : ↥K ⧸ Subgroup.center ↥K ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center ↥K) e
      (Subgroup.map_center_eq e)).symm
  by_cases hne : lab = ⟨.twD, 4, 2⟩
  · refine Or.inl ⟨hK, lab, hlab, standardTypeRecognitionRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, -⟩
    exact ⟨hs, hna, eZ.trans θ, hne⟩
  · refine Or.inr ⟨hK, lab, hlab, standardTypeRecognitionRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨hs, hna, eZ.trans θ, eq_A_five_two_of hP hne⟩

theorem e6FourCent5_of_facts (hT3 : E6FourOutInner) (hE1 : E6FourSylowFive)
    (hE3 : E6FourCentFive) : E6FourCent5 := by
  intro Γ _ _ J K B x lab hlab htag hn hZ hBN hB hxB hxJ hK hBK hcount
  have hmark : E6FourMark ↥J := by
    refine standardTypeRecognitionMarking_mono ?_ hlab
    rintro _ _ _ _ _ _ rfl
    exact ⟨htag, hn⟩
  have hKJ : K ≤ J := hK.1.trans inf_le_left
  let α : B →* MulAut ↥J := (Subgroup.normalizerMonoidHom (H := J)).comp (Subgroup.inclusion hBN)
  have hα : ∀ (b : B) (j : ↥J), ((α b j : ↥J) : Γ) = (b : Γ) * j * (b : Γ)⁻¹ := fun _ _ => rfl
  have hb5 : ∀ b : B, b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hB.2 b b.2)
  obtain ⟨β, hβ⟩ := exists_lift_of_range_le hZ α (by
    rintro _ ⟨b, rfl⟩
    exact (hT3 ↥J hmark hZ).1 (α b) (by rw [← map_pow, hb5, map_one]))
  have hβc : ∀ (b : B) (j : ↥J), (b : Γ) * j * (b : Γ)⁻¹ = (β b : Γ) * j * (β b : Γ)⁻¹ :=
    fun b j => by rw [← hα, ← hβ]; rfl
  have hBC : ∀ b : B, ((β b : ↥J) : Γ) ∈ Subgroup.centralizer (K : Set Γ) ↔
      (b : Γ) ∈ Subgroup.centralizer (K : Set Γ) := by
    intro b
    simp only [Subgroup.mem_centralizer_iff]
    refine forall₂_congr fun k hk => ?_
    have h := hβc b ⟨k, hKJ hk⟩
    dsimp only at h
    rw [comm_iff_conj_eq_self, comm_iff_conj_eq_self, h]
  let xb : B := ⟨x, hxB⟩
  have hs1 : β xb ≠ 1 := fun h1 => hxJ <| Subgroup.mem_centralizer_iff.2 fun j hj => by
    have h := hβc xb ⟨j, hj⟩
    rw [h1] at h
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
    exact (comm_iff_conj_eq_self x j).2 h
  have hs5 : β xb ^ 5 = 1 := by rw [← map_pow, hb5, map_one]
  have hcent : Subgroup.centralizer ({β xb} : Set ↥J) =
      (J ⊓ Subgroup.centralizer ({x} : Set Γ)).subgroupOf J := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul,
      comm_iff_conj_eq_self, comm_iff_conj_eq_self (x : Γ), ← hβc xb z]
    exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩
  have hcomp : CFSG.Assembly.IsComponentOf (K.subgroupOf J)
      (Subgroup.centralizer ({β xb} : Set ↥J)) := by
    rw [hcent]
    exact CFSG.Assembly.isComponentOf_iff_open.2 (isComponentOf_subgroupOf_of_le hKJ hK)
  have hAN : β.range ≤ Subgroup.normalizer ((K.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hz := Subgroup.mem_normalizer_iff.1 (hBK b.2) (z : Γ)
    rw [hβc b z] at hz
    simpa [Subgroup.mem_subgroupOf] using hz
  set H : Subgroup B := (B ⊓ Subgroup.centralizer (K : Set Γ)).subgroupOf B with hH
  have hcentK : Subgroup.centralizer ((K.subgroupOf J : Subgroup ↥J) : Set ↥J) =
      (Subgroup.centralizer (K : Set Γ)).subgroupOf J := by
    ext z
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hz k hk
      exact congrArg Subtype.val (hz ⟨k, hKJ hk⟩ hk)
    · intro hz k hk
      exact Subtype.ext (hz (k : Γ) hk)
  have hmap : β.range ⊓ Subgroup.centralizer ((K.subgroupOf J : Subgroup ↥J) : Set ↥J) =
      H.map β := by
    rw [hcentK]
    ext a
    constructor
    · rintro ⟨⟨b, rfl⟩, ha⟩
      exact ⟨b, ⟨b.2, (hBC b).1 ha⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, rfl⟩, (hBC b).2 hb.2⟩
  have hker : β.ker ≤ H := by
    intro b hb
    refine ⟨b.2, (hBC b).1 ?_⟩
    rw [MonoidHom.mem_ker.1 hb]
    exact Subgroup.one_mem _
  have hcB : Nat.card β.ker * Nat.card β.range = Nat.card B := Subgroup.card_ker_mul_card_range β
  have hcH : Nat.card β.ker * Nat.card (H.map β) = Nat.card H := by
    have h := Subgroup.card_ker_mul_card_range (β.comp H.subtype)
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.comap_ker] at h
    have hk : Nat.card ↥(β.ker.comap H.subtype) = Nat.card ↥β.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
    rwa [hk] at h
  have hcHB : Nat.card H = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Γ)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hineq : 5 ^ 3 * Nat.card (H.map β) ≤ Nat.card β.range := by
    have h1 : Nat.card β.ker * (5 ^ 3 * Nat.card (H.map β)) ≤
        Nat.card β.ker * Nat.card β.range := by
      calc Nat.card β.ker * (5 ^ 3 * Nat.card (H.map β)) = 5 ^ 3 * Nat.card H := by
            rw [← hcH]; ring
        _ ≤ Nat.card B := by rw [hcHB]; exact hcount
        _ = Nat.card β.ker * Nat.card β.range := hcB.symm
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA4le : Nat.card β.range ≤ 5 ^ 4 := by
    have hA5 : IsPGroup 5 β.range :=
      (CFSG.Open.IsElemAbelian.isPGroup hB).of_surjective β.rangeRestrict β.rangeRestrict_surjective
    obtain ⟨P, hP⟩ := hA5.exists_le_sylow
    have h := Subgroup.card_le_of_le hP
    rwa [hE1 ↥J hmark hZ P] at h
  have hxH : xb ∈ H := by
    rw [hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨hxB, fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk).2⟩
  have hz : Subgroup.zpowers (β xb) ≤ H.map β := Subgroup.zpowers_le.2 ⟨xb, hxH, rfl⟩
  have hzc : Nat.card (Subgroup.zpowers (β xb)) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hs5 hs1]
  have h5 : 5 ≤ Nat.card (H.map β) := by
    have h := Subgroup.card_le_of_le hz
    rwa [hzc] at h
  have hp4 : (5 : ℕ) ^ 4 = 625 := by norm_num
  rw [show (5 : ℕ) ^ 3 = 125 by norm_num] at hineq
  rw [hp4] at hA4le
  have hA4 : Nat.card β.range = 5 ^ 4 := by rw [hp4]; omega
  have hAC : β.range ⊓ Subgroup.centralizer ((K.subgroupOf J : Subgroup ↥J) : Set ↥J) =
      Subgroup.zpowers (β xb) := by
    rw [hmap]
    exact (Subgroup.eq_of_le_of_card_ge hz (by omega)).symm
  exact labelOf_of_subcompMark (Subgroup.subgroupOfEquivOfLe hKJ)
    (hE3 ↥J hmark hZ β.range hA4 (β xb) ⟨xb, rfl⟩ hs1 (K.subgroupOf J) hcomp hAN hAC)

end CFSG.LocalAnalysis.GLTheoremA

end
