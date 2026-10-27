module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlNDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Count
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6ExtCanon
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Fusion
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaHub
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma51B
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracPiece
import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section SigCenA

variable {X : Type} [Group X] [Finite X]

private theorem sca_sq {g : X} (hg : orderOf g = 2) : g ^ 2 = 1 := by
  rw [← hg]
  exact pow_orderOf_eq_one g

private theorem sca_mul_self {g : X} (hg : orderOf g = 2) : g * g = 1 := by
  rw [← sq]
  exact sca_sq hg

private theorem sca_comm {a b : X} (h : a ∈ cen b) : a * b = b * a :=
  Subgroup.mem_centralizer_singleton_iff.1 h

private theorem sca_mem_cen_symm {a b : X} (h : a ∈ cen b) : b ∈ cen a :=
  Subgroup.mem_centralizer_singleton_iff.2 (sca_comm h).symm

private theorem sca_conj_mem {S : Subgroup X} {c h : X} (hc : c ∈ normalizer (S : Set X))
    (hh : h ∈ S) : c * h * c⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 hc h).1 hh

private theorem sca_ne_one {g : X} (hg : orderOf g = 2) : g ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hg
  exact absurd hg (by norm_num)

private theorem sca_orderOf_two {g : X} (hg : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact hg) h1

private theorem sca_not_mem_odd {O : Subgroup X} (hO : Odd (Nat.card O)) {g : X}
    (hg : orderOf g = 2) : g ∉ O := by
  intro hgO
  have h1 : orderOf (⟨g, hgO⟩ : ↥O) ∣ Nat.card O := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hg] at h1
  exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h1)

private theorem sca_eq_of_mul_mem_odd {O : Subgroup X} (hO : Odd (Nat.card O)) {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (hmem : a * b ∈ O) : a = b := by
  by_contra hne
  have h1 : a * b ≠ 1 := by
    intro h
    apply hne
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h, one_mul]
  have h2 : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  exact sca_not_mem_odd hO (sca_orderOf_two h2 h1) hmem

private theorem sca_comm_of_sq {A : Subgroup X} (hA : ∀ a ∈ A, a ^ 2 = 1) {a b : X}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have e : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA x hx)
  have hab := hA _ (A.mul_mem ha hb)
  rw [sq] at hab
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  rw [h1, mul_inv_rev, e a ha, e b hb]

private theorem sca_isElemAbelian_of_sq {A : Subgroup X} (hA : ∀ a ∈ A, a ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 A :=
  ⟨⟨⟨fun c d => Subtype.ext (sca_comm_of_sq hA c.2 d.2)⟩⟩, hA⟩

private abbrev scaFour {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup X :=
  Holt.StarLemma26.fourSubgroup ha hb hab

private theorem sca_four_sq {a b : X} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} :
    ∀ y ∈ scaFour ha hb hab, y ^ 2 = 1 := fun y hy => by
  rw [pow_two]
  exact Holt.StarLemma26.mul_self_of_mem_fourSubgroup hy

private theorem sca_four_isElemAbelian {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} : CFSG.Open.IsElemAbelian 2 (scaFour ha hb hab) :=
  sca_isElemAbelian_of_sq sca_four_sq

private theorem sca_four_card {a b : X} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (scaFour ha hb hab) = 4 :=
  Holt.StarLemma26.card_fourSubgroup ha1 hb1 hne

private theorem sca_four_le {a b : X} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    {E : Subgroup X} (haE : a ∈ E) (hbE : b ∈ E) : scaFour ha hb hab ≤ E := by
  intro y hy
  rcases Holt.StarLemma26.mem_fourSubgroup.1 hy with rfl | rfl | rfl | rfl
  · exact E.one_mem
  · exact haE
  · exact hbE
  · exact E.mul_mem haE hbE

private theorem sca_left_mem_four {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} : a ∈ scaFour ha hb hab :=
  Holt.StarLemma26.mem_fourSubgroup.2 (Or.inr (Or.inl rfl))

private theorem sca_right_mem_four {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} : b ∈ scaFour ha hb hab :=
  Holt.StarLemma26.mem_fourSubgroup.2 (Or.inr (Or.inr (Or.inl rfl)))

private theorem sca_mem_zpowers {s x : X} (hs : s * s = 1) (hx : x ∈ zpowers s) :
    x = 1 ∨ x = s := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hs2 : s ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hs
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [hm, ← two_mul, zpow_mul, hs2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, hs2, one_zpow, one_mul, zpow_one]

private theorem sca_mem_normalizer_of_comm {B : Subgroup X} {s : X}
    (hsB : ∀ b ∈ B, s * b = b * s) : s ∈ normalizer (B : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hsB h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have hk := hsB _ hh
    have h1 : s * h * s⁻¹ = h := by
      calc s * h * s⁻¹ = s⁻¹ * (s * (s * h * s⁻¹)) := by group
        _ = s⁻¹ * (s * h * s⁻¹ * s) := by rw [hk]
        _ = h := by group
    rw [← h1]
    exact hh

private theorem sca_sup_zpowers {B : Subgroup X} (hB : CFSG.Open.IsElemAbelian 2 B) {s : X}
    (hs : s * s = 1) (hsB : ∀ b ∈ B, s * b = b * s) :
    CFSG.Open.IsElemAbelian 2 (B ⊔ zpowers s) ∧
      (s ∉ B → Nat.card ↥(B ⊔ zpowers s) = 2 * Nat.card B) := by
  have hsN : zpowers s ≤ normalizer (B : Set X) :=
    (Subgroup.zpowers_le).2 (sca_mem_normalizer_of_comm hsB)
  refine ⟨sca_isElemAbelian_of_sq fun x hx => ?_, fun hsB' => ?_⟩
  · rw [sup_comm] at hx
    obtain ⟨z, hz, b, hb, rfl⟩ := Sec6Fus.exists_mul_of_mem_sup hsN hx
    rcases sca_mem_zpowers hs hz with hz1 | hzs
    · rw [hz1, one_mul]
      exact hB.2 b hb
    · rw [hzs]
      have hb2 := hB.2 b hb
      rw [sq] at hb2 ⊢
      calc s * b * (s * b) = s * (b * s) * b := by group
        _ = s * (s * b) * b := by rw [hsB b hb]
        _ = (s * s) * (b * b) := by group
        _ = 1 := by rw [hs, hb2, one_mul]
  · have hcard := Sec6Fus.card_sup_mul_card_inf (A := B) (B := zpowers s) hsN
    have hinf : B ⊓ zpowers s = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases sca_mem_zpowers hs hx.2 with hx1 | hxs
      · rw [hx1]
        exact Subgroup.one_mem _
      · exact absurd (hxs ▸ hx.1) hsB'
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hsB' B.one_mem
    have hz : Nat.card ↥(zpowers s) = 2 := by
      rw [Nat.card_zpowers]
      exact sca_orderOf_two hs hs1
    rw [hinf, Subgroup.card_bot, mul_one, hz] at hcard
    rw [hcard, mul_comm]

private abbrev scaV (B : Subgroup X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)

private theorem sca_map_map_symm (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem sca_map_symm_map (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem sca_map_V_le (φ : X ≃* X) (B : Subgroup X) :
    (scaV B).map φ.toMonoidHom ≤ scaV (B.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
  rw [← Subgroup.map_le_iff_le_comap, oddCoreOf_map_mulEquiv', cen_map]
  exact le_iSup_of_le (φ b) (le_iSup_of_le (Subgroup.mem_map_of_mem φ.toMonoidHom hb)
    (le_iSup_of_le (fun h => hb1 ((MulEquiv.map_eq_one_iff φ).1 h)) le_rfl))

private theorem sca_V_map (φ : X ≃* X) (B : Subgroup X) :
    (scaV B).map φ.toMonoidHom = scaV (B.map φ.toMonoidHom) := by
  refine le_antisymm (sca_map_V_le φ B) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (sca_map_V_le φ.symm (B.map φ.toMonoidHom))
  rwa [sca_map_map_symm, sca_map_symm_map] at h

private theorem sca_le_V {B : Subgroup X} {b : X} (hb : b ∈ B) (hb1 : b ≠ 1) :
    oddCoreOf (cen b) ≤ scaV B :=
  le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))

private theorem sca_isElemAbelian_map (φ : X ≃* X) {B : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian 2 B) : CFSG.Open.IsElemAbelian 2 (B.map φ.toMonoidHom) := by
  refine sca_isElemAbelian_of_sq ?_
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_pow, hB.2 b hb, map_one]

private theorem sca_V_conj {W B : Subgroup X} {g : X} (hB : scaV B = W)
    (hg : g ∈ normalizer (W : Set X)) :
    scaV (B.map (MulAut.conj g).toMonoidHom) = W := by
  rw [← sca_V_map, hB]
  exact map_conj_eq_of_mem_normalizer hg

private theorem sca_mem_normalizer_of_V {W B : Subgroup X} {g : X} (hB : scaV B = W)
    (hBg : scaV (B.map (MulAut.conj g).toMonoidHom) = W) : g ∈ normalizer (W : Set X) := by
  apply mem_normalizer_of_map_conj_eq
  rw [← hB, sca_V_map]
  exact hBg.trans hB.symm

private theorem sca_exists_conj_le_of_normal {G : Type*} [Group G] [Finite G]
    {A N P : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P)
    (hPAN : P ≤ A ⊔ N) : ∃ o ∈ N, ∀ y ∈ P, o⁻¹ * y * o ∈ A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : A ≤ A ⊔ N := le_sup_left
  have hidxA : ¬ 2 ∣ A.relIndex (A ⊔ N) := by
    have h1 : A.relIndex (A ⊔ N) * Nat.card A = Nat.card ↥(A ⊔ N) := by
      have := Subgroup.relIndex_mul_card A (A ⊔ N)
      rwa [inf_of_le_left hAH] at this
    have h2 : N.relIndex A * Nat.card N = Nat.card ↥(A ⊔ N) := by
      have := Subgroup.relIndex_mul_card N (A ⊔ N)
      rwa [inf_of_le_left (le_sup_right : N ≤ A ⊔ N), Subgroup.relIndex_sup_right] at this
    have h3 : N.relIndex A * Nat.card ↥(N ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card N A
    have hpos : 0 < N.relIndex A := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at h3
      exact Nat.card_pos.ne' h3.symm
    have h4 : N.relIndex A * (A.relIndex (A ⊔ N) * Nat.card ↥(N ⊓ A)) =
        N.relIndex A * Nat.card N := by
      rw [h2, ← h1, ← h3]
      ring
    have h5 := Nat.eq_of_mul_eq_mul_left hpos h4
    intro hd
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 (hd.trans ⟨_, h5.symm⟩))
  let A₀ : Subgroup ↥(A ⊔ N) := A.subgroupOf (A ⊔ N)
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥A₀) := inferInstance
  let T₁ : Subgroup ↥(A ⊔ N) := (T : Subgroup ↥A₀).map A₀.subtype
  have hT₁p : IsPGroup 2 T₁ := T.isPGroup'.map A₀.subtype
  have hT₁idx : ¬ 2 ∣ T₁.index := by
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact T.not_dvd_index h
    · exact hidxA h
  let S : Sylow 2 ↥(A ⊔ N) := hT₁p.toSylow hT₁idx
  have hPH : IsPGroup 2 (P.subgroupOf (A ⊔ N)) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hPH.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥(A ⊔ N) S Q
  have hh' : (h : G) ∈ N ⊔ A := by
    rw [sup_comm]
    exact h.2
  obtain ⟨n, hn, a, ha, hna⟩ := Subgroup.mem_sup_of_normal_left.1 hh'
  refine ⟨n, hn, fun y hy => ?_⟩
  have hyH : y ∈ A ⊔ N := hPAN hy
  have hyQ : (⟨y, hyH⟩ : ↥(A ⊔ N)) ∈ (Q : Subgroup ↥(A ⊔ N)) :=
    hQ (show (⟨y, hyH⟩ : ↥(A ⊔ N)) ∈ P.subgroupOf (A ⊔ N) from hy)
  rw [← hh, mem_smul_sylow_iff_aux] at hyQ
  have h1 : h⁻¹ * ⟨y, hyH⟩ * h ∈ A₀ := by
    have hT : h⁻¹ * ⟨y, hyH⟩ * h ∈ T₁ := (IsPGroup.mem_toSylow hT₁p hT₁idx).1 hyQ
    obtain ⟨w, -, hw⟩ := hT
    rw [← hw]
    exact w.2
  have h2 : (h : G)⁻¹ * y * h ∈ A := Subgroup.mem_subgroupOf.1 h1
  have e : n⁻¹ * y * n = a * ((h : G)⁻¹ * y * h) * a⁻¹ := by
    rw [← hna]
    group
  rw [e]
  exact A.mul_mem (A.mul_mem ha h2) (A.inv_mem ha)

private theorem sca_exists_conj_le {A O P : Subgroup X} (hAO : A ≤ normalizer (O : Set X))
    (hO : Odd (Nat.card O)) (hP : IsPGroup 2 P) (hPAO : P ≤ A ⊔ O) :
    ∃ o ∈ O, ∀ y ∈ P, o⁻¹ * y * o ∈ A := by
  have hOD : O ≤ normalizer (O : Set X) := Subgroup.le_normalizer
  have hPD : P ≤ normalizer (O : Set X) := hPAO.trans (sup_le hAO hOD)
  have hMn : (O.subgroupOf (normalizer (O : Set X))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOD).2 le_rfl
  have hO' : Odd (Nat.card (O.subgroupOf (normalizer (O : Set X)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv]
    exact hO
  have hP' : IsPGroup 2 (P.subgroupOf (normalizer (O : Set X))) := hP.comap_subtype
  have hPAO' : P.subgroupOf (normalizer (O : Set X)) ≤
      A.subgroupOf (normalizer (O : Set X)) ⊔ O.subgroupOf (normalizer (O : Set X)) := by
    rw [← Subgroup.subgroupOf_sup hAO hOD]
    exact fun y hy => hPAO hy
  obtain ⟨o, ho, hoP⟩ := sca_exists_conj_le_of_normal hO' hP' hPAO'
  exact ⟨(o : X), Subgroup.mem_subgroupOf.1 ho, fun y hy =>
    Subgroup.mem_subgroupOf.1 (hoP ⟨y, hPD hy⟩ hy)⟩

private theorem sca_isPGroup {B : Subgroup X} (hB : CFSG.Open.IsElemAbelian 2 B) :
    IsPGroup 2 B := isPGroup_two_of_sq hB.2

private theorem sca_exists_four_conj {A O B : Subgroup X} (hAO : A ≤ normalizer (O : Set X))
    (hO : Odd (Nat.card O)) (hB : CFSG.Open.IsElemAbelian 2 B) (hB4 : Nat.card B = 4)
    (hBAO : B ≤ A ⊔ O) :
    ∃ o ∈ O, ∃ B' : Subgroup X, B' ≤ A ∧ CFSG.Open.IsElemAbelian 2 B' ∧ Nat.card B' = 4 ∧
      B = B'.map (MulAut.conj o).toMonoidHom := by
  obtain ⟨o, ho, hoB⟩ := sca_exists_conj_le hAO hO (sca_isPGroup hB) hBAO
  refine ⟨o, ho, B.map (MulAut.conj o).symm.toMonoidHom, ?_, sca_isElemAbelian_map _ hB, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := hoB y hy
    simpa [MulAut.conj_symm_apply] using h
  · rw [Subgroup.card_map_of_injective (MulAut.conj o).symm.injective]
    exact hB4
  · rw [sca_map_map_symm]

private theorem sca_two_dvd_card {E : Subgroup X} (hq : IsTwoGenQuasi ↥E) :
    2 ∣ Nat.card E := by
  by_contra h
  have hodd : Odd (Nat.card E) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  exact not_le_oddCoreOf_of_isTwoGenQuasi hq
    (le_oddCoreOf_of_normalized le_rfl Subgroup.le_normalizer hodd)

private theorem sca_isTwoGenQuasi {H L : Subgroup X} (hL : IsPCompIn 2 H L) :
    IsTwoGenQuasi ↥L :=
  (isTwoGenQuasi_subgroupOf_iff hL.1).1 (isPComponent_two_iff.1 hL.2).2

private theorem sca_exists_sq_eq_one_mk {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : Odd (Nat.card N)) (u : G ⧸ N) (hu : u ^ 2 = 1) :
    ∃ s : G, s ^ 2 = 1 ∧ (s : G ⧸ N) = u := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  have hg2 : g ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hu
  refine ⟨g ^ Nat.card N, ?_, ?_⟩
  · have h1 : (⟨g ^ 2, hg2⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul, mul_comm, pow_mul]
    exact h2
  · obtain ⟨k, hk⟩ := hN
    rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, hu, one_pow, one_mul]

private theorem sca_exists_ne_of_isAhatIntr {J : Subgroup X} {s : X} (hJ : IsAhatIntr X s J) :
    ∃ r ∈ J, r ^ 2 = 1 ∧ r ≠ 1 ∧ r ≠ s := by
  obtain ⟨hJC, hsJ, -, m, hm, hdc⟩ := hJ
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, y, -, hy2, hyZ, -⟩ := AhatData.exists_hub hm (AhatData.CoverSetup.ofCover hdc)
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨r, hr2, hry⟩ :=
    sca_exists_sq_eq_one_mk (pPrimeCore 2 ↥J) hodd y (by rw [sq]; exact hy2)
  have hsZ : (⟨s, hsJ⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hJC g.2))
  have hmkZ : ∀ z : ↥J, z ∈ center ↥J →
      (z : ↥J ⧸ pPrimeCore 2 ↥J) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := fun z hz =>
    Subgroup.map_center_le_center (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hz)
  refine ⟨r, r.2, ?_, ?_, ?_⟩
  · have h := congrArg Subtype.val hr2
    simpa using h
  · intro h
    have hr : r = 1 := Subtype.ext h
    apply hyZ
    rw [← hry, hr, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  · intro h
    have hr : r = ⟨s, hsJ⟩ := Subtype.ext h
    apply hyZ
    rw [← hry, hr]
    exact hmkZ _ hsZ

private theorem sca_exists_four_of_isAhatIntr {s : X} {D J : Subgroup X} (hs : orderOf s = 2)
    (hsD : s ∈ D) (hJ : IsAhatIntr X s J) (hJD : J ≤ (D ⊓ cen s) ⊔ oddCoreOf (cen s)) :
    ∃ B : Subgroup X, B ≤ D ∧ CFSG.Open.IsElemAbelian 2 B ∧ Nat.card B = 4 := by
  obtain ⟨r, hrJ, hr2, hr1, hrs⟩ := sca_exists_ne_of_isAhatIntr hJ
  have hr2' : r ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hr2
  obtain ⟨o, ho, a, ha, ha2, hra⟩ := exists_conj_twoElt_of_mem_sup_odd_X
    (A := D ⊓ cen s) (N := oddCoreOf (cen s))
    (fun c hc => le_normalizer_oddCoreOf (cen s) (Subgroup.mem_inf.1 hc).2)
    (odd_card_oddCoreOf _) (hJD hrJ) hr2'
  rw [pow_one] at ha2
  have hoC : o ∈ cen s := oddCoreOf_le _ ho
  have haD : a ∈ D := (Subgroup.mem_inf.1 ha).1
  have ha1 : a ≠ 1 := by
    intro h
    apply hr1
    rw [hra, h, mul_one, mul_inv_cancel]
  have has : a ≠ s := by
    intro h
    apply hrs
    have hcomm : o * s = s * o := Subgroup.mem_centralizer_singleton_iff.1 hoC
    rw [hra, h, hcomm, mul_inv_cancel_right]
  have hsa : s * a = a * s :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2).symm
  have hss : s * s = 1 := sca_mul_self hs
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact ha2
  exact ⟨scaFour hss haa hsa, sca_four_le hsD haD, sca_four_isElemAbelian,
    sca_four_card (sca_ne_one hs) ha1 has.symm⟩

private theorem sca_exists_four_of_sec6KComp {n : ℕ} {H F : Subgroup X}
    (hF : Sec6KComp X n H F) :
    ∃ B : Subgroup X, B ≤ F ∧ CFSG.Open.IsElemAbelian 2 B ∧ Nat.card B = 4 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hF with ⟨⟨u, hu⟩, -⟩ | ⟨⟨hpc, -, hJ⟩, -⟩
  · obtain ⟨hu2, huF, -, -, Lu, hLu, hLueq⟩ := hu
    refine sca_exists_four_of_isAhatIntr hu2 huF hLu (hLueq.le.trans (sup_le ?_ ?_))
    · exact (pPrimeCoreOf_le_oddCoreOf hLu.1 (isPComponent_two_iff.1 hLu.2.2.1).1).trans
        le_sup_right
    · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
      exact (oTwoPrimeOf_le _).trans le_sup_left
  · obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 2
      (sca_two_dvd_card (sca_isTwoGenQuasi hpc))
    have hs2 : orderOf (s : X) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hs
    obtain ⟨J, hJs, hJle⟩ := hJ s s.2 hs2
    exact sca_exists_four_of_isAhatIntr hs2 s.2 hJs hJle

private theorem sca_exists_ne_ne {B : Subgroup X} (hB4 : Nat.card B = 4) (m : X) :
    ∃ w ∈ B, w ≠ 1 ∧ w ≠ m := by
  by_contra hno
  push Not at hno
  have hsub : (B : Set X) ⊆ {1, m} := fun y hy => by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (hno y hy h1)
  have hle : Nat.card B ≤ 2 := by
    calc Nat.card B = Nat.card ↥(B : Set X) := rfl
      _ = (B : Set X).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, m} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({m} : Set X).ncard + 1 := Set.ncard_insert_le 1 {m}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

private theorem sca_K0_le {n : ℕ} (H : Subgroup X) : K0 X n H ≤ H := by
  rw [K0_eq_sSup_sec5Comp]
  exact sSup_le fun A hA => hA.1.choose_spec.2.2.1.1

private theorem sca_base_le_cen {n : ℕ} (t : X) : Sec6Base X n t ≤ cen t :=
  sup_le (Sec6Fus.sec6M_le n _) ((Sec6Fus.zStar_le _).trans (sca_K0_le _))

private theorem sca_t_mem_zStar {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hA : K0 X n (cen t) ≠ ⊥) : t ∈ zStar (K0 X n (cen t)) := by
  have htA : t ∈ K0 X n (cen t) := hS.central hA
  refine Subgroup.mem_inf.2 ⟨htA, Subgroup.le_normalizer htA,
    normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer htA), fun k hk => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.2 (sca_comm (sca_K0_le _ hk))]
  exact one_mem _

private theorem sca_t_mem_base {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hA : K0 X n (cen t) ≠ ⊥) : t ∈ Sec6Base X n t :=
  Subgroup.mem_sup_right (sca_t_mem_zStar hS hA)

private theorem sca_iSup_subgroupOf_eq {H : Subgroup X} (S : Finset (Subgroup X))
    (hle : ∀ L ∈ S, L ≤ H) : ⨆ L ∈ S, L.subgroupOf H = (⨆ L ∈ S, L).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (iSup₂_le hle)]
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun L => iSup_congr fun hL => Subgroup.map_subgroupOf_eq_of_le (hle L hL)

private theorem sca_not_mem_sec6M
    {n : ℕ} {t : X} (ht : orderOf t = 2) : t ∉ Sec6M X n (cen t) := by
  classical
  intro htM
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hMS, -⟩ := modOddCard_Sec6M_eq_prod_of_centerFree (n := n) mcLLyCenterFree (cen t)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(cen t)) with hπ
  have hpc : ∀ L ∈ S, IsPComponent 2 (L.subgroupOf (cen t)) := fun L hL => ((hS L).1 hL).1.1.2
  have hLC : ∀ L ∈ S, L ≤ cen t := fun L hL => ((hS L).1 hL).1.1.1
  have hT1 : ∀ L ∈ S, ∀ L' ∈ S, L ≠ L' → ∀ a ∈ (L.subgroupOf (cen t)).map π,
      ∀ b ∈ (L'.subgroupOf (cen t)).map π, a * b = b * a := by
    intro L hL L' hL' hne a ha b hb
    have hne' : L.subgroupOf (cen t) ≠ L'.subgroupOf (cen t) := by
      intro h
      apply hne
      rw [Subgroup.subgroupOf_inj, inf_of_le_left (hLC L hL), inf_of_le_left (hLC L' hL')] at h
      exact h
    exact (commute_of_mem_map_of_isPComponent (hpc L hL) (hpc L' hL') hne' ha hb).eq
  have hT2 : ∀ L ∈ S, ∀ a ∈ (L.subgroupOf (cen t)).map π,
      (∀ b ∈ (L.subgroupOf (cen t)).map π, a * b = b * a) → a = 1 := by
    intro L hL a ha hab
    have hsub : (L.subgroupOf (cen t)).IsSubnormal := (isPComponent_two_iff.1 (hpc L hL)).1
    obtain ⟨e₁⟩ := nonempty_quot_pPrimeCore_mulEquiv_map hsub
    obtain ⟨e₂⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe (hLC L hL))
    have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := mcLLyCenterFree _ ((hS L).1 hL).1.2.1
    have hZ' : center ↥((L.subgroupOf (cen t)).map π) = ⊥ := by
      rw [← Subgroup.map_center_eq (e₂.symm.trans e₁), hZ, Subgroup.map_bot]
    have hmem : (⟨a, ha⟩ : ↥((L.subgroupOf (cen t)).map π)) ∈
        center ↥((L.subgroupOf (cen t)).map π) := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hab b b.2).symm
    rw [hZ'] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  set t' : ↥(cen t) := ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with ht'
  have hT3 : ∀ y, y * π t' = π t' * y := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(cen t)) y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact sca_comm y.2
  have hT4 : ∀ S' : Finset (Subgroup X), S' ⊆ S →
      π t' ∈ ⨆ L ∈ S', (L.subgroupOf (cen t)).map π → π t' = 1 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      intro _ h
      simpa using h
    | insert L S' hLS' ih =>
      intro hsub hmem
      rw [Finset.iSup_insert] at hmem
      have hLS : L ∈ S := hsub (Finset.mem_insert_self L S')
      have hS'S : S' ⊆ S := (Finset.subset_insert L S').trans hsub
      have hcomm : ∀ a ∈ (L.subgroupOf (cen t)).map π,
          ∀ b ∈ ⨆ L' ∈ S', (L'.subgroupOf (cen t)).map π, a * b = b * a := by
        intro a ha b hb
        have hle : ⨆ L' ∈ S', (L'.subgroupOf (cen t)).map π ≤
            centralizer (((L.subgroupOf (cen t)).map π : Subgroup _) : Set _) := by
          refine iSup₂_le fun L' hL' => ?_
          intro c hc
          rw [Subgroup.mem_centralizer_iff]
          intro d hd
          exact hT1 L hLS L' (hS'S hL') (fun h => hLS' (h ▸ hL')) d hd c hc
        exact Subgroup.mem_centralizer_iff.1 (hle hb) a ha
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_eq_of_mem_sup_of_mul_comm hcomm hmem
      have ha1 : a = 1 := by
        refine hT2 L hLS a ha fun c hc => ?_
        have hbc : Commute b c := (hcomm c hc b hb).symm
        have hbc' : b⁻¹ * c = c * b⁻¹ := hbc.inv_left.eq
        have ha' : a = π t' * b⁻¹ := by rw [← hab]; group
        rw [ha']
        calc π t' * b⁻¹ * c = π t' * (b⁻¹ * c) := mul_assoc _ _ _
          _ = π t' * (c * b⁻¹) := by rw [hbc']
          _ = (π t' * c) * b⁻¹ := (mul_assoc _ _ _).symm
          _ = (c * π t') * b⁻¹ := by rw [← hT3 c]
          _ = c * (π t' * b⁻¹) := mul_assoc _ _ _
      rw [ha1, one_mul] at hab
      exact ih hS'S (hab ▸ hb)
  have ht'M : t' ∈ (⨆ L ∈ S, L).subgroupOf (cen t) := by
    rw [Subgroup.mem_subgroupOf, ← hMS]
    exact htM
  rw [← sca_iSup_subgroupOf_eq S hLC] at ht'M
  have hmem : π t' ∈ ⨆ L ∈ S, (L.subgroupOf (cen t)).map π := by
    have h1 : π t' ∈ (⨆ L ∈ S, L.subgroupOf (cen t)).map π := ⟨t', ht'M, rfl⟩
    simpa only [Subgroup.map_iSup] using h1
  have h1 := hT4 S (subset_refl S) hmem
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(cen t))) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have ht'2 : orderOf t' = 2 := by
    rw [ht', Subgroup.orderOf_mk]
    exact ht
  have := sca_not_mem_odd (X := ↥(cen t)) hodd ht'2
  exact this h1

private abbrev ScaUnp (n : ℕ) (t : X) : Prop :=
  ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
    Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x

private abbrev ScaExt (n : ℕ) (t : X) : Prop :=
  ∀ E : Subgroup X, E ≤ Sec6Base X n t → CFSG.Open.IsElemAbelian 2 E → 8 ≤ Nat.card E →
    (∃ B : Subgroup X, B ≤ E ⊓ Sec6M X n (cen t) ∧ CFSG.Open.IsElemAbelian 2 B ∧
      Nat.card B = 4) →
    ∀ B : Subgroup X, B ≤ E → CFSG.Open.IsElemAbelian 2 B → Nat.card B = 4 →
      (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t

private theorem sca_le_sec6M {n : ℕ} {H M : Subgroup X} (hM : Sec6MComp X n H M) :
    M ≤ Sec6M X n H :=
  le_sSup (s := {M | Sec6MComp X n H M}) hM

private theorem sca_le_sec6K {n : ℕ} {H L : Subgroup X} (hL : Sec6KComp X n H L) :
    L ≤ Sec6K X n H :=
  le_sSup (s := {L | Sec6KComp X n H L}) hL

private theorem sca_le_K0 {n : ℕ} {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    A ≤ K0 X n H := by
  rw [K0_eq_sSup_sec5Comp]
  exact le_sSup hA

private theorem sca_piece_le {L : Subgroup X} {y : X} : sec6Piece L y ≤ L :=
  (oTwoPrimeOf_le _).trans inf_le_left

private theorem sca_piece_le_cen {L : Subgroup X} {y : X} : sec6Piece L y ≤ cen y :=
  (oTwoPrimeOf_le _).trans inf_le_right

private theorem sca_exists_w {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hU : ScaUnp n t) {m : X} (hm : m ∈ Sec6M X n (cen t)) (hm2 : orderOf m = 2) :
    ∃ w ∈ Sec6M X n (cen t) ⊓ cen m, orderOf w = 2 ∧ w ≠ m := by
  obtain ⟨M, hM⟩ := hS.choice.hasM
  have hmb : m ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hm
  obtain ⟨F, hF, hPF⟩ := hC.land m hmb hm2 M (Or.inr hM)
  have hFeq := hU m hm hm2 M F hM hF hPF
  obtain ⟨B, hBF, hBe, hB4⟩ := sca_exists_four_of_sec6KComp hF
  have hPO : sec6Piece M m ≤ normalizer (oddCoreOf F : Set X) :=
    hPF.trans (le_normalizer_oddCoreOf F)
  have hBle : B ≤ sec6Piece M m ⊔ oddCoreOf F := by
    rw [sup_comm, ← hFeq]
    exact hBF
  obtain ⟨o, -, B', hB'P, hB'e, hB'4, -⟩ :=
    sca_exists_four_conj hPO (odd_card_oddCoreOf F) hBe hB4 hBle
  obtain ⟨w, hwB', hw1, hwm⟩ := sca_exists_ne_ne hB'4 m
  have hwP := hB'P hwB'
  refine ⟨w, Subgroup.mem_inf.2 ⟨sca_le_sec6M hM (sca_piece_le hwP), sca_piece_le_cen hwP⟩,
    sca_orderOf_two (by rw [← sq]; exact hB'e.2 w hwB') hw1, hwm⟩

private theorem sca_good_mt
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {m : X}
    (hm : m ∈ Sec6M X n (cen t)) (hm2 : orderOf m = 2) (ha : m * m = 1) (hb : t * t = 1)
    (hab : m * t = t * m) : scaV (scaFour ha hb hab) = sec6Sig X n t := by
  obtain ⟨w, ⟨hwM, hwm⟩, hw2, hwne⟩ := sca_exists_w hS hC hU hm hm2
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htM : t ∉ Sec6M X n (cen t) := sca_not_mem_sec6M ht2
  have hmw : m * w = w * m := (sca_comm hwm).symm
  set E₀ := scaFour ha (sca_mul_self hw2) hmw with hE₀
  have hE₀M : E₀ ≤ Sec6M X n (cen t) := sca_four_le hm hwM
  have hE₀4 : Nat.card E₀ = 4 := sca_four_card (sca_ne_one hm2) (sca_ne_one hw2) hwne.symm
  have htE₀ : ∀ b ∈ E₀, t * b = b * t := fun b hb' =>
    (sca_comm (Sec6Fus.sec6M_le n _ (hE₀M hb'))).symm
  obtain ⟨hEe, hEcard⟩ := sca_sup_zpowers (sca_four_isElemAbelian (hab := hmw)) hb htE₀
  have hE8 : 8 ≤ Nat.card ↥(E₀ ⊔ zpowers t) := by
    rw [hEcard (fun h => htM (hE₀M h)), hE₀4]
  have hEB : E₀ ⊔ zpowers t ≤ Sec6Base X n t :=
    sup_le (hE₀M.trans le_sup_left) ((Subgroup.zpowers_le).2 (sca_t_mem_base hS hA))
  have hmE : m ∈ E₀ ⊔ zpowers t := Subgroup.mem_sup_left sca_left_mem_four
  have htE : t ∈ E₀ ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hmt : m ≠ t := fun h => htM (h ▸ hm)
  exact hext _ hEB hEe hE8 ⟨E₀, le_inf le_sup_left hE₀M, sca_four_isElemAbelian, hE₀4⟩ _
    (sca_four_le hmE htE) sca_four_isElemAbelian
    (sca_four_card (sca_ne_one hm2) (sca_ne_one ht2) hmt)

private theorem sca_propagate
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t) {E : Subgroup X}
    (hEB : E ≤ Sec6Base X n t) (hE : CFSG.Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E)
    {B₀ : Subgroup X} (hB₀E : B₀ ≤ E) (hB₀4 : Nat.card B₀ = 4) {W : Subgroup X}
    (hB₀ : scaV B₀ = W) {B : Subgroup X} (hBE : B ≤ E) (hB4 : Nat.card B = 4) :
    scaV B = W := by
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => sca_comm_of_sq hE.2 hx hy
  have hinv : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    sca_orderOf_two (by rw [← sq]; exact hE.2 x hx) hx1
  have hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b) :=
    fun a ha ha1 b hb hb1 => sec6_base_balance hS hC (hEB ha) (hEB hb) (hinv a ha ha1)
      (hinv b hb hb1) (hEcomm a ha b hb)
  obtain ⟨-, -, hV⟩ := sec6_lambda2 hE hE8 hbal
  have h1 : scaV B = scaV B₀ := (hV B hBE hB4).trans (hV B₀ hB₀E hB₀4).symm
  rw [h1, hB₀]

private theorem sca_exists_inv_cen {n : ℕ} {t : X} (hS : Sec6Setting X n t) {y : X}
    (hyt : y ∈ cen t) (hy : y * y = 1) :
    ∃ m ∈ Sec6M X n (cen t) ⊓ cen y, orderOf m = 2 := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Sec6M X n (cen t) with hMdef
  have hyM : y ∈ normalizer (M : Set X) := Sec6M_cen_normal n t hyt
  obtain ⟨L, hL⟩ := hS.choice.hasM
  have hLM : L ≤ M := sca_le_sec6M hL
  have h2L : 2 ∣ Nat.card L := sca_two_dvd_card (sca_isTwoGenQuasi hL.1.1)
  have h2M : 2 ∣ Nat.card M := h2L.trans (Subgroup.card_dvd_of_le hLM)
  let f : Function.End ↥M := fun m => ⟨y * m * y⁻¹, sca_conj_mem hyM m.2⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext m
    apply Subtype.ext
    show y * (y * (m : X) * y⁻¹) * y⁻¹ = (m : X)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    rw [hyi]
    calc y * (y * (m : X) * y) * y = (y * y) * (m : X) * (y * y) := by group
      _ = (m : X) := by rw [hy, one_mul, mul_one]
  haveI : Fintype ↥M := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2
  have hfix : Fintype.card (Function.fixedPoints f) = Nat.card ↥(M ⊓ cen y) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun m => ⟨(m.1 : X), m.1.2, ?_⟩
        invFun := fun m => ⟨⟨(m : X), m.2.1⟩, ?_⟩
        left_inv := fun m => rfl
        right_inv := fun m => rfl }
    · have h := congrArg Subtype.val m.2
      change y * (m.1 : X) * y⁻¹ = (m.1 : X) at h
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc (m.1 : X) * y = y * (m.1 : X) * y⁻¹ * y := by rw [h]
        _ = y * (m.1 : X) := by group
    · apply Subtype.ext
      show y * (m : X) * y⁻¹ = (m : X)
      rw [← sca_comm m.2.2, mul_inv_cancel_right]
  have hM2 : Fintype.card ↥M % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.mod_eq_zero_of_dvd h2M
  have hfix2 : Fintype.card (Function.fixedPoints f) % 2 = 0 := by
    rw [← hM2]
    exact hmod.symm
  have h2C : 2 ∣ Nat.card ↥(M ⊓ cen y) := by
    rw [← hfix]
    exact Nat.dvd_of_mod_eq_zero hfix2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ cen y)) 2 h2C
  refine ⟨(g : X), g.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hg

private theorem sca_four_mul_eq {y t : X} (hy : y * y = 1) (ht : t * t = 1)
    (hyt : y * t = t * y) (hm : y * t * (y * t) = 1) (hmt : y * t * t = t * (y * t)) :
    scaFour hy ht hyt = scaFour hm ht hmt := by
  ext x
  simp only [Holt.StarLemma26.mem_fourSubgroup]
  have e : y * t * t = y := by rw [mul_assoc, ht, mul_one]
  rw [e]
  tauto

private theorem sca_good_yt
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) (hyt : y ≠ t) (ha : y * y = 1)
    (hb : t * t = 1) (hab : y * t = t * y) : scaV (scaFour ha hb hab) = sec6Sig X n t := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htM : t ∉ Sec6M X n (cen t) := sca_not_mem_sec6M ht2
  have hyC : y ∈ cen t := sca_base_le_cen t hyB
  obtain ⟨m, ⟨hmM, hmy⟩, hm2⟩ := sca_exists_inv_cen hS hyC ha
  have hmt : m * t = t * m := sca_comm (Sec6Fus.sec6M_le n _ hmM)
  by_cases hmy' : m = y
  · subst hmy'
    exact sca_good_mt hS hC hA hU hext hmM hm2 ha hb hab
  by_cases hmyt : m = y * t
  · have hm' : y * t * (y * t) = 1 := by rw [← hmyt]; exact sca_mul_self hm2
    have hmt' : y * t * t = t * (y * t) := by rw [← hmyt]; exact hmt
    rw [sca_four_mul_eq ha hb hab hm' hmt']
    exact sca_good_mt hS hC hA hU hext (hmyt ▸ hmM) (hmyt ▸ hm2) hm' hb hmt'
  have hmyc : m * y = y * m := sca_comm hmy
  have hmF : ∀ b ∈ scaFour ha hb hab, m * b = b * m := by
    intro b hb'
    rcases Holt.StarLemma26.mem_fourSubgroup.1 hb' with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hmyc
    · exact hmt
    · rw [← mul_assoc, hmyc, mul_assoc, hmt, ← mul_assoc]
  have hmnot : m ∉ scaFour ha hb hab := by
    intro h
    rcases Holt.StarLemma26.mem_fourSubgroup.1 h with h | h | h | h
    · exact sca_ne_one hm2 h
    · exact hmy' h
    · exact htM (h ▸ hmM)
    · exact hmyt h
  obtain ⟨hEe, hEcard⟩ := sca_sup_zpowers (sca_four_isElemAbelian (hab := hab))
    (sca_mul_self hm2) hmF
  have hE4 : Nat.card (scaFour ha hb hab) = 4 := sca_four_card (sca_ne_one hy2) (sca_ne_one ht2) hyt
  have hE8 : 8 ≤ Nat.card ↥(scaFour ha hb hab ⊔ zpowers m) := by
    rw [hEcard hmnot, hE4]
  have hEB : scaFour ha hb hab ⊔ zpowers m ≤ Sec6Base X n t :=
    sup_le (sca_four_le hyB (sca_t_mem_base hS hA))
      ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_left hmM))
  have hmE : m ∈ scaFour ha hb hab ⊔ zpowers m := Subgroup.mem_sup_right (Subgroup.mem_zpowers m)
  have htE : t ∈ scaFour ha hb hab ⊔ zpowers m := Subgroup.mem_sup_left sca_right_mem_four
  have hmt1 : m ≠ t := fun h => htM (h ▸ hmM)
  exact sca_propagate hS hC hEB hEe hE8 (sca_four_le hmE htE (hab := hmt))
    (sca_four_card (sca_ne_one hm2) (sca_ne_one ht2) hmt1)
    (sca_good_mt hS hC hA hU hext hmM hm2 (sca_mul_self hm2) hb hmt) le_sup_left hE4

private theorem sca_exists_inv_Mt {n : ℕ} {t : X} (hS : Sec6Setting X n t) :
    ∃ m ∈ Sec6M X n (cen t), orderOf m = 2 := by
  obtain ⟨L, hL⟩ := hS.choice.hasM
  obtain ⟨m, hmL, hm2⟩ := Sec6L51B.exists_involution_of_isTwoGenQuasi (sca_isTwoGenQuasi hL.1.1)
  exact ⟨m, sca_le_sec6M hL hmL, hm2⟩

private theorem sca_odd_le_V
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) :
    oddCoreOf (cen y) ≤ sec6Sig X n t := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  by_cases hyt : y = t
  · subst hyt
    obtain ⟨m, hmM, hm2⟩ := sca_exists_inv_Mt hS
    have hmt : m * y = y * m := sca_comm (Sec6Fus.sec6M_le n _ hmM)
    rw [← sca_good_mt hS hC hA hU hext hmM hm2 (sca_mul_self hm2) (sca_mul_self ht2) hmt]
    exact sca_le_V sca_right_mem_four (sca_ne_one ht2)
  · have hab : y * t = t * y := sca_comm (sca_base_le_cen t hyB)
    rw [← sca_good_yt hS hC hA hU hext hyB hy2 hyt (sca_mul_self hy2) (sca_mul_self ht2) hab]
    exact sca_le_V sca_left_mem_four (sca_ne_one hy2)

private theorem sca_N_ne_top
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t)
    (hne : sec6Sig X n t ≠ ⊥) : normalizer (sec6Sig X n t : Set X) ≠ ⊤ := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htM : t ∉ Sec6M X n (cen t) := sca_not_mem_sec6M ht2
  obtain ⟨m, hmM, hm2⟩ := sca_exists_inv_Mt hS
  obtain ⟨w, ⟨hwM, hwm⟩, hw2, hwne⟩ := sca_exists_w hS hC hU hmM hm2
  have hmw : m * w = w * m := (sca_comm hwm).symm
  set E₀ := scaFour (sca_mul_self hm2) (sca_mul_self hw2) hmw with hE₀
  have hE₀M : E₀ ≤ Sec6M X n (cen t) := sca_four_le hmM hwM
  have htE₀ : ∀ b ∈ E₀, t * b = b * t := fun b hb' =>
    (sca_comm (Sec6Fus.sec6M_le n _ (hE₀M hb'))).symm
  obtain ⟨hEe, hEcard⟩ := sca_sup_zpowers (sca_four_isElemAbelian (hab := hmw))
    (sca_mul_self ht2) htE₀
  have hE₀4 : Nat.card E₀ = 4 := sca_four_card (sca_ne_one hm2) (sca_ne_one hw2) hwne.symm
  have hE8 : 8 ≤ Nat.card ↥(E₀ ⊔ zpowers t) := by
    rw [hEcard (fun h => htM (hE₀M h)), hE₀4]
  have hEB : E₀ ⊔ zpowers t ≤ Sec6Base X n t :=
    sup_le (hE₀M.trans le_sup_left) ((Subgroup.zpowers_le).2 (sca_t_mem_base hS hA))
  set E := E₀ ⊔ zpowers t with hE
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => sca_comm_of_sq hEe.2 hx hy
  have hinv : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    sca_orderOf_two (by rw [← sq]; exact hEe.2 x hx) hx1
  have hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b) :=
    fun a ha ha1 b hb hb1 => sec6_base_balance hS hC (hEB ha) (hEB hb) (hinv a ha ha1)
      (hinv b hb hb1) (hEcomm a ha b hb)
  obtain ⟨hodd, -, hV⟩ := sec6_lambda2 hEe hE8 hbal
  have hVE : sec6Sig X n t = ⨆ (a : X) (_ : a ∈ E) (_ : a ≠ 1), oddCoreOf (cen a) := by
    have h1 := hext E hEB hEe hE8 ⟨E₀, le_inf le_sup_left hE₀M, sca_four_isElemAbelian, hE₀4⟩
      E₀ le_sup_left sca_four_isElemAbelian hE₀4
    rw [← h1]
    exact hV E₀ le_sup_left hE₀4
  have hVodd : Odd (Nat.card ↥(sec6Sig X n t)) := by
    rw [hVE]
    exact hodd
  intro htop
  haveI := hS.cex.simple
  haveI hnorm : (sec6Sig X n t).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sec6Sig X n t) with h | h
  · exact hne h
  · have htV : t ∈ sec6Sig X n t := by
      rw [h]
      exact Subgroup.mem_top t
    exact sca_not_mem_odd hVodd ht2 htV

private theorem sca_good_of_le
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) {B : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB4 : Nat.card B = 4)
    (hBle : B ≤ (Sec6M X n (cen t) ⊓ cen y) ⊔ oddCoreOf (cen y)) :
    scaV B = sec6Sig X n t := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htM : t ∉ Sec6M X n (cen t) := sca_not_mem_sec6M ht2
  have hAO : Sec6M X n (cen t) ⊓ cen y ≤ normalizer (oddCoreOf (cen y) : Set X) :=
    fun c hc => le_normalizer_oddCoreOf (cen y) hc.2
  obtain ⟨o, ho, B', hB'le, hB'e, hB'4, rfl⟩ :=
    sca_exists_four_conj hAO (odd_card_oddCoreOf _) hB hB4 hBle
  have hB'M : B' ≤ Sec6M X n (cen t) := hB'le.trans inf_le_left
  have htB' : ∀ b ∈ B', t * b = b * t := fun b hb' =>
    (sca_comm (Sec6Fus.sec6M_le n _ (hB'M hb'))).symm
  obtain ⟨hEe, hEcard⟩ := sca_sup_zpowers hB'e (sca_mul_self ht2) htB'
  have hE8 : 8 ≤ Nat.card ↥(B' ⊔ zpowers t) := by
    rw [hEcard (fun h => htM (hB'M h)), hB'4]
  have hEB : B' ⊔ zpowers t ≤ Sec6Base X n t :=
    sup_le (hB'M.trans le_sup_left) ((Subgroup.zpowers_le).2 (sca_t_mem_base hS hA))
  have hB'good : scaV B' = sec6Sig X n t :=
    hext _ hEB hEe hE8 ⟨B', le_inf le_sup_left hB'M, hB'e, hB'4⟩ B' le_sup_left hB'e hB'4
  have hoV : o ∈ normalizer (sec6Sig X n t : Set X) :=
    Subgroup.le_normalizer (sca_odd_le_V hS hC hA hU hext hyB hy2 ho)
  exact sca_V_conj hB'good hoV

private theorem sca_cen_le_of_family
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) {H : Subgroup X}
    (hHle : H ≤ (Sec6M X n (cen t) ⊓ cen y) ⊔ oddCoreOf (cen y))
    (hHn : cen y ≤ normalizer (H : Set X))
    (hH4 : ∃ B : Subgroup X, B ≤ H ∧ CFSG.Open.IsElemAbelian 2 B ∧ Nat.card B = 4) :
    cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  obtain ⟨B₀, hB₀H, hB₀e, hB₀4⟩ := hH4
  intro g hg
  have hgH := map_conj_eq_of_mem_normalizer (hHn hg)
  have hB₀gH : B₀.map (MulAut.conj g).toMonoidHom ≤ H := by
    rw [← hgH]
    exact Subgroup.map_mono hB₀H
  have hB₀g4 : Nat.card ↥(B₀.map (MulAut.conj g).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hB₀4
  exact sca_mem_normalizer_of_V
    (sca_good_of_le hS hC hA hU hext hyB hy2 hB₀e hB₀4 (hB₀H.trans hHle))
    (sca_good_of_le hS hC hA hU hext hyB hy2 (sca_isElemAbelian_map _ hB₀e) hB₀g4
      (hB₀gH.trans hHle))

private def scaComm (N : Subgroup X) (g : X) : Subgroup X where
  carrier := {k | k ∈ normalizer (N : Set X) ∧ ⁅k, g⁆ ∈ N}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h : ⁅a * b, g⁆ = a * ⁅b, g⁆ * a⁻¹ * ⁅a, g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact N.mul_mem (sca_conj_mem ha hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have h : ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact sca_conj_mem (inv_mem ha) (N.inv_mem ha')

private theorem sca_comm_mem_of_mem {O : Subgroup X} {o g : X} (ho : o ∈ O)
    (hg : g ∈ normalizer (O : Set X)) : ⁅o, g⁆ ∈ O := by
  have : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact O.mul_mem ho (sca_conj_mem hg (O.inv_mem ho))

private theorem sca_centModOdd_of_cover {F R : Subgroup X} {g : X} (hRF : R ≤ F)
    (hcov : F = oddCoreOf F ⊔ R) (hgO : g ∈ normalizer (oddCoreOf F : Set X))
    (hR : ∀ r ∈ R, ⁅r, g⁆ ∈ oddCoreOf F) : CentModOdd F g := by
  have hle : oddCoreOf F ⊔ R ≤ scaComm (oddCoreOf F) g :=
    sup_le (fun o ho => ⟨le_normalizer ho, sca_comm_mem_of_mem ho hgO⟩)
      (fun r hr => ⟨le_normalizer_oddCoreOf F (hRF hr), hR r hr⟩)
  intro a ha
  have ha' : a ∈ oddCoreOf F ⊔ R := by
    rw [← hcov]
    exact ha
  exact (hle ha').2

private theorem sca_cov {E K : Subgroup X} (hEK : E ≤ K)
    (hcov : E.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) : K = oddCoreOf K ⊔ E :=
  ((covers_subgroupOf_iff hEK).1 hcov).symm.trans (sup_comm _ _)

private theorem sca_oddCoreOf_le {H F : Subgroup X} (hF : IsPCompIn 2 H F) :
    oddCoreOf F ≤ oddCoreOf H :=
  pPrimeCoreOf_le_oddCoreOf hF.1 (isPComponent_two_iff.1 hF.2).1

private theorem sca_card_lt
    {n : ℕ} {Q K : Type} [Group Q] [Group K] (hT : IsSec6MType n Q)
    (hK : IsDoubleCoverOfAlt K n) : Nat.card K < Nat.card Q := by
  have hcardK : Nat.card K ≤ 2 * Nat.factorial n := by
    obtain ⟨-, hc, ⟨e⟩⟩ := hK
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
    rw [Nat.card_congr e.toEquiv, hc] at h1
    have h2 : Nat.card (alternatingGroup (Fin n)) ≤ Nat.factorial n := by
      calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
            Subgroup.card_le_card_group _
        _ = Nat.factorial n := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    omega
  rcases hT with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]
    have h8 : Nat.factorial 8 = 40320 := by norm_num [Nat.factorial]
    omega
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ly.card_Ly']
    have h11 : Nat.factorial 11 = 39916800 := by norm_num [Nat.factorial]
    omega

private theorem sca_false_of_types
    {n : ℕ} {F L P : Subgroup X} (hPF : P ≤ F) (hF : F = oddCoreOf F ⊔ P) (hPL : P ≤ L)
    (hL : L = oddCoreOf L ⊔ P) (hFt : IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F))
    (hLt : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) : False := by
  have h1 : modOddCard P = modOddCard F := modOddCard_eq_of_covers hPF hF
  have h2 : modOddCard P = modOddCard L := modOddCard_eq_of_covers hPL hL
  have h3 := sca_card_lt hFt hLt
  unfold modOddCard at h1 h2
  omega

private theorem sca_sec6M_le_QOf
    {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec5Comp X n (cen t) L) :
    Sec6M X n (cen t) ≤ QOf L := by
  refine sSup_le fun M hM => ?_
  exact Sec6Fus.le_QOf_of_ne (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL))
    (Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hM))
    (Sec6Fus.ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hL hM)

private theorem sca_K0_le_normalizer {n : ℕ} {t : X} {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : K0 X n (cen t) ≤ normalizer (L : Set X) := by
  rw [K0_eq_sSup_sec5Comp]
  exact Sec6Fus.sSup_le_normalizer (Sec6Fus.isPCompIn_of_sec6KComp hL)
    fun J hJ => Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hJ)

private theorem sca_sec6M_le_normalizer {n : ℕ} {t : X} {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : Sec6M X n (cen t) ≤ normalizer (L : Set X) :=
  Sec6Fus.sSup_le_normalizer (Sec6Fus.isPCompIn_of_sec6KComp hL)
    fun J hJ => Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hJ)

private theorem sca_base_le_normalizer {n : ℕ} {t : X} {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : Sec6Base X n t ≤ normalizer (L : Set X) :=
  sup_le (sca_sec6M_le_normalizer hL) ((Sec6Fus.zStar_le _).trans (sca_K0_le_normalizer hL))

private theorem sca_inf_oddCoreOf_le {L A : Subgroup X} (hLA : L ≤ A) :
    L ⊓ oddCoreOf A ≤ oddCoreOf L :=
  le_oddCoreOf_of_normalized inf_le_left
    (fun c hc => mem_normalizer_inf (le_normalizer hc) (le_normalizer_oddCoreOf A (hLA hc)))
    ((odd_card_oddCoreOf A).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))

private theorem sca_zStar_le_QOf
    {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    zStar (K0 X n (cen t)) ≤ QOf L := by
  rcases hL with hA | hM
  · intro z hz
    have hzN : z ∈ normalizer (L : Set X) := sca_K0_le_normalizer (Or.inl hA) hz.1
    refine mem_QOf_iff.2 ⟨hzN, fun l hl => ?_⟩
    have h1 : ⁅l, z⁆ ∈ L := by
      have e : ⁅l, z⁆ = l * (z * l⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact L.mul_mem hl (sca_conj_mem hzN (L.inv_mem hl))
    exact sca_inf_oddCoreOf_le (sca_le_K0 hA) ⟨h1, hz.2.2.2 l (sca_le_K0 hA hl)⟩
  · have hle : K0 X n (cen t) ≤ QOf L := by
      rw [K0_eq_sSup_sec5Comp]
      refine sSup_le fun A hA => ?_
      exact Sec6Fus.le_QOf_of_ne (Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hM))
        (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hA))
        (Sec6Fus.ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hA hM).symm
    exact (Sec6Fus.zStar_le _).trans hle

private theorem sca_base_le_QOf
    {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec5Comp X n (cen t) L) :
    Sec6Base X n t ≤ QOf L :=
  sup_le (sca_sec6M_le_QOf hL) (sca_zStar_le_QOf (Or.inl hL))

private theorem sca_oddCoreOf_le_oddCoreOf_sec6K {n : ℕ} {b : X} {F : Subgroup X}
    (hF : Sec6KComp X n (cen b) F) : oddCoreOf F ≤ oddCoreOf (Sec6K X n (cen b)) := by
  have hFK : F ≤ Sec6K X n (cen b) := sca_le_sec6K hF
  have h1 : oddCoreOf F ≤ oddCoreOf (cen b) :=
    sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp hF)
  have h2 : oddCoreOf (cen b) ⊓ Sec6K X n (cen b) ≤ oddCoreOf (Sec6K X n (cen b)) := by
    refine le_oddCoreOf_of_normalized inf_le_right (fun k hk => ?_)
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    exact mem_normalizer_inf (le_normalizer_oddCoreOf _ (Sec6Fus.sec6K_le n _ hk))
      (le_normalizer hk)
  exact (le_inf h1 ((oddCoreOf_le F).trans hFK)).trans h2

private theorem sca_zStar_le_Q
    {n : ℕ} {t : X} : zStar (K0 X n (cen t)) ≤ Sec6Q X n (cen t) := by
  intro z hz
  have hzt : z ∈ cen t := sca_K0_le _ hz.1
  have hzK : z ∈ normalizer (Sec6K X n (cen t) : Set X) := Sec6K_cen_normal n t hzt
  have hzO : z ∈ normalizer (oddCoreOf (Sec6K X n (cen t)) : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hzK
  refine Subgroup.mem_inf.2 ⟨hzt, mem_QOf_iff.2 ⟨hzK, fun k hk => ?_⟩⟩
  have hle : Sec6K X n (cen t) ≤ scaComm (oddCoreOf (Sec6K X n (cen t))) z := by
    refine sSup_le fun L hL l hl => ⟨le_normalizer_oddCoreOf _ (sca_le_sec6K hL hl), ?_⟩
    have hzL := mem_QOf_iff.1 (sca_zStar_le_QOf hL hz)
    exact sca_oddCoreOf_le_oddCoreOf_sec6K hL (hzL.2 l hl)
  exact (hle hk).2

private theorem sca_base_le_MQ
    {n : ℕ} {t : X} : Sec6Base X n t ≤ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) :=
  sup_le le_sup_left (sca_zStar_le_Q.trans le_sup_right)

private theorem sca_Q_le_QOf {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec6KComp X n (cen t) L)
    {y : X} (hyQ : y ∈ Sec6Q X n (cen t)) (hyL : y ∈ normalizer (L : Set X)) : y ∈ QOf L := by
  refine mem_QOf_iff.2 ⟨hyL, fun l hl => ?_⟩
  have h1 : ⁅l, y⁆ ∈ L := by
    have e : ⁅l, y⁆ = l * (y * l⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact L.mul_mem hl (sca_conj_mem hyL (L.inv_mem hl))
  exact sca_inf_oddCoreOf_le (sca_le_sec6K hL)
    ⟨h1, (mem_QOf_iff.1 (Subgroup.mem_inf.1 hyQ).2).2 l (sca_le_sec6K hL hl)⟩

private theorem sca_piece_cov {n : ℕ} {t y : X} {L : Subgroup X} (hL : Sec6KComp X n (cen t) L)
    (hy2 : orderOf y = 2) (hyL : y ∈ QOf L) : L = oddCoreOf L ⊔ sec6Piece L y :=
  sca_cov sca_piece_le
    (isPCompIn_restrict (Sec6Fus.isPCompIn_of_sec6KComp hL) (sca_sq hy2) hyL).2

private theorem sca_centModOdd_of_Q {n : ℕ} {t : X} (h61 : Sec6L61 X n t) {y : X}
    (hyQ : y ∈ Sec6Q X n (cen t)) (hy2 : orderOf y = 2) {F : Subgroup X}
    (hF : Sec6KComp X n (cen y) F) (htF : t ∈ normalizer (F : Set X)) : CentModOdd F t := by
  have hcv := h61.a y hyQ hy2
  have hyt : y ∈ cen t := (Subgroup.mem_inf.1 hyQ).1
  have hty : t ∈ cen y := sca_mem_cen_symm hyt
  have htK : t ∈ normalizer (Sec6K X n (cen y) : Set X) := Sec6K_cen_normal n y hty
  have htO : t ∈ normalizer (oddCoreOf (Sec6K X n (cen y)) : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htK
  have hle : oddCoreOf (Sec6K X n (cen y)) ⊔ (Sec6K X n (cen y) ⊓ Sec6K X n (cen t)) ≤
      scaComm (oddCoreOf (Sec6K X n (cen y))) t := by
    refine sup_le (fun o ho => ⟨le_normalizer ho, sca_comm_mem_of_mem ho htO⟩)
      (fun k hk => ⟨le_normalizer_oddCoreOf _ hk.1, ?_⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.2 (sca_comm (Sec6Fus.sec6K_le n _ hk.2))]
    exact one_mem _
  intro f hf
  have hfK : f ∈ Sec6K X n (cen y) := sca_le_sec6K hF hf
  have hf' : f ∈ oddCoreOf (Sec6K X n (cen y)) ⊔ (Sec6K X n (cen y) ⊓ Sec6K X n (cen t)) := by
    unfold Sec6Covers at hcv
    rw [← hcv]
    exact hfK
  have h1 : ⁅f, t⁆ ∈ oddCoreOf (Sec6K X n (cen y)) := (hle hf').2
  have h2 : ⁅f, t⁆ ∈ F := by
    have e : ⁅f, t⁆ = f * (t * f⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact F.mul_mem hf (sca_conj_mem htF (F.inv_mem hf))
  exact sca_inf_oddCoreOf_le (sca_le_sec6K hF) ⟨h2, h1⟩

private theorem sca_eq_piece_of_centModOdd {n : ℕ} {t : X} (hC : Sec6CtrlAt X n t) {y : X}
    (hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hy2 : orderOf y = 2)
    {F : Subgroup X} (hF : Sec6KComp X n (cen y) F)
    (hFt : t ∈ normalizer (F : Set X) → CentModOdd F t) :
    ∃ L, Sec6KComp X n (cen t) L ∧ sec6Piece L y ≤ F ∧ F = oddCoreOf F ⊔ sec6Piece L y := by
  obtain ⟨L, hL, hLF⟩ := hC.piece y hyMQ hy2 F hF
  obtain ⟨htF, hd⟩ := hC.dich y hyMQ hy2 L F hL hF hLF
  rcases hd with heq | ⟨-, hnt, -⟩
  · exact ⟨L, hL, hLF, heq⟩
  · exact absurd (hFt htF) hnt

private theorem sca_eq_piece_of_sec5Comp
    {n : ℕ} {t : X} (hC : Sec6CtrlAt X n t) {y : X}
    (hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hy2 : orderOf y = 2)
    {F L : Subgroup X} (hF : Sec5Comp X n (cen y) F) (hL : Sec6KComp X n (cen t) L)
    (hLF : sec6Piece L y ≤ F) : F = oddCoreOf F ⊔ sec6Piece L y := by
  obtain ⟨-, hd⟩ := hC.dich y hyMQ hy2 L F hL (Or.inl hF) hLF
  rcases hd with heq | ⟨hFM, -⟩
  · exact heq
  · exact absurd rfl (Sec6Fus.ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hF hFM)

private theorem sca_le_of_mpiece {n : ℕ} {t y : X} {F L : Subgroup X}
    (hF : Sec6KComp X n (cen y) F) (hL : Sec6MComp X n (cen t) L)
    (heq : F = oddCoreOf F ⊔ sec6Piece L y) :
    F ≤ (Sec6M X n (cen t) ⊓ cen y) ⊔ oddCoreOf (cen y) := by
  rw [heq]
  refine sup_le ((sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp hF)).trans le_sup_right) ?_
  exact le_sup_of_le_left (le_inf (sca_piece_le.trans (sca_le_sec6M hL)) sca_piece_le_cen)

private theorem sca_cen_le_of_Q
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hyQ : y ∈ Sec6Q X n (cen t)) (hy2 : orderOf y = 2) :
    cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_right hyQ
  have hpiece : ∀ F, Sec6KComp X n (cen y) F →
      ∃ L, Sec6KComp X n (cen t) L ∧ sec6Piece L y ≤ F ∧ F = oddCoreOf F ⊔ sec6Piece L y :=
    fun F hF => sca_eq_piece_of_centModOdd hC hyMQ hy2 hF (sca_centModOdd_of_Q h61 hyQ hy2 hF)
  have hyL : ∀ L, Sec6KComp X n (cen t) L → y ∈ QOf L := fun L hL =>
    sca_Q_le_QOf hL hyQ (sca_base_le_normalizer hL hyB)
  have hMle : Sec6M X n (cen y) ≤ (Sec6M X n (cen t) ⊓ cen y) ⊔ oddCoreOf (cen y) := by
    refine sSup_le fun F hF => ?_
    obtain ⟨L, hL, hLF, heq⟩ := hpiece F (Or.inr hF)
    rcases hL with hLA | hLM
    · exact (sca_false_of_types hLF heq sca_piece_le
        (sca_piece_cov (Or.inl hLA) hy2 (hyL L (Or.inl hLA))) hF.2 hLA.2).elim
    · exact sca_le_of_mpiece (Or.inr hF) hLM heq
  obtain ⟨M, hM⟩ := hS.choice.hasM
  obtain ⟨F, hF, hPF⟩ := hC.land y hyMQ hy2 M (Or.inr hM)
  have heq : F = oddCoreOf F ⊔ sec6Piece M y := by
    obtain ⟨htF, hd⟩ := hC.dich y hyMQ hy2 M F (Or.inr hM) hF hPF
    rcases hd with heq | ⟨-, hnt, -⟩
    · exact heq
    · exact absurd (sca_centModOdd_of_Q h61 hyQ hy2 hF htF) hnt
  have hFM : Sec6MComp X n (cen y) F := by
    rcases hF with hFA | hFM
    · exact (sca_false_of_types sca_piece_le (sca_piece_cov (Or.inr hM) hy2 (hyL M (Or.inr hM)))
        hPF heq hM.2 hFA.2).elim
    · exact hFM
  obtain ⟨B, hBF, hBe, hB4⟩ := sca_exists_four_of_sec6KComp (Or.inr hFM)
  exact sca_cen_le_of_family hS hC hA hU hext hyB hy2 hMle (Sec6M_cen_normal n y)
    ⟨B, hBF.trans (sca_le_sec6M hFM), hBe, hB4⟩

private theorem sca_cen_le_of_A_mpieces
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2)
    (hno : ∀ F, Sec5Comp X n (cen y) F → ∀ A, Sec5Comp X n (cen t) A → ¬ sec6Piece A y ≤ F)
    {F₀ : Subgroup X} (hF₀ : Sec5Comp X n (cen y) F₀) :
    cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  have hAle : K0 X n (cen y) ≤ (Sec6M X n (cen t) ⊓ cen y) ⊔ oddCoreOf (cen y) := by
    rw [K0_eq_sSup_sec5Comp]
    refine sSup_le fun F hF => ?_
    obtain ⟨L, hL, hLF⟩ := hC.piece y hyMQ hy2 F (Or.inl hF)
    have heq := sca_eq_piece_of_sec5Comp hC hyMQ hy2 hF hL hLF
    rcases hL with hLA | hLM
    · exact absurd hLF (hno F hF L hLA)
    · exact sca_le_of_mpiece (Or.inl hF) hLM heq
  obtain ⟨B, hBF, hBe, hB4⟩ := sca_exists_four_of_sec6KComp (Or.inl hF₀)
  exact sca_cen_le_of_family hS hC hA hU hext hyB hy2 hAle (K0_cen_normal n y)
    ⟨B, hBF.trans (sca_le_K0 hF₀), hBe, hB4⟩

private theorem sca_cen_le_of_unpumped
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2)
    (hnoA : ∀ F, ¬ Sec5Comp X n (cen y) F)
    (hunp : ∀ F, Sec6MComp X n (cen y) F → CentModOdd F t) :
    cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  have hMle : Sec6M X n (cen y) ≤ (Sec6M X n (cen t) ⊓ cen y) ⊔ oddCoreOf (cen y) := by
    refine sSup_le fun F hF => ?_
    obtain ⟨L, hL, hLF, heq⟩ :=
      sca_eq_piece_of_centModOdd hC hyMQ hy2 (Or.inr hF) fun _ => hunp F hF
    rcases hL with hLA | hLM
    · exact (sca_false_of_types hLF heq sca_piece_le
        (sca_piece_cov (Or.inl hLA) hy2 (sca_base_le_QOf hLA hyB)) hF.2 hLA.2).elim
    · exact sca_le_of_mpiece (Or.inr hF) hLM heq
  obtain ⟨M, hM⟩ := hS.choice.hasM
  obtain ⟨F, hF, -⟩ := hC.land y hyMQ hy2 M (Or.inr hM)
  have hFM : Sec6MComp X n (cen y) F := hF.resolve_left (hnoA F)
  obtain ⟨B, hBF, hBe, hB4⟩ := sca_exists_four_of_sec6KComp (Or.inr hFM)
  exact sca_cen_le_of_family hS hC hA hU hext hyB hy2 hMle (Sec6M_cen_normal n y)
    ⟨B, hBF.trans (sca_le_sec6M hFM), hBe, hB4⟩

private theorem sca_oddCoreOf_le_of_cov {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) : oddCoreOf F ≤ oddCoreOf K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥F →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hFK)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : x ∈ F.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov ▸ Subgroup.mem_top x
    obtain ⟨f, hf, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨(f : X), hf⟩, ?_⟩
    have h1 : (QuotientGroup.mk (f * o) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk f := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rw [h1]
    rfl
  have hN : ((pPrimeCore 2 ↥F).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hcard : Nat.card ((pPrimeCore 2 ↥F).map φ) ∣ Nat.card (pPrimeCore 2 ↥F) :=
    Subgroup.card_map_dvd _ _
  have hle : (pPrimeCore 2 ↥F).map φ ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
    le_sSup ⟨hN, Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card⟩
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
  rintro _ ⟨a, ha, rfl⟩
  have h2 : φ a = 1 := Subgroup.mem_bot.1 (hle ⟨a, ha, rfl⟩)
  exact ⟨Subgroup.inclusion hFK a, (QuotientGroup.eq_one_iff (Subgroup.inclusion hFK a)).1 h2,
    rfl⟩

private theorem sca_centModOdd_conj {F : Subgroup X} {u o : X} (hoF : o ∈ F)
    (hu : CentModOdd F u) : CentModOdd F (o⁻¹ * u * o) := by
  intro a ha
  have hoa : o * a * o⁻¹ ∈ F := F.mul_mem (F.mul_mem hoF ha) (F.inv_mem hoF)
  have h1 := hu _ hoa
  have e : ⁅a, o⁻¹ * u * o⁆ = o⁻¹ * ⁅o * a * o⁻¹, u⁆ * o⁻¹⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact sca_conj_mem (le_normalizer_oddCoreOf F (F.inv_mem hoF)) h1

private theorem sca_exists_centre {n : ℕ} {y : X} {F P : Subgroup X}
    (hF : Sec5Comp X n (cen y) F) (hPF : P ≤ F) (heq : F = oddCoreOf F ⊔ P) :
    ∃ c ∈ P, orderOf c = 2 ∧ CentModOdd F c := by
  obtain ⟨⟨u, hu⟩, -⟩ := hF
  obtain ⟨hu2, huF, -, hFeq, -⟩ := hu
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hFeq
  have hR : oTwoPrimeOf (F ⊓ centralizer ({u} : Set X)) ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  have hcu : CentModOdd F u := by
    refine sca_centModOdd_of_cover hR hFeq (le_normalizer_oddCoreOf F huF) fun r hr => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (sca_comm (((oTwoPrimeOf_le _).trans inf_le_right) hr))]
    exact one_mem _
  have huPO : u ∈ P ⊔ oddCoreOf F := by
    rw [sup_comm, ← heq]
    exact huF
  have hu2' : u ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact sca_sq hu2
  obtain ⟨o, ho, c, hc, hc2, rfl⟩ := exists_conj_twoElt_of_mem_sup_odd_X
    (A := P) (N := oddCoreOf F) (hPF.trans (le_normalizer_oddCoreOf F)) (odd_card_oddCoreOf F)
    huPO hu2'
  rw [pow_one] at hc2
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply sca_ne_one hu2
    group
  refine ⟨c, hc, sca_orderOf_two (by rw [← sq]; exact hc2) hc1, ?_⟩
  have h := sca_centModOdd_conj (oddCoreOf_le F ho) hcu
  have e : o⁻¹ * (o * c * o⁻¹) * o = c := by group
  rwa [e] at h

private theorem sca_centre_unique {n : ℕ} {F : Subgroup X}
    (hFn : IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) n) {u u' : X} (hu : u ∈ F) (hu' : u' ∈ F)
    (hu2 : orderOf u = 2) (hu'2 : orderOf u' = 2) (hc : CentModOdd F u)
    (hc' : CentModOdd F u') : u⁻¹ * u' ∈ oddCoreOf F := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
  have hmem : ∀ z : ↥F, z ∈ pPrimeCore 2 ↥F ↔ (z : X) ∈ oddCoreOf F :=
    fun z => ⟨fun h => ⟨z, h, rfl⟩, fun ⟨w, hw, hwz⟩ => by rwa [← Subtype.ext hwz]⟩
  have hZ : ∀ {v : X} (hv : v ∈ F), CentModOdd F v → π ⟨v, hv⟩ ∈ center (↥F ⧸ pPrimeCore 2 ↥F) := by
    intro v hv hcv
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥F) g
    have h1 : π ⁅a, ⟨v, hv⟩⁆ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmem]
      exact hcv a a.2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hne : ∀ {v : X} (hv : v ∈ F), orderOf v = 2 → π ⟨v, hv⟩ ≠ 1 := by
    intro v hv hv2 h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmem] at h
    exact sca_not_mem_odd (odd_card_oddCoreOf F) hv2 h
  have hZu := hZ hu hc
  have hZu' := hZ hu' hc'
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(center (↥F ⧸ pPrimeCore 2 ↥F)))).1 hFn.2.1
  have e1 := hw ⟨_, hZu⟩ (fun h => hne hu hu2 (congrArg Subtype.val h))
  have e2 := hw ⟨_, hZu'⟩ (fun h => hne hu' hu'2 (congrArg Subtype.val h))
  have e3 : π ⟨u, hu⟩ = π ⟨u', hu'⟩ := congrArg Subtype.val (e1.trans e2.symm)
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hmem] at e3
  exact e3

private theorem sca_centre_mem_zStar {n : ℕ} {t y : X} (hy2 : orderOf y = 2)
    {L F : Subgroup X} (hL : Sec5Comp X n (cen t) L) (hyL : y ∈ QOf L)
    (hPF : sec6Piece L y ≤ F) {c : X} (hcP : c ∈ sec6Piece L y) (hcc : CentModOdd F c) :
    c ∈ zStar (K0 X n (cen t)) := by
  have hLpc : IsPCompIn 2 (cen t) L := Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL)
  have hcovL := (isPCompIn_restrict hLpc (sca_sq hy2) hyL).2
  have hPL : sec6Piece L y ≤ L := sca_piece_le
  have hcL : c ∈ L := hPL hcP
  have hPO : sec6Piece L y ⊓ oddCoreOf F ≤ oddCoreOf L := by
    refine (le_oddCoreOf_of_normalized inf_le_left (fun k hk => mem_normalizer_inf
      (le_normalizer hk) (le_normalizer_oddCoreOf F (hPF hk)))
      ((odd_card_oddCoreOf F).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))).trans ?_
    exact sca_oddCoreOf_le_of_cov hPL hcovL
  have hcLc : CentModOdd L c := by
    refine sca_centModOdd_of_cover hPL (sca_cov hPL hcovL) (le_normalizer_oddCoreOf L hcL)
      fun p hp => hPO ⟨?_, hcc p (hPF hp)⟩
    have e : ⁅p, c⁆ = p * (c * p⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (sec6Piece L y).mul_mem hp ((sec6Piece L y).mul_mem ((sec6Piece L y).mul_mem hcP
      ((sec6Piece L y).inv_mem hp)) ((sec6Piece L y).inv_mem hcP))
  have hcA : c ∈ K0 X n (cen t) := sca_le_K0 hL hcL
  have hOA : ∀ L', Sec5Comp X n (cen t) L' → oddCoreOf L' ≤ oddCoreOf (K0 X n (cen t)) := by
    intro L' hL'
    have h1 : oddCoreOf L' ≤ oddCoreOf (cen t) :=
      sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL'))
    have h2 : oddCoreOf (cen t) ⊓ K0 X n (cen t) ≤ oddCoreOf (K0 X n (cen t)) := by
      refine le_oddCoreOf_of_normalized inf_le_right (fun k hk => ?_)
        ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
      exact mem_normalizer_inf (le_normalizer_oddCoreOf _ (sca_K0_le _ hk)) (le_normalizer hk)
    exact (le_inf h1 ((oddCoreOf_le L').trans (sca_le_K0 hL'))).trans h2
  have hcO : c ∈ normalizer (oddCoreOf (K0 X n (cen t)) : Set X) :=
    le_normalizer_oddCoreOf _ hcA
  have hle : K0 X n (cen t) ≤ scaComm (oddCoreOf (K0 X n (cen t))) c := by
    rw [K0_eq_sSup_sec5Comp]
    refine sSup_le fun L' hL' l hl => ⟨le_normalizer_oddCoreOf _ (sca_le_K0 hL' hl), ?_⟩
    by_cases hLL : L' = L
    · subst hLL
      exact hOA L' hL' (hcLc l hl)
    · exact hOA L' hL' (Sec6Fus.commutatorElement_mem_of_ne
        (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL')) hLpc hLL hl hcL)
  exact Subgroup.mem_inf.2 ⟨hcA, Subgroup.le_normalizer hcA,
    normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer hcA), fun k hk => (hle hk).2⟩

private theorem sca_exists_centre_base
    {n : ℕ} {t : X} (hC : Sec6CtrlAt X n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) {F : Subgroup X}
    (hF : Sec5Comp X n (cen y) F) :
    ∃ c ∈ F, c ∈ cen y ∧ c ∈ Sec6Base X n t ∧ orderOf c = 2 ∧ CentModOdd F c := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  obtain ⟨L, hL, hLF⟩ := hC.piece y hyMQ hy2 F (Or.inl hF)
  have heq := sca_eq_piece_of_sec5Comp hC hyMQ hy2 hF hL hLF
  obtain ⟨c, hcP, hc2, hcc⟩ := sca_exists_centre hF hLF heq
  refine ⟨c, hLF hcP, sca_piece_le_cen hcP, ?_, hc2, hcc⟩
  rcases hL with hLA | hLM
  · exact Subgroup.mem_sup_right
      (sca_centre_mem_zStar hy2 hLA (sca_base_le_QOf hLA hyB) hLF hcP hcc)
  · exact Subgroup.mem_sup_left (sca_le_sec6M hLM (sca_piece_le hcP))

private theorem sca_four_mul_eq' {y c : X} (hy : y * y = 1) (hc : c * c = 1)
    (hyc : y * c = c * y) (hm : y * c * (y * c) = 1) (hym : y * (y * c) = y * c * y) :
    scaFour hy hc hyc = scaFour hy hm hym := by
  ext x
  simp only [Holt.StarLemma26.mem_fourSubgroup]
  have e : y * (y * c) = c := by rw [← mul_assoc, hy, one_mul]
  rw [e]
  tauto

private theorem sca_good_yc
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) (hyt : y ≠ t) {c : X}
    (hcB : c ∈ Sec6Base X n t) (hc2 : orderOf c = 2) (hcy : c ≠ y) (ha : y * y = 1)
    (hb : c * c = 1) (hab : y * c = c * y) : scaV (scaFour ha hb hab) = sec6Sig X n t := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htt : t * t = 1 := sca_mul_self ht2
  have hyt' : y * t = t * y := sca_comm (sca_base_le_cen t hyB)
  have hct : c * t = t * c := sca_comm (sca_base_le_cen t hcB)
  by_cases htc : t = c
  · subst htc
    exact sca_good_yt hS hC hA hU hext hyB hy2 hyt ha hb hab
  by_cases htyc : t = y * c
  · have hm : y * c * (y * c) = 1 := by rw [← htyc]; exact htt
    have hym : y * (y * c) = y * c * y := by rw [← htyc]; exact hyt'
    rw [sca_four_mul_eq' ha hb hab hm hym]
    have h := sca_good_yt hS hC hA hU hext hyB hy2 hyt ha htt hyt'
    have e : scaFour ha htt hyt' = scaFour ha hm hym := by
      ext x
      simp only [Holt.StarLemma26.mem_fourSubgroup]
      rw [← htyc]
    rwa [e] at h
  have htF : ∀ b ∈ scaFour ha hb hab, t * b = b * t := by
    intro b hb'
    rcases Holt.StarLemma26.mem_fourSubgroup.1 hb' with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hyt'.symm
    · exact hct.symm
    · rw [← mul_assoc, ← hyt', mul_assoc, ← hct, ← mul_assoc]
  have htnot : t ∉ scaFour ha hb hab := by
    intro h
    rcases Holt.StarLemma26.mem_fourSubgroup.1 h with h | h | h | h
    · exact sca_ne_one ht2 h
    · exact hyt h.symm
    · exact htc h
    · exact htyc h
  obtain ⟨hEe, hEcard⟩ := sca_sup_zpowers (sca_four_isElemAbelian (hab := hab)) htt htF
  have hE4 : Nat.card (scaFour ha hb hab) = 4 :=
    sca_four_card (sca_ne_one hy2) (sca_ne_one hc2) hcy.symm
  have hE8 : 8 ≤ Nat.card ↥(scaFour ha hb hab ⊔ zpowers t) := by
    rw [hEcard htnot, hE4]
  have hEB : scaFour ha hb hab ⊔ zpowers t ≤ Sec6Base X n t :=
    sup_le (sca_four_le hyB hcB) ((Subgroup.zpowers_le).2 (sca_t_mem_base hS hA))
  have hyE : y ∈ scaFour ha hb hab ⊔ zpowers t := Subgroup.mem_sup_left sca_left_mem_four
  have htE : t ∈ scaFour ha hb hab ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  exact sca_propagate hS hC hEB hEe hE8 (sca_four_le hyE htE (hab := hyt'))
    (sca_four_card (sca_ne_one hy2) (sca_ne_one ht2) hyt)
    (sca_good_yt hS hC hA hU hext hyB hy2 hyt ha htt hyt') le_sup_left hE4

private theorem sca_good_of_centre
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) (hyt : y ≠ t) {F : Subgroup X}
    (hF : Sec5Comp X n (cen y) F) {c' : X} (hc'F : c' ∈ F) (hc'y : c' ∈ cen y)
    (hc'2 : orderOf c' = 2) (hc'c : CentModOdd F c') (hc'ne : c' ≠ y) (ha : y * y = 1)
    (hb : c' * c' = 1) (hab : y * c' = c' * y) : scaV (scaFour ha hb hab) = sec6Sig X n t := by
  obtain ⟨c, hcF, hcy, hcB, hc2, hcc⟩ := sca_exists_centre_base hC hyB hy2 hF
  have hun : c⁻¹ * c' ∈ oddCoreOf F := sca_centre_unique hF.2 hcF hc'F hc2 hc'2 hcc hc'c
  have hcc' : c = c' * (c⁻¹ * c')⁻¹ := by group
  have hcne : c ≠ y := by
    intro h
    apply hc'ne
    have h1 : y * c' ∈ oddCoreOf F := by
      have e : y * c' = c⁻¹ * c' := by
        rw [h, inv_eq_of_mul_eq_one_right ha]
      rw [e]
      exact hun
    exact (sca_eq_of_mul_mem_odd (odd_card_oddCoreOf F) ha hb hab h1).symm
  have hyc : y * c = c * y := (sca_comm hcy).symm
  have hgood := sca_good_yc hS hC hA hU hext hyB hy2 hyt hcB hc2 hcne ha (sca_mul_self hc2) hyc
  have hFy : F ≤ cen y := (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hF)).1
  have hyO : y ∈ normalizer (oddCoreOf F : Set X) :=
    sca_mem_normalizer_of_comm fun o ho => (sca_comm (hFy (oddCoreOf_le F ho))).symm
  set A := scaFour ha (sca_mul_self hc2) hyc with hAdef
  have hAO : A ≤ normalizer (oddCoreOf F : Set X) :=
    sca_four_le hyO (le_normalizer_oddCoreOf F hcF)
  have hA4 : Nat.card A = 4 := sca_four_card (sca_ne_one hy2) (sca_ne_one hc2) hcne.symm
  have hc'AO : c' ∈ A ⊔ oddCoreOf F := by
    have e : c' = c * (c⁻¹ * c') := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left sca_right_mem_four) (Subgroup.mem_sup_right hun)
  have hB'le : scaFour ha hb hab ≤ A ⊔ oddCoreOf F :=
    sca_four_le (Subgroup.mem_sup_left sca_left_mem_four) hc'AO
  have hB'4 : Nat.card (scaFour ha hb hab) = 4 :=
    sca_four_card (sca_ne_one hy2) (sca_ne_one hc'2) hc'ne.symm
  obtain ⟨o, ho, B'', hB''A, -, hB''4, hB'eq⟩ :=
    sca_exists_four_conj hAO (odd_card_oddCoreOf F) sca_four_isElemAbelian hB'4 hB'le
  have hB''eq : B'' = A := Subgroup.eq_of_le_of_card_ge hB''A (by rw [hA4, hB''4])
  have hoV : o ∈ normalizer (sec6Sig X n t : Set X) :=
    Subgroup.le_normalizer (sca_odd_le_V hS hC hA hU hext hyB hy2
      (sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hF)) ho))
  rw [hB'eq, hB''eq]
  exact sca_V_conj hgood hoV

private theorem sca_cen_le_of_centre
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) (hyt : y ≠ t) {F : Subgroup X}
    (hF : Sec5Comp X n (cen y) F) {c : X} (hcF : c ∈ F) (hcy : c ∈ cen y)
    (hc2 : orderOf c = 2) (hcc : CentModOdd F c) (hcne : c ≠ y) :
    cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  have ha : y * y = 1 := sca_mul_self hy2
  have hb : c * c = 1 := sca_mul_self hc2
  have hab : y * c = c * y := (sca_comm hcy).symm
  have hgood := sca_good_of_centre hS hC hA hU hext hyB hy2 hyt hF hcF hcy hc2 hcc hcne ha hb hab
  intro g hg
  have hgy : g * y * g⁻¹ = y := by rw [sca_comm hg, mul_inv_cancel_right]
  set c' := g * c * g⁻¹ with hc'
  have hFg : Sec5Comp X n (cen y) (F.map (MulAut.conj g).toMonoidHom) := by
    obtain ⟨⟨u, hu⟩, hcov⟩ := hF
    have h1 := hu.map_mulEquiv (MulAut.conj g)
    rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h1
    refine ⟨⟨_, h1⟩, ?_⟩
    let ψ : ↥F ≃* ↥(F.map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective F _ (MulAut.conj g).injective
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
    exact isDoubleCoverOfAlt_congr' f hcov
  have hc'F : c' ∈ F.map (MulAut.conj g).toMonoidHom := ⟨c, hcF, rfl⟩
  have hc'y : c' ∈ cen y := sca_conj_mem (Subgroup.le_normalizer hg) hcy
  have hc'2 : orderOf c' = 2 := by
    rw [hc', Sec6Fus.orderOf_conj]
    exact hc2
  have hc'c : CentModOdd (F.map (MulAut.conj g).toMonoidHom) c' := by
    intro a ha'
    obtain ⟨a₀, ha₀, rfl⟩ := ha'
    have h1 := hcc a₀ ha₀
    have e : ⁅(MulAut.conj g).toMonoidHom a₀, c'⁆ = (MulAut.conj g).toMonoidHom ⁅a₀, c⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc', commutatorElement_def]
      group
    rw [e, ← oddCoreOf_map_mulEquiv']
    exact Subgroup.mem_map_of_mem _ h1
  have hc'ne : c' ≠ y := by
    intro h
    apply hcne
    have e : c = g⁻¹ * c' * g := by rw [hc']; group
    rw [e, h]
    calc g⁻¹ * y * g = g⁻¹ * (y * g) := by group
      _ = g⁻¹ * (g * y) := by rw [sca_comm hg]
      _ = y := by group
  have hgood' := sca_good_of_centre hS hC hA hU hext hyB hy2 hyt hFg hc'F hc'y hc'2 hc'c hc'ne ha
    (sca_mul_self hc'2) (sca_comm hc'y).symm
  refine sca_mem_normalizer_of_V hgood ?_
  have hyc' : g * (y * c) * g⁻¹ = y * c' := by
    rw [hc']
    calc g * (y * c) * g⁻¹ = (g * y * g⁻¹) * (g * c * g⁻¹) := by group
      _ = y * (g * c * g⁻¹) := by rw [hgy]
  have e : (scaFour ha hb hab).map (MulAut.conj g).toMonoidHom =
      scaFour ha (sca_mul_self hc'2) (sca_comm hc'y).symm := by
    ext x
    simp only [Subgroup.mem_map, Holt.StarLemma26.mem_fourSubgroup, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl | rfl
      · left
        group
      · right; left; exact hgy
      · right; right; left; rfl
      · right; right; right; exact hyc'
    · rintro (h | h | h | h) <;> rw [h]
      · exact ⟨1, Or.inl rfl, by group⟩
      · exact ⟨y, Or.inr (Or.inl rfl), hgy⟩
      · exact ⟨c, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨y * c, Or.inr (Or.inr (Or.inr rfl)), hyc'⟩
  rw [e]
  exact hgood'

private theorem sca_cen_le_of_apiece
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t) {y : X}
    (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) (hyQ : y ∉ Sec6Q X n (cen t))
    {F L : Subgroup X} (hF : Sec5Comp X n (cen y) F) (hL : Sec5Comp X n (cen t) L)
    (hLF : sec6Piece L y ≤ F) : cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  have heq := sca_eq_piece_of_sec5Comp hC hyMQ hy2 hF (Or.inl hL) hLF
  obtain ⟨c, hcP, hc2, hcc⟩ := sca_exists_centre hF hLF heq
  have hcZ := sca_centre_mem_zStar hy2 hL (sca_base_le_QOf hL hyB) hLF hcP hcc
  have hcQ : c ∈ Sec6Q X n (cen t) := sca_zStar_le_Q hcZ
  have htQ : t ∈ Sec6Q X n (cen t) := sca_zStar_le_Q (sca_t_mem_zStar hS hA)
  have hyt : y ≠ t := fun h => hyQ (h ▸ htQ)
  exact sca_cen_le_of_centre hS hC hA hU hext hyB hy2 hyt hF (hLF hcP) (sca_piece_le_cen hcP)
    hc2 hcc (fun h => hyQ (h ▸ hcQ))

private theorem sca_mem_normalizer_oTwoPrimeOf {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : g ∈ normalizer (oTwoPrimeOf H : Set X) :=
  oTwoPrimeOf_normalizes ((Subgroup.zpowers_le).2 hg) (Subgroup.mem_zpowers g)

private theorem sca_witness_mem_Q {n : ℕ} {t x v : X} {A : Subgroup X}
    (hA : Sec5Comp X n (cen t) A) (hx2 : orderOf x = 2) (hxA : x ∈ QOf A)
    (hv : IsIntrinsicIn X (cen t ⊓ cen x) (sec6Piece A x) v) : v ∈ Sec6Q X n (cen t) := by
  have hApc : IsPCompIn 2 (cen t) A := Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hA)
  have hPA : sec6Piece A x ≤ A := sca_piece_le
  obtain ⟨-, hcovA⟩ := isPCompIn_restrict hApc (sca_sq hx2) hxA
  obtain ⟨-, hvP, -, hPeq, -⟩ := hv
  have hvA : v ∈ A := hPA hvP
  have hvt : v ∈ cen t := hApc.1 hvA
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hPeq
  have hvP' : CentModOdd (sec6Piece A x) v := by
    refine sca_centModOdd_of_cover ((oTwoPrimeOf_le _).trans inf_le_left) hPeq
      (le_normalizer_oddCoreOf _ hvP) fun e he => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (sca_comm (((oTwoPrimeOf_le _).trans inf_le_right) he))]
    exact one_mem _
  have hvA' : CentModOdd A v :=
    sca_centModOdd_of_cover hPA (sca_cov hPA hcovA) (le_normalizer_oddCoreOf _ hvA)
      fun p hp => sca_oddCoreOf_le_of_cov hPA hcovA (hvP' p hp)
  have hKt : CentModOdd (Sec6K X n (cen t)) v := by
    intro k hk
    have hle : Sec6K X n (cen t) ≤ scaComm (oddCoreOf (Sec6K X n (cen t))) v := by
      refine sSup_le fun L hL l hl => ⟨le_normalizer_oddCoreOf _ (sca_le_sec6K hL hl), ?_⟩
      by_cases hLA : L = A
      · rw [hLA] at hl
        exact sca_oddCoreOf_le_oddCoreOf_sec6K (Or.inl hA) (hvA' l hl)
      · exact sca_oddCoreOf_le_oddCoreOf_sec6K hL
          (Sec6Fus.commutatorElement_mem_of_ne (Sec6Fus.isPCompIn_of_sec6KComp hL) hApc hLA hl
            hvA)
    exact (hle hk).2
  exact Subgroup.mem_inf.2 ⟨hvt, mem_QOf_iff.2 ⟨Sec6K_cen_normal n t hvt, hKt⟩⟩

private theorem sca_centModOdd_of_Qv {n : ℕ} {t x v : X} (hK : Sec6Lemma51 X n)
    (h61 : Sec6L61 X n t) {F : Subgroup X} (hF : Sec6KComp X n (cen x) F)
    (htF : t ∈ normalizer (F : Set X)) (hvQ : v ∈ Sec6Q X n (cen t)) (hv2 : orderOf v = 2)
    (hvF : v ∈ QOf F) : CentModOdd F t := by
  set R : Subgroup X := oTwoPrimeOf (F ⊓ cen v) with hRdef
  have hRF : R ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  obtain ⟨-, hRcov⟩ :=
    isPCompIn_restrict (Sec6Fus.isPCompIn_of_sec6KComp hF) (sca_sq hv2) hvF
  have hRK : Sec6KComp X n (cen x ⊓ cen v) R := sec6KComp_restrict hF (sca_sq hv2) hvF
  have hRKv : R ≤ Sec6K X n (cen v) :=
    (sca_le_sec6K hRK).trans (hK.sub v hv2 _ inf_le_right).1
  have hcv := h61.a v hvQ hv2
  have hvt : v ∈ cen t := (Subgroup.mem_inf.1 hvQ).1
  have htv : t ∈ cen v := sca_mem_cen_symm hvt
  have htKv : t ∈ normalizer (Sec6K X n (cen v) : Set X) := Sec6K_cen_normal n v htv
  have htOKv : t ∈ normalizer (oddCoreOf (Sec6K X n (cen v)) : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htKv
  have hKvt : ∀ k ∈ Sec6K X n (cen v), ⁅k, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := by
    intro k hk
    have hk' : k ∈ oddCoreOf (Sec6K X n (cen v)) ⊔
        (Sec6K X n (cen v) ⊓ Sec6K X n (cen t)) := by
      unfold Sec6Covers at hcv
      rw [← hcv]
      exact hk
    have hle : oddCoreOf (Sec6K X n (cen v)) ⊔ (Sec6K X n (cen v) ⊓ Sec6K X n (cen t)) ≤
        scaComm (oddCoreOf (Sec6K X n (cen v))) t := by
      refine sup_le (fun o ho => ⟨le_normalizer ho, sca_comm_mem_of_mem ho htOKv⟩)
        (fun k hk => ⟨le_normalizer_oddCoreOf _ hk.1, ?_⟩)
      rw [commutatorElement_eq_one_iff_mul_comm.2 (sca_comm (Sec6Fus.sec6K_le n _ hk.2))]
      exact one_mem _
    exact (hle hk').2
  have htR : t ∈ normalizer (R : Set X) :=
    sca_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf htF (le_normalizer htv))
  have hRO : ∀ r ∈ R, ⁅r, t⁆ ∈ oddCoreOf F := by
    intro r hr
    have h1 : ⁅r, t⁆ ∈ R := by
      have : ⁅r, t⁆ = r * (t * r⁻¹ * t⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact R.mul_mem hr (sca_conj_mem htR (R.inv_mem hr))
    have h2 : ⁅r, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := hKvt r (hRKv hr)
    exact sca_oddCoreOf_le_of_cov hRF hRcov (inf_pPrimeCoreOf_le_pPrimeCoreOf hRKv ⟨h1, h2⟩)
  exact sca_centModOdd_of_cover hRF (sca_cov hRF hRcov)
    (mem_normalizer_oddCoreOf_of_mem_normalizer htF) hRO

private theorem sca_apiece_le
    {n : ℕ} {t : X} (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t)
    {y : X} (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) {J : Subgroup X}
    (hJ : Sec6KComp X n (cen y) J) (hnt : ¬ CentModOdd J t) {A : Subgroup X}
    (hA : Sec5Comp X n (cen t) A) : sec6Piece A y ≤ J := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  have hyA : y ∈ QOf A := sca_base_le_QOf hA hyB
  obtain ⟨⟨v, hv⟩, -⟩ := sec5Comp_restrict hA (sca_sq hy2) hyA
  have hvQ := sca_witness_mem_Q hA hy2 hyA hv
  obtain ⟨G, hG, hPG⟩ := hC.land y hyMQ hy2 A (Or.inl hA)
  by_contra hPJ
  have hGJ : J ≠ G := fun h => hPJ (h ▸ hPG)
  obtain ⟨L, hL, hLJ⟩ := hC.piece y hyMQ hy2 J hJ
  obtain ⟨htJ, -⟩ := hC.dich y hyMQ hy2 L J hL hJ hLJ
  have hvJ : v ∈ QOf J :=
    Sec6Fus.le_QOf_of_ne (Sec6Fus.isPCompIn_of_sec6KComp hJ) (Sec6Fus.isPCompIn_of_sec6KComp hG)
      hGJ (hPG hv.2.1)
  exact hnt (sca_centModOdd_of_Qv hK h61 hJ htJ hvQ hv.1 hvJ)

private theorem sca_two_pieces_false {F P P' : Subgroup X} (hFq : IsTwoGenQuasi ↥F)
    (hPF : P ≤ F) (hP'F : P' ≤ F) (heq : F = oddCoreOf F ⊔ P) (heq' : F = oddCoreOf F ⊔ P')
    (hcomm : ∀ p ∈ P, ∀ p' ∈ P', ⁅p, p'⁆ ∈ oddCoreOf F) : False := by
  apply not_commutator_le_of_odd hFq (odd_card_oddCoreOf F)
  rw [Subgroup.commutator_le]
  have h1 : ∀ p ∈ P, ∀ b ∈ F, ⁅b, p⁆ ∈ oddCoreOf F := by
    intro p hp b hb
    have hpO : p ∈ normalizer (oddCoreOf F : Set X) := le_normalizer_oddCoreOf F (hPF hp)
    have hle : oddCoreOf F ⊔ P' ≤ scaComm (oddCoreOf F) p := by
      refine sup_le (fun o ho => ⟨le_normalizer ho, sca_comm_mem_of_mem ho hpO⟩)
        (fun p' hp' => ⟨le_normalizer_oddCoreOf F (hP'F hp'), ?_⟩)
      have e : ⁅p', p⁆ = ⁅p, p'⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact inv_mem (hcomm p hp p' hp')
    have hb' : b ∈ oddCoreOf F ⊔ P' := by
      rw [← heq']
      exact hb
    exact (hle hb').2
  intro a ha b hb
  have hbO : b ∈ normalizer (oddCoreOf F : Set X) := le_normalizer_oddCoreOf F hb
  have hle : oddCoreOf F ⊔ P ≤ scaComm (oddCoreOf F) b := by
    refine sup_le (fun o ho => ⟨le_normalizer ho, sca_comm_mem_of_mem ho hbO⟩)
      (fun p hp => ⟨le_normalizer_oddCoreOf F (hPF hp), ?_⟩)
    have e : ⁅p, b⁆ = ⁅b, p⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem (h1 p hp b hb)
  have ha' : a ∈ oddCoreOf F ⊔ P := by
    rw [← heq]
    exact ha
  exact (hle ha').2

private theorem sca_pieces_comm
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) {y : X} (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2)
    {L L' : Subgroup X} (hL : Sec6KComp X n (cen t) L) (hL' : Sec6KComp X n (cen t) L')
    (hne : L ≠ L') {p p' : X} (hp : p ∈ sec6Piece L y) (hp' : p' ∈ sec6Piece L' y) :
    ⁅p, p'⁆ ∈ oddCoreOf (cen y) := by
  have hLpc := Sec6Fus.isPCompIn_of_sec6KComp hL
  have h1 : ⁅p, p'⁆ ∈ oddCoreOf (cen t) := sca_oddCoreOf_le hLpc
    (Sec6Fus.commutatorElement_mem_of_ne hLpc (Sec6Fus.isPCompIn_of_sec6KComp hL') hne
      (sca_piece_le hp) (sca_piece_le hp'))
  have h2 : ⁅p, p'⁆ ∈ cen y := by
    have hpy : p ∈ cen y := sca_piece_le_cen hp
    have hp'y : p' ∈ cen y := sca_piece_le_cen hp'
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hpy hp'y) (inv_mem hpy)) (inv_mem hp'y)
  exact sec6_base_balance hS hC (sca_t_mem_base hS hA) hyB hS.choice.inv hy2
    (sca_comm (sca_base_le_cen t hyB)).symm ⟨h1, h2⟩

private theorem sca_inf_oddCoreOf_cen_le {n : ℕ} {y : X} {F : Subgroup X}
    (hF : Sec6KComp X n (cen y) F) : F ⊓ oddCoreOf (cen y) ≤ oddCoreOf F :=
  sca_inf_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp hF).1

private theorem sca_count_false
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA : K0 X n (cen t) ≠ ⊥) {y : X} (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2)
    (hnoA : ∀ F, ¬ Sec5Comp X n (cen y) F) {J : Subgroup X} (hJ : Sec6KComp X n (cen y) J)
    (hnt : ¬ CentModOdd J t)
    (hall : ∀ L, Sec6MComp X n (cen t) L → ∀ F, Sec6KComp X n (cen y) F → sec6Piece L y ≤ F →
      CentModOdd F t) : False := by
  classical
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  set St : Set (Subgroup X) := {L | Sec6MComp X n (cen t) L} with hSt
  set Sy : Set (Subgroup X) := {F | Sec6MComp X n (cen y) F} with hSy
  let φ : Subgroup X → Subgroup X := fun L =>
    Classical.epsilon fun F => Sec6KComp X n (cen y) F ∧ sec6Piece L y ≤ F
  have hφ : ∀ L ∈ St, Sec6KComp X n (cen y) (φ L) ∧ sec6Piece L y ≤ φ L := fun L hL =>
    Classical.epsilon_spec (hC.land y hyMQ hy2 L (Or.inr hL))
  have hφt : ∀ L ∈ St, CentModOdd (φ L) t := fun L hL => hall L hL _ (hφ L hL).1 (hφ L hL).2
  have hJM : J ∈ Sy := hJ.resolve_left (hnoA J)
  have hmaps : ∀ L ∈ St, φ L ∈ Sy \ {J} := by
    intro L hL
    refine ⟨((hφ L hL).1).resolve_left (hnoA _), ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    exact hnt (h ▸ hφt L hL)
  have hinj : Set.InjOn φ St := by
    intro L hL L' hL' hLL'
    by_contra hne
    obtain ⟨hF, hPF⟩ := hφ L hL
    have hP'F : sec6Piece L' y ≤ φ L := hLL' ▸ (hφ L' hL').2
    have heq := (sca_eq_piece_of_centModOdd hC hyMQ hy2 hF (fun _ => hφt L hL))
    obtain ⟨L₁, hL₁, hL₁F, heq₁⟩ := heq
    have heqL : φ L = oddCoreOf (φ L) ⊔ sec6Piece L y := by
      obtain ⟨htF, hd⟩ := hC.dich y hyMQ hy2 L (φ L) (Or.inr hL) hF hPF
      rcases hd with h | ⟨-, hnt', -⟩
      · exact h
      · exact absurd (hφt L hL) hnt'
    have heqL' : φ L = oddCoreOf (φ L) ⊔ sec6Piece L' y := by
      obtain ⟨htF, hd⟩ := hC.dich y hyMQ hy2 L' (φ L) (Or.inr hL') hF hP'F
      rcases hd with h | ⟨-, hnt', -⟩
      · exact h
      · exact absurd (hφt L hL) hnt'
    refine sca_two_pieces_false (sca_isTwoGenQuasi (Sec6Fus.isPCompIn_of_sec6KComp hF)) hPF
      hP'F heqL heqL' fun p hp p' hp' => sca_inf_oddCoreOf_cen_le hF ⟨?_, ?_⟩
    · have hpF := hPF hp
      have hp'F := hP'F hp'
      rw [commutatorElement_def]
      exact (φ L).mul_mem ((φ L).mul_mem ((φ L).mul_mem hpF hp'F) ((φ L).inv_mem hpF))
        ((φ L).inv_mem hp'F)
    · exact sca_pieces_comm hS hC hA hyB hy2 (Or.inr hL) (Or.inr hL') hne hp hp'
  have h1 : St.ncard ≤ (Sy \ {J}).ncard := Set.ncard_le_ncard_of_injOn φ hmaps hinj
  have h2 : (Sy \ {J}).ncard + 1 = Sy.ncard := Set.ncard_sdiff_singleton_add_one hJM
  have h3 : Sy.ncard ≤ St.ncard :=
    (modOddCard_Sec6M_le_iff hS.deg (cen y) (cen t)).1 (hS.choice.maxM y hy2)
  omega

private theorem sca_mem_pPrimeCore_iff {F : Subgroup X} (y : ↥F) :
    y ∈ pPrimeCore 2 ↥F ↔ (y : X) ∈ oddCoreOf F :=
  ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, hzy⟩ => by rwa [← Subtype.ext hzy]⟩

private theorem sca_pi_eq_one_iff {F : Subgroup X} (y : ↥F) :
    QuotientGroup.mk' (pPrimeCore 2 ↥F) y = 1 ↔ (y : X) ∈ oddCoreOf F := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, sca_mem_pPrimeCore_iff]

private theorem sca_centModOdd_iff {F : Subgroup X} {c : X} (hcF : c ∈ normalizer (F : Set X)) :
    CentModOdd F c ↔ ∀ a (ha : a ∈ F),
      QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨c * a * c⁻¹, sca_conj_mem hcF ha⟩ : ↥F) =
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨a, ha⟩ : ↥F) := by
  constructor
  · intro h a ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, sca_mem_pPrimeCore_iff]
    show (c * a * c⁻¹)⁻¹ * a ∈ oddCoreOf F
    have h1 := h a⁻¹ (F.inv_mem ha)
    have e : (c * a * c⁻¹)⁻¹ * a = ⁅a⁻¹, c⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  · intro h a ha
    have h1 := h a ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      sca_mem_pPrimeCore_iff] at h1
    change (c * a * c⁻¹)⁻¹ * a ∈ oddCoreOf F at h1
    have e : ⁅a, c⁆ = a * ((c * a * c⁻¹)⁻¹ * a) * a⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact sca_conj_mem (le_normalizer_oddCoreOf F ha) h1

private theorem sca_pump_act {F : Subgroup X} {t f : X} (htF : t ∈ normalizer (F : Set X))
    (hfF : f ∈ F) (hft : CentModOdd F (f * t)) {a : X} (ha : a ∈ F) :
    QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨t * a * t⁻¹, sca_conj_mem htF ha⟩ : ↥F) =
      (QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F))⁻¹ *
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨a, ha⟩ : ↥F) *
          QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) := by
  have hftN : f * t ∈ normalizer (F : Set X) := mul_mem (le_normalizer hfF) htF
  have h := (sca_centModOdd_iff hftN).1 hft a ha
  have he : (⟨f * t * a * (f * t)⁻¹, sca_conj_mem hftN ha⟩ : ↥F) =
      (⟨f, hfF⟩ : ↥F) * ⟨t * a * t⁻¹, sca_conj_mem htF ha⟩ * (⟨f, hfF⟩ : ↥F)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he, map_mul, map_mul, map_inv] at h
  rw [← h]
  group

private theorem sca_pump_orderOf {F : Subgroup X} {t f : X} (ht2 : t * t = 1)
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t))
    (hnt : ¬ CentModOdd F t) (hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) with hgdef
  refine orderOf_eq_prime ?_ ?_
  · rw [sq]
    have hc : g * g ∈ center (↥F ⧸ pPrimeCore 2 ↥F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥F) y
      have hb : ((b : X)) ∈ F := b.2
      have h1 := sca_pump_act htF hfF hft hb
      have h2 := sca_pump_act htF hfF hft (sca_conj_mem htF hb)
      have he : (⟨t * (t * (b : X) * t⁻¹) * t⁻¹, sca_conj_mem htF (sca_conj_mem htF hb)⟩ : ↥F) =
          b := by
        apply Subtype.ext
        show t * (t * (b : X) * t⁻¹) * t⁻¹ = (b : X)
        rw [show t * (t * (b : X) * t⁻¹) * t⁻¹ = (t * t) * (b : X) * (t * t)⁻¹ by group, ht2]
        group
      rw [he, h1] at h2
      have hb' : (⟨(b : X), hb⟩ : ↥F) = b := Subtype.coe_eta b hb
      rw [hb', ← hgdef] at h2
      have h3 : g * g * QuotientGroup.mk' (pPrimeCore 2 ↥F) b =
          QuotientGroup.mk' (pPrimeCore 2 ↥F) b * (g * g) := by
        conv_lhs => rw [h2]
        group
      exact h3.symm
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  · intro hg1
    apply hnt
    rw [sca_centModOdd_iff htF]
    intro a ha
    rw [sca_pump_act htF hfF hft ha, ← hgdef, hg1]
    group

private theorem sca_cent_doubleCover
    {n : ℕ} {Q : Type} [Group Q]
    (hT : IsSec6MType n Q) {q : Q} (hq : orderOf q = 2) :
    IsDoubleCoverOfAlt ↥(centralizer ({q} : Set Q)) n := by
  rcases hT with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · exact Sec6L51B.isDoubleCoverOfAlt_centralizer_McL e q hq
  · exact Sec6L51B.isDoubleCoverOfAlt_centralizer_Ly e q hq

private theorem sca_card_eq {A B : Type} [Group A] [Group B] {n : ℕ}
    (hA : IsDoubleCoverOfAlt A n) (hB : IsDoubleCoverOfAlt B n) : Nat.card A = Nat.card B := by
  obtain ⟨-, hA2, ⟨eA⟩⟩ := hA
  obtain ⟨-, hB2, ⟨eB⟩⟩ := hB
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center B), hA2, hB2,
    Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]

private theorem sca_pump_comm {F : Subgroup X} {t f : X} (htF : t ∈ normalizer (F : Set X))
    (hfF : f ∈ F) (hft : CentModOdd F (f * t)) {p : X} (hpF : p ∈ F) (hpt : p ∈ cen t) :
    QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hpF⟩ : ↥F) *
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) =
      QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) *
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hpF⟩ : ↥F) := by
  have h := sca_pump_act htF hfF hft hpF
  have he : (⟨t * p * t⁻¹, sca_conj_mem htF hpF⟩ : ↥F) = ⟨p, hpF⟩ := by
    apply Subtype.ext
    show t * p * t⁻¹ = p
    rw [← sca_comm hpt]
    group
  rw [he] at h
  calc _ = QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) *
        ((QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F))⁻¹ *
          QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hpF⟩ : ↥F) *
            QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)) := by group
    _ = _ := by rw [← h]

private theorem sca_ker_le {F P : Subgroup X} (hPF : P ≤ F) :
    ((QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF)).ker ≤
      pPrimeCore 2 ↥P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF)
  have hodd : Nat.Coprime 2 (Nat.card φ.ker) := by
    let g : φ.ker →* pPrimeCore 2 ↥F :=
      { toFun := fun a => ⟨Subgroup.inclusion hPF (a : ↥P), by
          have h := a.2
          rw [MonoidHom.mem_ker] at h
          exact (QuotientGroup.eq_one_iff _).1 h⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun y : pPrimeCore 2 ↥F => ((y : ↥F) : X)) hab
      exact this
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
      pPrimeCore_coprime_card
  exact le_sSup ⟨inferInstance, hodd⟩

private theorem sca_pump_img
    {n : ℕ} {F P : Subgroup X}
    {t f : X} (hT : IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F)) (ht2 : t * t = 1)
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t))
    (hnt : ¬ CentModOdd F t) (hPF : P ≤ F) (hPt : P ≤ cen t)
    (hPn : IsDoubleCoverOfAlt (↥P ⧸ pPrimeCore 2 ↥P) n) :
    ∀ c ∈ centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)} :
        Set (↥F ⧸ pPrimeCore 2 ↥F)),
      ∃ p, ∃ hp : p ∈ P, QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hPF hp⟩ : ↥F) = c := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) with hgdef
  have hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥ :=
    mcLLyCenterFree _ (hT.imp (fun h => h.2) (fun h => h.2))
  have hg2 : orderOf g = 2 := sca_pump_orderOf ht2 htF hfF hft hnt hZ
  have hC : IsDoubleCoverOfAlt ↥(centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F))) n :=
    sca_cent_doubleCover hT hg2
  set ψ := (QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF) with hψ
  have hle : ψ.range ≤ centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F)) := by
    rintro _ ⟨p, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sca_pump_comm htF hfF hft (hPF p.2) (hPt p.2)
  have hker := sca_ker_le hPF
  have h1 : Nat.card ↥P = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have h2 : Nat.card ↥P = Nat.card (↥P ⧸ pPrimeCore 2 ↥P) * Nat.card (pPrimeCore 2 ↥P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ψ.ker ≤ Nat.card (pPrimeCore 2 ↥P) := Subgroup.card_le_of_le hker
  have h4 : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) =
      Nat.card ↥(centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F))) := sca_card_eq hPn hC
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h5 : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) ≤ Nat.card ψ.range := by
    by_contra hlt
    rw [not_le] at hlt
    have e1 : Nat.card ψ.range * Nat.card ψ.ker <
        Nat.card (↥P ⧸ pPrimeCore 2 ↥P) * Nat.card (pPrimeCore 2 ↥P) :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hkpos) (Nat.mul_le_mul_left _ h3)
    rw [← h1, ← h2] at e1
    exact lt_irrefl _ e1
  have hrange : ψ.range = centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F)) :=
    Subgroup.eq_of_le_of_card_ge hle (h4 ▸ h5)
  intro c hc
  rw [← hrange] at hc
  obtain ⟨p, rfl⟩ := hc
  exact ⟨(p : X), p.2, rfl⟩

private theorem sca_isSolvable_of_oTwoPrimeOf {H : Subgroup X}
    (h : Group.IsSolvable ↥(oTwoPrimeOf H)) : Group.IsSolvable ↥H := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥H with hR
  haveI : R.Characteristic :=
    ComponentClassification.CatalogueBPrimeJoin.primeResidual_characteristic 2 ↥H
  haveI : R.Normal := inferInstance
  have hRe : oTwoPrimeOf H = R.map H.subtype := oTwoPrimeOf_eq_map_primeResidual H
  have e : ↥R ≃* ↥(oTwoPrimeOf H) :=
    (Subgroup.equivMapOfInjective R H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hRe.symm)
  haveI : Group.IsSolvable ↥R := Group.isSolvable_of_isSolvable_injective
    (f := (e : ↥R →* ↥(oTwoPrimeOf H))) e.injective
  have hidx := ComponentClassification.CatalogueBPrimeJoin.primeResidual_coprime_index 2 ↥H
  haveI : Group.IsSolvable (↥H ⧸ R) := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rw [← Subgroup.index]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun hd => by
      have := Nat.Coprime.coprime_dvd_right hd hidx
      norm_num at this)
  exact Group.isSolvable_of_subgroup_quotient R

private theorem sca_isSolvable_of_commutator_odd {P : Subgroup X}
    (h : Odd (Nat.card ↥⁅P, P⁆)) : Group.IsSolvable ↥P := by
  set C := commutator ↥P with hC
  haveI : C.Normal := inferInstance
  have hmap : C.map P.subtype = ⁅P, P⁆ := by
    rw [hC, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hCodd : Odd (Nat.card ↥C) := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hmap]
    exact h
  haveI : Group.IsSolvable ↥C := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hCodd
  haveI : Group.IsSolvable (↥P ⧸ C) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hc : ⁅b⁻¹, a⁻¹⁆ ∈ C := by
      rw [hC, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    convert hc using 1
    simp only [commutatorElement_def]
    group
  exact Group.isSolvable_of_subgroup_quotient C

private theorem sca_base_le_QOf_sup
    {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec6MComp X n (cen t) L) :
    Sec6Base X n t ≤ QOf L ⊔ L := by
  have hLpc := Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hL)
  refine sup_le (sSup_le fun M hM => ?_) ((sca_zStar_le_QOf (Or.inr hL)).trans le_sup_left)
  by_cases hML : M = L
  · rw [hML]
    exact le_sup_right
  · exact (Sec6Fus.le_QOf_of_ne hLpc (Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hM))
      (Ne.symm hML)).trans le_sup_left

private theorem sca_false_of_pumped
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t)
    (hC : Sec6CtrlAt X n t) (hA : K0 X n (cen t) ≠ ⊥) {y : X} (hyB : y ∈ Sec6Base X n t)
    (hy2 : orderOf y = 2) (hnoA : ∀ F, ¬ Sec5Comp X n (cen y) F) {J : Subgroup X}
    (hJ : Sec6KComp X n (cen y) J) (hnt : ¬ CentModOdd J t) : False := by
  have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := sca_base_le_MQ hyB
  have ht2 : orderOf t = 2 := hS.choice.inv
  by_cases hall : ∀ L, Sec6MComp X n (cen t) L → ∀ F, Sec6KComp X n (cen y) F →
      sec6Piece L y ≤ F → CentModOdd F t
  · exact sca_count_false hS hC hA hyB hy2 hnoA hJ hnt hall
  push Not at hall
  obtain ⟨L, hL, J', hJ', hLJ', hnt'⟩ := hall
  obtain ⟨A, hA'⟩ : ∃ A, Sec5Comp X n (cen t) A := by
    by_contra hno
    push Not at hno
    apply hA
    rw [K0_eq_sSup_sec5Comp, sSup_eq_bot]
    exact fun A hA'' => absurd hA'' (hno A)
  have hAJ' := sca_apiece_le hK h61 hC hyB hy2 hJ' hnt' hA'
  obtain ⟨htJ', hd⟩ := hC.dich y hyMQ hy2 L J' (Or.inr hL) hJ' hLJ'
  rcases hd with heq | ⟨hJ'M, -, f, hfJ', hft⟩
  · refine hnt' (sca_centModOdd_of_cover hLJ' heq (mem_normalizer_oddCoreOf_of_mem_normalizer htJ')
      fun p hp => ?_)
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (sca_comm ((Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hL)).1 (sca_piece_le hp)))]
    exact one_mem _
  have hApc := Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hA')
  have hPAt : sec6Piece A y ≤ cen t := sca_piece_le.trans hApc.1
  have hPAn : IsDoubleCoverOfAlt (↥(sec6Piece A y) ⧸ pPrimeCore 2 ↥(sec6Piece A y)) n :=
    (sec5Comp_restrict hA' (sca_sq hy2) (sca_base_le_QOf hA' hyB)).2
  have himg := sca_pump_img hJ'M.2 (sca_mul_self ht2) htJ' hfJ' hft hnt' hAJ' hPAt hPAn
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥J') with hπ
  have hneAL : A ≠ L := Sec6Fus.ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hA' hL
  have hcommAL : ∀ p (hp : p ∈ sec6Piece A y) p' (hp' : p' ∈ sec6Piece L y),
      π ⟨p, hAJ' hp⟩ * π ⟨p', hLJ' hp'⟩ = π ⟨p', hLJ' hp'⟩ * π ⟨p, hAJ' hp⟩ := by
    intro p hp p' hp'
    have h1 : ⁅p, p'⁆ ∈ oddCoreOf J' := by
      refine sca_inf_oddCoreOf_cen_le hJ' ⟨?_, sca_pieces_comm hS hC hA hyB hy2 (Or.inl hA')
        (Or.inr hL) hneAL hp hp'⟩
      have hpJ := hAJ' hp
      have hp'J := hLJ' hp'
      rw [commutatorElement_def]
      exact J'.mul_mem (J'.mul_mem (J'.mul_mem hpJ hp'J) (J'.inv_mem hpJ)) (J'.inv_mem hp'J)
    have h2 : π ⁅(⟨p, hAJ' hp⟩ : ↥J'), ⟨p', hLJ' hp'⟩⁆ = 1 := (sca_pi_eq_one_iff _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hfimg : π ⟨f, hfJ'⟩ ∈ centralizer ({π ⟨f, hfJ'⟩} : Set (↥J' ⧸ pPrimeCore 2 ↥J')) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨p₀, hp₀, hp₀f⟩ := himg _ hfimg
  have hLimg : ∀ p' (hp' : p' ∈ sec6Piece L y),
      ∃ p, ∃ hp : p ∈ sec6Piece A y, π ⟨p, hAJ' hp⟩ = π ⟨p', hLJ' hp'⟩ := by
    intro p' hp'
    refine himg _ (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    rw [← hp₀f]
    exact (hcommAL p₀ hp₀ p' hp').symm
  have hLL : ⁅sec6Piece L y, sec6Piece L y⁆ ≤ oddCoreOf J' := by
    rw [Subgroup.commutator_le]
    intro p' hp' p'' hp''
    obtain ⟨p, hp, hpe⟩ := hLimg p'' hp''
    have h1 : π ⁅(⟨p', hLJ' hp'⟩ : ↥J'), ⟨p'', hLJ' hp''⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, ← hpe]
      exact (hcommAL p hp p' hp').symm
    exact (sca_pi_eq_one_iff _).1 h1
  have hodd : Odd (Nat.card ↥⁅sec6Piece L y, sec6Piece L y⁆) :=
    (odd_card_oddCoreOf J').of_dvd_nat (Subgroup.card_dvd_of_le hLL)
  have hsolv := sca_isSolvable_of_oTwoPrimeOf (sca_isSolvable_of_commutator_odd hodd)
  exact Sec6Fus.not_isSolvable_inf_cen_of_isMLIntrIn mcLLyCenterFree hL.1 (sca_sq hy2)
    (sca_base_le_QOf_sup hL hyB) hsolv

private theorem sca_cen_le_of_base
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t)
    (hC : Sec6CtrlAt X n t) (hA : K0 X n (cen t) ≠ ⊥) (hU : ScaUnp n t) (hext : ScaExt n t)
    {y : X} (hyB : y ∈ Sec6Base X n t) (hy2 : orderOf y = 2) :
    cen y ≤ normalizer (sec6Sig X n t : Set X) := by
  by_cases hyt : y = t
  · rw [hyt]
    exact cen_le_normalizer_sec6Sig n t
  by_cases hyQ : y ∈ Sec6Q X n (cen t)
  · exact sca_cen_le_of_Q hS h61 hC hA hU hext hyB hyQ hy2
  by_cases hap : ∃ F L, Sec5Comp X n (cen y) F ∧ Sec5Comp X n (cen t) L ∧ sec6Piece L y ≤ F
  · obtain ⟨F, L, hF, hL, hLF⟩ := hap
    exact sca_cen_le_of_apiece hS hC hA hU hext hyB hy2 hyQ hF hL hLF
  push Not at hap
  by_cases hAy : ∃ F, Sec5Comp X n (cen y) F
  · obtain ⟨F₀, hF₀⟩ := hAy
    exact sca_cen_le_of_A_mpieces hS hC hA hU hext hyB hy2 (fun F hF L hL => hap F L hF hL) hF₀
  push Not at hAy
  by_cases hunp : ∀ F, Sec6MComp X n (cen y) F → CentModOdd F t
  · exact sca_cen_le_of_unpumped hS hC hA hU hext hyB hy2 hAy hunp
  push Not at hunp
  obtain ⟨J, hJ, hnt⟩ := hunp
  exact (sca_false_of_pumped hS hK h61 hC hA hyB hy2 hAy (Or.inr hJ) hnt).elim

private theorem sca_mem_zStar_of_centModOdd {n : ℕ} {t : X} {L : Subgroup X}
    (hL : Sec5Comp X n (cen t) L) {c : X} (hcL : c ∈ L) (hcLc : CentModOdd L c) :
    c ∈ zStar (K0 X n (cen t)) := by
  have hLpc : IsPCompIn 2 (cen t) L := Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL)
  have hcA : c ∈ K0 X n (cen t) := sca_le_K0 hL hcL
  have hOA : ∀ L', Sec5Comp X n (cen t) L' → oddCoreOf L' ≤ oddCoreOf (K0 X n (cen t)) := by
    intro L' hL'
    have h1 : oddCoreOf L' ≤ oddCoreOf (cen t) :=
      sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL'))
    have h2 : oddCoreOf (cen t) ⊓ K0 X n (cen t) ≤ oddCoreOf (K0 X n (cen t)) := by
      refine le_oddCoreOf_of_normalized inf_le_right (fun k hk => ?_)
        ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
      exact mem_normalizer_inf (le_normalizer_oddCoreOf _ (sca_K0_le _ hk)) (le_normalizer hk)
    exact (le_inf h1 ((oddCoreOf_le L').trans (sca_le_K0 hL'))).trans h2
  have hle : K0 X n (cen t) ≤ scaComm (oddCoreOf (K0 X n (cen t))) c := by
    rw [K0_eq_sSup_sec5Comp]
    refine sSup_le fun L' hL' l hl => ⟨le_normalizer_oddCoreOf _ (sca_le_K0 hL' hl), ?_⟩
    by_cases hLL : L' = L
    · subst hLL
      exact hOA L' hL' (hcLc l hl)
    · exact hOA L' hL' (Sec6Fus.commutatorElement_mem_of_ne
        (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hL')) hLpc hLL hl hcL)
  exact Subgroup.mem_inf.2 ⟨hcA, Subgroup.le_normalizer hcA,
    normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer hcA), fun k hk => (hle hk).2⟩

private theorem sca_exists_witness {n : ℕ} {t : X} {L : Subgroup X}
    (hL : Sec5Comp X n (cen t) L) : ∃ c ∈ L, c ∈ zStar (K0 X n (cen t)) ∧ orderOf c = 2 := by
  obtain ⟨⟨u, hu⟩, -⟩ := id hL
  obtain ⟨hu2, huL, -, hLeq, -⟩ := hu
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq
  have hR : oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) ≤ L :=
    (oTwoPrimeOf_le _).trans inf_le_left
  have hcu : CentModOdd L u := by
    refine sca_centModOdd_of_cover hR hLeq (le_normalizer_oddCoreOf L huL) fun r hr => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (sca_comm (((oTwoPrimeOf_le _).trans inf_le_right) hr))]
    exact one_mem _
  exact ⟨u, huL, sca_mem_zStar_of_centModOdd hL huL hcu, hu2⟩

private theorem sca_self_eq (L : Subgroup X) : L = oddCoreOf L ⊔ L :=
  le_antisymm le_sup_right (sup_le (oddCoreOf_le L) le_rfl)

private theorem sca_N_unpumped
    {n : ℕ} {t : X} {N : Subgroup X} (hII : Sec6CtrlNAt X n t N) {F : Subgroup X}
    (hF : Sec6KComp X n N F) (hFt : CentModOdd F t) :
    ∃ L, L ≤ F ∧ F = oddCoreOf F ⊔ L ∧
      (Sec5Comp X n N F → Sec5Comp X n (cen t) L) ∧
      (Sec6MComp X n N F → Sec6MComp X n (cen t) L) := by
  obtain ⟨L, hL, hLF⟩ := hII.piece F hF
  have heq : F = oddCoreOf F ⊔ L := by
    rcases hII.dich L F hL hF hLF with h | ⟨-, -, hnt, -⟩
    · exact h
    · exact absurd hFt hnt
  refine ⟨L, hLF, heq, fun hFA => ?_, fun hFM => ?_⟩
  · rcases hL with hLA | hLM
    · exact hLA
    · exact (sca_false_of_types le_rfl (sca_self_eq L) hLF heq hLM.2 hFA.2).elim
  · rcases hL with hLA | hLM
    · exact (sca_false_of_types hLF heq le_rfl (sca_self_eq L) hFM.2 hLA.2).elim
    · exact hLM

private theorem sca_A_N_centModOdd
    {n : ℕ} {t : X} {N : Subgroup X} (hII : Sec6CtrlNAt X n t N) {F : Subgroup X}
    (hF : Sec5Comp X n N F) : CentModOdd F t := by
  obtain ⟨L, hL, hLF⟩ := hII.piece F (Or.inl hF)
  rcases hII.dich L F hL (Or.inl hF) hLF with heq | ⟨hFM, -⟩
  · refine sca_centModOdd_of_cover hLF heq
      (mem_normalizer_oddCoreOf_of_mem_normalizer (hII.norm F (Or.inl hF))) fun l hl => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (sca_comm ((Sec6Fus.isPCompIn_of_sec6KComp hL).1 hl))]
    exact one_mem _
  · exact absurd rfl (Sec6Fus.ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hF hFM)

private theorem sca_oddN_inf_le {t : X} {N : Subgroup X} (hCt : cen t ≤ N) :
    oddCoreOf N ⊓ cen t ≤ oddCoreOf (cen t) :=
  le_oddCoreOf_of_normalized inf_le_right
    (fun c hc => mem_normalizer_inf (le_normalizer_oddCoreOf N (hCt hc)) (le_normalizer hc))
    ((odd_card_oddCoreOf N).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

private theorem sca_oddCt_inf_le {n : ℕ} (t : X) :
    oddCoreOf (cen t) ⊓ K0 X n (cen t) ≤ oddCoreOf (K0 X n (cen t)) :=
  le_oddCoreOf_of_normalized inf_le_right
    (fun k hk => mem_normalizer_inf (le_normalizer_oddCoreOf _ (sca_K0_le _ hk)) (le_normalizer hk))
    ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

private theorem sca_oddA_le {n : ℕ} (N : Subgroup X) :
    oddCoreOf (K0 X n N) ≤ oddCoreOf N :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans (sca_K0_le N))
    (fun c hc => mem_normalizer_oddCoreOf_of_mem_normalizer
      (mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hc))))
    (odd_card_oddCoreOf _)

private theorem sca_zStar_AN
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCt : cen t ≤ N) (hII : Sec6CtrlNAt X n t N) :
    zStar (K0 X n N) ≤ Sec6Base X n t ⊔ oddCoreOf N ∧
      ∀ F, Sec6MComp X n N F → zStar (K0 X n N) ≤ QOf F := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htN : t ∈ N := hCt (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hAQ : ∀ F, Sec6MComp X n N F → K0 X n N ≤ QOf F := by
    intro F hF
    rw [K0_eq_sSup_sec5Comp]
    refine sSup_le fun A hA => ?_
    exact Sec6Fus.le_QOf_of_ne (Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hF))
      (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hA))
      (Sec6Fus.ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hA hF).symm
  refine ⟨fun z hz => ?_, fun F hF => (Sec6Fus.zStar_le _).trans (hAQ F hF)⟩
  have hzA : z ∈ K0 X n N := hz.1
  have hzN : z ∈ N := sca_K0_le N hzA
  have hAN : K0 X n N ≤ K0 X n (cen t) ⊔ oddCoreOf N := by
    rw [K0_eq_sSup_sec5Comp]
    refine sSup_le fun A hA => ?_
    obtain ⟨L, hLA, heq, hLt, -⟩ := sca_N_unpumped hII (Or.inl hA) (sca_A_N_centModOdd hII hA)
    rw [heq]
    exact sup_le ((sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp (Or.inl hA))).trans
      le_sup_right) ((sca_le_K0 (hLt hA)).trans le_sup_left)
  have hAtN : K0 X n (cen t) ≤ normalizer (oddCoreOf N : Set X) :=
    fun c hc => le_normalizer_oddCoreOf N (hCt (sca_K0_le _ hc))
  obtain ⟨a, ha, o, ho, rfl⟩ := Sec6Fus.exists_mul_of_mem_sup hAtN (hAN hzA)
  have hKz : Sec6K X n N ≤ scaComm (oddCoreOf N) (a * o) := by
    refine sSup_le fun F hF f hf => ⟨le_normalizer_oddCoreOf N
      ((Sec6Fus.isPCompIn_of_sec6KComp hF).1 hf), ?_⟩
    rcases hF with hFA | hFM
    · exact sca_oddA_le N (hz.2.2.2 f (sca_le_K0 hFA hf))
    · exact sca_oddCoreOf_le (Sec6Fus.isPCompIn_of_sec6KComp (Or.inr hFM))
        ((mem_QOf_iff.1 (hAQ F hFM hzA)).2 f hf)
  have hKt : Sec6K X n (cen t) ≤ Sec6K X n N := by
    have h := (hK.b N hN t htN ht2).1
    rwa [inf_of_le_right hCt] at h
  have haZ : a ∈ zStar (K0 X n (cen t)) := by
    refine Subgroup.mem_inf.2 ⟨ha, Subgroup.le_normalizer ha,
      normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer ha), fun k hk => ?_⟩
    have hkK : k ∈ Sec6K X n N := hKt ((sec6K_eq X n (cen t)).symm ▸ Subgroup.mem_sup_left hk)
    have h1 : ⁅k, a * o⁆ ∈ oddCoreOf N := (hKz hkK).2
    have hkN : k ∈ normalizer (oddCoreOf N : Set X) := hAtN hk
    have h2 : ⁅k, o⁻¹⁆ ∈ oddCoreOf N := by
      have e : ⁅k, o⁻¹⁆ = (k * o⁻¹ * k⁻¹) * o := by
        simp only [commutatorElement_def, inv_inv]
      rw [e]
      exact (oddCoreOf N).mul_mem (sca_conj_mem hkN ((oddCoreOf N).inv_mem ho)) ho
    have h3 : ⁅k, a⁆ ∈ oddCoreOf N := by
      have e : ⁅k, a⁆ = ⁅k, a * o⁆ * ((a * o) * ⁅k, o⁻¹⁆ * (a * o)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (oddCoreOf N).mul_mem h1 (sca_conj_mem (le_normalizer_oddCoreOf N hzN) h2)
    have h4 : ⁅k, a⁆ ∈ K0 X n (cen t) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hk ha) (inv_mem hk)) (inv_mem ha)
    exact sca_oddCt_inf_le t ⟨sca_oddN_inf_le hCt ⟨h3, sca_K0_le _ h4⟩, h4⟩
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right haZ)) (Subgroup.mem_sup_right ho)

private theorem sca_isConj
    {n : ℕ} {Q : Type} [Group Q] (hT : IsSec6MType n Q) (a b : Q) (ha : orderOf a = 2)
    (hb : orderOf b = 2) : IsConj a b := by
  rcases hT with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact Sec6L51B.isConj_of_equiv_McL e a b ha hb
  · exact Sec6L51B.isConj_of_equiv_Ly e a b ha hb

private theorem sca_sq_mem_of_mul {F : Subgroup X} (hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥)
    {q f : X} (hq : q ∈ QOf F) (hf : f ∈ F) (hx : q * f * (q * f) = 1) :
    f * f ∈ oddCoreOf F := by
  set O := oddCoreOf F with hOdef
  have hOF : O ≤ F := oddCoreOf_le F
  have hFnO : F ≤ normalizer (O : Set X) := le_normalizer_oddCoreOf F
  have hqc : ∀ a ∈ F, ⁅a, q⁆ ∈ O := (mem_QOf_iff.1 hq).2
  have ho1 : ⁅f, q⁆ ∈ O := hqc f hf
  have hq2 : q * q = f⁻¹ * ⁅f, q⁆ * f⁻¹ := by
    have h1 : f * q * f * q = 1 := by
      calc f * q * f * q = q⁻¹ * (q * f * (q * f)) * q := by group
        _ = 1 := by rw [hx]; group
    have hfqf : f * q * f = q⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [commutatorElement_def]
    calc q * q = q * f⁻¹ * (f * q * f) * f⁻¹ := by group
      _ = q * f⁻¹ * q⁻¹ * f⁻¹ := by rw [hfqf]
      _ = f⁻¹ * (f * q * f⁻¹ * q⁻¹) * f⁻¹ := by group
  have hq2F : q * q ∈ F := by
    rw [hq2]
    exact F.mul_mem (F.mul_mem (F.inv_mem hf) (hOF ho1)) (F.inv_mem hf)
  have hq2O : q * q ∈ O :=
    Sec6Fus.zStar_le_oddCoreOf_of_center hZ ⟨hq2F, (QOf F).mul_mem hq hq⟩
  have h1 : f⁻¹ * ⁅f, q⁆ * f⁻¹ ∈ O := hq2 ▸ hq2O
  have h2 : f⁻¹ * ⁅f, q⁆ * f ∈ O := by
    have := sca_conj_mem (hFnO (F.inv_mem hf)) ho1
    rwa [inv_inv] at this
  have h3 : (f * f)⁻¹ = (f⁻¹ * ⁅f, q⁆ * f)⁻¹ * (f⁻¹ * ⁅f, q⁆ * f⁻¹) := by group
  have h4 : (f * f)⁻¹ ∈ O := h3 ▸ O.mul_mem (O.inv_mem h2) h1
  have h5 := O.inv_mem h4
  rwa [inv_inv] at h5

private theorem sca_reduce_aux
    {n : ℕ} {t : X} {N : Subgroup X} (Ps : Finset (Subgroup X))
    (hPs : ∀ F ∈ Ps, IsPCompIn 2 N F ∧ IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F) ∧
      ∃ c ∈ F, c ∈ Sec6Base X n t ∧ orderOf c = 2)
    (hdist : ∀ F ∈ Ps, ∀ F' ∈ Ps, F ≠ F' → F' ≤ QOf F) :
    ∀ x : X, x * x = 1 →
      x ∈ ((Sec6Base X n t ⊔ oddCoreOf N) ⊓ ⨅ F ∈ Ps, QOf F) ⊔ ⨆ F ∈ Ps, F →
        ∃ g ∈ N, g * x * g⁻¹ ∈ Sec6Base X n t ⊔ oddCoreOf N := by
  classical
  induction Ps using Finset.induction_on with
  | empty =>
    intro x _ hx
    refine ⟨1, one_mem _, ?_⟩
    simp only [Finset.notMem_empty, iInf_of_empty, iInf_top, inf_top_eq, iSup_of_empty,
      iSup_bot, sup_bot_eq] at hx
    simpa using hx
  | insert F Ps'' hFPs ih =>
    intro x hx2 hx
    have hPs'' : ∀ F' ∈ Ps'', IsPCompIn 2 N F' ∧ IsSec6MType n (↥F' ⧸ pPrimeCore 2 ↥F') ∧
        ∃ c ∈ F', c ∈ Sec6Base X n t ∧ orderOf c = 2 :=
      fun F' hF' => hPs F' (Finset.mem_insert_of_mem hF')
    have hdist'' : ∀ F₁ ∈ Ps'', ∀ F₂ ∈ Ps'', F₁ ≠ F₂ → F₂ ≤ QOf F₁ := fun F₁ h₁ F₂ h₂ =>
      hdist F₁ (Finset.mem_insert_of_mem h₁) F₂ (Finset.mem_insert_of_mem h₂)
    obtain ⟨hFpc, hFT, c, hcF, hcB, hc2⟩ := hPs F (Finset.mem_insert_self F Ps'')
    set W'' := (Sec6Base X n t ⊔ oddCoreOf N) ⊓ ⨅ F' ∈ Ps'', QOf F' with hW''
    set P'' := ⨆ F' ∈ Ps'', F' with hP''
    have hneF : ∀ F' ∈ Ps'', F' ≠ F := fun F' hF' h => hFPs (h ▸ hF')
    have hFW : ∀ F' ∈ Ps'', F ≤ QOf F' := fun F' hF' =>
      hdist F' (Finset.mem_insert_of_mem hF') F (Finset.mem_insert_self F Ps'') (hneF F' hF')
    have hOW : oddCoreOf F ≤ W'' := by
      refine le_inf ((sca_oddCoreOf_le hFpc).trans le_sup_right) ?_
      exact le_iInf₂ fun F' hF' => (oddCoreOf_le F).trans (hFW F' hF')
    have hcW : c ∈ W'' := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hcB, ?_⟩
      exact Subgroup.mem_iInf.2 fun F' => Subgroup.mem_iInf.2 fun hF' => hFW F' hF' hcF
    set H := ((Sec6Base X n t ⊔ oddCoreOf N) ⊓ ⨅ F' ∈ insert F Ps'', QOf F') ⊔ P'' with hH
    have hHQ : H ≤ QOf F := by
      refine sup_le (inf_le_right.trans ?_) (iSup₂_le fun F' hF' => ?_)
      · exact iInf₂_le F (Finset.mem_insert_self F Ps'')
      · exact hdist F (Finset.mem_insert_self F Ps'') F' (Finset.mem_insert_of_mem hF')
          (hneF F' hF').symm
    have hHW : H ≤ W'' ⊔ P'' := by
      refine sup_le (le_sup_of_le_left (le_inf inf_le_left ?_)) le_sup_right
      exact inf_le_right.trans (le_iInf₂ fun F' hF' => iInf₂_le F' (Finset.mem_insert_of_mem hF'))
    have hxHF : x ∈ H ⊔ F := by
      have e : ((Sec6Base X n t ⊔ oddCoreOf N) ⊓ ⨅ F' ∈ insert F Ps'', QOf F') ⊔
          ⨆ F' ∈ insert F Ps'', F' = H ⊔ F := by
        rw [Finset.iSup_insert, hH]
        rw [sup_comm F P'', ← sup_assoc]
      rw [← e]
      exact hx
    have hHN : H ≤ normalizer (F : Set X) := hHQ.trans fun q hq => (mem_QOf_iff.1 hq).1
    obtain ⟨q, hqH, f, hfF, rfl⟩ := Sec6Fus.exists_mul_of_mem_sup hHN hxHF
    have hqQ : q ∈ QOf F := hHQ hqH
    have hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥ :=
      mcLLyCenterFree _ (hFT.imp (fun h => h.2) (fun h => h.2))
    have hf2 : f * f ∈ oddCoreOf F := sca_sq_mem_of_mul hZ hqQ hfF hx2
    by_cases hfO : f ∈ oddCoreOf F
    · exact ih hPs'' hdist'' (q * f) hx2 (mul_mem (hHW hqH) (Subgroup.mem_sup_left (hOW hfO)))
    set π := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
    have hmem : ∀ z : ↥F, π z = 1 ↔ (z : X) ∈ oddCoreOf F := fun z => sca_pi_eq_one_iff z
    have hfo : orderOf (π ⟨f, hfF⟩) = 2 := by
      have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [sq, ← map_mul, hmem]
        exact hf2
      · rw [Ne, hmem]
        exact hfO
    have hco : orderOf (π ⟨c, hcF⟩) = 2 := by
      have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [sq, ← map_mul, hmem]
        have : c * c = 1 := sca_mul_self hc2
        show c * c ∈ oddCoreOf F
        rw [this]
        exact one_mem _
      · rw [Ne, hmem]
        exact sca_not_mem_odd (odd_card_oddCoreOf F) hc2
    obtain ⟨hbar, hhbar⟩ := isConj_iff.1 (sca_isConj hFT _ _ hfo hco)
    obtain ⟨h₀, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥F) hbar
    set h : X := (h₀ : X) with hhdef
    have hhF : h ∈ F := h₀.2
    have h1 : ⁅h, q⁆ ∈ oddCoreOf F := (mem_QOf_iff.1 hqQ).2 h hhF
    have h2 : c⁻¹ * (h * f * h⁻¹) ∈ oddCoreOf F := by
      have e : π ⟨h * f * h⁻¹, F.mul_mem (F.mul_mem hhF hfF) (F.inv_mem hhF)⟩ = π ⟨c, hcF⟩ := by
        have e0 : (⟨h * f * h⁻¹, F.mul_mem (F.mul_mem hhF hfF) (F.inv_mem hhF)⟩ : ↥F) =
            h₀ * ⟨f, hfF⟩ * h₀⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhdef]
        rw [e0, map_mul, map_mul, map_inv]
        exact hhbar
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        sca_mem_pPrimeCore_iff] at e
      have e2 : ((⟨h * f * h⁻¹, F.mul_mem (F.mul_mem hhF hfF) (F.inv_mem hhF)⟩ : ↥F)⁻¹ *
          ⟨c, hcF⟩ : ↥F) = ((c⁻¹ * (h * f * h⁻¹))⁻¹ : X) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      have e3 := (oddCoreOf F).inv_mem e
      rw [e2, inv_inv] at e3
      exact e3
    have hx' : h * (q * f) * h⁻¹ = ⁅h, q⁆ * q * c * (c⁻¹ * (h * f * h⁻¹)) := by
      simp only [commutatorElement_def]
      group
    have hx'mem : h * (q * f) * h⁻¹ ∈ W'' ⊔ P'' := by
      rw [hx']
      exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left (hOW h1)) (hHW hqH))
        (Subgroup.mem_sup_left hcW)) (Subgroup.mem_sup_left (hOW h2))
    have hx'2 : h * (q * f) * h⁻¹ * (h * (q * f) * h⁻¹) = 1 := by
      calc h * (q * f) * h⁻¹ * (h * (q * f) * h⁻¹) = h * ((q * f) * (q * f)) * h⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    obtain ⟨g', hg'N, hg'⟩ := ih hPs'' hdist'' _ hx'2 hx'mem
    refine ⟨g' * h, mul_mem hg'N (hFpc.1 hhF), ?_⟩
    have e : g' * h * (q * f) * (g' * h)⁻¹ = g' * (h * (q * f) * h⁻¹) * g'⁻¹ := by group
    rw [e]
    exact hg'

theorem sec6R_exists_conj_base
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCt : cen t ≤ N) (hII : Sec6CtrlNAt X n t N) {x : X}
    (hx : x ∈ Sec6R X n N) (hx2 : orderOf x = 2) :
    ∃ g ∈ N, ∃ y ∈ Sec6Base X n t, orderOf y = 2 ∧ x = g * y * g⁻¹ := by
  classical
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  set Pset : Set (Subgroup X) := {F | Sec6KComp X n N F ∧ ¬ CentModOdd F t} with hPset
  set Ps : Finset (Subgroup X) := (Set.toFinite Pset).toFinset with hPs
  have hmemPs : ∀ F, F ∈ Ps ↔ Sec6KComp X n N F ∧ ¬ CentModOdd F t := fun F => by
    rw [hPs, Set.Finite.mem_toFinset]
    rfl
  have hpump : ∀ F, Sec6KComp X n N F → ¬ CentModOdd F t →
      Sec6MComp X n N F ∧ ∃ L, Sec5Comp X n (cen t) L ∧ L ≤ F := by
    intro F hF hnt
    obtain ⟨L, hL, hLF⟩ := hII.piece F hF
    rcases hII.dich L F hL hF hLF with heq | ⟨hFM, hLA, -, -⟩
    · refine absurd (sca_centModOdd_of_cover hLF heq
        (mem_normalizer_oddCoreOf_of_mem_normalizer (hII.norm F hF)) fun l hl => ?_) hnt
      rw [commutatorElement_eq_one_iff_mul_comm.2
        (sca_comm ((Sec6Fus.isPCompIn_of_sec6KComp hL).1 hl))]
      exact one_mem _
    · exact ⟨hFM, L, hLA, hLF⟩
  have hPs1 : ∀ F ∈ Ps, IsPCompIn 2 N F ∧ IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F) ∧
      ∃ c ∈ F, c ∈ Sec6Base X n t ∧ orderOf c = 2 := by
    intro F hF
    obtain ⟨hFK, hnt⟩ := (hmemPs F).1 hF
    obtain ⟨hFM, L, hL, hLF⟩ := hpump F hFK hnt
    obtain ⟨c, hcL, hcZ, hc2⟩ := sca_exists_witness hL
    exact ⟨hFM.1.1, hFM.2, c, hLF hcL, Subgroup.mem_sup_right hcZ, hc2⟩
  have hdist : ∀ F ∈ Ps, ∀ F' ∈ Ps, F ≠ F' → F' ≤ QOf F := fun F hF F' hF' hne =>
    Sec6Fus.le_QOf_of_ne (hPs1 F hF).1 (hPs1 F' hF').1 hne
  obtain ⟨hZB, hZQ⟩ := sca_zStar_AN hS hK hN hCt hII
  have hRle : Sec6R X n N ≤ ((Sec6Base X n t ⊔ oddCoreOf N) ⊓ ⨅ F ∈ Ps, QOf F) ⊔
      ⨆ F ∈ Ps, F := by
    refine sup_le (le_sup_of_le_left (le_inf hZB (le_iInf₂ fun F hF => ?_)))
      (sSup_le fun F hF => ?_)
    · exact hZQ F (hpump F ((hmemPs F).1 hF).1 ((hmemPs F).1 hF).2).1
    · have hF' : Sec6MComp X n N F := hF
      by_cases hFt : CentModOdd F t
      · refine le_sup_of_le_left (le_inf ?_ (le_iInf₂ fun F' hF'' => ?_))
        · obtain ⟨L, hLF, heq, -, hLM⟩ := sca_N_unpumped hII (Or.inr hF') hFt
          rw [heq]
          exact sup_le ((sca_oddCoreOf_le hF'.1.1).trans le_sup_right)
            ((sca_le_sec6M (hLM hF')).trans (le_sup_of_le_left le_sup_left))
        · refine Sec6Fus.le_QOf_of_ne (hPs1 F' hF'').1 hF'.1.1 fun h => ?_
          exact ((hmemPs F').1 hF'').2 (h ▸ hFt)
      · exact le_sup_of_le_right (le_iSup₂_of_le F ((hmemPs F).2 ⟨Or.inr hF', hFt⟩) le_rfl)
  obtain ⟨g, hgN, hg⟩ := sca_reduce_aux Ps hPs1 hdist x (sca_mul_self hx2) (hRle hx)
  have hBO : Sec6Base X n t ≤ normalizer (oddCoreOf N : Set X) :=
    fun b hb => le_normalizer_oddCoreOf N (hCt (sca_base_le_cen t hb))
  have hgx2 : (g * x * g⁻¹) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [sca_mul_self hx2]; group
  obtain ⟨o, ho, y, hyB, hy2, hgxy⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hBO (odd_card_oddCoreOf N) hg hgx2
  rw [pow_one] at hy2
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply sca_ne_one hx2
    have h1 : g * x * g⁻¹ = 1 := by rw [hgxy]; group
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  refine ⟨g⁻¹ * o, mul_mem (inv_mem hgN) (oddCoreOf_le N ho), y, hyB,
    sca_orderOf_two (by rw [← sq]; exact hy2) hy1, ?_⟩
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = g⁻¹ * (o * y * o⁻¹) * g := by rw [hgxy]
    _ = g⁻¹ * o * y * (g⁻¹ * o)⁻¹ := by group

end SigCenA

theorem sec6SigCen_of_A_ne_bot
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t)
    (hC : Sec6CtrlAt X n t) (hA : K0 X n (cen t) ≠ ⊥)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
      Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x)
    (hII : Sec6CtrlNAt X n t (normalizer (sec6Sig X n t : Set X)))
    (hext : ∀ E : Subgroup X, E ≤ Sec6Base X n t → CFSG.Open.IsElemAbelian 2 E → 8 ≤ Nat.card E →
      (∃ B : Subgroup X, B ≤ E ⊓ Sec6M X n (cen t) ∧ CFSG.Open.IsElemAbelian 2 B ∧
        Nat.card B = 4) →
      ∀ B : Subgroup X, B ≤ E → CFSG.Open.IsElemAbelian 2 B → Nat.card B = 4 →
        (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t)
    (hne : sec6Sig X n t ≠ ⊥) :
    ∀ x ∈ Sec6R X n (normalizer (sec6Sig X n t : Set X)), orderOf x = 2 →
      cen x ≤ normalizer (sec6Sig X n t : Set X) := by
  intro x hx hx2
  have hN := sca_N_ne_top hS hC hA hU hext hne
  obtain ⟨g, hgN, y, hyB, hy2, rfl⟩ :=
    sec6R_exists_conj_base hS hK hN (cen_le_normalizer_sec6Sig n t) hII hx hx2
  have hCy := sca_cen_le_of_base hS hK h61 hC hA hU hext hyB hy2
  have hcx : cen (g * y * g⁻¹) = (cen y).map (MulAut.conj g).toMonoidHom := by
    rw [cen_map, MulAut.conj_apply]
  rw [hcx]
  exact (Subgroup.map_mono hCy).trans
    (map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgN)).le

end CFSG.OddStandard.Solomon75
