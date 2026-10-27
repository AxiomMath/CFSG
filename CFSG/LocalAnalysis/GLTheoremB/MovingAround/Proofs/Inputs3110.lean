module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL34b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs2
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts5

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs3110

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34b

section Conn

variable {G : Type} [Group G] [Finite G]

theorem card_inf_ge {R Q A : Subgroup G} (hQ : Q.relIndex R ≤ 3) (hA : IsEkIn 3 4 R A) :
    27 ≤ Nat.card (A ⊓ Q : Subgroup G) := by
  obtain ⟨hAR, -, hAc⟩ := hA
  have h1 := Subgroup.relIndex_mul_card (H := Q) (K := A)
  have h0 : Q.relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : Q.relIndex A ≤ 3 := (Subgroup.relIndex_le_of_le_right hAR h0).trans hQ
  rw [hAc, inf_comm] at h1
  have hpos : 0 < Nat.card (A ⊓ Q : Subgroup G) := Nat.card_pos
  have h81 : (3 : ℕ) ^ 4 = 81 := by norm_num
  rw [h81] at h1
  nlinarith

theorem kc_of_cent {X R Q D : Subgroup G} (hRX : R ≤ X) (hDX : D ≤ X) (hD : IsElemAbelian 3 D)
    (hD27 : 27 ≤ Nat.card D) (hDQ : D ≤ Subgroup.centralizer (Q : Set G)) (hQ : Q.relIndex R ≤ 3)
    {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  have key : ∀ A, IsEkIn 3 4 R A → IsKConnectedIn 3 3 X A D := by
    intro A hA
    have h27 := card_inf_ge hQ hA
    obtain ⟨hAR, hAel, hAc⟩ := hA
    have hAc' : 27 ≤ Nat.card A := by rw [hAc]; norm_num
    refine kc_trans (kc_of_le_elem (hAR.trans hRX) hAel le_rfl inf_le_left hAc' h27) ?_
    exact kc_of_comm ((inf_le_left.trans hAR).trans hRX) (isElemAbelian_mono hAel inf_le_left) h27 hDX hD
      hD27 (inf_le_right.trans (cent_symm hDQ))
  exact kc_trans (key A hA) (kc_symm (key B hB))

theorem exists_e27_cent {P Q E : Subgroup G} (hP : IsPGroup 3 P) (hQP : Q ≤ P) (hEP : E ≤ P)
    (hE : IsElemAbelian 3 E) (W M : Fin 3 → Subgroup G) (hWE : ∀ i, W i ≤ E)
    (hWQ : ∀ i, Q ≤ Subgroup.normalizer (W i : Set G)) (hW1 : ∀ i, W i ≠ ⊥)
    (hWM : ∀ i, W i ⊓ M i = ⊥) (hMW : ∀ i j, i ≠ j → W j ≤ M i) :
    ∃ D : Subgroup G, D ≤ E ∧ IsElemAbelian 3 D ∧ Nat.card D = 27 ∧
      D ≤ Subgroup.centralizer (Q : Set G) := by
  have hz : ∀ i, ∃ z ∈ W i, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ q ∈ Q, q * z = z * q := by
    intro i
    obtain ⟨z, hzW, hz1, hz3, hzc⟩ := InputsL34b.exists_central_of_normalized (T := Q ⊔ W i) (N := W i)
      (hP.to_le (sup_le hQP ((hWE i).trans hEP))) le_sup_right
      (sup_le (hWQ i) Subgroup.le_normalizer) (hW1 i)
    exact ⟨z, hzW, hz1, hz3, fun q hq => hzc q (le_sup_left (a := Q) hq)⟩
  choose z hzW hz1 hz3 hzc using hz
  have hzM : ∀ i, z i ∉ M i := fun i h => hz1 i (by
    have : z i ∈ W i ⊓ M i := ⟨hzW i, h⟩
    rwa [hWM i, Subgroup.mem_bot] at this)
  have hzE : ∀ i, z i ∈ E := fun i => hWE i (hzW i)
  have hzMj : ∀ i j, i ≠ j → Subgroup.zpowers (z j) ≤ M i := fun i j hij =>
    Subgroup.zpowers_le.2 (hMW i j hij (hzW j))
  set D₁ : Subgroup G := Subgroup.zpowers (z 0) with hD₁
  set D₂ : Subgroup G := D₁ ⊔ Subgroup.zpowers (z 1) with hD₂
  set D : Subgroup G := D₂ ⊔ Subgroup.zpowers (z 2) with hD
  have hD₁E : D₁ ≤ E := Subgroup.zpowers_le.2 (hzE 0)
  have hD₂E : D₂ ≤ E := sup_le hD₁E (Subgroup.zpowers_le.2 (hzE 1))
  have hDE : D ≤ E := sup_le hD₂E (Subgroup.zpowers_le.2 (hzE 2))
  have hD₁c : Nat.card D₁ = 3 := by
    rw [hD₁, Nat.card_zpowers]
    exact orderOf_eq_prime (hz3 0) (hz1 0)
  have hD₂c : Nat.card D₂ = 9 := by
    rw [hD₂, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three D₁ (hz3 1)
      (fun h => hzM 1 (hzMj 1 0 (by decide) h)) (fun e he => hE.comm (hD₁E he) (hzE 1)), hD₁c]
  have hD₂M : D₂ ≤ M 2 := sup_le (hzMj 2 0 (by decide)) (hzMj 2 1 (by decide))
  have hDc : Nat.card D = 27 := by
    rw [hD, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three D₂ (hz3 2)
      (fun h => hzM 2 (hD₂M h)) (fun e he => hE.comm (hD₂E he) (hzE 2)), hD₂c]
  refine ⟨D, hDE, isElemAbelian_mono hE hDE, hDc, ?_⟩
  have hzC : ∀ i, Subgroup.zpowers (z i) ≤ Subgroup.centralizer (Q : Set G) := fun i =>
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun q hq => hzc i q hq)
  exact sup_le (sup_le (hzC 0) (hzC 1)) (hzC 2)

end Conn

section CaseB

variable {G : Type} [Group G] [Finite G]

theorem kc_of_normalizesB {X L P : Subgroup G}
    (hZ : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3)
    (hAut : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 A →
      Nat.card A ≤ 9 * Nat.card (centBar 3 A L))
    (hcyc : ∀ T : Subgroup G, IsSylowIn 3 L T → ¬ IsCyclic T)
    (hPX : P ≤ X) (hP : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hT : IsSylowIn 3 L (P ⊓ L)) {A B : Subgroup G} (hA : IsEkIn 3 4 P A) (hB : IsEkIn 3 4 P B) :
    IsKConnectedIn 3 3 X A B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTn : ((P ⊓ L).subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨P.mul_mem (P.mul_mem g.2 hn.1) (P.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.1 (hPN g.2) n).1 hn.2⟩⟩
  obtain ⟨U₂, hU₂T, hU₂, hU₂N⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) P
    (P ⊓ L) hP inf_le_left hTn (hcyc _ hT)
  set D := centBar 3 P L with hD
  have hDP : D ≤ P := inf_le_right
  have hAD : 9 ≤ Nat.card (A ⊓ D : Subgroup G) := by
    obtain ⟨hAP, hAel, hAc⟩ := hA
    have h := hAut A (hAP.trans hPN) hAel
    have he : centBar 3 A L = A ⊓ D := by
      ext g
      rw [mem_centBar_iff', Subgroup.mem_inf, mem_centBar_iff']
      exact ⟨fun h' => ⟨h'.1, hAP h'.1, h'.2⟩, fun h' => ⟨h'.1, h'.2.2⟩⟩
    rw [he, hAc] at h
    omega
  have hDnc : ¬ IsCyclic D := by
    intro hcyc'
    have hAel := hA.2.1
    have hADel : IsElemAbelian 3 (A ⊓ D) := isElemAbelian_mono hAel inf_le_left
    have hnc := not_isCyclic_of_isElemAbelian hADel (by norm_num; exact hAD)
    apply hnc
    exact isCyclic_of_injective (Subgroup.inclusion (inf_le_right : A ⊓ D ≤ D))
      (Subgroup.inclusion_injective _)
  obtain ⟨U₁, hU₁D, hU₁, hU₁N⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) P D
    hP hDP (centBar_normal hPN) hDnc
  have hU₁C : U₁ ≤ centBar 3 ⊤ L := fun u hu => by
    obtain ⟨-, h, hb⟩ := mem_centBar_iff'.1 (hU₁D hu)
    exact mem_centBar_iff'.2 ⟨Subgroup.mem_top u, h, hb⟩
  have hU₁P : U₁ ≤ P := hU₁D.trans hDP
  have hU₂P : U₂ ≤ P := hU₂T.trans inf_le_left
  have hU₂L : U₂ ≤ L := hU₂T.trans inf_le_right
  have hcomm : U₁ ≤ Subgroup.centralizer (U₂ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun v hv =>
      (comm_of_centBar hP (hU₁P hu) (hU₁C hu) (hU₂P hv) (hU₂L hv)).symm
  have hne : U₁ ≠ U₂ := by
    intro heq
    have h3 := hZ U₂ hU₂L (hP.to_le hU₂P) (heq ▸ hU₁C)
    rw [hU₂.2] at h3
    norm_num at h3
  exact kc_of_plane_pair hPX hP hU₁ hU₂ hU₁P hU₂P hU₁N hU₂N hne hcomm hA hB

theorem exists_mem_second_center3 {T M Z₀ : Subgroup G} (hT : IsPGroup 3 T) (hMT : M ≤ T)
    (hZM : Z₀ ≤ M) (hMN : T ≤ Subgroup.normalizer (M : Set G))
    (hZN : T ≤ Subgroup.normalizer (Z₀ : Set G)) (hne : Z₀ ≠ M) :
    ∃ u ∈ M, u ∉ Z₀ ∧ u ^ 3 ∈ Z₀ ∧ ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ Z₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z' : Subgroup ↥T := Z₀.subgroupOf T with hZ'
  haveI hZ'n : Z'.Normal := ⟨fun n hn g => by
    rw [hZ', Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hZN g.2) n).1 hn⟩
  have hQ : IsPGroup 3 (↥T ⧸ Z') := hT.to_quotient Z'
  haveI : Group.IsNilpotent (↥T ⧸ Z') := hQ.isNilpotent
  set q : ↥T →* ↥T ⧸ Z' := QuotientGroup.mk' Z' with hq
  obtain ⟨m, hmM, hmZ⟩ : ∃ m ∈ M, m ∉ Z₀ := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hZM h)
  have hMn : (M.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hMN g.2) n).1 hn⟩
  set M' : Subgroup (↥T ⧸ Z') := (M.subgroupOf T).map q with hM'
  haveI : M'.Normal := hMn.map q (QuotientGroup.mk'_surjective Z')
  have hM'ne : M' ≠ ⊥ := by
    intro h
    have hmem : q ⟨m, hMT hmM⟩ ∈ M' := ⟨⟨m, hMT hmM⟩, Subgroup.mem_subgroupOf.2 hmM, rfl⟩
    rw [h, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmZ (Subgroup.mem_subgroupOf.1 hmem)
  set H : Subgroup (↥T ⧸ Z') := M' ⊓ Subgroup.center (↥T ⧸ Z') with hH
  have hHne : H ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hM'ne
  have hHp : IsPGroup 3 ↥H := hQ.to_subgroup H
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot _).2 hHne
  obtain ⟨k, hk, hcard⟩ := hHp.nontrivial_iff_card.1 inferInstance
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3
    (by rw [hcard]; exact dvd_pow_self 3 (by omega))
  have hw' : orderOf (w : ↥T ⧸ Z') = 3 := by rw [Subgroup.orderOf_coe]; exact hw
  obtain ⟨hwM', hwZ⟩ := Subgroup.mem_inf.1 w.2
  obtain ⟨u, huM, huw⟩ := Subgroup.mem_map.1 hwM'
  have hw1 : (w : ↥T ⧸ Z') ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw'
    norm_num at hw'
  have hw3 : (w : ↥T ⧸ Z') ^ 3 = 1 := by rw [← hw']; exact pow_orderOf_eq_one _
  refine ⟨u, Subgroup.mem_subgroupOf.1 huM, fun huZ => hw1 ?_, ?_, fun t ht => ?_⟩
  · rw [← huw, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 huZ
  · have h1 : q (u ^ 3) = 1 := by rw [map_pow, huw]; exact hw3
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rwa [Subgroup.coe_pow] at h2
  · have hc := Subgroup.mem_center_iff.1 hwZ (q ⟨t, ht⟩)
    have h1 : q (⟨t, ht⟩ * u * ⟨t, ht⟩⁻¹ * u⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      have huw' : q u = (w : ↥T ⧸ Z') := huw
      rw [huw', hc]
      group
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1

theorem false_of_sc3B {X L R Y : Subgroup G} {a : G} (hL : GLAPComponent 3 X L)
    (hZ : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3)
    (hT₁ne : R ⊓ L ≠ ⊥) (hT₁nc : ∀ Z : Subgroup G, Nat.card Z ≤ 3 → Z ≠ R ⊓ L)
    (hRX : R ≤ X) (hR : IsPGroup 3 R)
    (hNn : ∀ r ∈ R, ∀ n ∈ R ⊓ Subgroup.normalizer (L : Set G),
      r * n * r⁻¹ ∈ R ⊓ Subgroup.normalizer (L : Set G))
    (hYN : Y ≤ R ⊓ Subgroup.normalizer (L : Set G))
    (haR : a ∈ R) (haN : a ∉ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (haY : ∀ y ∈ Y, a * y = y * a)
    (hsc : ∀ w ∈ R ⊓ Subgroup.normalizer (L : Set G), w ^ 3 = 1 → (∀ y ∈ Y, w * y = y * w) →
      w ∈ Y) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  set T₁ := R ⊓ L with hT₁
  set Z₀ := T₁ ⊓ centBar 3 ⊤ L with hZ₀
  have hT₁N : T₁ ≤ N := fun t ht => ⟨ht.1, Subgroup.le_normalizer ht.2⟩
  have hNT₁ : N ≤ Subgroup.normalizer (T₁ : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hT₁, Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hn.1)) t)
      ((Subgroup.mem_normalizer_iff.1 hn.2) t)
  have hNZ₀ : N ≤ Subgroup.normalizer (Z₀ : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hNT₁ hn) z).1 hz.1, conj_mem_centBar hn.2 hz.2⟩
  have haX : a⁻¹ ∈ X := X.inv_mem (hRX haR)
  set La := GLBConj a⁻¹ L with hLadef
  set La2 := GLBConj a⁻¹ La with hLa2def
  have hLa : GLAPComponent 3 X La := comp_conj hL haX
  have hLa2 : GLAPComponent 3 X La2 := comp_conj hLa haX
  have hconjLa : ∀ {H : Subgroup G} {u : G}, u ∈ H → a * u * a⁻¹ ∈ GLBConj a⁻¹ H := by
    intro H u hu
    rw [mem_gLBConj]
    simpa [mul_assoc] using hu
  have hneLa : La ≠ L := by
    intro h
    apply haN
    have h1 : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 h
    simpa using (Subgroup.normalizer _).inv_mem h1
  have ha2 : a⁻¹ * a⁻¹ = a := by
    calc a⁻¹ * a⁻¹ = a⁻¹ * a⁻¹ * a ^ 3 := by rw [ha3, mul_one]
      _ = a := by group
  have hneLa2 : La2 ≠ L := by
    intro h
    rw [hLa2def, hLadef, gLBConj_gLBConj, ha2] at h
    exact haN (mem_normalizer_iff_gLBConj_eq.2 h)
  have hneLa12 : La2 ≠ La := by
    intro h
    apply hneLa
    have h1 : GLBConj a La2 = GLBConj a La := by rw [h]
    rwa [hLa2def, gLBConj_gLBConj, inv_mul_cancel, gLBConj_one, hLadef, gLBConj_gLBConj,
      inv_mul_cancel, gLBConj_one] at h1
  have hΩ : ∀ t ∈ T₁, t ^ 3 = 1 → (∀ y ∈ Y, t * y = y * t) → t ∈ Z₀ ∧ t ∈ Y ∧ a * t = t * a := by
    intro t ht ht3 htY
    have htY' := hsc t (hT₁N ht) ht3 htY
    have hta := haY t htY'
    have htLa : t ∈ La := by
      have := hconjLa (H := L) ht.2
      rwa [hta, mul_inv_cancel_right] at this
    exact ⟨⟨ht, mem_centBar_of_modCent hL ht.2 (le_modCent hL hLa hneLa htLa)⟩, htY', hta⟩
  set TY := Y ⊔ T₁ with hTY
  have hTYN : TY ≤ N := sup_le hYN hT₁N
  have hTYp : IsPGroup 3 TY := hR.to_le (hTYN.trans inf_le_left)
  obtain ⟨ζ, hζT, hζ1, hζ3, hζc⟩ := exists_central_of_normalized hTYp le_sup_right
    (hTYN.trans hNT₁) hT₁ne
  obtain ⟨hζZ, -, hζa⟩ := hΩ ζ hζT hζ3 fun y hy => (hζc y (le_sup_left (a := Y) hy)).symm
  have hZ₀3 : Nat.card Z₀ ≤ 3 := hZ Z₀ (inf_le_left.trans inf_le_right)
    (hR.to_le (inf_le_left.trans inf_le_left)) inf_le_right
  have hZ₀eq : Z₀ = Subgroup.zpowers ζ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hζZ) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hζ3 hζ1]
    exact hZ₀3
  have hZa : ∀ c ∈ Z₀, a * c = c * a := by
    intro c hc
    rw [hZ₀eq] at hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_right hζa i).eq
  have hne : Z₀ ≠ T₁ := hT₁nc Z₀ hZ₀3
  obtain ⟨u, huT, huZ, hu3, huc⟩ := exists_mem_second_center3 hTYp le_sup_right inf_le_left
    (hTYN.trans hNT₁) (hTYN.trans hNZ₀) hne
  have huR : u ∈ R := huT.1
  have huL : u ∈ L := huT.2
  set v := a * u * a⁻¹ with hv
  have hvR : v ∈ R := R.mul_mem (R.mul_mem haR huR) (R.inv_mem haR)
  have hvLa : v ∈ La := hconjLa huL
  have hvN : v ∈ N := hNn a haR u (hT₁N huT)
  have huv : u * v = v * u :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR hL hLa hneLa.symm ⟨huR, huL⟩
      ⟨hvR, hvLa⟩
  have hv3 : v ^ 3 = u ^ 3 := by
    rw [hv, conj_pow, hZa _ hu3, mul_inv_cancel_right]
  set x := u * v⁻¹ with hx
  have hxN : x ∈ N := N.mul_mem (hT₁N huT) (N.inv_mem hvN)
  have hx3 : x ^ 3 = 1 := by
    have hcomm : Commute u v⁻¹ := (Commute.inv_right huv)
    rw [hx, hcomm.mul_pow, inv_pow, hv3, mul_inv_cancel]
  have hxY : ∀ y ∈ Y, x * y = y * x := by
    intro y hy
    set c := y * u * y⁻¹ * u⁻¹ with hc
    have hcZ : c ∈ Z₀ := huc y (le_sup_left (a := Y) hy)
    have hca : a * c = c * a := hZa c hcZ
    have hya : a * y = y * a := haY y hy
    have hcu : c * u = u * c :=
      comm_of_centBar hR hcZ.1.1 hcZ.2 huR huL
    have hcv : y * v * y⁻¹ * v⁻¹ = c := by
      have e : y * v * y⁻¹ * v⁻¹ = a * c * a⁻¹ := by
        rw [hv, hc]
        have hy' : a⁻¹ * y * a = y := by
          calc a⁻¹ * y * a = a⁻¹ * (y * a) := by group
            _ = a⁻¹ * (a * y) := by rw [hya]
            _ = y := by group
        calc y * (a * u * a⁻¹) * y⁻¹ * (a * u * a⁻¹)⁻¹
            = a * ((a⁻¹ * y * a) * u * (a⁻¹ * y * a)⁻¹ * u⁻¹) * a⁻¹ := by group
          _ = a * (y * u * y⁻¹ * u⁻¹) * a⁻¹ := by rw [hy']
      rw [e, hca, mul_inv_cancel_right]
    have hcv' : c * v = v * c := by
      have e : c * v = a * (c * u) * a⁻¹ := by
        calc c * v = (a * c * a⁻¹) * v := by rw [hca, mul_inv_cancel_right]
          _ = a * (c * u) * a⁻¹ := by rw [hv]; group
      rw [e, hcu]
      calc a * (u * c) * a⁻¹ = (a * u * a⁻¹) * (a * c * a⁻¹) := by group
        _ = v * c := by rw [hca, mul_inv_cancel_right]
    have e1 : y * u = c * u * y := by rw [hc]; group
    have e2 : y * v⁻¹ = c⁻¹ * v⁻¹ * y := by
      have : c⁻¹ * v⁻¹ = v⁻¹ * c⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hcv']
      rw [this, ← hcv]
      group
    calc x * y = u * v⁻¹ * y := rfl
      _ = c * u * c⁻¹ * v⁻¹ * y := by
          rw [show c * u * c⁻¹ = u by rw [hcu]; group]
      _ = c * u * (c⁻¹ * v⁻¹ * y) := by group
      _ = c * u * (y * v⁻¹) := by rw [e2]
      _ = y * u * v⁻¹ := by rw [← mul_assoc, ← e1]
      _ = y * x := by rw [hx]; group
  have hxa : a * x = x * a := haY x (hsc x hxN hx3 hxY)
  set w := a * v * a⁻¹ with hw
  have hwR : w ∈ R := R.mul_mem (R.mul_mem haR hvR) (R.inv_mem haR)
  have hwLa2 : w ∈ La2 := hconjLa hvLa
  have hvw : v * w = w * v :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR hLa hLa2 hneLa12.symm
      ⟨hvR, hvLa⟩ ⟨hwR, hwLa2⟩
  have huvw : u = v * v * w⁻¹ := by
    have e : a * x * a⁻¹ = v * w⁻¹ := by rw [hx, hw, hv]; group
    rw [hxa, mul_inv_cancel_right, hx] at e
    have hwv : w⁻¹ * v = v * w⁻¹ := by
      calc w⁻¹ * v = w⁻¹ * (v * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * v) * w⁻¹ := by rw [hvw]
        _ = v * w⁻¹ := by group
    calc u = u * v⁻¹ * v := by group
      _ = v * w⁻¹ * v := by rw [e]
      _ = v * (w⁻¹ * v) := by group
      _ = v * (v * w⁻¹) := by rw [hwv]
      _ = v * v * w⁻¹ := by group
  have hum : u ∈ modCent X L := by
    rw [huvw]
    exact (modCent X L).mul_mem ((modCent X L).mul_mem (le_modCent hL hLa hneLa hvLa)
      (le_modCent hL hLa hneLa hvLa)) ((modCent X L).inv_mem (le_modCent hL hLa2 hneLa2 hwLa2))
  exact huZ ⟨huT, mem_centBar_of_modCent hL huL hum⟩

theorem isCyclic_of_card_le_three {Y : Type*} [Group Y] [Finite Y] (h : Nat.card Y ≤ 3) : IsCyclic Y := by
  have h' : Nat.card Y = 1 ∨ Nat.card Y = 2 ∨ Nat.card Y = 3 := by
    have := Nat.card_pos (α := Y)
    omega
  rcases h' with h' | h' | h'
  · haveI : Subsingleton Y := (Nat.card_eq_one_iff_unique.1 h').1
    infer_instance
  · exact isCyclic_of_prime_card (p := 2) (hp := ⟨Nat.prime_two⟩) h'
  · exact isCyclic_of_prime_card (p := 3) (hp := ⟨Nat.prime_three⟩) h'

theorem ne_of_not_isCyclic {T : Subgroup G} (hT : ¬ IsCyclic T) :
    ∀ Z : Subgroup G, Nat.card Z ≤ 3 → Z ≠ T := by
  rintro Z hZ rfl
  exact hT (isCyclic_of_card_le_three hZ)

theorem kc_index_threeB {X L R : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3)
    (hAut : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 A →
      Nat.card A ≤ 9 * Nat.card (centBar 3 A L))
    (hcyc : ∀ T : Subgroup G, IsSylowIn 3 L T → ¬ IsCyclic T)
    (hRX : R ≤ X) (hR : IsPGroup 3 R)
    (hT : IsSylowIn 3 L (R ⊓ L)) (hn : (Subgroup.normalizer (L : Set G)).relIndex R = 3)
    {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  have hnorm : ((Subgroup.normalizer (L : Set G)).subgroupOf R).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hR
    have hidx : ((Subgroup.normalizer (L : Set G)).subgroupOf R).index = 3 := hn
    rw [hidx, hr]
    have hr0 : r ≠ 0 := by
      rintro rfl
      have h1 := ((Subgroup.normalizer (L : Set G)).subgroupOf R).index_dvd_card
      rw [hidx, hr, pow_zero] at h1
      norm_num at h1
    have hp := Nat.minFac_prime (show 3 ^ r ≠ 1 by
      intro h; exact hr0 (by simpa using (Nat.pow_eq_one.1 h)))
    exact ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hp.dvd_of_dvd_pow (Nat.minFac_dvd _))).symm
  have hNn : ∀ r ∈ R, ∀ m ∈ N, r * m * r⁻¹ ∈ N := by
    intro r hr m hm
    have := hnorm.conj_mem ⟨m, hm.1⟩ (Subgroup.mem_subgroupOf.2 hm.2) ⟨r, hr⟩
    exact ⟨R.mul_mem (R.mul_mem hr hm.1) (R.inv_mem hr), Subgroup.mem_subgroupOf.1 this⟩
  have hNX : N ≤ X := inf_le_left.trans hRX
  have hNp : IsPGroup 3 N := hR.to_le inf_le_left
  have hNN : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hTN : IsSylowIn 3 L (N ⊓ L) := by
    have : N ⊓ L = R ⊓ L := by
      rw [hN, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : L ≤ Subgroup.normalizer (L : Set G))]
    rw [this]
    exact hT
  have hT₁ne : R ⊓ L ≠ ⊥ := by
    intro h
    apply hcyc _ hT
    rw [h]
    infer_instance
  have hred : ∀ A : Subgroup G, IsEkIn 3 4 R A →
      ∃ A' : Subgroup G, IsEkIn 3 4 N A' ∧ IsKConnectedIn 3 3 X A A' := by
    intro A hA
    obtain ⟨hAR, hAel, hAc⟩ := hA
    have hA81 : Nat.card A = 81 := by rw [hAc]; norm_num
    by_cases hAN : A ≤ Subgroup.normalizer (L : Set G)
    · exact ⟨A, ⟨le_inf hAR hAN, hAel, hAc⟩,
        kc_of_le_elem (hAR.trans hRX) hAel le_rfl le_rfl (by omega) (by omega)⟩
    · obtain ⟨a, haA, haN⟩ := Set.not_subset.1 hAN
      set Y := A ⊓ Subgroup.normalizer (L : Set G) with hY
      have hY27 : Nat.card Y = 27 := by
        have h1 := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (L : Set G)) (K := A)
        have h2 : (Subgroup.normalizer (L : Set G)).relIndex A ≤ 3 :=
          hn ▸ Subgroup.relIndex_le_of_le_right hAR (by rw [hn]; norm_num)
        have h3 : (Subgroup.normalizer (L : Set G)).relIndex A ≠ 1 := fun h =>
          hAN (Subgroup.relIndex_eq_one.1 h)
        rw [hA81, inf_comm] at h1
        rw [← hY] at h1
        have h0 : (Subgroup.normalizer (L : Set G)).relIndex A ≠ 0 := by
          intro h; rw [h, zero_mul] at h1; norm_num at h1
        interval_cases h : (Subgroup.normalizer (L : Set G)).relIndex A <;> omega
      have hYN : Y ≤ N := fun y hy => ⟨hAR hy.1, hy.2⟩
      have hYel : IsElemAbelian 3 Y := isElemAbelian_mono hAel inf_le_left
      by_cases hw : ∃ w ∈ N, w ^ 3 = 1 ∧ (∀ y ∈ Y, w * y = y * w) ∧ w ∉ Y
      · obtain ⟨w, hwN, hw3, hwY, hwnY⟩ := hw
        set A' : Subgroup G := Y ⊔ Subgroup.zpowers w with hA'
        have hA'c : Nat.card A' = 81 := by
          rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three Y hw3 hwnY
            (fun e he => (hwY e he).symm), hY27]
        have hYz : Y ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          exact (Commute.zpow_left (hwY y hy) i).eq
        have hA'el : IsElemAbelian 3 A' := isElemAbelian_sup_of_commute hYel
          (Claims1245.isElemAbelian_zpowers_of_pow_three hw3) hYz
        have hA'N : A' ≤ N := sup_le hYN (Subgroup.zpowers_le.2 hwN)
        refine ⟨A', ⟨hA'N, hA'el, by rw [hA'c]; norm_num⟩, ?_⟩
        exact kc_trans (kc_of_le_elem (hAR.trans hRX) hAel le_rfl (show Y ≤ A from inf_le_left)
            (by omega) (by omega))
          (kc_of_le_elem (hA'N.trans hNX) hA'el (show Y ≤ A' from le_sup_left) le_rfl (by omega)
            (by omega))
      · exfalso
        push Not at hw
        exact false_of_sc3B hL hZ hT₁ne (ne_of_not_isCyclic (hcyc _ hT)) hRX hR hNn hYN (hAR haA) haN
          (hAel.2 a haA) (fun y hy => hAel.comm haA hy.1) (fun w hwN hw3 hwY => hw w hwN hw3 hwY)
  obtain ⟨A', hA', hAA'⟩ := hred A hA
  obtain ⟨B', hB', hBB'⟩ := hred B hB
  exact kc_trans hAA' (kc_trans (kc_of_normalizesB hZ hAut hcyc hNX hNp hNN hTN hA' hB')
    (kc_symm hBB'))

theorem card_iSup_conj_geB {X L R U : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3) (hRX : R ≤ X)
    (hR : IsPGroup 3 R) (hUR : U ≤ R) (hUL : U ≤ L) (hU : IsPPlane 3 U) :
    ∀ S : Finset G, (∀ g ∈ S, g ∈ R) →
      (∀ g ∈ S, ∀ g' ∈ S, GLBConj g L = GLBConj g' L → g = g') → S.Nonempty →
      3 ^ (S.card + 1) ≤ Nat.card ↥(⨆ (g : G) (_ : g ∈ S), GLBConj g U : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUc : Nat.card U = 9 := by rw [hU.2]; norm_num
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _ h; exact absurd h Finset.not_nonempty_empty
  | @insert g S hgS ih =>
    intro hSR hinj _
    rw [Finset.iSup_insert]
    have hgR : g ∈ R := hSR g (Finset.mem_insert_self g S)
    set V := GLBConj g U with hV
    have hVc : Nat.card V = 9 := by rw [hV, Lemma1112b.card_glbConj, hUc]
    by_cases hS0 : S = ∅
    · subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq, insert_empty_eq,
        Finset.card_singleton]
      rw [hVc]
      norm_num
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS0
    have ih' := ih (fun g' hg' => hSR g' (Finset.mem_insert_of_mem hg'))
      (fun g₁ h₁ g₂ h₂ h => hinj g₁ (Finset.mem_insert_of_mem h₁) g₂ (Finset.mem_insert_of_mem h₂) h)
      hSne
    set W := ⨆ (g' : G) (_ : g' ∈ S), GLBConj g' U with hW
    have hne : ∀ g' ∈ S, GLBConj g' L ≠ GLBConj g L := fun g' hg' h =>
      hgS (hinj g' (Finset.mem_insert_of_mem hg') g (Finset.mem_insert_self g S) h ▸ hg')
    have hUr : ∀ r ∈ R, GLBConj r U ≤ R ⊓ GLBConj r L := fun r hr =>
      le_inf ((gLBConj_mono r hUR).trans
        (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hr)).le) (gLBConj_mono r hUL)
    have hcomm : V ≤ Subgroup.centralizer (W : Set G) := by
      refine cent_symm (iSup₂_le fun g' hg' => ?_)
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hg'R := hSR g' (Finset.mem_insert_of_mem hg')
      exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR
        (comp_conj hL (hRX hgR)) (comp_conj hL (hRX hg'R)) (hne g' hg').symm (hUr g hgR hz)
        (hUr g' hg'R hy)
    have hint : Nat.card (V ⊓ W : Subgroup G) ≤ 3 := by
      have hconjV : GLBConj g⁻¹ V = U := by
        rw [hV, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
      have hconjW : GLBConj g⁻¹ W ≤ modCent X L := by
        change W.map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ _
        rw [Subgroup.map_le_iff_le_comap]
        refine iSup₂_le fun g' hg' => ?_
        rw [← Subgroup.map_le_iff_le_comap]
        change GLBConj g⁻¹ (GLBConj g' U) ≤ _
        rw [gLBConj_gLBConj]
        have hg'R := hSR g' (Finset.mem_insert_of_mem hg')
        have hc : GLAPComponent 3 X (GLBConj (g' * g⁻¹) L) :=
          comp_conj hL (hRX (R.mul_mem hg'R (R.inv_mem hgR)))
        have hneL : GLBConj (g' * g⁻¹) L ≠ L := by
          intro h
          apply hne g' hg'
          have h1 : GLBConj g (GLBConj (g' * g⁻¹) L) = GLBConj g L := by rw [h]
          rwa [gLBConj_gLBConj, show g' * g⁻¹ * g = g' by group] at h1
        exact (gLBConj_mono _ hUL).trans (le_modCent hL hc hneL)
      have hle : GLBConj g⁻¹ (V ⊓ W) ≤ U ⊓ modCent X L := by
        rw [← hconjV]
        exact le_inf (gLBConj_mono _ inf_le_left) ((gLBConj_mono _ inf_le_right).trans hconjW)
      have h3 : Nat.card (U ⊓ modCent X L : Subgroup G) ≤ 3 :=
        hZ _ (inf_le_left.trans hUL) (hR.to_le (inf_le_left.trans hUR))
          (fun t ht => mem_centBar_of_modCent hL (hUL ht.1) ht.2)
      calc Nat.card (V ⊓ W : Subgroup G) = Nat.card (GLBConj g⁻¹ (V ⊓ W)) :=
            (Lemma1112b.card_glbConj _ _).symm
        _ ≤ Nat.card (U ⊓ modCent X L : Subgroup G) := Subgroup.card_le_of_le hle
        _ ≤ 3 := h3
    have hcard := card_sup_mul_inf hcomm
    rw [hVc] at hcard
    rw [Finset.card_insert_of_notMem hgS]
    have hpos : 0 < Nat.card (V ⊓ W : Subgroup G) := Nat.card_pos
    have h3S : 3 ^ (S.card + 1 + 1) = 3 * 3 ^ (S.card + 1) := by ring
    rw [h3S]
    nlinarith

theorem kc_index_ge_nineB {X L R : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3)
    (hcyc : ∀ T : Subgroup G, IsSylowIn 3 L T → ¬ IsCyclic T) (hRX : R ≤ X) (hR : IsPGroup 3 R)
    (hT : IsSylowIn 3 L (R ⊓ L)) (hn : 9 ≤ (Subgroup.normalizer (L : Set G)).relIndex R)
    {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  have hTn : ((R ⊓ L).subgroupOf N).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨R.mul_mem (R.mul_mem g.2.1 hx.1) (R.inv_mem g.2.1),
      (Subgroup.mem_normalizer_iff.1 g.2.2 x).1 hx.2⟩⟩
  obtain ⟨U, hUT, hU, hUN⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) N
    (R ⊓ L) (hR.to_le inf_le_left) (fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩) hTn
    (hcyc _ hT)
  have hUR : U ≤ R := hUT.trans inf_le_left
  have hUL : U ≤ L := hUT.trans inf_le_right
  obtain ⟨hER, hEel, hEN⟩ := conjProd_props hL hRX hR hUR hUL hU.1 hUN
  set Q := ↥R ⧸ (Subgroup.normalizer (L : Set G)).subgroupOf R with hQ
  haveI : Fintype Q := Fintype.ofFinite Q
  have hQc : 9 ≤ (Finset.univ : Finset Q).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hn
  obtain ⟨F, -, hF⟩ := Finset.exists_subset_card_eq hQc
  set S : Finset G := F.image (fun q : Q => ((q.out : ↥R) : G)⁻¹) with hS
  have hSR : ∀ g ∈ S, g ∈ R := by
    intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
    exact R.inv_mem (q.out).2
  have hinj : ∀ g ∈ S, ∀ g' ∈ S, GLBConj g L = GLBConj g' L → g = g' := by
    intro g hg g' hg' h
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hg'
    have h1 : GLBConj (q'.out : G) (GLBConj ((q.out : ↥R) : G)⁻¹ L) =
        GLBConj (q'.out : G) (GLBConj ((q'.out : ↥R) : G)⁻¹ L) := by rw [h]
    rw [gLBConj_gLBConj, gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1
    have hmem : ((q.out : ↥R) : G)⁻¹ * (q'.out : G) ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 h1
    have hqq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using hmem))
    rw [hqq]
  have hScard : S.card = 9 := by
    rw [hS, Finset.card_image_of_injOn, hF]
    intro q _ q' _ h
    have h1 : (q.out : ↥R) = q'.out := Subtype.ext (inv_injective h)
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', h1]
  have hSne : S.Nonempty := Finset.card_pos.1 (by rw [hScard]; norm_num)
  have hbound := card_iSup_conj_geB hL hZ hRX hR hUR hUL hU S hSR hinj hSne
  rw [hScard] at hbound
  have hE10 : 3 ^ 10 ≤ Nat.card (conjProd R U) := by
    refine hbound.trans (Subgroup.card_le_of_le (iSup₂_le fun g hg => ?_))
    exact gLBConj_le_conjProd (hSR g hg)
  exact kc_trans (kc_of_big_normal hRX hR hER hEN hEel hE10 hA)
    (kc_symm (kc_of_big_normal hRX hR hER hEN hEel hE10 hB))

theorem kc_of_hypB {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3)
    (hAut : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 A →
      Nat.card A ≤ 9 * Nat.card (centBar 3 A L))
    (hcyc : ∀ T : Subgroup G, IsSylowIn 3 L T → ¬ IsCyclic T)
    {R : Subgroup G} (hR : IsSylowIn 3 X R) {U V : Subgroup G} (hU : IsEkIn 3 4 R U)
    (hV : IsEkIn 3 4 R V) : IsKConnectedIn 3 3 X U V := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : IsSylowIn 3 L (R ⊓ L) := Claims1245.isSylowIn_inf_of_isSubnormal hR hL.2.1
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hR.2.1
  have hdvd : (Subgroup.normalizer (L : Set G)).relIndex R ∣ 3 ^ r := by
    rw [← hr]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rcases k with _ | _ | k
  · rw [pow_zero] at hk
    exact kc_of_normalizesB hZ hAut hcyc hR.1 hR.2.1 (Subgroup.relIndex_eq_one.1 hk) hT hU hV
  · rw [zero_add, pow_one] at hk
    exact kc_index_threeB hL hZ hAut hcyc hR.1 hR.2.1 hT hk hU hV
  · refine kc_index_ge_nineB hL hZ hcyc hR.1 hR.2.1 hT ?_ hU hV
    rw [hk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CaseB

section PropsB

variable {G : Type} [Group G] [Finite G]

theorem card_le_center_of_le_centBar {L U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 3 U)
    (hUC : U ≤ centBar 3 ⊤ L) : Nat.card U ≤ Nat.card (Subgroup.center (barOf 3 L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hf
  let g : ↥U →* barOf 3 L := f.comp (Subgroup.inclusion hUL)
  have hginj : Function.Injective g := by
    intro u v huv
    exact Subtype.ext (barOf_injOn hUL hU u.2 v.2 huv)
  have hcen : g.range ≤ Subgroup.center (barOf 3 L) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) w
    obtain ⟨-, -, hcomm⟩ := Inputs1114.mem_centBar_iff_forall.1 (hUC u.2)
    have h1 := hcomm l l.2
    obtain ⟨y, hy, hyc⟩ := h1
    have hy' : (⟨u, hUL u.2⟩ : ↥L) * l * (⟨u, hUL u.2⟩ : ↥L)⁻¹ * l⁻¹ ∈ GLAPPrimeCore 3 ↥L := by
      have : y = (⟨u, hUL u.2⟩ : ↥L) * l * (⟨u, hUL u.2⟩ : ↥L)⁻¹ * l⁻¹ := Subtype.ext (by simpa using hyc)
      rw [← this]
      exact hy
    have h2 : f ((⟨u, hUL u.2⟩ : ↥L) * l * (⟨u, hUL u.2⟩ : ↥L)⁻¹ * l⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hy'
    simp only [map_mul, map_inv] at h2
    have h3 : g u = f ⟨u, hUL u.2⟩ := rfl
    rw [h3]
    calc f l * f ⟨u, hUL u.2⟩ = (f ⟨u, hUL u.2⟩ * f l * (f ⟨u, hUL u.2⟩)⁻¹ * (f l)⁻¹)⁻¹ *
          (f ⟨u, hUL u.2⟩ * f l) := by group
      _ = f ⟨u, hUL u.2⟩ * f l := by rw [h2, inv_one, one_mul]
  calc Nat.card U = Nat.card g.range := Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
    _ ≤ Nat.card (Subgroup.center (barOf 3 L)) := Subgroup.card_le_of_le hcen

theorem card_center_le_three_of_not_dvd {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hZ : IsPGroup 3 (Subgroup.center Y)) (h81 : ¬ 81 ∣ Nat.card Y) :
    Nat.card (Subgroup.center Y) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hZP⟩ := hZ.exists_le_sylow
  set Z := Subgroup.center Y with hZdef
  have hZle : Z ≤ ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ := by
    intro z hz
    have h1 := pow_index_mem_comm hperf P hz
    obtain ⟨k, hk⟩ := hZ ⟨z, hz⟩
    have hzk : z ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hcop : (P : Subgroup Y).index.Coprime (orderOf z) := by
      have h3i : Nat.Coprime 3 (P : Subgroup Y).index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hzk)
        (Nat.Coprime.pow_right k h3i.symm)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ h1 m
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have ha3 : a ≤ 3 := by
    by_contra h
    apply h81
    have : 3 ^ 4 ∣ Nat.card (P : Subgroup Y) := ha ▸ pow_dvd_pow 3 (by omega)
    exact this.trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hZ
  have hb2 : 2 ≤ b := by
    by_contra h
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl | rfl <;> rw [hb] at hlt <;> norm_num at hlt
  set Z' : Subgroup ↥(P : Subgroup Y) := Z.subgroupOf P with hZ'
  haveI : Z'.Normal := (Subgroup.normal_of_characteristic _).subgroupOf _
  have hZ'c : Nat.card Z' = Nat.card Z := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
  rw [hZ'c, hb, ha] at hq
  have hq3 : Nat.card (↥(P : Subgroup Y) ⧸ Z') ≤ 3 := by
    have h1 : (3 : ℕ) ^ a ≤ 27 := by
      calc (3 : ℕ) ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha3
        _ = 27 := by norm_num
    have h2 : (9 : ℕ) ≤ 3 ^ b := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb2
    nlinarith
  haveI : IsCyclic (↥(P : Subgroup Y) ⧸ Z') := isCyclic_of_card_le_three hq3
  have hab : IsMulCommutative ↥(P : Subgroup Y) := by
    refine (QuotientGroup.mk' Z').isMulCommutative_of_isCyclic_of_ker_le_center ?_
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : Y) ∈ Z := Subgroup.mem_subgroupOf.1 hx
    exact Subtype.ext (Subgroup.mem_center_iff.1 hx' y)
  have hcomm : ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hcomm] at hZle
  have h1 : Nat.card Z ≤ 1 := by
    calc Nat.card Z ≤ Nat.card (⊥ : Subgroup Y) := Subgroup.card_le_of_le hZle
      _ = 1 := Subgroup.card_bot
  omega

theorem hZ_of_not_dvd {X L : Subgroup G} (hL : GLAPComponent 3 X L) (h81 : ¬ 81 ∣ Nat.card L) :
    ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 3 := by
  intro U hUL hU hUC
  refine (card_le_center_of_le_centBar hUL hU hUC).trans ?_
  refine card_center_le_three_of_not_dvd (barOf_perfect hL)
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.isPGroup_center_barOf L) ?_
  intro h
  apply h81
  exact h.trans (Dvd.intro _
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)).symm)

theorem card_le_nine_mul_centBarB {L A : Subgroup G}
    (hAutL : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) ≤ 2)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 9 * Nat.card (centBar 3 A L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ι : ↥A →* ↥(Subgroup.normalizer (L : Set G)) :=
    { toFun := fun a => ⟨a.1, hAN a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let f : ↥A →* MulAut (barOf 3 L) := (barAut 3 L).comp ι
  have hker : f.ker.map A.subtype = centBar 3 A L := by
    ext g
    rw [Subgroup.mem_map, mem_centBar_iff']
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hAN x.2, MonoidHom.mem_ker.1 hx⟩
    · rintro ⟨hX, h, hb⟩
      exact ⟨⟨g, hX⟩, MonoidHom.mem_ker.2 hb, rfl⟩
  have hkc : Nat.card (centBar 3 A L) = Nat.card f.ker := by
    rw [← hker, Subgroup.card_map_of_injective A.subtype_injective]
  have hel : IsElemAbelian 3 f.range := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      show (u : MulAut (barOf 3 L)) * v = v * u
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.comm a.2 b.2)
    · obtain ⟨a, rfl⟩ := hy
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a.1 a.2)
      rw [this, map_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hel.isPGroup
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : f.range ≤ ⊤) hel hk).trans hAutL
  have hr : Nat.card f.range ≤ 9 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hA' : Nat.card A = Nat.card ↥A := rfl
  rw [hA', CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f, hkc, mul_comm]
  exact Nat.mul_le_mul_right _ hr

theorem not_isCyclic_of_two_le_pRank {L T : Subgroup G}
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L))) (hT : IsSylowIn 3 L T) : ¬ IsCyclic T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcyc
  obtain ⟨F, -, hF, hFc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (barOf 3 L))
  obtain ⟨F₂, hF₂F, hF₂, hF₂c⟩ := exists_le_isElemAbelian_card hF
    (show 3 ^ 2 ∣ Nat.card F by rw [hFc]; exact pow_dvd_pow 3 h2)
  obtain ⟨S', hS'⟩ := hF₂.isPGroup.exists_le_sylow
  obtain ⟨P', hP'⟩ := Claims1245.exists_sylow_of_isSylowIn hT
  set S := P'.mapSurjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L)) with hS
  have hTc : IsCyclic ↥(T.subgroupOf L) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hT.1).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hScyc : IsCyclic ↥(S : Subgroup (barOf 3 L)) := by
    rw [hS, Sylow.coe_mapSurjective, hP']
    exact isCyclic_of_surjective ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).subgroupMap (T.subgroupOf L))
      ((QuotientGroup.mk' _).subgroupMap_surjective _)
  have hS'cyc : IsCyclic ↥(S' : Subgroup (barOf 3 L)) := (MulEquiv.isCyclic (Sylow.equiv S S')).1 hScyc
  have hF₂cyc : IsCyclic ↥F₂ :=
    isCyclic_of_injective (Subgroup.inclusion hS') (Subgroup.inclusion_injective _)
  exact not_isCyclic_of_isElemAbelian hF₂ (by rw [hF₂c]) hF₂cyc

end PropsB

section AssemblyB

variable {G : Type} [Group G] [Finite G]

theorem kc_caseB {X L : Subgroup G} (hL : GLAPComponent 3 X L) (h81 : ¬ 81 ∣ Nat.card L)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) = 2)
    (hAut2 : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) = 2) {R : Subgroup G}
    (hR : IsSylowIn 3 X R) {U V : Subgroup G} (hU : IsEkIn 3 4 R U) (hV : IsEkIn 3 4 R V) :
    IsKConnectedIn 3 3 X U V :=
  kc_of_hypB hL (hZ_of_not_dvd hL h81) (fun _ hAN hA => card_le_nine_mul_centBarB hAut2.le hAN hA)
    (fun _ hT => not_isCyclic_of_two_le_pRank h2.ge hT) hR hU hV

end AssemblyB

section NonNormalizing

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.Coordinator (conj_mem_gLAPPrimeCoreOf_of_mem_normalizer)

theorem exists_index_three {R N : Subgroup G} (hR : IsPGroup 3 R) (hNR : N ≤ R) (hne : N ≠ R) :
    ∃ Q : Subgroup G, N ≤ Q ∧ Q ≤ R ∧ Q.relIndex R = 3 ∧ ∀ r ∈ R, ∀ q ∈ Q, r * q * r⁻¹ ∈ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hR
  set N' : Subgroup ↥R := N.subgroupOf R with hN'
  have hN'p : IsPGroup 3 ↥N' := hR.to_subgroup N'
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hN'p
  have hN'c : Nat.card N' = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  have hba : b < a := by
    by_contra h
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hNR ?_
    rw [← hN'c, hb, ha]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hRc : Nat.card ↥R = 3 ^ a := ha
  obtain ⟨Q', hQ'c, hNQ'⟩ := Sylow.exists_subgroup_card_pow_prime_le 3 (n := b) (m := a - 1)
    (show 3 ^ (a - 1) ∣ Nat.card ↥R by rw [hRc]; exact pow_dvd_pow 3 (by omega)) N' hb (by omega)
  have hidx : Q'.index = 3 := by
    have h := Q'.index_mul_card
    rw [hQ'c, hRc] at h
    have h3 : 3 ^ a = 3 * 3 ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h
  have hnorm : Q'.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hidx, hRc]
    have ha0 : a ≠ 0 := by omega
    have hp := Nat.minFac_prime (show 3 ^ a ≠ 1 by
      intro h; exact ha0 (by simpa using (Nat.pow_eq_one.1 h)))
    exact ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hp.dvd_of_dvd_pow (Nat.minFac_dvd _))).symm
  refine ⟨Q'.map R.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hNR hx⟩, hNQ' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · show ((Q'.map R.subtype).comap R.subtype).index = 3
    rw [Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    exact hidx
  · rintro r hr _ ⟨q, hq, rfl⟩
    exact ⟨⟨r, hr⟩ * q * ⟨r, hr⟩⁻¹, hnorm.conj_mem q hq ⟨r, hr⟩, rfl⟩

theorem zpow_mem_iff {R Q : Subgroup G} (hQR : Q ≤ R) (hQ : Q.relIndex R = 3)
    (hQn : ∀ r ∈ R, ∀ q ∈ Q, r * q * r⁻¹ ∈ Q) {t : G} (htR : t ∈ R) (htQ : t ∉ Q) (m : ℤ) :
    t ^ m ∈ Q ↔ (3 : ℤ) ∣ m := by
  set Q' : Subgroup ↥R := Q.subgroupOf R with hQ'
  haveI : Q'.Normal := ⟨fun n hn g => by
    rw [hQ', Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g g.2 n hn⟩
  have hcard : Nat.card (↥R ⧸ Q') = 3 := hQ
  have ht3 : t ^ 3 ∈ Q := by
    have h1 : (QuotientGroup.mk' Q' ⟨t, htR⟩) ^ Nat.card (↥R ⧸ Q') = 1 := pow_card_eq_one'
    rw [hcard, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simpa using h2
  have ht3' : ∀ k : ℤ, t ^ (3 * k) ∈ Q := fun k => by
    rw [zpow_mul]
    exact Q.zpow_mem (by exact_mod_cast ht3) k
  have ht2 : t ^ 2 ∉ Q := by
    intro h
    apply htQ
    have : t = t ^ 3 * (t ^ 2)⁻¹ := by group
    rw [this]
    exact Q.mul_mem ht3 (Q.inv_mem h)
  constructor
  · intro h
    obtain ⟨k, r, hr0, hr3, rfl⟩ : ∃ k r : ℤ, 0 ≤ r ∧ r < 3 ∧ m = 3 * k + r :=
      ⟨m / 3, m % 3, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num),
        (Int.mul_ediv_add_emod m 3).symm⟩
    have hr : t ^ r ∈ Q := by
      have e : t ^ r = (t ^ (3 * k))⁻¹ * t ^ (3 * k + r) := by rw [zpow_add]; group
      rw [e]
      exact Q.mul_mem (Q.inv_mem (ht3' k)) h
    interval_cases r
    · exact ⟨k, by ring⟩
    · exact absurd (by simpa using hr) htQ
    · exact absurd (by simpa using hr) ht2
  · rintro ⟨k, rfl⟩
    exact ht3' k

theorem eq_of_pow_mul_mem {R Q : Subgroup G} (hQR : Q ≤ R) (hQ : Q.relIndex R = 3)
    (hQn : ∀ r ∈ R, ∀ q ∈ Q, r * q * r⁻¹ ∈ Q) {t : G} (htR : t ∈ R) (htQ : t ∉ Q) {j k : ℕ}
    (hj : j < 3) (hk : k < 3) {x : G} (hx : x ∈ Q) (h : t ^ j * x * (t ^ k)⁻¹ ∈ Q) : j = k := by
  have h1 : t ^ j * x * (t ^ j)⁻¹ ∈ Q := hQn _ (R.pow_mem htR j) x hx
  have h2 : t ^ j * (t ^ k)⁻¹ ∈ Q := by
    have e : t ^ j * (t ^ k)⁻¹ = (t ^ j * x * (t ^ j)⁻¹)⁻¹ * (t ^ j * x * (t ^ k)⁻¹) := by group
    rw [e]
    exact Q.mul_mem (Q.inv_mem h1) h
  have h3 : t ^ ((j : ℤ) - k) ∈ Q := by
    rw [zpow_sub, zpow_natCast, zpow_natCast]
    exact h2
  rw [zpow_mem_iff hQR hQ hQn htR htQ] at h3
  omega

theorem conj_mem_modCent {X L : Subgroup G} {g m : G} (hg : g ∈ X)
    (hm : m ∈ modCent X (GLBConj g L)) : g * m * g⁻¹ ∈ modCent X L := by
  obtain ⟨hmX, hm⟩ := mem_modCent.1 hm
  refine mem_modCent.2 ⟨X.mul_mem (X.mul_mem hg hmX) (X.inv_mem hg), fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ GLBConj g L := by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hl
  have h2 := conj_mem_gLAPPrimeCoreOf_of_mem_normalizer (Subgroup.le_normalizer hg) (hm _ hl')
  have e : g * (m * (g⁻¹ * l * g) * m⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ =
      g * m * g⁻¹ * l * (g * m * g⁻¹)⁻¹ * l⁻¹ := by group
  rwa [e] at h2

theorem iSup_inf_iInf_eq_bot {X L R U : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ1 : ∀ w ∈ L, w ∈ modCent X L → (∃ k : ℕ, w ^ (3 ^ k) = 1) → w = 1)
    (hRX : R ≤ X) (hR : IsPGroup 3 R) (hUR : U ≤ R) (hUL : U ≤ L)
    (hUN : R ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    ∀ S : Finset G, (∀ g ∈ S, g ∈ R) →
      (⨆ (g : G) (_ : g ∈ S), GLBConj g U) ⊓ (⨅ (g : G) (_ : g ∈ S), modCent X (GLBConj g L)) = ⊥ := by
  classical
  have hUr : ∀ r ∈ R, GLBConj r U ≤ R ⊓ GLBConj r L := fun r hr =>
    le_inf ((gLBConj_mono r hUR).trans
      (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hr)).le) (gLBConj_mono r hUL)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert g₀ S hg₀S ih =>
    intro hSR
    have hg₀R : g₀ ∈ R := hSR g₀ (Finset.mem_insert_self g₀ S)
    have hSR' : ∀ g ∈ S, g ∈ R := fun g hg => hSR g (Finset.mem_insert_of_mem hg)
    have ih' := ih hSR'
    rw [Finset.iSup_insert, Finset.iInf_insert]
    set V := GLBConj g₀ U with hV
    set W := ⨆ (g : G) (_ : g ∈ S), GLBConj g U with hW
    set M := ⨅ (g : G) (_ : g ∈ S), modCent X (GLBConj g L) with hM
    rw [eq_bot_iff]
    rintro x ⟨hxVW, hxM0, hxM⟩
    by_cases hrep : ∃ g ∈ S, GLBConj g L = GLBConj g₀ L
    · obtain ⟨g, hgS, hgL⟩ := hrep
      have hVW : V ≤ W := by
        rw [hV, gLBConj_eq_of_eq hUN hg₀R (hSR' g hgS) hgL.symm]
        exact le_iSup₂_of_le g hgS le_rfl
      have hx : x ∈ W ⊓ M := ⟨(sup_eq_right.2 hVW) ▸ hxVW, hxM⟩
      rw [ih'] at hx
      exact hx
    · push Not at hrep
      have hWM0 : W ≤ modCent X (GLBConj g₀ L) := iSup₂_le fun g hg =>
        (gLBConj_mono g hUL).trans (le_modCent (comp_conj hL (hRX hg₀R)) (comp_conj hL (hRX (hSR' g hg)))
          (hrep g hg))
      have hVc : V ≤ Subgroup.centralizer (W : Set G) := by
        refine cent_symm (iSup₂_le fun g hg => ?_)
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR
          (comp_conj hL (hRX hg₀R)) (comp_conj hL (hRX (hSR' g hg))) (hrep g hg).symm (hUr g₀ hg₀R hz)
          (hUr g (hSR' g hg) hy)
      obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup hVc hxVW
      have hvM : v ∈ modCent X (GLBConj g₀ L) := by
        have e : v = v * w * w⁻¹ := by group
        rw [e]
        exact (modCent X _).mul_mem hxM0 ((modCent X _).inv_mem (hWM0 hw))
      have hv1 : v = 1 := by
        have hvL : g₀ * v * g₀⁻¹ ∈ L := mem_gLBConj.1 ((hUr g₀ hg₀R hv).2)
        have hvm := conj_mem_modCent (hRX hg₀R) hvM
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨v, (hUr g₀ hg₀R hv).1⟩
        have hvk : v ^ (3 ^ k) = 1 := by
          rw [← hk]
          simpa using pow_orderOf_eq_one (⟨v, (hUr g₀ hg₀R hv).1⟩ : ↥R)
        have h1 := hZ1 _ hvL hvm ⟨k, by rw [conj_pow, hvk]; group⟩
        calc v = g₀⁻¹ * (g₀ * v * g₀⁻¹) * g₀ := by group
          _ = 1 := by rw [h1]; group
      rw [hv1, one_mul] at hxM ⊢
      have hx : w ∈ W ⊓ M := ⟨hw, hxM⟩
      rw [ih'] at hx
      exact hx

theorem iSup_inf_iInf_eq_bot' {X L R U : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ1 : ∀ w ∈ L, w ∈ modCent X L → (∃ k : ℕ, w ^ (3 ^ k) = 1) → w = 1)
    (hRX : R ≤ X) (hR : IsPGroup 3 R) (hUR : U ≤ R) (hUL : U ≤ L)
    (hUN : R ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (U : Set G)) (s : Set G)
    (hs : ∀ g ∈ s, g ∈ R) :
    (⨆ (g : G) (_ : g ∈ s), GLBConj g U) ⊓ (⨅ (g : G) (_ : g ∈ s), modCent X (GLBConj g L)) = ⊥ := by
  have h := iSup_inf_iInf_eq_bot hL hZ1 hRX hR hUR hUL hUN s.toFinite.toFinset
    (fun g hg => hs g ((Set.Finite.mem_toFinset _).1 hg))
  simpa only [Set.Finite.mem_toFinset] using h

theorem le_normalizer_conjSup {Q U : Subgroup G} {s : Set G} (hs : ∀ g ∈ s, ∀ q ∈ Q, g * q ∈ s) :
    Q ≤ Subgroup.normalizer ((⨆ (g : G) (_ : g ∈ s), GLBConj g U : Subgroup G) : Set G) := by
  intro q' hq'
  have hle : GLBConj q'⁻¹ (⨆ (g : G) (_ : g ∈ s), GLBConj g U) ≤ ⨆ (g : G) (_ : g ∈ s), GLBConj g U := by
    change (⨆ (g : G) (_ : g ∈ s), GLBConj g U).map (MulAut.conj q'⁻¹⁻¹).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g hg => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    change GLBConj q'⁻¹ (GLBConj g U) ≤ _
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (g * q'⁻¹) (hs g hg _ (Q.inv_mem hq')) le_rfl
  refine Subgroup.mem_normalizer_fintype fun x hx => hle ?_
  rw [mem_gLBConj]
  simpa [mul_assoc] using hx

theorem kc_of_not_normalizes {X L R : Subgroup G} (hL : GLAPComponent 3 X L)
    (hZ1 : ∀ w ∈ L, w ∈ modCent X L → (∃ k : ℕ, w ^ (3 ^ k) = 1) → w = 1)
    (hRX : R ≤ X) (hR : IsPGroup 3 R) (hT1 : R ⊓ L ≠ ⊥)
    (hRN : ¬ R ≤ Subgroup.normalizer (L : Set G)) {A B : Subgroup G} (hA : IsEkIn 3 4 R A)
    (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  have hNR : N ≤ R := inf_le_left
  have hNne : N ≠ R := fun h => hRN (h ▸ inf_le_right)
  obtain ⟨Q, hNQ, hQR, hQi, hQn⟩ := exists_index_three hR hNR hNne
  obtain ⟨t, htR, htQ⟩ : ∃ t ∈ R, t ∉ Q := by
    by_contra h
    push Not at h
    have hQR' : Q = R := le_antisymm hQR h
    rw [hQR', Subgroup.relIndex_self] at hQi
    norm_num at hQi
  have hT₁N : R ⊓ L ≤ N := fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hNT₁ : N ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hn.1)) x)
      ((Subgroup.mem_normalizer_iff.1 hn.2) x)
  obtain ⟨ζ, hζT, hζ1, hζ3, hζc⟩ := exists_central_of_normalized (hR.to_le hNR) hT₁N hNT₁ hT1
  set U : Subgroup G := Subgroup.zpowers ζ with hU
  have hUR : U ≤ R := Subgroup.zpowers_le.2 hζT.1
  have hUL : U ≤ L := Subgroup.zpowers_le.2 hζT.2
  have hUel : IsElemAbelian 3 U := Claims1245.isElemAbelian_zpowers_of_pow_three hζ3
  have hUc : Nat.card U = 3 := by rw [hU, Nat.card_zpowers]; exact orderOf_eq_prime hζ3 hζ1
  have hUN : N ≤ Subgroup.normalizer (U : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : n * ζ ^ i = ζ ^ i * n := (Commute.zpow_right (hζc n hn) i).eq
    rw [hc, mul_inv_cancel_right]
    exact hx
  obtain ⟨hER, hEel, -⟩ := conjProd_props hL hRX hR hUR hUL hUel hUN
  set Bl : Fin 3 → Set G := fun j => {g | (t ^ (j : ℕ))⁻¹ * g ∈ Q} with hBl
  have hBR : ∀ j, ∀ g ∈ Bl j, g ∈ R := by
    intro j g hg
    have e : g = t ^ (j : ℕ) * ((t ^ (j : ℕ))⁻¹ * g) := by group
    rw [e]
    exact R.mul_mem (R.pow_mem htR _) (hQR hg)
  have hBQ : ∀ j, ∀ g ∈ Bl j, ∀ q ∈ Q, g * q ∈ Bl j := by
    intro j g hg q hq
    show (t ^ (j : ℕ))⁻¹ * (g * q) ∈ Q
    rw [← mul_assoc]
    exact Q.mul_mem hg hq
  have htB : ∀ j : Fin 3, t ^ (j : ℕ) ∈ Bl j := by
    intro j
    show (t ^ (j : ℕ))⁻¹ * t ^ (j : ℕ) ∈ Q
    rw [inv_mul_cancel]
    exact Q.one_mem
  have hdist : ∀ i j : Fin 3, i ≠ j → ∀ g ∈ Bl j, ∀ g' ∈ Bl i, GLBConj g L ≠ GLBConj g' L := by
    intro i j hij g hg g' hg' h
    have h1 : GLBConj g'⁻¹ (GLBConj g L) = GLBConj g'⁻¹ (GLBConj g' L) := by rw [h]
    rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h1
    have hmem : g * g'⁻¹ ∈ N :=
      ⟨R.mul_mem (hBR j g hg) (R.inv_mem (hBR i g' hg')), mem_normalizer_iff_gLBConj_eq.2 h1⟩
    have hg0 : (t ^ (j : ℕ))⁻¹ * g ∈ Q := hg
    have hg0' : (t ^ (i : ℕ))⁻¹ * g' ∈ Q := hg'
    have hxQ : (t ^ (j : ℕ))⁻¹ * g * ((t ^ (i : ℕ))⁻¹ * g')⁻¹ ∈ Q :=
      Q.mul_mem hg0 (Q.inv_mem hg0')
    have h2 : t ^ (j : ℕ) * ((t ^ (j : ℕ))⁻¹ * g * ((t ^ (i : ℕ))⁻¹ * g')⁻¹) * (t ^ (i : ℕ))⁻¹ ∈ Q := by
      have e : t ^ (j : ℕ) * ((t ^ (j : ℕ))⁻¹ * g * ((t ^ (i : ℕ))⁻¹ * g')⁻¹) * (t ^ (i : ℕ))⁻¹ =
          g * g'⁻¹ := by group
      rw [e]
      exact hNQ hmem
    have := eq_of_pow_mul_mem hQR hQi hQn htR htQ j.2 i.2 hxQ h2
    exact hij (Fin.ext this.symm)
  have hWE : ∀ j : Fin 3, (⨆ (g : G) (_ : g ∈ Bl j), GLBConj g U) ≤ conjProd R U := fun j =>
    iSup₂_le fun g hg => gLBConj_le_conjProd (hBR j g hg)
  have hW1 : ∀ j : Fin 3, (⨆ (g : G) (_ : g ∈ Bl j), GLBConj g U) ≠ ⊥ := by
    intro j h
    have hle : GLBConj (t ^ (j : ℕ)) U ≤ ⊥ := h ▸ le_iSup₂_of_le (t ^ (j : ℕ)) (htB j) le_rfl
    have hc := Subgroup.card_le_of_le hle
    rw [Lemma1112b.card_glbConj, hUc, Subgroup.card_bot] at hc
    norm_num at hc
  have hMW : ∀ i j : Fin 3, i ≠ j → (⨆ (g : G) (_ : g ∈ Bl j), GLBConj g U) ≤
      ⨅ (g : G) (_ : g ∈ Bl i), modCent X (GLBConj g L) := by
    intro i j hij
    refine iSup₂_le fun g hg => le_iInf₂ fun g' hg' => ?_
    exact (gLBConj_mono g hUL).trans (le_modCent (comp_conj hL (hRX (hBR i g' hg')))
      (comp_conj hL (hRX (hBR j g hg))) (hdist i j hij g hg g' hg'))
  obtain ⟨D, hDE, hDel, hDc, hDQ⟩ := exists_e27_cent hR hQR hER hEel
    (fun j => ⨆ (g : G) (_ : g ∈ Bl j), GLBConj g U)
    (fun j => ⨅ (g : G) (_ : g ∈ Bl j), modCent X (GLBConj g L)) hWE
    (fun j => le_normalizer_conjSup (hBQ j)) hW1
    (fun j => iSup_inf_iInf_eq_bot' hL hZ1 hRX hR hUR hUL hUN (Bl j) (hBR j)) hMW
  exact kc_of_cent hRX ((hDE.trans hER).trans hRX) hDel hDc.ge hDQ hQi.le hA hB

end NonNormalizing

section Normalizing

variable {G : Type} [Group G] [Finite G]

theorem card_center_eq_one {L : Subgroup G} {n : ℕ} (h4 : 4 ≤ n)
    (e : barOf 3 L ≃* alternatingGroup (Fin n)) : Nat.card (Subgroup.center (barOf 3 L)) = 1 := by
  rw [Subgroup.card_eq_one, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : ((e x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1 := by
    refine AltFacts5.eq_one_of_comm_alt h4 fun g hg => ?_
    have hc := Subgroup.mem_center_iff.1 hx (e.symm ⟨g, hg⟩)
    have h2 := congrArg (fun y => ((e y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) hc
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h2
    exact h2.symm
  have h2 : e x = 1 := Subtype.ext h1
  exact (map_eq_one_iff e e.injective).1 h2

theorem centBar_le_top {L R : Subgroup G} : centBar 3 R L ≤ centBar 3 ⊤ L := fun g hg => by
  obtain ⟨-, h, hb⟩ := mem_centBar_iff'.1 hg
  exact mem_centBar_iff'.2 ⟨Subgroup.mem_top g, h, hb⟩

theorem eq_one_of_mem_centBar {L : Subgroup G}
    (hZ0 : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 1) {c : G}
    (hc3 : ∃ k : ℕ, c ^ (3 ^ k) = 1) (hcL : c ∈ L) (hcC : c ∈ centBar 3 ⊤ L) : c = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hc3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
  have hp : IsPGroup 3 (Subgroup.zpowers c) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have h1 := hZ0 _ (Subgroup.zpowers_le.2 hcL) hp (Subgroup.zpowers_le.2 hcC)
  have h2 : Subgroup.zpowers c = ⊥ := (Subgroup.card_le_one_iff_eq_bot _).1 h1
  rw [Subgroup.zpowers_eq_bot] at h2
  exact h2

theorem exists_tau {L R : Subgroup G} {n : ℕ} (h5 : 5 ≤ n) (e : barOf 3 L ≃* alternatingGroup (Fin n))
    (hR : IsPGroup 3 R) (hRN : R ≤ Subgroup.normalizer (L : Set G)) :
    ∃ τ : ↥R →* Equiv.Perm (Fin n), ∀ r : ↥R, τ r = 1 ↔ (r : G) ∈ centBar 3 R L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥R →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr e).toMonoidHom.comp ((barAut 3 L).comp (Subgroup.inclusion hRN)) with hφ
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hR
  have hodd : Odd (Nat.card ↥R) := by rw [ha]; exact Odd.pow (by decide)
  obtain ⟨τ, hτ⟩ := AltFacts5.exists_perm_hom hodd h5 φ fun s => by
    rw [← map_pow, pow_card_eq_one', map_one]
  refine ⟨τ, fun r => ?_⟩
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  rw [mem_centBar_iff']
  constructor
  · intro h
    refine ⟨r.2, hRN r.2, ?_⟩
    have h1 : φ r = 1 := by rw [← hτ r, h, map_one]
    have h2 : (MulAut.congr e) (barAut 3 L (Subgroup.inclusion hRN r)) = 1 := h1
    exact (map_eq_one_iff (MulAut.congr e) (MulAut.congr e).injective).1 h2
  · rintro ⟨-, h, hb⟩
    apply hinj
    rw [hτ r, map_one]
    show (MulAut.congr e) (barAut 3 L (Subgroup.inclusion hRN r)) = 1
    have : Subgroup.inclusion hRN r = ⟨(r : G), h⟩ := rfl
    rw [this, hb, map_one]

theorem card_le_mul_centBar_of_tau {L R A : Subgroup G} {n : ℕ} (τ : ↥R →* Equiv.Perm (Fin n))
    (hτ : ∀ r : ↥R, τ r = 1 ↔ (r : G) ∈ centBar 3 R L) (hAR : A ≤ R) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 ^ (n / 3) * Nat.card (centBar 3 A L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f : ↥A →* Equiv.Perm (Fin n) := τ.comp (Subgroup.inclusion hAR) with hf
  have hker : f.ker.map A.subtype = centBar 3 A L := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hτ (Subgroup.inclusion hAR x)).1 (MonoidHom.mem_ker.1 hx)
      obtain ⟨-, h, hb⟩ := mem_centBar_iff'.1 h1
      exact mem_centBar_iff'.2 ⟨x.2, h, hb⟩
    · intro hg
      obtain ⟨hgA, h, hb⟩ := mem_centBar_iff'.1 hg
      exact ⟨⟨g, hgA⟩, MonoidHom.mem_ker.2 ((hτ _).2 (mem_centBar_iff'.2 ⟨hAR hgA, h, hb⟩)), rfl⟩
  have hkc : Nat.card (centBar 3 A L) = Nat.card f.ker := by
    rw [← hker, Subgroup.card_map_of_injective A.subtype_injective]
  have hel : IsElemAbelian 3 f.range := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      show (u : Equiv.Perm (Fin n)) * v = v * u
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.comm a.2 b.2)
    · obtain ⟨a, rfl⟩ := hy
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a.1 a.2)
      rw [this, map_one]
  have hr : Nat.card f.range ≤ 3 ^ (n / 3) := by
    have := AltInputs.card_le_pow_div hel
    simpa using this
  have hA' : Nat.card A = Nat.card ↥A := rfl
  rw [hA', CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f, hkc, mul_comm]
  exact Nat.mul_le_mul_right _ hr

theorem kc_normalizes_small {X L R : Subgroup G}
    (hZ0 : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 1)
    (hRX : R ≤ X) (hR : IsPGroup 3 R) (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hT1 : R ⊓ L ≠ ⊥)
    (hAut : ∀ A : Subgroup G, A ≤ R → IsElemAbelian 3 A → Nat.card A ≤ 9 * Nat.card (centBar 3 A L))
    {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centBar 3 R L with hC
  have hCR : C ≤ R := inf_le_right
  have hAC : 9 ≤ Nat.card (A ⊓ C : Subgroup G) := by
    obtain ⟨hAR, hAel, hAc⟩ := hA
    have h := hAut A hAR hAel
    have he : centBar 3 A L = A ⊓ C := by
      ext g
      rw [mem_centBar_iff', Subgroup.mem_inf, mem_centBar_iff']
      exact ⟨fun h' => ⟨h'.1, hAR h'.1, h'.2⟩, fun h' => ⟨h'.1, h'.2.2⟩⟩
    rw [he, hAc] at h
    omega
  have hCnc : ¬ IsCyclic C := by
    intro hcyc
    have hACel : IsElemAbelian 3 (A ⊓ C) := isElemAbelian_mono hA.2.1 inf_le_left
    exact not_isCyclic_of_isElemAbelian hACel (by norm_num; exact hAC)
      (isCyclic_of_injective (Subgroup.inclusion (inf_le_right : A ⊓ C ≤ C))
        (Subgroup.inclusion_injective _))
  have hCn := centBar_normal hRN
  obtain ⟨U₁, hU₁C, hU₁, hU₁N⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) R C hR
    hCR hCn hCnc
  have hRT : R ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hr)) x)
      ((Subgroup.mem_normalizer_iff.1 (hRN hr)) x)
  obtain ⟨z, hzT, hz1, hz3, hzc⟩ := exists_central_of_normalized hR inf_le_left hRT hT1
  have hRC : R ≤ Subgroup.normalizer (C : Set G) := fun r hr =>
    Subgroup.mem_normalizer_fintype fun x hx =>
      Subgroup.mem_subgroupOf.1 (hCn.conj_mem ⟨x, hCR hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨r, hr⟩)
  have hCne : C ≠ ⊥ := fun h => hCnc (h ▸ inferInstance)
  obtain ⟨c, hcC, hc1, hc3, hcc⟩ := exists_central_of_normalized hR hCR hRC hCne
  have hzC : z ∉ C := fun h =>
    hz1 (eq_one_of_mem_centBar hZ0 ⟨1, by simpa using hz3⟩ hzT.2 (centBar_le_top h))
  set U₂ : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers z with hU₂def
  have hcz : ∀ e ∈ Subgroup.zpowers c, e * z = z * e := by
    intro e he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (Commute.zpow_left (hzc c (hCR hcC)) i).eq
  have hU₂c : Nat.card U₂ = 9 := by
    rw [hU₂def, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three _ hz3
      (fun h => hzC ((Subgroup.zpowers_le.2 hcC) h)) hcz, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hU₂el : IsElemAbelian 3 U₂ := by
    refine isElemAbelian_sup_of_commute (Claims1245.isElemAbelian_zpowers_of_pow_three hc3)
      (Claims1245.isElemAbelian_zpowers_of_pow_three hz3) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (hcz e he).symm j).eq
  have hU₂ : IsPPlane 3 U₂ := ⟨hU₂el, by rw [hU₂c]; norm_num⟩
  have hU₂R : U₂ ≤ R := sup_le (Subgroup.zpowers_le.2 (hCR hcC)) (Subgroup.zpowers_le.2 hzT.1)
  have hU₂cent : U₂ ≤ Subgroup.centralizer (R : Set G) :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun r hr => hcc r hr))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun r hr => hzc r hr))
  have hU₂N : R ≤ Subgroup.normalizer (U₂ : Set G) := fun r hr =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      rw [(Subgroup.mem_centralizer_iff.1 (hU₂cent hx) r hr), mul_inv_cancel_right]
      exact hx
  have hne : U₁ ≠ U₂ := by
    intro h
    exact hzC (hU₁C (h ▸ (le_sup_right : Subgroup.zpowers z ≤ U₂) (Subgroup.mem_zpowers z)))
  have hcomm : U₁ ≤ Subgroup.centralizer (U₂ : Set G) :=
    cent_symm (hU₂cent.trans (Subgroup.centralizer_le (hU₁C.trans hCR)))
  exact kc_of_plane_pair hRX hR hU₁ hU₂ (hU₁C.trans hCR) hU₂R hU₁N hU₂N hne hcomm hA hB

end Normalizing

section Blocks

variable {α : Type} [Fintype α] [DecidableEq α]

open Equiv

theorem pcyc_conj {c : Perm α} (hc : AltInputs2.PCyc 3 c) (g : Perm α) :
    AltInputs2.PCyc 3 (g * c * g⁻¹) :=
  ⟨hc.1.conj, by rw [Perm.support_conj, Finset.card_map]; exact hc.2⟩

theorem pcyc_ne_one {c : Perm α} (hc : AltInputs2.PCyc 3 c) : c ≠ 1 := by
  rintro rfl
  have := hc.2
  rw [Perm.support_one, Finset.card_empty] at this
  norm_num at this

theorem eq_one_of_fix {s : Set α} {x : Perm α} (h1 : x ∈ fixingSubgroup (Perm α) s)
    (h2 : x ∈ fixingSubgroup (Perm α) sᶜ) : x = 1 := by
  refine Equiv.ext fun y => ?_
  by_cases hy : y ∈ s
  · exact (mem_fixingSubgroup_iff _).1 h1 y hy
  · exact (mem_fixingSubgroup_iff _).1 h2 y hy

theorem mem_fix_compl_support (x : Perm α) :
    x ∈ fixingSubgroup (Perm α) ((x.support : Set α)ᶜ) := by
  rw [mem_fixingSubgroup_iff]
  intro y hy
  rw [Perm.smul_def]
  exact Perm.notMem_support.1 (by simpa using hy)

theorem mem_normalizer_of_conj_mem {c h : Perm α} (hc : h * c * h⁻¹ ∈ Subgroup.zpowers c) :
    h ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (Perm α)) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hc i

theorem exists_e27_cent_perm {T E : Subgroup (Perm α)} (hT : IsPGroup 3 T) (hET : E ≤ T)
    (hEn : ∀ t ∈ T, ∀ e ∈ E, t * e * t⁻¹ ∈ E) (hE : IsElemAbelian 3 E) (c : Fin 3 → Perm α)
    (hcE : ∀ i, c i ∈ E) (hc : ∀ i, AltInputs2.PCyc 3 (c i))
    (hcd : ∀ i j, i ≠ j → Perm.Disjoint (c i) (c j)) :
    ∃ Q : Subgroup (Perm α), Q ≤ T ∧ Q.relIndex T ≤ 3 ∧ ∃ D : Subgroup (Perm α), D ≤ E ∧
      IsElemAbelian 3 D ∧ Nat.card D = 27 ∧ D ≤ Subgroup.centralizer (Q : Set (Perm α)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : ∀ g ∈ T, ∃ k : ℕ, g ^ 3 ^ k = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hT ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  by_cases h1 : ∀ i, T ≤ Subgroup.normalizer (Subgroup.zpowers (c i) : Set (Perm α))
  ·
    refine ⟨T, le_rfl, by rw [Subgroup.relIndex_self]; norm_num, ?_⟩
    refine exists_e27_cent hT le_rfl hET hE (fun i => Subgroup.zpowers (c i))
      (fun i => fixingSubgroup (Perm α) ((c i).support : Set α))
      (fun i => Subgroup.zpowers_le.2 (hcE i)) h1 ?_ ?_ ?_
    · intro i h
      exact pcyc_ne_one (hc i) ((Subgroup.zpowers_eq_bot).1 h)
    · intro i
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      exact eq_one_of_fix hx2 ((Subgroup.zpowers_le.2 (mem_fix_compl_support (c i))) hx1)
    · intro i j hij
      refine Subgroup.zpowers_le.2 ((mem_fixingSubgroup_iff _).2 fun y hy => ?_)
      rw [Perm.smul_def]
      rcases hcd i j hij y with h | h
      · exact absurd h (Perm.mem_support.1 (by simpa using hy))
      · exact h
  ·
    push Not at h1
    obtain ⟨i₀, hi₀⟩ := h1
    set c₀ := c i₀ with hc₀
    set N := T ⊓ Subgroup.normalizer (Subgroup.zpowers c₀ : Set (Perm α)) with hN
    have hNne : N ≠ T := fun h => hi₀ (h ▸ inf_le_right)
    obtain ⟨Q, hNQ, hQT, hQi, hQn⟩ := exists_index_three hT inf_le_left hNne
    obtain ⟨t, htT, htQ⟩ : ∃ t ∈ T, t ∉ Q := by
      by_contra h
      push Not at h
      have hQT' : Q = T := le_antisymm hQT h
      rw [hQT', Subgroup.relIndex_self] at hQi
      norm_num at hQi
    set d : Fin 3 → Perm α := fun j => t ^ (j : ℕ) * c₀ * (t ^ (j : ℕ))⁻¹ with hd
    have hdE : ∀ j, d j ∈ E := fun j => hEn _ (T.pow_mem htT _) c₀ (hcE i₀)
    have hdc : ∀ j, AltInputs2.PCyc 3 (d j) := fun j => pcyc_conj (hc i₀) _
    have hqd : ∀ j, ∀ q ∈ Q, q * d j * q⁻¹ ∈ E := fun j q hq => hEn q (hQT hq) _ (hdE j)
    set S : Fin 3 → Set (Perm α) := fun j => {y | ∃ q ∈ Q, y = q * d j * q⁻¹} with hS
    set Ω : Fin 3 → Set α := fun j => {x | ∃ q ∈ Q, x ∈ (q * d j * q⁻¹).support} with hΩ
    refine ⟨Q, hQT, hQi.le, exists_e27_cent hT hQT hET hE (fun j => Subgroup.closure (S j))
      (fun j => fixingSubgroup (Perm α) (Ω j)) ?_ ?_ ?_ ?_ ?_⟩
    ·
      intro j
      rw [Subgroup.closure_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hqd j q hq
    ·
      intro j q' hq'
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hle : (Subgroup.closure (S j)).map (MulAut.conj q').toMonoidHom ≤ Subgroup.closure (S j) := by
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨y, ⟨q, hq, rfl⟩, rfl⟩
        exact Subgroup.subset_closure ⟨q' * q, Q.mul_mem hq' hq, by simp [MulAut.conj_apply, mul_assoc]⟩
      exact hle ⟨x, hx, rfl⟩
    ·
      intro j h
      have hmem : d j ∈ Subgroup.closure (S j) :=
        Subgroup.subset_closure ⟨1, Q.one_mem, by simp⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact pcyc_ne_one (hdc j) hmem
    ·
      intro j
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      have hle : Subgroup.closure (S j) ≤ fixingSubgroup (Perm α) (Ω j)ᶜ := by
        rw [Subgroup.closure_le]
        rintro _ ⟨q, hq, rfl⟩
        refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
        rw [Perm.smul_def]
        by_contra hne
        exact hy ⟨q, hq, Perm.mem_support.2 hne⟩
      exact eq_one_of_fix hx2 (hle hx1)
    ·
      intro i j hij
      rw [Subgroup.closure_le]
      rintro _ ⟨q, hq, rfl⟩
      refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
      rw [Perm.smul_def]
      by_contra hne
      obtain ⟨q', hq', hyq'⟩ := hy
      have hzp := AltInputs2.pcycle_mem_zpowers hTp (pcyc_conj (hdc i) q') (pcyc_conj (hdc j) q)
        (hET (hqd i q' hq')) (hET (hqd j q hq)) hyq' (Perm.mem_support.2 hne)
      set a := q' * t ^ (i : ℕ) with ha
      set b := q * t ^ (j : ℕ) with hb
      have hcb : b * c₀ * b⁻¹ ∈ Subgroup.zpowers (a * c₀ * a⁻¹) := by
        have e : b * c₀ * b⁻¹ = q * d j * q⁻¹ := by rw [hb, hd]; group
        have e' : a * c₀ * a⁻¹ = q' * d i * q'⁻¹ := by rw [ha, hd]; group
        rw [e, e']
        exact hzp
      have hh : (a⁻¹ * b) * c₀ * (a⁻¹ * b)⁻¹ ∈ Subgroup.zpowers c₀ := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcb
        rw [conj_zpow] at hk
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        calc c₀ ^ k = a⁻¹ * (a * c₀ ^ k * a⁻¹) * a := by group
          _ = a⁻¹ * (b * c₀ * b⁻¹) * a := by rw [hk]
          _ = (a⁻¹ * b) * c₀ * (a⁻¹ * b)⁻¹ := by group
      have hhT : a⁻¹ * b ∈ T := T.mul_mem (T.inv_mem (T.mul_mem (hQT hq') (T.pow_mem htT _)))
        (T.mul_mem (hQT hq) (T.pow_mem htT _))
      have hhQ : a⁻¹ * b ∈ Q := hNQ ⟨hhT, mem_normalizer_of_conj_mem hh⟩
      have h2 : t ^ (j : ℕ) * 1 * (t ^ (i : ℕ))⁻¹ ∈ Q := by
        have h3 : t ^ (i : ℕ) * (a⁻¹ * b) * (t ^ (i : ℕ))⁻¹ ∈ Q := hQn _ (T.pow_mem htT _) _ hhQ
        have e : t ^ (j : ℕ) * 1 * (t ^ (i : ℕ))⁻¹ =
            (q'⁻¹ * q)⁻¹ * (t ^ (i : ℕ) * (a⁻¹ * b) * (t ^ (i : ℕ))⁻¹) := by rw [ha, hb]; group
        rw [e]
        exact Q.mul_mem (Q.inv_mem (Q.mul_mem (Q.inv_mem hq') hq)) h3
      have := eq_of_pow_mul_mem hQT hQi hQn htT htQ j.2 i.2 Q.one_mem h2
      exact hij (Fin.ext this.symm)

end Blocks

section NormalizingLarge

variable {G : Type} [Group G] [Finite G]

theorem kc_normalizes_large {X L R : Subgroup G} {n : ℕ} (h9 : 9 ≤ n)
    (e : barOf 3 L ≃* alternatingGroup (Fin n))
    (hZ0 : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 1)
    (hRX : R ≤ X) (hR : IsPGroup 3 R) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hT : IsSylowIn 3 L (R ⊓ L)) {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) :
    IsKConnectedIn 3 3 X A B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ⟩ := exists_tau (by omega) e hR hRN
  obtain ⟨EL, ⟨hELT, hELel, hELr⟩, huniq⟩ :=
    Lemma118T.Input10_5K_holds G 3 n Nat.prime_three (by norm_num) L ⟨e⟩ (R ⊓ L) hT
  have hELc : Nat.card EL = 3 ^ (n / 3) := by rw [← hELr]; exact Lemma124.card_eq_pow_pRank hELel
  have hELR : EL ≤ R := hELT.trans inf_le_left
  have hRT : R ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hr)) x)
      ((Subgroup.mem_normalizer_iff.1 (hRN hr)) x)
  have hREL : ∀ r ∈ R, ∀ x ∈ EL, r * x * r⁻¹ ∈ EL := by
    intro r hr x hx
    have h1 : GLBConj r⁻¹ EL = EL := by
      refine huniq _ ⟨?_, Lemma1112b.isElemAbelian_glbConj hELel _, ?_⟩
      · calc GLBConj r⁻¹ EL ≤ GLBConj r⁻¹ (R ⊓ L) := gLBConj_mono _ hELT
          _ = R ⊓ L := gLBConj_eq_of_mem_normalizer (hRT (R.inv_mem hr))
      · exact Lemma118T.pRank_eq_of_isElemAbelian_card (Lemma1112b.isElemAbelian_glbConj hELel _)
          (by rw [Lemma1112b.card_glbConj, hELc])
    have h2 : r * x * r⁻¹ ∈ GLBConj r⁻¹ EL := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hx
    rwa [h1] at h2
  have h3el : ∀ y ∈ R, ∃ k : ℕ, y ^ (3 ^ k) = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hR ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hinj : ∀ x : ↥R, (x : G) ∈ EL → τ x = 1 → x = 1 := by
    intro x hxE hx1
    exact Subtype.ext (eq_one_of_mem_centBar hZ0 (h3el x x.2) (hELT hxE).2
      (centBar_le_top ((hτ x).1 hx1)))
  set EL' : Subgroup ↥R := EL.subgroupOf R with hEL'
  set Ebar : Subgroup (Equiv.Perm (Fin n)) := EL'.map τ with hEbar
  have hEbarc : Nat.card Ebar = 3 ^ (n / 3) := by
    rw [hEbar, AltInputs2.card_map_of_injOn τ EL' (fun x hx h1 => hinj x (Subgroup.mem_subgroupOf.1 hx) h1),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hELR).toEquiv, hELc]
  have hEbarel : IsElemAbelian 3 Ebar :=
    AltInputs2.isElemAbelian_map_hom τ (AltInputs.isElemAbelian_subgroupOf hELel)
  have hTbar : IsPGroup 3 τ.range := by
    rintro ⟨_, r, rfl⟩
    obtain ⟨k, hk⟩ := hR r
    exact ⟨k, Subtype.ext (by simp [← map_pow, hk])⟩
  have hEbarT : Ebar ≤ τ.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hEbarn : ∀ t ∈ τ.range, ∀ y ∈ Ebar, t * y * t⁻¹ ∈ Ebar := by
    rintro _ ⟨r, rfl⟩ _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ EL := Subgroup.mem_subgroupOf.1 hx
    exact ⟨r * x * r⁻¹, Subgroup.mem_subgroupOf.2 (by simpa using hREL r r.2 x hx'),
      by simp [map_mul, map_inv]⟩
  obtain ⟨k, x, hk, hxE, hxc, hxd⟩ := AltInputs2.exists_pcyc (p := 3) (le_refl 3) hEbarel
    (by rw [hEbarc, Fintype.card_fin])
  have hk3 : 3 ≤ k := by
    rw [hk, Fintype.card_fin]
    omega
  obtain ⟨Qb, hQbT, hQbi, Db, hDbE, -, hDbc, hDbQ⟩ := exists_e27_cent_perm hTbar hEbarT hEbarn hEbarel
    (fun i => x (Fin.castLE hk3 i)) (fun i => hxE _) (fun i => hxc _)
    (fun i j hij => hxd _ _ (fun h => hij (Fin.castLE_injective hk3 h)))
  set Q : Subgroup G := (Qb.comap τ).map R.subtype with hQ
  have hQi : Q.relIndex R ≤ 3 := by
    have e1 : Q.relIndex R = (Qb.comap τ).index := by
      show (Q.comap R.subtype).index = _
      rw [hQ, Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    rw [e1, ← Subgroup.relIndex_top_right, Subgroup.relIndex_comap, ← MonoidHom.range_eq_map]
    exact hQbi
  set D : Subgroup G := ((Db.comap τ) ⊓ EL').map R.subtype with hD
  have hDEL : D ≤ EL := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hy.2
  have hDel : IsElemAbelian 3 D := isElemAbelian_mono hELel hDEL
  have hDc : 27 ≤ Nat.card D := by
    have h1 : Nat.card D = Nat.card ((Db.comap τ) ⊓ EL' : Subgroup ↥R) :=
      Subgroup.card_map_of_injective R.subtype_injective
    have h2 : ((Db.comap τ) ⊓ EL').map τ = Db := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact hy.1
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := hDbE hz
        exact ⟨y, ⟨hz, hy⟩, rfl⟩
    have h3 : Nat.card (((Db.comap τ) ⊓ EL').map τ) = Nat.card ((Db.comap τ) ⊓ EL' : Subgroup ↥R) :=
      AltInputs2.card_map_of_injOn τ _ (fun y hy h1 => hinj y (Subgroup.mem_subgroupOf.1 hy.2) h1)
    rw [h1, ← h3, h2, hDbc]
  have hDQ : D ≤ Subgroup.centralizer (Q : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have hcomm : τ q * τ d = τ d * τ q := Subgroup.mem_centralizer_iff.1 (hDbQ hd.1) (τ q) hq
    have hk1 : τ (q * d * q⁻¹ * d⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hc1 := (hτ _).1 hk1
    have hdT : (d : G) ∈ R ⊓ L := hELT (Subgroup.mem_subgroupOf.1 hd.2)
    have hcL : (q : G) * d * (q : G)⁻¹ * (d : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hRN q.2) _).1 hdT.2) (L.inv_mem hdT.2)
    have hc3 := h3el _ (q * d * q⁻¹ * d⁻¹).2
    have h4 := eq_one_of_mem_centBar hZ0 (by simpa using hc3) hcL (centBar_le_top (by simpa using hc1))
    show (q : G) * d = d * q
    calc (q : G) * d = ((q : G) * d * (q : G)⁻¹ * (d : G)⁻¹) * (d * q) := by group
      _ = d * q := by rw [h4, one_mul]
  exact kc_of_cent hRX ((hDEL.trans hELR).trans hRX) hDel hDc hDQ hQi hA hB

end NormalizingLarge

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem sylow_ne_bot_of_alt {L T : Subgroup G} {n : ℕ} (h3 : 3 ≤ n)
    (e : barOf 3 L ≃* alternatingGroup (Fin n)) (hT : IsSylowIn 3 L T) : T ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hT0
  obtain ⟨P', hP'⟩ := Claims1245.exists_sylow_of_isSylowIn hT
  have hidx := P'.not_dvd_index
  rw [hP', hT0, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
  apply hidx
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 : 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h2
    have h3' : 3 ∣ 2 * Nat.card (alternatingGroup (Fin n)) := h2 ▸ Nat.dvd_factorial (by norm_num) h3
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3'
  have h4 : Nat.card (barOf 3 L) = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
  rw [← h4] at h1
  exact h1.trans (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)).symm)

theorem kc_caseA {X L : Subgroup G} (hL : GLAPComponent 3 X L) {n : ℕ}
    (hAlt : IsAltType n (barOf 3 L)) {R : Subgroup G} (hR : IsSylowIn 3 X R) {U V : Subgroup G}
    (hU : IsEkIn 3 4 R U) (hV : IsEkIn 3 4 R V) : IsKConnectedIn 3 3 X U V := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hAlt
  have h5 : 5 ≤ n := Input236gt.five_le_of_isQuasisimple
    (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent
      Nat.prime_three hL) e
  have hZ0 : ∀ U : Subgroup G, U ≤ L → IsPGroup 3 U → U ≤ centBar 3 ⊤ L → Nat.card U ≤ 1 :=
    fun U hUL hU hUC =>
      (card_le_center_of_le_centBar hUL hU hUC).trans (card_center_eq_one (by omega) e).le
  have hT : IsSylowIn 3 L (R ⊓ L) := Claims1245.isSylowIn_inf_of_isSubnormal hR hL.2.1
  have hT1 : R ⊓ L ≠ ⊥ := sylow_ne_bot_of_alt (by omega) e hT
  by_cases hRN : R ≤ Subgroup.normalizer (L : Set G)
  · by_cases h9 : 9 ≤ n
    · exact kc_normalizes_large h9 e hZ0 hR.1 hR.2.1 hRN hT hU hV
    · obtain ⟨τ, hτ⟩ := exists_tau h5 e hR.2.1 hRN
      refine kc_normalizes_small hZ0 hR.1 hR.2.1 hRN hT1 (fun A hAR hA => ?_) hU hV
      refine (card_le_mul_centBar_of_tau τ hτ hAR hA).trans (Nat.mul_le_mul_right _ ?_)
      calc 3 ^ (n / 3) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 := by norm_num
  · have hZ1 : ∀ w ∈ L, w ∈ modCent X L → (∃ k : ℕ, w ^ (3 ^ k) = 1) → w = 1 :=
      fun w hwL hwM hw3 => eq_one_of_mem_centBar hZ0 hw3 hwL (mem_centBar_of_modCent hL hwL hwM)
    exact kc_of_not_normalizes hL hZ1 hR.1 hR.2.1 hT1 hRN hU hV

theorem input31_10ab_holds : Claims1245b.Input31_10ab := by
  intro G _ _ X L hL hcase R hR U V hU hV
  rcases hcase with ⟨n, hn⟩ | ⟨h81, h2, hAut2⟩
  · exact kc_caseA hL hn hR hU hV
  · exact kc_caseB hL h81 h2 hAut2 hR hU hV

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs3110
