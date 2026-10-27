module

public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8

section Local

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_orderFour_acting_by_sign (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {L : Subgroup G}
    (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : ∀ q ∈ P, conjSub q L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧ ∀ q ∈ P, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
  obtain ⟨R, hRL, hRfix⟩ := T3.exists_sylow_normalized hP
    (fun q hq => mem_normalizer_iff_conjSub_eq.mpr (hPN q hq))
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hL hRL)
  have hbR : b ∈ R := T3.mem_of_isPGroup hb hRL.1 hRL.2.1 (by omega)
  have hb' : IsUniqueInvolution R b := uniqueInvolution_restrict hb hRL.1 hbR
  have hRn : P ≤ Subgroup.normalizer (R : Set G) := fun q hq =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix q hq)
  have hPR : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hRL.2.1 hRn
  have hTn : ∀ q ∈ P ⊔ R, conjSub q R = R := fun q hq =>
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hRn Subgroup.le_normalizer : P ⊔ R ≤ _) hq)
  obtain ⟨A, hAR, hAc, hA4, hAP⟩ :=
    exists_invariant_cyclic_order_four hPR (le_sup_right : R ≤ P ⊔ R) hTn hb' (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  have hxo : orderOf (g : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hA4]
  have hgen : ∀ y ∈ A, y ∈ Subgroup.zpowers (g : G) := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  exact ⟨g, hRL.1 (hAR g.2), hxo, fun q hq =>
    conj_eq_or_inv_of_cyclic_four hgen g.2 hxo (hAP q ((le_sup_left : P ≤ P ⊔ R) hq))⟩

theorem exists_orderFour_centralizes_sq (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {L : Subgroup G}
    (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {q : G}
    (hq : IsPGroup 2 (Subgroup.zpowers q)) (hqL : conjSub q L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * (q * q) = (q * q) * x := by
  have hqN : Subgroup.zpowers q ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hqL)
  obtain ⟨x, hxL, hxo, hx⟩ := exists_orderFour_acting_by_sign hp hΩ hL hb hq
    (fun w hw => mem_normalizer_iff_conjSub_eq.mp (hqN hw))
  refine ⟨x, hxL, hxo, ?_⟩
  rcases hx q (Subgroup.mem_zpowers q) with h | h
  · have h1 : q * x = x * q := by
      calc q * x = (q * x * q⁻¹) * q := by group
        _ = x * q := by rw [h]
    calc x * (q * q) = (x * q) * q := by group
      _ = (q * x) * q := by rw [h1]
      _ = q * (x * q) := by group
      _ = q * (q * x) := by rw [h1]
      _ = (q * q) * x := by group
  · have h1 : q * x = x⁻¹ * q := by
      calc q * x = (q * x * q⁻¹) * q := by group
        _ = x⁻¹ * q := by rw [h]
    have h2 : q * x⁻¹ = x * q := by
      calc q * x⁻¹ = (q * x * q⁻¹)⁻¹ * q := by group
        _ = x * q := by rw [h, inv_inv]
    calc x * (q * q) = (x * q) * q := by group
      _ = (q * x⁻¹) * q := by rw [h2]
      _ = q * (x⁻¹ * q) := by group
      _ = q * (q * x) := by rw [h1]
      _ = (q * q) * x := by group

theorem exists_orderFour_centralizes_one_of_three (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {L : Subgroup G} (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {S₀ : Subgroup G}
    (hS₀ : IsPGroup 2 S₀) {d u : G} (hd : d ∈ S₀) (hu : u ∈ S₀) (hdL : conjSub d L = L)
    (huL : conjSub u L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧
      (x * d = d * x ∨ x * u = u * x ∨ x * (d * u) = (d * u) * x) := by
  have hcl : Subgroup.closure {d, u} ≤ S₀ := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hd
    · exact hu
  have hclN : Subgroup.closure {d, u} ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact mem_normalizer_iff_conjSub_eq.mpr hdL
    · exact mem_normalizer_iff_conjSub_eq.mpr huL
  obtain ⟨x, hxL, hxo, hx⟩ := exists_orderFour_acting_by_sign hp hΩ hL hb (hS₀.to_le hcl)
    (fun q hq => mem_normalizer_iff_conjSub_eq.mp (hclN hq))
  refine ⟨x, hxL, hxo, ?_⟩
  have hdm : d ∈ Subgroup.closure {d, u} := Subgroup.subset_closure (by simp)
  have hum : u ∈ Subgroup.closure {d, u} := Subgroup.subset_closure (by simp)
  have hcomm : ∀ w : G, w * x * w⁻¹ = x → x * w = w * x := fun w h => by
    calc x * w = (w * x * w⁻¹) * w := by rw [h]
      _ = w * x := by group
  rcases hx d hdm with h | h
  · exact Or.inl (hcomm d h)
  rcases hx u hum with h' | h'
  · exact Or.inr (Or.inl (hcomm u h'))
  · refine Or.inr (Or.inr (hcomm (d * u) ?_))
    calc d * u * x * (d * u)⁻¹ = d * (u * x * u⁻¹) * d⁻¹ := by group
      _ = d * x⁻¹ * d⁻¹ := by rw [h']
      _ = (d * x * d⁻¹)⁻¹ := by group
      _ = x := by rw [h, inv_inv]

theorem exists_orderFour_centralizes_mul_conj (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {M P : Subgroup G} {S : Sylow 2 G} (hM : M ∈ Ω) (hP : P ∈ RSet Ω)
    (hPM : P ≤ M) (hPS : P ≤ (S : Subgroup G)) {m : G} (hm : IsUniqueInvolution M m) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbP : conjSub b P ≠ P) {L : Subgroup G} (hL : L ∈ Ω)
    (hb : IsUniqueInvolution L b)
    (hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * (m * (b * m * b⁻¹)) = (m * (b * m * b⁻¹)) * x := by
  have hPsyl : IsSylow2In P M := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hM hP hPM
  have h8 : 8 ≤ Nat.card P := hΩ.eight_le_of_mem_RSet hp hP
  obtain ⟨r, hrP, hro⟩ := exists_orderOf_four_of_four_le hm hPM hPsyl.2.1 (by omega)
  have hPb : conjSub b P ∈ RSet Ω := RSet.conj hΩ.conjInvariant hP b
  have hPbS : conjSub b P ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := b) hPS
    rwa [conjSub_eq_self_of_mem hbS] at this
  have hcomm : Commutes P (conjSub b P) :=
    l6_7_proved p f hp hq G Ω hΩ S P hP _ hPb hPS hPbS (Ne.symm hbP)
  have hr4 : (r * r) * (r * r) = 1 := by
    have h4 : r ^ 4 = (r * r) * (r * r) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← h4, ← hro]
    exact pow_orderOf_eq_one r
  have hrr : r * r = m := by
    rcases hm.unique _ (M.mul_mem (hPM hrP) (hPM hrP)) hr4 with h | h
    · exfalso
      have h2 : r ^ 2 = 1 := by rw [pow_two]; exact h
      have h4 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hro] at h4
      omega
    · exact h
  have hbb : b * b = 1 := hb.sq
  have hbb' : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hbb, inv_one]
  obtain ⟨r', hr'⟩ : ∃ r', r' = b * r * b⁻¹ := ⟨_, rfl⟩
  have hr'mem : r' ∈ conjSub b P := hr' ▸ conj_mem_conjSub hrP
  have hrr' : r * r' = r' * r := hcomm r hrP r' hr'mem
  have hbr' : b * r' * b⁻¹ = r := by
    rw [hr']
    calc b * (b * r * b⁻¹) * b⁻¹ = (b * b) * r * (b⁻¹ * b⁻¹) := by group
      _ = r := by rw [hbb, hbb']; group
  have hbq : b * (r * r') = (r * r') * b := by
    calc b * (r * r') = (b * r * b⁻¹) * (b * r' * b⁻¹) * b := by group
      _ = r' * r * b := by rw [← hr', hbr']
      _ = (r * r') * b := by rw [hrr']
  have hqL : conjSub (r * r') L = L := by
    refine mem_normalizer_iff_conjSub_eq.mp (hCb ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hbq.symm
  have hqS : r * r' ∈ (S : Subgroup G) := S.mul_mem (hPS hrP) (hPbS hr'mem)
  have hq2 : IsPGroup 2 (Subgroup.zpowers (r * r')) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hqS)
  obtain ⟨x, hxL, hxo, hx⟩ := exists_orderFour_centralizes_sq hp hΩ hL hb hq2 hqL
  have hsq : (r * r') * (r * r') = m * (b * m * b⁻¹) := by
    have h1 : r' * r' = b * m * b⁻¹ := by
      calc r' * r' = (b * r * b⁻¹) * (b * r * b⁻¹) := by rw [← hr']
        _ = b * (r * r) * b⁻¹ := by group
        _ = b * m * b⁻¹ := by rw [hrr]
    calc (r * r') * (r * r') = r * (r' * r) * r' := by group
      _ = r * (r * r') * r' := by rw [← hrr']
      _ = (r * r) * (r' * r') := by group
      _ = m * (b * m * b⁻¹) := by rw [hrr, h1]
  exact ⟨x, hxL, hxo, hsq ▸ hx⟩

end Local

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_dComp_of_four_le_card (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) {L : Subgroup G} (hL : L ∈ Ω)
    (hLS : 4 ≤ Nat.card ↥(L ⊓ (S : Subgroup G))) : L ∈ dComp Ω K := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂_of_le V hV le_rfl).trans hWS
  obtain ⟨S', hS'η, hS'inv⟩ := id hη
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp hR
  have hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (h8.trans (Subgroup.card_le_of_le (le_inf hRK hRS)))
  have hUK := l6_11_proved p f hp hq G Ω hΩ S η hη hηS K hK hKS
  have hUL := l6_11_proved p f hp hq G Ω hΩ S η hη hηS L hL (by omega)
  have hab := ((l6_9_proved p f hp hq G Ω hΩ S').2 η hS'η hS'inv).1
  have hUSet : ∀ U ∈ η, U ∈ USet Ω := fun U hU => (hS'η.1 hU).1
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  have hUKord : 4 ≤ Nat.card ↥(K ⊓ ⨆ V ∈ η, V) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp (hUSet _ hUK)
    exact h4
  have hUK2 : IsPGroup 2 ↥(K ⊓ ⨆ V ∈ η, V) := S.isPGroup'.to_le (inf_le_right.trans hWS)
  have hzU : z ∈ K ⊓ ⨆ V ∈ η, V := T3.mem_of_isPGroup hz inf_le_left hUK2 (by omega)
  have hUN : (L ⊓ ⨆ V ∈ η, V) ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    refine centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hnt hz ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hab y hy.2 z hzU.2
  have hstar : L ∈ omegaStarNbr Ω K :=
    ⟨hL, hLK, L ⊓ ⨆ V ∈ η, V, hUSet _ hUL, inf_le_left, hUN⟩
  rw [hcomp]
  exact Relation.ReflTransGen.single ⟨hL, Or.inl hstar⟩

theorem exists_conj_mem_dComp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) (hSH : (S : Subgroup G) ≤ H274 Ω K z) {L : Subgroup G}
    (hL : L ∈ Ω) {x : G} (hxL : x ∈ L) (hxo : orderOf x = 4) (hxH : x ∈ H274 Ω K z) :
    ∃ y ∈ H274 Ω K z, conjSub y L ∈ dComp Ω K := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxo]; norm_num)
  obtain ⟨y, hyH, hyS⟩ := exists_conj_into_sylow S hSH hxH hx2
  refine ⟨y, hyH, mem_dComp_of_four_le_card hp hq hΩ hcomp hK hnt hz hR hRK hRS hW hWS
    (hΩ.conjInvariant y L hL) ?_⟩
  have hle : Subgroup.zpowers (y * x * y⁻¹) ≤ conjSub y L ⊓ (S : Subgroup G) :=
    le_inf (Subgroup.zpowers_le.mpr (conj_mem_conjSub hxL)) (Subgroup.zpowers_le.mpr hyS)
  have hord : orderOf (y * x * y⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) x
    rw [MulAut.conj_apply, hxo] at this
    exact this
  have := Subgroup.card_le_of_le hle
  rwa [Nat.card_zpowers, hord] at this

theorem mem_H274_of_conj_mem_sylow {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g ∈ H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have htrans := hs.stand.trans
  have hz := hs.hz
  have ht := hs.ht
  have hJ := hs.hJ
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hJ.1
  have hJc : J ∈ dComp Ω K := mem_dComp_of_mem_omegaNbr hJ
  have hntJ : ∀ J' ∈ twinSet Ω J, J' = J :=
    noTwins_of_mem hΩ.conjInvariant htrans hs.noTwins hJΩ
  have hSH : (S : Subgroup G) ≤ H274 Ω K z :=
    (sylow_le_sigmaNorm hp hq hΩ hK hRΩ hRK hRS hz).trans (sigmaNorm_le_H274 K z)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hz).trans
      ((normalizer_le_sigmaNorm hΩ.conjInvariant hK).trans (sigmaNorm_le_H274 K z))
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ hntJ ht).trans
      ((normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJc).trans (sigmaNorm_le_H274 K z))
  have hCzt : Subgroup.centralizer ({z * t} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hJ ht
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hbdef] at hg
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjSub g⁻¹ K := ⟨_, rfl⟩
  have hLΩ : L ∈ Ω := hLdef ▸ hΩ.conjInvariant g⁻¹ K hK
  have hb : IsUniqueInvolution L b := by
    have := hz.conj g⁻¹
    rwa [inv_inv, ← hbdef, ← hLdef] at this
  have hntL : ∀ L' ∈ twinSet Ω L, L' = L :=
    noTwins_of_mem hΩ.conjInvariant htrans hs.noTwins hLΩ
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hLΩ hntL hb
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have hzR : z ∈ R := T3.mem_of_isPGroup hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hRΩ; omega)
  have htT : t ∈ T := T3.mem_of_isPGroup ht hTJ hTsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hTΩ; omega)
  have key : ∃ x ∈ L, orderOf x = 4 ∧ x ∈ H274 Ω K z := by
    by_cases hRb : conjSub b R = R
    swap
    · have hKb : conjSub b K ∈ omegaNbr Ω K :=
        conjSub_mem_omegaNbr hp hq hΩ hK hRΩ hRK hRS hz hg hRb
      obtain ⟨x, hxL, hxo, hxc⟩ := exists_orderFour_centralizes_mul_conj hp hq hΩ hK hRΩ hRK hRS
        hz hg hRb hLΩ hb hCb
      exact ⟨x, hxL, hxo, centralizer_mul_le_H274 hKb (hz.conj b)
        (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    by_cases hTb : conjSub b T = T
    swap
    · have hJb : conjSub b J ∈ omegaNbr Ω J :=
        conjSub_mem_omegaNbr hp hq hΩ hJΩ hTΩ hTJ hTS ht hg hTb
      obtain ⟨x, hxL, hxo, hxc⟩ := exists_orderFour_centralizes_mul_conj hp hq hΩ hJΩ hTΩ hTJ hTS
        ht hg hTb hLΩ hb hCb
      exact ⟨x, hxL, hxo, centralizer_mul_le_H274_of_mem_dComp hΩ.conjInvariant hK htrans hJc hz
        ht hJb (ht.conj b) (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    have hKb : conjSub b K = K := conjSub_eq_of_conjSub_eq hp hΩ hK hRΩ hRK hRb
    have hJb : conjSub b J = J := conjSub_eq_of_conjSub_eq hp hΩ hJΩ hTΩ hTJ hTb
    have hbz : b * z * b⁻¹ = z := hz.conj_eq hKb
    have hbt : b * t * b⁻¹ = t := ht.conj_eq hJb
    have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * b = (b * z * b⁻¹) * b := by rw [hbz]
        _ = b * z := by group
    have htb : t ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * b = (b * t * b⁻¹) * b := by rw [hbt]
        _ = b * t := by group
    obtain ⟨x, hxL, hxo, hxc⟩ := exists_orderFour_centralizes_one_of_three hp hΩ hLΩ hb
      S.isPGroup' (hRS hzR) (hTS htT) (mem_normalizer_iff_conjSub_eq.mp (hCb hzb))
      (mem_normalizer_iff_conjSub_eq.mp (hCb htb))
    refine ⟨x, hxL, hxo, ?_⟩
    rcases hxc with h | h | h
    · exact hCz (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCt (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCzt (Subgroup.mem_centralizer_singleton_iff.mpr h)
  obtain ⟨x, hxL, hxo, hxH⟩ := key
  obtain ⟨y, hyH, hyc⟩ := exists_conj_mem_dComp hp hq hΩ hcomp hK hs.noTwins hz hRΩ hRK hRS
    hs.hW.1 hs.hW.2.1 hSH hLΩ hxL hxo hxH
  have hyN : y * g⁻¹ ∈ sigmaNorm Ω K := by
    rw [mem_sigmaNorm_iff hΩ.conjInvariant hK, conjSub_mul, ← hLdef]
    exact hyc
  have h1 : g⁻¹ ∈ H274 Ω K z := by
    have := (H274 Ω K z).mul_mem ((H274 Ω K z).inv_mem hyH) (sigmaNorm_le_H274 K z hyN)
    simpa using this
  simpa using (H274 Ω K z).inv_mem h1

theorem mem_H274_of_conj_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ H274 Ω K z) : g ∈ H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hSH : (S : Subgroup G) ≤ H274 Ω K z :=
    (sylow_le_sigmaNorm hp hq hΩ hK hRΩ hRK hRS hs.hz).trans (sigmaNorm_le_H274 K z)
  have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have := hs.hz.conj g⁻¹
    rwa [inv_inv] at this
  have hb2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * z * g)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one)
  obtain ⟨y, hyH, hyS⟩ := exists_conj_into_sylow S hSH hg hb2
  have h1 : (g * y⁻¹)⁻¹ * z * (g * y⁻¹) ∈ (S : Subgroup G) := by
    have : (g * y⁻¹)⁻¹ * z * (g * y⁻¹) = y * (g⁻¹ * z * g) * y⁻¹ := by group
    rwa [this]
  have h2 := mem_H274_of_conj_mem_sylow hs hcomp h1
  have : g = (g * y⁻¹) * y := by group
  rw [this]
  exact (H274 Ω K z).mul_mem h2 hyH

end Main

end T8

end CFSG.ClassicalInvolution.Asc77
