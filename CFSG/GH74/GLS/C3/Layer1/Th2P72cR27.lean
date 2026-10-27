module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR26
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR19

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_cbar_five {x u : G} {K J B : Subgroup G} (hlt : PumpUpLT 2 x K u J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K)
    (e5 : kBar K ≃* alternatingGroup (Fin 5))
    (hBJ : B ≤ normalizer (J : Set G)) (hBK : B ≤ normalizer (K : Set G))
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (huB : u ∈ B)
    (hout : ∃ y' ∈ B, y' ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K))
    (hB16 : 16 ≤ Nat.card ↥B)
    (hker : Nat.card ↥(B ⊓ centralizerSection K (pPrimeCoreOf 2 K)) ≤ 4) :
    ∃ (V : Subgroup G) (hVB : V ≤ B) (b : G) (hbB : b ∈ B), Nat.card B = 2 * Nat.card V ∧
      ∃ c : kBar J, Nat.Prime (orderOf c) ∧ Odd (orderOf c) ∧
        (∀ v (hv : v ∈ V), barAct J ⟨v, hBJ (hVB hv)⟩ c = c) ∧
        barAct J ⟨b, hBJ hbB⟩ c = c⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Θ, hΘ⟩ := exists_theta hlt hxJ e
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  let κ : ↥B →* MulAut (kBar K) := (barAct K).comp (Subgroup.inclusion hBK)
  have hκapp : ∀ g (hg : g ∈ B), κ ⟨g, hg⟩ = barAct K ⟨g, hBK hg⟩ := fun g hg => rfl
  have hcomm : ∀ a ∈ κ.range, ∀ b ∈ κ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc a a.2 b b.2)
  have hsq : ∀ a ∈ κ.range, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hBsq a a.2)
    rw [this, map_one]
  have hkerκ : κ.ker = (B ⊓ centralizerSection K (pPrimeCoreOf 2 K)).subgroupOf B := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨g.2, (barAct_eq_one_iff ⟨(g : G), hBK g.2⟩).1 h1⟩
    · rintro ⟨-, h1⟩
      exact (barAct_eq_one_iff ⟨(g : G), hBK g.2⟩).2 h1
  have hkercard : Nat.card κ.ker ≤ 4 := by
    rw [hkerκ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : B ⊓ centralizerSection K (pPrimeCoreOf 2 K) ≤ B)).toEquiv]
    exact hker
  have hrange4 : 4 ≤ Nat.card κ.range := by
    have h1 := Subgroup.card_ker_mul_card_range κ
    by_contra hlt4
    push Not at hlt4
    have : Nat.card ↥B ≤ 4 * 3 := by
      rw [← h1]
      exact Nat.mul_le_mul hkercard (by omega)
    omega
  have hout' : ∃ r ∈ κ.range, r ∉ (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
    obtain ⟨y', hy'B, hy'⟩ := hout
    refine ⟨κ ⟨y', hy'B⟩, ⟨⟨y', hy'B⟩, rfl⟩, ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective z
    apply hy'
    have h1 : barAct K ⟨k, Subgroup.le_normalizer hk⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩) :=
      barAct_of_mem hk
    have h2 : barAct K ⟨k⁻¹ * y', (normalizer (K : Set G)).mul_mem
        ((normalizer (K : Set G)).inv_mem (Subgroup.le_normalizer hk)) (hBK hy'B)⟩ = 1 := by
      have : (⟨k⁻¹ * y', (normalizer (K : Set G)).mul_mem
          ((normalizer (K : Set G)).inv_mem (Subgroup.le_normalizer hk)) (hBK hy'B)⟩ :
          ↥(normalizer (K : Set G))) = ⟨k, Subgroup.le_normalizer hk⟩⁻¹ * ⟨y', hBK hy'B⟩ :=
        Subtype.ext (by simp)
      rw [this, map_mul, map_inv, h1, ← hκapp y' hy'B, ← hz, inv_mul_cancel]
    have h3 : k⁻¹ * y' ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
      (barAct_eq_one_iff _).1 h2
    have e1 : y' = k * (k⁻¹ * y') := by group
    rw [e1]
    exact Subgroup.mul_mem_sup hk h3
  obtain ⟨v', b', c', hv'R, hb'R, hv'1, hcardv', hc'ord, hv'c, hb'c⟩ :=
    exists_klein_data_aut5 e5 κ.range hcomm hsq hrange4 hout'
  have hV'le : zpowers v' ≤ κ.range := (Subgroup.zpowers_le).2 hv'R
  obtain ⟨V, hVB, hVcard, hVmem, hVback⟩ := exists_pullback κ hV'le hcardv'
  obtain ⟨bb, hbb⟩ := hb'R
  have hstab : ∀ φ ∈ zpowers v', φ c' = c' := by
    intro φ hφ
    have hst : v' ∈ MulAction.stabilizer (MulAut (kBar K)) c' := hv'c
    have := (Subgroup.zpowers_le (H := MulAction.stabilizer (MulAut (kBar K)) c')).2 hst hφ
    exact this
  refine ⟨V, hVB, bb.1, bb.2, hVcard, Θ.symm c', ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hc'ord]; exact Nat.prime_three
  · rw [MulEquiv.orderOf_eq, hc'ord]; exact ⟨1, rfl⟩
  · intro v hv
    apply Θ.injective
    have htv : v * u = u * v := hBc v (hVB hv) u huB
    rw [hΘ v (hBJ (hVB hv)) (hBK (hVB hv)) htv, MulEquiv.apply_symm_apply]
    have h1 : κ ⟨v, hVB hv⟩ c' = c' := hstab _ (hVmem v hv)
    exact h1
  · apply Θ.injective
    have htb : bb.1 * u = u * bb.1 := hBc bb.1 bb.2 u huB
    rw [hΘ bb.1 (hBJ bb.2) (hBK bb.2) htb, MulEquiv.apply_symm_apply, map_inv,
      MulEquiv.apply_symm_apply]
    have h1 : κ bb c' = c'⁻¹ := by rw [hbb]; exact hb'c
    exact h1

theorem u2_core (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hKG : B_ivk_oddcent)
    {B : Subgroup G} {t : G} (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hrk : 4 ≤ pRank 2 ↥B)
    (htB : t ∈ B) (ht2 : orderOf t = 2)
    (h7B1 : ∀ W : Subgroup G, IsE 3 B W → AG W = ⊥)
    (h7B2 : ∀ W : Subgroup G, IsE 2 B W → ⁅AG W, B⁆ = ⊥)
    (hdata : ∃ (W V : Subgroup G) (b : G) (X₀ X₁ : Subgroup G),
      W ≤ V ∧ V ≤ B ∧ Nat.card B = 2 * Nat.card V ∧ Nat.card B = 4 * Nat.card W ∧ b ∈ B ∧
      Odd (Nat.card X₀) ∧ Odd (Nat.card X₁) ∧
      X₀ ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ∧ X₁ ≤ centralizer ({t} : Set G) ∧
      (∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w) ∧ (∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v) ∧
      (∀ g ∈ B, ∀ z ∈ X₀, g * z * g⁻¹ ∈ X₀) ∧ (∀ z ∈ X₁, ∀ z' ∈ X₀, z * z' * z⁻¹ ∈ X₀) ∧
      (∀ z ∈ X₁, b * z * b⁻¹ = z⁻¹) ∧ ⁅⁅X₀, X₁⁆, X₁⁆ ≠ ⊥ ∧
      ((∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
        (∀ v ∈ V, v ∉ W → ∃ z ∈ ⁅⁅X₀, X₁⁆, X₁⁆, v * z ≠ z * v))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨W, V, b, X₀, X₁, hWV, hVB, hVcard, hWcard, hbB, hX₀odd, hX₁odd, hX₀t, hX₁t, hWX₀, hVX₁,
    hBX₀, hX₁X₀, hbinv, hZne, hα⟩ := hdata
  set Z : Subgroup G := ⁅⁅X₀, X₁⁆, X₁⁆ with hZ
  have hZX₀ : Z ≤ X₀ := by
    have h1 : ⁅X₀, X₁⁆ ≤ X₀ := by
      rw [Subgroup.commutator_le]
      intro z hz y hy
      have : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact X₀.mul_mem hz (hX₁X₀ y hy z⁻¹ (X₀.inv_mem hz))
    rw [hZ, Subgroup.commutator_le]
    intro m hm y hy
    have : ⁅m, y⁆ = m * (y * m⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact X₀.mul_mem (h1 hm) (hX₁X₀ y hy m⁻¹ (X₀.inv_mem (h1 hm)))
  have key : ∀ u ∈ B, u ≠ 1 → (∀ z ∈ X₀, u * z = z * u) → (∀ z ∈ X₁, u * z = z * u) →
      ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({u} : Set G)) → False := by
    intro u huB hu1 hu₀ hu₁ hZnot
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq u huB) hu1
    have hut : u * t = t * u := hBc u huB t htB
    have hZt : Z ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) := hZX₀.trans hX₀t
    have hZu : Z ≤ centralizer ({u} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.2 (hu₀ z (hZX₀ hz)).symm
    obtain ⟨L, hL, htN, hZN, htnot, hZnot'⟩ := exists_pComponent_of_Z ht2 hut hZt hZu hZnot
    have htu : t ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hut.symm
    have hunb : IsUnbalancingTriple u t L :=
      ⟨⟨hu2, hL⟩, ht2, htu, htN, fun hle => hZnot' (fun z hz => hle ⟨hZt hz, hZu hz⟩)⟩
    have hu := kBar_u2_of_unbal hG hL34 h102 hunb
    have hLN := centralizer_le_normalizer_of_u2 hG.pRank_eq_four.le hu2 hL hu
    have hXu : X₁ ≤ centralizer ({u} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.2 (hu₁ z hz).symm
    have hbu : b ∈ centralizer ({u} : Set G) :=
      mem_centralizer_singleton_iff.2 (hBc b hbB u huB)
    have hEG := endgame_comm_le_cSec hKG ht2 hut hL hLN hu hXu hX₁t hX₁odd hbu hbinv
    have hX₀A : X₀ ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
      le_inf hX₀t (fun z hz => mem_centralizer_singleton_iff.2 (hu₀ z hz).symm)
    have hZle : Z ≤ ⁅⁅pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G), X₁⁆,
        X₁⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hX₀A le_rfl) le_rfl
    exact hZnot' (hZle.trans hEG)
  obtain ⟨u, huV, hu1, huX₀, huX₁, hZnot⟩ :=
    exists_defect_centralizing_actors hBel hrk hWV hVB hVcard hWcard hZne h7B1 h7B2 hWX₀ hVX₁ hα
  exact key u (hVB huV) hu1 huX₀ huX₁ hZnot

theorem p713_of_B0
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (h102a : B_ivk_10_2a) (hKG : B_ivk_oddcent)
    (h218 : B_IG_21_8) (h2110 : B_IG_21_10)
    (hG : C3Hyp G) {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S)
    (hrow : Th2Row.r4b.holds x y K T S)
    (hbal : ∀ B ∈ Th2Row.r4b.BT x K T S, Th2Row.r4b.level.IsBal B)
    {B : Subgroup G} (hB : B ∈ Th2Row.r4b.BT x K T S) (hθ : Th2Row.r4b.level.theta B = ⊥)
    {B₀ : Subgroup G} (hB₀T : B₀ ≤ T) (hB₀el : CFSG.IsElementaryAbelian 2 ↥B₀)
    (hB₀rk : 4 ≤ pRank 2 ↥B₀) {u y' : G} (huB : u ∈ B₀) (huQ : u ∈ T ⊓ CxK x K)
    (hu2 : orderOf u = 2) (hy'B : y' ∈ B₀) (hy'R : y' ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K))
    {J : Subgroup G} (hJ : PumpUpLT 2 x K u J) : CFSG.IsQuasisimple ↥J := by
  classical
  by_contra hnqs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL5, -, -, -⟩ := hrow
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by
    rintro q rfl
    decide
  have hcen := centerlessBar_of_hasL2Model hPr hL5
  have hPQ := hstd.commDisj hcen
  have hP := rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL5
  have hP4 := card_sylow_L2_five hstd.sylow_P hL5
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hUP : U = T ⊓ K := Subgroup.eq_of_le_of_card_ge hU.1 (by rw [hU.2.2, hP4])
  have hrkP : 2 ≤ pRank 2 ↥(T ⊓ K) := by rw [← hUP, pRank_of_isFourSub hU]
  have hKN := hstd.K_normal (by rw [hG.pRank_eq_four]) hcen hrkP
  obtain ⟨e5⟩ := C3.Layer1.Back.nonempty_alt5_of_hasL2Model5 hL5
  have hTle := hstd.card_T_le_of_A5 hKN e5
  have hRcard : Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) = 4 * Nat.card ↥(T ⊓ CxK x K) := by
    rw [hPQ.card_sup le_rfl le_rfl, hP4]
  have hRT : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ T := sup_le inf_le_left inf_le_left
  have hTR : Nat.card ↥T ≤ 2 * Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) := by omega
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB₀el
  have hB₀S : IsS T B₀ := Th2.P812.isS_of_isE_rank hG hB₀T hB₀el hB₀rk
  have hB₀BT : B₀ ∈ Th2Row.r4b.BT x K T S := ⟨hB₀S, hB₀rk⟩
  set Tstar : Subgroup G := ⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B' with hTs
  have hTsT : Tstar ≤ T := iSup₂_le fun B' hB' => hB'.1.1
  have hB₀le : B₀ ≤ Tstar :=
    le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ {B'' : Subgroup G | IsSn 4 T B''}) => B) B₀ hB₀BT
  have hA : IsE 4 Tstar B₀ := ⟨hB₀le, hB₀el, hB₀rk⟩
  have hconn := conn_L2_five hG hstd hL5 hB hA
  have hS : ∀ B' : Subgroup G, IsSn Th2Level.fiveHalves.n Tstar B' →
      IsE Th2Level.fiveHalves.minRank ⊤ B' ∧ Th2Level.fiveHalves.IsBal B' := by
    intro B' hB'
    have hB'T : B' ≤ T := hB'.1.1.trans hTsT
    have hB'S : IsS T B' := Th2.P812.isS_of_isE_rank hG hB'T hB'.1.2.1 hB'.2
    exact ⟨⟨le_top, hB'.1.2.1, hB'.2⟩, hbal B' ⟨hB'S, hB'.2⟩⟩
  have hθ₀ : thetaHalf 2 B₀ = ⊥ := by
    have h1 := theta_eq_of_conn Th2Level.fiveHalves h218 h2110 hS
      (show IsE 3 Tstar B₀ from ⟨hB₀le, hB₀el, by omega⟩) hconn
    have h2 : thetaHalf 2 B₀ = thetaHalf 2 B := h1
    rw [h2]
    exact hθ
  have hbalB₀ : IsKBal 3 B₀ ∧ IsWeakKBal 2 B₀ := hbal B₀ hB₀BT
  obtain ⟨h7B1, h7B2⟩ := seven_B_of_thetaHalf_eq_bot hbalB₀.1 hθ₀
  obtain ⟨⟨e⟩, hJcen, hJ2, hJN⟩ := hstd.pumpup_facts hG hL34 h102 hu2 hJ
  have hJc : IsPCompIn 2 (centralizer ({u} : Set G)) J := hJ.2.1.2.2
  have hBJ : B₀ ≤ normalizer (J : Set G) := fun g hg =>
    hJN g (mem_centralizer_singleton_iff.2 (hBc g hg u huB))
  have hBK : B₀ ≤ normalizer (K : Set G) := fun g hg =>
    mem_normalizer_K_of_KN hKN (hstd.T_le_C (hB₀T hg))
  have hxJ : x ∈ normalizer (J : Set G) := by
    refine hJN x ?_
    exact TwoThin.mem_centralizer_symm (hstd.T_le_C huQ.1)
  have hyout : y ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K) := by
    obtain ⟨p, f, hp, hf, hP5, hLie⟩ := hL5
    have hP5' : p ^ f = 5 := hP5
    have hfm : HasL2Model (kBar K) IsFM9 :=
      ⟨p, f, hp, hf, by rw [hP5']; exact Or.inr ⟨by norm_num, Or.inl ⟨1, by norm_num⟩⟩, hLie⟩
    exact h102a G hG x y K hstd.v2ss.isV2Triple hfm
  have hy'out : y' ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K) := by
    intro hy'
    set D : Subgroup G := T ⊓ (K ⊔ centralizerSection K (pPrimeCoreOf 2 K)) with hD
    have hRD : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ D := by
      refine sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left)) ?_
      exact le_inf inf_le_left ((inf_le_right.trans (inf_le_right)).trans le_sup_right)
    have hy'D : y' ∈ D := ⟨hB₀T hy'B, hy'⟩
    have hRne : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≠ D := fun h => hy'R (h ▸ hy'D)
    have hDT : D = T := by
      by_contra hne
      have hDle : D ≤ T := inf_le_left
      have hRpos : 0 < Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) := Nat.card_pos
      have hDlt : Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) < Nat.card ↥D := by
        by_contra hge
        push Not at hge
        exact hRne (Subgroup.eq_of_le_of_card_ge hRD hge)
      have hTlt : Nat.card ↥D < Nat.card ↥T := by
        by_contra hge
        push Not at hge
        exact hne (Subgroup.eq_of_le_of_card_ge hDle hge)
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hRD
      obtain ⟨m', hm'⟩ := Subgroup.card_dvd_of_le hDle
      have hm2 : 2 ≤ m := by
        by_contra hlt
        push Not at hlt
        interval_cases m <;> omega
      have hm'2 : 2 ≤ m' := by
        by_contra hlt
        push Not at hlt
        interval_cases m' <;> omega
      nlinarith
    have hyD : y ∈ D := by rw [hDT]; exact hstd.y_mem
    exact hyout hyD.2
  have hker : Nat.card ↥(B₀ ⊓ centralizerSection K (pPrimeCoreOf 2 K)) ≤ 4 := by
    have hle : B₀ ⊓ centralizerSection K (pPrimeCoreOf 2 K) ≤ T ⊓ CxK x K := by
      intro g hg
      exact ⟨hB₀T hg.1, hstd.T_le_C (hB₀T hg.1), hg.2⟩
    have hel : CFSG.IsElementaryAbelian 2 ↥(B₀ ⊓ centralizerSection K (pPrimeCoreOf 2 K)) :=
      isElementaryAbelian_le hB₀el inf_le_left
    have h2 := hstd.pRank_le_two_of_le_Q hG hL34 h102 hle
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hel]
    calc 2 ^ pRank 2 ↥(B₀ ⊓ centralizerSection K (pPrimeCoreOf 2 K)) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  have hB16 : 16 ≤ Nat.card ↥B₀ := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hB₀el]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥B₀ := Nat.pow_le_pow_right (by norm_num) hB₀rk
  obtain ⟨V, hVB, b, hbB, hVcard, c, hcp, hcodd, hVc, hbc⟩ :=
    exists_cbar_five hJ hxJ e e5 hBJ hBK hB₀el huB ⟨y', hy'B, hy'out⟩ hB16 hker
  have hsimpleK : IsSimpleGroup (kBar K) :=
    (e5.isSimpleGroup_congr).2 (alternatingGroup.isSimpleGroup (by simp))
  have hsimpleJ : IsSimpleGroup (kBar J) := (e.isSimpleGroup_congr).2 hsimpleK
  have hdihK := hasDihedralSylowTwo_of_hasL2Model hPr hL5
  have hdihJ : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J) :=
    CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e hdihK
  have hdata := p79_of_data hJc hnqs hsimpleJ hdihJ hBJ hB₀el hB₀rk
    ⟨V, hVB, b, hbB, hVcard, c, hcp, hcodd, hVc, hbc⟩
  exact u2_core hG hL34 h102 hKG hB₀el hB₀rk huB hu2 h7B1 h7B2 hdata

end CFSG.GH74.GLS.Th2.Obs
