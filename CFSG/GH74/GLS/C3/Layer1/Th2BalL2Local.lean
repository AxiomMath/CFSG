module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalLocal
public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Core
public import CFSG.GH74.GLS.Prop27.Balance

public section

namespace CFSG.GH74.GLS.Th2.Bal

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution.Balance

section Generic

theorem isElementaryAbelian_two_of_sq {G : Type*} [Group G] (A : Subgroup G)
    (h : ∀ x ∈ A, x * x = 1) : IsElementaryAbelian 2 ↥A :=
  { toIsMulCommutative := ⟨⟨fun a b => by
      apply Subtype.ext
      have hab : ((a : G) * b)⁻¹ = (a : G) * b :=
        inv_eq_of_mul_eq_one_right (h _ (A.mul_mem a.2 b.2))
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (h _ a.2),
        inv_eq_of_mul_eq_one_right (h _ b.2)] at hab
      exact hab.symm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun g => by
      apply Subtype.ext
      simpa [pow_two] using h g g.2) }

theorem exists_two_ne_one {G : Type*} [Group G] [Finite G] (hG : 3 ≤ Nat.card G) :
    ∃ a b : G, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun g : G => decide (g ≠ 1)) := by
    intro a b hab
    by_cases ha : a = 1 <;> by_cases hb : b = 1
    · rw [ha, hb]
    · exfalso
      simp [ha, hb] at hab
    · exfalso
      simp [ha, hb] at hab
    · exact h a b ha hb
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem involutionOddCore_eq_bot_of_pPrimeCoreOf {X : Type} [Group X] (H : Subgroup X) (f : H)
    (h : pPrimeCoreOf 2 (H ⊓ centralizer ({(f : X)} : Set X)) = ⊥) :
    CFSG.Assembly.Dichotomy.involutionOddCore f = ⊥ := by
  rw [Prop27.involutionOddCore_eq_bot_iff']
  obtain ⟨D, hD⟩ : ∃ D : Subgroup X, D = H ⊓ centralizer ({(f : X)} : Set X) := ⟨_, rfl⟩
  rw [← hD] at h
  have hmap : (centralizer ({f} : Set H)).map H.subtype = D := by
    rw [hD]
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      have hc' : c ∈ centralizer ({f} : Set H) := hc
      rw [mem_centralizer_singleton_iff] at hc'
      show H.subtype c ∈ centralizer ({(f : X)} : Set X)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hc'
    · rintro ⟨hyH, hy⟩
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      have hy' : y ∈ centralizer ({(f : X)} : Set X) := hy
      rw [mem_centralizer_singleton_iff] at hy'
      show (⟨y, hyH⟩ : H) ∈ centralizer ({f} : Set H)
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext hy'
  let e : ↥(centralizer ({f} : Set H)) ≃* ↥D :=
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have h1 : pPrimeCore 2 ↥D = ⊥ := by
    have : (pPrimeCore 2 ↥D).map D.subtype = ⊥ := h
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 this
  have h2 := CFSG.pPrimeCore_map_iso 2 e
  rw [h1] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h2


theorem exists_l2Field_of_lieModel {K : Type} [Group K] {p f : ℕ} (hodd : Odd (p ^ f))
    (hL : CFSG.Blueprint.LieModel K .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : K ≃* L2 F), L2Field F ∧ Nat.card F = p ^ f := by
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · refine ⟨F, hF, hFin, e, ⟨by rw [hcard]; exact hodd, ?_⟩, hcard⟩
    have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
    have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
    have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hodd
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hcard] at h1 ⊢
    omega
  all_goals exact absurd h0 (by norm_num)

end Generic

section ThreeBalance

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem isLocallyKBalanced_three_of_l2
    (hF : L2Field F) (e : K ≃* L2 F) : IsLocallyKBalanced 3 K := by
  classical
  intro H hH F' hF8 hF2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFp : IsPGroup 2 ↥F' := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hF2 g g.2⟩
  obtain ⟨m, hm⟩ := hFp.exists_card_eq
  have h3m : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 2 ^ 3 ∣ Nat.card ↥F' := hm ▸ pow_dvd_pow 2 h3m
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥F') 2 h8
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (MulAut K), E = (E'.map F'.subtype).map H.subtype := ⟨_, rfl⟩
  have hEcard : Nat.card ↥E = 8 := by
    rw [hE, Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective F'.subtype_injective, hE']
    norm_num
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rw [hE]
    rintro _ ⟨_, ⟨f, -, rfl⟩, rfl⟩
    exact congrArg Subtype.val (hF2 f f.2)
  obtain ⟨x, hxE, hxo, e', σ', hσ'⟩ := ivk_1_2k_b_same hF e E
    (isElementaryAbelian_two_of_sq E hEsq) hEcard
  obtain ⟨g, hgF, hgx⟩ : ∃ g : H, g ∈ F' ∧ H.subtype g = x := by
    rw [hE] at hxE
    obtain ⟨_, ⟨f, -, rfl⟩, rfl⟩ := hxE
    exact ⟨F'.subtype f, f.2, rfl⟩
  subst hgx
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1] at hxo
    simp at hxo
  have hσ2 : orderOf σ' = 2 := by
    rw [← orderOf_injective (fieldAutHom e') (fieldAutHom_injective e') σ', hσ']
    exact hxo
  have hbot : pPrimeCoreOf 2 (H ⊓ centralizer ({(g : MulAut K)} : Set (MulAut K))) = ⊥ := by
    rw [show (g : MulAut K) = fieldAutHom e' σ' from hσ'.symm]
    exact pPrimeCoreOf_fieldInvolution_eq_bot hF e' H hH σ' hσ2
  have hbot' := involutionOddCore_eq_bot_of_pPrimeCoreOf H g hbot
  exact le_bot_iff.mp ((deltaCore_le_involutionOddCore hgF hg1).trans hbot'.le)

end ThreeBalance

section TwoBalanceFM9

variable {K : Type} [Group K] [Finite K]

theorem ivk_10_2L_diag {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (hfm : IsFM9 (Nat.card F)) (e0 : K ≃* L2 F) :
    ∃ e : K ≃* L2 F, ∀ (y : MulAut K) (H : Subgroup (MulAut K)), innAut K ≤ H → y ^ 2 = 1 →
        pPrimeCoreOf 2 (H ⊓ centralizer ({y} : Set (MulAut K))) ≠ ⊥ →
          y ∈ innDiagSub e ∧ y ∉ innAut K := by
  obtain ⟨e, N, -⟩ := ivk_1_2a_exists F hF K e0 (inferInstance : Nonempty (Sylow 2 (MulAut K))).some
  refine ⟨e, ?_⟩
  intro y H hH hy2 hW
  have hinj := conj_injective_of_L2 e
  obtain ⟨W', hne, hle, hodd, hnorm⟩ :=
    exists_normal_odd_fixed hinj (fun w hw => mem_innAut_of_odd_orderOf hF hfm e hw) hH hW
  by_cases hyInn : y ∈ innAut K
  ·
    exfalso
    obtain ⟨u, rfl⟩ := hyInn
    have hu2 : u ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hy2, map_one]
    by_cases hu1 : u = 1
    · subst hu1
      have hs : IsSimpleGroup K := isSimpleGroup_of_l2 hF e
      have hN : W'.Normal := ⟨fun k hk c => hnorm c (by simp [fixedSubgroup]) k hk⟩
      rcases hs.eq_bot_or_eq_top_of_normal W' with h | h
      · exact hne h
      · rw [h, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_card_of_l2 hF e)
    · have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
      obtain ⟨a, ha⟩ := exists_two_pow_card_centralizer hF hfm e hu
      have hle' : W' ≤ centralizer ({u} : Set K) := by
        rw [← Lemma118.fixedSubgroup_conj]
        exact hle
      have hdvd : Nat.card ↥W' ∣ 2 ^ a := ha ▸ Subgroup.card_dvd_of_le hle'
      exact hne (Subgroup.card_eq_one.1 (Lemma118.odd_dvd_two_pow hodd hdvd))
  · refine ⟨?_, hyInn⟩
    by_contra hyD
    obtain ⟨-, ⟨ρ⟩⟩ := exists_equiv_perm4_fixedSubgroup hF hfm e N hy2 hyD
    have hWn : (W'.subgroupOf (fixedSubgroup K y)).Normal := ⟨fun n hn c => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hnorm c c.2 n hn⟩
    have hWodd : Odd (Nat.card ↥(W'.subgroupOf (fixedSubgroup K y))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact hodd
    have hbot := eq_bot_of_normal_odd_of_equiv_perm4 ρ _ hWodd
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have hk' : (⟨k, hle hk⟩ : ↥(fixedSubgroup K y)) ∈ W'.subgroupOf (fixedSubgroup K y) := hk
    rw [hbot, Subgroup.mem_bot] at hk'
    exact congrArg Subtype.val hk'

theorem mul_mem_innAut_of_mem_innDiagSub {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (e : K ≃* L2 F) {a b : MulAut K} (ha : a ∈ innDiagSub e) (hb : b ∈ innDiagSub e)
    (ha' : a ∉ innAut K) (hb' : b ∉ innAut K) : a * b ∈ innAut K := by
  set D := innDiagSub e with hD
  have hle : innAut K ≤ D := innAut_le_innDiagSub e
  have hidx : ((innAut K).subgroupOf D).index = 2 := by
    have h1 := Subgroup.card_mul_index ((innAut K).subgroupOf D)
    have h2 : Nat.card ↥((innAut K).subgroupOf D) = Nat.card ↥(innAut K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have h3 := card_innDiagSub_eq e hF
    have hpos : 0 < Nat.card ↥(innAut K) := Nat.card_pos
    rw [h2, h3] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have := ((innAut K).subgroupOf D).mul_mem_iff_of_index_two hidx
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  exact this.2 (iff_of_false ha' hb')

theorem isLocallyKBalanced_two_of_fm9 {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (hfm : IsFM9 (Nat.card F)) (e0 : K ≃* L2 F) : IsLocallyKBalanced 2 K := by
  classical
  obtain ⟨e, hdiag⟩ := ivk_10_2L_diag hF hfm e0
  intro H hH F' hF4 hF2
  by_contra hne
  have hF3 : 3 ≤ Nat.card ↥F' := by
    have : (2 : ℕ) ^ 2 = 4 := by norm_num
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne_one (G := ↥F') hF3
  have hone : ∀ g : H, g ∈ F' → g ≠ 1 →
      (g : MulAut K) ∈ innDiagSub e ∧ (g : MulAut K) ∉ innAut K := by
    intro g hgF hg1
    have hcore : CFSG.Assembly.Dichotomy.involutionOddCore g ≠ ⊥ := fun hbot =>
      hne (le_bot_iff.mp ((deltaCore_le_involutionOddCore hgF hg1).trans hbot.le))
    have hW : pPrimeCoreOf 2 (H ⊓ centralizer ({(g : MulAut K)} : Set (MulAut K))) ≠ ⊥ :=
      fun h => hcore (involutionOddCore_eq_bot_of_pPrimeCoreOf H g h)
    exact hdiag (g : MulAut K) H hH (by rw [pow_two]; exact congrArg Subtype.val (hF2 g hgF)) hW
  have hne1 : ∀ g : ↥F', g ≠ 1 → ((g : H) : H) ≠ 1 := fun g hg h => hg (Subtype.ext h)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : a * a = 1 := Subtype.ext (hF2 a a.2)
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right h2).symm
  obtain ⟨haD, haI⟩ := hone a a.2 (hne1 a ha)
  obtain ⟨hbD, hbI⟩ := hone b b.2 (hne1 b hb)
  obtain ⟨-, habI⟩ := hone (a * b : ↥F') (a * b).2 (hne1 _ hab1)
  exact habI (mul_mem_innAut_of_mem_innDiagSub hF e haD hbD haI hbI)

end TwoBalanceFM9

end CFSG.GH74.GLS.Th2.Bal
