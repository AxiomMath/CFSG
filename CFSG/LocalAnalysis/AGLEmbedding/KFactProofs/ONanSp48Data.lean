module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Rank
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs
public import Certificates.Certificate9536
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Emb
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48LocalMain

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin KFactProofs.Sp48 CFSG.PreuniquenessRankFour.Helpers

namespace KFactProofs.Sp48

section Injective

variable {G H : Type*} [Group G] [Group H] {f : G →* H}

theorem centerOf_map (hf : Function.Injective f) (X : Subgroup G) :
    centerOf (X.map f) = (centerOf X).map f := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hz (f y) ⟨y, hy, rfl⟩
    apply hf
    rw [map_mul, map_mul]
    exact this
  · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hxc y hy]

theorem isElemAbelian_comap (hf : Function.Injective f) {E : Subgroup H} {p : ℕ}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap f) := CFSG.Open.IsElemAbelian.comap hE hf

end Injective

end KFactProofs.Sp48

open KFactProofs.Sp48 in
theorem kFactSp48Data : KFactSp48Data := by
  intro Y _ _ K d hd hKn he hC T Y₀ h3 hW _ _
  obtain ⟨Tm, Am, Em, T0m, t1, t2, w, s, f, L⟩ :=
    sp48Local_of_check Certificates.certificate9536
  obtain ⟨e⟩ := he
  obtain ⟨⟨eK⟩, hcardK⟩ := exists_equiv_sp8 hd e
  have hcardS : Nat.card Sp8 = 3 ^ 4 * 13045760 := by
    rw [← hcardK]
    exact Nat.card_congr eK.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnot : ¬ (T : Subgroup Y) ≤ K := by
    intro hTK
    obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
      (T : Subgroup Y)
    let κ : Sp8 →* Y := K.subtype.comp eK.symm.toMonoidHom
    have hκ : Function.Injective κ := fun a b h => eK.symm.injective (Subtype.val_injective h)
    have hEκ : E ≤ κ.range := fun x hx => ⟨eK ⟨x, hTK (hET hx)⟩, by simp [κ]⟩
    have hF : IsElemAbelian 3 (E.comap κ) := isElemAbelian_comap hκ hE
    have h9 := elem_le_nine L hcardS _ hF
    have hc : Nat.card (E.comap κ) = Nat.card E := by
      conv_rhs => rw [← Subgroup.map_comap_eq_self hEκ]
      rw [Subgroup.card_map_of_injective hκ]
    rw [hc, hcard] at h9
    have : Open.pRank 3 (T : Subgroup Y) ≤ 2 := by
      by_contra hlt
      have : 3 ^ 3 ≤ 3 ^ Open.pRank 3 (T : Subgroup Y) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  obtain ⟨y, hyT, hyK⟩ : ∃ y ∈ (T : Subgroup Y), y ∉ K := by
    by_contra h
    push Not at h
    exact hnot fun x hx => h x hx
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ (3 ^ m) = 1 := by
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨y, hyT⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have : K.Normal := hKn
  obtain ⟨Θ, hΘ, hΘinl, hΘK⟩ := exists_embedding hC (eK := eK) hyK hm
  have hidx := index_le_six (eK := eK) hC
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hTle : Nat.card (T : Subgroup Y) ≤ 3 ^ 5 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 T.isPGroup'
    have hdvd : 3 ^ a ∣ 3 ^ 4 * 13045760 * K.index := by
      rw [← ha]
      have := Subgroup.card_subgroup_dvd_card (T : Subgroup Y)
      rwa [← Subgroup.card_mul_index K, hcardK] at this
    rw [ha]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hlt
    have h6 : 3 ^ 6 ∣ 3 ^ 4 * 13045760 * K.index :=
      (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
    generalize K.index = i at hidx hidx0 h6
    interval_cases i <;> omega
  have hc1 : Nat.card (Tm.map Θ) = 3 ^ 5 :=
    (Subgroup.card_map_of_injective hΘ).trans L.card_T
  obtain ⟨y₀, hy₀⟩ := exists_conj_eq_map T (IsPGroup.of_card hc1) hc1 hTle
  let Θ' : Hh →* Y := (MulAut.conj y₀).toMonoidHom.comp Θ
  have hΘ' : Function.Injective Θ' := (MulAut.conj y₀).injective.comp hΘ
  have hT : (T : Subgroup Y) = Tm.map Θ' := by rw [hy₀, Subgroup.map_map]
  have hQ : centerOf (T : Subgroup Y) = Em.map Θ' := by rw [hT, centerOf_map hΘ', L.E_eq]
  have hKc : ∀ x : Hh, Θ' x ∈ K ↔ x.right = 1 := fun x => by
    rw [← hΘK]
    show y₀ * Θ x * y₀⁻¹ ∈ K ↔ _
    constructor
    · intro h
      have h2 := hKn.conj_mem _ h y₀⁻¹
      have e : y₀⁻¹ * (y₀ * Θ x * y₀⁻¹) * y₀⁻¹⁻¹ = Θ x := by group
      rwa [e] at h2
    · intro h
      exact hKn.conj_mem _ h y₀
  have hT0 : ∀ x, x ∈ T0m ↔ x ∈ Tm ∧ x.right = 1 := fun x => by
    rw [L.T0_eq, Subgroup.mem_inf, MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right]
  have hTK : (T : Subgroup Y) ⊓ K = T0m.map Θ' := by
    ext z
    rw [hT, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, (hT0 x).2 ⟨hx, (hKc x).1 hz⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hx1, hx2⟩ := (hT0 x).1 hx
      exact ⟨⟨x, hx1, rfl⟩, (hKc x).2 hx2⟩
  have hEel : IsElemAbelian 3 Em := by
    refine ⟨IsMulCommutative.of_comm ?_, L.E_pow⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (L.A_comm a (L.E_le_A ha) b (L.E_le_A hb))
  have hQN : Subgroup.normalizer (centerOf (T : Subgroup Y) : Set Y) ≤
      GLBWeakCore 3 (T : Subgroup Y) := by
    refine normalizer_le_weakCore 3 inf_le_left ?_ ?_
    · rw [hQ]
      exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel Θ')
        (k := 2) (by rw [Subgroup.card_map_of_injective hΘ', L.card_E])
    · refine h3.trans (pRank_mono 3 Nat.prime_three ?_)
      intro x hx
      refine Subgroup.mem_sup_right ⟨hx, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hq.2 x hx).symm
  have hB : ∀ b ∈ ({t1, t2, w, s, f} : Set Hh), Θ' b ∈ Y₀ := by
    intro b hb
    have hnorm : Θ' b ∈ Subgroup.normalizer (centerOf (T : Subgroup Y) : Set Y) := by
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      rw [SetLike.mem_coe, hQ] at hn ⊢
      obtain ⟨e', he', rfl⟩ := hn
      exact ⟨b * e' * b⁻¹, L.norm_E b hb e' he', by simp [map_mul, map_inv]⟩
    exact hW (hQN hnorm)
  refine ⟨Am.map Θ', ?_⟩
  refine
  { card_T := by rw [hT, Subgroup.card_map_of_injective hΘ', L.card_T]
    center_pow := fun z hz => by
      rw [hQ] at hz
      obtain ⟨e', he', rfl⟩ := hz
      rw [← map_pow, L.E_pow e' he', map_one]
    card_center := by rw [hQ, Subgroup.card_map_of_injective hΘ', L.card_E]
    card_TK := by rw [hTK, Subgroup.card_map_of_injective hΘ', L.card_T0]
    A_le := by rw [hT]; exact Subgroup.map_mono L.A_le
    A_pow := by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, L.A_pow a ha, map_one]
    A_comm := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, L.A_comm a ha b hb]
    card_A := by rw [Subgroup.card_map_of_injective hΘ', L.card_A]
    center_le_A := by rw [hQ]; exact Subgroup.map_mono L.E_le_A
    sylow_normal := ?_
    homocyclic := ?_
    orbit_nine := ?_ }
  ·
    intro W hWY hYW hZW
    have hU := L.lattice (Tm ⊓ W.comap Θ') ?_ inf_le_left ?_
    · have hTW : (T : Subgroup Y) ⊓ W = (Tm ⊓ W.comap Θ').map Θ' := by
        ext z
        rw [hT, Subgroup.mem_inf]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hz⟩
          exact ⟨x, ⟨hx, hz⟩, rfl⟩
        · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
          exact ⟨⟨x, hx, rfl⟩, hz⟩
      rw [hTW]
      rcases hU with h | h | h | h
      · left; rw [h, hQ]
      · right; left; rw [h]
      · right; right; left; rw [h, hTK]
      · right; right; right; rw [h, hT]
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [L.E_eq] at hx
        exact hx.1
      · show Θ' x ∈ W
        apply hZW
        rw [hQ]
        exact ⟨x, hx, rfl⟩
    · intro b hb x hx
      refine ⟨L.norm_T b hb x hx.1, ?_⟩
      show Θ' (b * x * b⁻¹) ∈ W
      have hbY : Θ' b ∈ Subgroup.normalizer (W : Set Y) := hYW (hB b hb)
      have := (Subgroup.mem_normalizer_iff.1 hbY (Θ' x)).1 (show Θ' x ∈ W from hx.2)
      simpa [map_mul, map_inv] using this
  · refine ⟨Θ' t1, Θ' t2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hTK]; exact ⟨t1, L.t1_mem, rfl⟩
    · rw [hTK]; exact ⟨t2, L.t2_mem, rfl⟩
    · rw [orderOf_injective Θ' hΘ', L.order_t1]
    · rw [orderOf_injective Θ' hΘ', L.order_t2]
    · rw [← map_mul, ← map_mul, L.comm_t]
    · rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ _ hΘ',
        L.inf_t, Subgroup.map_bot]
  · intro a ha haZ W
    obtain ⟨a', ha', rfl⟩ := ha
    have ha'E : a' ∉ Em := fun h => haZ (by rw [hQ]; exact ⟨a', h, rfl⟩)
    obtain ⟨u, hu, hW'⟩ := L.orbit a' ha' ha'E fun i => (W i).comap Θ'
    refine ⟨Θ' u, by rw [hTK]; exact ⟨u, hu, rfl⟩, fun i hi => hW' i ?_⟩
    have h1 : (Subgroup.zpowers (Θ' a')).map (MulAut.conj (Θ' u)).toMonoidHom =
        ((Subgroup.zpowers a').map (MulAut.conj u).toMonoidHom).map Θ' := by
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      congr 1
      simp [MulAut.conj_apply]
    rw [h1] at hi
    rw [← hi, Subgroup.comap_map_eq_self_of_injective hΘ']

end CFSG.AGLEmbedding
