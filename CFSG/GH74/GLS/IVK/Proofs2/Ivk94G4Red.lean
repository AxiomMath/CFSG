module

public import CFSG.GH74.GLS.Stage4.T2F1Red
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.GH74.GLS.IVK.Statements.Sec4c
public import CFSG.GH74.GLS.Stage4.T2F1Gen

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem pRank_two_centralizerBar_le {G : Type} [Group G] [Finite G] (f : G) {r : ℕ}
    (hr : CFSG.pRank 2 G ≤ r) :
    CFSG.pRank 2 (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) ≤ r := by
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({f} : Set G))) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({f} : Set G))))
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd]
  refine le_trans ?_ hr
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 (centralizer ({f} : Set G)),
    CFSG.SectionRank.pRank_eq_open_pRank_top 2 G]
  exact CFSG.SectionRank.pRank_top_le_of_injective Nat.prime_two.one_lt
    (centralizer ({f} : Set G)).subtype (centralizer ({f} : Set G)).subtype_injective

theorem ch6T2F1PrimeGe5_of_leaves_g4_three
    (hRemL : Ch6T2Rem) (h3 : Ch6T2P51) (h4 : Ch6T2P52)
    (hL : Ch6T2F1Local) (h94 : IVK_9_4_g4_G2three) (h47 : IVK_4_7ef) : Ch6T2F1PrimeGe5 := by
  intro G _ _ hStd hr Gs _ n hn _ hAt hBad z K₁ K₂ F₁ F₂ _ _ hSet
  have hn0 : n ≠ 0 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, hRem⟩ := hRemL G hStd hr Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ hSet
  obtain ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    h3 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem rfl
  obtain ⟨F, hF5⟩ :=
    h4 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨P₀, hP₀⟩ := t2_bad3 hSet hBad
  have hab := t2F1_three_abelian hn0 hSet hLoc hK₁ hK₂ hq₁ hq₂
  have hno : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro T hT x hx y hy
    obtain ⟨P, hTP⟩ := hT.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
    have hx' := hTP hx
    have hy' := hTP hy
    rw [← hg, Sylow.coe_subgroup_smul] at hx' hy'
    obtain ⟨x', hx'', hxx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx'
    obtain ⟨y', hy'', hyy⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy'
    have hc : x' * y' = y' * x' := hab (P₀ : Subgroup G) hP₀ P₀.isPGroup' x' hx'' y' hy''
    have hxx' : x = g * x' * g⁻¹ := by
      rw [← hxx]; simp [MulAut.smul_def, MulAut.conj_apply]
    have hyy' : y = g * y' * g⁻¹ := by
      rw [← hyy]; simp [MulAut.smul_def, MulAut.conj_apply]
    rw [hxx', hyy']
    calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
      _ = g * (y' * x') * g⁻¹ := by rw [hc]
      _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group
  subst hz hK₁ hK₂
  have hF1 : ∀ f ∈ F, f = 1 := by
    intro f hf
    by_contra hf1
    have hodd : Odd (orderOf f) := hF5.F_odd f hf
    have hne : orderOf f ≠ 1 := fun h => hf1 (orderOf_eq_one_iff.1 h)
    obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hf'F : f ^ (orderOf f / r) ∈ F := F.pow_mem hf _
    have hf'ord : orderOf (f ^ (orderOf f / r)) = r :=
      orderOf_pow_orderOf_div (orderOf_pos f).ne' hrd
    generalize f ^ (orderOf f / r) = f' at hf'F hf'ord
    have hr_odd : Odd r := Odd.of_dvd_nat hodd hrd
    have hfC : f' ∈ centralizer (N.S : Set G) := by
      rw [hF5.centS]; exact Subgroup.mem_sup_right hf'F
    have hfS : ∀ s ∈ N.S, f' * s = s * f' := fun s hs =>
      (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
    have hfz : f' * N.z = N.z * f' := hfS N.z hLoc.z_mem_S
    have hfC' : f' ∈ centralizer ({N.z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hfz
    have hr3 : r ≠ 3 := by
      intro h3'
      have hf3 : f' ^ (3 ^ 1) = 1 := by
        rw [pow_one, ← h3', ← hf'ord]; exact pow_orderOf_eq_one _
      have hfK : f' ∈ N.K₁ ⊔ N.K₂ :=
        t2G_three_elt_mem hSet.le_centralizer (fun c hc x hx => ctx.Kn c hc x hx) P₀ hP₀ hfC' hf3
      have hfzp := t2C_cent_K hSet hRem ctx.Sctx f' hfK hfS
      rcases t2C_zpowers_cases (t2C_zz hSet) hfzp with h1 | h1
      · rw [h1, orderOf_one] at hf'ord; omega
      · rw [h1, hSet.central.1] at hf'ord; omega
    have hr5 : 5 ≤ r := by
      have h2 := hrp.two_le
      have h2' : r ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hr_odd) even_two
      have h4 : r ≠ 4 := by rintro rfl; norm_num at hrp
      omega
    have hSyl : ∃ S : Sylow 2 G, (∀ s ∈ (S : Subgroup G), s * N.z = N.z * s) ∧
        f' ∈ centralizer ((S : Subgroup G) : Set G) := by
      refine ⟨hLoc.S_pGroup.toSylow hLoc.S_sylow, ?_, ?_⟩
      · rw [IsPGroup.toSylow_coe]; exact hLoc.z_cent_S
      · rw [IsPGroup.toSylow_coe]; exact hfC
    obtain ⟨m, hzC, hnm, hHyp⟩ :=
      hL G hStd hr Gs n hn hAt hBad N.z N.K₁ N.K₂ F₁ F₂ t hSet hRem r hrp hr5 f' hf'ord hSyl
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hnm
      exact hn0 hnm
    have hfne : centralizer ({f'} : Set G) ≠ ⊤ := by
      intro htop
      have hf'c : f' ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have : g ∈ centralizer ({f'} : Set G) := by rw [htop]; exact Subgroup.mem_top g
        exact Subgroup.mem_centralizer_singleton_iff.1 this
      have hsimple : IsSimpleGroup G := hStd.kps.1
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
      · rw [h0] at hf'c
        have h1 : f' = 1 := Subgroup.mem_bot.1 hf'c
        rw [h1, orderOf_one] at hf'ord
        exact hrp.one_lt.ne hf'ord
      · obtain ⟨b, c, hbc⟩ := hStd.kps.2.1
        apply hbc
        have := Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) b
        exact this
    have hKX : IsKGroupNative ↥(centralizer ({f'} : Set G)) :=
      hStd.kps.isKGroupNative_of_ne_top hfne
    have hKH : IsKGroupNative
        (↥(centralizer ({f'} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f'} : Set G))) :=
      CFSG.SectionRank.IsKGroupCat.quotient hKX _
    have hO : pPrimeCore 2
        (↥(centralizer ({f'} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f'} : Set G))) = ⊥ :=
      pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥(centralizer ({f'} : Set G))) (p := 2)
    have hGen4H : Gen4
        (↥(centralizer ({f'} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f'} : Set G))) :=
      Gen4.quotient _ (Gen4.subgroup _ hStd.gen4)
    have hrkH : CFSG.pRank 2
        (↥(centralizer ({f'} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f'} : Set G))) ≤ 3 :=
      pRank_two_centralizerBar_le f' hr.le
    have hLie := h94 _ Gs _ m (Nat.one_le_iff_ne_zero.2 hm0) hGen4H hrkH ⟨hKH, hO, hHyp⟩
    set Hb := ↥(centralizer ({f'} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f'} : Set G)) with hHb
    obtain ⟨P'⟩ : Nonempty (Sylow 3 ↥(layer Hb)) := inferInstance
    obtain ⟨-, hPc⟩ := h47.1 ↥(layer Hb) 3 m Nat.prime_three (by norm_num) (Or.inl hLie) P'
    obtain ⟨-, hZc⟩ := h47.2 ↥(layer Hb) m hLie P'
    have hnonab : ∃ a ∈ (P' : Subgroup ↥(layer Hb)), ∃ b ∈ (P' : Subgroup ↥(layer Hb)),
        a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hZtop : Subgroup.center ↥(P' : Subgroup ↥(layer Hb)) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hcon _ y.2 _ x.2)
      have hcard : Nat.card ↥(Subgroup.center ↥(P' : Subgroup ↥(layer Hb))) =
          Nat.card ↥(P' : Subgroup ↥(layer Hb)) := by
        rw [hZtop]; exact Subgroup.card_top
      rw [hZc, hPc hLie] at hcard
      have h2 : 2 ≤ 3 ^ m := by
        have : 3 ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hm0)
        omega
      have := Nat.pow_right_injective h2 hcard
      omega
    let Q : Subgroup Hb := (P' : Subgroup ↥(layer Hb)).map (layer Hb).subtype
    have hQp : IsPGroup 3 ↥Q := by
      rintro ⟨q, hq⟩
      obtain ⟨a, ha, rfl⟩ := hq
      obtain ⟨k, hk⟩ := P'.isPGroup' ⟨a, ha⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      have := congrArg (fun x : ↥(P' : Subgroup ↥(layer Hb)) => (((x : ↥(layer Hb)) : Hb))) hk
      simpa using this
    have hπ : Function.Surjective
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G)))) :=
      QuotientGroup.mk'_surjective _
    obtain ⟨Tc⟩ : Nonempty (Sylow 3 ↥(centralizer ({f'} : Set G))) := inferInstance
    let S₁ : Sylow 3 Hb := Tc.mapSurjective hπ
    obtain ⟨S₂, hQS₂⟩ := hQp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Hb S₁ S₂
    obtain ⟨a, ha, b, hb, hab'⟩ := hnonab
    have haQ : (a : Hb) ∈ Q := ⟨a, ha, rfl⟩
    have hbQ : (b : Hb) ∈ Q := ⟨b, hb, rfl⟩
    have ha2 := hQS₂ haQ
    have hb2 := hQS₂ hbQ
    rw [← hg, Sylow.coe_subgroup_smul] at ha2 hb2
    obtain ⟨a', ha', haa⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 ha2
    obtain ⟨b', hb', hbb⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hb2
    rw [Sylow.coe_mapSurjective] at ha' hb'
    obtain ⟨x, hx, rfl⟩ := ha'
    obtain ⟨y, hy, rfl⟩ := hb'
    have hxy : x * y ≠ y * x := by
      intro hxy
      apply hab'
      apply Subtype.ext
      have h1 : (a : Hb) = g * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) x) * g⁻¹ := by
        rw [← haa]; simp [MulAut.smul_def, MulAut.conj_apply]; rfl
      have h2 : (b : Hb) = g * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) y) * g⁻¹ := by
        rw [← hbb]; simp [MulAut.smul_def, MulAut.conj_apply]; rfl
      have h3 : (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) x) *
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) y) =
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) y) *
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) x) := by
        rw [← map_mul, ← map_mul, hxy]
      show (a : Hb) * (b : Hb) = (b : Hb) * (a : Hb)
      rw [h1, h2]
      calc g * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) x) * g⁻¹ *
            (g * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) y) * g⁻¹)
          = g * ((QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) x) *
            (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) y)) * g⁻¹ := by group
        _ = g * ((QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) y) *
            (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f'} : Set G))) x)) * g⁻¹ := by rw [h3]
        _ = _ := by group
    let T : Subgroup G := (Tc : Subgroup ↥(centralizer ({f'} : Set G))).map (centralizer ({f'} : Set G)).subtype
    have hTp : IsPGroup 3 ↥T := by
      rintro ⟨q, hq⟩
      obtain ⟨t', ht', rfl⟩ := hq
      obtain ⟨k, hk⟩ := Tc.isPGroup' ⟨t', ht'⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      have := congrArg (fun x : ↥(Tc : Subgroup ↥(centralizer ({f'} : Set G))) =>
        (((x : ↥(centralizer ({f'} : Set G))) : G))) hk
      simpa using this
    exact hxy (Subtype.ext (hno T hTp x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩))
  intro c hc
  have h1 := hF5.C_le hc
  have h2 : c ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
    have hFb : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hF1
    rw [hFb, sup_bot_eq] at h1
    exact h1
  rw [← ctx.KS]
  exact h2

end CFSG.GH74.GLS.Stage4.Rest
