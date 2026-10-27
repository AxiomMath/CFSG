module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196OCRank2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H196OC

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie isL2 ambiguousChev)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (Lemma123.autQ Lemma123.autQ_injective)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196 (mem_innerAut_of_congr
  mem_innerAut_of_not_dvd ambiguousChev_lie_odd l2Eight_of_catalog psp43_model_of_twistedA
  mem_innerAut_of_psp43 charP_two_of_card toPGL_surjective_of_charTwo)
open CFSG.ComponentClassification.AutL2Facts (autEquiv autEquiv_conj incl_apply)

theorem prime_of_isChevSimple {p : ℕ} (hp2 : p ≠ 2) {S : Type} [Group S] (h : IsChevSimple p S) :
    p.Prime := by
  rcases h with ⟨i, hi, -⟩ | ⟨i, hi, -⟩
  · cases i with
    | lie d =>
      have hd : d.1.characteristic = p := hi
      exact hd ▸ TauCeti.LieTypeIndex.characteristic_prime d.1
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | lie d =>
      obtain ⟨rfl, -⟩ := ambiguousChev_lie_odd hp2 hi
      exact Nat.prime_three
    | alternating n hn =>
      simp only [ambiguousChev] at hi
      rcases hi with ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩
      · exact absurd h hp2
      · rw [h]; exact Nat.prime_five
      · exact absurd h hp2
      · rw [h]; exact Nat.prime_three
      · exact absurd h hp2
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

theorem card_le_three_of_l2Eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    {S : Type} [Group S] (e : S ≃* CFSG.GorensteinWalter.PSL2 F) {D : Subgroup (MulAut S)}
    (hDI : D ⊓ innerAut S = ⊥) : Nat.card D ≤ 3 := by
  haveI : CharP F 2 := charP_two_of_card hF
  let ρ : ↥D →* (F ≃+* F) :=
    SemidirectProduct.rightHom.comp ((autEquiv e).toMonoidHom.comp D.subtype)
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hinl : autEquiv e (d : MulAut S) =
        SemidirectProduct.inl (autEquiv e (d : MulAut S)).left := SemidirectProduct.ext rfl hd
    obtain ⟨u, hu⟩ := toPGL_surjective_of_charTwo (autEquiv e (d : MulAut S)).left
    have h1 : autEquiv e (d : MulAut S) = autEquiv e (MulAut.conj (e.symm u)) := by
      rw [autEquiv_conj, MulEquiv.apply_symm_apply, incl_apply, hu]
      exact hinl
    have h2 : (d : MulAut S) ∈ D ⊓ innerAut S :=
      ⟨d.2, ⟨e.symm u, ((autEquiv e).injective h1).symm⟩⟩
    rw [hDI, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  calc Nat.card D ≤ Nat.card (F ≃+* F) := Nat.card_le_card_of_injective ρ hρ
    _ = 3 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hF).1


theorem coreFree_outer_simple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hChev : IsChevSimple p S)
    (h27 : ¬ (p = 3 ∧ catalogIs S (onLie (isL2 27))))
    {D : Subgroup (MulAut S)} (hD : CFSG.Open.IsElemAbelian p D) (hD1 : D ≠ ⊥)
    (hDI : D ⊓ innerAut S = ⊥) :
    GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer (D : Set (MulAut S))) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut S) := finite_mulAut S
  obtain ⟨⟨d, hdD⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hdp : d ^ p = 1 := hD.2 d hdD
  have hdord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hdI : d ∉ innerAut S := fun h => by
    have hmem : d ∈ D ⊓ innerAut S := ⟨hdD, h⟩
    rw [hDI, Subgroup.mem_bot] at hmem
    exact hd1 hmem
  have hDp : IsPGroup p D := fun g => ⟨1, Subtype.ext (by simpa using hD.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hDp
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hD1 (Subgroup.eq_bot_of_card_eq D hk)
  have hcyc : k = 1 →
      GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer (D : Set (MulAut S))) = ⊥ := by
    intro hk1
    have hDeq : D = Subgroup.zpowers d :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
        (by rw [Nat.card_zpowers, hdord, hk, hk1, pow_one])).symm
    rw [hDeq, centralizer_zpowers_eq]
    refine coreFree_cyc_simple hp hp2 hS hnc hChev hdord le_rfl ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.2 (innerAut_normal S)]
      exact Subgroup.mem_top d
    · rintro ⟨h3, hL, -⟩
      exact h27 ⟨h3, hL⟩
  rcases hChev with hL | hAmb
  · obtain ⟨idx, hidx, hch⟩ := CFSG.HardMathSupport.Dickson.I271.lieType_of_catalogIs hL
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have hdvd : p ^ 3 ∣ Nat.card D := by
        rw [hk]
        exact Nat.pow_dvd_pow p hk3
      obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
      have hEel : CFSG.Open.IsElemAbelian p (E.map D.subtype) :=
        hD.mono (Subgroup.map_subtype_le E)
      have hEcard : Nat.card (E.map D.subtype) = p ^ 3 := by
        rw [Subgroup.card_map_of_injective D.subtype_injective, hE]
      obtain ⟨x, ⟨hxE, hxI⟩, hx1⟩ := CFSG.HardMathSupport.Timmesfeld.DefChar.lieOuterRank_proved S
        hS hnc idx hidx p hp hp2 _ hEel hEcard
      have hmem : x ∈ D ⊓ innerAut S := ⟨Subgroup.map_subtype_le E hxE, hxI⟩
      rw [hDI, Subgroup.mem_bot] at hmem
      exact hx1 hmem
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    interval_cases k
    · exact hcyc rfl
    · refine coreFree_rankTwo_lie hp hp2 hS hnc idx hidx hch ?_ hD hk hDI
      rintro ⟨h3, hL'⟩
      exact h27 ⟨h3, ys03_catalogIs_of_isL227 hL'⟩
  · obtain ⟨i, hi, ⟨e⟩⟩ := hAmb
    cases i with
    | alternating n hn =>
      exfalso
      have hn5 : 5 ≤ n := by
        simp only [ambiguousChev] at hi
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
      exact hdI (mem_innerAut_of_congr e (mem_innerAut_of_not_dvd hp
        (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2)
        (by rw [← map_pow, hdp, map_one])))
    | lie idx =>
      obtain ⟨hp3, hidx⟩ := ambiguousChev_lie_odd hp2 hi
      subst hp3
      obtain ⟨dd, hv⟩ := idx
      rcases hidx with ⟨q, hq, hq8⟩ | ⟨q, hq, hq2⟩
      ·
        simp only at hq
        subst hq
        obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := l2Eight_of_catalog hq8 e
        have h3 := card_le_three_of_l2Eight hF e' hDI
        rw [hk] at h3
        have hle : 3 ^ k ≤ 3 ^ 1 := by rw [pow_one]; exact h3
        have hk1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
        exact hcyc (by omega)
      ·
        simp only at hq
        subst hq
        exact absurd (mem_innerAut_of_psp43 (psp43_model_of_twistedA hq2 e) hdp) hdI
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

theorem i196OuterCore_holds : ∀ p : ℕ, I196OuterCore p := by
  intro p hp2 K _ _ hK hch D hDel hD1 hDI
  have hp : p.Prime := prime_of_isChevSimple hp2 hch
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) := finite_mulAut K
  by_cases h27 : p = 3 ∧ catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27))
  · exact Or.inr h27
  left
  have hφ : Function.Injective (Lemma123.autQ K) := Lemma123.autQ_injective hK.1
  refine coreFree_of_autQ hK.1 p (innerAut K) D ?_
  rw [map_autQ_innerAut]
  refine coreFree_outer_simple hp hp2 hK.2 (nonabelian_centerQuot hK) hch h27 (hDel.map _) ?_ ?_
  · intro h
    exact hD1 ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h)
  · rw [eq_bot_iff]
    rintro _ ⟨⟨d, hd, rfl⟩, hdI⟩
    rw [← map_autQ_innerAut] at hdI
    obtain ⟨c, hc, hcd⟩ := hdI
    have hmem : d ∈ D ⊓ innerAut K := ⟨hd, (hφ hcd) ▸ hc⟩
    rw [hDI, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
    exact Subgroup.one_mem _

end CFSG.LocalAnalysis.GLTheoremA.H196OC

end
