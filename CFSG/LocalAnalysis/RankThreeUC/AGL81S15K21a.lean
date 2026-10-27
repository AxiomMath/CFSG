module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall
public import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open KFactsSmall
open scoped Pointwise
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom centerQuotientHom_injective onCenterQuotient onCenterQuotient_apply_mk)

namespace K21aProof

theorem cqh_conj {G : Type} [Group G] (g : G) :
    centerQuotientHom G (MulAut.conj g) = MulAut.conj (QuotientGroup.mk' (Subgroup.center G) g) := by
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  change onCenterQuotient (MulAut.conj g) (QuotientGroup.mk' (Subgroup.center G) h) = _
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem ker_conj_eq_center (G : Type) [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg := congrArg (fun φ : MulAut G => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g, mul_inv_cancel_right]

noncomputable def innIso (G : Type) [Group G] : (G ⧸ Subgroup.center G) ≃* innAut G :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center G)).symm.trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : G →* MulAut G))

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem no72_alt6 (H : Subgroup (alternatingGroup (Fin 6))) : Nat.card H ≠ 72 := by
  intro hH
  have hidx : H.index = 5 := by
    have h := Subgroup.card_mul_index (H := H)
    rw [hH, card_alt6] at h
    omega
  have hcard : Nat.card (alternatingGroup (Fin 6) ⧸ H) = 5 := hidx
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let φ : alternatingGroup (Fin 6) →* Equiv.Perm (alternatingGroup (Fin 6) ⧸ H) :=
    MulAction.toPermHom _ _
  have hker : φ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have htop : H = ⊤ := by
        rw [eq_top_iff]
        intro g _
        have hg : φ g = 1 := by
          have : g ∈ φ.ker := by rw [h]; exact Subgroup.mem_top g
          exact this
        have h1 : (QuotientGroup.mk (g * 1) : alternatingGroup (Fin 6) ⧸ H) =
            QuotientGroup.mk 1 := by
          have := congrArg (fun σ : Equiv.Perm (alternatingGroup (Fin 6) ⧸ H) =>
            σ (QuotientGroup.mk 1)) hg
          exact this
        have h2 := QuotientGroup.eq.mp h1
        simpa using H.inv_mem h2
      have hc : Nat.card H = 360 := by rw [htop, Subgroup.card_top, card_alt6]
      omega
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hle := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_perm, hcard, card_alt6] at hle
  norm_num [Nat.factorial] at hle

theorem no72_of_mulEquiv {G : Type} [Group G] (ι : G ≃* alternatingGroup (Fin 6))
    (H : Subgroup G) : Nat.card H ≠ 72 := by
  intro h
  apply no72_alt6 (H.map ι.toMonoidHom)
  rw [Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective]
  exact h

theorem factorization_360 : Nat.factorization 360 2 = 3 := by
  have h1 : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
  rw [h1, Nat.factorization_mul (show (2 : ℕ) ^ 3 ≠ 0 by norm_num)
    (show (45 : ℕ) ≠ 0 by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 ∣ 45) by norm_num)]
  simp

def prodSub {G : Type} [Group G] (E P : Subgroup G)
    (h : ∀ p ∈ P, ∀ e ∈ E, ∃ e' ∈ E, ∃ p' ∈ P, p * e = e' * p') : Subgroup G where
  carrier := {g | ∃ e ∈ E, ∃ p ∈ P, g = e * p}
  one_mem' := ⟨1, E.one_mem, 1, P.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨e1, he1, p1, hp1, rfl⟩ ⟨e2, he2, p2, hp2, rfl⟩
    obtain ⟨e', he', p', hp', hpe⟩ := h p1 hp1 e2 he2
    refine ⟨e1 * e', E.mul_mem he1 he', p' * p2, P.mul_mem hp' hp2, ?_⟩
    rw [show e1 * p1 * (e2 * p2) = e1 * (p1 * e2) * p2 by group, hpe]
    group
  inv_mem' := by
    rintro _ ⟨e, he, p, hp, rfl⟩
    obtain ⟨e', he', p', hp', hpe⟩ := h p⁻¹ (P.inv_mem hp) e⁻¹ (E.inv_mem he)
    exact ⟨e', he', p', hp', by rw [mul_inv_rev, hpe]⟩

theorem le_prodSub_left {G : Type} [Group G] (E P : Subgroup G)
    (h : ∀ p ∈ P, ∀ e ∈ E, ∃ e' ∈ E, ∃ p' ∈ P, p * e = e' * p') :
    E ≤ prodSub E P h :=
  fun e he => ⟨e, he, 1, P.one_mem, (mul_one e).symm⟩

theorem le_prodSub_right {G : Type} [Group G] (E P : Subgroup G)
    (h : ∀ p ∈ P, ∀ e ∈ E, ∃ e' ∈ E, ∃ p' ∈ P, p * e = e' * p') :
    P ≤ prodSub E P h :=
  fun p hp => ⟨1, E.one_mem, p, hp, (one_mul p).symm⟩

theorem card_prodSub {G : Type} [Group G] (E P : Subgroup G)
    (h : ∀ p ∈ P, ∀ e ∈ E, ∃ e' ∈ E, ∃ p' ∈ P, p * e = e' * p')
    (hE : Nat.card E = 9) (hP : Nat.card P = 8) : Nat.card (prodSub E P h) = 72 := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  let f : E × P → prodSub E P h := fun q => ⟨q.1.1 * q.2.1, q.1.1, q.1.2, q.2.1, q.2.2, rfl⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, e, he, p, hp, rfl⟩
    exact ⟨(⟨e, he⟩, ⟨p, hp⟩), rfl⟩
  haveI : Finite (prodSub E P h) := Finite.of_surjective f hsurj
  have hle : Nat.card (prodSub E P h) ≤ 72 := by
    have := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, hE, hP] at this
    exact this
  have h9 : Nat.card E ∣ Nat.card (prodSub E P h) :=
    Subgroup.card_dvd_of_le (le_prodSub_left E P h)
  have h8 : Nat.card P ∣ Nat.card (prodSub E P h) :=
    Subgroup.card_dvd_of_le (le_prodSub_right E P h)
  rw [hE] at h9
  rw [hP] at h8
  have hd : 9 * 8 ∣ Nat.card (prodSub E P h) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h8
  have hpos : 0 < Nat.card (prodSub E P h) := Nat.card_pos
  obtain ⟨c, hc⟩ := hd
  omega

theorem mem_inn_of_mem {Jh : Type} [Group Jh] (hQ : CFSG.Open.IsQuasisimple Jh)
    (f : (Jh ⧸ Subgroup.center Jh) ≃* alternatingGroup (Fin 6))
    (E : Subgroup (MulAut Jh)) (hE : Nat.card E = 9) (x : MulAut Jh) (hx : x ∈ E) :
    x ∈ innAut Jh := by
  haveI : Group.IsPerfect Jh := ⟨hQ.1⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hx9 : x ^ 9 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : E))
    rw [hE] at h
    simpa using congrArg Subtype.val h
  have hσ : ∃ k : ℕ, centerQuotientHom Jh x ^ 3 ^ k = 1 :=
    ⟨2, by rw [← map_pow]; norm_num [hx9]⟩
  have hY : ∀ τ : MulAut (alternatingGroup (Fin 6)), (∃ k : ℕ, τ ^ 3 ^ k = 1) →
      ∃ y : alternatingGroup (Fin 6), τ = MulAut.conj y := by
    intro τ hτ
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp
      (CFSG.RankThree.PartTwo.KFacts.mem_range_conj_alternatingGroup_six hτ)
    exact ⟨y, hy.symm⟩
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_of_mulEquiv f hY _ hσ
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Jh) s
  have hjx : MulAut.conj j = x :=
    centerQuotientHom_injective Jh (by rw [cqh_conj]; exact hs.symm)
  show x ∈ (MulAut.conj : Jh →* MulAut Jh).range
  exact MonoidHom.mem_range.mpr ⟨j, hjx⟩

theorem caseA {Jh : Type} [Group Jh] (hQ : CFSG.Open.IsQuasisimple Jh)
    (f : (Jh ⧸ Subgroup.center Jh) ≃* alternatingGroup (Fin 6))
    (E T' : Subgroup (MulAut Jh)) (hE : Nat.card E = 9)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut Jh) (innAut Jh))
    (hPerm : Permutable E T') : False := by
  have hEinn : ∀ x ∈ E, x ∈ innAut Jh := fun x hx => mem_inn_of_mem hQ f E hE x hx
  have hPerm' : (E : Set (MulAut Jh)) * (T' : Set (MulAut Jh)) =
      (T' : Set (MulAut Jh)) * (E : Set (MulAut Jh)) := hPerm
  have hPE : ∀ p ∈ T' ⊓ innAut Jh, ∀ e ∈ E, ∃ e' ∈ E, ∃ p' ∈ T' ⊓ innAut Jh,
      p * e = e' * p' := by
    intro p hp e he
    have h1 : p * e ∈ (E : Set (MulAut Jh)) * (T' : Set (MulAut Jh)) := by
      rw [hPerm']
      exact ⟨p, (Subgroup.mem_inf.mp hp).1, e, he, rfl⟩
    obtain ⟨e', he', t, ht, hpe⟩ := h1
    have ht' : t = e'⁻¹ * (p * e) := by rw [← hpe, inv_mul_cancel_left]
    have hti : t ∈ innAut Jh := by
      rw [ht']
      exact (innAut Jh).mul_mem ((innAut Jh).inv_mem (hEinn e' he'))
        ((innAut Jh).mul_mem (Subgroup.mem_inf.mp hp).2 (hEinn e he))
    exact ⟨e', he', t, Subgroup.mem_inf.mpr ⟨ht, hti⟩, hpe.symm⟩
  have hKcard : Nat.card (innAut Jh) = 360 := by
    rw [Nat.card_congr (innIso Jh).symm.toEquiv, Nat.card_congr f.toEquiv, card_alt6]
  haveI : Finite (innAut Jh) := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQeq⟩ := hSyl
  have hPcard : Nat.card (T' ⊓ innAut Jh : Subgroup (MulAut Jh)) = 8 := by
    rw [← hQeq, Subgroup.card_map_of_injective (innAut Jh).subtype_injective]
    have hQc := Sylow.card_eq_multiplicity Q
    rw [hKcard, factorization_360] at hQc
    exact hQc
  have hUle : prodSub E (T' ⊓ innAut Jh) hPE ≤ innAut Jh := by
    intro g hg
    obtain ⟨e, he, p, hp, rfl⟩ := hg
    exact (innAut Jh).mul_mem (hEinn e he) (Subgroup.mem_inf.mp hp).2
  have hUcard := card_prodSub E (T' ⊓ innAut Jh) hPE hE hPcard
  have hsub : Nat.card ((prodSub E (T' ⊓ innAut Jh) hPE).subgroupOf (innAut Jh)) = 72 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv, hUcard]
  exact no72_of_mulEquiv ((innIso Jh).symm.trans f) _ hsub

theorem caseB {Jh : Type} [Group Jh] (hQ : CFSG.Open.IsQuasisimple Jh)
    (hL : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo
      (Jh ⧸ Subgroup.center Jh))
    (E : Subgroup (MulAut Jh)) (hE : Nat.card E = 9) : False := by
  haveI : Group.IsPerfect Jh := ⟨hQ.1⟩
  obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.nonempty_mulEquiv_GL_of_isLThreeTwo hL
  have hcard1 : Nat.card (E.map (centerQuotientHom Jh)) = 9 := by
    rw [Subgroup.card_map_of_injective (centerQuotientHom_injective Jh), hE]
  have hdvd := Subgroup.card_subgroup_dvd_card (E.map (centerQuotientHom Jh))
  rw [hcard1, Nat.card_congr (MulAut.congr e).toEquiv,
    CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32] at hdvd
  norm_num at hdvd

end K21aProof

theorem K21a_holds : K21a := by
  intro Jh _ _ hQ hS E T' hE hSyl hPerm
  rcases hS with hN | hL
  · obtain ⟨f⟩ := hN
    exact K21aProof.caseA hQ f E T' hE hSyl hPerm
  · exact K21aProof.caseB hQ hL E hE

end CFSG.LocalAnalysis.RankThreeUC.S15
