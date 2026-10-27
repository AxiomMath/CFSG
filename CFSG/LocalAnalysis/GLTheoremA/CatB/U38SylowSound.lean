module

public import Certificates.Data.HuppertU38Q.Check
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KD26dRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 U38Sylow

theorem exists_eq_mul_of_complement {G : Type*} [Group G] [Finite G] {Q X E : Subgroup G}
    (hEQ : E ≤ Q) (hEX : ∀ x ∈ E, x ∈ X → x = 1) {T : Finset G}
    (hTS : ∀ t ∈ T, t ∈ Q ∧ t ∈ X) (hT : T.card = 81) (hQ : Nat.card Q = 729)
    (hE : Nat.card E = 9) : ∀ q ∈ Q, ∃ e ∈ E, ∃ t ∈ T, e = q * t := by
  classical
  haveI := Fintype.ofFinite G
  set S : Subgroup G := Q ⊓ X with hS
  let f : E × S → Q := fun p => ⟨(p.1 : G) * (p.2 : G), Q.mul_mem (hEQ p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨e, s⟩ ⟨e', s'⟩ hee
    have h1 : (e : G) * s = e' * s' := congrArg Subtype.val hee
    have h2 : (e' : G)⁻¹ * e = s' * (s : G)⁻¹ := by
      calc (e' : G)⁻¹ * e = (e' : G)⁻¹ * (e * s) * (s : G)⁻¹ := by group
        _ = (e' : G)⁻¹ * (e' * s') * (s : G)⁻¹ := by rw [h1]
        _ = s' * (s : G)⁻¹ := by group
    have h3 : (e' : G)⁻¹ * e = 1 := by
      apply hEX
      · exact E.mul_mem (E.inv_mem e'.2) e.2
      · rw [h2]
        exact X.mul_mem s'.2.2 (X.inv_mem s.2.2)
    have h4 : (e : G) = e' := by
      have := h3
      rw [inv_mul_eq_one] at this
      exact this.symm
    have h5 : (s : G) = s' := by
      rw [h4] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have hcard : 9 * Nat.card S ≤ 729 := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, hE, hQ] at this
  have hTle : T.card ≤ Nat.card S := by
    let g : T → S := fun t => ⟨(t : G), (hTS t t.2).1, (hTS t t.2).2⟩
    have hg : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa [g] using this
    have := Nat.card_le_card_of_injective g hg
    simpa [Nat.card_eq_fintype_card] using this
  have hS81 : Nat.card S = 81 := by omega
  have hTall : ∀ s ∈ S, s ∈ T := by
    let Sfin : Finset G := Finset.univ.filter (· ∈ S)
    have hSfin : Sfin.card = Nat.card S := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsub : T ⊆ Sfin := fun t ht => by
      simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hTS t ht).1, (hTS t ht).2⟩
    have heq : T = Sfin := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro s hs
    rw [heq]
    simpa [Sfin] using hs
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [Nat.card_prod, hE, hS81, hQ])
  intro q hq
  obtain ⟨⟨e, s⟩, hes⟩ := hbij.2 ⟨q, hq⟩
  have h1 : (e : G) * s = q := congrArg Subtype.val hes
  refine ⟨e, e.2, (s : G)⁻¹, hTall _ (S.inv_mem s.2), ?_⟩
  rw [← h1]
  group

section Cover


theorem meets_X_of_cover {pts : Array (Array ℕ)} {Q : Subgroup (Equiv.Perm (Fin 513))}
    {nIdx : List ℕ} {r₁ r₂ : Array ℕ}
    (hval : ∀ i < pts.size, validA 513 pts[i]! = true)
    (hmem : ∀ x, x ∈ Q ↔ ∃ i < pts.size, permOfArr 513 pts[i]! = x)
    (hQ : Nat.card Q = 729) (hsz : pts.size = 729)
    (hnIdx : ∀ i ∈ nIdx, i < pts.size ∧
      siftA 513 (rawLevels 513 strong3 base3) base3 0 pts[i]! = true)
    (hnd : nIdx.Nodup) (hlen : nIdx.length = 81)
    (hr₁ : validA 513 r₁ = true) (hr₁Q : permOfArr 513 r₁ ∈ Q)
    (hr₂ : validA 513 r₂ = true) (hr₂Q : permOfArr 513 r₂ ∈ Q)
    (hnc : noCommuting (cosetCubes r₁ pts nIdx) (cosetCubes r₂ pts nIdx) = true)
    {E : Subgroup (Equiv.Perm (Fin 513))} (hEQ : E ≤ Q) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) : ∃ x ∈ E, x ≠ 1 ∧ x ∈ X' := by
  classical
  by_contra hcon
  push Not at hcon
  have hEX : ∀ x ∈ E, x ∈ X' → x = 1 := fun x hx hX => by
    by_contra hne
    exact hcon x hx hne hX
  let pt : ℕ → Equiv.Perm (Fin 513) := fun i => permOfArr 513 pts[i]!
  have hF : Function.Surjective
      (fun i : Fin pts.size => (⟨pt i, (hmem _).2 ⟨i, i.2, rfl⟩⟩ : Q)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    exact ⟨⟨i, hi⟩, rfl⟩
  have hFb := hF.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hQ, hsz])
  have hinj : ∀ i < pts.size, ∀ j < pts.size, pt i = pt j → i = j := by
    intro i hi j hj h
    exact congrArg Fin.val (hFb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h))
  let T : Finset (Equiv.Perm (Fin 513)) := nIdx.toFinset.image pt
  have hT : T.card = 81 := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
    intro i hi j hj h
    exact hinj i (hnIdx i (by simpa using hi)).1 j (hnIdx j (by simpa using hj)).1 h
  have hTS : ∀ t ∈ T, t ∈ Q ∧ t ∈ X' := by
    intro t ht
    simp only [T, Finset.mem_image, List.mem_toFinset] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    obtain ⟨hlt, hsift⟩ := hnIdx i hi
    exact ⟨(hmem _).2 ⟨i, hlt, rfl⟩, sift3_mem (rep_of_validA (hval i hlt)) hsift⟩
  have key := exists_eq_mul_of_complement hEQ hEX hTS hT hQ hcard
  have hcube : ∀ {r : Array ℕ}, validA 513 r = true → permOfArr 513 r ∈ Q →
      ∃ a ∈ cosetCubes r pts nIdx, ∃ e ∈ E, Rep 513 a e := by
    intro r hr hrQ
    obtain ⟨e, he, t, ht, hee⟩ := key _ hrQ
    simp only [T, Finset.mem_image, List.mem_toFinset] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    obtain ⟨hlt, -⟩ := hnIdx i hi
    have ha : Rep 513 (compA 513 r pts[i]!) e := by
      rw [hee]
      exact rep_compA (rep_of_validA hr) (rep_of_validA (hval i hlt))
    refine ⟨compA 513 r pts[i]!, ?_, e, he, ha⟩
    unfold cosetCubes
    rw [List.mem_filter]
    refine ⟨List.mem_map.2 ⟨i, hi, rfl⟩, ?_⟩
    unfold cubeOne
    exact (eqA_iff (rep_compA ha (rep_compA ha ha)) rep_idA).2
      ((pow_three e).symm.trans (hE.2 e he))
  obtain ⟨a₁, ha₁, e₁, he₁, hra₁⟩ := hcube hr₁ hr₁Q
  obtain ⟨a₂, ha₂, e₂, he₂, hra₂⟩ := hcube hr₂ hr₂Q
  have hcomm : e₁ * e₂ = e₂ * e₁ := by
    have := hE.1.1.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    simpa using congrArg Subtype.val this
  have hfalse := List.all_eq_true.1 (List.all_eq_true.1 hnc a₁ ha₁) a₂ ha₂
  rw [Bool.not_eq_true'] at hfalse
  have htrue : eqA 513 (compA 513 a₁ a₂) (compA 513 a₂ a₁) = true :=
    (eqA_iff (rep_compA hra₁ hra₂) (rep_compA hra₂ hra₁)).2 hcomm
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

end Cover

section Sylow


@[expose] noncomputable def U38Q : Subgroup (Equiv.Perm (Fin 513)) :=
  Subgroup.closure (permsA 513 qGens)

theorem u38SylowMeetsX_of_check (h : u38SylowCheck () = true) : U38SylowMeetsX := by
  classical
  simp only [u38SylowCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨henum, hsize⟩, hsift⟩, hN⟩, hnc⟩ := h
  have hps : ∀ p ∈ keyPts, p < 513 := by
    intro p hp
    simp [keyPts, base1, base1L] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hgens : ∀ k < qGens.size, validA 513 qGens[k]! = true := fun k hk => enumOK_gens_valid henum hk
  have hQ : Nat.card U38Q = 729 := by
    change Nat.card (Subgroup.closure (permsA 513 qGens)) = 729
    rw [hcard, hsize]
  have hQΓ : U38Q ≤ U38G := by
    rw [U38Q, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact mem_U38G_of_sift1 (hgens k hk) (allLt_spec hsift hk)
  have hsz3 : qGens.size = 3 := by simp [qGens]
  have hnIdx : ∀ i ∈ inX (qCert ()).pts (rawLevels 513 strong3 base3), i < (qCert ()).pts.size ∧
      siftA 513 (rawLevels 513 strong3 base3) base3 0 (qCert ()).pts[i]! = true := by
    intro i hi
    simp only [inX, List.mem_filter, List.mem_range] at hi
    exact ⟨hi.1, hi.2⟩
  have hnd : (inX (qCert ()).pts (rawLevels 513 strong3 base3)).Nodup :=
    (List.nodup_range).filter _
  have hcover := fun {E : Subgroup (Equiv.Perm (Fin 513))} (hEQ : E ≤ U38Q) (hE : IsElemAbelian 3 E)
      (hE9 : Nat.card E = 9) =>
    meets_X_of_cover (Q := U38Q) (hval := hval) (hmem := hmem) hQ hsize hnIdx hnd hN
      (hgens 0 (by omega)) (Subgroup.subset_closure ⟨0, by rw [Set.mem_setOf_eq, hsz3]; omega, rfl⟩)
      (hgens 1 (by omega)) (Subgroup.subset_closure ⟨1, by rw [Set.mem_setOf_eq, hsz3]; omega, rfl⟩) hnc hEQ hE hE9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Qs : Subgroup U38G := U38Q.subgroupOf U38G
  have hQs : Nat.card Qs = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv, hQ]
    norm_num
  have hindex : ¬ 3 ∣ Qs.index := by
    have h1 := Subgroup.card_mul_index Qs
    rw [hQs, card_U38G] at h1
    have h2 : Qs.index = 136192 := by omega
    rw [h2]
    decide
  refine ⟨(IsPGroup.of_card hQs).toSylow hindex, ?_⟩
  intro E hEQ hE hE9
  have hE'Q : E.map U38G.subtype ≤ U38Q := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hEQ he)
  have hE'ab : IsElemAbelian 3 (E.map U38G.subtype) := hE.map U38G.subtype
  have hE'card : Nat.card (E.map U38G.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective U38G), hE9]
  obtain ⟨x, hx, hx1, hxX⟩ := hcover hE'Q hE'ab hE'card
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  exact ⟨y, hy, fun h1 => hx1 (by rw [h1]; rfl), hxX⟩

end Sylow

end CFSG.LocalAnalysis.GLTheoremA.CatB
