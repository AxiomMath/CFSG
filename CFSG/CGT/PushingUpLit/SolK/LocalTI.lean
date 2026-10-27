module

public import CFSG.CGT.PushingUpLit.SolK.FourA

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem conj_le_TOf_local (hT : TightData S) {a g : G}
    (hag : g⁻¹ * a * g ∈ pCoreOf 2 M) (hMa : ∀ k : G, k * a * k⁻¹ = a → k ∈ M)
    (hMq : ∀ k : G, k * (g⁻¹ * a * g) * k⁻¹ = g⁻¹ * a * g → k ∈ M) :
    conjSubgroup g (pCoreOf 2 M) ≤ TOf M a := by
  classical
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set q : G := g⁻¹ * a * g with hq
  have hU2 : IsPGroup 2 (conjSubgroup g Q) := (isPGroup_pCoreOf' M).map _
  have hUC : conjSubgroup g Q ≤
      M ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ Q := mem_conjSubgroup.1 hu
    have hcomm : u * a * u⁻¹ = a := by
      have h1 := hT.abelian _ hu' _ hag
      have h2 : u * a = a * u :=
        calc u * a = g * ((g⁻¹ * u * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * a * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
          _ = a * u := by group
      calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [h2]
        _ = a := by group
    exact Subgroup.mem_inf.2 ⟨hMa u hcomm, mem_centralizer_zpowers_iff.2 hcomm⟩
  have hnorm : ∀ k ∈ M ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G),
      ∀ u ∈ conjSubgroup g Q, k * u * k⁻¹ ∈ conjSubgroup g Q := by
    intro k hk u hu
    have hka : k * a * k⁻¹ = a := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
    have hkq : (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ = q := by
      calc (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * a * k⁻¹) * g := by rw [hq]; group
        _ = q := by rw [hka]
    have hk'M : g⁻¹ * k * g ∈ M := hMq _ hkq
    have hu' : g⁻¹ * u * g ∈ Q := mem_conjSubgroup.1 hu
    refine mem_conjSubgroup.2 ?_
    have e : g⁻¹ * (k * u * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * u * g) * (g⁻¹ * k * g)⁻¹ := by
      group
    rw [e]
    exact pCoreOf_normalized M hk'M hu'
  exact le_pCoreOf_of_normalized hUC hnorm hU2

theorem conj_eq_of_not_len_two_local (hT : TightData S) (hQe : QElem S) {g h : G}
    (hh : h ∈ pCoreOf 2 M) (hhg : g⁻¹ * h * g ∈ pCoreOf 2 M) (hlen : ¬ S.HasLen h 2)
    (hMh : ∀ k : G, k * h * k⁻¹ = h → k ∈ M)
    (hMq : ∀ k : G, k * (g⁻¹ * h * g) * k⁻¹ = g⁻¹ * h * g → k ∈ M) :
    conjSubgroup g (pCoreOf 2 M) = pCoreOf 2 M := by
  have hle : conjSubgroup g (pCoreOf 2 M) ≤ TOf M h := S.conj_le_TOf_local hT hhg hMh hMq
  have hcardg : Nat.card ↥(conjSubgroup g (pCoreOf 2 M)) = Nat.card ↥(pCoreOf 2 M) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨l, hl⟩ := S.exists_hasLen hh
  by_cases hl4 : l = 4
  · subst hl4
    obtain ⟨w, hw, r, hr, hhwr, hcard⟩ := hl
    subst hhwr
    obtain ⟨-, hEq⟩ := S.elem_le_of_len_four hT hw hr hcard hle (S.elemAbelian_conj hT hQe g)
    exact hEq hcardg
  · have hl2 : l ≠ 2 := fun h2 => hlen (h2 ▸ hl)
    have hTQ := S.pCoreOf_centralizer_le_of_len hT hl hl2 hl4
    exact Subgroup.eq_of_le_of_card_ge (hle.trans hTQ) hcardg.ge

@[expose] def HAway : Prop :=
  ∀ z ∈ pCoreOf 2 M, z ≠ 1 → ¬ S.HasLen z 2 → ∀ k : G, k * z * k⁻¹ = z → k ∈ M

noncomputable def suppQ (q : ↥(pCoreOf 2 M)) : Finset (Fin (2 * n + 1)) :=
  vsupp (S.D.β (projWFun S q))

theorem mem_suppQ {q : ↥(pCoreOf 2 M)} {i : Fin (2 * n + 1)} :
    i ∈ S.suppQ q ↔ vcoord (S.D.β (projWFun S q)) i = 1 := mem_vsupp

noncomputable def rpartQ (q : ↥(pCoreOf 2 M)) : ↥(rOf M X) :=
  ⟨(projWFun S q : G)⁻¹ * q, by
    obtain ⟨r, hr, h⟩ := projWFun_spec S q
    have : (projWFun S q : G)⁻¹ * q = r := by rw [h]; group
    rw [this]
    exact hr⟩

theorem eq_of_suppQ_rpartQ {q q' : ↥(pCoreOf 2 M)} (h1 : S.suppQ q = S.suppQ q')
    (h2 : S.rpartQ q = S.rpartQ q') : q = q' := by
  have hv : S.D.β (projWFun S q) = S.D.β (projWFun S q') := by
    refine vcoord_ext fun i => ?_
    have h3 : i ∈ vsupp (S.D.β (projWFun S q)) ↔ i ∈ vsupp (S.D.β (projWFun S q')) := by
      have := h1
      unfold suppQ at this
      rw [this]
    simp only [mem_vsupp] at h3
    generalize vcoord (S.D.β (projWFun S q)) i = a at h3 ⊢
    generalize vcoord (S.D.β (projWFun S q')) i = b at h3 ⊢
    revert a b
    decide
  have hw : projWFun S q = projWFun S q' := S.D.β.injective hv
  have hr : (projWFun S q : G)⁻¹ * q = (projWFun S q' : G)⁻¹ * q' := congrArg Subtype.val h2
  rw [hw] at hr
  exact Subtype.ext (mul_left_cancel hr)

theorem card_suppQ_of_hasLen {q : ↥(pCoreOf 2 M)} (h : S.HasLen (q : G) 2) :
    (S.suppQ q).card = 2 := by
  obtain ⟨w, hw, r, hr, hq, hcard⟩ := h
  have : (projWFun S q : G) = w := projWFun_eq S hw hr hq
  have h' : projWFun S q = ⟨w, hw⟩ := Subtype.ext this
  unfold suppQ
  rw [h']
  exact hcard
theorem hasLen_conj (hT : TightData S) (hQe : QElem S) (hA : S.HAway) {g h : G} (hg : g ∉ M)
    (hhQ : h ∈ pCoreOf 2 M) (hhg : g⁻¹ * h * g ∈ pCoreOf 2 M) (hh1 : h ≠ 1)
    (hlen : ¬ S.HasLen h 2) : S.HasLen (g⁻¹ * h * g) 2 := by
  by_contra hlen'
  have hh'1 : g⁻¹ * h * g ≠ 1 := by
    intro h'
    apply hh1
    have := congrArg (fun t => g * t * g⁻¹) h'
    simpa [mul_assoc] using this
  have hQg := S.conj_eq_of_not_len_two_local hT hQe hhQ hhg hlen
    (hA _ hhQ hh1 hlen) (hA _ hhg hh'1 hlen')
  apply hg
  refine S.mem_M_of_conj_Q (fun q hq => ?_) (fun q hq => ?_)
  · have : g * q * g⁻¹ ∈ conjSubgroup g (pCoreOf 2 M) := by
      refine mem_conjSubgroup.2 ?_
      have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
      rw [e]
      exact hq
    rwa [hQg] at this
  · have : q ∈ conjSubgroup g (pCoreOf 2 M) := by rwa [hQg]
    exact mem_conjSubgroup.1 this

theorem card_Q2_le :
    Nat.card {q : ↥(pCoreOf 2 M) // S.HasLen (q : G) 2} ≤
      (2 * n + 1).choose 2 * Nat.card ↥(rOf M X) := by
  let f : {q : ↥(pCoreOf 2 M) // S.HasLen (q : G) 2} →
      ↥((Finset.univ : Finset (Fin (2 * n + 1))).powersetCard 2) × ↥(rOf M X) := fun q =>
    (⟨S.suppQ q.1, Finset.mem_powersetCard.2
      ⟨Finset.subset_univ _, S.card_suppQ_of_hasLen q.2⟩⟩, S.rpartQ q.1)
  have hf : Function.Injective f := by
    intro q q' h
    have h1 : S.suppQ q.1 = S.suppQ q'.1 := congrArg Subtype.val (congrArg Prod.fst h)
    have h2 : S.rpartQ q.1 = S.rpartQ q'.1 := congrArg Prod.snd h
    exact Subtype.ext (S.eq_of_suppQ_rpartQ h1 h2)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card
    (α := ↥((Finset.univ : Finset (Fin (2 * n + 1))).powersetCard 2)), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem card_D2_le {D : Subgroup G} (hDQ : D ≤ pCoreOf 2 M) {i j : Fin (2 * n + 1)} (hij : i ≠ j)
    (hD : ∀ h : ↥D, (i ∈ S.suppQ ⟨h, hDQ h.2⟩ ↔ j ∈ S.suppQ ⟨h, hDQ h.2⟩)) :
    Nat.card {h : ↥D // S.HasLen (h : G) 2} ≤
      (1 + (2 * n + 1 - 2).choose 2) * Nat.card ↥(rOf M X) := by
  classical
  let Tset : Finset (Finset (Fin (2 * n + 1))) :=
    insert {i, j} (((Finset.univ : Finset (Fin (2 * n + 1))).erase i).erase j |>.powersetCard 2)
  have hTcard : Nat.card ↥Tset ≤ 1 + (2 * n + 1 - 2).choose 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    refine (Finset.card_insert_le _ _).trans ?_
    have h1 : ((((Finset.univ : Finset (Fin (2 * n + 1))).erase i).erase j)).card =
        2 * n + 1 - 2 := by
      rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      · omega
      · exact Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ _⟩
    rw [Finset.card_powersetCard, h1]
    omega
  have hmem : ∀ h : {h : ↥D // S.HasLen (h : G) 2}, S.suppQ ⟨h.1, hDQ h.1.2⟩ ∈ Tset := by
    intro h
    have hc : (S.suppQ ⟨h.1, hDQ h.1.2⟩).card = 2 :=
      S.card_suppQ_of_hasLen (q := ⟨h.1, hDQ h.1.2⟩) h.2
    by_cases hi : i ∈ S.suppQ ⟨h.1, hDQ h.1.2⟩
    · refine Finset.mem_insert.2 (Or.inl ?_)
      have hj : j ∈ S.suppQ ⟨h.1, hDQ h.1.2⟩ := (hD h.1).1 hi
      symm
      refine Finset.eq_of_subset_of_card_le ?_ (by rw [hc, Finset.card_pair hij])
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_powersetCard.2 ⟨fun x hx => ?_, hc⟩))
      have hj : j ∉ S.suppQ ⟨h.1, hDQ h.1.2⟩ := fun hj => hi ((hD h.1).2 hj)
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hxj => hj (hxj ▸ hx), fun hxi => hi (hxi ▸ hx)⟩
  let f : {h : ↥D // S.HasLen (h : G) 2} → ↥Tset × ↥(rOf M X) := fun h =>
    (⟨S.suppQ ⟨h.1, hDQ h.1.2⟩, hmem h⟩, S.rpartQ ⟨h.1, hDQ h.1.2⟩)
  have hf : Function.Injective f := by
    intro h h' hh
    have h1 : S.suppQ ⟨h.1, hDQ h.1.2⟩ = S.suppQ ⟨h'.1, hDQ h'.1.2⟩ :=
      congrArg Subtype.val (congrArg Prod.fst hh)
    have h2 : S.rpartQ ⟨h.1, hDQ h.1.2⟩ = S.rpartQ ⟨h'.1, hDQ h'.1.2⟩ := congrArg Prod.snd hh
    have h3 := S.eq_of_suppQ_rpartQ h1 h2
    have h4 : (h.1 : G) = (h'.1 : G) := by
      have := congrArg Subtype.val h3
      simpa using this
    exact Subtype.ext (Subtype.ext h4)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at this
  exact this.trans (Nat.mul_le_mul_right _ hTcard)

theorem card_le_of_conj_inter (hT : TightData S) (hQe : QElem S) (hA : S.HAway) {g : G}
    (hg : g ∉ M) {D : Subgroup G} (hDQ : D ≤ pCoreOf 2 M)
    (hDg : ∀ h ∈ D, g⁻¹ * h * g ∈ pCoreOf 2 M) :
    Nat.card ↥D ≤ Nat.card {h : ↥D // S.HasLen (h : G) 2} + 1 +
      Nat.card {q : ↥(pCoreOf 2 M) // S.HasLen (q : G) 2} := by
  classical
  have hsplit : Nat.card ↥D = Nat.card {h : ↥D // S.HasLen (h : G) 2} +
      Nat.card {h : ↥D // ¬ S.HasLen (h : G) 2} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl _).symm
  have hY : Nat.card {h : ↥D // ¬ S.HasLen (h : G) 2} =
      Nat.card {y : {h : ↥D // ¬ S.HasLen (h : G) 2} // ((y.1 : ↥D) : G) = 1} +
      Nat.card {y : {h : ↥D // ¬ S.HasLen (h : G) 2} // ¬ ((y.1 : ↥D) : G) = 1} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl _).symm
  have hY1 : Nat.card {y : {h : ↥D // ¬ S.HasLen (h : G) 2} // ((y.1 : ↥D) : G) = 1} ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    exact ⟨fun a b => Subtype.ext (Subtype.ext (Subtype.ext (a.2.trans b.2.symm)))⟩
  let f : {y : {h : ↥D // ¬ S.HasLen (h : G) 2} // ¬ ((y.1 : ↥D) : G) = 1} →
      {q : ↥(pCoreOf 2 M) // S.HasLen (q : G) 2} := fun y =>
    ⟨⟨g⁻¹ * ((y.1.1 : ↥D) : G) * g, hDg y.1.1 y.1.1.2⟩,
      S.hasLen_conj hT hQe hA hg (hDQ y.1.1.2) (hDg y.1.1 y.1.1.2) y.2 y.1.2⟩
  have hf : Function.Injective f := by
    intro y y' hh
    have h2 : g⁻¹ * ((y.1.1 : ↥D) : G) * g = g⁻¹ * ((y'.1.1 : ↥D) : G) * g :=
      congrArg Subtype.val (congrArg Subtype.val hh)
    have h3 : ((y.1.1 : ↥D) : G) = ((y'.1.1 : ↥D) : G) := by simpa using h2
    exact Subtype.ext (Subtype.ext (Subtype.ext h3))
  have h3 := Nat.card_le_card_of_injective f hf
  omega

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
