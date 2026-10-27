module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSL
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ro

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore


private theorem betaHom_inclusion_eq_conj {Y : Type} [Group Y] {E : Subgroup Y}
    {P : Type} [Group P] (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) (d' : ↥E) :
    betaHom e' (Subgroup.inclusion (Subgroup.le_normalizer (H := E)) d') =
      MulAut.conj (e' (QuotientGroup.mk d')) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨q, rfl⟩ := e'.surjective z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [betaHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

private theorem isMulCommutative_closure_union_of_commute {N : Type} [Group N]
    {H : Subgroup N} [IsMulCommutative H] {u : N} (hu : ∀ x ∈ H, Commute u x) :
    IsMulCommutative (Subgroup.closure ((H : Set N) ∪ {u})) := by
  refine Subgroup.isMulCommutative_closure ?_
  intro a ha b hb _
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · exact Subgroup.mul_comm_of_mem_isMulCommutative (H := H) ha hb
  · exact (hu a ha).symm
  · exact hu b hb
  · exact Commute.refl _

private theorem commute_of_betaHom_eq_of_fixes {Y : Type} [Group Y] {E : Subgroup Y}
    {P : Type} [Group P] (e' : ↥E ⧸ Subgroup.center ↥E ≃* P)
    (hφ : Function.Injective fun d : ↥E => e' (QuotientGroup.mk d))
    {u : ↥(Subgroup.normalizer (E : Set Y))} {α : MulAut P} {D : Subgroup P}
    (hbu : betaHom e' u = α) (hα : ∀ t ∈ D, α t = t) {d : ↥E}
    (hd : e' (QuotientGroup.mk d) ∈ D) :
    Commute u (Subgroup.inclusion (Subgroup.le_normalizer (H := E)) d) := by
  have hnm : Subgroup.normalizerMonoidHom (H := E) u d = d := by
    apply hφ
    change e' (QuotientGroup.mk ((E.normalizerMonoidHom u) d)) =
      e' (QuotientGroup.mk d)
    rw [← betaHom_apply e' u d, hbu]
    exact hα _ hd
  have hval : ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y) * (d : Y) *
      ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y)⁻¹ = (d : Y) := by
    simpa using congrArg (fun z : ↥E => (z : Y)) hnm
  show u * Subgroup.inclusion (Subgroup.le_normalizer (H := E)) d =
    Subgroup.inclusion (Subgroup.le_normalizer (H := E)) d * u
  apply Subtype.ext
  change ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y) * (d : Y) =
    (d : Y) * ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y)
  calc ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y) * (d : Y)
      = ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y) * (d : Y) *
        ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y)⁻¹ *
        ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y) := by group
    _ = (d : Y) * ((u : ↥(Subgroup.normalizer (E : Set Y))) : Y) := by rw [hval]

private theorem exists_abelian_witness_of_generators {Y : Type} [Group Y] [Finite Y]
    {E : Subgroup Y} {P : Type} [Group P] [Finite P]
    (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {y : Y} {D : Subgroup P} {α : MulAut P}
    {u : ↥(Subgroup.normalizer (E : Set Y))}
    {H : Subgroup ↥(Subgroup.normalizer (E : Set Y))}
    (hH : IsMulCommutative H) (hcomm : ∀ x ∈ H, Commute u x)
    (hDle : D.map (MulAut.conj : P →* MulAut P) ≤ H.map (betaHom e'))
    (hbu : betaHom e' u = α)
    (hHE : H.map (Subgroup.normalizer (E : Set Y)).subtype ≤ E)
    (huE : (u : Y) ∈ E ⊔ Subgroup.zpowers y) :
    ∃ A : Subgroup ↥(Subgroup.normalizer (E : Set Y)),
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      D.map (MulAut.conj : P →* MulAut P) ⊔ Subgroup.zpowers α ≤ A.map (betaHom e') ∧
      A.map (Subgroup.normalizer (E : Set Y)).subtype ≤ E ⊔ Subgroup.zpowers y := by
  classical
  let N : Subgroup Y := Subgroup.normalizer (E : Set Y)
  let A : Subgroup ↥N := Subgroup.closure ((H : Set ↥N) ∪ {u})
  have hAc : IsMulCommutative A :=
    isMulCommutative_closure_union_of_commute (H := H) hcomm
  have hHA : H ≤ A :=
    Subgroup.subset_closure.trans (Subgroup.closure_mono (Set.subset_union_left))
  have hAle : D.map (MulAut.conj : P →* MulAut P) ⊔ Subgroup.zpowers α ≤
      A.map (betaHom e') := by
    refine sup_le (hDle.trans (Subgroup.map_mono hHA)) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨u, Subgroup.subset_closure (Or.inr rfl), hbu⟩
  have hAleY : A.map (Subgroup.normalizer (E : Set Y)).subtype ≤
      E ⊔ Subgroup.zpowers y := by
    change (Subgroup.closure ((H : Set ↥N) ∪ {u})).map N.subtype ≤ _
    rw [MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro z ⟨x, hx, rfl⟩
    rcases hx with hx | rfl
    · exact Subgroup.mem_sup_left (hHE (Subgroup.mem_map.2 ⟨x, hx, rfl⟩))
    · exact huE
  exact ⟨A, fun _ ha _ hb => Subgroup.mul_comm_of_mem_isMulCommutative (H := A) ha hb,
    hAle, hAleY⟩

private theorem exists_split_element_of_split {Y : Type} [Group Y] {E : Subgroup Y}
    {P : Type} [Group P] (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {y : Y}
    (hy : y ∈ Subgroup.normalizer (E : Set Y)) {s : P} {α : MulAut P}
    (hβ : betaHom e' ⟨y, hy⟩ = MulAut.conj s * α) :
    ∃ u : ↥(Subgroup.normalizer (E : Set Y)),
      betaHom e' u = α ∧ (u : Y) ∈ E ⊔ Subgroup.zpowers y := by
  classical
  let N : Subgroup Y := Subgroup.normalizer (E : Set Y)
  let φ : ↥E →* P := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))
  have hφsurj : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨st, hst⟩ : ∃ st : ↥E, φ st = s := hφsurj s
  let inc : ↥E →* ↥N := Subgroup.inclusion (Subgroup.le_normalizer (H := E))
  let stN : ↥N := inc st
  let yN : ↥N := ⟨y, hy⟩
  let uN : ↥N := stN⁻¹ * yN
  have hbst : betaHom e' stN = MulAut.conj s := by
    have hst' : e' (QuotientGroup.mk st) = s := hst
    have h := betaHom_inclusion_eq_conj e' st
    rwa [hst'] at h
  have hyb : betaHom e' yN = MulAut.conj s * α := hβ
  have hbu : betaHom e' uN = α := by
    have hdef : uN = stN⁻¹ * yN := rfl
    rw [hdef, map_mul, map_inv, hbst, hyb]
    group
  have huE : ((uN : ↥N) : Y) ∈ E ⊔ Subgroup.zpowers y := by
    change (st : Y)⁻¹ * y ∈ E ⊔ Subgroup.zpowers y
    exact Subgroup.mul_mem_sup (E.inv_mem st.2) (Subgroup.mem_zpowers y)
  exact ⟨uN, hbu, huE⟩

private theorem exists_preimage_commutative_generators {Y : Type} [Group Y] {E : Subgroup Y}
    (hZ : Subgroup.center ↥E = ⊥) {P : Type} [Group P]
    (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {D : Subgroup P}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {α : MulAut P}
    {u : ↥(Subgroup.normalizer (E : Set Y))} (hbu : betaHom e' u = α)
    (hα : ∀ t ∈ D, α t = t) :
    ∃ H : Subgroup ↥(Subgroup.normalizer (E : Set Y)),
      IsMulCommutative H ∧ (∀ x ∈ H, Commute u x) ∧
      D.map (MulAut.conj : P →* MulAut P) ≤ H.map (betaHom e') ∧
      H.map (Subgroup.normalizer (E : Set Y)).subtype ≤ E := by
  classical
  let N : Subgroup Y := Subgroup.normalizer (E : Set Y)
  let φ : ↥E →* P := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))
  have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥E) :
      ↥E →* ↥E ⧸ Subgroup.center ↥E) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hφinj : Function.Injective φ := e'.injective.comp hmk
  have hφsurj : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hDc : IsMulCommutative D :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hD a a.2 b b.2))
  let Dt : Subgroup ↥E := D.comap φ
  have hDtc : IsMulCommutative Dt := D.comap_injective_isMulCommutative hφinj
  let inc : ↥E →* ↥N := Subgroup.inclusion (Subgroup.le_normalizer (H := E))
  let DtN : Subgroup ↥N := Dt.map inc
  have hDtNc : IsMulCommutative DtN := Dt.map_isMulCommutative inc
  have hcomm : ∀ d : ↥E, d ∈ Dt → Commute u (inc d) := by
    intro d hd
    exact commute_of_betaHom_eq_of_fixes e' hφinj hbu hα hd
  have hcommN : ∀ x ∈ DtN, Commute u x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    exact hcomm d hd
  have hDle : D.map (MulAut.conj : P →* MulAut P) ≤ DtN.map (betaHom e') := by
    rintro γ ⟨d, hd, rfl⟩
    obtain ⟨d', rfl⟩ : ∃ d' : ↥E, φ d' = d := hφsurj d
    exact ⟨inc d', Subgroup.mem_map.2 ⟨d', hd, rfl⟩, betaHom_inclusion_eq_conj e' d'⟩
  have hDtNE : DtN.map N.subtype ≤ E := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    exact d.2
  exact ⟨DtN, hDtNc, hcommN, hDle, hDtNE⟩

private theorem exists_abelian_witness_of_split {Y : Type} [Group Y] [Finite Y]
    {E : Subgroup Y} (hZ : Subgroup.center ↥E = ⊥) {P : Type} [Group P] [Finite P]
    (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {y : Y}
    (hy : y ∈ Subgroup.normalizer (E : Set Y)) {s : P} {D : Subgroup P}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {α : MulAut P}
    (hβ : betaHom e' ⟨y, hy⟩ = MulAut.conj s * α) (hα : ∀ t ∈ D, α t = t) :
    ∃ A : Subgroup ↥(Subgroup.normalizer (E : Set Y)),
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      D.map (MulAut.conj : P →* MulAut P) ⊔ Subgroup.zpowers α ≤ A.map (betaHom e') ∧
      A.map (Subgroup.normalizer (E : Set Y)).subtype ≤ E ⊔ Subgroup.zpowers y := by
  obtain ⟨u, hbu, huE⟩ := exists_split_element_of_split e' hy hβ
  obtain ⟨H, hH, hcomm, hDle, hHE⟩ :=
    exists_preimage_commutative_generators hZ e' hD hbu hα
  exact exists_abelian_witness_of_generators e' hH hcomm hDle hbu hHE huE

theorem le_pRank_of_split {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y}
    (hZ : Subgroup.center ↥E = ⊥) {P : Type} [Group P] [Finite P]
    (e' : ↥E ⧸ Subgroup.center ↥E ≃* P) {y : Y} (hy : y ∈ Subgroup.normalizer (E : Set Y))
    {s : P} {D : Subgroup P} (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {α : MulAut P}
    (hβ : betaHom e' ⟨y, hy⟩ = MulAut.conj s * α) (hα : ∀ t ∈ D, α t = t) {p k : ℕ}
    (hp : p.Prime)
    (hk : k ≤ CFSG.Open.pRank p (D.map (MulAut.conj : P →* MulAut P) ⊔ Subgroup.zpowers α)) :
    k ≤ CFSG.Open.pRank p (E ⊔ Subgroup.zpowers y) := by
  classical
  obtain ⟨A, hAcomm, hAle, hAleY⟩ :=
    exists_abelian_witness_of_split hZ e' hy hD hβ hα
  exact hk.trans ((CFSG.SectionRank.pRank_mono hp.one_lt hAle).trans
    ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_pRank_map_le hp (betaHom e')
      hAcomm).trans
      ((CFSG.SectionRank.pRank_le_map hp.one_lt _ Subtype.coe_injective A).trans
        (CFSG.SectionRank.pRank_mono hp.one_lt hAleY))))

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore
