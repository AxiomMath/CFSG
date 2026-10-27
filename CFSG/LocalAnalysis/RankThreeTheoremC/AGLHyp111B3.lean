module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111DataBridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem le_centralizer_of_noTwo_of_normal (hNo2 : KFactCaseTwoNoTwo) {L : Subgroup Y} [L.Normal]
    (hL : IsCaseTwoGroup p L) {U : Subgroup Y} (hU : IsPGroup 2 U) {t : Y} (htL : t ∈ L)
    (htp : orderOf t = p) (htU : t ∈ Subgroup.normalizer (U : Set Y)) :
    U ≤ Subgroup.centralizer (L : Set Y) := by
  set V : Subgroup (MulAut L) := U.map (MulAut.conjNormal (H := L))
  have hV2 : IsPGroup 2 V := hU.map _
  have hconj : MulAut.conjNormal (H := L) t = MulAut.conj (⟨t, htL⟩ : L) := by
    ext k
    simp
  have hVn : MulAut.conj (⟨t, htL⟩ : L) ∈ Subgroup.normalizer (V : Set (MulAut L)) := by
    rw [← hconj]
    apply mem_normalizer_of_conj_map_le
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨t * u * t⁻¹, (Subgroup.mem_normalizer_iff.mp htU u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have htp' : orderOf (⟨t, htL⟩ : L) = p := by rw [Subgroup.orderOf_mk]; exact htp
  have hVbot := hNo2 p L hL _ htp' V hV2 hVn
  intro u hu
  have h1 : MulAut.conjNormal (H := L) u = 1 :=
    (Subgroup.map_eq_bot_iff _).mp hVbot hu
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : Y)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  conv_lhs => rw [← h2]
  group

theorem le_centralizer_of_noTwo (hNo2 : KFactCaseTwoNoTwo) {L : Subgroup Y}
    (hL : IsCaseTwoGroup p L) {U : Subgroup Y} (hU : IsPGroup 2 U)
    (hUN : U ≤ Subgroup.normalizer (L : Set Y)) {t : Y} (htL : t ∈ L) (htp : orderOf t = p)
    (htU : t ∈ Subgroup.normalizer (U : Set Y)) :
    U ≤ Subgroup.centralizer (L : Set Y) := by
  set N := Subgroup.normalizer (L : Set Y)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have : (L.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hL' : IsCaseTwoGroup p (L.subgroupOf N) := by
    obtain ⟨d, hd, ⟨e⟩⟩ := hL
    exact ⟨d, hd, ⟨(Subgroup.subgroupOfEquivOfLe hLN).trans e⟩⟩
  have hU' : IsPGroup 2 (U.subgroupOf N) := hU.comap_subtype
  have htN : t ∈ N := hLN htL
  have htU' : (⟨t, htN⟩ : N) ∈ Subgroup.normalizer ((U.subgroupOf N : Subgroup N) : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp htU x
  have hC := le_centralizer_of_noTwo_of_normal hNo2 hL' hU'
    (t := ⟨t, htN⟩) (Subgroup.mem_subgroupOf.mpr htL)
    (by rw [Subgroup.orderOf_mk]; exact htp) htU'
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := Subgroup.mem_centralizer_iff.mp (hC (Subgroup.mem_subgroupOf.mpr (show
    ((⟨u, hUN hu⟩ : N) : Y) ∈ U from hu))) ⟨l, hLN hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
  exact congrArg Subtype.val this

theorem le_normalizer_of_two (hNo2 : KFactCaseTwoNoTwo) (hp : p.Prime) {L₁ L₂ : Subgroup Y}
    (hconj : ∀ g : Y, L₁.map (MulAut.conj g).toMonoidHom = L₁ ∨
      L₁.map (MulAut.conj g).toMonoidHom = L₂)
    (hcomm : L₂ ≤ Subgroup.centralizer (L₁ : Set Y)) (hZ : Subgroup.center L₁ = ⊥)
    (hL : IsCaseTwoGroup p L₁) {U : Subgroup Y} (hU : IsPGroup 2 U) {t : Y} (htL : t ∈ L₁)
    (htp : orderOf t = p) (htU : t ∈ Subgroup.normalizer (U : Set Y)) :
    U ≤ Subgroup.normalizer (L₁ : Set Y) := by
  intro s hs
  rcases hconj s with h | h
  · apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [← h]
    exact ⟨n, hn, rfl⟩
  · exfalso
    set N := Subgroup.normalizer (L₁ : Set Y)
    have htN : t ∈ N := Subgroup.le_normalizer htL
    have hU₀ : IsPGroup 2 (U ⊓ N : Subgroup Y) := hU.to_le inf_le_left
    have htU₀ : t ∈ Subgroup.normalizer ((U ⊓ N : Subgroup Y) : Set Y) := by
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      exact ⟨(Subgroup.mem_normalizer_iff.mp htU n).mp hn.1,
        N.mul_mem (N.mul_mem htN hn.2) (N.inv_mem htN)⟩
    have hC := le_centralizer_of_noTwo hNo2 hL hU₀ inf_le_right htL htp htU₀
    have hsts : s * t * s⁻¹ ∈ L₂ := by rw [← h]; exact ⟨t, htL, rfl⟩
    have hsts' : s * t * s⁻¹ ∈ Subgroup.centralizer (L₁ : Set Y) := hcomm hsts
    have hcU : s * t * s⁻¹ * t⁻¹ ∈ U := by
      have h1 : t * s⁻¹ * t⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp htU s⁻¹).mp (U.inv_mem hs)
      have e : s * t * s⁻¹ * t⁻¹ = s * (t * s⁻¹ * t⁻¹) := by group
      rw [e]
      exact U.mul_mem hs h1
    have hcN : s * t * s⁻¹ * t⁻¹ ∈ N :=
      N.mul_mem (Subgroup.centralizer_le_normalizer (L₁ : Set Y) hsts') (N.inv_mem htN)
    have hc := hC ⟨hcU, hcN⟩
    have htC : t ∈ Subgroup.centralizer (L₁ : Set Y) := by
      have e : t = (s * t * s⁻¹ * t⁻¹)⁻¹ * (s * t * s⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hsts'
    have htZ : (⟨t, htL⟩ : L₁) ∈ Subgroup.center L₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htC g g.2)
    rw [hZ, Subgroup.mem_bot] at htZ
    have ht1 : t = 1 := congrArg Subtype.val htZ
    rw [ht1, orderOf_one] at htp
    exact hp.one_lt.ne htp

theorem le_centralizer_of_aut {L : Subgroup Y} [L.Normal] {T : Subgroup Y} (_hTL : T ≤ L)
    (hK : ∀ V : Subgroup (MulAut L), IsPGroup 2 V →
      (∀ x : L, (x : Y) ∈ T → MulAut.conj x ∈ Subgroup.normalizer (V : Set (MulAut L))) → V = ⊥)
    {U : Subgroup Y} (hU : IsPGroup 2 U) (hTU : T ≤ Subgroup.normalizer (U : Set Y)) :
    U ≤ Subgroup.centralizer (L : Set Y) := by
  set V : Subgroup (MulAut L) := U.map (MulAut.conjNormal (H := L))
  have hVbot : V = ⊥ := by
    refine hK V (hU.map _) fun x hx => ?_
    have hconj : MulAut.conjNormal (H := L) (x : Y) = MulAut.conj x := by
      ext k
      simp
    rw [← hconj]
    apply mem_normalizer_of_conj_map_le
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨(x : Y) * u * (x : Y)⁻¹, (Subgroup.mem_normalizer_iff.mp (hTU hx) u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  intro u hu
  have h1 : MulAut.conjNormal (H := L) u = 1 :=
    (Subgroup.map_eq_bot_iff _).mp hVbot hu
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : Y)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  conv_lhs => rw [← h2]
  group

end Abstract

section Local

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

abbrev imgBar (p : ℕ) (H S : Subgroup G) : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  (S.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

omit [Finite G] in
theorem b3_of_img (Q : Subgroup G) {J : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Q ≤ Subgroup.normalizer (S : Set G) →
      imgBar p H S ≤ Subgroup.centralizer (J : Set _)) :
    Hyp111B3 p H Q J := by
  intro S hS hSH hQS x hx
  exact ⟨⟨x, hSH hx⟩, hC S hS hSH hQS ⟨⟨x, hSH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩

theorem img_facts {Q S : Subgroup G} (hS : IsPGroup 2 S) (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    {q : H} (hq : (q : G) ∈ Q) :
    IsPGroup 2 (imgBar p H S) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) q ∈
        Subgroup.normalizer
          ((imgBar p H S : Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) := by
  refine ⟨hS.comap_subtype.map _, ?_⟩
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨q * u * q⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
  have := (Subgroup.mem_normalizer_iff.mp (hQS hq) u).mp (Subgroup.mem_subgroupOf.mp hu)
  simpa using this

theorem b3_of_normal (hNo2 : KFactCaseTwoNoTwo) {Q : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} [L.Normal] (hL : IsCaseTwoGroup p L)
    (hq : ∃ q : H, (q : G) ∈ Q ∧ QuotientGroup.mk' (primeComplementCore (G := H) p) q ∈ L ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) q) = p) :
    Hyp111B3 p H Q L := by
  obtain ⟨q, hqQ, hqL, hqp⟩ := hq
  refine b3_of_img Q fun S hS _ hQS => ?_
  obtain ⟨hU, hqU⟩ := img_facts (p := p) hS hQS hqQ
  exact le_centralizer_of_noTwo_of_normal hNo2 hL hU hqL hqp hqU

theorem b3_of_normal_of_aut {Q : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} [L.Normal]
    (hK : ∀ V : Subgroup (MulAut L), IsPGroup 2 V →
      (∀ x : L, (x : H ⧸ primeComplementCore (G := H) p) ∈
          (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
        MulAut.conj x ∈ Subgroup.normalizer (V : Set (MulAut L))) → V = ⊥) :
    Hyp111B3 p H Q L := by
  refine b3_of_img Q fun S hS _ hQS => ?_
  have hU : IsPGroup 2 (imgBar p H S) := hS.comap_subtype.map _
  refine le_centralizer_of_aut (T := (Q.subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L) inf_le_right
    (fun V hV hT => hK V hV fun x hx => hT x ⟨hx, x.2⟩) hU ?_
  rintro _ ⟨⟨q, hq, rfl⟩, -⟩
  exact (img_facts (p := p) hS hQS (Subgroup.mem_subgroupOf.mp hq)).2

omit [Finite G] in
theorem exists_mem_of_isFieldOmegaA (hp : p.Prime)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G}
    (hE : IsFieldOmegaA p M H R L E) :
    ∃ q : H, (q : G) ∈ E ∧ QuotientGroup.mk' (primeComplementCore (G := H) p) q ∈ L ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) q) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hEl, -, hne, -⟩ := hE
  obtain ⟨⟨x, hxE, hxL⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨q, hq, rfl⟩ := hxE
  refine ⟨q, Subgroup.mem_subgroupOf.mp hq, hxL, orderOf_eq_prime ?_ ?_⟩
  · rw [← map_pow]
    have h1 : (q : G) ^ p = 1 := hEl.2 _ (Subgroup.mem_subgroupOf.mp hq)
    have h2 : q ^ p = 1 := Subtype.ext (by simpa using h1)
    rw [h2, map_one]
  · intro h
    exact hx1 (Subtype.ext (by simpa using h))

theorem b3_of_isFieldOmegaA (hNo2 : KFactCaseTwoNoTwo) (hp : p.Prime)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} [L.Normal] (hL : IsCaseTwoGroup p L)
    {E : Subgroup G} (hE : IsFieldOmegaA p M H R L E) : Hyp111B3 p H E L :=
  b3_of_normal hNo2 hL (exists_mem_of_isFieldOmegaA hp hE)

end Local

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
