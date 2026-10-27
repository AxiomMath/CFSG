module

public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCore
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Quotient

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem inf_eq_bot_of_isPGroup (hp : p.Prime) {T O : Subgroup X} (hT : IsPGroup p T)
    (hO : p.Coprime (Nat.card O)) : T ⊓ O = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  exact (Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hO.pow_left n)).eq_bot

theorem card_map_mk_of_isPGroup (hp : p.Prime) (O : Subgroup X) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T : Subgroup X} (hT : IsPGroup p T) :
    Nat.card (T.map (QuotientGroup.mk' O)) = Nat.card T :=
  (Nat.card_congr (Equiv.ofBijective _
    ⟨pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp O
      (hp.coprime_iff_not_dvd.mp hO) T hT,
    (QuotientGroup.mk' O).subgroupMap_surjective T⟩)).symm

omit [Finite X] in
theorem map_comap_inf_eq {Y : Type*} [Group Y] (f : X →* Y) {R : Subgroup X}
    {Qbar : Subgroup Y} (hQ : Qbar ≤ R.map f) : (Qbar.comap f ⊓ R).map f = Qbar := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_left) fun y hy => ?_
  obtain ⟨r, hr, rfl⟩ := hQ hy
  exact ⟨r, ⟨hy, hr⟩, rfl⟩

omit [Finite X] in
theorem le_map_of_comap_le {Y : Type*} [Group Y] {f : X →* Y} (hf : Function.Surjective f)
    {S : Subgroup Y} {T : Subgroup X} (h : S.comap f ≤ T) : S ≤ T.map f :=
  (Subgroup.map_comap_eq_self_of_surjective hf S).symm.le.trans (Subgroup.map_mono h)

theorem map_inf_centralizer_map_le (hp : p.Prime) (O : Subgroup X) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {Q R : Subgroup X} (hR : IsPGroup p R) (hQR : Q ≤ R) :
    R.map (QuotientGroup.mk' O) ⊓
        Subgroup.centralizer ((Q.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O)) ≤
      (R ⊓ Subgroup.centralizer (Q : Set X)).map (QuotientGroup.mk' O) := by
  rintro _ ⟨⟨r, hr, rfl⟩, hz⟩
  refine ⟨r, ⟨hr, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hz _ (Subgroup.mem_map_of_mem _ hq)
  have hker : q * r * (r * q)⁻¹ ∈ (QuotientGroup.mk' O).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm, mul_inv_cancel]
  rw [QuotientGroup.ker_mk'] at hker
  have hmem : q * r * (r * q)⁻¹ ∈ R ⊓ O :=
    ⟨R.mul_mem (R.mul_mem (hQR hq) hr) (R.inv_mem (R.mul_mem hr (hQR hq))), hker⟩
  rwa [inf_eq_bot_of_isPGroup hp hR hO, Subgroup.mem_bot, mul_inv_eq_one] at hmem

theorem comap_centralizer_map_le_sup (hp : p.Prime) (O : Subgroup X) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {A : Subgroup X} (hA : IsPGroup p A) :
    (Subgroup.centralizer ((A.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) :
        Set (X ⧸ O))).comap (QuotientGroup.mk' O) ≤
      O ⊔ Subgroup.centralizer (A : Set X) := by
  intro x hx
  rw [Subgroup.mem_comap] at hx
  obtain ⟨y, hy, hyfixed⟩ :=
    @CFSG.RankThreeCoreUniqueness.Helpers.coprime_pGroup_fixed_lift A X (X ⧸ O) _ _ _ _
      (CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom
        (MulAut.conj.comp A.subtype))
      (CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom
        (MulAut.conj.comp ((QuotientGroup.mk' O).comp A.subtype)))
      p hp hA (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
      (fun a z => by
        change QuotientGroup.mk' O ((a : X) * z * (a : X)⁻¹) =
          QuotientGroup.mk' O a * QuotientGroup.mk' O z * (QuotientGroup.mk' O a)⁻¹
        rw [map_mul, map_mul, map_inv])
      (by rwa [QuotientGroup.ker_mk'])
      (QuotientGroup.mk' O x)
      (fun a => by
        change QuotientGroup.mk' O a * QuotientGroup.mk' O x * (QuotientGroup.mk' O a)⁻¹ =
          QuotientGroup.mk' O x
        rw [Subgroup.mem_centralizer_iff.mp hx _ (Subgroup.mem_map_of_mem _ a.property),
          mul_inv_cancel_right])
  have hyC : y ∈ Subgroup.centralizer (A : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have h := hyfixed ⟨a, ha⟩
    change a * y * a⁻¹ = y at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hxy : x * y⁻¹ ∈ (QuotientGroup.mk' O).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
  rw [QuotientGroup.ker_mk'] at hxy
  simpa using Subgroup.mul_mem_sup hxy hyC

theorem comap_normalizer_map_le_sup (hp : p.Prime) (O : Subgroup X) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {Q : Subgroup X} (hQ : IsPGroup p Q) :
    (Subgroup.normalizer ((Q.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) :
        Set (X ⧸ O))).comap (QuotientGroup.mk' O) ≤
      O ⊔ Subgroup.normalizer (Q : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  let K := (Q.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O)
  have hbound : ∀ T : Subgroup X, IsPGroup p T → T ≤ K → Nat.card T ≤ Nat.card Q := by
    intro T hT hTK
    rw [← card_map_mk_of_isPGroup hp O hO hT, ← card_map_mk_of_isPGroup hp O hO hQ]
    exact Subgroup.card_le_of_le (Subgroup.map_le_iff_le_comap.mpr hTK)
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have hQK : Q ≤ K := Subgroup.le_comap_map _ Q
  have hQ'K : Q.map (MulAut.conj x).toMonoidHom ≤ K := by
    rintro _ ⟨q, hq, rfl⟩
    change QuotientGroup.mk' O (x * q * x⁻¹) ∈ Q.map (QuotientGroup.mk' O)
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mem_map_of_mem _ hq)
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨S', hS'⟩ :=
    ((hQ.map (MulAut.conj x).toMonoidHom).comap_subtype (K := K)).exists_le_sylow
  have hSeq : (S : Subgroup K) = Q.subgroupOf K := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    have hSmap := hbound ((S : Subgroup K).map K.subtype) (S.isPGroup'.map _)
      (Subgroup.map_subtype_le _)
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hSmap
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S' S
  have hconj : ∀ q ∈ Q, (k : X) * (x * q * x⁻¹) * (k : X)⁻¹ ∈ Q := by
    intro q hq
    have hmem : (⟨x * q * x⁻¹, hQ'K ⟨q, hq, rfl⟩⟩ : K) ∈ (S' : Subgroup K) := hS' ⟨q, hq, rfl⟩
    have hmem' : k * ⟨x * q * x⁻¹, hQ'K ⟨q, hq, rfl⟩⟩ * k⁻¹ ∈
        ((k • S' : Sylow p K) : Subgroup K) := by
      rw [CFSG.RankThreeCoreUniqueness.Helpers.sylow_conjugate_eq_map]
      exact Subgroup.mem_map_of_mem _ hmem
    rw [hk, hSeq] at hmem'
    exact hmem'
  obtain ⟨q₀, hq₀, hq₀k⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp k.property)
  have hnN : q₀⁻¹ * (k : X) * x ∈ Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      change q₀⁻¹ * (k : X) * x * q * (q₀⁻¹ * (k : X) * x)⁻¹ ∈ Q
      have heq : q₀⁻¹ * (k : X) * x * q * (q₀⁻¹ * (k : X) * x)⁻¹ =
          q₀⁻¹ * ((k : X) * (x * q * x⁻¹) * (k : X)⁻¹) * q₀ := by group
      rw [heq]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq₀) (hconj q hq)) hq₀
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hxn : x * (q₀⁻¹ * (k : X) * x)⁻¹ ∈ (QuotientGroup.mk' O).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hq₀k]
    group
  rw [QuotientGroup.ker_mk'] at hxn
  have hmem := Subgroup.mul_mem_sup hxn hnN
  rwa [inv_mul_cancel_right] at hmem

end Quotient

section Hyperplane

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem three_le_pRank_of_card {E : Subgroup G} (hp : p.Prime) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 3) : 3 ≤ pRank p E :=
  CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hEcard

theorem two_le_pRank_of_relIndex {E F : Subgroup G} (hp : p.Prime) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 3) (hFE : F ≤ E) (hindex : F.relIndex E = p) :
    2 ≤ pRank p F := by
  have hrank := elementary_prime_index_subgroup_rank p hp hE 3 hEcard (F.subgroupOf E)
    (Or.inr hindex)
  rwa [Subgroup.map_subgroupOf_eq_of_le hFE] at hrank

theorem centralizer_le_of_two_le_pRank (hp : p.Prime) (P : Sylow p G) {M E F : Subgroup G}
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 3) (hEP : E ≤ P) (hFE : F ≤ E) (hF : 2 ≤ pRank p F) :
    Subgroup.centralizer (F : Set G) ≤ M :=
  ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_weakCore_of_commutative_overgroup p hp hEP hFE hE.1 hF
      (three_le_pRank_of_card hp hE hEcard))).trans hWM

end Hyperplane

theorem hyperplane_centralizers_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (P : Sylow p G) {M E : Subgroup G}
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) (hEP : E ≤ P) :
    ⨆ (F : Subgroup G) (_ : F ≤ E ∧ F.relIndex E = p), Subgroup.centralizer (F : Set G) ≤ M :=
  iSup₂_le fun _ hF => centralizer_le_of_two_le_pRank hp P hWM hE hEcard hEP hF.1
    (two_le_pRank_of_relIndex hp hE hEcard hF.1 hF.2)

section Transfer

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem isElemAbelian_subgroupOf {E : Subgroup G} (hE : IsElemAbelian p E) (H : Subgroup G) :
    IsElemAbelian p (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem pRank_map_mk_eq_pRank_map_subtype (hp : p.Prime) {H : Subgroup G} (O : Subgroup H)
    [O.Normal] (hO : p.Coprime (Nat.card O)) (Y : Subgroup H) :
    pRank p (Y.map (QuotientGroup.mk' O)) = pRank p (Y.map H.subtype) := by
  rw [pRank_quotient_map_of_coprime_normal p hp O (hp.coprime_iff_not_dvd.mp hO) Y,
    pRank_map_of_injective p hp H.subtype H.subtype_injective Y]

omit [Finite G] in
theorem map_subtype_centralizer_le {H : Subgroup G} (F : Subgroup H) :
    (Subgroup.centralizer (F : Set H)).map H.subtype ≤
      Subgroup.centralizer ((F.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact Subgroup.map_centralizer_le_centralizer_image _ _

theorem weakCore_map_le_map_inf_of_coprime (hp : p.Prime) (P : Sylow p G) {M H R : Subgroup G}
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (hRP : R ≤ P) (hRH : R ≤ H)
    (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O))
    (hOM : O ≤ (H ⊓ M).subgroupOf H) :
    GLBWeakCore p ((R.subgroupOf H).map (QuotientGroup.mk' O)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) := by
  have hR : IsPGroup p (R.subgroupOf H) := (P.isPGroup'.to_le hRP).comap_subtype
  have hRG : (R.subgroupOf H).map H.subtype ≤ P :=
    (Subgroup.map_subgroupOf_eq_of_le hRH).le.trans hRP
  refine (weakCore_le_iff p _ _).mpr fun Qbar hQR hQ2 hQ3 => ?_
  obtain ⟨Q, hQR', rfl⟩ : ∃ Q ≤ R.subgroupOf H, Q.map (QuotientGroup.mk' O) = Qbar :=
    ⟨_, inf_le_right, map_comap_inf_eq _ hQR⟩
  rw [pRank_map_mk_eq_pRank_map_subtype hp O hO] at hQ2
  have hle₁ : Q.map (QuotientGroup.mk' O) ⊔ ((R.subgroupOf H).map (QuotientGroup.mk' O) ⊓
      Subgroup.centralizer ((Q.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O))) ≤
      (Q ⊔ (R.subgroupOf H ⊓ Subgroup.centralizer (Q : Set H))).map (QuotientGroup.mk' O) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup_left (map_inf_centralizer_map_le hp O hO hR hQR') _
  have hle₂ : (Q ⊔ (R.subgroupOf H ⊓ Subgroup.centralizer (Q : Set H))).map H.subtype ≤
      Q.map H.subtype ⊔ ((P : Subgroup G) ⊓
        Subgroup.centralizer ((Q.map H.subtype : Subgroup G) : Set G)) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup_left (le_inf ((Subgroup.map_mono inf_le_left).trans hRG)
      ((Subgroup.map_mono inf_le_right).trans (map_subtype_centralizer_le Q))) _
  have hQ3' := hQ3.trans ((pRank_mono p hp hle₁).trans
    ((pRank_map_mk_eq_pRank_map_subtype hp O hO _).le.trans (pRank_mono p hp hle₂)))
  have hN : Subgroup.normalizer ((Q.map H.subtype : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_weakCore p ((Subgroup.map_mono hQR').trans hRG) hQ2 hQ3').trans hWM
  have hNH : Subgroup.normalizer (Q : Set H) ≤ (H ⊓ M).subgroupOf H := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hN (Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩)⟩
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
    ((comap_normalizer_map_le_sup hp O hO (hR.to_le hQR')).trans (sup_le hOM hNH))

theorem hyperplane_centralizers_map_le_map_inf_of_coprime (hp : p.Prime) (P : Sylow p G)
    {M H E : Subgroup G} (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) (hEP : E ≤ P) (hEH : E ≤ H)
    (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O))
    (hOM : O ≤ (H ⊓ M).subgroupOf H) :
    ⨆ (F : Subgroup (H ⧸ O))
        (_ : F ≤ (E.subgroupOf H).map (QuotientGroup.mk' O) ∧
          F.relIndex ((E.subgroupOf H).map (QuotientGroup.mk' O)) = p),
        Subgroup.centralizer (F : Set (H ⧸ O)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) := by
  refine iSup₂_le fun Fbar hF => ?_
  have hEHcard : Nat.card (E.subgroupOf H) = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hEcard]
  have hEHp : IsPGroup p (E.subgroupOf H) := IsPGroup.of_card hEHcard
  have hrank := two_le_pRank_of_relIndex hp
    (elementary_abelian_map p (isElemAbelian_subgroupOf hE H) (QuotientGroup.mk' O))
    (by rw [card_map_mk_of_isPGroup hp O hO hEHp, hEHcard]) hF.1 hF.2
  obtain ⟨F, hFE, rfl⟩ : ∃ F ≤ E.subgroupOf H, F.map (QuotientGroup.mk' O) = Fbar :=
    ⟨_, inf_le_right, map_comap_inf_eq _ hF.1⟩
  rw [pRank_map_mk_eq_pRank_map_subtype hp O hO] at hrank
  have hC := centralizer_le_of_two_le_pRank hp P hWM hE hEcard hEP
    ((Subgroup.map_mono hFE).trans (Subgroup.map_subgroupOf_eq_of_le hEH).le) hrank
  have hCH : Subgroup.centralizer (F : Set H) ≤ (H ⊓ M).subgroupOf H := fun c hc =>
    Subgroup.mem_subgroupOf.mpr ⟨c.property, hC (map_subtype_centralizer_le F ⟨c, hc, rfl⟩)⟩
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
    ((comap_centralizer_map_le_sup hp O hO (hEHp.to_le hFE)).trans (sup_le hOM hCH))

end Transfer

theorem glbPrimeCore_subgroupOf_coprime {G : Type*} [Group G] [Finite G] (p : ℕ)
    (H : Subgroup G) : p.Coprime (Nat.card ((GLBPrimeCore p H).subgroupOf H)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le p H)).toEquiv]
  exact glbPrimeCore_coprime p H

theorem glbPrimeCore_subgroupOf_le_inf {G : Type*} [Group G] {p : ℕ} {M H : Subgroup G}
    (hcore : GLBPrimeCore p H ≤ M) :
    (GLBPrimeCore p H).subgroupOf H ≤ (H ⊓ M).subgroupOf H := fun o ho =>
  Subgroup.mem_subgroupOf.mpr ⟨o.property, hcore (Subgroup.mem_subgroupOf.mp ho)⟩

theorem quotient_weakCore_le_map_inf
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (P : Sylow p G) {M H R : Subgroup G}
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (hRP : R ≤ P) (hRH : R ≤ H)
    (hcore : GLBPrimeCore p H ≤ M) [((GLBPrimeCore p H).subgroupOf H).Normal] :
    GLBWeakCore p ((R.subgroupOf H).map (QuotientGroup.mk' ((GLBPrimeCore p H).subgroupOf H))) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' ((GLBPrimeCore p H).subgroupOf H)) :=
  weakCore_map_le_map_inf_of_coprime hp P hWM hRP hRH _ (glbPrimeCore_subgroupOf_coprime p H)
    (glbPrimeCore_subgroupOf_le_inf hcore)

theorem quotient_hyperplane_centralizers_le_map_inf
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (P : Sylow p G) {M H E : Subgroup G}
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) (hEP : E ≤ P) (hEH : E ≤ H)
    (hcore : GLBPrimeCore p H ≤ M) [((GLBPrimeCore p H).subgroupOf H).Normal] :
    ⨆ (F : Subgroup (↥H ⧸ (GLBPrimeCore p H).subgroupOf H))
        (_ : F ≤ (E.subgroupOf H).map (QuotientGroup.mk' ((GLBPrimeCore p H).subgroupOf H)) ∧
          F.relIndex ((E.subgroupOf H).map
            (QuotientGroup.mk' ((GLBPrimeCore p H).subgroupOf H))) = p),
        Subgroup.centralizer (F : Set (↥H ⧸ (GLBPrimeCore p H).subgroupOf H)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' ((GLBPrimeCore p H).subgroupOf H)) :=
  hyperplane_centralizers_map_le_map_inf_of_coprime hp P hWM hE hEcard hEP hEH _
    (glbPrimeCore_subgroupOf_coprime p H) (glbPrimeCore_subgroupOf_le_inf hcore)

end CFSG.AGLEmbedding
