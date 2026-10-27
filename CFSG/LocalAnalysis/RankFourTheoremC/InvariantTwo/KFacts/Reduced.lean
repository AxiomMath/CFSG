module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

universe u

namespace CFSG.ABGLocalTools

theorem IsSylowOf.map {X : Type*} {Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

end CFSG.ABGLocalTools

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem IsPlaneDiagonal.map {H H' : Type*} [Group H] [Group H'] (f : H →* H') {p : ℕ}
    {D : Subgroup H} {z g : H} (h : IsPlaneDiagonal p D z g) :
    IsPlaneDiagonal p (D.map f) (f z) (f g) := by
  obtain ⟨hgN, hcop, a, b, hab, hord, hga, hgd⟩ := h
  refine ⟨Subgroup.le_normalizer_map f ⟨g, hgN, rfl⟩,
    hcop.coprime_dvd_right (orderOf_map_dvd f g), a, b, hab, hord, ?_, ?_⟩
  · rw [← map_mul, ← map_inv, ← map_mul, hga, map_pow]
  · rintro _ ⟨d, hd, rfl⟩ hdz
    obtain ⟨c, hc⟩ := hgd d hd fun hmem => hdz
      (by rw [← MonoidHom.map_zpowers]; exact Subgroup.mem_map_of_mem f hmem)
    exact ⟨c, by rw [← map_mul, ← map_inv, ← map_mul, hc, map_mul, map_pow, map_pow]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

section Quotient

variable {H : Type u} [Group H] [Finite H] {p : ℕ} (N : Subgroup H) [N.Normal]

theorem injOn_mk_of_isPGroup_coprime (hp : p.Prime) (hN : p.Coprime (Nat.card N)) {T : Subgroup H}
    (hT : IsPGroup p T) : Set.InjOn (QuotientGroup.mk' N) (T : Set H) := fun a ha b hb hab => by
  have hmem : a⁻¹ * b ∈ T ⊓ N := ⟨T.mul_mem (T.inv_mem ha) hb, QuotientGroup.eq.mp hab⟩
  rwa [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hT hN, Subgroup.mem_bot, inv_mul_eq_one]
    at hmem

theorem eq_of_map_mk_eq (hp : p.Prime) (hN : p.Coprime (Nat.card N)) {T A B : Subgroup H}
    (hT : IsPGroup p T) (hA : A ≤ T) (hB : B ≤ T)
    (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) : A = B := by
  have hinj := injOn_mk_of_isPGroup_coprime N hp hN hT
  refine le_antisymm (fun a ha => ?_) (fun b hb => ?_)
  · obtain ⟨b, hb, hba⟩ : QuotientGroup.mk' N a ∈ B.map (QuotientGroup.mk' N) :=
      h ▸ mem_map_of_mem _ ha
    exact hinj (hB hb) (hA ha) hba ▸ hb
  · obtain ⟨a, ha, hab⟩ : QuotientGroup.mk' N b ∈ A.map (QuotientGroup.mk' N) :=
      h ▸ mem_map_of_mem _ hb
    exact hinj (hA ha) (hB hb) hab ▸ ha

theorem normalizer_map_mk (hp : p.Prime) (hN : p.Coprime (Nat.card N)) {S : Subgroup H}
    (hS : IsPGroup p S) :
    normalizer ((S.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) =
      (normalizer (S : Set H)).map (QuotientGroup.mk' N) := by
  refine le_antisymm (fun x hx => ?_) (le_normalizer_map _)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ ((N ⊔ normalizer (S : Set H) : Subgroup H) : Set H) :=
    CFSG.AGLEmbedding.comap_normalizer_map_le_sup hp N hN hS hx
  rw [Subgroup.normal_mul, Set.mem_mul] at hy
  obtain ⟨m, hm, g, hg, rfl⟩ := hy
  have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
  exact ⟨g, hg, by rw [map_mul, hm1, one_mul]⟩

theorem centralizer_map_mk (hp : p.Prime) (hN : p.Coprime (Nat.card N)) {A : Subgroup H}
    (hA : IsPGroup p A) :
    centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) =
      (centralizer (A : Set H)).map (QuotientGroup.mk' N) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ ((N ⊔ centralizer (A : Set H) : Subgroup H) : Set H) :=
      CFSG.AGLEmbedding.comap_centralizer_map_le_sup hp N hN hA hx
    rw [Subgroup.normal_mul, Set.mem_mul] at hy
    obtain ⟨m, hm, g, hg, rfl⟩ := hy
    have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    exact ⟨g, hg, by rw [map_mul, hm1, one_mul]⟩
  · rw [Subgroup.coe_map]
    exact map_centralizer_le_centralizer_image _ _

theorem centralizer_singleton_map_mk (hp : p.Prime) (hN : p.Coprime (Nat.card N)) {d : H}
    (hd : IsPGroup p (zpowers d)) :
    centralizer ({QuotientGroup.mk' N d} : Set (H ⧸ N)) =
      (centralizer ({d} : Set H)).map (QuotientGroup.mk' N) := by
  have h := centralizer_map_mk N hp hN hd
  rwa [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure, zpowers_eq_closure,
    centralizer_closure] at h

theorem Lemma212ConfigGe.map_mk [Fact p.Prime] (hN : p.Coprime (Nat.card N)) {n : ℕ}
    {P : Sylow p H} {z : H} {D : Subgroup H} (h : Lemma212ConfigGe n p P z D) :
    Lemma212ConfigGe n p (P.mapSurjective (QuotientGroup.mk'_surjective N))
      (QuotientGroup.mk' N z) (D.map (QuotientGroup.mk' N)) := by
  have hp : p.Prime := Fact.out
  have hPp : IsPGroup p (P : Subgroup H) := P.isPGroup'
  have hDp : IsPGroup p D := IsPGroup.of_card h.card
  have hinjP := injOn_mk_of_isPGroup_coprime N hp hN hPp
  have hzP : z ∈ (P : Subgroup H) := h.le h.mem
  have hzp : z ^ p = 1 := h.elem.2 z h.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective,
      CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p hp N
        (hp.coprime_iff_not_dvd.mp hN) (P : Subgroup H)]
    exact h.rank
  · have hz1 : z ≠ 1 := fun hz => hp.one_lt.ne (by rw [← h.ord, hz, orderOf_one])
    refine orderOf_eq_prime (by rw [← map_pow, hzp, map_one]) fun h1 => hz1 ?_
    exact hinjP hzP (P : Subgroup H).one_mem (by rw [h1, map_one])
  · rw [Sylow.coe_mapSurjective]
    refine mem_centralizer_iff.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp h.central x hx]
  · intro y hy hyc hyp
    rw [Sylow.coe_mapSurjective] at hy hyc
    obtain ⟨x, hxP, rfl⟩ := hy
    have hxc : x ∈ centralizer ((P : Subgroup H) : Set H) := by
      refine mem_centralizer_iff.mpr fun u hu => ?_
      have := mem_centralizer_iff.mp hyc (QuotientGroup.mk' N u) (mem_map_of_mem _ hu)
      exact hinjP (mul_mem hu hxP) (mul_mem hxP hu) (by rw [map_mul, map_mul]; exact this)
    have hxp : x ^ p = 1 :=
      hinjP (pow_mem hxP p) (P : Subgroup H).one_mem (by rw [map_pow, hyp, map_one])
    rw [← MonoidHom.map_zpowers]
    exact mem_map_of_mem _ (h.unique x hxP hxc hxp)
  · rw [Sylow.coe_mapSurjective]
    exact map_mono h.le
  · exact CFSG.SectionRank.isElemAbelian_map h.elem _
  · rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp N hN hDp, h.card]
  · exact mem_map_of_mem _ h.mem
  · rw [Sylow.coe_mapSurjective]
    intro hle
    apply h.notNormal
    have key : ∀ s ∈ (P : Subgroup H), QuotientGroup.mk' N s ∈
        normalizer ((D.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) →
        ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
      intro s hs hsn d hd
      obtain ⟨d', hd', hdd'⟩ :
          QuotientGroup.mk' N (s * d * s⁻¹) ∈ D.map (QuotientGroup.mk' N) := by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp hsn _).mp (mem_map_of_mem _ hd)
      have hmem : s * d * s⁻¹ ∈ (P : Subgroup H) :=
        mul_mem (mul_mem hs (h.le hd)) ((P : Subgroup H).inv_mem hs)
      exact hinjP (h.le hd') hmem hdd' ▸ hd'
    intro t ht
    have htn := hle (mem_map_of_mem _ ht)
    refine mem_normalizer_iff.mpr fun d => ⟨key t ht htn d, fun hd => ?_⟩
    have := key t⁻¹ ((P : Subgroup H).inv_mem ht) (by rw [map_inv]; exact inv_mem htn) _ hd
    simpa [mul_assoc] using this
  · rw [centralizer_map_mk N hp hN hDp]
    exact h.sylow.map _

omit [Finite H] in
theorem map_map_conj_zpowers {H' : Type*} [Group H'] (f : H →* H') (g z : H) :
    ((zpowers z).map (MulAut.conj g).toMonoidHom).map f =
      (zpowers (f z)).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, ← MonoidHom.map_zpowers, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem exists_mem_normalizer_zpowers_eq_of_map_mk (hp : p.Prime) (hN : p.Coprime (Nat.card N))
    {D : Subgroup H} (hD : IsPGroup p D) {z : H} (hzD : z ∈ D)
    (h : ∀ y ∈ D.map (QuotientGroup.mk' N), y ≠ 1 →
      ∃ g ∈ normalizer ((D.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)),
        zpowers y = (zpowers (QuotientGroup.mk' N z)).map (MulAut.conj g).toMonoidHom) :
    ∀ y ∈ D, y ≠ 1 → ∃ g ∈ normalizer (D : Set H),
      zpowers y = (zpowers z).map (MulAut.conj g).toMonoidHom := by
  intro y hyD hy1
  have hinj := injOn_mk_of_isPGroup_coprime N hp hN hD
  have hy1' : QuotientGroup.mk' N y ≠ 1 := fun h1 =>
    hy1 (hinj hyD D.one_mem (by rw [h1, map_one]))
  obtain ⟨g', hg', hzp⟩ := h _ (mem_map_of_mem _ hyD) hy1'
  rw [normalizer_map_mk N hp hN hD] at hg'
  obtain ⟨g, hg, rfl⟩ := hg'
  refine ⟨g, hg, eq_of_map_mk_eq N hp hN hD (zpowers_le.2 hyD) ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (zpowers_le.2 hzD hx)
  · rw [map_map_conj_zpowers, ← hzp, MonoidHom.map_zpowers]

theorem exists_invariant_coprime_map_eq (hN : p.Coprime (Nat.card N)) {D : Subgroup H}
    {T : Subgroup (H ⧸ N)} (hT : p.Coprime (Nat.card T))
    (hDT : D.map (QuotientGroup.mk' N) ≤ normalizer (T : Set (H ⧸ N))) :
    ∃ T' : Subgroup H, p.Coprime (Nat.card T') ∧ D ≤ normalizer (T' : Set H) ∧
      T'.map (QuotientGroup.mk' N) = T := by
  have hker : p.Coprime (Nat.card (QuotientGroup.mk' N).ker) := by
    rwa [QuotientGroup.ker_mk']
  refine ⟨T.comap (QuotientGroup.mk' N),
    coprime_comap_of_coprime_kernel p _ (QuotientGroup.mk'_surjective N) hker T hT,
    fun d hd => mem_normalizer_iff.mpr fun x => ?_,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) T⟩
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact mem_normalizer_iff.mp (hDT (mem_map_of_mem _ hd)) _

theorem forall_le_iff_forall_eq_bot (hN : p.Coprime (Nat.card N)) (D : Subgroup H) :
    (∀ T : Subgroup H, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set H) → T ≤ N) ↔
      ∀ T : Subgroup (H ⧸ N), p.Coprime (Nat.card T) →
        D.map (QuotientGroup.mk' N) ≤ normalizer (T : Set (H ⧸ N)) → T = ⊥ := by
  constructor
  · intro h T hT hDT
    obtain ⟨T', hT', hDT', rfl⟩ := exists_invariant_coprime_map_eq N hN hT hDT
    refine (eq_bot_iff_forall _).mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff y).mpr (h T' hT' hDT' hy)
  · intro h T hT hDT
    have hbot := h (T.map (QuotientGroup.mk' N))
      (hT.coprime_dvd_right (card_map_dvd T _)) fun x hx => by
        obtain ⟨d, hd, rfl⟩ := hx
        exact le_normalizer_map _ ⟨d, hDT hd, rfl⟩
    intro x hx
    have : QuotientGroup.mk' N x ∈ T.map (QuotientGroup.mk' N) := mem_map_of_mem _ hx
    rw [hbot, mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this

end Quotient

@[expose] def CentralizerSectionEmbeds (p : ℕ) {K : Type u} [Group K] (D : Subgroup K) (z : K) :
    Prop :=
  ∀ d ∈ D, d ∉ zpowers z → ∀ (T : Type u) [Group T] [IsSimpleGroup T], p ∣ Nat.card T →
    (∃ (U : Subgroup K) (f : U →* T), U ≤ centralizer ({d} : Set K) ∧ Function.Surjective f) →
      ∃ (U' : Subgroup K) (f' : U' →* T), U' ≤ centralizer ({z} : Set K) ∧
        Function.Surjective f'

section Embeds

variable {H : Type u} [Group H] [Finite H] {p : ℕ} (N : Subgroup H) [N.Normal]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.CentralizerEmbeds.sectionEmbeds_map_mk
    (hp : p.Prime) (hN : p.Coprime (Nat.card N))
    {D : Subgroup H} {z : H} (hD : IsPGroup p D) (h : CentralizerEmbeds D z) :
    CentralizerSectionEmbeds p (D.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N z) := by
  rintro _ ⟨d, hdD, rfl⟩ hdz T _ _ hpT ⟨U, f, hU, hf⟩
  have hdz' : d ∉ zpowers z := fun hmem => hdz
    (by rw [← MonoidHom.map_zpowers]; exact mem_map_of_mem _ hmem)
  obtain ⟨g, hg⟩ := h d hdD hdz'
  have hC := centralizer_singleton_map_mk N hp hN (hD.to_le (zpowers_le.2 hdD))
  set U₁ : Subgroup H := centralizer ({d} : Set H) ⊓ U.comap (QuotientGroup.mk' N)
  let φ : U₁ →* U := ((QuotientGroup.mk' N).comp U₁.subtype).codRestrict U fun x => x.2.2
  have hφ : Function.Surjective φ := by
    intro u
    obtain ⟨c, hc, hcu⟩ : (u : H ⧸ N) ∈ (centralizer ({d} : Set H)).map (QuotientGroup.mk' N) :=
      hC ▸ hU u.2
    have hcU : QuotientGroup.mk' N c ∈ U := by rw [hcu]; exact u.2
    exact ⟨⟨c, hc, hcU⟩, Subtype.ext hcu⟩
  let ε : U₁ →* centralizer ({z} : Set H) := g.comp (Subgroup.inclusion inf_le_left)
  let E : U₁ →* H := (centralizer ({z} : Set H)).subtype.comp ε
  have hE : Function.Injective E :=
    Subtype.val_injective.comp (hg.comp (Subgroup.inclusion_injective _))
  let π' : U₁ →* H ⧸ N := (QuotientGroup.mk' N).comp E
  let f₁ : U₁ →* T := f.comp φ
  have hf₁ : Function.Surjective f₁ := hf.comp hφ
  have hker : π'.ker ≤ f₁.ker := by
    have hW : Nat.card π'.ker ∣ Nat.card N := by
      let κ : π'.ker →* N := (E.comp π'.ker.subtype).codRestrict N fun w =>
        (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp w.2)
      refine Subgroup.card_dvd_of_injective κ fun a b hab => Subtype.ext (hE ?_)
      have hab' := congrArg (fun x : N => (x : H)) hab
      exact hab'
    have hnorm : (π'.ker.map f₁).Normal := (MonoidHom.normal_ker π').map f₁ hf₁
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π'.ker.map f₁) with hbot | htop
    · intro w hw
      have : f₁ w ∈ π'.ker.map f₁ := mem_map_of_mem _ hw
      rw [hbot, mem_bot] at this
      exact this
    · exfalso
      have h1 : Nat.card T ∣ Nat.card π'.ker := by
        have := card_map_dvd π'.ker f₁
        rwa [htop, card_top] at this
      exact (hp.coprime_iff_not_dvd.mp hN) (hpT.trans (h1.trans hW))
  have hrange : π'.range ≤ centralizer ({QuotientGroup.mk' N z} : Set (H ⧸ N)) := by
    rintro _ ⟨u, rfl⟩
    have hz : E u * z = z * E u := mem_centralizer_singleton_iff.mp (ε u).2
    refine mem_centralizer_singleton_iff.mpr ?_
    change QuotientGroup.mk' N (E u) * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N (E u)
    rw [← map_mul, ← map_mul, hz]
  have hker' : π'.rangeRestrict.ker ≤ f₁.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let ψ : π'.range →* T :=
    MonoidHom.liftOfSurjective π'.rangeRestrict π'.rangeRestrict_surjective ⟨f₁, hker'⟩
  have hψ : ∀ u, ψ (π'.rangeRestrict u) = f₁ u := fun u => by simp [ψ]
  refine ⟨π'.range, ψ, hrange, fun t => ?_⟩
  obtain ⟨u, rfl⟩ := hf₁ t
  exact ⟨π'.rangeRestrict u, hψ u⟩

end Embeds

section Constraint

variable {X Y : Type*} [Group X] [Group Y] {p : ℕ}

theorem exists_normal_isPGroup_centralizer_le_of_mulEquiv (e : X ≃* Y)
    (h : ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set X) ≤ Q) :
    ∃ Q : Subgroup Y, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set Y) ≤ Q := by
  obtain ⟨Q, hQ, hQp, hQc⟩ := h
  refine ⟨Q.map e.toMonoidHom, hQ.map _ e.surjective, hQp.map _, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective y
  refine ⟨x, hQc (mem_centralizer_iff.mpr fun q hq => ?_), rfl⟩
  have := mem_centralizer_iff.mp hy (e q) (mem_map_of_mem _ hq)
  exact e.injective (by simpa using this)

theorem exists_normal_isPGroup_centralizer_le_iff :
    (∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set X) ≤ Q) ↔
      centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X := by
  constructor
  · rintro ⟨Q, hQ, hQp, hQc⟩
    have hQle : Q ≤ CFSG.pCore p X := le_sSup ⟨hQ, hQp⟩
    exact (centralizer_le hQle).trans (hQc.trans hQle)
  · exact fun h => ⟨CFSG.pCore p X, CFSG.pCore_normal, CFSG.pCore_isPGroup, h⟩

variable [Finite X]

omit [Finite X] in
theorem hasPrimeConstraint_iff_of_primeComplementCore_eq_bot
    (hK : primeComplementCore (G := X) p = ⊥) :
    HasPrimeConstraint (G := X) p ↔
      ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set X) ≤ Q := by
  let e : X ⧸ primeComplementCore (G := X) p ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hK).trans QuotientGroup.quotientBot
  exact ⟨exists_normal_isPGroup_centralizer_le_of_mulEquiv e,
    exists_normal_isPGroup_centralizer_le_of_mulEquiv e.symm⟩

end Constraint

@[expose] def KFactLemma212Red (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
    CFSG.AGLEmbedding.CatalogSimpleSections K → primeComplementCore (G := K) p = ⊥ →
      ∀ (P : Sylow p K) (z : K) (D : Subgroup K), Lemma212ConfigGe n p P z D →
        (∃ g, IsPlaneDiagonal p D z g) →
          (∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q) ∨
            CFSG.pCore p K = ⊥

@[expose] def KFactLemma213Red (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
    CFSG.AGLEmbedding.CatalogSimpleSections K → primeComplementCore (G := K) p = ⊥ →
      (¬ ∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q) →
      CFSG.pCore p K = ⊥ →
      ∀ (P : Sylow p K) (z : K) (D : Subgroup K), Lemma212ConfigGe n p P z D →
        (∃ g, IsPlaneDiagonal p D z g) → CentralizerSectionEmbeds p D z →
        (∀ T : Subgroup K, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set K) → T = ⊥) ∨
          (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set K),
            zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom)

theorem KFactLemma212Red.toGe {n : ℕ} (h : KFactLemma212Red n) : KFactLemma212Ge n := by
  intro p hp hp2 H _ _ hcat P z D hconf hg
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hg
  exact h p hp hp2 (H ⧸ primeComplementCore (G := H) p) (hcat.quotient _)
    (primeComplementCore_quotient_eq_bot p) _ _ _
    (hconf.map_mk _ (primeComplementCore_coprime p)) ⟨_, hg.map _⟩

theorem KFactLemma213Red.toGe {n : ℕ} (h : KFactLemma213Red n) : KFactLemma213Ge n := by
  intro p hp hp2 H _ _ hcat hcon hpc P z D hconf hg hemb
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hg
  have hN := primeComplementCore_coprime (G := H) p
  have hDp : IsPGroup p D := IsPGroup.of_card hconf.card
  rcases h p hp hp2 (H ⧸ primeComplementCore (G := H) p) (hcat.quotient _)
    (primeComplementCore_quotient_eq_bot p) hcon hpc _ _ _
    (hconf.map_mk _ hN) ⟨_, hg.map _⟩ (hemb.sectionEmbeds_map_mk _ hp hN hDp) with h1 | h2
  · exact Or.inl ((forall_le_iff_forall_eq_bot _ hN D).mpr h1)
  · exact Or.inr (exists_mem_normalizer_zpowers_eq_of_map_mk _ hp hN hDp hconf.mem h2)

end CFSG.LocalAnalysis.RankFourTheoremC
