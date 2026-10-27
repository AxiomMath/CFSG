module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1EndForm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup HarrisEnd Standing.Setup42

namespace HarrisEnd

theorem map_subtype_normal_of_characteristic {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (K : Subgroup N) [hK : K.Characteristic] : (K.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hx
  have hfix := hK.fixed (MulAut.conjNormal (H := N) g⁻¹)
  have hk' : MulAut.conjNormal (H := N) g k ∈ K := by
    have he : (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom (MulAut.conjNormal (H := N) g k) =
        k := by
      ext
      simp
    have h1 : (MulAut.conjNormal (H := N) g k) ∈
        K.comap (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom := by
      rw [mem_comap, he]
      exact hk
    rwa [hfix] at h1
  exact ⟨_, hk', by simp [MulAut.conjNormal_apply]⟩

theorem isMType_of_surjective {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker)
    (hA : Group.IsPerfect A) (hB : IsMType p B) : IsMType p A := by
  obtain ⟨⟨-, hBq⟩, ⟨tag, n, k, hL⟩, hev, hcond⟩ := hB
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f hf hker
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hf hker
  have hZ := GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hker
  have hcard : Nat.card (Open.fusionZStar A) =
      Nat.card f.ker * Nat.card (Open.fusionZStar B) := by
    have hs := f.subgroupComap_surjective (Open.fusionZStar B) hf
    have h1 := Subgroup.card_ker_mul_card_range (f.subgroupComap (Open.fusionZStar B))
    rw [MonoidHom.range_eq_top_of_surjective _ hs, card_top] at h1
    have h2 : Nat.card (f.subgroupComap (Open.fusionZStar B)).ker = Nat.card f.ker := by
      refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x : (Open.fusionZStar B).comap f),
        MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))⟩)
        ⟨fun x y h => ?_, fun y => ?_⟩)
      · exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : A)) h))
      · refine ⟨⟨⟨y, ?_⟩, ?_⟩, rfl⟩
        · rw [mem_comap, MonoidHom.mem_ker.mp y.2]
          exact one_mem _
        · exact Subtype.ext (MonoidHom.mem_ker.mp y.2)
    rw [← hZ, ← h1, h2]
  have hkerodd : Odd (Nat.card f.ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hker)
  have hfact : (Nat.card (Open.fusionZStar A)).factorization 2 =
      (Nat.card (Open.fusionZStar B)).factorization 2 := by
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  refine ⟨⟨hA, HarrisEnd.isQuasisimple_of_mulEquiv eO.symm hBq⟩,
    ⟨tag, n, k, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hL⟩, ?_, fun n k => ⟨fun h => ?_,
      fun h => ?_⟩⟩
  · rw [hcard]
    exact Nat.even_mul.mpr (Or.inr hev)
  · rw [hfact]
    exact (hcond n k).1 (GSThmB.OddQuot.lieModel_of_equiv eZ h)
  · rw [hfact]
    exact (hcond n k).2 (GSThmB.OddQuot.lieModel_of_equiv eZ h)

end HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem pPrimeCore_MBar_eq_bot (β : X) : pPrimeCore 2 (MBar β) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (prime_complement_kernel_core_preimage
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    (QuotientGroup.mk'_surjective _) GSThmB.OddQuot.not_two_dvd_card_ker).2
  rw [← h, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem pPrimeCore_layer_eq_bot (β : X) : pPrimeCore 2 ↥(layer (MBar β)) = ⊥ := by
  have hn := HarrisEnd.map_subtype_normal_of_characteristic (N := layer (MBar β))
    (pPrimeCore 2 ↥(layer (MBar β)))
  have hle : (pPrimeCore 2 ↥(layer (MBar β))).map (layer (MBar β)).subtype ≤
      pPrimeCore 2 (MBar β) := by
    refine le_pPrimeCore_of_normal_coprime hn ?_
    rw [card_map_of_injective (layer (MBar β)).subtype_injective]
    exact pPrimeCore_coprime_card
  rw [pPrimeCore_MBar_eq_bot, le_bot_iff, map_eq_bot_iff_of_injective _
    (layer (MBar β)).subtype_injective] at hle
  exact hle

theorem fusionZStar_layer_eq_center (β : X) :
    Open.fusionZStar ↥(layer (MBar β)) = center ↥(layer (MBar β)) := by
  ext l
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, pPrimeCore_layer_eq_bot, mem_center_iff]
  constructor
  · intro h m
    have := h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · intro h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h m).symm

theorem exists_pComponent_of_isQuasisimple (β : X) (hq : IsQuasisimple ↥(layer (MBar β))) :
    ∃ J : Subgroup ↥(centralizer ({β} : Set X)), IsPComponent 2 J ∧
      J.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))) = layer (MBar β) ∧
      ∃ g : ↥J →* ↥(layer (MBar β)), Function.Surjective g ∧ ¬ 2 ∣ Nat.card g.ker := by
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))
  have hcomp : IsComponent (layer (MBar β)) := ⟨hq, (HarrisEnd.layer_normal _).isSubnormal⟩
  obtain ⟨J, hJ, hJE⟩ :=
    LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hcomp
  refine ⟨J, hJ, hJE, (MulEquiv.subgroupCongr hJE).toMonoidHom.comp (π.subgroupMap J),
    (MulEquiv.subgroupCongr hJE).surjective.comp (π.subgroupMap_surjective J), ?_⟩
  have hk : ((MulEquiv.subgroupCongr hJE).toMonoidHom.comp (π.subgroupMap J)).ker =
      (π.subgroupMap J).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (MulEquiv.subgroupCongr hJE).injective]
  rw [hk]
  exact GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap π GSThmB.OddQuot.not_two_dvd_card_ker J

theorem beta_mem_of_mem_map {β : X} (hβ2 : β ^ 2 = 1) {J : Subgroup ↥(centralizer ({β} : Set X))}
    (hJ : betaBar β ∈ J.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))) :
    (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ∈ J := by
  set M := centralizer ({β} : Set X) with hM
  set b : ↥M := ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ with hb
  obtain ⟨y, hyJ, hy⟩ := hJ
  have ho : b⁻¹ * y ∈ pPrimeCore 2 ↥M := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M), MonoidHom.mem_ker, map_mul, map_inv]
    change (QuotientGroup.mk' _ b)⁻¹ * QuotientGroup.mk' _ y = 1
    rw [hy]
    exact inv_mul_cancel _
  have hodd : Odd (orderOf (b⁻¹ * y)) := by
    have hdvd : orderOf (⟨_, ho⟩ : pPrimeCore 2 ↥M) ∣ Nat.card (pPrimeCore 2 ↥M) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat (GSThmB.OddQuot.odd_card_pPrimeCore) hdvd
  have hbc : ∀ m : ↥M, b * m = m * b := fun m =>
    Subtype.ext (mem_centralizer_singleton_iff.mp m.2).symm
  have hb2 : b ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hβ2, Subgroup.coe_one])
  set o := b⁻¹ * y with ho_def
  obtain ⟨n, hn⟩ := hodd
  have hy' : b * o = y := by rw [ho_def]; group
  have hpow : y ^ orderOf o = b := by
    rw [← hy', (Commute.mul_pow (show Commute b o from hbc o) _), pow_orderOf_eq_one, mul_one, hn,
      pow_succ, pow_mul, hb2, one_pow, one_mul]
  rw [← hpow]
  exact pow_mem hyJ _

theorem isOfType_layer_of_isQuasisimple (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hq : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    IsOfType (HarrisF p) ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  rcases h412.lemma46d with h | ⟨K₁, K₂, hsup, hinf, hcomm, -, ⟨e₁⟩, ⟨e₂⟩, hlie, -, -⟩
  · exact h.2
  · exfalso
    set E := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hE
    obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 hlie
    have hK₁E : K₁ ≤ E := hsup ▸ le_sup_left
    have hK₂E : K₂ ≤ E := hsup ▸ le_sup_right
    have hn : (K₁.subgroupOf E).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      have hle : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
        sup_le le_normalizer (fun y hy => Subgroup.centralizer_le_normalizer _
          (mem_centralizer_iff.mpr fun x hx => (mem_centralizer_iff.mp (hcomm hx) y hy).symm))
      exact (mem_normalizer_iff.mp (hle (by rw [hsup]; exact g.2)) n).mp hn
    rcases LocalCores.quasisimple_normal_subgroups hq hn with h | h
    ·
      apply hab
      have h1 : Subsingleton ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
        have hK₂ : K₂ = ⊥ := by
          rw [eq_bot_iff, ← hinf]
          intro x hx
          refine ⟨?_, hx⟩
          have : (⟨x, hK₂E hx⟩ : ↥E) ∈ K₁.subgroupOf E := h ▸ mem_top _
          exact this
        have hc : Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := by
          rw [← Nat.card_congr e₂.toEquiv, hK₂, card_bot]
        exact (Nat.card_eq_one_iff_unique.mp hc).1
      exact Subsingleton.elim _ _
    ·
      apply hab
      apply e₁.symm.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      have hx : (⟨(e₁.symm a : _), hK₁E (e₁.symm a).2⟩ : ↥E) ∈ center ↥E := h (e₁.symm a).2
      have := mem_center_iff.mp hx ⟨(e₁.symm b : _), hK₁E (e₁.symm b).2⟩
      have := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at this ⊢
      exact this.symm

theorem cases_of_isQuasisimple [IsSimpleGroup X] (hin : Harris36NonsimpleInput)
    (h39 : Harris82TheoremOneKProper) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (h47 : IsLemma47 p (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hq : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hns : ¬ IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
        innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      ((Nonempty (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
            Blueprint.NativeSporadic.J2) ∧
          Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2) ∨
        (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
            center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 3 2 2 ∧
          Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) < 16)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  set τ := conjOn E (hs.setup.tBar i j) with hτdef
  have hcen : center ↥E ≠ ⊥ := by
    intro h
    apply hns
    have e : ↥E ⧸ center ↥E ≃* ↥E :=
      (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot
    have := hq.2.1
    exact e.symm.isSimpleGroup
  have hβE : betaBar β ∈ E := by
    obtain ⟨x, -, hx⟩ := h412.lemma46c.2.2 hcen
    rw [← hx]
    exact x.2
  have hZ2 : IsPGroup 2 ↥(center ↥E) := by
    have hle : (center ↥E).map E.subtype ≤ pCore 2 (MBar β) := by
      rw [← hs.centralizer_layer_eq h412]
      rintro _ ⟨c, hc, rfl⟩
      exact mem_centralizer_iff.mpr fun e he =>
        congrArg Subtype.val (mem_center_iff.mp hc ⟨e, he⟩)
    have h1 : IsPGroup 2 ↥((center ↥E).map E.subtype) := pCore_isPGroup.to_le hle
    exact h1.of_equiv (equivMapOfInjective _ _ E.subtype_injective).symm
  have hF := hs.isOfType_layer_of_isQuasisimple h412 hq
  obtain ⟨J, hJ, hJE, g, hg, hgk⟩ := exists_pComponent_of_isQuasisimple β hq
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (Standing.Setup42.beta_mem_X i j)
  have hβJ := beta_mem_of_mem_map hβ2 (J := J) (by rw [hJE]; exact hβE)
  have hM : ¬ IsMType p ↥E := by
    intro hME
    have hMJ := HarrisEnd.isMType_of_surjective g hg hgk
      (ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ) hME
    have hβord : orderOf β = 2 := orderOf_eq_prime hβ2 hs.beta.ne_one
    exact h39 X hnonab hK hcat β hβord J hJ hβJ p hs.prime_p hs.p_ne_two hMJ
  have htb := hs.tBar_not_mem_centralizer_layer h412
  have hτ1 : τ ≠ 1 := fun h => htb (conjOn_eq_one_iff.mp h)
  have hτ2 : τ ^ 2 = 1 := by rw [hτdef, ← map_pow, hs.tBar_sq, map_one]
  have hKτ : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p (f / 2) := by
    rw [hτdef, layerIn_fixedPoints_conjOn, h412.layerIn_layer_centralizer]
    exact lieModel_psl2_of_mulEquiv (subgroupOfEquivOfLe hs.KBar_le_layer) (hs.lieModel_KBar h412)
  have hsq : ∀ e : ↥E, MulAut.conj e = τ → e ^ 2 = 1 := by
    intro e he
    have hconj : conjOn E (e : MBar β) = MulAut.conj e := by
      ext x
      simp [MulAut.conj_apply]
    have hc : hs.setup.tBar i j * (e : MBar β)⁻¹ ∈ centralizer (E : Set (MBar β)) := by
      rw [← conjOn_eq_one_iff, map_mul, map_inv, hconj, he, hτdef, mul_inv_cancel]
    set c := hs.setup.tBar i j * (e : MBar β)⁻¹ with hcdef
    have hce : c * (e : MBar β) = (e : MBar β) * c :=
      (mem_centralizer_iff.mp hc (e : MBar β) e.2).symm
    have hte : hs.setup.tBar i j = c * e := by rw [hcdef]; group
    have hct : c ∈ centralizer ({hs.setup.tBar i j} : Set (MBar β)) := by
      rw [mem_centralizer_singleton_iff, hte, mul_assoc c (e : MBar β) c, ← hce]
    have hc' : c ∈ centralizer (E : Set (MBar β)) ⊓ centralizer {hs.setup.tBar i j} := ⟨hc, hct⟩
    rw [hs.centralizer_layer_inf_centralizer_tBar h412] at hc'
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hc'
    have hc2 : c ^ 2 = 1 := by
      rw [← hn, ← zpow_natCast (betaBar β ^ n), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hs.betaBar_sq, one_zpow]
    have ht2 := hs.tBar_sq
    rw [hte, (Commute.mul_pow (show Commute c (e : MBar β) from hce) 2), hc2, one_mul] at ht2
    exact Subtype.ext (by rw [Subgroup.coe_pow, ht2, Subgroup.coe_one])
  rcases hin ↥E hq hns hZ2 p (f / 2) hs.prime_p hs.p_ne_two hs.one_le_half hs.sixteen_dvd hF hM τ
    (orderOf_eq_prime hτ2 hτ1) hKτ with ⟨hJ2, hc2, hout⟩ | ⟨-, -, hin'⟩ | ⟨hL34, hc16, hout⟩ |
      ⟨k, hk, hk'⟩
  · exact ⟨hout, Or.inl ⟨hJ2, hc2⟩⟩
  · exfalso
    obtain ⟨⟨e, he⟩, hall⟩ := hin'
    exact hall e he (hsq e he)
  · exact ⟨hout, Or.inr ⟨hL34, hc16⟩⟩
  · exfalso
    obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hg hgk
    obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective g hg hgk
    have eO' : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥E :=
      eO.trans ((QuotientGroup.quotientMulEquivOfEq (pPrimeCore_layer_eq_bot β)).trans
        QuotientGroup.quotientBot)
    have eZ' : ↥J ⧸ Open.fusionZStar ↥J ≃* ↥E ⧸ center ↥E :=
      eZ.trans (QuotientGroup.quotientMulEquivOfEq (fusionZStar_layer_eq_center β))
    have h2q : IsTwoQuasisimple ↥J :=
      ⟨ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ,
        HarrisEnd.isQuasisimple_of_mulEquiv eO'.symm hq⟩
    exact h47 J hJ k hk ⟨h2q, ↥E ⧸ center ↥E, inferInstance, hk', ⟨eZ'⟩⟩

end Setting46e

@[expose] def Harris414CaseHyp (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X)
    (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ) : Prop :=
  ∃ hs : Setting46e t L p f S w z V i j,
    IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j) ∧
    (∀ i' j' : ℕ, IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')) ∧
    IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
    ¬ IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

@[expose] def Harris414J2Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris414CaseHyp X t L p f S w z V i j →
      ¬ (Nonempty (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
            Blueprint.NativeSporadic.J2) ∧
        Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)

@[expose] def Harris414L34Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris414CaseHyp X t L p f S w z V i j →
      ¬ (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
            center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 3 2 2 ∧
          Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) < 16)

theorem harris414_of_cases (hin : Harris36NonsimpleInput) (h39 : Harris82TheoremOneKProper)
    (h412 : Harris412Statement) (h47 : Harris47Input) (hJ2 : Harris414J2Case)
    (hL34 : Harris414L34Case) : Harris414Input46e := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs hns hq
  have h412' := h412 X hnonab hK hcat t L p f S w z V i j hs
  have h47' := h47 X hnonab hK hcat t L p f S w z V i j hs
  obtain ⟨hout, hc⟩ := hs.cases_of_isQuasisimple hin h39 hnonab hK hcat h412' (h47' i j) hq hns
  have hhyp : Harris414CaseHyp X t L p f S w z V i j := ⟨hs, h412', h47', hq, hns, hout⟩
  rcases hc with hc | hc
  · exact hJ2 X hnonab hK hcat t L p f S w z V i j hhyp hc
  · exact hL34 X hnonab hK hcat t L p f S w z V i j hhyp hc

end CFSG.ComponentClassification.HarrisLit
