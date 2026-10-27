module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporSmall
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFive
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CarrierFactsProof
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporB7
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MonsterTargets
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017MRankFive

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen

open CFSG.Open

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def centGen (A : Subgroup K) : Subgroup K :=
  ⨆ (a : K) (_ : a ∈ A) (_ : a ≠ 1), Subgroup.centralizer ({a} : Set K)

theorem centralizer_le_centGen {A : Subgroup K} {a : K} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set K) ≤ centGen A :=
  le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

theorem le_normalizer_centGen (A : Subgroup K) :
    Subgroup.normalizer (A : Set K) ≤ Subgroup.normalizer (centGen A : Set K) := by
  intro n hn
  have key : ∀ n ∈ Subgroup.normalizer (A : Set K),
      ∀ x ∈ centGen A, n * x * n⁻¹ ∈ centGen A := by
    intro n hn x hx
    have hle : centGen A ≤ (centGen A).comap (MulAut.conj n).toMonoidHom := by
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      intro y hy
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hna : n * a * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hn a).mp ha
      have hna1 : n * a * n⁻¹ ≠ 1 := by
        rw [Ne, conj_eq_one_iff]; exact ha1
      refine centralizer_le_centGen hna hna1 ?_
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc y, hy]; group
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun h => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h
  simpa [mul_assoc] using this

theorem normalizer_le_centGen_sup (T : Sylow p K) (hT : IsMulCommutative (T : Subgroup K))
    {Q : Subgroup K} (hQT : Q ≤ T) (hQ : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set K) ≤ centGen (T : Subgroup K) ⊔ Subgroup.normalizer (T : Set K) := by
  obtain ⟨⟨a, haQ⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  set C := Subgroup.centralizer (Q : Set K)
  have hCa : C ≤ centGen (T : Subgroup K) := by
    refine le_trans ?_ (centralizer_le_centGen (hQT haQ) (by simpa using ha1))
    exact Subgroup.centralizer_le (by simpa using haQ)
  have hTC : (T : Subgroup K) ≤ C := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hT.is_comm.comm ⟨q, hQT hq⟩ ⟨t, ht⟩ |> congrArg Subtype.val)
  intro g hg
  have hgC : ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) q).mp hq
      simpa using this
    have := hx _ hq'
    calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * q := by group
  have hgTC : ((g • T : Sylow p K) : Subgroup K) ≤ C := by
    intro y hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have := hgC _ (hTC hy)
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (T.subtype hTC) ((g • T).subtype hgTC)
  have hcg : (c : K)⁻¹ * g ∈ Subgroup.normalizer (T : Set K) := by
    have h1 : ((c : K) • T : Sylow p K) = g • T := by
      have h0 := hc
      rw [Sylow.smul_subtype] at h0
      exact Sylow.subtype_injective h0
    have h2 : (((c : K)⁻¹ * g) • T : Sylow p K) = T := by
      rw [mul_smul, ← h1, ← mul_smul, inv_mul_cancel, one_smul]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h2
  have : g = (c : K) * ((c : K)⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem_sup (hCa c.2) hcg

theorem ne_bot_of_one_le_pRank {Q : Subgroup K} (h : 1 ≤ CFSG.Open.pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup K) = 0 := by
    unfold CFSG.Open.pRank
    refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
    rintro k ⟨E, hE, -, hc⟩
    rw [le_bot_iff] at hE
    subst hE
    rw [Subgroup.card_bot] at hc
    exact ((Nat.pow_eq_one.mp hc.symm).resolve_left (Fact.out : p.Prime).one_lt.ne').le
  omega

theorem centGen_eq_top_of_glbCore [IsSimpleGroup K] (T : Sylow p K)
    (hT : IsMulCommutative (T : Subgroup K)) (hΓ : GLBCore p 1 (T : Subgroup K) = ⊤) :
    centGen (T : Subgroup K) = ⊤ := by
  have hsup : centGen (T : Subgroup K) ⊔ Subgroup.normalizer (T : Set K) = ⊤ := by
    rw [eq_top_iff, ← hΓ]
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQ, rfl⟩
    exact normalizer_le_centGen_sup T hT hQT (ne_bot_of_one_le_pRank hQ)
  have hnorm : (centGen (T : Subgroup K)).Normal := by
    have hle : centGen (T : Subgroup K) ⊔ Subgroup.normalizer (T : Set K) ≤
        Subgroup.normalizer (centGen (T : Subgroup K) : Set K) :=
      sup_le Subgroup.le_normalizer (le_normalizer_centGen _)
    rw [hsup, top_le_iff] at hle
    exact Subgroup.normalizer_eq_top_iff.mp hle
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hTbot : (T : Subgroup K) = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      by_contra ha1
      have := centralizer_le_centGen ha ha1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      rw [hbot, Subgroup.mem_bot] at this
      exact ha1 this
    have hΓbot : GLBCore p 1 (T : Subgroup K) = ⊥ := by
      refine le_bot_iff.mp (sSup_le ?_)
      rintro N ⟨Q, hQT, hQ, -⟩
      exact absurd (le_bot_iff.mp (hTbot ▸ hQT)) (ne_bot_of_one_le_pRank hQ)
    rw [hΓbot] at hΓ
    exact bot_ne_top hΓ
  · exact htop

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem one_le_pRank_zpowers {e : X} (he : orderOf e = p) :
    1 ≤ CFSG.Open.pRank p (Subgroup.zpowers e) := by
  have hp : p.Prime := Fact.out
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨Subgroup.zpowers e, le_rfl, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro k ⟨E, -, -, hc⟩
    calc k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
      _ = Nat.card E := hc.symm
      _ ≤ Nat.card X := Subgroup.card_le_card_group E
  · rintro x ⟨n, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← he, pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, he, pow_one]

theorem centralizer_inf_le_gammaOver {K E : Subgroup X} {e : X} (heE : e ∈ E) (he1 : e ≠ 1)
    (hep : e ^ p = 1) :
    Subgroup.centralizer ({e} : Set X) ⊓ K ≤
      CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver 1 p E K := by
  have hp : p.Prime := Fact.out
  have ho : orderOf e = p := orderOf_eq_prime hep he1
  refine le_trans ?_ (le_iSup_of_le (Subgroup.zpowers e) (le_iSup_of_le
    ((Subgroup.zpowers_le).mpr heE) (le_iSup_of_le (one_le_pRank_zpowers ho) le_rfl)))
  refine inf_le_inf_right K ?_
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hc : ∀ n : ℤ, Commute x (e ^ n) := fun n =>
    Commute.zpow_right (show Commute x e from hx) n
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simp only
    rw [(hc n).eq, mul_inv_cancel_right]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp only at hn ⊢
    have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [this, ← hn, ((hc n).inv_left).eq, inv_mul_cancel_right]

theorem le_gammaOver_of_inner {K E : Subgroup X}
    (hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1)
    (hinn : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hgen : ∀ A : Subgroup X, A ≤ K → IsElemAbelian p A → Nat.card A = p ^ 2 →
      K ≤ ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ K) :
    K ≤ CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver 1 p E K := by
  by_cases hker : ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ K, e * x * e⁻¹ = x
  · obtain ⟨e, heE, he1, hcomm⟩ := hker
    refine le_trans (fun x hx => Subgroup.mem_inf.mpr ⟨?_, hx⟩)
      (centralizer_inf_le_gammaOver heE he1 (hE.2 e heE))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcomm x hx
    calc x * e = e * x * e⁻¹ * e := by rw [this]
      _ = e * x := by group
  push Not at hker
  choose κ hκK hκ using hinn
  have huniq : ∀ k ∈ K, ∀ k' ∈ K, (∀ x ∈ K, k * x * k⁻¹ = k' * x * k'⁻¹) → k = k' := by
    intro k hk k' hk' h
    have : k'⁻¹ * k = 1 := hZ _ (K.mul_mem (K.inv_mem hk') hk) fun x hx => by
      have := h x hx
      calc k'⁻¹ * k * x = k'⁻¹ * (k * x * k⁻¹) * k := by group
        _ = k'⁻¹ * (k' * x * k'⁻¹) * k := by rw [this]
        _ = x * (k'⁻¹ * k) := by group
    calc k = k' * (k'⁻¹ * k) := by group
      _ = k' := by rw [this, mul_one]
  let φ : E →* X :=
    { toFun := fun e => κ e e.2
      map_one' := by
        refine (huniq _ (hκK 1 E.one_mem) 1 K.one_mem fun x hx => ?_)
        rw [← hκ 1 E.one_mem x hx]
      map_mul' := by
        rintro ⟨e, he⟩ ⟨f, hf⟩
        refine huniq _ (hκK _ (E.mul_mem he hf)) _ (K.mul_mem (hκK e he) (hκK f hf)) fun x hx => ?_
        rw [← hκ _ (E.mul_mem he hf) x hx]
        have h1 := hκ f hf x hx
        have h2 := hκ e he (κ f hf * x * (κ f hf)⁻¹)
          (K.mul_mem (K.mul_mem (hκK f hf) hx) (K.inv_mem (hκK f hf)))
        calc e * f * x * (e * f)⁻¹ = e * (f * x * f⁻¹) * e⁻¹ := by group
          _ = e * (κ f hf * x * (κ f hf)⁻¹) * e⁻¹ := by rw [h1]
          _ = κ e he * (κ f hf * x * (κ f hf)⁻¹) * (κ e he)⁻¹ := h2
          _ = κ e he * κ f hf * x * (κ e he * κ f hf)⁻¹ := by group }
  have hφK : φ.range ≤ K := by
    rintro _ ⟨⟨e, he⟩, rfl⟩
    exact hκK e he
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, he⟩ h1
    by_contra hne
    have he1 : e ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨x, hx, hxne⟩ := hker e he he1
    apply hxne
    rw [hκ e he x hx]
    change κ e he = 1 at h1
    rw [h1]; group
  have hcard : Nat.card φ.range = p ^ 2 := by
    rw [← hEc, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hab : IsElemAbelian p φ.range := by
    refine ⟨⟨⟨fun ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩ => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← φ.map_mul, ← φ.map_mul]
      congr 1
      exact hE.1.is_comm.comm a b
    · rintro _ ⟨⟨a, ha⟩, rfl⟩
      rw [← φ.map_pow]
      have : (⟨a, ha⟩ : E) ^ p = 1 := Subtype.ext (by simpa using hE.2 a ha)
      rw [this, φ.map_one]
  refine le_trans (hgen φ.range hφK hab hcard) (iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_)
  obtain ⟨⟨e, he⟩, rfl⟩ := ha
  have he1 : e ≠ 1 := by
    rintro rfl
    exact ha1 (show φ 1 = 1 from φ.map_one)
  refine le_trans (fun x hx => Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hx).2⟩)
    (centralizer_inf_le_gammaOver he he1 (hE.2 e he))
  have hxa := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hκ e he x (Subgroup.mem_inf.mp hx).2
  change x * κ e he = κ e he * x at hxa
  have : e * x * e⁻¹ = x := by rw [h, ← hxa]; group
  calc x * e = e * x * e⁻¹ * e := by rw [this]
    _ = e * x := by group

theorem exists_inner_of_card_outer_le_two {K : Subgroup X} [K.Normal]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) ≤ 2)
    (hp2 : p ≠ 2) {e : X} (hep : e ^ p = 1) :
    ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := by
  have hp : p.Prime := Fact.out
  set q : CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K :=
    QuotientGroup.mk (MulAut.conjNormal e) with hq
  have hqp : q ^ p = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, ← map_pow, hep, map_one, QuotientGroup.mk_one]
  have hfin : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    Nat.finite_of_card_ne_zero (by
      intro h0
      have := Nat.card_pos (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)
      omega)
  have hq1 : q = 1 := by
    have h1 : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hqp
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have h2 : orderOf q ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
        orderOf_dvd_natCard q
      rw [h] at h2
      have := Nat.le_of_dvd (Nat.card_pos) h2
      have := hp.two_le
      omega
  have hmem : MulAut.conjNormal e ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
    (QuotientGroup.eq_one_iff _).mp hq1
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, k.2, fun x hx => ?_⟩
  have := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : X)) hk
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at this
  exact this.symm

theorem le_iSup_centralizer_inf_of_centGen {K A : Subgroup X} (hAK : A ≤ K)
    (h : centGen (A.subgroupOf K) = ⊤) :
    K ≤ ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ K := by
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥K) ∈ centGen (A.subgroupOf K) := h ▸ Subgroup.mem_top _
  have hmap : (centGen (A.subgroupOf K)).map K.subtype ≤
      ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ K := by
    rw [centGen, Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha1 => ?_
    refine le_trans ?_ (le_iSup_of_le (a : X) (le_iSup_of_le (Subgroup.mem_subgroupOf.mp ha)
      (le_iSup_of_le (fun h1 => ha1 (Subtype.ext h1)) le_rfl)))
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
    have hy' : y ∈ Subgroup.centralizer ({a} : Set ↥K) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy' ⊢
    exact congrArg Subtype.val hy'
  exact hmap ⟨⟨x, hx⟩, hx', rfl⟩

end Reduction

section Rows

theorem pRank_top_le_two_of_not_cube {L : Type*} [Group L] [Finite L]
    (hcube : ¬ p ^ 3 ∣ Nat.card L) : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ 2 := by
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hc⟩
  by_contra hk
  exact hcube ((pow_dvd_pow p (by omega : 3 ≤ k)).trans (hc ▸ Subgroup.card_subgroup_dvd_card E))

theorem centGen_eq_top_of_not_cube {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    (hcube : ¬ p ^ 3 ∣ Nat.card L)
    (hΓ : ∀ T : Sylow p L, ¬ IsCyclic (T : Subgroup L) → GLBCore p 1 (T : Subgroup L) = ⊤)
    (A : Subgroup L) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : centGen A = ⊤ := by
  have hp : p.Prime := Fact.out
  have hAp : IsPGroup p A := IsPGroup.of_card hAc
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra h
    exact hcube ((pow_dvd_pow p (by omega : 3 ≤ n)).trans
      (hn ▸ Subgroup.card_subgroup_dvd_card (T : Subgroup L)))
  have hTA : (T : Subgroup L) = A := by
    refine (Subgroup.eq_of_le_of_card_ge hAT ?_).symm
    rw [hn, hAc]
    exact Nat.pow_le_pow_right hp.pos hn2
  have hab : IsMulCommutative (T : Subgroup L) := hTA ▸ hA.1
  have hnc : ¬ IsCyclic (T : Subgroup L) := by
    intro hcyc
    rw [hTA] at hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hA.2 g g.2)
    have := orderOf_dvd_of_pow_eq_one hgp
    rw [hg, hAc] at this
    have := Nat.le_of_dvd hp.pos this
    nlinarith [hp.two_le]
  rw [← hTA]
  exact centGen_eq_top_of_glbCore T hab (hΓ T hnc)

theorem glbCore_eq_top_of_provedRow (hrows : CFSG.AGLEmbedding.SporProvedRows)
    {s : TauCeti.SporadicName} (hpr : (s, p) ∈ CFSG.AGLEmbeddingD2.d2SporadicProvedList)
    (hp2 : p ≠ 2) {L : Type} [Group L] [Finite L]
    (e : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcube : ¬ p ^ 3 ∣ Nat.card L) (T : Sylow p L)
    (hT : ¬ IsCyclic (T : Subgroup L)) : GLBCore p 1 (T : Subgroup L) = ⊤ := by
  by_contra hΓ
  exact CFSG.AGLEmbedding.false_of_d2DatumPlus Fact.out hp2 (hrows s p hpr L e) T hT hΓ
    (pRank_top_le_two_of_not_cube hcube)

end Rows

section Cases

open TauCeti CFSG.Blueprint CFSG.AGLEmbeddingD2

@[expose] def SporadicCentGen (p : ℕ) (s : SporadicName) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* s.Group) →
    ∀ A : Subgroup L, IsElemAbelian p A → Nat.card A = p ^ 2 → centGen A = ⊤

theorem centGen_of_ne_M (hrows : CFSG.AGLEmbedding.SporProvedRows)
    (hbr : ∀ s : SporadicName, Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hcard : ∀ s : SporadicName, s ≠ .M → Nat.card (NativeSporadic.Carrier s) = d2SporadicOrder s)
    (hB7 : CFSG.AGLEmbedding.SporGammaOneAt .B 7) (hTh5 : SporadicCentGen 5 .Th)
    {s : SporadicName} (hs : s ≠ .M) (hp5 : 5 ≤ p)
    (hnot : ¬ CFSG.LocalAnalysis.AGL81I.Section3.SporadicIn24_12 p s)
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (e : L ≃* s.Group)
    (A : Subgroup L) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : centGen A = ⊤ := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨f⟩ := hbr s
  have eL : L ≃* NativeSporadic.Carrier s := e.trans f.symm
  have hL : Nat.card L = d2SporadicOrder s := (Nat.card_congr eL.toEquiv).trans (hcard s hs)
  have hsq : p ^ 2 ∣ d2SporadicOrder s := hL ▸ hAc ▸ Subgroup.card_subgroup_dvd_card A
  rcases (d2SporadicSq_iff s p).1 ⟨hs, hp, hp2, hsq⟩ with hpr | hleaf | hopen
  · have hrow := fun (hcube : ¬ p ^ 3 ∣ Nat.card L) =>
      centGen_eq_top_of_not_cube hcube
        (glbCore_eq_top_of_provedRow hrows hpr hp2 ⟨eL⟩ hcube) A hA hAc
    simp only [d2SporadicProvedList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hpr
    rcases hpr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | omega
      | (simp [CFSG.LocalAnalysis.AGL81I.Section3.SporadicIn24_12] at hnot; done)
      | exact hTh5 L ⟨e⟩ A hA hAc
      | exact hrow (by rw [hL]; norm_num [d2SporadicOrder])
  · simp only [d2SporadicLeafList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hleaf
    rcases hleaf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | omega
      | (simp [CFSG.LocalAnalysis.AGL81I.Section3.SporadicIn24_12] at hnot; done)
  · simp only [d2SporadicOpenList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hopen
    rcases hopen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | (simp [CFSG.LocalAnalysis.AGL81I.Section3.SporadicIn24_12] at hnot; done)
      | exact centGen_eq_top_of_not_cube (by rw [hL]; norm_num [d2SporadicOrder])
          (fun T _ => hB7 L ⟨e⟩ T) A hA hAc

theorem eq_of_sq_dvd_monsterOrder {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (h : q ^ 2 ∣ CFSG.Open.monsterOrder) : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 := by
  have hdvd : q ∣ CFSG.Open.monsterOrder := (dvd_pow_self q two_ne_zero).trans h
  have hmem : q ∈ Nat.primeFactors CFSG.Open.monsterOrder :=
    Nat.mem_primeFactors.mpr ⟨hq, hdvd, by norm_num [CFSG.Open.monsterOrder]⟩
  have hpf : Nat.primeFactors CFSG.Open.monsterOrder =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71} := by
    simp only [CFSG.Open.monsterOrder]
    repeat rw [Nat.primeFactors_mul (by positivity) (by positivity)]
    repeat rw [Nat.primeFactors_pow _ (by norm_num)]
    simp only [Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 3), Nat.Prime.primeFactors (by norm_num : Nat.Prime 5),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 7), Nat.Prime.primeFactors (by norm_num : Nat.Prime 11),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 13), Nat.Prime.primeFactors (by norm_num : Nat.Prime 17),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 19), Nat.Prime.primeFactors (by norm_num : Nat.Prime 23),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 29), Nat.Prime.primeFactors (by norm_num : Nat.Prime 31),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 41), Nat.Prime.primeFactors (by norm_num : Nat.Prime 47),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 59), Nat.Prime.primeFactors (by norm_num : Nat.Prime 71)]
    decide
  rw [hpf] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> first | omega | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
    (right; right; right; rfl) | (exfalso; revert h; norm_num [CFSG.Open.monsterOrder])

theorem centGen_of_M
    (hcardM : Nat.card (NativeSporadic.Carrier .M) = CFSG.Open.monsterOrder)
    (hbrM : Nonempty (NativeSporadic.Carrier .M ≃* SporadicName.M.Group))
    (hM11 : CFSG.AGLEmbedding.SporGammaOneAt .M 11) (hM13 : SporadicCentGen 13 .M)
    (hp5 : 5 ≤ p) (hp5' : p ≠ 5)
    (hnot : ¬ CFSG.LocalAnalysis.AGL81I.Section3.SporadicIn24_12 p .M)
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (e : L ≃* SporadicName.M.Group)
    (A : Subgroup L) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : centGen A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨f⟩ := hbrM
  have hL : Nat.card L = CFSG.Open.monsterOrder :=
    (Nat.card_congr (e.trans f.symm).toEquiv).trans hcardM
  have hsq : p ^ 2 ∣ CFSG.Open.monsterOrder := hL ▸ hAc ▸ Subgroup.card_subgroup_dvd_card A
  rcases eq_of_sq_dvd_monsterOrder hp hp5 hsq with rfl | rfl | rfl | rfl
  · exact absurd rfl hp5'
  · exact absurd (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩)) hnot
  · exact centGen_eq_top_of_not_cube (by rw [hL]; norm_num [CFSG.Open.monsterOrder])
      (fun T _ => hM11 L ⟨e⟩ T) A hA hAc
  · exact hM13 L ⟨e⟩ A hA hAc

end Cases

section Assembly

open TauCeti CFSG.Blueprint CFSG.AGLEmbeddingD2

theorem sporadicGen24_12Five_of_parts (hrows : CFSG.AGLEmbedding.SporProvedRows)
    (hbr : ∀ s : SporadicName, Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hcard : ∀ s : SporadicName, s ≠ .M → Nat.card (NativeSporadic.Carrier s) = d2SporadicOrder s)
    (hcardM : Nat.card (NativeSporadic.Carrier .M) = CFSG.Open.monsterOrder)
    (hout : ∀ s : SporadicName, Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (NativeSporadic.Carrier s)) ≤ 2)
    (hsimple : ∀ s : SporadicName, IsSimpleGroup (NativeSporadic.Carrier s))
    (hnonab : ∀ s : SporadicName, ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a)
    (hB7 : CFSG.AGLEmbedding.SporGammaOneAt .B 7) (hM11 : CFSG.AGLEmbedding.SporGammaOneAt .M 11)
    (hTh5 : SporadicCentGen 5 .Th) (hM13 : SporadicCentGen 13 .M)
    (hM5 : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* SporadicName.M.Group) →
      4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup L)) :
    CFSG.LocalAnalysis.AGL81I.Section3.SporadicGen24_12Five := by
  intro X _ _ K E p s hp hp5 hnot hKn ⟨φ⟩ hE hEc hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨f⟩ := hbr s
  let ψ : ↥K ≃* NativeSporadic.Carrier s := φ.trans f.symm
  haveI := hsimple s
  haveI : IsSimpleGroup ↥K := ψ.isSimpleGroup
  have hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1 := by
    intro k hk hcomm
    have hcen : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2).symm
    rcases (Subgroup.center ↥K).normal_of_characteristic.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab s
      apply hab
      have hc : ∀ x y : ↥K, x * y = y * x := fun x y =>
        (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top y) x)
      have := hc (ψ.symm a) (ψ.symm b)
      simpa using congrArg ψ this
  haveI : K.Normal := hKn
  have hout' : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) ≤ 2 :=
    (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence ψ).toEquiv).le.trans
      (hout s)
  have hinn : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := fun e he =>
    exists_inner_of_card_outer_le_two hout' hp2 (hE.2 e he)
  by_cases hM5p : s = .M ∧ p = 5
  · exfalso
    obtain ⟨rfl, rfl⟩ := hM5p
    have h4 := hM5 ↥K ⟨φ⟩
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at h4
    have := (CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left).trans hrk
    omega
  refine le_gammaOver_of_inner hZ hinn hE hEc fun A hAK hA hAc => ?_
  refine le_iSup_centralizer_inf_of_centGen hAK ?_
  have hA' : IsElemAbelian p (A.subgroupOf K) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · simpa using congrArg Subtype.val (hA.1.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
    · simpa using hA.2 x (Subgroup.mem_subgroupOf.mp hx)
  have hAc' : Nat.card (A.subgroupOf K) = p ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv).trans hAc
  by_cases hs : s = .M
  · subst hs
    have hp5' : p ≠ 5 := fun h => hM5p ⟨rfl, h⟩
    exact centGen_of_M hcardM (hbr .M) hM11 hM13 hp5 hp5' hnot φ _ hA' hAc'
  · exact centGen_of_ne_M hrows hbr hcard hB7 hTh5 hs hp5 hnot φ _ hA' hAc'

section Producer

open TauCeti CFSG.Blueprint CFSG.AGLEmbeddingD2

set_option linter.unusedSectionVars false

theorem sporadicGen24_12Five_of_inputs
    (hTh5 : SporadicCentGen 5 .Th)
    (hM13 : SporadicCentGen 13 .M) :
    CFSG.LocalAnalysis.AGL81I.Section3.SporadicGen24_12Five := by
  have hMfacts := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_M
    CFSG.Milestones.fam_m_finiteness CFSG.Milestones.fam_m_simplicity
  have hMcard : Nat.card (NativeSporadic.Carrier .M) = CFSG.Open.monsterOrder :=
    (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans
      CFSG.Milestones.fam_m_finiteness
  haveI : Finite (NativeSporadic.Carrier .M) := hMfacts.1
  have hMout : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (NativeSporadic.Carrier .M)) ≤ 2 :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds _ hMfacts.2.1 hMfacts.2.2.2 .M
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M)
  have hfacts : ∀ s, CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CarrierFacts s :=
    fun s => if hs : s = .M then hs ▸ hMfacts else
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M s hs
  refine sporadicGen24_12Five_of_parts CFSG.AGLEmbedding.sporProvedRows
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group card_carrier_eq_d2SporadicOrder hMcard
    (fun s => if hs : s = .M then hs ▸ hMout else card_outer_carrier_le_two_of_ne_M s hs)
    (fun s => (hfacts s).2.1) (fun s => (hfacts s).2.2.2)
    CFSG.AGLEmbedding.sporGammaOneAt_B_seven CFSG.AGLEmbedding.Norton.sporGammaOneAt_M_eleven_holds
    hTh5 hM13 fun L _ _ he => ?_
  obtain ⟨E, hE, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.H1017.i1017MonsterFiveRank_holds L ⟨_, rfl, he⟩
  exact CFSG.AGLEmbedding.le_pRank_of_pow_le_card (by norm_num) le_top hE hc.ge

end Producer

end Assembly

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen

