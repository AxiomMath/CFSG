module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.AGLEmbedding

section Criterion

variable {K : Type} [Group K]

private def fixSub (S : Set K) : Subgroup (MulAut K) where
  carrier := {α | ∀ x ∈ S, α x = x}
  mul_mem' := fun {a b} ha hb x hx => by rw [MulAut.mul_apply, hb x hx, ha x hx]
  one_mem' := fun x _ => rfl
  inv_mem' := fun {a} ha x hx => by
    calc a⁻¹ x = a⁻¹ (a x) := by rw [ha x hx]
      _ = x := by simp

private def fixedPoints (W : Subgroup (MulAut K)) : Subgroup K where
  carrier := {x | ∀ α ∈ W, α x = x}
  mul_mem' := fun {a b} ha hb α hα => by rw [map_mul, ha α hα, hb α hα]
  one_mem' := fun α _ => map_one α
  inv_mem' := fun {a} ha α hα => by rw [map_inv, ha α hα]

private theorem aut_mul_conj_mul_inv (α : MulAut K) (g : K) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.conj_apply]

private theorem eq_one_of_mem_of_mem_map_conj {p : ℕ} {U : Subgroup K} (hU : IsPGroup p U)
    {W : Subgroup (MulAut K)} (hW : Nat.Coprime p (Nat.card W)) {β : MulAut K} (hβW : β ∈ W)
    (hβU : β ∈ U.map (MulAut.conj : K →* MulAut K)) : β = 1 := by
  obtain ⟨u, hu, rfl⟩ := hβU
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have h1 : (MulAut.conj u) ^ p ^ k = 1 := by
    rw [← map_pow]
    have : u ^ p ^ k = 1 := congrArg Subtype.val hk
    rw [this, map_one]
  have h2 : orderOf (MulAut.conj u) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (MulAut.conj u) ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hβW
  have h4 : Nat.Coprime (orderOf (MulAut.conj u)) (p ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h3 hW.symm)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h2)

private theorem map_eq_of_ti {p : ℕ} [Fact p.Prime] [Finite K] (U : Sylow p K)
    (hti : ∀ t ∈ (U : Subgroup K), t ≠ 1 → ∀ g : K, g * t * g⁻¹ ∈ (U : Subgroup K) →
      g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K))
    (α : MulAut K) {e : K} (heU : e ∈ (U : Subgroup K)) (he1 : e ≠ 1) (hαe : α e = e) :
    (U : Subgroup K).map α.toMonoidHom = (U : Subgroup K) := by
  have hsurj : Function.Surjective α.toMonoidHom := α.surjective
  have hQ : ((U.mapSurjective hsurj : Sylow p K) : Subgroup K) =
      (U : Subgroup K).map α.toMonoidHom := Sylow.coe_mapSurjective hsurj U
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K U (U.mapSurjective hsurj)
  have heQ : e ∈ ((U.mapSurjective hsurj : Sylow p K) : Subgroup K) := by
    rw [hQ]
    exact ⟨e, heU, hαe⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at heQ
  obtain ⟨s, hs, hse⟩ := heQ
  have hge : g * s * g⁻¹ = e := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hse
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply he1
    rw [← hge]
    group
  have hgN : g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K) :=
    hti s hs hs1 g (hge ▸ heU)
  rw [← hQ, ← hg, Sylow.smul_eq_iff_mem_normalizer.2 hgN]

private theorem le_fixSub_of_plane {p : ℕ} [Fact p.Prime] [Finite K] (U : Sylow p K)
    (hZ : Function.Injective (MulAut.conj : K →* MulAut K))
    (hti : ∀ t ∈ (U : Subgroup K), t ≠ 1 → ∀ g : K, g * t * g⁻¹ ∈ (U : Subgroup K) →
      g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K))
    (W : Subgroup (MulAut K)) (hW : Nat.Coprime p (Nat.card W))
    (hnorm : ∀ g ∈ (U : Subgroup K), ∀ w ∈ W, MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ W)
    (E : Subgroup K) (hEU : E ≤ (U : Subgroup K)) (hEcard : Nat.card E = p ^ 2)
    (hEexp : ∀ y ∈ E, y ^ p = 1) : W ≤ fixSub (E : Set K) := by
  set actor : Subgroup (MulAut K) := E.map (MulAut.conj : K →* MulAut K) with hactor
  have hpower : ∀ member : actor, member ^ p = 1 := by
    rintro ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    show (MulAut.conj y) ^ p = 1
    rw [← map_pow, hEexp y hy, map_one]
  have hcard : Nat.card actor = p ^ 2 := by
    rw [hactor, Subgroup.card_map_of_injective hZ, hEcard]
  have hcomp : ¬ p ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hW
  have hnormalized : actor ≤ Subgroup.normalizer (W : Set (MulAut K)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm y (hEU hy) h hh, fun hh => ?_⟩
    have := hnorm y⁻¹ (inv_mem (hEU hy)) _ hh
    simpa [map_inv, mul_assoc] using this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    Fact.out actor W hpower hcard hcomp hnormalized
  refine hgen.le.trans (iSup_le fun member => iSup_le fun hne => ?_)
  obtain ⟨m, hm⟩ := member
  obtain ⟨e, heE, rfl⟩ := hm
  have he1 : e ≠ 1 := by
    rintro rfl
    exact hne (Subtype.ext (map_one _))
  rintro α ⟨hαW, hαC⟩
  have hcomm : α * MulAut.conj e = MulAut.conj e * α :=
    Subgroup.mem_centralizer_singleton_iff.1 hαC
  have hαe : α e = e := by
    apply hZ
    rw [← aut_mul_conj_mul_inv, hcomm]
    group
  have hUα := map_eq_of_ti U hti α (hEU heE) he1 hαe
  have hαU : ∀ x ∈ (U : Subgroup K), α x ∈ (U : Subgroup K) := by
    intro x hx
    have : α x ∈ (U : Subgroup K).map α.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hUα] at this
  intro x hx
  set β : MulAut K := α * MulAut.conj x * α⁻¹ * (MulAut.conj x)⁻¹ with hβ
  have hβW : β ∈ W := by
    have h1 := hnorm x (hEU hx) α⁻¹ (W.inv_mem hαW)
    have h2 := W.mul_mem hαW h1
    simpa [hβ, mul_assoc] using h2
  have hβU : β ∈ (U : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
    refine ⟨α x * x⁻¹, (U : Subgroup K).mul_mem (hαU x (hEU hx)) (inv_mem (hEU hx)), ?_⟩
    rw [hβ, aut_mul_conj_mul_inv, map_mul, map_inv]
  have hβ1 : β = 1 := eq_one_of_mem_of_mem_map_conj U.isPGroup' hW hβW hβU
  apply hZ
  have : α * MulAut.conj x * α⁻¹ = MulAut.conj x := mul_inv_eq_one.1 hβ1
  rw [← aut_mul_conj_mul_inv, this]

theorem signalizer_eq_bot_of_ti_planes {p : ℕ} (hp : p.Prime) [Finite K] (U : Sylow p K)
    (hZ : Subgroup.center K = ⊥)
    (hti : ∀ t ∈ (U : Subgroup K), t ≠ 1 → ∀ g : K, g * t * g⁻¹ ∈ (U : Subgroup K) →
      g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K))
    (hinner : ∀ f : MulAut K, (∀ t ∈ (U : Subgroup K), f t = t) →
      ∃ u ∈ (U : Subgroup K), f = MulAut.conj u)
    (hgen : (U : Subgroup K) ≤ ⨆ (E : Subgroup K)
      (_ : E ≤ (U : Subgroup K) ∧ Nat.card E = p ^ 2 ∧ ∀ y ∈ E, y ^ p = 1), E)
    (W : Subgroup (MulAut K)) (hW : Nat.Coprime p (Nat.card W))
    (hnorm : ∀ g ∈ (U : Subgroup K), ∀ w ∈ W, MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ W) :
    W = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_trivial hZ
  have hfix : (U : Subgroup K) ≤ fixedPoints W := by
    refine hgen.trans (iSup_le fun E => iSup_le fun hE => fun x hx α hα => ?_)
    exact le_fixSub_of_plane U hinj hti W hW hnorm E hE.1 hE.2.1 hE.2.2 hα x hx
  rw [eq_bot_iff]
  intro α hα
  obtain ⟨u, hu, rfl⟩ := hinner α fun t ht => hfix ht α hα
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_of_mem_map_conj U.isPGroup' hW hα ⟨u, hu, rfl⟩

private theorem le_iSup_planes_of_card {p : ℕ} [Fact p.Prime] [Finite K] (U : Subgroup K)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card U = p ^ n) (hexp : ∀ x ∈ U, x ^ p = 1) :
    U ≤ ⨆ (E : Subgroup K) (_ : E ≤ U ∧ Nat.card E = p ^ 2 ∧ ∀ y ∈ E, y ^ p = 1), E := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  have hord : orderOf (⟨x, hx⟩ : U) = p := by
    apply orderOf_eq_prime
    · exact Subtype.ext (hexp x hx)
    · intro h
      exact hx1 (congrArg Subtype.val h)
  have hH : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : U)) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hdvd : p ^ (1 + 1) ∣ Nat.card U := by
    rw [hcard]
    exact pow_dvd_pow p (by omega)
  obtain ⟨E', hE'card, hE'le⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hH
  have hxE : x ∈ E'.map U.subtype := ⟨⟨x, hx⟩, hE'le (Subgroup.mem_zpowers _), rfl⟩
  refine Subgroup.mem_iSup_of_mem (E'.map U.subtype) (Subgroup.mem_iSup_of_mem ?_ hxE)
  exact ⟨Subgroup.map_subtype_le _,
    by rw [Subgroup.card_map_of_injective U.subtype_injective, hE'card],
    fun y hy => by
      obtain ⟨y', -, rfl⟩ := hy
      exact hexp y' y'.2⟩

end Criterion

section Families

theorem signalizerTrivialL2_holds : SignalizerTrivialL2 := by
  intro p _ hp5 K _ _ ⟨e⟩ P W hW hnorm
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hfs : Function.Surjective e.toMonoidHom := e.surjective
  have hmap := (Sylow.coe_mapSurjective hfs P).symm
  have D := SmallRankOneData.of_equiv e hmap (smallRankOneData_psl2GF hp2 (P.mapSurjective hfs))
  obtain ⟨hel, hcard⟩ := psl2GF_sylow p 2 (by norm_num) (P.mapSurjective hfs)
  have hPcard : Nat.card (P : Subgroup K) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
    exact hcard
  have hPexp : ∀ x ∈ (P : Subgroup K), x ^ p = 1 := by
    intro x hx
    have h1 : e x ∈ ((P.mapSurjective hfs : Sylow p (PSL2GF p 2)) : Subgroup (PSL2GF p 2)) := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    apply e.injective
    rw [map_pow, hel.2 (e x) h1, map_one]
  exact signalizer_eq_bot_of_ti_planes hp P D.center D.ti D.inner
    (le_iSup_planes_of_card _ le_rfl hPcard hPexp) W hW hnorm

theorem signalizerTrivialU3_holds : SignalizerTrivialU3 := by
  intro p hp hp5 K _ _ ⟨q, hqp, hq1, hv, ⟨e0⟩⟩ P W hW hnorm
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hIS : IsSmallUnitary p K := ⟨⟨.twistedA 2 q, hv⟩, ⟨q, hqp, hq1, rfl⟩, ⟨e0⟩⟩
  have D := smallRankOneData_of_isSmallUnitary hp hIS P
  have hd : IsUnitaryIndex p (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) := ⟨q, hqp, rfl⟩
  have hLd : Nonempty (K ≃* CatGroup (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)) := ⟨e0⟩
  have hfe : (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = 1 := by
    obtain ⟨q', -, hd', hfe, -⟩ := hd.exists_eq
    injection hd' with _ hqq
    subst hqq
    rw [hfe, hq1]
  obtain ⟨hcard, -, hexp, -⟩ := kFactUnitarySylowStructure K p _ hp2 hd hLd P
  rw [hfe] at hcard
  exact signalizer_eq_bot_of_ti_planes hp P D.center D.ti D.inner
    (le_iSup_planes_of_card _ (n := 3) (by norm_num) (by simpa using hcard) hexp) W hW hnorm

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
