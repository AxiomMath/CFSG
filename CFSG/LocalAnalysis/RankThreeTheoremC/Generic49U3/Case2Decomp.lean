module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem dec_exists_conj_hom (J H : Subgroup G) (hH : H ≤ Subgroup.normalizer (J : Set G)) :
    ∃ ι : H →* MulAut J, ∀ (c : H) (j : J), ((ι c j : J) : G) = (c : G) * j * (c : G)⁻¹ := by
  let f : ∀ c : G, c ∈ Subgroup.normalizer (J : Set G) → MulAut J := fun c hc =>
    { toFun := fun j => ⟨c * j * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc j).mp j.2⟩
      invFun := fun j => ⟨c⁻¹ * j * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hc) j).mp j.2⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  refine ⟨{ toFun := fun c => f c (hH c.2), map_one' := ?_, map_mul' := ?_ }, fun c j => rfl⟩
  · ext j; simp [f]
  · intro a b; ext j; simp [f, mul_assoc]

private theorem dec_exists_descent {J Q H : Type} [Group J] [Group Q] [Group H] (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (ι : H →* MulAut J)
    (h : ∀ c j, ψ j = 1 → ψ (ι c j) = 1) :
    ∃ θ : H →* MulAut Q, ∀ c j, θ c (ψ j) = ψ (ι c j) := by
  have key : ∀ c : H, ∃ f : Q →* Q, ∀ j, f (ψ j) = ψ (ι c j) := by
    intro c
    refine ⟨ψ.liftOfSurjective hψ ⟨ψ.comp (ι c).toMonoidHom, fun j hj => h c j hj⟩, fun j => ?_⟩
    simp
  choose F hF using key
  have hmul : ∀ c d : H, ∀ q, F (c * d) q = F c (F d q) := by
    intro c d q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF, hF, hF]
    simp
  have hone : ∀ q, F 1 q = q := by
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF]
    simp
  let θ' : ∀ c : H, MulAut Q := fun c =>
    { toFun := F c
      invFun := F c⁻¹
      left_inv := fun q => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := (F c).map_mul }
  refine ⟨{ toFun := θ', map_one' := ?_, map_mul' := ?_ }, fun c j => hF c j⟩
  · ext q; exact hone q
  · intro a b; ext q; exact hmul a b q

theorem u3_P_decomp_core {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) {k : ℕ}
    (hTcard : Nat.card (u3T P x J) = p ^ k)
    (hAut : ∀ (K : Type) [Group K] [Finite K], Typ p K → Subgroup.center K = ⊥ →
      ∀ S : Subgroup (MulAut K), IsPGroup p S → Nat.card S ∣ p ^ k) :
    (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := hP.trans hc.cent_le
  obtain ⟨ι, hι⟩ := dec_exists_conj_hom J (P : Subgroup G) hPN
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hιker : ∀ (c : (P : Subgroup G)) (j : J), ψ j = 1 → ψ (ι c j) = 1 := by
    intro c j hj
    rw [hOker] at hj ⊢
    rw [hι]
    exact u3_core_conj (hPN c.2) hj
  obtain ⟨θ, hθ⟩ := dec_exists_descent ψ hψ ι hιker
  have hθK : ∀ c : (P : Subgroup G), θ c = 1 → (c : G) ∈ u3K0 p x J := by
    intro c hc1
    refine ⟨hP c.2, hPN c.2, fun j hj => ?_⟩
    have h1 : ψ (ι c ⟨j, hj⟩) = ψ ⟨j, hj⟩ := by
      rw [← hθ, hc1]; rfl
    have h2 : ψ ((ι c ⟨j, hj⟩) * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hOker _).mp h2
    simpa [hι] using h3
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  set T₀ : Subgroup (P : Subgroup G) := (u3T P x J).subgroupOf (P : Subgroup G) with hT₀
  have hinj : Function.Injective (θ.comp T₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have htK : ((t : (P : Subgroup G)) : G) ∈ u3K0 p x J := hθK t ht
    have htT : ((t : (P : Subgroup G)) : G) ∈ u3T P x J := t.2
    have : ((t : (P : Subgroup G)) : G) ∈ u3T P x J ⊓ u3K0 p x J := ⟨htT, htK⟩
    rw [u3_T_inf_K0_gen hc, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hcardT : Nat.card ↥(T₀.map θ) = p ^ k := by
    have e1 : (θ.comp T₀.subtype).range = T₀.map θ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv]
    exact hTcard
  have hSp : IsPGroup p θ.range :=
    P.isPGroup'.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  haveI : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  have hdvd : Nat.card θ.range ∣ p ^ k := hAut Q hQ hZ θ.range hSp
  have hA : T₀.map θ = θ.range :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_range θ T₀) (by
      rw [hcardT]; exact Nat.le_of_dvd (pow_pos hp.pos k) hdvd)
  intro s hs
  have hs' : θ ⟨s, hs⟩ ∈ T₀.map θ := by
    rw [hA]; exact ⟨⟨s, hs⟩, rfl⟩
  obtain ⟨t, ht, htθ⟩ := hs'
  have hkθ : θ (t⁻¹ * ⟨s, hs⟩) = 1 := by rw [map_mul, map_inv, htθ, inv_mul_cancel]
  have hkK := hθK _ hkθ
  have hkP : ((t⁻¹ * ⟨s, hs⟩ : (P : Subgroup G)) : G) ∈ (P : Subgroup G) :=
    (t⁻¹ * ⟨s, hs⟩).2
  have hsd : s = (t : G) * ((t⁻¹ * ⟨s, hs⟩ : (P : Subgroup G)) : G) := by
    simp
  rw [hsd]
  exact Subgroup.mul_mem_sup ht ⟨hkP, hkK⟩

theorem u3_P_decomp_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hTstr : TypeTStruct p P x J) (hAut : TypeAutPCard Typ p) :
    (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) :=
  u3_P_decomp_core hc hP hTstr.1 hAut

private theorem dec_inf_core (hp : p.Prime) :
    (P : Subgroup G) ⊓ rankThreePrimeCore p J = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ rankThreePrimeCore p J) := P.isPGroup'.to_inf_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  have hdvd : Nat.card ((P : Subgroup G) ⊓ rankThreePrimeCore p J : Subgroup G) ∣
      Nat.card (rankThreePrimeCore p J) := Subgroup.card_dvd_of_le inf_le_right
  have hk0 : k = 0 := by
    by_contra hk0
    have : p ∣ Nat.card (rankThreePrimeCore p J) := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
    exact (hp.coprime_iff_not_dvd.mp hOcop) this
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

private theorem dec_mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {s : G} (hs : s ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => h a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem u3_pdata_common {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hSdec : TypeSDecomp p P x J)
    (hdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J)) :
    u3T P x J ≤ (P : Subgroup G) ∧ (P : Subgroup G) ⊓ u3K0 p x J ≤ (P : Subgroup G) ∧
      u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) = (P : Subgroup G) ∧
      u3T P x J ⊓ ((P : Subgroup G) ⊓ u3K0 p x J) = ⊥ ∧
      (∀ t ∈ u3T P x J, ∀ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, t * d = d * t) ∧
      IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J) ∧ x ∈ (P : Subgroup G) ⊓ u3K0 p x J ∧ orderOf x = p := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := hP.trans hc.cent_le
  have hPO := dec_inf_core (P := P) (J := J) hp
  have hinf : u3T P x J ⊓ ((P : Subgroup G) ⊓ u3K0 p x J) = ⊥ := by
    rw [eq_bot_iff, ← u3_T_inf_K0_gen hc]
    exact inf_le_inf_left _ inf_le_right
  have hTconj : ∀ a ∈ (P : Subgroup G), ∀ t ∈ u3T P x J, a * t * a⁻¹ ∈ u3T P x J := by
    intro a ha t ht
    have ht' : (t ∈ (P : Subgroup G) ∧ t ∈ Subgroup.centralizer ({x} : Set G)) ∧ t ∈ J := ht
    have h1 : a * t * a⁻¹ ∈ (P : Subgroup G) := mul_mem (mul_mem ha ht'.1.1) (inv_mem ha)
    have h2 : a * t * a⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
      mul_mem (mul_mem (hP ha) ht'.1.2) (inv_mem (hP ha))
    have h3 : a * t * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hPN ha) t).mp ht'.2
    exact ⟨⟨h1, h2⟩, h3⟩
  have hcomm : ∀ t ∈ u3T P x J, ∀ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, t * d = d * t := by
    intro t ht d hd
    obtain ⟨hdP, -, -, hdO⟩ := hd
    have h1 : d * t * d⁻¹ * t⁻¹ ∈ rankThreePrimeCore p J := hdO t ht.2
    have h2 : d * t * d⁻¹ * t⁻¹ ∈ u3T P x J := mul_mem (hTconj d hdP t ht) (inv_mem ht)
    have h3 : d * t * d⁻¹ * t⁻¹ ∈ (P : Subgroup G) ⊓ rankThreePrimeCore p J := ⟨hTP h2, h1⟩
    rw [hPO, Subgroup.mem_bot] at h3
    have h4 : d * t = t * d := by
      calc d * t = d * t * d⁻¹ * t⁻¹ * (t * d) := by group
        _ = t * d := by rw [h3, one_mul]
    exact h4.symm
  have hDP : (P : Subgroup G) ⊓ u3K0 p x J ≤ (P : Subgroup G) := inf_le_left
  have hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J) := by
    obtain ⟨Z, hZc, -, hZS, hZT, -, hTZS⟩ := hSdec
    have hS : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hP
    rw [hS] at hZS hTZS
    haveI := hZc
    let T₀ : Subgroup (P : Subgroup G) := (u3T P x J).subgroupOf (P : Subgroup G)
    haveI hT₀n : T₀.Normal := ⟨fun n hn g => hTconj g g.2 n hn⟩
    let q : (P : Subgroup G) →* (P : Subgroup G) ⧸ T₀ := QuotientGroup.mk' T₀
    let g : Z →* (P : Subgroup G) ⧸ T₀ := q.comp (Subgroup.inclusion hZS)
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
      have hs : (s : G) ∈ u3T P x J ⊔ Z := by rw [hTZS]; exact s.2
      obtain ⟨t, ht, z, hz, hsz⟩ := dec_mem_sup_of_commute (fun a ha b hb => (hZT b hb a ha).symm) hs
      refine ⟨⟨z, hz⟩, ?_⟩
      have hts : (⟨t, hTP ht⟩ : (P : Subgroup G)) ∈ T₀ := ht
      have hsz' : s = ⟨t, hTP ht⟩ * ⟨z, hZS hz⟩ := Subtype.ext hsz
      show (QuotientGroup.mk (⟨z, hZS hz⟩ : (P : Subgroup G)) : (P : Subgroup G) ⧸ T₀) =
        QuotientGroup.mk s
      rw [hsz', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := T₀) _).mpr hts, one_mul]
    haveI : IsCyclic ((P : Subgroup G) ⧸ T₀) := isCyclic_of_surjective g hg
    let f : ↥((P : Subgroup G) ⊓ u3K0 p x J) →* (P : Subgroup G) ⧸ T₀ :=
      q.comp (Subgroup.inclusion hDP)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro d hd
      have hd' : (QuotientGroup.mk (Subgroup.inclusion hDP d) : (P : Subgroup G) ⧸ T₀) = 1 := hd
      have hdT0 : Subgroup.inclusion hDP d ∈ T₀ := (QuotientGroup.eq_one_iff (N := T₀) _).mp hd'
      have hdT : (d : G) ∈ u3T P x J := hdT0
      have : (d : G) ∈ u3T P x J ⊓ ((P : Subgroup G) ⊓ u3K0 p x J) := ⟨hdT, d.2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact Subtype.ext this
    exact isCyclic_of_injective f hf
  have hxD : x ∈ (P : Subgroup G) ⊓ u3K0 p x J := ⟨hc.generic.1, x_mem_u3K0_gen hc⟩
  have hsup : u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) = (P : Subgroup G) :=
    le_antisymm (sup_le hTP hDP) hdec
  have hord : orderOf x = p := orderOf_eq_prime hc.generic.2.1.2.2.1 hc.generic.2.1.2.1
  exact ⟨hTP, hDP, hsup, hinf, hcomm, hDcyc, hxD, hord⟩

theorem u3_pdata_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hTstr : TypeTStruct p P x J) (hSdec : TypeSDecomp p P x J) (hAut : TypeAutPCard Typ p) :
    PGroupData p (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 p x J) x := by
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := id hTstr
  obtain ⟨hTP, hDP, hsup, hinf, hcomm, hDcyc, hxD, hord⟩ :=
    u3_pdata_common hc hP hSdec (u3_P_decomp_gen hc hP hTstr hAut)
  exact ⟨hTP, hDP, hsup, hinf, hcomm, hTcard, hTexp, hTnab, hDcyc, hxD, hord⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
