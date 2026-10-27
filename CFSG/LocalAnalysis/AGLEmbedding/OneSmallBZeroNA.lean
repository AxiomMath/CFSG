module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroPlane
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
theorem mem_centerOf_iff_commute {R : Subgroup G} {a : G} :
    a ∈ centerOf R ↔ a ∈ R ∧ ∀ r ∈ R, r * a = a * r := Iff.rfl

theorem D1OneSmallData.card_center_inf_le (hd : D1OneSmallData p P M H R Rbar K)
    {T₁ : Sylow p K} (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :
    Nat.card (centerOf R ⊓ d1LiftX p H R K : Subgroup G) ≤
      Nat.card (Subgroup.center (T₁ : Subgroup K)) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hO := primeComplementCore_coprime (G := H) p
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRHp ha hb hab
  have hex : ∀ t : (centerOf R ⊓ d1LiftX p H R K : Subgroup G), ∃ s : (T₁ : Subgroup K),
      ((s : K) : H ⧸ primeComplementCore (G := H) p) =
        π ⟨t, hd.cfg.ext.le_H (mem_centerOf_iff_commute.mp t.2.1).1⟩ := by
    rintro ⟨t, htZ, t', ⟨htR, htK⟩, rfl⟩
    have hmem : π t' ∈ (T₁ : Subgroup K).map K.subtype := by
      rw [hT₁]
      exact ⟨by rw [hd.cfg.rbar]; exact ⟨t', htR, rfl⟩, htK⟩
    obtain ⟨s, hs, hseq⟩ := hmem
    exact ⟨⟨s, hs⟩, hseq⟩
  choose F hF using hex
  have hFc : ∀ t, F t ∈ Subgroup.center (T₁ : Subgroup K) := by
    intro t
    refine Subgroup.mem_center_iff.mpr fun s' => ?_
    have hs' : (((s' : (T₁ : Subgroup K)) : K) : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup _) := by
      have : (((s' : (T₁ : Subgroup K)) : K) : H ⧸ _) ∈ (T₁ : Subgroup K).map K.subtype :=
        ⟨s', s'.2, rfl⟩
      rw [hT₁] at this
      exact this.1
    rw [hd.cfg.rbar] at hs'
    obtain ⟨r, hr, hreq⟩ := hs'
    have htc := (mem_centerOf_iff_commute.mp t.2.1).2 r hr
    have h1 : π r * π ⟨t, hd.cfg.ext.le_H (mem_centerOf_iff_commute.mp t.2.1).1⟩ =
        π ⟨t, hd.cfg.ext.le_H (mem_centerOf_iff_commute.mp t.2.1).1⟩ * π r := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext htc
    rw [← hF t, hreq] at h1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  have hFinj : Function.Injective
      (fun t => (⟨F t, hFc t⟩ : Subgroup.center (T₁ : Subgroup K))) := by
    intro t₁ t₂ h
    have h1 : F t₁ = F t₂ := congrArg Subtype.val h
    have h2 := hF t₁
    rw [h1, hF t₂] at h2
    have h3 := hinj _ (show (⟨(t₂ : G), _⟩ : H) ∈ R.subgroupOf H from
      (mem_centerOf_iff_commute.mp t₂.2.1).1)
      _ (show (⟨(t₁ : G), _⟩ : H) ∈ R.subgroupOf H from (mem_centerOf_iff_commute.mp t₁.2.1).1) h2
    exact Subtype.ext (congrArg Subtype.val h3).symm
  exact Nat.card_le_card_of_injective _ hFinj

theorem D1OneSmallData.false_of_na (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hZT : Nat.card (Subgroup.center (T₁ : Subgroup K)) = p) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  obtain ⟨x, hxP, hxN, -, hxz⟩ := hd.exists_moving_elt hz hB0
  have hxM : x ∈ M := hd.cfg.ext.sylow_le hxP
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  set A := centerOf R with hAdef
  have hzA : z ∈ A := mem_centerOf_iff_commute.mpr ⟨hz.1, fun r hr =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRC hr))⟩
  have hxAN : x ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨haR, hac⟩ := mem_centerOf_iff_commute.mp ha
    refine mem_centerOf_iff_commute.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hxN a).mp haR, fun r hr => ?_⟩
    have hr' : x⁻¹ * r * x ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) r).mp hr
      simpa using this
    have h1 := hac _ hr'
    calc r * (x * a * x⁻¹) = x * ((x⁻¹ * r * x) * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * r * x)) * x⁻¹ := by rw [h1]
      _ = x * a * x⁻¹ * r := by group
  have hAR : A ≤ R := fun a ha => (mem_centerOf_iff_commute.mp ha).1
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    ((mem_centerOf_iff_commute.mp hb).2 a (hAR ha))
  have hAel : IsElemAbelian p A :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommA a a.2 b b.2)⟩⟩, fun a ha => hexpR a (hAR ha)⟩
  have hzp : orderOf z = p := hz.2.1
  set w := x * z * x⁻¹ with hw
  have hwA : w ∈ A := (Subgroup.mem_normalizer_iff.mp hxAN z).mp hzA
  have hwp : orderOf w = p := by
    have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective z
    rw [← hzp, ← this]
    rfl
  have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers w = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers z ⊓ Subgroup.zpowers w : Subgroup G) ∣ p := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers z ⊓ Subgroup.zpowers w ≤
        Subgroup.zpowers z)
      rwa [Nat.card_zpowers, hzp] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers z ⊓ Subgroup.zpowers w = Subgroup.zpowers w :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hwp])
      exact hxz ((heq ▸ (inf_le_left : Subgroup.zpowers z ⊓ Subgroup.zpowers w ≤ _))
        (Subgroup.mem_zpowers w))
  have hge : p ^ 2 ≤ Nat.card A := by
    have h1 := mul_card_le_of_inf_eq_bot (Subgroup.zpowers_le.mpr hzA)
      (Subgroup.zpowers_le.mpr hwA) hinf
    rw [Nat.card_zpowers, Nat.card_zpowers, hzp, hwp] at h1
    rw [sq]
    exact h1
  have hle : Nat.card A ≤ p ^ 2 := by
    have hdecA : ∀ r ∈ A, ∃ t ∈ A ⊓ d1LiftX p H R K, ∃ c ∈ Subgroup.zpowers z, t * c = r := by
      intro r hr
      obtain ⟨t, ht, i, hti⟩ := hdec r (hAR hr)
      refine ⟨t, ⟨?_, ht⟩, z ^ i, Subgroup.npow_mem_zpowers z i, hti.symm⟩
      have : t = r * (z ^ i)⁻¹ := by rw [hti]; group
      rw [this]
      exact A.mul_mem hr (A.inv_mem (A.pow_mem hzA i))
    have h1 := card_le_mul_of_decomp (Subgroup.zpowers_le.mpr hzA) hdecA
    have h2 := hd.card_center_inf_le hT₁
    rw [hZT] at h2
    rw [Nat.card_zpowers, hzp] at h1
    calc Nat.card A ≤ _ := h1
      _ ≤ p * p := Nat.mul_le_mul_right _ h2
      _ = p ^ 2 := (sq p).symm
  have hAcard : Nat.card A = p ^ 2 := le_antisymm hle hge
  obtain ⟨a, haA, ha1, -, hab⟩ := exists_axis_of_plane hp hAel hAcard hxAN hxk hzA hxz
  apply ha1
  refine eq_one_of_plane hp hp2 hd.cfg.glob.charTwo hd.cfg.loc.maxLocal.1
    (hAR.trans hd.cfg.ext.le_M) hAel hAcard haA fun b hb hba => ?_
  obtain ⟨j, hj⟩ := hab b hb hba
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hxjN : x ^ j ∈ Subgroup.normalizer (R : Set G) := Subgroup.pow_mem _ hxN j
  have h1 := twoCore_inf_centralizer_le_of_conj hp hzp (M.pow_mem hxM j) hxjN hQz hj hb1
  intro u hu
  have := h1 hu
  rw [Subgroup.mem_centralizer_iff] at this
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (this a (hAR haA)).symm

end Config

end CFSG.AGLEmbedding
