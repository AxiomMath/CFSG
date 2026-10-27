module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCInGen
import CFSG.GH74.Generic.GKFCover
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.ComponentClassification.CentralCover
  CFSG.Open

theorem mem_of_pow_mem_of_pow_eq_one {G : Type*} [Group G] {H : Subgroup G} {x : G} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : x ^ m ∈ H) (hn : x ^ n = 1) : x ∈ H := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hmn hn1
    have h := Nat.div_add_mod (m * u) n
    rw [hu] at h
    have hx : x = (x ^ m) ^ u := by
      rw [← pow_mul, ← h, pow_add, pow_mul, hn, one_pow, one_mul, pow_one]
    rw [hx]
    exact H.pow_mem hm u
  · interval_cases n
    · rw [Nat.coprime_zero_right] at hmn
      subst hmn
      simpa using hm
    · simp at hn
      rw [hn]
      exact H.one_mem

theorem kOutTwoGroup_of_isPGroup_outer {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hOut : IsPGroup 2 (Outer (K ⧸ Subgroup.center K))) :
    KOutTwoGroup K := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  intro f
  obtain ⟨k, hk⟩ := hOut (centerQuotientOuterHom K (QuotientGroup.mk' (inner K) f))
  refine ⟨k, ?_⟩
  have h1 : QuotientGroup.mk' (inner K) (f ^ (2 ^ k)) = 1 := by
    apply centerQuotient_outer_injective K
    rw [map_one, map_pow, map_pow]
    exact hk
  exact (QuotientGroup.eq_one_iff (N := inner K) _).mp h1

theorem kOutNormalSylow_three_of_kOutTwoGroup {K : Type} [Group K] [Finite K]
    (h : KOutTwoGroup K) : KOutNormalSylow 3 K := by
  intro S
  have hle : (S : Subgroup (MulAut K)) ≤ (MulAut.conj : K →* MulAut K).range := by
    intro s hs
    obtain ⟨b, hb⟩ := h s
    obtain ⟨a, ha⟩ := S.isPGroup' ⟨s, hs⟩
    have hs3 : s ^ (3 ^ a) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    exact mem_of_pow_mem_of_pow_eq_one (Nat.Coprime.pow _ _ (by norm_num)) hb hs3
  rw [sup_eq_left.mpr hle]
  exact innerNormal K

theorem card_center_eq_three_of_dvd {K : Type} [Group K] [Finite K]
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) {m : ℕ}
    (hdvd : Nat.card (Subgroup.center K) ∣ m) (hm : ¬ 3 ^ 2 ∣ m) :
    Nat.card (Subgroup.center K) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card).ne'
  · have hk0 : k = 0 := by
      by_contra hne
      exact hm ((pow_dvd_pow 3 (by omega : 2 ≤ k + 1)).trans (hk ▸ hdvd))
    subst hk0
    simpa using hk

theorem kGenTwoModAb_of_small {K X : Type} [Group K] [Finite K] [Group X]
    (hK : Open.IsQuasisimple K) (hZ3 : Nat.card (Subgroup.center K) = 3)
    (e : K ⧸ Subgroup.center K ≃* X) (h9 : 3 ^ 2 ∣ Nat.card X) (h27 : ¬ 3 ^ 3 ∣ Nat.card X)
    (hOut : KOutTwoGroup K) : KGenTwoModAb 3 K := by
  intro E hEab hEcard hcomm
  exfalso
  classical
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hEin : ∀ ε ∈ E, ε ∈ (MulAut.conj : K →* MulAut K).range := by
    intro ε hε
    obtain ⟨b, hb⟩ := hOut ε
    exact mem_of_pow_mem_of_pow_eq_one (Nat.Coprime.pow_left _ (by norm_num)) hb (hEab.2 ε hε)
  set T : Subgroup K := E.comap (MulAut.conj : K →* MulAut K) with hT
  have hmemT : ∀ t : K, t ∈ T ↔ MulAut.conj t ∈ E := fun t => Iff.rfl
  have hcen : ∀ g : K, MulAut.conj g = 1 → g ∈ Subgroup.center K := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut K => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  have hcenterT : Subgroup.center K ≤ T := by
    intro z hz
    rw [hmemT]
    have : (MulAut.conj z : MulAut K) = 1 := by
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← Subgroup.mem_center_iff.mp hz x]
      group
    rw [this]
    exact E.one_mem
  have hzexp : ∀ z ∈ Subgroup.center K, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  have hTp : IsPGroup 3 T := by
    intro t
    refine ⟨2, ?_⟩
    apply Subtype.ext
    have h1 : (MulAut.conj (t : K)) ^ 3 = 1 := hEab.2 _ t.2
    have h2 : MulAut.conj ((t : K) ^ 3) = 1 := by rw [map_pow]; exact h1
    have h3 := hzexp _ (hcen _ h2)
    have h4 : ((t : K)) ^ (3 ^ 2) = 1 := by
      rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h3
    simpa using h4
  let φ : T →* E := (MulAut.conj : K →* MulAut K).subgroupComap E
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ε, hε⟩
    obtain ⟨k, hk⟩ := hEin ε hε
    exact ⟨⟨k, by rw [hmemT, hk]; exact hε⟩, Subtype.ext hk⟩
  have hcard := CFSG.GH74.Generic.card_eq_card_mul_card_ker φ hφsurj
  have hker : 3 ≤ Nat.card φ.ker := by
    have hmem : ∀ z : Subgroup.center K, (⟨(z : K), hcenterT z.2⟩ : T) ∈ φ.ker := by
      intro z
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      ext x
      have hz := Subgroup.mem_center_iff.mp z.2 x
      show (MulAut.conj (z : K) : MulAut K) x = x
      rw [MulAut.conj_apply, ← hz]
      group
    have hinj : Function.Injective (fun z : Subgroup.center K => (⟨_, hmem z⟩ : φ.ker)) := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun w : φ.ker => ((w : T) : K)) hab
    calc 3 = Nat.card (Subgroup.center K) := hZ3.symm
      _ ≤ Nat.card φ.ker := Nat.card_le_card_of_injective _ hinj
  have hT27 : 27 ≤ Nat.card T := by
    rw [hcard, hEcard]
    nlinarith
  obtain ⟨P, hTP⟩ := hTp.exists_le_sylow
  have : Finite X := Finite.of_equiv _ e.toEquiv
  have hKcard : Nat.card K = Nat.card X * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZ3,
      Nat.card_congr e.toEquiv]
  have hPcard : Nat.card P = 27 := by
    rw [Sylow.card_eq_multiplicity, hKcard,
      Nat.factorization_mul (Nat.card_pos (α := X)).ne' (by norm_num)]
    have hX0 : Nat.card X ≠ 0 := (Nat.card_pos (α := X)).ne'
    have h2 : 2 ≤ (Nat.card X).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hX0).mp h9
    have h3' : ¬ 3 ≤ (Nat.card X).factorization 3 := fun h =>
      h27 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hX0).mpr h)
    have h2' : (Nat.card X).factorization 3 = 2 := by omega
    simp [h2', Nat.Prime.factorization_self Nat.prime_three]
  have hTeq : T = P := Subgroup.eq_of_le_of_card_ge hTP (by rw [hPcard]; exact hT27)
  have hPcomm : ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K), x * y = y * x := by
    intro x hx y hy
    rw [← hTeq] at hx hy
    exact hcomm x y hx hy
  obtain ⟨Cp⟩ : Nonempty (Sylow 3 (QuotientGroup.mk' (Subgroup.center K)).ker) := inferInstance
  have hbot := CFSG.SectionRank.OddCover.sylow_kernel_eq_bot_of_commute
    (QuotientGroup.mk' (Subgroup.center K)) (by rw [QuotientGroup.ker_mk']) P hPcomm Cp
  have hdvd : 3 ∣ Nat.card (QuotientGroup.mk' (Subgroup.center K)).ker := by
    rw [QuotientGroup.ker_mk', hZ3]
  exact Sylow.ne_bot_of_dvd_card Cp hdvd hbot

theorem mulAut_apply_mem_center {K : Type*} [Group K] (ε : MulAut K) {z : K}
    (hz : z ∈ Subgroup.center K) : ε z ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h := hz (ε.symm g)
  have h2 := congrArg ε h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem kGenTwoMod_of_seitz {K L : Type} [Group K] [Group L] (hperf : Group.IsPerfect K)
    (e : K ⧸ Subgroup.center K ≃* L)
    (hS : ∀ E' : Subgroup (MulAut L), IsElemAbelian 3 E' → Nat.card E' = 3 ^ 2 →
      Subgroup.closure {l : L | ∃ a ∈ E', a ≠ 1 ∧ a l = l} = ⊤) :
    KGenTwoMod 3 K := by
  intro E hE hEcard
  let ρ : MulAut K →* MulAut L :=
    (MulAut.congr e).toMonoidHom.comp (centerQuotientHom K)
  have hρ : Function.Injective ρ :=
    (MulAut.congr e).injective.comp (centerQuotientHom_injective K)
  let q : K →* L := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : ∀ k, q k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    simp [q]
  have hρq : ∀ (ε : MulAut K) (k : K), ρ ε (q k) = q (ε k) := by
    intro ε k
    simp [ρ, q, MulAut.congr_apply, centerQuotientHom_apply_mk]
  have hE1 : ∃ ε ∈ E, ε ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [this, Subgroup.card_bot] at hEcard
    omega
  have hρE : IsElemAbelian 3 (E.map ρ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨α, hα, ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨β, hβ, hb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      show (a : MulAut L) * (b : MulAut L) = (b : MulAut L) * (a : MulAut L)
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨α, hα⟩ ⟨β, hβ⟩)
    · intro a ha
      obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_pow, hE.2 α hα, map_one]
  have hcl := hS (E.map ρ) hρE (by rw [Subgroup.card_map_of_injective hρ, hEcard])
  have hsub : {l : L | ∃ a ∈ E.map ρ, a ≠ 1 ∧ a l = l} ⊆
      q '' {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K} := by
    rintro l ⟨a, ha, ha1, hal⟩
    obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨k, rfl⟩ := hq l
    refine ⟨k, ⟨ε, hε, ?_, ?_⟩, rfl⟩
    · rintro rfl
      exact ha1 (map_one ρ)
    · rw [← hqker, map_mul, map_inv, ← hρq, hal, mul_inv_cancel]
  have hmap : (Subgroup.closure
      {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K}).map q = ⊤ := by
    rw [MonoidHom.map_closure, eq_top_iff, ← hcl]
    exact Subgroup.closure_mono hsub
  have hZF : (Subgroup.center K : Set K) ⊆
      {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K} := by
    intro z hz
    obtain ⟨ε, hε, hε1⟩ := hE1
    exact ⟨ε, hε, hε1, Subgroup.mul_mem _ (mulAut_apply_mem_center ε hz) (Subgroup.inv_mem _ hz)⟩
  rw [eq_top_iff]
  intro k _
  obtain ⟨c, hc, hck⟩ : ∃ c ∈ Subgroup.closure
      {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K}, q c = q k := by
    have : q k ∈ (Subgroup.closure
      {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K}).map q :=
      hmap ▸ Subgroup.mem_top _
    exact Subgroup.mem_map.mp this
  have hcz : c⁻¹ * k ∈ Subgroup.center K := by
    rw [← hqker, map_mul, map_inv, hck, inv_mul_cancel]
  have hk : k = c * (c⁻¹ * k) := by group
  rw [hk]
  exact Subgroup.mul_mem _ hc (Subgroup.subset_closure (hZF hcz))

end CFSG.AGLEmbedding.KFactProofs.CoverThree
