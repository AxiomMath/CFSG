module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_conj_le_of_relIndex [Finite G] {p : ℕ} [Fact p.Prime] {H R S : Subgroup G}
    (hR : R ≤ H) (hRp : IsPGroup p R) (hS : S ≤ H) (hSp : IsPGroup p S)
    (hSi : ¬ p ∣ S.relIndex H) : ∃ h ∈ H, ∀ x ∈ R, h * x * h⁻¹ ∈ S := by
  have hSp' : IsPGroup p (S.subgroupOf H) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hRp' : IsPGroup p (R.subgroupOf H) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
  obtain ⟨n, hn⟩ := hSp'.exists_card_eq
  have hcard : Nat.card (S.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf H)
    have hidx : (S.subgroupOf H).index = S.relIndex H := rfl
    rw [hidx, hn] at h1
    have hne : S.relIndex H ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact (Nat.card_pos (α := H)).ne' h1.symm
    rw [← h1, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hne,
      Nat.Prime.factorization_pow (Fact.out : p.Prime)]
    simp [Nat.factorization_eq_zero_of_not_dvd hSi, hn]
  let Q : Sylow p H := Sylow.ofCard (S.subgroupOf H) hcard
  obtain ⟨Q', hQ'⟩ := hRp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q Q'
  have hg' := congrArg (fun S : Sylow p H => (S : Subgroup H)) hg
  simp only [Sylow.coe_subgroup_smul] at hg'
  refine ⟨(g : G)⁻¹, (inv_mem g.2), fun x hx => ?_⟩
  have hxH : x ∈ H := hR hx
  have h1 : (⟨x, hxH⟩ : H) ∈ (Q' : Subgroup H) := hQ' ((Subgroup.mem_subgroupOf).2 hx)
  rw [← hg', Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (MulAut.conj g)⁻¹ • (⟨x, hxH⟩ : H) = g⁻¹ * ⟨x, hxH⟩ * g := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [h2] at h1
  have h1' : g⁻¹ * ⟨x, hxH⟩ * g ∈ S.subgroupOf H := by
    have := h1
    rwa [show (Q : Subgroup H) = S.subgroupOf H from Sylow.coe_ofCard _ _] at this
  have h3 : ((g⁻¹ * ⟨x, hxH⟩ * g : H) : G) ∈ S := (Subgroup.mem_subgroupOf).1 h1'
  have h4 : ((g : G)⁻¹)⁻¹ = g := by simp
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  simpa [h4] using h3

theorem mem_normalizer_of_conj_le [Finite G] {S : Subgroup G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    simpa using h s hs
  have hcard : Nat.card S ≤ Nat.card (S.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · simpa using h y hy
  · have : g * y * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hy
    obtain ⟨s, hs, hsy⟩ := this
    have : s = y := by
      have := congrArg (fun z => g⁻¹ * z * g) hsy
      simpa [MulAut.conj_apply, mul_assoc] using this
    exact this ▸ hs

theorem exists_mul_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {Y P S : Subgroup G}
    (hPY : P ≤ Y) (hYP : Y ≤ Subgroup.normalizer (P : Set G)) (hSP : S ≤ P)
    (hSp : IsPGroup p S) (hSi : ¬ p ∣ S.relIndex P) {y : G} (hy : y ∈ Y) :
    ∃ q ∈ P, ∃ w ∈ Subgroup.normalizer (S : Set G) ⊓ Y, y = q * w := by
  set f : G →* G := (MulAut.conj y).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj y).injective
  have hRP : S.map f ≤ P := by
    rintro _ ⟨s, hs, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (hYP hy) s).1 (hSP hs)
    simpa [hf, MulAut.conj_apply] using this
  have hRp : IsPGroup p (S.map f) := hSp.of_equiv (Subgroup.equivMapOfInjective S f hinj)
  obtain ⟨q, hq, hqS⟩ := exists_conj_le_of_relIndex hRP hRp hSP hSp hSi
  have hN : q * y ∈ Subgroup.normalizer (S : Set G) := by
    refine mem_normalizer_of_conj_le fun s hs => ?_
    have := hqS (y * s * y⁻¹) ⟨s, hs, by simp [hf, MulAut.conj_apply]⟩
    simpa [mul_assoc] using this
  refine ⟨q⁻¹, inv_mem hq, q * y, ⟨hN, Y.mul_mem (hPY hq) hy⟩, by simp⟩

theorem mem_normalizer_commutator [Finite G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) →
      g ∈ Subgroup.normalizer (K : Set G) → ∀ x ∈ ⁅H, K⁆, g * x * g⁻¹ ∈ ⁅H, K⁆ := by
    intro g hH hK
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have h1 : g * a * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hH a).1 ha
      have h2 : g * b * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hK b).1 hb
      have := Subgroup.commutator_mem_commutator h1 h2
      rw [Subgroup.mem_comap]
      convert this using 1
      simp [MulAut.conj_apply, commutatorElement_def, mul_assoc]
    intro x hx
    simpa using hle hx
  have hg1 := key g hH hK
  have hg2 := key g⁻¹ (inv_mem hH) (inv_mem hK)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hg1 y, fun hy => ?_⟩
  simpa [mul_assoc] using hg2 _ hy

theorem not_dvd_relIndex_inf [Finite G] {p : ℕ} {P S V : Subgroup G} (hVP : V ≤ P)
    (hVn : P ≤ Subgroup.normalizer (V : Set G)) (hSP : S ≤ P)
    (hSi : ¬ p ∣ S.relIndex P) : ¬ p ∣ (S ⊓ V).relIndex V := by
  have hprod := Lemma85Aux.card_sup_mul_card_inf' (A := S) (N := V) (hSP.trans hVn)
  have h1 := Subgroup.relIndex_mul_card S P
  rw [inf_eq_left.2 hSP] at h1
  have h2 := Subgroup.relIndex_mul_card (S ⊓ V) V
  rw [inf_eq_left.2 inf_le_right] at h2
  have hdvd : Nat.card (S ⊔ V : Subgroup G) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le (sup_le hSP hVP)
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hIpos : 0 < Nat.card (S ⊓ V : Subgroup G) := Nat.card_pos
  have h3 : Nat.card (S ⊔ V : Subgroup G) = Nat.card S * (S ⊓ V).relIndex V := by
    have : Nat.card (S ⊔ V : Subgroup G) * Nat.card (S ⊓ V : Subgroup G) =
        (Nat.card S * (S ⊓ V).relIndex V) * Nat.card (S ⊓ V : Subgroup G) := by
      rw [hprod, ← h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hIpos this
  rw [h3, ← h1, mul_comm] at hdvd
  have : (S ⊓ V).relIndex V ∣ S.relIndex P := Nat.dvd_of_mul_dvd_mul_right hSpos hdvd
  exact fun hp => hSi (hp.trans this)

theorem eq_or_eq_of_normal_of_isLThreeFour [Finite G] {I N : Subgroup G}
    (hl : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I)) (hON : GLAPPrimeCoreOf 3 I ≤ N) (hNI : N ≤ I)
    (hn : I ≤ Subgroup.normalizer (N : Set G)) : N = GLAPPrimeCoreOf 3 I ∨ N = I := by
  have := (isSimpleGroup_of_isLThreeFour hl).1
  set K := GLAPPrimeCore 3 ↥I with hK
  have hKN : K ≤ N.subgroupOf I := by
    intro k hk
    exact (Subgroup.mem_subgroupOf).2 (hON ⟨k, hk, rfl⟩)
  have : (N.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNI).2 hn
  have hnm : ((N.subgroupOf I).map (QuotientGroup.mk' K)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
  have := hnm
  have hcomap : ((N.subgroupOf I).map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) =
      N.subgroupOf I := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hKN]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf I).map (QuotientGroup.mk' K)) with h | h
  · left
    rw [h] at hcomap
    refine le_antisymm ?_ hON
    intro x hx
    have h1 : (⟨x, hNI hx⟩ : I) ∈ N.subgroupOf I := (Subgroup.mem_subgroupOf).2 hx
    rw [← hcomap, Subgroup.mem_comap, Subgroup.mem_bot] at h1
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  · right
    rw [h, Subgroup.comap_top] at hcomap
    refine le_antisymm hNI fun x hx => ?_
    have : (⟨x, hx⟩ : I) ∈ N.subgroupOf I := hcomap ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf).1 this

theorem not_le_of_isLThreeFour {I : Subgroup G}
    (hl : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I)) : ¬ I ≤ GLAPPrimeCoreOf 3 I := by
  have := (isSimpleGroup_of_isLThreeFour hl).1
  intro hle
  have : Subsingleton (↥I ⧸ GLAPPrimeCore 3 ↥I) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | _ a => ?_
    induction b using QuotientGroup.induction_on with | _ b => ?_
    have ha : a ∈ GLAPPrimeCore 3 ↥I := by
      obtain ⟨k, hk, hka⟩ := hle a.2
      have : k = a := Subtype.ext hka
      exact this ▸ hk
    have hb : b ∈ GLAPPrimeCore 3 ↥I := by
      obtain ⟨k, hk, hka⟩ := hle b.2
      have : k = b := Subtype.ext hka
      exact this ▸ hk
    rw [(QuotientGroup.eq_one_iff a).2 ha, (QuotientGroup.eq_one_iff b).2 hb]
  exact not_subsingleton _ this

theorem pow_conj_eq {b p : G} {S : Subgroup G} (hb : ∀ s ∈ S, b * s * b⁻¹ = p * s * p⁻¹)
    (hp : ∀ s ∈ S, p * s * p⁻¹ ∈ S) :
    ∀ k : ℕ, ∀ s ∈ S, b ^ k * s * (b ^ k)⁻¹ = p ^ k * s * (p ^ k)⁻¹ ∧
      p ^ k * s * (p ^ k)⁻¹ ∈ S := by
  intro k
  induction k with
  | zero => intro s hs; simp [hs]
  | succ k ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := ih s hs
    refine ⟨?_, ?_⟩
    · have : b ^ (k + 1) * s * (b ^ (k + 1))⁻¹ = b * (b ^ k * s * (b ^ k)⁻¹) * b⁻¹ := by
        rw [pow_succ']; group
      rw [this, h1, hb _ h2]
      rw [pow_succ']; group
    · have : p ^ (k + 1) * s * (p ^ (k + 1))⁻¹ = p * (p ^ k * s * (p ^ k)⁻¹) * p⁻¹ := by
        rw [pow_succ']; group
      rw [this]
      exact hp _ h2

theorem conj_eq_self_of_coprime {b p : G} {S : Subgroup G} {n m : ℕ} (hm : 0 < m)
    (hnm : Nat.Coprime n m) (hbn : b ^ n = 1) (hpm : p ^ m = 1)
    (hb : ∀ s ∈ S, b * s * b⁻¹ = p * s * p⁻¹) (hp : ∀ s ∈ S, p * s * p⁻¹ ∈ S) :
    ∀ s ∈ S, b * s * b⁻¹ = s := by
  intro s hs
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hnm 0 1
  have h1 := (pow_conj_eq hb hp k s hs).1
  have hbk : b ^ k = 1 := by
    obtain ⟨c, hc⟩ := (Nat.modEq_zero_iff_dvd).1 hk1
    rw [hc, pow_mul, hbn, one_pow]
  have hpk : p ^ k = p := by
    rcases Nat.lt_or_ge 1 m with h | h
    · have hk : k % m = 1 := by
        have : k % m = 1 % m := hk2
        rwa [Nat.mod_eq_of_lt h] at this
      have h2 := Nat.div_add_mod k m
      rw [← h2, pow_add, pow_mul, hpm, one_pow, one_mul, hk, pow_one]
    · have hm1 : m = 1 := by omega
      subst hm1
      have : p = 1 := by simpa using hpm
      simp [this]
  rw [hbk, hpk] at h1
  have h3 : s = p * s * p⁻¹ := by simpa using h1
  rw [hb s hs]
  exact h3.symm

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
