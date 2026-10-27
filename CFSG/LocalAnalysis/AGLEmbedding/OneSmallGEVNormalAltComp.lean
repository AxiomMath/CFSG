module

public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Comp

variable {Y : Type*} [Group Y] [Finite Y]

theorem mem_normalizer_of_conj_not_mem_centralizer {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    {x y : Y} (hxL : x ∈ L) (hy : y * x * y⁻¹ ∉ Subgroup.centralizer (L : Set Y)) :
    y ∈ Subgroup.normalizer (L : Set Y) := by
  set L' := L.map (MulAut.conj y).toMonoidHom
  have hL' : IsComponentOf L' ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj y) L).mpr hL
  have hxL' : y * x * y⁻¹ ∈ L' := ⟨x, hxL, rfl⟩
  by_cases hne : L' = L
  · refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    have : y * l * y⁻¹ ∈ L' := ⟨l, hl, rfl⟩
    rwa [hne] at this
  · exact absurd (le_centralizer_of_component_ne hL' hL hne hxL') hy

theorem exists_pow_mem_of_inv_mul_mem_centralizer {p : ℕ} (hp : p.Prime) {L : Subgroup Y}
    {x l : Y} (hx : x ^ p = 1) (hlL : l ∈ L) (hc : l⁻¹ * x ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ l' ∈ L, l' ∈ Subgroup.zpowers l ∧ (∃ k : ℕ, l' ^ p ^ k = 1) ∧
      l'⁻¹ * x ∈ Subgroup.centralizer (L : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  set c := l⁻¹ * x
  have hxlc : x = l * c := by simp [c]
  have hlc : Commute l c := Subgroup.mem_centralizer_iff.mp hc l hlL
  have hlp : l ^ p ∈ Subgroup.centralizer (L : Set Y) := by
    have h1 : l ^ p * c ^ p = 1 := by rw [← hlc.mul_pow, ← hxlc, hx]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
  set r := Group.pRegular p l
  set l' := Group.pSingular p l
  have hrl : r ∈ Subgroup.zpowers l := ⟨_, rfl⟩
  have hl'l : l' ∈ Subgroup.zpowers l := ⟨_, rfl⟩
  have hfin : IsOfFinOrder l := isOfFinOrder_of_finite l
  have hdec : r * l' = l := Group.pDecomp' p hfin
  have hrC : r ∈ Subgroup.centralizer (L : Set Y) := by
    have hrp : r ^ p ∈ Subgroup.centralizer (L : Set Y) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrl
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ hlp k
    have hreg : (orderOf r).Coprime p := Group.isPRegular_pRegular p hfin
    have hmem : r ∈ Subgroup.zpowers (r ^ p) := mem_zpowers_pow_iff.mpr (Nat.Coprime.symm hreg)
    exact (Subgroup.zpowers_le.mpr hrp) hmem
  refine ⟨l', (Subgroup.zpowers_le.mpr hlL) hl'l, hl'l, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := Group.isPSingular_pSingular p l
    exact ⟨n, by rw [← hn, pow_orderOf_eq_one]⟩
  · have hrl' : Commute r l' := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hrl
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hl'l
      rw [← ha, ← hb]
      exact Commute.zpow_zpow_self l a b
    have : l'⁻¹ * x = r * c := by
      rw [hxlc, ← hdec]
      calc l'⁻¹ * (r * l' * c) = l'⁻¹ * (l' * r * c) := by rw [hrl'.eq]
        _ = r * c := by group
    rw [this]
    exact Subgroup.mul_mem _ hrC hc

@[expose] def lambdaSet (p : ℕ) (𝓑 : Set (Subgroup Y)) (x : Y) : Set Y :=
  {l | ∃ L ∈ 𝓑, l ∈ L ∧ (∃ k : ℕ, l ^ p ^ k = 1) ∧
    l⁻¹ * x ∈ Subgroup.centralizer (L : Set Y)}

theorem commute_of_mem_lambdaSet {p : ℕ} {𝓑 : Set (Subgroup Y)}
    (h𝓑 : ∀ L ∈ 𝓑, IsComponentOf L ⊤) {x a b : Y} (ha : a ∈ lambdaSet p 𝓑 x)
    (hb : b ∈ lambdaSet p 𝓑 x) : a * b = b * a := by
  obtain ⟨L₁, hL₁, haL, -, hac⟩ := ha
  obtain ⟨L₂, hL₂, hbL, -, hbc⟩ := hb
  by_cases hne : L₁ = L₂
  · subst hne
    have hd : a⁻¹ * b ∈ Subgroup.centralizer (L₁ : Set Y) := by
      have := Subgroup.mul_mem _ hac (Subgroup.inv_mem _ hbc)
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.mp hd a haL
    calc a * b = a * (a * (a⁻¹ * b)) := by group
      _ = a * ((a⁻¹ * b) * a) := by rw [h1]
      _ = b * a := by group
  · exact (Subgroup.mem_centralizer_iff.mp
      (le_centralizer_of_component_ne (h𝓑 L₁ hL₁) (h𝓑 L₂ hL₂) hne haL) b hbL).symm

omit [Finite Y] in
theorem commute_of_mem_lambdaSet_self {p : ℕ} {𝓑 : Set (Subgroup Y)} {x l : Y}
    (hl : l ∈ lambdaSet p 𝓑 x) : l * x = x * l := by
  obtain ⟨L, -, hlL, -, hc⟩ := hl
  have h1 := Subgroup.mem_centralizer_iff.mp hc l hlL
  calc l * x = l * (l * (l⁻¹ * x)) * l⁻¹ * l := by group
    _ = l * ((l⁻¹ * x) * l) * l⁻¹ * l := by rw [h1]
    _ = x * l := by group

theorem exists_pow_eq_one_of_mem_closure_lambdaSet {p : ℕ} {𝓑 : Set (Subgroup Y)}
    (h𝓑 : ∀ L ∈ 𝓑, IsComponentOf L ⊤) {x g : Y}
    (hg : g ∈ Subgroup.closure (lambdaSet p 𝓑 x)) : ∃ k : ℕ, g ^ p ^ k = 1 := by
  set S := lambdaSet p 𝓑 x
  have hcl : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr
    fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => commute_of_mem_lambdaSet h𝓑 hb ha
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have hSa : Subgroup.closure S ≤ Subgroup.centralizer ({a} : Set Y) :=
      (Subgroup.closure_le _).mpr fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hcl ha) c hc)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hSa hb)).symm
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨L, -, -, hk, -⟩ := hy
    exact hk
  | one => exact ⟨0, by simp⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨i, hi⟩ := iha
    obtain ⟨j, hj⟩ := ihb
    refine ⟨i + j, ?_⟩
    rw [(Commute.mul_pow (hcomm a ha b hb) _), pow_add, pow_mul, hi, one_pow, mul_comm (p ^ i),
      pow_mul, hj, one_pow, one_mul]
  | inv a ha iha =>
    obtain ⟨i, hi⟩ := iha
    exact ⟨i, by rw [inv_pow, hi, inv_one]⟩

theorem conj_mem_closure_lambdaSet {p : ℕ} {𝓑 : Set (Subgroup Y)} {x c : Y}
    (hc : c * x = x * c) (h𝓑c : ∀ L ∈ 𝓑, L.map (MulAut.conj c).toMonoidHom ∈ 𝓑) :
    c ∈ Subgroup.normalizer (Subgroup.closure (lambdaSet p 𝓑 x) : Set Y) := by
  set S := lambdaSet p 𝓑 x
  have himg : (MulAut.conj c).toMonoidHom '' S ⊆ S := by
    rintro _ ⟨l, ⟨L, hL, hlL, ⟨k, hk⟩, hlc⟩, rfl⟩
    refine ⟨L.map (MulAut.conj c).toMonoidHom, h𝓑c L hL, ⟨l, hlL, rfl⟩, ⟨k, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hk]
      group
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨m, hm, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hlc m hm
      have hcx : c⁻¹ * x = x * c⁻¹ := by
        calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hc]
          _ = x * c⁻¹ := by group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c * m * c⁻¹ * ((c * l * c⁻¹)⁻¹ * x)
          = c * (m * (l⁻¹ * (c⁻¹ * x))) := by group
        _ = c * (m * (l⁻¹ * (x * c⁻¹))) := by rw [hcx]
        _ = c * (m * (l⁻¹ * x)) * c⁻¹ := by group
        _ = c * ((l⁻¹ * x) * m) * c⁻¹ := by rw [h1]
        _ = c * (l⁻¹ * (c⁻¹ * x)) * (c * m * c⁻¹) := by rw [hcx]; group
        _ = (c * l * c⁻¹)⁻¹ * x * (c * m * c⁻¹) := by group
  have hmap : (Subgroup.closure S).map (MulAut.conj c).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono himg
  refine Subgroup.mem_normalizer_fintype fun g hg => hmap ⟨g, hg, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem exists_conj_mem_of_card_le {p : ℕ} [Fact p.Prime] {A R : Subgroup Y} (hRA : R ≤ A)
    (hR : IsPGroup p R)
    (hmax : ∀ Q : Subgroup Y, Q ≤ A → IsPGroup p Q → Nat.card Q ≤ Nat.card R) {y : Y}
    (hyA : y ∈ A) (hy : ∃ k : ℕ, y ^ p ^ k = 1) : ∃ a ∈ A, a⁻¹ * y * a ∈ R := by
  have hR' : IsPGroup p (R.subgroupOf A) := hR.comap_subtype
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  have hSR : (S : Subgroup A) = R.subgroupOf A := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    have h1 := hmax ((S : Subgroup A).map A.subtype) (Subgroup.map_subtype_le _)
      (S.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective A.subtype_injective,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRA).toEquiv] at h1
  set y' : A := ⟨y, hyA⟩
  have hy' : IsPGroup p (Subgroup.zpowers y') := by
    obtain ⟨k, hk⟩ := hy
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hk)
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hj]
  obtain ⟨S', hS'⟩ := hy'.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A S S'
  have hyS : y' ∈ ((a • S : Sylow p A) : Subgroup A) := ha ▸ hS' (Subgroup.mem_zpowers y')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv, hSR] at hyS
  exact ⟨a, a.2, by simpa [y'] using Subgroup.mem_subgroupOf.mp hyS⟩

end Comp

end CFSG.AGLEmbedding
