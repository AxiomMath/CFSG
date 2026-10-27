module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34OuterDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

section Helpers

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.RankThree.PartTwo.KFacts.L34

private theorem mem_of_pow_mem_of_coprime {H : Subgroup X} {x : X} {a b : ℕ}
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) (hab : Nat.Coprime a b) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hx : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h,
      zpow_one]
  rw [hx]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

private theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {x : X} {j : ℕ} (h : x ^ p ^ j = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨j, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

private theorem exists_autEmbedding {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup X} (hKn : K.Normal) (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 4 ∧ ∃ (ψ : K ≃* projectiveSL 3 F)
      (ι : X →* MulAut (projectiveSL 3 F)), Function.Injective ι ∧
      ∀ (x : X) (k : K), ι x (ψ k) = ψ ⟨x * k * x⁻¹, hKn.conj_mem k k.2 x⟩ := by
  have : K.Normal := hKn
  obtain ⟨e⟩ := he
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := Tits.S3AmalgamBound.exists_equiv_projectiveSL_of_l34Index hd e
  let θ : X →* MulAut K := MulAut.conjNormal
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : g * k * g⁻¹ = k := by
        have := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) hg
        simpa [θ, MulAut.conjNormal_apply] using this
      calc k * g = g * k * g⁻¹ * g := by rw [h1]
        _ = g * k := by group
    rw [hC] at hmem
    exact hmem
  refine ⟨F, inferInstance, hF, ψ, (MulAut.congr ψ).toMonoidHom.comp θ,
    (MulAut.congr ψ).injective.comp hθ, fun x k => ?_⟩
  have h1 : (MulAut.congr ψ (θ x)) (ψ k) = ψ (θ x k) := by
    simp [MulAut.congr_apply]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  exact congrArg ψ (Subtype.ext (MulAut.conjNormal_apply x k))

private theorem centralizer_facts {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup X} (hKn : K.Normal) (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) {Ab : Subgroup X}
    (hA9 : Nat.card Ab = 3 ^ 2) (hAK : Ab ≤ K) :
    (∀ c ∈ Subgroup.centralizer (Ab : Set X), c ∈ K → c ∈ Ab) ∧
      ∀ c ∈ Subgroup.centralizer (Ab : Set X), ∀ c' ∈ Subgroup.centralizer (Ab : Set X),
        c ∉ Ab → c' ∉ Ab → c⁻¹ * c' ∈ Ab := by
  obtain ⟨F, _, hF, ψ, ι, hinj, hι⟩ := exists_autEmbedding hd hKn hC he
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hF
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  set σ : F ≃+* F := frobeniusEquiv F 2
  have hσ : ∀ a, σ a = a ^ 2 := fun a => frobeniusEquiv_apply F 2 a
  have hconj : ∀ k : K, ι k = MulAut.conj (ψ k) := by
    intro k
    ext y
    obtain ⟨k', rfl⟩ := ψ.surjective y
    rw [hι, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  set E : Subgroup (projectiveSL 3 F) := (Ab.subgroupOf K).map ψ.toMonoidHom with hEdef
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9]
    norm_num
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hF hE9
  have hmemE : ∀ y ∈ eZero F, ∃ a : K, (a : X) ∈ Ab ∧ ψ a = g * y * g⁻¹ := by
    intro y hy
    have hyE : g * y * g⁻¹ ∈ E := by
      rw [hg]
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    obtain ⟨a, ha, hay⟩ := hyE
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, hay⟩
  let α : X →* MulAut (projectiveSL 3 F) :=
    (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom.comp ι
  have hα : ∀ x, α x = (MulAut.conj g)⁻¹ * ι x * MulAut.conj g := fun x => by
    simp [α, MulAut.conj_apply]
  have hfix : ∀ c ∈ Subgroup.centralizer (Ab : Set X), ∀ y ∈ eZero F, α c y = y := by
    intro c hc y hy
    obtain ⟨a, haA, hay⟩ := hmemE y hy
    have hca : (⟨c * a * c⁻¹, hKn.conj_mem a a.2 c⟩ : K) = a := by
      apply Subtype.ext
      rw [Subgroup.mem_centralizer_iff] at hc
      change c * a * c⁻¹ = a
      rw [← hc a haA]
      group
    rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, ← hay, hι, hca, hay,
      MulAut.conj_inv_apply]
    group
  have hA : ∀ x : X, ∀ e ∈ eZero F, α x = MulAut.conj e → x ∈ Ab := by
    intro x e he hxe
    obtain ⟨a, haA, hae⟩ := hmemE e he
    have h1 : ι x = MulAut.conj (g * e * g⁻¹) := by
      have : ι x = MulAut.conj g * α x * (MulAut.conj g)⁻¹ := by rw [hα]; group
      rw [this, hxe, map_mul, map_mul, map_inv]
    have h2 : ι x = ι a := by rw [h1, hconj, hae]
    rw [hinj h2]
    exact haA
  have hβ : ∀ e p : projectiveSL 3 F, MulAut.conj e * betaAut σ ≠ MulAut.conj p := by
    intro e p h
    have hb : betaAut σ = MulAut.conj (e⁻¹ * p) := by
      rw [map_mul, map_inv, ← h]
      group
    have hq : e⁻¹ * p ∈ eZero F := by
      rw [← centralizer_eZero hF, Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := betaAut_fixed hF hσ hy
      rw [hb, MulAut.conj_apply] at h1
      calc y * (e⁻¹ * p) = e⁻¹ * p * y * (e⁻¹ * p)⁻¹ * (e⁻¹ * p) := by rw [h1]
        _ = e⁻¹ * p * y := by group
    have h3 : betaAut σ ^ 3 = 1 := by
      rw [hb, ← map_pow, pow_three_of_mem_eZero hF hq, map_one]
    have key : ∀ b : MulAut (projectiveSL 3 F), b ^ 3 = 1 → b * b = 1 → b = 1 :=
      fun b hb3 hb2 => by
        calc b = b ^ 3 * (b * b)⁻¹ := by group
          _ = 1 := by rw [hb3, hb2]; group
    exact betaAut_ne_one hF (key _ h3 (betaAut_mul_self hF hσ))
  refine ⟨fun c hc hcK => ?_, fun c hc c' hc' hcA hc'A => ?_⟩
  · obtain ⟨e, he, h | h⟩ := (forall_fixes_eZero_iff hF hσ (α c)).mp (hfix c hc)
    · exact hA c e he h
    · exfalso
      have hck : ι c = MulAut.conj (ψ ⟨c, hcK⟩) := hconj ⟨c, hcK⟩
      have h1 : α c = MulAut.conj (g⁻¹ * ψ ⟨c, hcK⟩ * g) := by
        rw [hα, hck, map_mul, map_mul, map_inv]
      exact hβ e _ (h.symm.trans h1)
  · have hβc : ∀ x ∈ Subgroup.centralizer (Ab : Set X), x ∉ Ab →
        ∃ e ∈ eZero F, α x = MulAut.conj e * betaAut σ := by
      intro x hx hxA
      obtain ⟨e, he, h | h⟩ := (forall_fixes_eZero_iff hF hσ (α x)).mp (hfix x hx)
      · exact absurd (hA x e he h) hxA
      · exact ⟨e, he, h⟩
    obtain ⟨e, he, h⟩ := hβc c hc hcA
    obtain ⟨e', he', h'⟩ := hβc c' hc' hc'A
    have hee : e⁻¹ * e' ∈ eZero F := mul_mem (inv_mem he) he'
    refine hA (c⁻¹ * c') (e⁻¹ * e') hee ?_
    have hβinv : (betaAut σ)⁻¹ = betaAut σ :=
      inv_eq_of_mul_eq_one_right (betaAut_mul_self hF hσ)
    have key : betaAut σ * MulAut.conj (e⁻¹ * e') * (betaAut σ)⁻¹ =
        MulAut.conj (e⁻¹ * e') := by
      rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, betaAut_fixed hF hσ hee]
    rw [map_mul, map_inv, h, h']
    calc (MulAut.conj e * betaAut σ)⁻¹ * (MulAut.conj e' * betaAut σ)
        = (betaAut σ)⁻¹ * MulAut.conj (e⁻¹ * e') * betaAut σ := by
          rw [map_mul, map_inv]
          group
      _ = betaAut σ * MulAut.conj (e⁻¹ * e') * (betaAut σ)⁻¹ := by rw [hβinv]
      _ = MulAut.conj (e⁻¹ * e') := key

private theorem card_facts {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup X} (hKn : K.Normal) (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card K = 20160 ∧ Nat.card X ∣ 241920 := by
  obtain ⟨F, _, hF, ψ, ι, hinj, -⟩ := exists_autEmbedding hd hKn hC he
  refine ⟨by rw [Nat.card_congr ψ.toEquiv, card_projectiveSL hF], ?_⟩
  rw [← card_mulAut hF, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Helpers

theorem l34_index_eq_six_or_twelve
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {K : Subgroup X} (hKn : K.Normal)
    (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) {Ab : Subgroup X}
    (hAel : IsElemAbelian 3 Ab) (hA9 : Nat.card Ab = 3 ^ 2) (hAK : Ab ≤ K)
    (hcent : ¬ Subgroup.centralizer (Ab : Set X) ≤ Ab) (h27 : 27 ∣ Nat.card X) :
    K.index = 6 ∨ K.index = 12 := by
  have : K.Normal := hKn
  obtain ⟨hCK, hCC⟩ := centralizer_facts hd hKn hC he hA9 hAK
  obtain ⟨c, hcC, hcA⟩ := IsConcreteLE.not_le_iff_exists.mp hcent
  have hcK : c ∉ K := fun h => hcA (hCK c hcC h)
  have hc2 : c * c ∈ K := by
    have h1 := hCC c⁻¹ (inv_mem hcC) c hcC (fun h => hcA (by simpa using inv_mem h)) hcA
    rw [inv_inv] at h1
    exact hAK h1
  obtain ⟨hKc, hXdvd⟩ := card_facts hd hKn hC he
  have hidx : K.index * 20160 = Nat.card X := hKc ▸ K.index_mul_card
  have h2 : 2 ∣ K.index := by
    have hne : (c : X ⧸ K) ≠ 1 := by
      rwa [Ne, QuotientGroup.eq_one_iff]
    have hsq : (c : X ⧸ K) ^ 2 = 1 := by
      rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hc2
    have hord : orderOf (c : X ⧸ K) = 2 := orderOf_eq_prime hsq hne
    rw [Subgroup.index_eq_card, ← hord]
    exact orderOf_dvd_natCard _
  have h3 : 3 ∣ K.index := by
    rw [← hidx] at h27
    omega
  have h12 : K.index ∣ 12 := by
    rw [← hidx] at hXdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 20160) (by simpa using hXdvd)
  have hle : K.index ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  obtain ⟨n, hn⟩ : ∃ n, K.index = n := ⟨_, rfl⟩
  rw [hn] at h2 h3 h12 hle ⊢
  interval_cases n <;> omega

theorem l34_exists_outer_three_normalizing
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {K : Subgroup X} (hKn : K.Normal)
    (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) {Ab : Subgroup X}
    (hAel : IsElemAbelian 3 Ab) (hA9 : Nat.card Ab = 3 ^ 2) (hAK : Ab ≤ K)
    (hcent : ¬ Subgroup.centralizer (Ab : Set X) ≤ Ab) (h6 : K.index = 6) {Tb : Subgroup X}
    (hTb : IsSylowTwoOf Tb (Subgroup.normalizer (Ab : Set X))) :
    ∃ s ∈ Subgroup.normalizer (Ab : Set X),
      s ∈ Subgroup.normalizer (Tb : Set X) ∧ s ∉ K ∧ s ^ 3 = 1 := by
  have : K.Normal := hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hCK, hCC⟩ := centralizer_facts hd hKn hC he hA9 hAK
  obtain ⟨c₀, hc₀C, hc₀A⟩ := IsConcreteLE.not_le_iff_exists.mp hcent
  obtain ⟨hKc, -⟩ := card_facts hd hKn hC he
  set C := Subgroup.centralizer (Ab : Set X) with hCdef
  set N := Subgroup.normalizer (Ab : Set X) with hNdef
  have hfr : N ⊔ K = ⊤ := by
    have hfK : (Nat.card K).factorization 3 = 2 := by
      rw [hKc]
      exact factorization_eq_of_pow_dvd Nat.prime_three (by norm_num) (by norm_num)
        (by norm_num)
    let P : Sylow 3 K := Sylow.ofCard (Ab.subgroupOf K) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9, hfK])
    have h := Sylow.normalizer_sup_eq_top P
    have hP : ((P : Subgroup K).map K.subtype : Subgroup X) = Ab :=
      Subgroup.map_subgroupOf_eq_of_le hAK
    rwa [hP] at h
  have hNC : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    rw [hCdef, Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n⁻¹ * a * n ∈ Ab := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) a).mp ha
      simpa using this
    have hca := hc _ ha'
    calc a * (n * c * n⁻¹) = n * (n⁻¹ * a * n * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hca]
      _ = n * c * n⁻¹ * a := by group
  set L := K ⊔ C with hLdef
  have hLn : L.Normal := by
    constructor
    intro l hl x
    obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hfr ▸ Subgroup.mem_top x)
    obtain ⟨k', hk', c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hl
    have h1 : k * k' * (c * k⁻¹ * c⁻¹) ∈ K :=
      mul_mem (mul_mem hk hk') (hKn.conj_mem _ (inv_mem hk) c)
    have h2 : n * (k * k' * (c * k⁻¹ * c⁻¹)) * n⁻¹ ∈ K := hKn.conj_mem _ h1 n
    have h3 : n * c * n⁻¹ ∈ C := hNC n hn c hc
    have heq : n * k * (k' * c) * (n * k)⁻¹ =
        n * (k * k' * (c * k⁻¹ * c⁻¹)) * n⁻¹ * (n * c * n⁻¹) := by group
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right h3)
  have hKL : K.relIndex L = 2 := by
    rw [hLdef, Subgroup.relIndex_sup_left, Subgroup.relIndex_eq_two_iff]
    refine ⟨c₀, hc₀C, fun b hb => ?_⟩
    by_cases hbA : b ∈ Ab
    · have hbK : b ∈ K := hAK hbA
      have hbc : b * c₀ ∉ K := fun h => hc₀A (by
        have := mul_mem (inv_mem hbA) (hCK (b * c₀) (mul_mem hb hc₀C) h)
        simpa using this)
      exact Or.inr ⟨hbK, hbc⟩
    · have hbK : b ∉ K := fun h => hbA (hCK b hb h)
      have hbc : b * c₀ ∈ K := by
        have h1 := hCC b⁻¹ (inv_mem hb) c₀ hc₀C (fun h => hbA (by simpa using inv_mem h)) hc₀A
        rw [inv_inv] at h1
        exact hAK h1
      exact Or.inl ⟨hbc, hbK⟩
  have hL3 : L.index = 3 := by
    have h : K.relIndex L * L.index = K.index := Subgroup.relIndex_mul_index le_sup_left
    rw [hKL, h6] at h
    omega
  have hpow3 : ∀ x : X, x ^ 3 ∈ L := fun x => hL3 ▸ L.pow_index_mem x
  have hTbL : Tb ≤ L := by
    intro t ht
    obtain ⟨j, hj⟩ := hTb.2.1 ⟨t, ht⟩
    have htj : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact mem_of_pow_mem_of_coprime (htj ▸ one_mem L) (hpow3 t)
      (Nat.Coprime.pow_left j (by norm_num))
  obtain ⟨n, hnN, hnL⟩ : ∃ n ∈ N, n ∉ L := by
    by_contra h
    push Not at h
    have hL : L = ⊤ := eq_top_iff.mpr (hfr ▸ sup_le (fun n hn => h n hn) le_sup_left)
    rw [hL, Subgroup.index_top] at hL3
    omega
  set W := N ⊓ L with hWdef
  have hTbW : Tb ≤ W := le_inf hTb.1 hTbL
  set T₂ := Tb.map (MulAut.conj n).toMonoidHom with hT₂def
  have hT₂W : T₂ ≤ W := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (MulAut.conj n).toMonoidHom t = n * t * n⁻¹ := rfl
    rw [h1]
    exact Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem hnN (hTb.1 ht)) (inv_mem hnN), hLn.conj_mem t (hTbL ht) n⟩
  have hTbW' : IsSylowTwoOf Tb W := by
    have hT := isSylowTwoOf_iff.mp hTb
    refine isSylowTwoOf_iff.mpr ⟨hTbW, hT.2.1, le_antisymm (card_le_twoPart hTbW hT.2.1) ?_⟩
    rw [hT.2.2]
    exact twoPart_mono inf_le_left
  have hT₂W' : IsSylowTwoOf T₂ W := by
    have hT := isSylowTwoOf_iff.mp hTbW'
    refine isSylowTwoOf_iff.mpr ⟨hT₂W, hT.2.1.map _, ?_⟩
    rw [hT₂def, Subgroup.card_map_of_injective (MulAut.conj n).injective, hT.2.2]
  obtain ⟨w, hwW, hw⟩ := IsSylowTwoOf.exists_conj hTbW' hT₂W'
  set s₀ := w⁻¹ * n with hs₀
  have hwN : w ∈ N := (Subgroup.mem_inf.mp hwW).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp hwW).2
  have hs₀N : s₀ ∈ N := mul_mem (inv_mem hwN) hnN
  have hs₀L : s₀ ∉ L := fun h => hnL (by simpa [hs₀] using mul_mem hwL h)
  have hs₀T : s₀ ∈ Subgroup.normalizer (Tb : Set X) := by
    apply Subgroup.mem_normalizer_fintype
    intro t ht
    have h1 : n * t * n⁻¹ ∈ T₂ := ⟨t, ht, by simp [MulAut.conj_apply]⟩
    rw [hw] at h1
    obtain ⟨t', ht', ht'e⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ht'e
    have : s₀ * t * s₀⁻¹ = t' := by
      calc s₀ * t * s₀⁻¹ = w⁻¹ * (n * t * n⁻¹) * w := by rw [hs₀]; group
        _ = w⁻¹ * (w * t' * w⁻¹) * w := by rw [ht'e]
        _ = t' := by group
    rw [this]
    exact ht'
  obtain ⟨a, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos s₀).ne' 3 (by norm_num)
  refine ⟨s₀ ^ m, pow_mem hs₀N m, pow_mem hs₀T m, fun hK => ?_, ?_⟩
  · exact hs₀L (mem_of_pow_mem_of_coprime ((le_sup_left : K ≤ L) hK) (hpow3 s₀)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm)
  · refine Tits.S3AmalgamBound.kFactL34Exp3 d hd X K hKn hC he _
      (isPGroup_zpowers_of_pow_eq_one (j := a) ?_)
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]

theorem l34_exists_le_of_pow_eq_one
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {K : Subgroup X} (hKn : K.Normal)
    (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ L : Subgroup X, K ≤ L ∧ K.relIndex L ≤ 3 ∧ ∀ x : X, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ L := by
  have : K.Normal := hKn
  obtain ⟨e⟩ := he
  obtain ⟨θ⟩ := nonempty_equiv_S_of_index hd e
  obtain ⟨ι, hinj, hιK, hιR⟩ := exists_embedding_l34 hC θ
  have facts := l34_outer_check
  have hKL : K ≤ CFSG.AGLEmbedding.L34Outer.L34T.comap ι := by
    intro k hk
    change ι k ∈ CFSG.AGLEmbedding.L34Outer.L34T
    rw [show ι k = (θ ⟨k, hk⟩ : Equiv.Perm (Fin 42)) from hιK ⟨k, hk⟩]
    exact CFSG.AGLEmbedding.L34Outer.S_le_T (θ ⟨k, hk⟩).2
  refine ⟨CFSG.AGLEmbedding.L34Outer.L34T.comap ι, hKL, ?_, fun x j hx => ?_⟩
  · have hcardK : Nat.card K = 20160 := by
      rw [Nat.card_congr θ.toEquiv, CFSG.ComponentClassification.PSL3Four.card_S]
    have h1 : K.relIndex (CFSG.AGLEmbedding.L34Outer.L34T.comap ι) * Nat.card K =
        Nat.card (CFSG.AGLEmbedding.L34Outer.L34T.comap ι) := by
      rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
      exact Subgroup.index_mul_card _
    have h2 : Nat.card (CFSG.AGLEmbedding.L34Outer.L34T.comap ι) ∣ 60480 := by
      rw [← facts.cardT, ← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    rw [← h1, hcardK] at h2
    have h3 : K.relIndex (CFSG.AGLEmbedding.L34Outer.L34T.comap ι) ∣ 3 :=
      Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 20160) (by simpa using h2)
    exact Nat.le_of_dvd (by norm_num) h3
  · have hx3 : x ^ 3 = 1 := Tits.S3AmalgamBound.kFactL34Exp3 d hd X K hKn hC ⟨e⟩ x
      (isPGroup_zpowers_of_pow_eq_one hx)
    change ι x ∈ CFSG.AGLEmbedding.L34Outer.L34T
    exact facts.order3 (ι x) (hιR ⟨x, rfl⟩) (by rw [← map_pow, hx3, map_one])

end CFSG.LocalAnalysis.RankThreeTheoremC
